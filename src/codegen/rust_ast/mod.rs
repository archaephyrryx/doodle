use std::borrow::Cow;
use std::cmp::Ordering;
use std::rc::Rc;

pub(crate) mod analysis;
pub(crate) mod rebind;
pub(crate) mod resolve;

use crate::codegen::model::READ_ARRAY_IS_COPY;
use crate::output::{Fragment, FragmentBuilder};

use crate::precedence::{cond_paren, Precedence};
use crate::{BaseKind, BaseType, IntoLabel, Label, ValueType};

/// Enum-type (currently degenerate) for specifying the visibility of a top-level item
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub(crate) enum Visibility {
    /// Equivalent to leaving out any visibility keywords (i.e. as if `pub(self)`)
    #[default]
    Implicit,
    Public,
}

impl Visibility {
    fn add_vis(&self, item: Fragment) -> Fragment {
        match self {
            Self::Implicit => item,
            Self::Public => Fragment::cat(Fragment::string("pub "), item),
        }
    }
}

// FIXME - this shouldn't be open-coded but it will do for now
pub(crate) struct AllowAttr(Label);

impl From<Label> for AllowAttr {
    fn from(value: Label) -> Self {
        AllowAttr(value)
    }
}

impl ToFragment for AllowAttr {
    fn to_fragment(&self) -> Fragment {
        Fragment::cat(
            Fragment::string("allow"),
            Fragment::string(self.0.clone()).delimit(Fragment::Char('('), Fragment::Char(')')),
        )
    }
}

pub(crate) enum ModuleAttr {
    Allow(AllowAttr),
    // REVIEW - this feels a bit like a hack since it is a hard-coded one-off
    RustFmtSkip,
}

impl ToFragment for ModuleAttr {
    fn to_fragment(&self) -> Fragment {
        match self {
            ModuleAttr::Allow(allow_attr) => Fragment::string("#!").cat(
                allow_attr
                    .to_fragment()
                    .delimit(Fragment::Char('['), Fragment::Char(']')),
            ),
            ModuleAttr::RustFmtSkip => Fragment::string("#!").cat(
                // NOTE - "rustfmt::skip" by itself is flagged as unstable and breaks compilation
                Fragment::string("cfg_attr(rustfmt, rustfmt::skip)")
                    .delimit(Fragment::Char('['), Fragment::Char(']')),
            ),
        }
    }
}

pub(crate) struct RustSubmodule(Visibility, Label);

impl RustSubmodule {
    pub fn new(label: impl IntoLabel) -> Self {
        RustSubmodule(Visibility::default(), label.into())
    }

    pub fn new_pub(label: impl IntoLabel) -> Self {
        RustSubmodule(Visibility::Public, label.into())
    }
}

impl ToFragment for RustSubmodule {
    fn to_fragment(&self) -> Fragment {
        self.0
            .add_vis(Fragment::cat(
                Fragment::string("mod "),
                self.1.to_fragment(),
            ))
            .cat(Fragment::Char(';'))
    }
}

#[derive(Default)]
pub(crate) struct RustProgram {
    mod_level_attrs: Vec<ModuleAttr>,
    submodules: Vec<RustSubmodule>,
    imports: Vec<RustImport>,
    items: Vec<RustItem>,
}

impl FromIterator<RustItem> for RustProgram {
    fn from_iter<T: IntoIterator<Item = RustItem>>(iter: T) -> Self {
        Self {
            imports: Vec::new(),
            items: Vec::from_iter(iter),
            ..Default::default()
        }
    }
}

impl RustProgram {
    // pub fn new() -> Self {
    //     RustProgram {
    //         mod_level_attrs: Vec::new(),
    //         submodules: Vec::new(),
    //         imports: Vec::new(),
    //         items: Vec::new(),
    //     }
    // }

    pub fn add_module_attr(&mut self, attr: ModuleAttr) {
        self.mod_level_attrs.push(attr)
    }

    pub fn add_submodule(&mut self, submodule: RustSubmodule) {
        self.submodules.push(submodule)
    }

    pub fn add_import(&mut self, import: RustImport) {
        self.imports.push(import)
    }
}

impl ToFragment for RustProgram {
    fn to_fragment(&self) -> Fragment {
        let mut frags = FragmentBuilder::new();
        for mod_level_attr in self.mod_level_attrs.iter() {
            frags.push(mod_level_attr.to_fragment().cat_break());
        }
        if !self.mod_level_attrs.is_empty() {
            frags.push(Fragment::Empty.cat_break());
        }
        for submodule in self.submodules.iter() {
            frags.push(submodule.to_fragment().cat_break());
        }
        if !self.submodules.is_empty() {
            frags.push(Fragment::Empty.cat_break());
        }

        for import in self.imports.iter() {
            frags.push(import.to_fragment().cat_break());
        }

        if !self.imports.is_empty() {
            frags.push(Fragment::Empty.cat_break());
        }

        for item in self.items.iter() {
            frags.push(item.to_fragment().cat_break().cat_break());
        }
        frags.finalize()
    }
}

pub(crate) struct RustImport {
    pub(crate) path: Vec<Label>,
    pub(crate) uses: RustImportItems,
}

impl ToFragment for RustImport {
    fn to_fragment(&self) -> Fragment {
        let keyword = Fragment::string("use");
        let spec = Fragment::seq(
            self.path
                .iter()
                .cloned()
                .map(Fragment::String)
                .chain(std::iter::once(self.uses.to_fragment())),
            Some(Fragment::string("::")),
        );
        keyword
            .intervene(Fragment::Char(' '), spec)
            .cat(Fragment::Char(';'))
    }
}

/// Representation for the specifications of what items should be imported from a module in a top-level or block-local `use` expression.
pub(crate) enum RustImportItems {
    /// Glob-imports from a single module
    Wildcard,
    Singleton(Label),
}

impl ToFragment for RustImportItems {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustImportItems::Wildcard => Fragment::Char('*'),
            RustImportItems::Singleton(lbl) => Fragment::String(lbl.clone()),
        }
    }
}

/// Top-level declared item (e.g. struct definitions and functions)
pub(crate) struct RustItem {
    vis: Visibility,
    attrs: Vec<RustAttr>,
    doc_comment: Option<RustDocComment>,
    decl: RustDecl,
}

type CommentLine = Label;

#[derive(Clone, Debug)]
pub(crate) struct RustDocComment {
    lines: Vec<CommentLine>,
}

impl ToFragment for RustDocComment {
    fn to_fragment(&self) -> Fragment {
        // REVIEW - consider a Fragment token that is either newline (if not at column 1) or no-op (if at column 1)
        Fragment::seq(
            self.lines
                .iter()
                .map(|line| Fragment::string("/// ").cat(Fragment::String(line.clone()))),
            Some(Fragment::Char('\n')),
        )
    }
}

/// Specialized pseudo-bitflags implementation that directly implies Clone when Copy is set
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[repr(u8)]
#[allow(dead_code)]
pub(crate) enum TraitSet {
    Empty = 0,
    Debug = 1,
    Clone = 2,
    #[default]
    DebugClone = 3,
    Copy = 6, // 4 for Copy itself, BitOr'd with 2 for the implied Clone
    DebugCopy = 7,
}

impl std::ops::BitAnd<TraitSet> for TraitSet {
    type Output = TraitSet;

    fn bitand(self, rhs: TraitSet) -> Self::Output {
        unsafe { std::mem::transmute(self as u8 & rhs as u8) }
    }
}

impl std::ops::BitOr<TraitSet> for TraitSet {
    type Output = TraitSet;

    fn bitor(self, rhs: TraitSet) -> Self::Output {
        unsafe { std::mem::transmute(self as u8 | rhs as u8) }
    }
}

impl TraitSet {
    pub fn into_label_vec(self) -> Vec<Label> {
        match self {
            TraitSet::Empty => vec![],
            TraitSet::Debug => vec![Label::from("Debug")],
            TraitSet::Clone => vec![Label::from("Clone")],
            TraitSet::DebugClone => vec![Label::from("Debug"), Label::from("Clone")],
            TraitSet::Copy => vec![Label::from("Copy"), Label::from("Clone")],
            TraitSet::DebugCopy => vec![
                Label::from("Debug"),
                Label::from("Copy"),
                Label::from("Clone"),
            ],
        }
    }

    pub fn into_attr(self) -> RustAttr {
        RustAttr::DeriveTraits(DeclDerives(self.into_label_vec()))
    }
}

impl RustItem {
    /// Promotes a standalone declaration to a top-level item with implicitly 'default' visibility (i.e. `pub(self)`).
    ///
    /// Attaches the specified set of derive-traits `traits` to the declaration if it is a type definition.
    ///
    /// Currently, this argument is ignored for functions.
    pub fn from_decl_with_traits(decl: RustDecl, traits: TraitSet) -> Self {
        let attrs = match decl {
            RustDecl::TypeDef(..) => vec![traits.into_attr()],
            RustDecl::Function(_) => Vec::new(),
        };
        Self {
            attrs,
            vis: Default::default(),
            doc_comment: None,
            decl,
        }
    }

    /// Promotes a standalone declaration to a top-level item with explicit 'pub' visibility.
    ///
    /// Attaches the specified set of derive-traits `traits` to the declaration if it is a type definition.
    ///
    /// Currently, this argument is ignored for functions.
    pub fn pub_decl_with_traits(decl: RustDecl, traits: TraitSet) -> Self {
        let attrs = match decl {
            RustDecl::TypeDef(..) => vec![traits.into_attr()],
            RustDecl::Function(_) => Vec::new(),
        };
        Self {
            attrs,
            vis: Visibility::Public,
            doc_comment: None,
            decl,
        }
    }

    /// Promotes a type declaration to a top-level item with implicit 'pub(self)' visibility and the default set of derive-traits
    /// (currently, `Debug` and `Clone`).
    ///
    /// For more fine-control over the traits that are derived, use [`from_decl_with_traits`](Self::from_decl_with_traits).
    #[inline]
    pub fn from_decl(decl: RustDecl) -> Self {
        Self::from_decl_with_traits(decl, TraitSet::default())
    }

    /// Promotes a type declaration to a top-level item with implicit 'pub(self)' visibility and the default set of derive-traits
    /// (currently, `Debug` and `Clone`).
    ///
    /// For more fine-control over the traits that are derived, use [`pub_decl_with_traits`](Self::pub_decl_with_traits).
    #[inline]
    #[allow(dead_code)]
    pub fn pub_decl(decl: RustDecl) -> Self {
        Self::pub_decl_with_traits(decl, TraitSet::default())
    }

    pub fn with_comment<Text: IntoLabel>(
        mut self,
        comment: impl IntoIterator<Item = Text>,
    ) -> Self {
        if let Some(doc_comment) = self.doc_comment.as_mut() {
            // We only want to call this once because doc-comments are exclusive
            unreachable!("RustItem already has a doc comment: {doc_comment:?}");
        };
        self.doc_comment = Some(RustDocComment {
            lines: comment.into_iter().map(Text::into).collect::<Vec<Label>>(),
        });
        self
    }
}

impl ToFragment for RustItem {
    fn to_fragment(&self) -> Fragment {
        let mut builder = FragmentBuilder::new();
        if let Some(com) = &self.doc_comment {
            builder.push(com.to_fragment().cat_break());
        }
        for attr in self.attrs.iter() {
            builder.push(attr.to_fragment().cat_break());
        }
        builder
            .finalize()
            .cat(self.vis.add_vis(self.decl.to_fragment()))
    }
}

type TraitName = Label;

#[derive(Debug, Clone)]
pub enum RustAttr {
    DeriveTraits(DeclDerives),
}

impl ToFragment for RustAttr {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustAttr::DeriveTraits(derives) => derives.to_fragment(),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct DeclDerives(Vec<TraitName>);

impl ToFragment for DeclDerives {
    fn to_fragment(&self) -> Fragment {
        let DeclDerives(traits) = self;
        if traits.is_empty() {
            Fragment::Empty
        } else {
            ToFragment::paren_list(traits)
                .delimit(Fragment::string("#[derive"), Fragment::Char(']'))
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum RustDecl {
    TypeDef(Label, RustTypeDecl),
    Function(RustFn),
}

impl RustDecl {
    #[expect(dead_code)]
    pub fn type_def(lab: impl IntoLabel, def: RustTypeDef) -> Self {
        Self::TypeDef(lab.into(), RustTypeDecl { def, lt: None })
    }
}

impl ToFragment for RustDecl {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustDecl::TypeDef(name, RustTypeDecl { def, lt }) => {
                let identifier = if let Some(lt) = lt {
                    name.to_fragment().cat(
                        lt.to_fragment()
                            .delimit(Fragment::Char('<'), Fragment::Char('>')),
                    )
                } else {
                    name.to_fragment()
                };
                let keyword = Fragment::string(def.keyword_for());
                keyword
                    .intervene(Fragment::Char(' '), identifier)
                    .intervene(Fragment::Char(' '), def.to_fragment())
            }
            RustDecl::Function(fn_def) => fn_def.to_fragment(),
        }
    }
}

/// Generic representation for a list of lifetime- and type-parameters, generic over the types used to represent
/// each of those two components
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct RustParams<Lt, Ty> {
    pub(crate) lt_params: Vec<Lt>,
    pub(crate) ty_params: Vec<Ty>,
}

impl<Lt, Ty> Default for RustParams<Lt, Ty> {
    fn default() -> Self {
        Self {
            lt_params: Default::default(),
            ty_params: Default::default(),
        }
    }
}

/// Representation of the abstract, name-only parameters used in the definition of a type or function
pub(crate) type DefParams = RustParams<Label, Label>;
/// Representation of the concrete, specific parameters used when locally invoking a function or qualifying a type
pub(crate) type UseParams = RustParams<RustLt, RustType>;

impl<Lt, Ty> RustParams<Lt, Ty> {
    pub fn new() -> Self {
        Self {
            lt_params: Vec::new(),
            ty_params: Vec::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.lt_params.is_empty() && self.ty_params.is_empty()
    }

    pub(crate) fn from_lt(lt: Lt) -> Self {
        Self {
            lt_params: vec![lt],
            ty_params: Vec::new(),
        }
    }
}

impl<Lt, Ty> RustParams<Lt, Ty> {
    pub fn push_lifetime(&mut self, lt: impl Into<Lt>) {
        self.lt_params.push(lt.into())
    }
}

impl<Lt, Ty> ToFragment for RustParams<Lt, Ty>
where
    Lt: ToFragment,
    Ty: ToFragment,
{
    fn to_fragment(&self) -> Fragment {
        let all = self
            .lt_params
            .iter()
            .map(Lt::to_fragment)
            .chain(self.ty_params.iter().map(Ty::to_fragment));
        Fragment::seq(all, Some(Fragment::string(", ")))
            .delimit(Fragment::Char('<'), Fragment::Char('>'))
    }
}

/// Representation for the signature, both arguments and return type, for a non-closure function
#[derive(Clone, Debug)]
pub(crate) struct FnSig {
    /// List of arguments with accompanying type annotations
    args: Vec<(Label, RustType)>,
    /// Return type (assumed to be unit if omitted)
    ret: Option<RustType>,
}

impl FnSig {
    pub fn new(args: Vec<(Label, RustType)>, ret: Option<RustType>) -> Self {
        Self { args, ret }
    }
}

impl ToFragment for (Label, RustType) {
    fn to_fragment(&self) -> Fragment {
        self.0
            .to_fragment()
            .intervene(Fragment::string(": "), self.1.to_fragment())
    }
}

impl ToFragment for FnSig {
    fn to_fragment(&self) -> Fragment {
        ToFragment::paren_list(self.args.iter()).intervene(
            Fragment::string(" -> "),
            Fragment::opt(self.ret.as_ref(), RustType::to_fragment),
        )
    }
}

/// Representation for standalone functions declared either inline or top-level in Rust
#[derive(Clone, Debug)]
pub(crate) struct RustFn {
    /// Function name
    name: Label,
    /// Optional list of generic lifetimes and types for the function declaration
    params: Option<DefParams>,
    /// Signature, including both input parameters and return type
    sig: FnSig,
    /// List of statements comprising the body of the function
    body: Vec<RustStmt>,
}

impl RustFn {
    pub fn new(name: Label, params: Option<DefParams>, sig: FnSig, body: Vec<RustStmt>) -> Self {
        Self {
            name,
            params,
            sig,
            body,
        }
    }
}

impl ToFragment for RustFn {
    fn to_fragment(&self) -> Fragment {
        let f_name = Fragment::string(self.name.clone());
        let f_params = Fragment::opt(self.params.as_ref(), RustParams::to_fragment);
        let f_sig = self.sig.to_fragment();
        let body = RustStmt::block(self.body.iter());
        Fragment::string("fn ")
            .cat(f_name)
            .cat(f_params)
            .cat(f_sig)
            .cat(Fragment::Char(' '))
            .cat(body)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RustTypeDecl {
    pub(crate) def: RustTypeDef,
    pub(crate) lt: Option<RustLt>,
}

impl RustTypeDecl {
    pub(crate) fn lt_param(&self) -> Option<&RustLt> {
        self.lt.as_ref()
    }
}

/// Representation for both `struct` and `enum`-keyword declarations.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RustTypeDef {
    Enum(Vec<RustVariant>),
    Struct(RustStruct),
}

impl RustTypeDef {
    /// Determines the Rust keyword associated with a particular type-definition, being one of `enum` or `struct`.
    pub const fn keyword_for(&self) -> &'static str {
        match self {
            Self::Enum(..) => "enum",
            Self::Struct(..) => "struct",
        }
    }

    pub fn to_fragment(&self) -> Fragment {
        match self {
            RustTypeDef::Enum(vars) => {
                let iter = vars.iter().map(RustVariant::to_fragment);
                let inner = Fragment::seq(iter, Some(Fragment::string(", ")));
                inner.delimit(Fragment::string("{ "), Fragment::string(" }"))
            }
            RustTypeDef::Struct(str) => str.to_fragment(),
        }
    }

    /// Rough heuristic to determine whether a `RustTypeDef` can derive `Copy` without resulting in a compiler error.
    pub(crate) fn can_be_copy(&self) -> bool {
        match self {
            RustTypeDef::Enum(variants) => variants.iter().all(|v| v.can_be_copy()),
            RustTypeDef::Struct(struct_def) => struct_def.can_be_copy(),
        }
    }
}

/// Entry-type for representing type-level constructions in Rust, for use in function signatures and return types,
/// the field-types of struct definitions, and expression-level type annotations.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RustType {
    Atom(AtomType),
    AnonTuple(Vec<RustType>),
    /// Catch-all for generics that we may not be able or willing to hardcode
    Verbatim(Label, UseParams),
    ReadArray(RustLt, MarkerType),
}

impl RustType {
    pub const UNIT: RustType = RustType::Atom(AtomType::Prim(PrimType::Unit));

    /// Returns the RustType representation of an externally-defined and imported type `<name>`.
    pub fn imported(name: impl Into<Label>) -> Self {
        Self::Atom(AtomType::TypeRef(LocalType::External(name.into())))
    }

    /// Returns the RustType representation of a locally-defined type whose index in the code-generation table
    /// is `ix` and whose identifier is `name`.
    pub fn defined(ix: usize, name: impl Into<Label>, params: UseParams) -> Self {
        Self::Atom(AtomType::TypeRef(LocalType::LocalDef(
            ix,
            name.into(),
            params,
        )))
    }

    /// Maps the provided RustType according to the transformation `T -> Vec<T>`
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn vec_of(inner: Self) -> Self {
        Self::Atom(AtomType::Comp(CompType::Vec(Box::new(inner))))
    }

    /// Constructs an anonymous tuple-type representative over an iterable collection of RustType elements.
    pub fn anon_tuple(elts: impl IntoIterator<Item = Self>) -> Self {
        Self::AnonTuple(elts.into_iter().collect())
    }

    /// Returns a RustType given a verbatim string-form of the type-level constructor to use,
    /// with an optional list of generic arguments to parameterize it with.
    pub fn verbatim(con: impl Into<Label>, params: Option<UseParams>) -> Self {
        Self::Verbatim(con.into(), params.unwrap_or_default())
    }

    /// Predicate function that determines whether values of RustType `self` should be borrowed
    /// before being used in signatures of, or when passed in as arguments to, top-level decoder functions.
    pub fn should_borrow_for_arg(&self) -> bool {
        match self {
            RustType::Atom(ref atom_type) => match atom_type {
                AtomType::Comp(ct) => match ct {
                    // REVIEW - this may lead to code divergence and may not be stable...
                    CompType::Vec(..) => true,
                    CompType::Borrow(..) => false,
                    CompType::Option(t) => t.should_borrow_for_arg(),
                    CompType::Result(t_ok, _t_err) => t_ok.should_borrow_for_arg(),
                    CompType::RawSlice(..) => {
                        unreachable!("raw slice should always be behind a ref")
                    }
                },
                AtomType::TypeRef(local) => match local {
                    // REVIEW - shallow wrappers around vec should be treated as if vec, but that is difficult to achieve without more state-info from generation process
                    LocalType::LocalDef(_ix, ..) => false,
                    LocalType::External(..) => false,
                },
                AtomType::Prim(..) => false,
            },
            // REVIEW - are there cases where we want to selectively borrow anon-tuples (and if so, distributive or unified)?
            RustType::AnonTuple(_elts) => false,
            RustType::Verbatim(..) => false,
            // FIXME - is this correct?
            RustType::ReadArray(..) => !READ_ARRAY_IS_COPY,
        }
    }

    pub fn selective_borrow(lt: Option<RustLt>, m: Mut, ty: RustType) -> Self {
        if ty.should_borrow_for_arg() {
            Self::borrow_of(lt, m, ty)
        } else {
            ty
        }
    }

    /// Constructs a `RustType` representing `&'a (mut|) T` from parameters representing `'a` (optional),
    /// the mutability of the reference, and `T`, respectively.
    pub fn borrow_of(lt: Option<RustLt>, m: Mut, ty: RustType) -> Self {
        let ty = if m.is_mutable() { ty } else { ty.deref_tgt() };
        Self::Atom(AtomType::Comp(CompType::Borrow(lt, m, Box::new(ty))))
    }

    /// Constructs a `RustType` representing `Result<T, E>` from parameters representing `T` and `E`, respectively.
    pub fn result_of(ok_type: RustType, err_type: RustType) -> RustType {
        Self::Atom(AtomType::Comp(CompType::Result(
            Box::new(ok_type),
            Box::new(err_type),
        )))
    }

    pub fn try_as_prim(&self) -> Option<PrimType> {
        match self {
            RustType::Atom(AtomType::Prim(pt)) => Some(*pt),
            _ => None,
        }
    }

    /// Returns `true` if seq-formats ([`Format::Sequence`]) of type `Seq(<self>)` should prefer to use
    /// fixed-size arrays (`[T; N]`) over vectors (`Vec<T>`) during construction. An additional parameter,
    /// the length of the sequence (`len`), is passed in to guide the decision, as simple types can be
    /// preferable as vectors depending more on the length of the sequence than anything else.
    pub(crate) fn prefer_array(&self, _n: usize) -> bool {
        // REVIEW - currently, we would need to orchestrate the correct decision at multiple layers, which would take a lot of work
        false
    }

    /// Returns `true` if `self` is a known-`Copy` `RustType`.
    ///
    /// # Note
    ///
    /// Though superficially similar to [`can_be_copy`], these methods serve starkly different purposes.
    ///
    /// The in-crate use-case for `RustType::is_copy` is as a direct heuristic on pattern-introspection on
    /// `Some` (or similar) should be destructive (when `true`) or referential (when `false`) to allow for
    /// the more natural type of the bound value to be available in the rhs block without having to explicitly
    /// dereference, clone, or otherwise perturb the usage-sites of the bound variables.
    ///
    /// In contrast, the in-crate use-case for `RustType::can_be_copy` is to determine whether the presence
    /// of a `RustType` (i.e. the received `self`) as a recursive element within the body of some abstract
    /// `RustTypeDef` would preclude a `Copy` implementation on that definition.
    pub(crate) fn is_copy(&self) -> bool {
        match self.try_as_prim() {
            // NOTE - all PrimTypes are Copy, and only PrimTypes care specifically about being owned or referenced in terms of what operations we perform on them in the RHS
            Some(_pt) => true,
            _ => false,
        }
    }

    /// Returns the most natural form of `self` to be used when being borrowed, as
    /// in `[T]` to replace `Vec<T>`.
    fn deref_tgt(self) -> RustType {
        match self {
            RustType::Atom(AtomType::Comp(CompType::Vec(t))) => {
                RustType::Atom(AtomType::Comp(CompType::RawSlice(t)))
            }
            this => this,
        }
    }

    pub(crate) fn lt_param(&self) -> Option<&RustLt> {
        match self {
            RustType::Atom(atom_type) => atom_type.lt_param(),
            RustType::AnonTuple(rust_types) => rust_types.iter().find_map(|t| t.lt_param()),
            RustType::Verbatim(_, rust_params) => rust_params.lt_params.first(),
            RustType::ReadArray(lt, _) => Some(lt),
        }
    }
}

impl RustType {
    /// Conservative heuristic for determining whether it is possible to implement `Copy` on a `RustTypeDef` containing embedded values of this `RustType` without
    /// resulting in a compiler error.
    ///
    /// Returns `true` if `self` is a primitive type, an immutable reference, or if it is an anonymous tuple or `Result` consisting only of such value-types.
    ///
    /// Because inference is performed locally, no embedded `LocalDef` values are considered to be Copyable, even when they are locally-defined with a `#[derive(Copy)]` attribute.
    pub(crate) fn can_be_copy(&self) -> bool {
        match self {
            RustType::Atom(at) => match at {
                AtomType::Prim(..) => true,
                // Without passing around high-level type-maps, we can't check any externally-defined or local ad-hoc types for Copy-safety
                AtomType::TypeRef(..) => false,
                AtomType::Comp(ct) => match ct {
                    CompType::Vec(_) => false,
                    CompType::Option(t) => t.can_be_copy(),
                    CompType::Result(t_ok, t_err) => t_ok.can_be_copy() && t_err.can_be_copy(),
                    CompType::Borrow(_lt, m, _t) => !m.is_mutable(),
                    CompType::RawSlice(_) => {
                        unreachable!("raw slice should not exist outside of ref context")
                    }
                },
            },
            RustType::AnonTuple(args) => args.iter().all(|t| t.can_be_copy()),
            // Without lexical analysis rules, we have no good way to determine whether a verbatim-injected type-name is Copy-safe or not
            RustType::Verbatim(..) => false,
            RustType::ReadArray(..) => READ_ARRAY_IS_COPY,
        }
    }
}

impl ToFragment for RustType {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustType::Atom(at) => at.to_fragment(),
            RustType::AnonTuple(args) => {
                let inner = args.iter().map(|elt| elt.to_fragment());
                let mut elems = Fragment::seq(inner, Some(Fragment::string(", ")));
                // NOTE - Rust 1-tuples need an explicit ',' after the sole element
                if args.len() == 1 {
                    elems.append(Fragment::Char(','));
                }
                elems.delimit(Fragment::Char('('), Fragment::Char(')'))
            }
            RustType::Verbatim(con, params) => con.to_fragment().cat(params.to_fragment()),
            RustType::ReadArray(lt, mt) => {
                let params = RustParams {
                    lt_params: vec![lt.clone()],
                    ty_params: vec![mt.clone()],
                };
                Fragment::string("ReadArray").cat(params.to_fragment())
            }
        }
    }
}

impl ToFragmentExt for RustType {
    // FIXME - this impl is only to fix test cases
    fn to_fragment_precedence(&self, _prec: Precedence) -> Fragment {
        self.to_fragment()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RustStruct {
    Record(Vec<(Label, RustType)>),
}

impl RustStruct {
    /// Rough heuristic to determine whether a `RustStruct` can derive `Copy` without resulting in a compiler error.
    pub(crate) fn can_be_copy(&self) -> bool {
        match self {
            RustStruct::Record(flds) => flds.iter().all(|(_, t)| t.can_be_copy()),
        }
    }
}

impl ToFragment for RustStruct {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustStruct::Record(flds) => {
                <(Label, RustType)>::block_sep(flds.iter(), Fragment::Char(','))
            }
        }
    }
}

impl ToFragment for Label {
    /// Special-case for sanitization of labels-as-identifiers rather than a direct identity-function.
    fn to_fragment(&self) -> Fragment {
        Fragment::String(sanitize_label(self))
    }
}

/// Sanitizes a label such that it can be used as an identifier.
///
/// Crucially, this function is invariant and deterministic, so any two instances
/// of a common pre-image will always yield identical images, both within each
/// run of the code-generation phase and between such runs.
pub(crate) fn sanitize_label(label: &Label) -> Label {
    if label.chars().enumerate().all(|(ix, c)| is_valid(ix, c)) {
        remap(label.clone())
    } else {
        remap(Label::from(replace_bad(label.as_ref())))
    }
}

/// Adds a `r#` prefix to any reserved Rust keywords that would be invalid as identifiers.
fn remap(input: Label) -> Label {
    match input.as_ref() {
        "as" | "async" | "await" | "break" | "const" | "continue" | "crate" | "dyn" | "else"
        | "enum" | "extern" | "false" | "fn" | "for" | "if" | "impl" | "in" | "let" | "loop"
        | "match" | "mod" | "move" | "mut" | "pub" | "ref" | "return" | "self" | "Self"
        | "static" | "struct" | "super" | "trait" | "true" | "type" | "unsafe" | "use"
        | "where" | "while" | "abstract" | "become" | "box" | "do" | "final" | "macro"
        | "override" | "priv" | "try" | "typeof" | "unsized" | "virtual" | "yield" => {
            Label::from(format!("r#{}", input))
        }
        _ => input,
    }
}

/// Returns `true` if the given character at the given index is valid in Rust-compatible identifiers
fn is_valid(ix: usize, c: char) -> bool {
    match c {
        '-' | '.' | ' ' | '\t' => false,
        '0'..='9' => ix != 0,
        _ => true,
    }
}

/// Sanitizes a given identifier by replacing all runs of one or more disallowed characters with a single underscore,
/// and preceding any initial ASCII digits with a leading underscore
fn replace_bad(input: &str) -> String {
    let mut ret = String::new();
    let mut dashed = false;
    for c in input.chars() {
        if c.is_ascii_digit() && ret.is_empty() {
            ret.push('_');
            ret.push(c);
            dashed = false;
        } else if is_valid(ret.len(), c) {
            ret.push(c);
            dashed = false;
        } else if !dashed {
            ret.push('_');
            dashed = true;
        }
    }
    ret
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RustVariant {
    Unit(Label),
    Tuple(Label, Vec<RustType>),
}

impl RustVariant {
    pub(crate) fn get_label(&self) -> &Label {
        match self {
            RustVariant::Unit(lab) | RustVariant::Tuple(lab, _) => lab,
        }
    }

    /// Rough heuristic to determine whether an enum containing the given `RustVariant` can derive `Copy` without resulting in a compiler error.
    ///
    /// As a heuristic, this function is local-only, meaning a result of `true` merely indicates that the provided `RustVariant` itself is Copy-able,
    /// but not that the overall enum is necessarily Copyable given its other variants.
    pub(crate) fn can_be_copy(&self) -> bool {
        match self {
            RustVariant::Unit(_) => true,
            RustVariant::Tuple(_, elts) => elts.iter().all(RustType::can_be_copy),
        }
    }

    pub(crate) fn lt_param(&self) -> Option<&RustLt> {
        match self {
            RustVariant::Unit(_) => None,
            RustVariant::Tuple(_, elts) => elts.iter().find_map(RustType::lt_param),
        }
    }
}

impl ToFragment for RustVariant {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustVariant::Unit(lab) => lab.to_fragment(),
            RustVariant::Tuple(lab, args) => {
                lab.to_fragment().cat(RustType::paren_list(args.iter()))
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum AtomType<T = Box<RustType>, U = T>
where
    T: Sized,
    U: Sized,
{
    TypeRef(LocalType),
    Prim(PrimType),
    Comp(CompType<T, U>),
}

impl AtomType {
    fn lt_param(&self) -> Option<&RustLt> {
        match self {
            AtomType::TypeRef(local_type) => match local_type {
                LocalType::LocalDef(_, _, params) => params.lt_params.first(),
                _ => None,
            },
            AtomType::Prim(..) => None,
            AtomType::Comp(ct) => ct.lt_param(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum LocalType {
    LocalDef(usize, Label, UseParams),
    External(Label),
}

// impl AsRef<Label> for LocalType {
//     fn as_ref(&self) -> &Label {
//         match self {
//             LocalType::External(lab) | LocalType::LocalDef(_, lab) => lab,
//         }
//     }
// }

impl ToFragment for LocalType {
    fn to_fragment(&self) -> Fragment {
        match self {
            Self::LocalDef(_, lab, params) => {
                if params.is_empty() {
                    lab.to_fragment()
                } else {
                    lab.to_fragment().cat(params.to_fragment())
                }
            }
            Self::External(lab) => lab.to_fragment(),
        }
    }
}

impl<T, U> ToFragment for AtomType<T, U>
where
    T: Sized + ToFragment,
    U: Sized + ToFragment,
{
    fn to_fragment(&self) -> Fragment {
        match self {
            AtomType::TypeRef(local_type) => local_type.to_fragment(),
            AtomType::Prim(pt) => pt.to_fragment(),
            AtomType::Comp(ct) => ct.to_fragment(),
        }
    }
}

/// Representatives for `smallsorts::binary::*` marker-types.
#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
pub(crate) enum MarkerType {
    U8,
    U16Be,
    U32Be,
    U64Be,
}

impl From<BaseKind> for MarkerType {
    fn from(bk: BaseKind) -> Self {
        match bk {
            BaseKind::U8 => MarkerType::U8,
            BaseKind::U16 => MarkerType::U16Be,
            BaseKind::U32 => MarkerType::U32Be,
            BaseKind::U64 => MarkerType::U64Be,
        }
    }
}

impl ToFragment for MarkerType {
    fn to_fragment(&self) -> Fragment {
        match self {
            MarkerType::U8 => Fragment::string("U8"),
            MarkerType::U16Be => Fragment::string("U16Be"),
            MarkerType::U32Be => Fragment::string("U32Be"),
            MarkerType::U64Be => Fragment::string("U64Be"),
        }
    }
}

#[derive(Debug)]
pub struct InvalidMarkerTypeError(PrimType);

impl std::fmt::Display for InvalidMarkerTypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid marker type: {:?}", self.0)
    }
}

impl std::error::Error for InvalidMarkerTypeError {}

impl TryFrom<PrimType> for MarkerType {
    type Error = InvalidMarkerTypeError;

    fn try_from(pt: PrimType) -> Result<Self, Self::Error> {
        match pt {
            PrimType::U8 => Ok(MarkerType::U8),
            PrimType::U16 => Ok(MarkerType::U16Be),
            PrimType::U32 => Ok(MarkerType::U32Be),
            PrimType::U64 => Ok(MarkerType::U64Be),
            _ => Err(InvalidMarkerTypeError(pt)),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
pub(crate) enum PrimType {
    Unit,
    U8,
    U16,
    U32,
    U64,
    Bool,
    Char,
    Usize,
}

impl PrimType {
    fn is_numeric(&self) -> bool {
        matches!(
            self,
            PrimType::U8 | PrimType::U16 | PrimType::U32 | PrimType::U64 | PrimType::Usize
        )
    }

    fn compare_width(pt0: PrimType, pt1: PrimType) -> Option<Ordering> {
        match (pt0, pt1) {
            (PrimType::Unit, _) | (_, PrimType::Unit) => None,
            (PrimType::Char, _) | (_, PrimType::Char) => None,
            (PrimType::Bool, _) | (_, PrimType::Bool) => None,
            (PrimType::U8, PrimType::U8) => Some(Ordering::Equal),
            (PrimType::U8, _) => Some(Ordering::Less),
            (_, PrimType::U8) => Some(Ordering::Greater),
            (PrimType::U16, PrimType::U16) => Some(Ordering::Equal),
            (PrimType::U16, _) => Some(Ordering::Less),
            (_, PrimType::U16) => Some(Ordering::Greater),
            (PrimType::U32, PrimType::U32) => Some(Ordering::Equal),
            (PrimType::U32, _) => Some(Ordering::Less),
            (_, PrimType::U32) => Some(Ordering::Greater),
            (PrimType::U64 | PrimType::Usize, PrimType::U64 | PrimType::Usize) => {
                Some(Ordering::Equal)
            }
        }
    }
}

impl From<BaseType> for PrimType {
    fn from(value: BaseType) -> Self {
        match value {
            BaseType::Bool => PrimType::Bool,
            BaseType::U8 => PrimType::U8,
            BaseType::U16 => PrimType::U16,
            BaseType::U32 => PrimType::U32,
            BaseType::U64 => PrimType::U64,
            BaseType::Char => PrimType::Char,
        }
    }
}

impl ToFragment for PrimType {
    fn to_fragment(&self) -> Fragment {
        Fragment::string(match self {
            PrimType::Unit => "()",
            PrimType::U8 => "u8",
            PrimType::U16 => "u16",
            PrimType::U32 => "u32",
            PrimType::U64 => "u64",
            PrimType::Bool => "bool",
            PrimType::Char => "char",
            PrimType::Usize => "usize",
        })
    }
}

/// AST type for Rust Lifetimes
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RustLt {
    /// Label contents should contain leading `'`
    Parametric(Label),
}

impl AsRef<Label> for RustLt {
    fn as_ref(&self) -> &Label {
        match self {
            RustLt::Parametric(lab) => lab,
        }
    }
}

impl ToFragment for RustLt {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustLt::Parametric(lab) => lab.to_fragment(),
        }
    }
}

/// Compound type that is either unary over `T` or binary over `T, U`.
///
/// If not specified, `U` will implicitly have the same type as `T`
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum CompType<T = Box<RustType>, U = T> {
    Vec(T),
    RawSlice(T),
    Option(T),
    Result(T, U),
    Borrow(Option<RustLt>, Mut, T),
}

impl CompType {
    fn lt_param(&self) -> Option<&RustLt> {
        match self {
            CompType::Vec(t) => t.lt_param(),
            CompType::RawSlice(t) => t.lt_param(),
            CompType::Option(t) => t.lt_param(),
            CompType::Result(t, _) => t.lt_param(),
            CompType::Borrow(rust_lt, _, t) => rust_lt.as_ref().or_else(|| t.lt_param()),
        }
    }
}

impl<T, U> ToFragment for CompType<T, U>
where
    T: ToFragment,
    U: ToFragment,
{
    fn to_fragment(&self) -> Fragment {
        match self {
            CompType::Option(inner) => {
                let tmp = inner.to_fragment();
                tmp.delimit(Fragment::string("Option<"), Fragment::Char('>'))
            }
            CompType::Vec(inner) => {
                let tmp = inner.to_fragment();
                tmp.delimit(Fragment::string("Vec<"), Fragment::Char('>'))
            }
            CompType::RawSlice(inner) => {
                let tmp = inner.to_fragment();
                tmp.delimit(Fragment::Char('['), Fragment::Char(']'))
            }
            CompType::Result(ok, err) => {
                let tmp = ok
                    .to_fragment()
                    .intervene(Fragment::string(", "), err.to_fragment());
                tmp.delimit(Fragment::string("Result<"), Fragment::Char('>'))
            }
            CompType::Borrow(lt, _mut, ty) => {
                let f_lt = Fragment::opt(lt.as_ref(), <RustLt as ToFragment>::to_fragment);
                let f_mut = _mut.to_fragment();
                let f_aux = Fragment::intervene(f_lt, Fragment::Char(' '), f_mut);
                let f_body = Fragment::intervene(f_aux, Fragment::Char(' '), ty.to_fragment());
                Fragment::cat(Fragment::Char('&'), f_body)
            }
        }
    }
}

impl From<PrimType> for AtomType {
    fn from(value: PrimType) -> Self {
        Self::Prim(value)
    }
}

impl From<CompType<Box<RustType>>> for AtomType {
    fn from(value: CompType<Box<RustType>>) -> Self {
        Self::Comp(value)
    }
}

impl From<AtomType> for RustType {
    fn from(value: AtomType) -> Self {
        Self::Atom(value)
    }
}

impl From<PrimType> for RustType {
    fn from(value: PrimType) -> Self {
        Self::from(AtomType::from(value))
    }
}

impl From<CompType<Box<RustType>>> for RustType {
    fn from(value: CompType<Box<RustType>>) -> Self {
        Self::from(AtomType::from(value))
    }
}

impl TryFrom<ValueType> for RustType {
    type Error = ValueType;

    fn try_from(value: ValueType) -> Result<Self, Self::Error> {
        match value {
            ValueType::Empty => Ok(RustType::UNIT),
            ValueType::Base(BaseType::Bool) => Ok(PrimType::Bool.into()),
            ValueType::Base(BaseType::U8) => Ok(PrimType::U8.into()),
            ValueType::Base(BaseType::U16) => Ok(PrimType::U16.into()),
            ValueType::Base(BaseType::U32) => Ok(PrimType::U32.into()),
            ValueType::Base(BaseType::U64) => Ok(PrimType::U64.into()),
            ValueType::Base(BaseType::Char) => Ok(PrimType::Char.into()),
            ValueType::Tuple(mut vs) => {
                let mut buf = Vec::with_capacity(vs.len());
                for v in vs.drain(..) {
                    buf.push(Self::try_from(v)?);
                }
                Ok(Self::AnonTuple(buf))
            }
            ValueType::Seq(t) => {
                let inner = Self::try_from(t.as_ref().clone())?;
                Ok(CompType::<Box<RustType>>::Vec(Box::new(inner)).into())
            }
            ValueType::Option(t) => {
                let inner = Self::try_from(t.as_ref().clone())?;
                Ok(RustType::Atom(AtomType::Comp(CompType::Option(Box::new(
                    inner,
                )))))
            }
            ValueType::Any | ValueType::Record(..) | ValueType::Union(..) => Err(value),
        }
    }
}

#[derive(Clone, Copy, Default, Eq, PartialEq, Debug, PartialOrd, Ord, Hash)]
pub(crate) enum Mut {
    #[default]
    Immutable,
    Mutable,
}

impl Mut {
    pub fn is_mutable(&self) -> bool {
        matches!(self, Self::Mutable)
    }
}

impl ToFragment for Mut {
    fn to_fragment(&self) -> Fragment {
        match self {
            Mut::Mutable => Fragment::string("mut"),
            Mut::Immutable => Fragment::Empty,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum RustEntity {
    Local(Label),
    Scoped(Vec<Label>, Label),
}

impl RustEntity {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustEntity::Local(v) => v.to_fragment(),
            RustEntity::Scoped(path, v) => Fragment::seq(
                path.iter()
                    .chain(std::iter::once(v))
                    .map(|scope| scope.to_fragment()),
                Some(Fragment::string("::")),
            ),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SubIdent {
    ByPosition(usize),
    ByName(Label),
}

impl ToFragment for SubIdent {
    fn to_fragment(&self) -> Fragment {
        match self {
            SubIdent::ByPosition(ix) => Fragment::DisplayAtom(Rc::new(*ix)),
            SubIdent::ByName(lab) => lab.to_fragment(),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum RustPrimLit {
    Boolean(bool),
    Numeric(RustNumLit),
    Char(char),
    String(Label),
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum RustNumLit {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    Usize(usize),
}

impl From<RustNumLit> for usize {
    fn from(value: RustNumLit) -> Self {
        match value {
            RustNumLit::U8(n) => n as usize,
            RustNumLit::U16(n) => n as usize,
            RustNumLit::U32(n) => n as usize,
            RustNumLit::U64(n) => n as usize,
            RustNumLit::Usize(n) => n,
        }
    }
}

impl ToFragment for RustNumLit {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustNumLit::U8(n) => Fragment::string(format!("{n}u8")),
            RustNumLit::U16(n) => Fragment::string(format!("{n}u16")),
            RustNumLit::U32(n) => Fragment::string(format!("{n}u32")),
            RustNumLit::U64(n) => Fragment::string(format!("{n}u64")),
            RustNumLit::Usize(n) => Fragment::string(format!("{n}")),
        }
    }
}

impl ToFragment for RustPrimLit {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustPrimLit::Boolean(b) => Fragment::DisplayAtom(Rc::new(*b)),
            RustPrimLit::Numeric(n) => n.to_fragment(),
            RustPrimLit::Char(c) => Fragment::DisplayAtom(Rc::new(*c))
                .delimit(Fragment::Char('\''), Fragment::Char('\'')),
            RustPrimLit::String(s) => Fragment::String(s.clone())
                .delimit(Fragment::string("r#\""), Fragment::string("\"#")),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum MethodSpecifier {
    Arbitrary(SubIdent),
    Common(CommonMethod),
}

impl MethodSpecifier {
    pub const LEN: Self = Self::Common(CommonMethod::Len);
    pub const IS_EMPTY: Self = Self::Common(CommonMethod::IsEmpty);
}

impl From<SubIdent> for MethodSpecifier {
    fn from(v: SubIdent) -> Self {
        Self::Arbitrary(v)
    }
}

impl From<CommonMethod> for MethodSpecifier {
    fn from(v: CommonMethod) -> Self {
        Self::Common(v)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum CommonMethod {
    Len,
    IsEmpty,
}

impl CommonMethod {
    pub(crate) fn try_get_return_primtype(&self) -> Option<PrimType> {
        match self {
            CommonMethod::Len => Some(PrimType::Usize),
            CommonMethod::IsEmpty => Some(PrimType::Bool),
        }
    }
}

impl ToFragment for CommonMethod {
    fn to_fragment(&self) -> Fragment {
        match self {
            CommonMethod::Len => Fragment::string("len"),
            CommonMethod::IsEmpty => Fragment::string("is_empty"),
        }
    }
}

impl ToFragment for MethodSpecifier {
    fn to_fragment(&self) -> Fragment {
        match self {
            MethodSpecifier::Arbitrary(v) => v.to_fragment(),
            MethodSpecifier::Common(v) => v.to_fragment(),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum StructExpr {
    EmptyExpr,
    RecordExpr(Vec<(Label, Option<RustExpr>)>),
    TupleExpr(Vec<RustExpr>),
}

impl ToFragment for StructExpr {
    fn to_fragment(&self) -> Fragment {
        match self {
            StructExpr::RecordExpr(fields) => Fragment::seq(
                fields.iter().map(|(lab, expr)| {
                    Fragment::intervene(
                        lab.to_fragment(),
                        Fragment::string(": "),
                        expr.as_ref().map_or(Fragment::Empty, |x| {
                            x.to_fragment_precedence(Precedence::Top)
                        }),
                    )
                }),
                Some(Fragment::string(", ")),
            )
            .delimit(Fragment::string(" { "), Fragment::string(" }")),
            StructExpr::TupleExpr(elts) => RustExpr::paren_list_prec(elts, Precedence::Top),
            StructExpr::EmptyExpr => Fragment::Empty,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct OwnedRustExpr {
    pub expr: Box<RustExpr>,
    pub kind: OwnedKind,
}

#[derive(Debug, Clone)]
pub(crate) enum OwnedKind {
    Cloned,
    Copied,
    Deref,
    Unresolved(Lens<RustType>),
}

#[derive(Debug, Clone)]
pub(crate) enum Lens<T> {
    /// Type of 'this'-object is directly known
    Ground(T),
    /// Type of 'this' is the element-type of the given lens-type
    ///
    /// (e.g. `ElemOf(Seq(T)) => this :: T`)
    ElemOf(Box<Lens<T>>),
    /// Type of 'this' is the type of the given field in the provided lens-type
    ///
    /// (e.g. `FieldAccess(ByPosition(0), (T, U)) => this :: T`)
    FieldAccess(SubIdent, Box<Lens<T>>),
    /// Type of 'this' is the parameter of the given lens-type which is implicitly a generic builtin type like `Option<T>`
    ///
    /// (e.g. `ParamOf(Option(T)) => this :: T`)
    ParamOf(Box<Lens<T>>),
}

impl Lens<RustType> {
    fn field(&self, field: Label) -> Lens<RustType> {
        Lens::FieldAccess(SubIdent::ByName(field), Box::new(self.clone()))
    }

    fn pos(&self, pos: usize) -> Lens<RustType> {
        Lens::FieldAccess(SubIdent::ByPosition(pos), Box::new(self.clone()))
    }

    fn elem(&self) -> Lens<RustType> {
        Lens::ElemOf(Box::new(self.clone()))
    }

    fn param(&self) -> Lens<RustType> {
        Lens::ParamOf(Box::new(self.clone()))
    }
}

#[derive(Debug, Clone)]
pub(crate) enum RustExpr {
    Entity(RustEntity),
    PrimitiveLit(RustPrimLit),
    ArrayLit(Vec<RustExpr>),
    MethodCall(Box<RustExpr>, MethodSpecifier, Vec<RustExpr>), // NOTE - to avoid nesting parentheses, we avoid chaining `FieldAccess` and `FunctionCall` and instead use a distinguished variant
    FieldAccess(Box<RustExpr>, SubIdent), // can be used for receiver methods as well, with FunctionCall
    FunctionCall(Box<RustExpr>, Vec<RustExpr>), // can be used for tuple constructors as well
    Tuple(Vec<RustExpr>),
    Struct(Constructor, StructExpr),
    Owned(OwnedRustExpr),
    Borrow(Box<RustExpr>),
    BorrowMut(Box<RustExpr>),
    Try(Box<RustExpr>),
    Operation(RustOp),
    // REVIEW - Blocks without a final value are implicitly Unit, so maybe optimize for such cases by allowing the expr to be elided entirely (perhaps only if there is at least one statement)
    BlockScope(Vec<RustStmt>, Box<RustExpr>), // scoped block with a final value as an implicit return
    Control(Box<RustControl>),                // for control blocks that return a value
    Closure(RustClosure),                     // only simple lambdas for now
    Index(Box<RustExpr>, Box<RustExpr>),      // object, index
    Slice(Box<RustExpr>, Box<RustExpr>, Box<RustExpr>), // object, start ix, end ix (exclusive)
    RangeExclusive(Box<RustExpr>, Box<RustExpr>),
    ResultOk(Option<Label>, Box<RustExpr>),
    ResultErr(Box<RustExpr>),
    Macro(RustMacro),
}

#[derive(Debug, Clone)]
pub(crate) enum RustMacro {
    Matches(Box<RustExpr>, Vec<RustPattern>),
    Vec(VecExpr),
}

#[derive(Debug, Clone)]
pub(crate) enum VecExpr {
    Nil,
    #[expect(dead_code)]
    Single(Box<RustExpr>),
    #[expect(dead_code)]
    Repeat(Box<RustExpr>, Box<RustExpr>),
    List(Vec<RustExpr>),
}

impl RustExpr {
    pub const UNIT: Self = Self::Tuple(Vec::new());

    pub const NONE: Self = Self::Entity(RustEntity::Local(Label::Borrowed("None")));

    pub const TRUE: Self = Self::PrimitiveLit(RustPrimLit::Boolean(true));

    #[expect(dead_code)]
    pub const FALSE: Self = Self::PrimitiveLit(RustPrimLit::Boolean(false));

    pub const VEC_NIL: Self = RustExpr::Macro(RustMacro::Vec(VecExpr::Nil));

    pub const ARR_NIL: Self = RustExpr::ArrayLit(Vec::new());

    /// Returns `Some(varname)` if `self` is a simple entity-reference to identifier `varname`, and
    /// `None` otherwise.
    pub fn as_local(&self) -> Option<&Label> {
        match self {
            RustExpr::Entity(RustEntity::Local(v)) => Some(v),
            _ => None,
        }
    }

    pub fn lift_option(expr: Option<Self>) -> Self {
        match expr {
            Some(expr) => expr.wrap_some(),
            None => Self::NONE,
        }
    }

    #[expect(dead_code)]
    pub fn embed_match(scrutinee: Self, body: RustMatchBody<Vec<RustStmt>>) -> Self {
        match body {
            RustMatchBody::Irrefutable(mut cases) if cases.len() == 1 && cases[0].0.is_simple() => {
                let Some((MatchCaseLHS::Pattern(pat), mut stmts)) = cases.pop() else {
                    panic!("bad guard")
                };
                let let_bind = RustStmt::destructure(pat, scrutinee);
                stmts.insert(0, let_bind);
                match vec_stmts_to_block(stmts) {
                    None => unreachable!("unexpected no-value match expr in RustExpr::embed_match"),
                    Some((stmts, expr)) => Self::BlockScope(stmts, Box::new(expr)),
                }
            }
            _ => {
                let match_item = RustControl::Match(scrutinee, body);
                Self::Control(Box::new(match_item))
            }
        }
    }

    pub(crate) fn local_tuple<Name: IntoLabel>(locals: impl IntoIterator<Item = Name>) -> Self {
        Self::Tuple(locals.into_iter().map(Self::local).collect())
    }

    pub fn local(name: impl Into<Label>) -> Self {
        Self::Entity(RustEntity::Local(name.into()))
    }

    pub fn num_lit<N: Into<usize>>(num: N) -> Self {
        Self::PrimitiveLit(RustPrimLit::Numeric(RustNumLit::Usize(num.into())))
    }

    #[inline]
    pub const fn bool_lit(b: bool) -> Self {
        Self::PrimitiveLit(RustPrimLit::Boolean(b))
    }

    #[inline]
    pub const fn u8lit(num: u8) -> Self {
        Self::PrimitiveLit(RustPrimLit::Numeric(RustNumLit::U8(num)))
    }

    #[inline]
    pub const fn u16lit(num: u16) -> Self {
        Self::PrimitiveLit(RustPrimLit::Numeric(RustNumLit::U16(num)))
    }

    #[inline]
    pub const fn u32lit(num: u32) -> Self {
        Self::PrimitiveLit(RustPrimLit::Numeric(RustNumLit::U32(num)))
    }

    #[inline]
    pub const fn u64lit(num: u64) -> RustExpr {
        Self::PrimitiveLit(RustPrimLit::Numeric(RustNumLit::U64(num)))
    }

    pub fn as_usize(self) -> Self {
        Self::Operation(RustOp::AsCast(
            Box::new(self),
            RustType::from(PrimType::Usize),
        ))
    }

    pub fn scoped<Name: Into<Label>>(
        path: impl IntoIterator<Item = Name>,
        name: impl Into<Label>,
    ) -> Self {
        let labels = path.into_iter().map(|x| x.into()).collect::<Vec<Label>>();
        Self::Entity(RustEntity::Scoped(labels, name.into()))
    }

    pub fn borrow_of(self) -> Self {
        match self {
            // REVIEW - we need a more cohesive idea/model for where we want to borrow and what syntax is required for the desired semantics
            Self::Owned(OwnedRustExpr { expr, .. }) => match &*expr {
                Self::FieldAccess(..) => Self::Borrow(expr),
                _ => *expr,
            },
            other => Self::Borrow(Box::new(other)),
        }
    }

    pub fn field<Name>(self, name: Name) -> Self
    where
        Name: Into<Label> + AsRef<str>,
    {
        match self {
            Self::Owned(OwnedRustExpr { expr, kind }) => {
                let (expr, kind) = match kind {
                    OwnedKind::Unresolved(lens) => {
                        let lab = name.into();
                        let lens = lens.field(lab.clone());
                        (Box::new(expr.field(lab)), OwnedKind::Unresolved(lens))
                    }
                    _ => (Box::new(expr.field(name)), kind),
                };
                Self::Owned(OwnedRustExpr { expr, kind })
            }
            other => Self::FieldAccess(Box::new(other), SubIdent::ByName(name.into())),
        }
    }

    pub fn at_pos(self, n: usize) -> Self {
        match self {
            Self::Owned(OwnedRustExpr { expr, kind }) => match kind {
                OwnedKind::Cloned => unreachable!("tuple-position smart-constructor should not be used on decided-clone expressions"),
                OwnedKind::Copied | OwnedKind::Deref => expr.at_pos(n),
                OwnedKind::Unresolved(lens) => {
                    Self::Owned(OwnedRustExpr {
                        expr: Box::new(expr.at_pos(n)),
                        kind: OwnedKind::Unresolved(lens.pos(n)),
                    })
                },
            }
            other => Self::FieldAccess(Box::new(other), SubIdent::ByPosition(n)),
        }
    }

    pub fn index(self, ix: RustExpr) -> RustExpr {
        match self {
            Self::Owned(owned) => match owned {
                OwnedRustExpr {
                    kind: OwnedKind::Copied | OwnedKind::Deref,
                    expr: this,
                } => this.index(ix),
                OwnedRustExpr {
                    kind: OwnedKind::Unresolved(lens),
                    expr,
                } => Self::Owned(OwnedRustExpr {
                    expr: Box::new(expr.index(ix)),
                    kind: OwnedKind::Unresolved(lens.elem()),
                }),
                OwnedRustExpr {
                    kind: OwnedKind::Cloned,
                    ..
                } => {
                    unreachable!(
                        "index smart-constructor should only be used on undecided expressions"
                    );
                }
            },
            other => Self::Index(Box::new(other), Box::new(ix)),
        }
    }

    pub fn call_with(self, args: impl IntoIterator<Item = Self>) -> Self {
        Self::FunctionCall(Box::new(self), args.into_iter().collect())
    }

    pub fn call(self) -> Self {
        self.call_with(None)
    }

    pub fn negate(self) -> Self {
        RustExpr::Operation(RustOp::PrefixOp(PrefixOperator::BoolNot, Box::new(self)))
    }

    #[expect(dead_code)]
    pub fn gte(self, other: Self) -> Self {
        RustExpr::Operation(RustOp::InfixOp(
            InfixOperator::Gte,
            Box::new(self),
            Box::new(other),
        ))
    }

    #[expect(dead_code)]
    pub fn eq_to(self, other: Self) -> Self {
        RustExpr::Operation(RustOp::InfixOp(
            InfixOperator::Eq,
            Box::new(self),
            Box::new(other),
        ))
    }

    /// Helper method that calls the `as_slice` method on the expression passed in,
    /// unpacking any top-level `RustExpr::CloneOf` variants to avoid inefficient (and unnecessary)
    /// clone-then-borrow constructs in the generated code.
    pub fn vec_as_slice(self) -> Self {
        let this = match self {
            Self::Owned(OwnedRustExpr { expr, .. }) => *expr,
            other => other,
        };
        this.call_method("as_slice")
    }

    /// Helper method that calls the `len` method on the expression passed in,
    /// unpacking any top-level `RustExpr::CloneOf` variants to avoid inefficient (and unnecessary)
    /// clone-then-borrow constructs in the generated code.
    pub fn vec_len(self) -> Self {
        let this = match self {
            Self::Owned(OwnedRustExpr { expr, .. }) => expr,
            other => Box::new(other),
        };
        RustExpr::MethodCall(this, MethodSpecifier::LEN, Vec::new())
    }

    pub fn vec_is_empty(self) -> Self {
        let this = match self {
            Self::Owned(OwnedRustExpr { expr, .. }) => expr,
            other => Box::new(other),
        };
        RustExpr::MethodCall(this, MethodSpecifier::IS_EMPTY, Vec::new())
    }

    /// Invokes `<self>.<name>` as a callable method, passing in an empty list of arguments.
    pub fn call_method(self, name: impl Into<Label>) -> Self {
        self.call_method_with(name, None)
    }

    /// Invokes `<self>.<name>` as a callable method, passing in the argument list produced by iterating
    /// over `args`.
    pub fn call_method_with(
        self,
        name: impl Into<Label>,
        args: impl IntoIterator<Item = Self>,
    ) -> Self {
        RustExpr::MethodCall(
            Box::new(self),
            SubIdent::ByName(name.into()).into(),
            args.into_iter().collect(),
        )
    }

    /// Produces the infix-operator term with surface syntax `<lhs> <op> <rhs>`.
    pub fn infix(lhs: Self, op: InfixOperator, rhs: Self) -> Self {
        Self::Operation(RustOp::InfixOp(op, Box::new(lhs), Box::new(rhs)))
    }

    /// Produces the most natural expression equivalent to `<self>?`.
    ///
    /// Cancels out `Result::Ok(...)`, and permeates `RustExpr::BlockScope` constructs to avoid overly complex syntactical
    /// productions.
    pub fn wrap_try(self) -> Self {
        match self {
            Self::ResultOk(_, inner) => *inner,
            Self::BlockScope(stmts, ret) => Self::BlockScope(stmts, Box::new(ret.wrap_try())),
            // REVIEW - consider whether there are any other special cases
            _ => Self::Try(Box::new(self)),
        }
    }

    pub fn str_lit(str: impl Into<Label>) -> Self {
        Self::PrimitiveLit(RustPrimLit::String(str.into()))
    }

    /// Attempts to infer and return the (primitive) type of the given `RustExpr`,
    /// returning `None` if the expression is not a primitive type or otherwise
    /// cannot be inferred without further context or more complicated heuristics.
    pub fn try_get_primtype(&self) -> Option<PrimType> {
        match self {
            RustExpr::Entity(_) => None,
            RustExpr::PrimitiveLit(p_lit) => match p_lit {
                RustPrimLit::Boolean(..) => Some(PrimType::Bool),
                RustPrimLit::Numeric(n_lit) => match n_lit {
                    RustNumLit::U8(..) => Some(PrimType::U8),
                    RustNumLit::U16(..) => Some(PrimType::U16),
                    RustNumLit::U32(..) => Some(PrimType::U32),
                    RustNumLit::U64(..) => Some(PrimType::U64),
                    RustNumLit::Usize(..) => Some(PrimType::Usize),
                },
                RustPrimLit::Char(..) => Some(PrimType::Char),
                RustPrimLit::String(..) => None,
            },
            RustExpr::Macro(RustMacro::Matches(..)) => Some(PrimType::Bool),
            RustExpr::Macro(RustMacro::Vec(..)) => None,
            RustExpr::ArrayLit(..) => None,
            RustExpr::MethodCall(_recv, _method, _args) => {
                match _method {
                    MethodSpecifier::Common(cm) => {
                        // REVIEW - the current only CommonMethod, Len, is not well-defined over non-empty argument lists, but we don't check this
                        cm.try_get_return_primtype()
                    }
                    MethodSpecifier::Arbitrary(SubIdent::ByPosition(_)) => {
                        unreachable!("unexpected method call using numeric SubIdent")
                    }
                    MethodSpecifier::Arbitrary(SubIdent::ByName(name)) => {
                        if name.as_ref() == "len" && _args.is_empty() {
                            if cfg!(debug_assertions) {
                                // REVIEW - is this worth warning about or should it be an acceptable invocation?
                                eprintln!("WARNING: `.len()` method should be specified as a `MethodSpecifier::Common`, but was called via `Arbitrary(SubIdent::ByName)` instead...");
                            }
                            // REVIEW - we don't really check anything about `_recv`, and really just assume that a `.len()` method will always return `usize`
                            Some(PrimType::Usize)
                        } else {
                            // REVIEW - we might want to log the number of times we hit this branch, and with what values, to see if there are any obvious cases to handle
                            None
                        }
                    }
                }
            }
            RustExpr::FieldAccess(obj, ident) => {
                match ident {
                    &SubIdent::ByPosition(ix) => match &**obj {
                        RustExpr::Tuple(tuple)
                        | RustExpr::Struct(_, StructExpr::TupleExpr(tuple)) => {
                            if tuple.len() <= ix {
                                unreachable!(
                                    "bad tuple-index `_.{ix}` on {}-tuple {:?}",
                                    tuple.len(),
                                    tuple
                                );
                            }
                            tuple[ix].try_get_primtype()
                        }
                        _ => {
                            // REVIEW - at least notionally, it is hard to come up with any other cases that aren't invariably dead-ends
                            None
                        }
                    },
                    SubIdent::ByName(name) => match &**obj {
                        RustExpr::Struct(_con, StructExpr::RecordExpr(fields)) => {
                            for (field, val) in fields {
                                if field == name {
                                    if let Some(val) = val {
                                        return val.try_get_primtype();
                                    } else {
                                        // NOTE - solving a named-field pun requires non-local reasoning equivalent to solving `RustExpr::Entity`
                                        return None;
                                    }
                                }
                            }
                            unreachable!(
                                "missing struct-field `_.{name}` on struct expression: {obj:?}"
                            );
                        }
                        RustExpr::Struct(..) => unreachable!(
                            "bad indexing {ident:?} on non-record struct expression: {obj:?}"
                        ),
                        _ => {
                            // REVIEW - at least notionally, it is hard to come up with any other cases that aren't invariably dead-ends
                            None
                        }
                    },
                }
            }
            RustExpr::Struct(..) => None,
            RustExpr::Tuple(tuple) => match &tuple[..] {
                [] => Some(PrimType::Unit),
                [x] => x.try_get_primtype(),
                [_, ..] => None,
            },
            RustExpr::Index(seq, index) => {
                match &**seq {
                    RustExpr::ArrayLit(lits) => {
                        if index.try_get_primtype() == Some(PrimType::Usize) {
                            lits[0].try_get_primtype()
                        } else {
                            None
                        }
                    }
                    _ => {
                        // REVIEW - It is unclear whether adding logic to support anything more complex than an array literal would be worth it
                        // TODO - we might want to log the number of times we hit this branch, and with what values, to see if there are any obvious cases to handle
                        None
                    }
                }
            }
            RustExpr::FunctionCall(..) => {
                // FIXME - there may be some functions we can predict the return values of, but for now we can leave this alone
                // REVIEW - we might want to log the number of times we hit this branch, and with what values, to see if there are any obvious cases to handle
                None
            }
            RustExpr::ResultOk(..) | RustExpr::ResultErr(..) => None,
            RustExpr::Owned(OwnedRustExpr { expr, .. }) => match &**expr {
                RustExpr::Borrow(y) | RustExpr::BorrowMut(y) => y.try_get_primtype(),
                other => other.try_get_primtype(),
            },
            RustExpr::Borrow(_) | RustExpr::BorrowMut(_) => None,
            RustExpr::Try(inner) => match inner.as_ref() {
                RustExpr::ResultOk(.., x) => x.try_get_primtype(),
                _ => None,
            },
            RustExpr::Operation(op) => match op {
                RustOp::InfixOp(op, lhs, rhs) => {
                    let lhs_type = lhs.try_get_primtype()?;
                    let rhs_type = rhs.try_get_primtype()?;
                    op.out_type(lhs_type, rhs_type)
                }
                RustOp::PrefixOp(op, expr) => {
                    let expr_type = expr.try_get_primtype()?;
                    op.out_type(expr_type)
                }
                RustOp::AsCast(expr, typ) => {
                    let out_typ = typ.try_as_prim()?;
                    if expr
                        .try_get_primtype()
                        .as_ref()
                        .map_or(false, PrimType::is_numeric)
                        && out_typ.is_numeric()
                    {
                        Some(out_typ)
                    } else {
                        None
                    }
                }
            },
            RustExpr::BlockScope(_stmts, ret) => {
                // REVIEW - consider whether it is worthwhile to bother scanning `_stmts` for local definitions that `ret` might then refer to...
                ret.try_get_primtype()
            }
            RustExpr::Control(..)
            | RustExpr::Closure(..)
            | RustExpr::Slice(..)
            | RustExpr::RangeExclusive(..) => None,
        }
    }

    /// Basic heuristic to determine whether a `RustExpr` is free of any side-effects, and therefore can be fully elided
    /// if its direct evaluation would be immediately discarded (as with [`RustStmt::Expr`],  or [`RustStmt::Let`] with the `_` identifier).
    pub fn is_pure(&self) -> bool {
        match self {
            RustExpr::Entity(..) => true,
            RustExpr::Macro(RustMacro::Matches(expr, ..)) => expr.is_pure(),
            RustExpr::Macro(RustMacro::Vec(vec_expr)) => match vec_expr {
                VecExpr::Nil => true,
                VecExpr::Single(x) => x.is_pure(),
                VecExpr::Repeat(x, n) => x.is_pure() && n.is_pure(),
                VecExpr::List(xs) => xs.iter().all(Self::is_pure),
            },
            RustExpr::PrimitiveLit(..) => true,
            RustExpr::ArrayLit(arr) => arr.iter().all(Self::is_pure),
            // REVIEW - over types we have no control over, clone itself can be impure, but it should never be so for the code we ourselves are generating
            RustExpr::Owned(OwnedRustExpr { expr, .. }) => expr.is_pure(),
            RustExpr::MethodCall(x, MethodSpecifier::LEN, args) => {
                if args.is_empty() {
                    x.is_pure()
                } else {
                    unreachable!("unexpected method call on `len` with args: {:?}", args);
                }
            }
            // NOTE - there is no guaranteed-accurate static heuristic to distinguish pure fn's from those with possible side-effects
            RustExpr::FunctionCall(..) | RustExpr::MethodCall(..) => false,
            RustExpr::FieldAccess(expr, ..) => expr.is_pure(),
            RustExpr::Tuple(tuple) => tuple.iter().all(Self::is_pure),
            RustExpr::Struct(_, assigns) => match assigns {
                StructExpr::RecordExpr(assigns) => assigns
                    .iter()
                    .all(|(_, val)| val.as_ref().map_or(true, Self::is_pure)),
                StructExpr::TupleExpr(values) => values.iter().all(|val| val.is_pure()),
                StructExpr::EmptyExpr => true,
            },
            RustExpr::Borrow(expr) | RustExpr::BorrowMut(expr) => expr.is_pure(),
            // NOTE - while we can construct pure Try-expressions manually, the intent of `?` is to have potential side-effects and so we judge them de-facto impure
            RustExpr::Try(..) => false,
            RustExpr::Operation(op) => match op {
                RustOp::InfixOp(.., lhs, rhs) => lhs.is_pure() && rhs.is_pure() && op.is_sound(),
                RustOp::PrefixOp(.., inner) => inner.is_pure() && op.is_sound(),
                // NOTE - illegal casts like `x as u8` where x >= 256 are language-level errors that are neither pure nor impure
                RustOp::AsCast(expr, ..) => expr.is_pure() && op.is_sound(),
            },
            RustExpr::ResultOk(.., inner) | RustExpr::ResultErr(inner) => inner.is_pure(),
            // NOTE - we can have block-scopes with non-empty statements that are pure, but that is a bit too much work for our purposes right now.
            RustExpr::BlockScope(stmts, tail) => stmts.is_empty() && tail.is_pure(),
            // NOTE - there may be some pure control expressions but those will be relatively rare as natural occurrences
            RustExpr::Control(..) => false,
            // NOTE - closures are presupposed to never appear in a context where elision is a possibility to consider so this result doesn't actually need to be refined further
            RustExpr::Closure(..) => false,
            // NOTE - slice/index exprs can always be out-of-bounds so they cannot be elided without changing program behavior
            RustExpr::Slice(..) | RustExpr::Index(..) => false,
            // NOTE - ranges can only ever be language-level errors if the endpoint types are not the same
            RustExpr::RangeExclusive(start, end) => {
                start.is_pure()
                    && end.is_pure()
                    && match (start.try_get_primtype(), end.try_get_primtype()) {
                        (Some(pt0), Some(pt1)) => pt0 == pt1,
                        // NOTE - there are legal cases for ranges involving unknown types (i.e. those with untyped variables) but we cannot rule one way or another on those
                        _ => false,
                    }
            }
        }
    }

    /// Embed a RustExpr into a new non-temporary value, or return it if it is already non-temporary
    pub(crate) fn make_persistent(&self) -> Cow<'_, Self> {
        match self {
            RustExpr::Entity(..) => Cow::Borrowed(self),
            // REVIEW - consider which non-entity cases are already 'persistent'
            _ => Cow::Owned(RustExpr::BlockScope(
                vec![RustStmt::assign("tmp", self.clone())],
                Box::new(RustExpr::local("tmp")),
            )),
        }
    }

    pub(crate) fn use_as_persistent(self, f: impl FnOnce(Self) -> Self) -> Self {
        const NAME: &str = "tmp";
        match self {
            this @ RustExpr::Entity(..) => f(this),
            _ => RustExpr::BlockScope(
                vec![RustStmt::assign(NAME, self)],
                Box::new(f(RustExpr::local(NAME))),
            ),
        }
    }

    /// Determines whether a given [`RustExpr`] is "complex" in the sense of
    /// preferentially requiring a temporary assignment rather than being directly
    /// used as an `if` or `match` expression scrutinee.
    ///
    /// This corresponds primarily to [`RustExpr::BlockScope`] and any ancestor-nodes
    /// thereof.
    pub(crate) fn is_complex(&self) -> bool {
        match self {
            // base cases
            RustExpr::Entity(..) => false,
            RustExpr::PrimitiveLit(..) => false,
            RustExpr::BlockScope(stmts, _) => !stmts.is_empty(),
            RustExpr::Control(..) => true,
            RustExpr::Struct(_, StructExpr::EmptyExpr) => false,

            // Special case - `matches!` macro is an idiomatic conditional expression
            RustExpr::Macro(RustMacro::Matches(..)) => false,
            // Special case - `vec!` will typically be constructed only over simple sub-expressions
            RustExpr::Macro(RustMacro::Vec(..)) => false,

            // REVIEW - is there a better heuristic?
            RustExpr::Closure(..) => true,

            // '.any(..)' cases
            RustExpr::Struct(_, StructExpr::TupleExpr(exprs))
            | RustExpr::ArrayLit(exprs)
            | RustExpr::Tuple(exprs) => exprs.iter().any(RustExpr::is_complex),

            // special cases
            RustExpr::Struct(.., StructExpr::RecordExpr(flds)) => flds
                .iter()
                .any(|(_, val)| val.as_ref().is_some_and(RustExpr::is_complex)),

            // single descent cases
            RustExpr::Owned(OwnedRustExpr { expr, .. })
            | RustExpr::Try(expr)
            | RustExpr::ResultOk(.., expr)
            | RustExpr::ResultErr(expr)
            | RustExpr::FieldAccess(expr, _)
            | RustExpr::Operation(RustOp::PrefixOp(.., expr) | RustOp::AsCast(expr, ..))
            | RustExpr::BorrowMut(expr)
            | RustExpr::Borrow(expr) => expr.is_complex(),

            // 1 + N cases
            RustExpr::MethodCall(head, _meth, args) => {
                head.is_complex() || args.iter().any(RustExpr::is_complex)
            }
            RustExpr::FunctionCall(fun, args) => {
                fun.is_complex() || args.iter().any(RustExpr::is_complex)
            }

            // 1 + 1 cases
            RustExpr::Index(lhs, rhs)
            | RustExpr::RangeExclusive(lhs, rhs)
            | RustExpr::Operation(RustOp::InfixOp(.., lhs, rhs)) => {
                lhs.is_complex() || rhs.is_complex()
            }

            // 1 + 1 + 1 cases
            RustExpr::Slice(head, start, stop) => {
                head.is_complex() || start.is_complex() || stop.is_complex()
            }
        }
    }

    pub(crate) fn wrap_ok<Name: IntoLabel>(self, qualifier: Option<Name>) -> RustExpr {
        match self {
            RustExpr::Try(x) => *x,
            other => RustExpr::ResultOk(qualifier.map(Name::into), Box::new(other)),
        }
    }

    pub fn err(self) -> RustExpr {
        RustExpr::ResultErr(Box::new(self))
    }

    pub(crate) fn wrap_some(self) -> RustExpr {
        match self {
            RustExpr::BlockScope(stmts, tail) => {
                RustExpr::BlockScope(stmts, Box::new(tail.wrap_some()))
            }
            _ => RustExpr::local("Some").call_with([self]),
        }
    }

    pub(crate) fn option_none() -> Self {
        RustExpr::local("None")
    }

    /// Returns `true` if the expression has a guaranteed-constant
    /// value.
    pub(crate) fn is_pure_numeric_const(&self) -> bool {
        match self {
            RustExpr::PrimitiveLit(RustPrimLit::Numeric(..)) => true,
            // REVIEW - there are edge cases but they are largely 'obfuscations'
            _ => false,
        }
    }

    pub(crate) fn get_const(&self) -> Option<usize> {
        match self {
            RustExpr::PrimitiveLit(RustPrimLit::Numeric(rnl)) => Some(usize::from(*rnl)),
            _ => None,
        }
    }

    pub(crate) fn add(self, other: Self) -> RustExpr {
        if self.is_pure_numeric_const() && matches!(self.get_const(), Some(0)) {
            other
        } else if other.is_pure_numeric_const() && matches!(other.get_const(), Some(0)) {
            self
        } else {
            RustExpr::infix(self, InfixOperator::Add, other)
        }
    }

    pub(crate) fn prepend_stmt(self, value: RustStmt) -> Self {
        match self {
            RustExpr::BlockScope(mut stmts, tail) => {
                let mut stmts0 = Vec::with_capacity(stmts.len() + 1);
                stmts0.push(value);
                stmts0.append(&mut stmts);
                RustExpr::BlockScope(stmts0, tail)
            }
            other => RustExpr::BlockScope(vec![value], Box::new(other)),
        }
    }

    /// Applies a type-sensitive ownership model to an expression, given its exact type.
    ///
    /// For known-`Copy` types, this amounts to a no-op.
    /// For references to known-`Copy` types, this amounts to a simple deref.
    /// For owned or referenced `Clone`-but-not-`Copy` types, this amounts to a clone operation.
    pub(crate) fn owned(self, expr_type: RustType) -> RustExpr {
        let owned = if expr_type.can_be_copy() {
            OwnedRustExpr {
                expr: Box::new(self),
                kind: OwnedKind::Copied,
            }
        } else {
            OwnedRustExpr {
                expr: Box::new(self),
                kind: OwnedKind::Unresolved(Lens::Ground(expr_type)),
            }
        };
        RustExpr::Owned(owned)
    }

    /// Takes a AST-expression with virtual type `Option<&U>` and a type
    /// representing `Option<U>`, and returns an expression of type `Option<U>`,
    /// avoiding explicit cloning when unnecessary.
    pub(crate) fn owned_opt_ref(self, opt_type: RustType) -> RustExpr {
        fn borrow_param(rt: RustType) -> RustType {
            match rt {
                RustType::Atom(at) => match at {
                    AtomType::Comp(ct) => match ct {
                        CompType::Option(inner) => CompType::Option(Box::new(
                            CompType::Borrow(None, Mut::Immutable, inner).into(),
                        ))
                        .into(),
                        other => other.into(),
                    },
                    other => other.into(),
                },
                other => other,
            }
        }

        let f = if opt_type.can_be_copy() {
            RustClosure::new_predicate(
                "x",
                None,
                RustExpr::Owned(OwnedRustExpr {
                    expr: Box::new(RustExpr::local("x")),
                    kind: OwnedKind::Deref,
                }),
            )
        } else {
            RustClosure::new_predicate(
                "x",
                None,
                RustExpr::Owned(OwnedRustExpr {
                    expr: Box::new(RustExpr::local("x")),
                    kind: OwnedKind::Unresolved(Lens::Ground(borrow_param(opt_type)).param()),
                }),
            )
        };
        self.call_method_with("map", [RustExpr::Closure(f)])
    }
}

impl ToFragment for VecExpr {
    fn to_fragment(&self) -> Fragment {
        let contents = match self {
            VecExpr::Nil => Fragment::Empty,
            VecExpr::Single(x) => x.to_fragment_precedence(Precedence::Top),
            VecExpr::Repeat(x, n) => x.to_fragment_precedence(Precedence::Top).intervene(
                Fragment::string("; "),
                n.to_fragment_precedence(Precedence::Top),
            ),
            VecExpr::List(elts) => Fragment::seq(
                elts.iter()
                    .map(|x| x.to_fragment_precedence(Precedence::Top)),
                Some(Fragment::string(", ")),
            ),
        };
        contents.delimit(Fragment::Char('['), Fragment::Char(']'))
    }
}

impl ToFragmentExt for RustExpr {
    fn to_fragment_precedence(&self, prec: Precedence) -> Fragment {
        match self {
            RustExpr::Entity(e) => e.to_fragment(),
            RustExpr::PrimitiveLit(pl) => pl.to_fragment(),
            RustExpr::ArrayLit(elts) => Fragment::seq(
                elts.iter()
                    .map(|x| RustExpr::to_fragment_precedence(x, Precedence::Top)),
                Some(Fragment::string(", ")),
            )
            .delimit(Fragment::Char('['), Fragment::Char(']')),
            RustExpr::MethodCall(x, name, args) => cond_paren(
                x.to_fragment_precedence(Precedence::Projection)
                    .intervene(Fragment::Char('.'), name.to_fragment())
                    .cat(ToFragmentExt::paren_list_prec(args, Precedence::Top)),
                prec,
                Precedence::Projection,
            ),
            RustExpr::ResultErr(inner) => cond_paren(
                Fragment::group(
                    Fragment::string("Err").cat(
                        inner
                            .to_fragment_precedence(Precedence::TOP)
                            .delimit(Fragment::Char('('), Fragment::Char(')')),
                    ),
                ),
                prec,
                Precedence::INVOKE,
            ),
            RustExpr::ResultOk(opt_qual, inner) => cond_paren(
                Fragment::group(
                    Fragment::opt(opt_qual.as_ref(), |qual| {
                        Fragment::String(qual.clone()).cat(Fragment::string("::"))
                    })
                    .cat(Fragment::string("Ok")),
                )
                .cat(
                    inner
                        .to_fragment_precedence(Precedence::Top)
                        .delimit(Fragment::Char('('), Fragment::Char(')')),
                ),
                prec,
                Precedence::INVOKE,
            ),
            RustExpr::Owned(OwnedRustExpr {
                expr: x,
                kind: OwnedKind::Cloned,
            }) => cond_paren(
                x.to_fragment_precedence(Precedence::Projection)
                    .intervene(Fragment::Char('.'), Fragment::string("clone()")),
                prec,
                Precedence::Projection,
            ),
            RustExpr::Owned(OwnedRustExpr {
                kind: OwnedKind::Deref,
                expr,
            }) => Fragment::Char('*').cat(expr.to_fragment_precedence(Precedence::Prefix)),
            RustExpr::Owned(OwnedRustExpr {
                kind: OwnedKind::Copied,
                expr,
            }) => expr.to_fragment_precedence(prec),
            RustExpr::Owned(OwnedRustExpr {
                kind: OwnedKind::Unresolved(lens),
                expr,
            }) => {
                unreachable!("unresolved ownership: ({expr:?}: {lens:?})")
            }
            RustExpr::FieldAccess(x, name) => x
                .to_fragment_precedence(Precedence::Projection)
                .intervene(Fragment::Char('.'), name.to_fragment()),
            RustExpr::FunctionCall(f, args) => cond_paren(
                f.to_fragment_precedence(Precedence::INVOKE)
                    .cat(ToFragmentExt::paren_list_prec(args, Precedence::Top)),
                prec,
                Precedence::INVOKE,
            ),
            RustExpr::Macro(RustMacro::Matches(head, pats)) => Fragment::string("matches!")
                .cat(
                    head.to_fragment_precedence(Precedence::Top)
                        .cat(Fragment::string(", "))
                        .cat(Fragment::seq(
                            pats.iter().map(|p| p.to_fragment()),
                            Some(Fragment::string(" | ")),
                        ))
                        .delimit(Fragment::Char('('), Fragment::Char(')')),
                )
                .group(),
            RustExpr::Macro(RustMacro::Vec(vec_expr)) => {
                Fragment::string("vec!").cat(vec_expr.to_fragment())
            }
            RustExpr::Tuple(elts) => match elts.as_slice() {
                [elt] => elt
                    .to_fragment_precedence(Precedence::Top)
                    .delimit(Fragment::Char('('), Fragment::string(",)")),
                _ => Self::paren_list_prec(elts, Precedence::Top),
            },
            RustExpr::Struct(con, contents) => RustEntity::from(con.clone())
                .to_fragment()
                .cat(contents.to_fragment()),
            RustExpr::Borrow(expr) => {
                Fragment::Char('&').cat(expr.to_fragment_precedence(Precedence::Prefix))
            }
            RustExpr::BorrowMut(expr) => {
                Fragment::string("&mut ").cat(expr.to_fragment_precedence(Precedence::Prefix))
            }
            RustExpr::Try(expr) => expr
                .to_fragment_precedence(Precedence::Projection)
                .cat(Fragment::Char('?')),
            RustExpr::Operation(op) => op.to_fragment_precedence(prec),
            // REVIEW - special rule for reducing blocks to inline expressions when there are no statements; should this be a simplification rule or a printing rule?
            RustExpr::BlockScope(stmts, val) if stmts.is_empty() => {
                val.to_fragment_precedence(prec)
            }
            RustExpr::BlockScope(stmts, val) => {
                RustStmt::block(stmts.iter().chain(std::iter::once(&RustStmt::Return(
                    ReturnKind::Implicit,
                    val.as_ref().clone(),
                ))))
            }
            RustExpr::Control(ctrl) => ctrl.to_fragment(),
            RustExpr::Closure(cl) => cl.to_fragment_precedence(prec),
            RustExpr::Index(expr, ix) => expr.to_fragment_precedence(Precedence::Projection).cat(
                ix.to_fragment_precedence(Precedence::Top)
                    .delimit(Fragment::Char('['), Fragment::Char(']')),
            ),
            RustExpr::Slice(expr, start, stop) => expr
                .to_fragment_precedence(Precedence::Projection)
                .cat(Fragment::seq(
                    [
                        Fragment::Char('['),
                        start.to_fragment(),
                        Fragment::string(".."),
                        stop.to_fragment(),
                        Fragment::Char(']'),
                    ],
                    None,
                )),
            RustExpr::RangeExclusive(start, stop) => cond_paren(
                start.to_fragment_precedence(Precedence::Top).intervene(
                    Fragment::string(".."),
                    stop.to_fragment_precedence(Precedence::Top),
                ),
                prec,
                Precedence::Top,
            ),
        }
    }
}

impl ToFragment for RustExpr {
    fn to_fragment(&self) -> Fragment {
        self.to_fragment_precedence(Precedence::Atomic)
    }
}

/// Given a block of `RustStmt` that do not have any explicit `return` keywords anywhere within,
/// extract the value of the statement-block as a `RustExpr` (or Unit, if this is the implicit evaluation),
/// and return it.
///
/// Returns `None` if the query is ill-founded, i.e. the block can short-circuit (without `try`).
pub(crate) fn stmts_to_block(
    stmts: Cow<'_, [RustStmt]>,
) -> Option<(Cow<'_, [RustStmt]>, Cow<'_, RustExpr>)> {
    match stmts {
        Cow::Owned(stmts) => {
            let (init, last) = vec_stmts_to_block(stmts)?;
            Some((Cow::Owned(init), Cow::Owned(last)))
        }
        Cow::Borrowed(stmts) => {
            let (init, last) = slice_stmts_to_block(stmts)?;
            Some((Cow::Borrowed(init), last))
        }
    }
}

pub(crate) fn slice_stmts_to_block(stmts: &[RustStmt]) -> Option<(&[RustStmt], Cow<'_, RustExpr>)> {
    if let Some((last, init)) = stmts.split_last() {
        match last {
            RustStmt::Return(ReturnKind::Implicit, expr) | RustStmt::Expr(expr) => {
                Some((init, Cow::Borrowed(expr)))
            }
            RustStmt::Return(ReturnKind::Keyword, ..) => None,
            RustStmt::LetPattern(..) | RustStmt::Let(..) | RustStmt::Reassign(..) => {
                Some((stmts, Cow::Owned(RustExpr::UNIT)))
            } // REVIEW - is unguarded inheritance of a Control block always correct?
              // RustStmt::Control(ctrl) => {
              //     Some((init, Cow::Owned(RustExpr::Control(Box::new(ctrl.clone())))))
              // }
        }
    } else {
        Some((stmts, Cow::Owned(RustExpr::UNIT)))
    }
}

pub(crate) fn vec_stmts_to_block(stmts: Vec<RustStmt>) -> Option<(Vec<RustStmt>, RustExpr)> {
    let mut init = stmts;
    let last = match init.pop() {
        None => RustExpr::UNIT,
        Some(stmt) => match stmt {
            RustStmt::Return(ReturnKind::Keyword, ..) => return None,
            RustStmt::Return(_, expr) | RustStmt::Expr(expr) => expr,
            RustStmt::LetPattern(..) | RustStmt::Let(..) | RustStmt::Reassign(..) => RustExpr::UNIT,
            // REVIEW - is unguarded inheritance of a Control block always correct?
            // RustStmt::Control(ctrl) => RustExpr::Control(Box::new(ctrl.clone())),
        },
    };
    Some((init, last))
}

#[derive(Clone, Debug)]
pub(crate) struct RustClosure(RustClosureHead, ClosureBody);

#[derive(Clone, Debug)]
pub(crate) enum ClosureBody {
    Expression(Box<RustExpr>),
    Statements(Vec<RustStmt>),
}

impl ToFragmentExt for ClosureBody {
    fn to_fragment_precedence(&self, prec: Precedence) -> Fragment {
        match self {
            ClosureBody::Expression(expr) => expr.to_fragment_precedence(prec),
            ClosureBody::Statements(..) => self.to_fragment(),
        }
    }
}

impl ToFragment for ClosureBody {
    fn to_fragment(&self) -> Fragment {
        match self {
            ClosureBody::Expression(expr) => expr.to_fragment_precedence(Precedence::TOP),
            ClosureBody::Statements(stmts) => <RustStmt as ToFragment>::block(stmts),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum RustClosureHead {
    Thunk,
    SimpleVar(Label, Option<RustType>),
}

impl RustClosure {
    pub fn thunk_expr(expr: RustExpr) -> RustClosure {
        RustClosure(
            RustClosureHead::Thunk,
            ClosureBody::Expression(Box::new(expr)),
        )
    }

    pub fn thunk_body(stmts: impl IntoIterator<Item = RustStmt>) -> RustClosure {
        RustClosure(
            RustClosureHead::Thunk,
            ClosureBody::Statements(Vec::from_iter(stmts)),
        )
    }

    /// Constructs a new closure with 'predicate' (ref-bound argument) semantics.
    ///
    /// Also applies to extract-key semantics `(&T) -> K where K: Copy`
    pub fn new_predicate(
        head: impl IntoLabel,
        deref_t: Option<RustType>,
        body: RustExpr,
    ) -> RustClosure {
        RustClosure(
            RustClosureHead::SimpleVar(
                head.into(),
                deref_t.map(|ty| RustType::borrow_of(None, Mut::Immutable, ty)),
            ),
            ClosureBody::Expression(Box::new(body)),
        )
    }

    /// Constructs a new closure with 'transform' (value) semantics
    pub fn new_transform(
        head: impl IntoLabel,
        value_t: Option<RustType>,
        body: RustExpr,
    ) -> RustClosure {
        RustClosure(
            RustClosureHead::SimpleVar(head.into(), value_t),
            ClosureBody::Expression(Box::new(body)),
        )
    }
}

impl ToFragment for RustClosureHead {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustClosureHead::Thunk => Fragment::string("||"),
            RustClosureHead::SimpleVar(lbl, sig) => lbl
                .to_fragment()
                .intervene(
                    Fragment::string(": "),
                    Fragment::opt(sig.as_ref(), RustType::to_fragment),
                )
                .delimit(Fragment::Char('|'), Fragment::Char('|')),
        }
    }
}

impl ToFragment for RustClosure {
    fn to_fragment(&self) -> Fragment {
        self.to_fragment_precedence(Precedence::ARROW)
    }
}

impl ToFragmentExt for RustClosure {
    fn to_fragment_precedence(&self, prec: Precedence) -> Fragment {
        match self {
            RustClosure(head, body) => cond_paren(
                head.to_fragment().intervene(
                    Fragment::Char(' '),
                    body.to_fragment_precedence(Precedence::ARROW),
                ),
                prec,
                Precedence::ARROW,
            ),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum InfixOperator {
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    Div,
    Rem,
    Add,
    Sub,
    Mul,
    Shl,
    Shr,
    BitOr,
    BitAnd,
    BoolOr,
    BoolAnd,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PrefixOperator {
    BoolNot,
}
impl PrefixOperator {
    fn precedence(&self) -> Precedence {
        match self {
            PrefixOperator::BoolNot => Precedence::LOGICAL_NEGATE,
        }
    }

    pub(crate) fn out_type(&self, inner_type: PrimType) -> Option<PrimType> {
        match self {
            PrefixOperator::BoolNot => match inner_type {
                PrimType::Bool => Some(PrimType::Bool),
                _ => None,
            },
        }
    }
}

impl InfixOperator {
    pub(crate) fn precedence(&self) -> Precedence {
        match self {
            InfixOperator::Eq | InfixOperator::Neq => Precedence::EQUALITY,
            InfixOperator::Lt | InfixOperator::Lte | InfixOperator::Gt | InfixOperator::Gte => {
                Precedence::COMPARE
            }
            InfixOperator::Div | InfixOperator::Rem => Precedence::DIV_REM,
            InfixOperator::Add | InfixOperator::Sub => Precedence::ADD_SUB,
            InfixOperator::Mul => Precedence::MUL,
            InfixOperator::Shl | InfixOperator::Shr => Precedence::BIT_SHIFT,
            InfixOperator::BitOr => Precedence::BITOR,
            InfixOperator::BitAnd => Precedence::BITAND,
            InfixOperator::BoolAnd => Precedence::LOGICAL_AND,
            InfixOperator::BoolOr => Precedence::LOGICAL_OR,
        }
    }

    pub(crate) fn out_type(&self, lhs_type: PrimType, rhs_type: PrimType) -> Option<PrimType> {
        match self {
            InfixOperator::Eq | InfixOperator::Neq => {
                if lhs_type == rhs_type {
                    Some(PrimType::Bool)
                } else {
                    None
                }
            }
            InfixOperator::BoolAnd | InfixOperator::BoolOr => match (lhs_type, rhs_type) {
                (PrimType::Bool, PrimType::Bool) => Some(PrimType::Bool),
                _ => None,
            },
            InfixOperator::Lt | InfixOperator::Lte | InfixOperator::Gt | InfixOperator::Gte => {
                if lhs_type == rhs_type && lhs_type.is_numeric() {
                    Some(PrimType::Bool)
                } else {
                    None
                }
            }
            InfixOperator::BitOr
            | InfixOperator::BitAnd
            | InfixOperator::Div
            | InfixOperator::Rem
            | InfixOperator::Add
            | InfixOperator::Sub
            | InfixOperator::Mul => {
                if lhs_type == rhs_type && lhs_type.is_numeric() {
                    Some(lhs_type)
                } else {
                    None
                }
            }
            // NOTE - the types of a SHR or SHL do not have to be the same, but both must be numeric at the very least
            InfixOperator::Shl | InfixOperator::Shr => {
                if lhs_type.is_numeric() && rhs_type.is_numeric() {
                    Some(lhs_type)
                } else {
                    None
                }
            }
        }
    }
}

impl InfixOperator {
    pub(crate) fn token(&self) -> &'static str {
        match self {
            InfixOperator::Eq => " == ",
            InfixOperator::Neq => " != ",
            InfixOperator::Lt => " < ",
            InfixOperator::Lte => " <= ",
            InfixOperator::Gt => " > ",
            InfixOperator::Gte => " >= ",
            InfixOperator::Div => " / ",
            InfixOperator::Rem => " % ",
            InfixOperator::Add => " + ",
            InfixOperator::Sub => " - ",
            InfixOperator::Mul => " * ",
            InfixOperator::Shl => " << ",
            InfixOperator::Shr => " >> ",
            InfixOperator::BitOr => " | ",
            InfixOperator::BitAnd => " & ",
            InfixOperator::BoolOr => " || ",
            InfixOperator::BoolAnd => " && ",
        }
    }
}

impl PrefixOperator {
    pub(crate) fn token(&self) -> &'static str {
        match self {
            PrefixOperator::BoolNot => "!",
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum RustOp {
    InfixOp(InfixOperator, Box<RustExpr>, Box<RustExpr>),
    PrefixOp(PrefixOperator, Box<RustExpr>),
    AsCast(Box<RustExpr>, RustType),
}

impl RustOp {
    pub(crate) fn precedence(&self) -> Precedence {
        match self {
            Self::InfixOp(op, _, _) => op.precedence(),
            Self::PrefixOp(op, _) => op.precedence(),
            Self::AsCast(_, _) => Precedence::CAST_INFIX,
        }
    }

    /// Basic heuristic to determine whether a given operation is 'sound' at the type-level, i.e.
    /// that the operation in question is defined on the type of the operands and that the operands conform
    /// to the expectations of the operation, and are homogenous if that is required.
    ///
    /// If the operation could possibly be unsound, this method may conservatively return false even if it happens to be sound
    /// for the given operation, in practice.
    pub fn is_sound(&self) -> bool {
        match self {
            RustOp::InfixOp(op, lhs, rhs) => {
                match (op, lhs.try_get_primtype(), rhs.try_get_primtype()) {
                    (InfixOperator::Eq | InfixOperator::Neq, Some(lhs_type), Some(rhs_type)) => {
                        lhs_type == rhs_type
                    }
                    // NOTE - we need to filter out BoolAnd and BoolOr from the next catchall branch, so we can't merely match on the literal PrimType::Bool in the case-pattern
                    (
                        InfixOperator::BoolAnd | InfixOperator::BoolOr,
                        Some(lhs_type),
                        Some(rhs_type),
                    ) => {
                        matches!((lhs_type, rhs_type), (PrimType::Bool, PrimType::Bool))
                    }
                    (_, Some(lhs_type), Some(rhs_type)) => {
                        lhs_type == rhs_type && lhs_type.is_numeric()
                    }
                    (_, None, _) | (_, _, None) => false,
                }
            }
            RustOp::PrefixOp(op, inner) => match (op, inner.try_get_primtype()) {
                (PrefixOperator::BoolNot, Some(PrimType::Bool)) => true,
                (PrefixOperator::BoolNot, _) => false,
            },
            RustOp::AsCast(expr, typ) => match (expr.try_get_primtype(), typ.try_as_prim()) {
                (Some(pt0), Some(pt1)) => !matches!(
                    PrimType::compare_width(pt0, pt1),
                    None | Some(Ordering::Greater)
                ),
                _ => false,
            },
        }
    }
}

impl RustOp {
    pub fn op_eq(lhs: RustExpr, rhs: RustExpr) -> Self {
        Self::InfixOp(InfixOperator::Eq, Box::new(lhs), Box::new(rhs))
    }

    pub fn op_neq(lhs: RustExpr, rhs: RustExpr) -> Self {
        Self::InfixOp(InfixOperator::Neq, Box::new(lhs), Box::new(rhs))
    }
}

impl ToFragmentExt for RustOp {
    fn to_fragment_precedence(&self, prec: Precedence) -> Fragment {
        let inherent = self.precedence();
        match self {
            RustOp::InfixOp(op, lhs, rhs) => cond_paren(
                lhs.to_fragment_precedence(inherent)
                    .cat(Fragment::string(op.token()))
                    .cat(rhs.to_fragment_precedence(inherent)),
                prec,
                inherent,
            ),
            RustOp::PrefixOp(op, inner) => cond_paren(
                Fragment::string(op.token()).cat(inner.to_fragment_precedence(inherent)),
                prec,
                inherent,
            ),
            RustOp::AsCast(expr, typ) => cond_paren(
                expr.to_fragment()
                    .intervene(Fragment::string(" as "), typ.to_fragment()),
                prec,
                inherent,
            ),
        }
    }
}

impl ToFragment for RustOp {
    fn to_fragment(&self) -> Fragment {
        self.to_fragment_precedence(Precedence::ATOM)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord, Hash, Default)]
pub(crate) enum ReturnKind {
    #[default]
    Implicit,
    Keyword,
}
impl ReturnKind {
    pub(crate) const fn is_keyword(&self) -> bool {
        matches!(self, Self::Keyword)
    }
}

impl From<bool> for ReturnKind {
    fn from(value: bool) -> Self {
        if value {
            Self::Keyword
        } else {
            Self::Implicit
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum RustStmt {
    Let(Mut, Label, Option<RustType>, RustExpr),
    // REVIEW - we might be able to modify `Let` to use a Pattern in place of a Label, but that would be a bit disruptive as the first pass
    LetPattern(RustPattern, RustExpr),
    Reassign(Label, RustExpr),
    Expr(RustExpr),
    Return(ReturnKind, RustExpr),
    // Control(RustControl),
}

impl RustStmt {
    // pub const BREAK: Self = Self::Control(RustControl::Break);

    pub fn assign(name: impl Into<Label>, rhs: RustExpr) -> Self {
        Self::Let(Mut::Immutable, name.into(), None, rhs)
    }

    pub fn assign_mut(name: impl Into<Label>, rhs: RustExpr) -> Self {
        Self::Let(Mut::Mutable, name.into(), None, rhs)
    }

    pub fn destructure(pat: RustPattern, rhs: RustExpr) -> Self {
        Self::LetPattern(pat, rhs)
    }

    /// Classifies the provided Expr using [`RustExpr::is_pure`], and returns a [`RustStmt`]
    /// that performs a vacuous let-assignment if it is effect-ful. Otherwise,
    /// returns None.
    pub fn assign_and_forget(rhs: RustExpr) -> Option<Self> {
        if rhs.is_pure() {
            None
        } else {
            Some(Self::Let(Mut::Immutable, Label::from("_"), None, rhs))
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum RustCatchAll {
    PanicUnreachable { message: Label },
    ReturnErrorValue { value: RustExpr },
}

impl RustCatchAll {
    pub fn to_match_case(&self) -> RustMatchCase {
        match self {
            RustCatchAll::PanicUnreachable { message } => (
                MatchCaseLHS::Pattern(RustPattern::CatchAll(Some(Label::Borrowed("_other")))),
                [RustStmt::Expr(RustExpr::local("unreachable!").call_with([
                    RustExpr::str_lit(format!(
                        "{message}match refuted with unexpected value {{_other:?}}"
                    )),
                ]))]
                .to_vec(),
            ),
            RustCatchAll::ReturnErrorValue { value } => (
                MatchCaseLHS::Pattern(RustPattern::CatchAll(None)),
                [RustStmt::Return(ReturnKind::Keyword, value.clone())].to_vec(),
            ),
        }
    }
}

pub(crate) type RustMatchCase<BlockType = Vec<RustStmt>> = (MatchCaseLHS, BlockType);

impl<T> From<Vec<RustMatchCase<T>>> for RustMatchBody<T> {
    fn from(value: Vec<RustMatchCase<T>>) -> Self {
        RustMatchBody::Refutable(
            value,
            RustCatchAll::ReturnErrorValue {
                value: RustExpr::scoped(["ParseError"], "ExcludedBranch"),
            },
        )
    }
}

#[derive(Clone, Debug)]
pub(crate) enum RustMatchBody<BlockType = Vec<RustStmt>> {
    Irrefutable(Vec<RustMatchCase<BlockType>>),
    Refutable(Vec<RustMatchCase<BlockType>>, RustCatchAll),
}

impl RustMatchBody {
    #[expect(dead_code)]
    pub fn tuple_capture<const N: usize>(
        labels: [&'static str; N],
        semantics: [CaptureSemantics; N],
    ) -> Self {
        let case_valid = {
            let lhs = {
                let pat = RustPattern::tuple_capture(labels, semantics);
                MatchCaseLHS::Pattern(pat)
            };
            let rhs = {
                let stmt = {
                    let expr = RustExpr::Tuple(labels.into_iter().map(RustExpr::local).collect());
                    RustStmt::Expr(expr)
                };
                vec![stmt]
            };
            (lhs, rhs)
        };
        Self::Irrefutable(vec![case_valid])
    }
}

impl ToFragment for RustMatchBody {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustMatchBody::Irrefutable(cases) => {
                <RustMatchCase>::block_sep(cases, Fragment::string(",\n"))
            }
            RustMatchBody::Refutable(cases, catchall) => <RustMatchCase>::block_sep(
                cases
                    .iter()
                    .chain(std::iter::once(&catchall.to_match_case())),
                Fragment::string(",\n"),
            ),
        }
    }
}

impl<T> RustMatchBody<T> {
    fn translate<U: From<T>>(self) -> RustMatchBody<U> {
        fn from_branches<T, U: From<T>>(branches: Vec<RustMatchCase<T>>) -> Vec<RustMatchCase<U>> {
            branches
                .into_iter()
                .map(|(pat, rhs)| (pat, rhs.into()))
                .collect()
        }
        match self {
            RustMatchBody::Irrefutable(block) => RustMatchBody::Irrefutable(from_branches(block)),
            RustMatchBody::Refutable(block, catchall) => {
                RustMatchBody::Refutable(from_branches(block), catchall)
            }
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum RustControl<BlockType = Vec<RustStmt>> {
    Loop(BlockType),
    While(RustExpr, BlockType),
    ForIter(Label, RustExpr, BlockType), // element variable name, iterator expression (verbatim), loop contents
    ForRange0(Label, RustExpr, BlockType), // index variable name, upper bound (exclusive), loop contents (0..N)
    If(RustExpr, BlockType, Option<BlockType>),
    Match(RustExpr, RustMatchBody<BlockType>),
    Break, // no support for break values or loop labels, yet
}

impl<T> RustControl<T> {
    pub(crate) fn translate<U: From<T>>(self) -> RustControl<U> {
        match self {
            RustControl::Loop(block) => RustControl::Loop(U::from(block)),
            RustControl::While(cond, block) => RustControl::While(cond, U::from(block)),
            RustControl::ForIter(iter_var, iter, block) => {
                RustControl::ForIter(iter_var, iter, U::from(block))
            }
            RustControl::ForRange0(iter_var, range_max, block) => {
                RustControl::ForRange0(iter_var, range_max, U::from(block))
            }
            RustControl::If(cond, then, opt_else) => {
                RustControl::If(cond, U::from(then), opt_else.map(U::from))
            }
            RustControl::Match(scrutinee, body) => RustControl::Match(scrutinee, body.translate()),
            RustControl::Break => RustControl::Break,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub enum CaptureSemantics {
    #[default]
    Owned,
    Ref,
}

impl CaptureSemantics {
    pub fn is_ref(self) -> bool {
        matches!(self, Self::Ref)
    }
}

impl RustPattern {
    /// Manually replaces a direct capture of a variable with a `ref` binding under the same name, or preserves
    /// the original value if some other pattern.
    pub(crate) fn ref_hack(self) -> Self {
        match self {
            RustPattern::CatchAll(Some(label)) => RustPattern::BindRef(label),
            _ => self,
        }
    }

    /// Captures an `N`-tuple with the provided per-position labels, along with a boolean flag
    /// to signal to bind by `ref` (if true) or by direct identifier capture (if false).
    pub(crate) fn tuple_capture<Name: IntoLabel, const N: usize>(
        bindings: [Name; N],
        semantics: [CaptureSemantics; N],
    ) -> Self {
        let mut binds = Vec::with_capacity(N);
        for (name, sem) in Iterator::zip(bindings.into_iter(), semantics.into_iter()) {
            let pat = if sem.is_ref() {
                RustPattern::BindRef(name.into())
            } else {
                RustPattern::CatchAll(Some(name.into()))
            };
            binds.push(pat)
        }
        RustPattern::TupleLiteral(binds)
    }
}

#[derive(Clone, Debug)]
pub(crate) enum MatchCaseLHS {
    Pattern(RustPattern),
    WithGuard(RustPattern, RustExpr),
}

impl MatchCaseLHS {
    pub(crate) fn is_simple(&self) -> bool {
        matches!(self, MatchCaseLHS::Pattern(..))
    }
}

impl ToFragment for MatchCaseLHS {
    fn to_fragment(&self) -> Fragment {
        match self {
            MatchCaseLHS::Pattern(pat) => pat.to_fragment(),
            MatchCaseLHS::WithGuard(pat, guard) => pat
                .to_fragment()
                .intervene(Fragment::string(" if "), guard.to_fragment()),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum RustPattern {
    PrimLiteral(RustPrimLit),
    PrimRange(RustPrimLit, Option<RustPrimLit>),
    TupleLiteral(Vec<RustPattern>),
    ArrayLiteral(Vec<RustPattern>),
    Option(Option<Box<RustPattern>>),
    Fill,                                   // `..`
    CatchAll(Option<Label>),                // Wildcard when None, otherwise a variable-binding
    BindRef(Label),                         // "x" => `ref x`
    Variant(Constructor, Box<RustPattern>), // FIXME - need to attach enum scope
}

#[derive(Debug, Clone)]
pub(crate) enum Constructor {
    // Simple struct constructor (mostly used for in-scope-by-default variants like `Ok` and `None`)
    Simple(Label),
    // Compound: Variant with intervening `::` between labels
    Compound(Label, Label),
}

impl From<Constructor> for RustEntity {
    fn from(value: Constructor) -> Self {
        match value {
            Constructor::Simple(lab) => RustEntity::Local(lab),
            Constructor::Compound(path, lab) => RustEntity::Scoped(vec![path], lab),
        }
    }
}

impl From<Constructor> for Label {
    fn from(value: Constructor) -> Self {
        match value {
            Constructor::Simple(lab) => lab,
            Constructor::Compound(path, var) => format!("{path}::{var}").into(),
        }
    }
}

impl ToFragment for RustPattern {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustPattern::PrimLiteral(pl) => pl.to_fragment(),
            RustPattern::PrimRange(pl0, Some(pl1)) => pl0
                .to_fragment()
                .intervene(Fragment::string("..="), pl1.to_fragment()),
            RustPattern::PrimRange(pl0, None) => pl0.to_fragment().cat(Fragment::string("..")),
            RustPattern::TupleLiteral(tup) => RustPattern::paren_list(tup),
            RustPattern::ArrayLiteral(tup) => RustPattern::brace_list(tup),
            RustPattern::Variant(constr, inner) => {
                RustExpr::Entity(RustEntity::from(constr.clone()))
                    .to_fragment()
                    .cat(
                        inner
                            .to_fragment()
                            .delimit(Fragment::Char('('), Fragment::Char(')')),
                    )
            }
            RustPattern::Fill => Fragment::String("..".into()),
            RustPattern::CatchAll(None) => Fragment::Char('_'),
            RustPattern::CatchAll(Some(lab)) => lab.to_fragment(),
            RustPattern::BindRef(lab) => Fragment::string("ref ").cat(lab.to_fragment()),
            RustPattern::Option(None) => Fragment::string("None"),
            RustPattern::Option(Some(pat)) => Fragment::string("Some").cat(
                pat.to_fragment()
                    .delimit(Fragment::Char('('), Fragment::Char(')')),
            ),
        }
    }
}

impl ToFragment for RustControl {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustControl::Loop(body) => Fragment::string("loop")
                .intervene(Fragment::Char(' '), RustStmt::block(body.iter())),
            RustControl::While(cond, body) => Fragment::string("while")
                .intervene(
                    Fragment::Char(' '),
                    cond.to_fragment_precedence(Precedence::TOP),
                )
                .intervene(Fragment::Char(' '), RustStmt::block(body.iter())),
            RustControl::If(cond, b_then, b_else) => Fragment::string("if")
                .intervene(
                    Fragment::Char(' '),
                    cond.to_fragment_precedence(Precedence::TOP),
                )
                .intervene(Fragment::Char(' '), RustStmt::block(b_then.iter()))
                .intervene(
                    Fragment::string(" else "),
                    Fragment::opt(b_else.as_ref(), |branch| RustStmt::block(branch.iter())),
                ),
            RustControl::Match(expr, body) => Fragment::string("match")
                .intervene(
                    Fragment::Char(' '),
                    expr.to_fragment_precedence(Precedence::TOP),
                )
                .intervene(Fragment::Char(' '), body.to_fragment()),
            RustControl::ForRange0(ctr_name, ubound, body) => Fragment::string("for")
                .intervene(Fragment::Char(' '), Fragment::String(ctr_name.clone()))
                .intervene(
                    Fragment::string(" in "),
                    Fragment::cat(
                        Fragment::string("0.."),
                        ubound.to_fragment_precedence(Precedence::TOP),
                    ),
                )
                .intervene(Fragment::Char(' '), RustStmt::block(body.iter())),
            RustControl::ForIter(elt_name, iterable, body) => Fragment::string("for")
                .intervene(Fragment::Char(' '), Fragment::String(elt_name.clone()))
                .intervene(
                    Fragment::string(" in "),
                    iterable.to_fragment_precedence(Precedence::TOP),
                )
                .intervene(Fragment::Char(' '), RustStmt::block(body.iter())),
            RustControl::Break => Fragment::string("break"),
        }
    }
}

impl ToFragment for (MatchCaseLHS, Vec<RustStmt>) {
    fn to_fragment(&self) -> Fragment {
        self.0
            .to_fragment()
            .intervene(Fragment::string(" => "), RustStmt::block(self.1.iter()))
    }
}

impl ToFragment for RustStmt {
    fn to_fragment(&self) -> Fragment {
        match self {
            RustStmt::Let(_mut, binding, sig, value) => (match _mut {
                Mut::Mutable => Fragment::string("let mut "),
                Mut::Immutable => Fragment::string("let "),
            })
            .cat(binding.to_fragment())
            .intervene(
                Fragment::string(": "),
                Fragment::opt(sig.as_ref(), RustType::to_fragment),
            )
            .cat(Fragment::string(" = "))
            .cat(value.to_fragment_precedence(Precedence::TOP))
            .cat(Fragment::Char(';')),
            RustStmt::LetPattern(pat, value) => Fragment::string("let ")
                .cat(pat.to_fragment())
                .cat(Fragment::string(" = "))
                .cat(value.to_fragment_precedence(Precedence::TOP))
                .cat(Fragment::Char(';')),
            RustStmt::Reassign(binding, value) => binding
                .to_fragment()
                .cat(Fragment::string(" = "))
                .cat(value.to_fragment_precedence(Precedence::TOP))
                .cat(Fragment::Char(';')),
            RustStmt::Expr(expr) => expr
                .to_fragment_precedence(Precedence::TOP)
                .cat(Fragment::Char(';')),
            RustStmt::Return(kind, expr) => {
                let (before, after) = if kind.is_keyword() {
                    (Fragment::String("return ".into()), Fragment::Char(';'))
                } else {
                    (Fragment::Empty, Fragment::Empty)
                };
                expr.to_fragment_precedence(Precedence::TOP)
                    .delimit(before, after)
            } // RustStmt::Control(ctrl) => ctrl.to_fragment(),
        }
    }
}

pub trait ToFragment {
    fn to_fragment(&self) -> Fragment;

    fn delim_list<'a>(
        items: impl IntoIterator<Item = &'a Self>,
        before: Fragment,
        after: Fragment,
    ) -> Fragment
    where
        Self: 'a,
    {
        Fragment::seq(
            items.into_iter().map(Self::to_fragment),
            Some(Fragment::string(", ")),
        )
        .delimit(before, after)
    }

    fn paren_list<'a>(items: impl IntoIterator<Item = &'a Self>) -> Fragment
    where
        Self: 'a,
    {
        Self::delim_list(items, Fragment::Char('('), Fragment::Char(')'))
    }

    fn brace_list<'a>(items: impl IntoIterator<Item = &'a Self>) -> Fragment
    where
        Self: 'a,
    {
        Self::delim_list(items, Fragment::Char('['), Fragment::Char(']'))
    }

    fn block<'a>(items: impl IntoIterator<Item = &'a Self>) -> Fragment
    where
        Self: 'a,
    {
        Self::block_sep(items, Fragment::Empty)
    }

    fn block_sep<'a>(items: impl IntoIterator<Item = &'a Self>, sep: Fragment) -> Fragment
    where
        Self: 'a,
    {
        let lines = items.into_iter().map(Self::to_fragment);
        Fragment::seq(lines, Some(Fragment::cat(sep, Fragment::Char('\n'))))
            .delimit(Fragment::string("{\n"), Fragment::string("\n}"))
    }
}

trait ToFragmentExt: ToFragment {
    fn to_fragment_precedence(&self, prec: Precedence) -> Fragment;

    fn delim_list_prec<'a>(
        items: impl IntoIterator<Item = &'a Self>,
        prec: Precedence,
        before: Fragment,
        after: Fragment,
    ) -> Fragment
    where
        Self: 'a,
    {
        Fragment::seq(
            items.into_iter().map(|x| x.to_fragment_precedence(prec)),
            Some(Fragment::string(", ")),
        )
        .delimit(before, after)
    }

    fn paren_list_prec<'a>(items: impl IntoIterator<Item = &'a Self>, prec: Precedence) -> Fragment
    where
        Self: 'a,
    {
        Self::delim_list_prec(items, prec, Fragment::Char('('), Fragment::Char(')'))
    }
}

impl<T> ToFragment for Box<T>
where
    T: ToFragment,
{
    fn to_fragment(&self) -> Fragment {
        self.as_ref().to_fragment()
    }
}

impl<T> ToFragmentExt for Box<T>
where
    T: ToFragmentExt,
{
    fn to_fragment_precedence(&self, prec: Precedence) -> Fragment {
        self.as_ref().to_fragment_precedence(prec)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn expect_fragment(value: &impl ToFragmentExt, expected: &str) {
        assert_eq!(
            &format!("{}", value.to_fragment_precedence(Precedence::TOP)),
            expected
        )
    }

    #[test]
    fn sample_type() {
        let rt = RustType::vec_of(RustType::anon_tuple([
            RustType::imported("Label"),
            RustType::imported("TypeRef"),
        ]));
        expect_fragment(&rt, "Vec<(Label, TypeRef)>");
    }

    #[test]
    fn sample_expr() {
        let re = RustExpr::local("this").call_method_with(
            "append",
            [RustExpr::BorrowMut(Box::new(RustExpr::local("other")))],
        );
        expect_fragment(&re, "this.append(&mut other)")
    }
}

pub mod short_circuit {
    use super::{
        OwnedRustExpr, ReturnKind, RustCatchAll, RustControl, RustExpr, RustMacro, RustMatchBody,
        RustMatchCase, RustOp, RustStmt, StructExpr, VecExpr,
    };

    #[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
    pub enum EvalPurity {
        /// Can never constitute a short-circuit
        Pure = 0,
        /// Short-circuit if and only if it is the only non-pure term in a terminal value-producing node
        Try = 1,
        /// Explicit `return` keyword -- constitutes a potential short-circuit regardless of context
        Return = 2,
    }

    impl std::ops::BitOr for EvalPurity {
        type Output = Self;

        fn bitor(self, rhs: Self) -> Self::Output {
            match self {
                EvalPurity::Pure => rhs,
                EvalPurity::Try => match rhs {
                    EvalPurity::Return => EvalPurity::Return,
                    _ => self,
                },
                EvalPurity::Return => EvalPurity::Return,
            }
        }
    }

    impl std::ops::BitOrAssign for EvalPurity {
        fn bitor_assign(&mut self, rhs: Self) {
            if matches!(
                (&self, rhs),
                (EvalPurity::Pure, _) | (_, EvalPurity::Return)
            ) {
                *self = rhs;
            }
        }
    }

    pub trait ShortCircuit {
        /// Returns `true` if `self` might have a (non-panic) short-circuit, as `return` or a Try (`?`) expression.
        fn is_short_circuiting(&self) -> bool;
    }

    pub trait ShortCircuitExt: ShortCircuit {
        /// Returns the eval-purity of the given Rust-AST node.
        fn check_eval_purity(&self) -> EvalPurity;

        /// Returns `true` if there is a 'true' short-circuit before the final value returned by the evaluation of `self`
        /// as in `BlockScope` with a short-circuiting statement.
        ///
        /// Used to determine whether a closure can be beta-reduced.
        fn has_short_circuit(&self, is_last: bool) -> bool {
            match self.check_eval_purity() {
                EvalPurity::Pure => false,
                EvalPurity::Try => !is_last,
                EvalPurity::Return => true,
            }
        }
    }

    pub trait ValueCheckpoint {
        /// Returns `true` if, as a value-producing AST node, `self` would need to be wrapped in `Ok(..)` in order to
        /// properly encompass internal short-circuiting.
        fn needs_ok(&self) -> bool;
    }

    impl ValueCheckpoint for RustExpr {
        fn needs_ok(&self) -> bool {
            match self {
                RustExpr::ResultOk(..) => false,
                RustExpr::BlockScope(.., ret) => ret.needs_ok(),
                RustExpr::Control(ctrl) => ctrl.needs_ok(),
                _ => true,
            }
        }
    }

    impl ValueCheckpoint for RustControl {
        fn needs_ok(&self) -> bool {
            match self {
                RustControl::Match(.., body) => match body {
                    RustMatchBody::Refutable(.., RustCatchAll::ReturnErrorValue { .. }) => true,
                    RustMatchBody::Refutable(cases, ..) | RustMatchBody::Irrefutable(cases) => {
                        cases
                            .iter()
                            .map(|(_, body)| body)
                            .any(<Vec<RustStmt>>::needs_ok)
                    }
                },
                // REVIEW - check these  always-true conditions
                RustControl::Loop(..) => true,
                RustControl::While(..) => true,
                RustControl::ForRange0(..) => true,
                RustControl::ForIter(..) => true,
                RustControl::If(.., None) => true,
                RustControl::Break => {
                    unreachable!("bad descent: ValueCheckpoint::needs_ok hit RustControl::Break")
                }
                RustControl::If(.., t, Some(f)) => t.needs_ok() || f.needs_ok(),
            }
        }
    }

    impl ValueCheckpoint for Vec<RustStmt> {
        fn needs_ok(&self) -> bool {
            match self.last() {
                None => true,
                Some(stmt) => match stmt {
                    RustStmt::Let(..) | RustStmt::LetPattern(..) | RustStmt::Reassign(..) => true,
                    RustStmt::Expr(expr) | RustStmt::Return(_, expr) => expr.needs_ok(),
                    // RustStmt::Control(ctrl) => ctrl.needs_ok(),
                },
            }
        }
    }

    impl ShortCircuit for RustStmt {
        fn is_short_circuiting(&self) -> bool {
            match self {
                RustStmt::Expr(expr)
                | RustStmt::Reassign(.., expr)
                | RustStmt::Let(.., expr)
                | RustStmt::LetPattern(.., expr)
                | RustStmt::Return(ReturnKind::Implicit, expr) => expr.is_short_circuiting(),
                RustStmt::Return(ReturnKind::Keyword, ..) => true,
                // RustStmt::Control(ctrl) => ctrl.is_short_circuiting(),
            }
        }
    }

    impl ShortCircuitExt for RustStmt {
        fn check_eval_purity(&self) -> EvalPurity {
            match self {
                RustStmt::Expr(expr)
                | RustStmt::Reassign(.., expr)
                | RustStmt::Let(.., expr)
                | RustStmt::LetPattern(.., expr)
                | RustStmt::Return(ReturnKind::Implicit, expr) => expr.check_eval_purity(),
                RustStmt::Return(ReturnKind::Keyword, ..) => EvalPurity::Try,
                // RustStmt::Control(ctrl) => ctrl.check_eval_purity(),
            }
        }
    }

    impl<T> ShortCircuit for Vec<T>
    where
        T: ShortCircuit,
    {
        fn is_short_circuiting(&self) -> bool {
            self.iter().any(T::is_short_circuiting)
        }
    }

    impl<BlockType: ShortCircuit> ShortCircuit for RustControl<BlockType> {
        fn is_short_circuiting(&self) -> bool {
            match self {
                RustControl::Loop(stmts) => stmts.is_short_circuiting(),
                RustControl::ForIter(_, expr, stmts)
                | RustControl::While(expr, stmts)
                | RustControl::ForRange0(_, expr, stmts) => {
                    expr.is_short_circuiting() || stmts.is_short_circuiting()
                }
                RustControl::If(cond, then, opt_else) => {
                    cond.is_short_circuiting()
                        || then.is_short_circuiting()
                        || opt_else
                            .as_ref()
                            .is_some_and(<BlockType as ShortCircuit>::is_short_circuiting)
                }
                RustControl::Match(scrutinee, body) => {
                    scrutinee.is_short_circuiting() || body.is_short_circuiting()
                }
                RustControl::Break => false,
            }
        }
    }

    impl<BlockType> ShortCircuitExt for RustControl<BlockType>
    where
        BlockType: ShortCircuitExt,
    {
        fn check_eval_purity(&self) -> EvalPurity {
            match self {
                RustControl::Loop(stmts) => stmts.check_eval_purity(),
                RustControl::ForIter(_, expr, stmts)
                | RustControl::While(expr, stmts)
                | RustControl::ForRange0(_, expr, stmts) => {
                    expr.check_eval_purity() | stmts.check_eval_purity()
                }
                RustControl::If(cond, then, opt_else) => {
                    cond.check_eval_purity()
                        | then.check_eval_purity()
                        | opt_else
                            .as_ref()
                            .map_or(EvalPurity::Pure, BlockType::check_eval_purity)
                }
                RustControl::Match(scrutinee, body) => {
                    scrutinee.check_eval_purity() | body.check_eval_purity()
                }
                RustControl::Break => EvalPurity::Pure,
            }
        }
    }

    impl<BlockType: ShortCircuit> ShortCircuit for RustMatchCase<BlockType> {
        fn is_short_circuiting(&self) -> bool {
            self.1.is_short_circuiting()
        }
    }

    impl<BlockType: ShortCircuitExt> ShortCircuitExt for RustMatchCase<BlockType> {
        fn check_eval_purity(&self) -> EvalPurity {
            self.1.check_eval_purity()
        }
    }

    impl<BlockType: ShortCircuit> ShortCircuit for RustMatchBody<BlockType> {
        fn is_short_circuiting(&self) -> bool {
            match self {
                RustMatchBody::Irrefutable(branches) => branches.is_short_circuiting(),
                RustMatchBody::Refutable(branches, rust_catch_all) => match rust_catch_all {
                    RustCatchAll::ReturnErrorValue { .. } => true,
                    RustCatchAll::PanicUnreachable { .. } => branches.is_short_circuiting(),
                },
            }
        }
    }

    impl<BlockType: ShortCircuitExt> ShortCircuitExt for RustMatchBody<BlockType> {
        fn check_eval_purity(&self) -> EvalPurity {
            match self {
                RustMatchBody::Irrefutable(branches) => branches.check_eval_purity(),
                RustMatchBody::Refutable(branches, rust_catch_all) => match rust_catch_all {
                    RustCatchAll::ReturnErrorValue { .. } => EvalPurity::Try,
                    RustCatchAll::PanicUnreachable { .. } => branches.check_eval_purity(),
                },
            }
        }
    }

    impl<BlockType: ShortCircuitExt> ShortCircuitExt for Vec<RustMatchCase<BlockType>> {
        fn check_eval_purity(&self) -> EvalPurity {
            self.iter()
                .map(<RustMatchCase<BlockType>>::check_eval_purity)
                .max()
                .unwrap_or(EvalPurity::Pure)
        }
    }

    impl ShortCircuit for RustExpr {
        fn is_short_circuiting(&self) -> bool {
            match self {
                RustExpr::ArrayLit(exprs) => exprs.is_short_circuiting(),
                RustExpr::Entity(..) => false,
                RustExpr::PrimitiveLit(..) => false,
                RustExpr::MethodCall(recv, _, args) => {
                    recv.is_short_circuiting() || args.is_short_circuiting()
                }
                RustExpr::FieldAccess(expr, ..) => expr.is_short_circuiting(),
                RustExpr::FunctionCall(.., args) => args.is_short_circuiting(),
                RustExpr::Tuple(elts) => elts.is_short_circuiting(),
                RustExpr::Struct(.., struct_expr) => struct_expr.is_short_circuiting(),
                RustExpr::Owned(OwnedRustExpr { expr: inner, .. })
                | RustExpr::Borrow(inner)
                | RustExpr::ResultOk(.., inner)
                | RustExpr::ResultErr(inner)
                | RustExpr::BorrowMut(inner) => inner.is_short_circuiting(),
                RustExpr::Try(inner) => match inner.as_ref() {
                    RustExpr::ResultOk(.., expr) => expr.is_short_circuiting(),
                    _ => true,
                },
                RustExpr::Operation(op) => op.is_short_circuiting(),
                RustExpr::BlockScope(stmts, expr) => {
                    stmts.is_short_circuiting() || expr.is_short_circuiting()
                }
                RustExpr::Macro(RustMacro::Matches(expr, ..)) => expr.is_short_circuiting(),
                RustExpr::Macro(RustMacro::Vec(vec_expr)) => vec_expr.is_short_circuiting(),
                RustExpr::Control(ctrl) => ctrl.is_short_circuiting(),
                RustExpr::Closure(..) => false,
                RustExpr::Index(head, index) => {
                    head.is_short_circuiting() || index.is_short_circuiting()
                }
                RustExpr::Slice(seq, start, stop) => {
                    seq.is_short_circuiting()
                        || start.is_short_circuiting()
                        || stop.is_short_circuiting()
                }
                RustExpr::RangeExclusive(start, stop) => {
                    start.is_short_circuiting() || stop.is_short_circuiting()
                }
            }
        }
    }

    macro_rules! short_circuit_ext_vec {
        ( $( $t:ty ),+ $(,)? ) => {
            $(
                impl ShortCircuitExt for Vec<$t> {
                    fn check_eval_purity(&self) -> EvalPurity {
                        let mut acc = EvalPurity::Pure;
                        for expr in self.iter() {
                            if acc == EvalPurity::Return { break; }
                            acc |= expr.check_eval_purity();
                        }
                        acc
                    }
                }
            )+
        };
    }

    impl ShortCircuitExt for Vec<RustStmt> {
        fn check_eval_purity(&self) -> EvalPurity {
            let mut acc = EvalPurity::Pure;
            for expr in self.iter() {
                if matches!(acc, EvalPurity::Try | EvalPurity::Return) {
                    return EvalPurity::Return;
                }
                acc |= expr.check_eval_purity();
            }
            acc
        }
    }

    short_circuit_ext_vec!(RustExpr, (crate::Label, Option<RustExpr>));

    impl ShortCircuitExt for RustExpr {
        fn check_eval_purity(&self) -> EvalPurity {
            match self {
                RustExpr::ArrayLit(exprs) => exprs.check_eval_purity(),
                RustExpr::Entity(..) | RustExpr::PrimitiveLit(..) => EvalPurity::Pure,
                RustExpr::Closure(..) => EvalPurity::Pure,
                RustExpr::MethodCall(recv, _, args) => {
                    recv.check_eval_purity() | args.check_eval_purity()
                }
                RustExpr::FieldAccess(expr, ..) => expr.check_eval_purity(),
                RustExpr::FunctionCall(.., args) => args.check_eval_purity(),
                RustExpr::Tuple(elts) => elts.check_eval_purity(),
                RustExpr::Struct(.., struct_expr) => struct_expr.check_eval_purity(),
                RustExpr::Owned(OwnedRustExpr { expr: inner, .. })
                | RustExpr::Borrow(inner)
                | RustExpr::ResultOk(.., inner)
                | RustExpr::ResultErr(inner)
                | RustExpr::BorrowMut(inner) => inner.check_eval_purity(),
                RustExpr::Try(inner) => match inner.as_ref() {
                    RustExpr::ResultOk(.., expr) => expr.check_eval_purity(),
                    _ => EvalPurity::Try,
                },
                RustExpr::Operation(op) => op.check_eval_purity(),
                RustExpr::BlockScope(stmts, expr) => {
                    stmts.check_eval_purity() | expr.check_eval_purity()
                }
                RustExpr::Macro(RustMacro::Matches(expr, ..)) => expr.check_eval_purity(),
                RustExpr::Macro(RustMacro::Vec(vec_expr)) => vec_expr.check_eval_purity(),
                RustExpr::Control(ctrl) => ctrl.check_eval_purity(),
                RustExpr::Index(head, index) => {
                    head.check_eval_purity() | index.check_eval_purity()
                }
                RustExpr::Slice(seq, start, stop) => {
                    seq.check_eval_purity() | start.check_eval_purity() | stop.check_eval_purity()
                }
                RustExpr::RangeExclusive(start, stop) => {
                    start.check_eval_purity() | stop.check_eval_purity()
                }
            }
        }
    }

    impl ShortCircuit for VecExpr {
        fn is_short_circuiting(&self) -> bool {
            match self {
                VecExpr::Nil => false,
                VecExpr::Single(x) => x.is_short_circuiting(),
                VecExpr::Repeat(x, n) => x.is_short_circuiting() || n.is_short_circuiting(),
                VecExpr::List(xs) => xs.is_short_circuiting(),
            }
        }
    }

    impl ShortCircuitExt for VecExpr {
        fn check_eval_purity(&self) -> EvalPurity {
            match self {
                VecExpr::Nil => EvalPurity::Pure,
                VecExpr::Single(x) => x.check_eval_purity(),
                VecExpr::Repeat(x, n) => x.check_eval_purity() | n.check_eval_purity(),
                VecExpr::List(xs) => xs.check_eval_purity(),
            }
        }
    }

    impl ShortCircuit for RustOp {
        fn is_short_circuiting(&self) -> bool {
            match self {
                RustOp::InfixOp(_, lhs, rhs) => {
                    lhs.is_short_circuiting() || rhs.is_short_circuiting()
                }
                RustOp::PrefixOp(_, expr) => expr.is_short_circuiting(),
                RustOp::AsCast(expr, _) => expr.is_short_circuiting(),
            }
        }
    }

    impl ShortCircuitExt for RustOp {
        fn check_eval_purity(&self) -> EvalPurity {
            match self {
                RustOp::InfixOp(_, lhs, rhs) => lhs.check_eval_purity() | rhs.check_eval_purity(),
                RustOp::PrefixOp(_, expr) | RustOp::AsCast(expr, _) => expr.check_eval_purity(),
            }
        }
    }

    impl ShortCircuit for (crate::Label, Option<RustExpr>) {
        fn is_short_circuiting(&self) -> bool {
            self.1.as_ref().is_some_and(RustExpr::is_short_circuiting)
        }
    }

    impl ShortCircuitExt for (crate::Label, Option<RustExpr>) {
        fn check_eval_purity(&self) -> EvalPurity {
            if let Some(expr) = self.1.as_ref() {
                expr.check_eval_purity()
            } else {
                EvalPurity::Pure
            }
        }
    }

    impl ShortCircuit for StructExpr {
        fn is_short_circuiting(&self) -> bool {
            match self {
                StructExpr::EmptyExpr => false,
                StructExpr::TupleExpr(elts) => elts.is_short_circuiting(),
                StructExpr::RecordExpr(flds) => flds.is_short_circuiting(),
            }
        }
    }

    impl ShortCircuitExt for StructExpr {
        fn check_eval_purity(&self) -> EvalPurity {
            match self {
                StructExpr::EmptyExpr => EvalPurity::Pure,
                StructExpr::TupleExpr(elts) => elts.check_eval_purity(),
                StructExpr::RecordExpr(flds) => flds.check_eval_purity(),
            }
        }
    }
}
pub use short_circuit::{ShortCircuit, ShortCircuitExt, ValueCheckpoint};

pub mod var_container {
    use super::{
        ClosureBody, MatchCaseLHS, OwnedRustExpr, RustCatchAll, RustClosure, RustClosureHead,
        RustControl, RustEntity, RustExpr, RustMacro, RustMatchBody, RustMatchCase, RustOp,
        RustPattern, RustStmt, StructExpr, VecExpr,
    };

    pub trait VarBinder {
        /// Returns `true` if self introduces a binding of `var` that
        /// shadows the same identifier's bindings from any external scopes.
        fn binds_var<Name: AsRef<str> + ?Sized>(&self, var: &Name) -> bool;
    }

    pub trait VarContainer {
        /// Returns `true` if an unbound (external) reference is made to a variable
        /// of the specified identifier.
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized;
    }

    impl<'a> VarContainer for [RustStmt] {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            for stmt in self.iter() {
                if stmt.binds_var(var) {
                    break;
                }
                if stmt.contains_var_ref(var) {
                    return true;
                }
            }
            false
        }
    }

    impl VarBinder for [RustStmt] {
        fn binds_var<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            for stmt in self.iter() {
                if stmt.binds_var(var) {
                    return true;
                }
            }
            false
        }
    }

    impl VarContainer for RustStmt {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                RustStmt::Let(.., value) => value.contains_var_ref(var),
                RustStmt::LetPattern(.., value) => value.contains_var_ref(var),
                RustStmt::Reassign(binding, value) => {
                    binding == var.as_ref() || value.contains_var_ref(var)
                }
                RustStmt::Expr(expr) => expr.contains_var_ref(var),
                RustStmt::Return(_, expr) => expr.contains_var_ref(var),
                // RustStmt::Control(ctrl) => ctrl.contains_var_ref(var),
            }
        }
    }

    impl VarBinder for RustStmt {
        fn binds_var<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                RustStmt::Let(_, name, ..) => name.as_ref() == var.as_ref(),
                RustStmt::LetPattern(pat, ..) => pat.binds_var(var),
                _ => false,
            }
        }
    }

    impl VarBinder for RustPattern {
        fn binds_var<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                // Non-binding patterns
                RustPattern::PrimLiteral(..) | RustPattern::PrimRange(..) => false,
                RustPattern::Fill => false,
                RustPattern::Option(None) => false,
                RustPattern::CatchAll(None) => false,

                // nested patterns
                RustPattern::TupleLiteral(pats) | RustPattern::ArrayLiteral(pats) => {
                    pats.iter().any(|pat| pat.binds_var(var))
                }
                RustPattern::Option(Some(pat)) | RustPattern::Variant(.., pat) => {
                    pat.binds_var(var)
                }

                // binding patterns
                RustPattern::BindRef(lab) | RustPattern::CatchAll(Some(lab)) => {
                    lab.as_ref() == var.as_ref()
                }
            }
        }
    }

    impl<'a> VarContainer for [RustExpr] {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            for expr in self.iter() {
                if expr.contains_var_ref(var) {
                    return true;
                }
            }
            false
        }
    }

    impl VarBinder for [RustExpr] {
        fn binds_var<Name>(&self, _: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            false
        }
    }

    impl VarContainer for StructExpr {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                StructExpr::EmptyExpr => false,
                StructExpr::TupleExpr(elts) => elts.contains_var_ref(var),
                StructExpr::RecordExpr(flds) => {
                    for (lab, expr) in flds.iter() {
                        match expr {
                            Some(expr) => {
                                if expr.contains_var_ref(var) {
                                    return true;
                                }
                            }
                            None => {
                                if lab.as_ref() == var.as_ref() {
                                    return true;
                                }
                            }
                        }
                    }
                    false
                }
            }
        }
    }

    impl VarBinder for StructExpr {
        fn binds_var<Name>(&self, _: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            false
        }
    }

    impl VarContainer for RustExpr {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                RustExpr::Entity(ent) => ent.contains_var_ref(var),
                RustExpr::FieldAccess(expr, ..) => expr.contains_var_ref(var),
                RustExpr::MethodCall(recv, .., args) => {
                    recv.contains_var_ref(var) || args.iter().any(|arg| arg.contains_var_ref(var))
                }
                RustExpr::FunctionCall(fun, args) => {
                    fun.contains_var_ref(var) || args.iter().any(|arg| arg.contains_var_ref(var))
                }
                RustExpr::Tuple(elts) => elts.contains_var_ref(var),
                RustExpr::Struct(.., struct_expr) => struct_expr.contains_var_ref(var),

                RustExpr::Owned(OwnedRustExpr { expr: inner, .. })
                | RustExpr::ResultOk(.., inner)
                | RustExpr::ResultErr(inner)
                | RustExpr::Borrow(inner)
                | RustExpr::BorrowMut(inner) => inner.contains_var_ref(var),

                RustExpr::Try(inner) => inner.contains_var_ref(var),
                RustExpr::Operation(op) => op.contains_var_ref(var),
                RustExpr::BlockScope(stmts, expr) => {
                    stmts.contains_var_ref(var)
                        || (!stmts.binds_var(var) && expr.contains_var_ref(var))
                }
                RustExpr::Macro(RustMacro::Matches(expr, ..)) => expr.contains_var_ref(var),
                RustExpr::Macro(RustMacro::Vec(vec_expr)) => vec_expr.contains_var_ref(var),
                RustExpr::Control(ctrl) => ctrl.contains_var_ref(var),
                RustExpr::PrimitiveLit(..) => false,
                RustExpr::ArrayLit(rust_exprs) => {
                    rust_exprs.iter().any(|elt| elt.contains_var_ref(var))
                }
                RustExpr::Closure(lambda) => lambda.contains_var_ref(var),

                RustExpr::Index(expr, ix) => expr.contains_var_ref(var) || ix.contains_var_ref(var),
                RustExpr::Slice(expr, ix0, ix1) => {
                    expr.contains_var_ref(var)
                        || ix0.contains_var_ref(var)
                        || ix1.contains_var_ref(var)
                }
                RustExpr::RangeExclusive(lo, hi) => {
                    lo.contains_var_ref(var) || hi.contains_var_ref(var)
                }
            }
        }
    }

    impl VarContainer for VecExpr {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                VecExpr::Nil => false,
                VecExpr::Single(x) => x.contains_var_ref(var),
                VecExpr::Repeat(x, n) => x.contains_var_ref(var) || n.contains_var_ref(var),
                VecExpr::List(xs) => xs.contains_var_ref(var),
            }
        }
    }

    impl VarContainer for RustClosure {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            if self.binds_var(var) {
                return false;
            }

            match &self.1 {
                ClosureBody::Expression(rust_expr) => rust_expr.contains_var_ref(var),
                ClosureBody::Statements(rust_stmts) => rust_stmts.contains_var_ref(var),
            }
        }
    }

    impl VarBinder for RustClosure {
        fn binds_var<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match &self.0 {
                RustClosureHead::Thunk => false,
                RustClosureHead::SimpleVar(head_var, ..) => head_var.as_ref() == var.as_ref(),
            }
        }
    }

    impl VarContainer for RustOp {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                RustOp::InfixOp(_, lhs, rhs) => {
                    lhs.contains_var_ref(var) || rhs.contains_var_ref(var)
                }
                RustOp::PrefixOp(_, expr) => expr.contains_var_ref(var),
                RustOp::AsCast(expr, _) => expr.contains_var_ref(var),
            }
        }
    }

    impl VarContainer for RustEntity {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                RustEntity::Local(lab) => lab.as_ref() == var.as_ref(),
                RustEntity::Scoped(..) => false,
            }
        }
    }

    impl VarContainer for RustControl {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                RustControl::Break => false,
                RustControl::ForIter(_, expr, body) => {
                    expr.contains_var_ref(var)
                        || (!self.binds_var(var) && body.contains_var_ref(var))
                }
                RustControl::ForRange0(_, lim, body) => {
                    lim.contains_var_ref(var)
                        || (!self.binds_var(var) && body.contains_var_ref(var))
                }
                RustControl::If(cond, then, o_else) => {
                    cond.contains_var_ref(var)
                        || then.contains_var_ref(var)
                        || o_else
                            .as_ref()
                            .is_some_and(|branch| branch.contains_var_ref(var))
                }
                RustControl::While(cond, body) => {
                    cond.contains_var_ref(var) || body.contains_var_ref(var)
                }
                RustControl::Loop(body) => body.contains_var_ref(var),
                RustControl::Match(expr, match_body) => {
                    expr.contains_var_ref(var) || match_body.contains_var_ref(var)
                }
            }
        }
    }

    impl VarBinder for RustControl<Vec<RustStmt>> {
        fn binds_var<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                RustControl::ForIter(lab, ..) | RustControl::ForRange0(lab, ..) => {
                    lab.as_ref() == var.as_ref()
                }
                RustControl::Break
                | RustControl::If(..)
                | RustControl::While(..)
                | RustControl::Loop(..)
                | RustControl::Match(..) => false,
            }
        }
    }

    impl VarContainer for RustMatchBody {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                RustMatchBody::Irrefutable(items) => {
                    items.iter().any(|branch| branch.contains_var_ref(var))
                }
                RustMatchBody::Refutable(items, catch_all) => {
                    items.iter().any(|branch| branch.contains_var_ref(var))
                        || (if let RustCatchAll::ReturnErrorValue { value } = catch_all {
                            value.contains_var_ref(var)
                        } else {
                            false
                        })
                }
            }
        }
    }

    impl VarContainer for RustMatchCase {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            self.0.contains_var_ref(var) || (!self.0.binds_var(var) && self.1.contains_var_ref(var))
        }
    }

    impl VarContainer for MatchCaseLHS {
        fn contains_var_ref<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                MatchCaseLHS::Pattern(..) => false,
                MatchCaseLHS::WithGuard(pat, expr) => {
                    !pat.binds_var(var) && expr.contains_var_ref(var)
                }
            }
        }
    }

    impl VarBinder for MatchCaseLHS {
        fn binds_var<Name>(&self, var: &Name) -> bool
        where
            Name: AsRef<str> + ?Sized,
        {
            match self {
                MatchCaseLHS::Pattern(pat) | MatchCaseLHS::WithGuard(pat, ..) => pat.binds_var(var),
            }
        }
    }
}
pub(crate) use var_container::VarContainer;
