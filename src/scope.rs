use crate::{error::ParseResult, Decoder, Program, ReadCtxt, Value, ValueType};

pub struct TypeScope {
    names: Vec<String>,
    types: Vec<ValueType>,
}

impl TypeScope {
    pub fn new() -> Self {
        let names = Vec::new();
        let types = Vec::new();
        TypeScope { names, types }
    }

    pub fn push(&mut self, name: String, t: ValueType) {
        self.names.push(name);
        self.types.push(t);
    }

    pub fn pop(&mut self) -> ValueType {
        self.names.pop();
        self.types.pop().unwrap()
    }

    pub fn len(&self) -> usize {
        self.types.len()
    }

    pub fn truncate(&mut self, len: usize) {
        self.names.truncate(len);
        self.types.truncate(len);
    }

    pub fn get_type_by_name(&self, name: &str) -> &ValueType {
        for (i, n) in self.names.iter().enumerate().rev() {
            if n == name {
                return &self.types[i];
            }
        }
        panic!("variable not found: {name}");
    }
}

pub struct VecScope {
    names: Vec<String>,
    values: Vec<Value>,
    decoders: Vec<Option<Decoder>>,
}

impl VecScope {
    pub fn new() -> Self {
        let names = Vec::new();
        let values = Vec::new();
        let decoders = Vec::new();
        VecScope {
            names,
            values,
            decoders,
        }
    }

    pub fn push(&mut self, name: String, v: Value) {
        self.names.push(name);
        self.values.push(v);
        self.decoders.push(None);
    }

    pub fn pop(&mut self) -> Value {
        self.names.pop();
        self.decoders.pop();
        self.values.pop().unwrap()
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn truncate(&mut self, len: usize) {
        self.names.truncate(len);
        self.values.truncate(len);
        self.decoders.truncate(len);
    }

    pub fn extend(&mut self, other: VecScope) {
        self.names.extend(other.names);
        self.values.extend(other.values);
        self.decoders.extend(other.decoders);
    }

    pub fn get_index_by_name(&self, name: &str) -> usize {
        for (i, n) in self.names.iter().enumerate().rev() {
            if n == name {
                return i;
            }
        }
        panic!("variable not found: {name}");
    }

    pub fn get_value_by_name(&self, name: &str) -> &Value {
        &self.values[self.get_index_by_name(name)]
    }

    pub(crate) fn call_decoder_by_name<'input>(
        &mut self,
        name: &str,
        program: &Program,
        input: ReadCtxt<'input>,
    ) -> ParseResult<(Value, ReadCtxt<'input>)> {
        let i = self.get_index_by_name(name);
        let mut od = std::mem::replace(&mut self.decoders[i], None);
        if od.is_none() {
            let d = match &self.values[i] {
                Value::Format(f) => Decoder::compile_one(&*f).unwrap(),
                _ => panic!("variable not format: {name}"),
            };
            od = Some(d);
        }
        let res = od.as_ref().unwrap().parse(program, self, input);
        self.decoders[i] = od;
        res
    }
}

pub struct VecScopeIter {
    name_iter: std::vec::IntoIter<String>,
    value_iter: std::vec::IntoIter<Value>,
}

pub struct SliceScopeIter<'a> {
    name_iter: std::slice::Iter<'a, String>,
    value_iter: std::slice::Iter<'a, Value>,
}

impl<'a> Iterator for SliceScopeIter<'a> {
    type Item = (&'a String, &'a Value);

    fn next(&mut self) -> Option<Self::Item> {
        match (self.name_iter.next(), self.value_iter.next()) {
            (Some(name), Some(value)) => Some((name, value)),
            _ => None,
        }
    }
}

impl Iterator for VecScopeIter {
    type Item = (String, Value);

    fn next(&mut self) -> Option<Self::Item> {
        match (self.name_iter.next(), self.value_iter.next()) {
            (Some(name), Some(value)) => Some((name, value)),
            _ => None,
        }
    }
}

impl<'a> IntoIterator for &'a VecScope {
    type Item = (&'a String, &'a Value);

    type IntoIter = SliceScopeIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        SliceScopeIter {
            name_iter: self.names.iter(),
            value_iter: self.values.iter(),
        }
    }
}

impl VecScope {
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Value)> {
        (&self).into_iter()
    }
}

// NOTE - Scaffolding in case we ever want to redefine Scope to have more ergonomic nesting capabilities
pub type Scope = VecScope;
