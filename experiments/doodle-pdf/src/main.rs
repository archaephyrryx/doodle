#![deny(rust_2018_idioms)]

use anyhow::{Result as AResult, anyhow};
use doodle::codegen::{ToFragment, generate_code};
use doodle::decoder::Compiler;
use doodle::read::ReadCtxt;
use doodle::{Format, FormatModule, typecheck};
use std::fs;
use std::path::PathBuf;

use clap::{Parser, ValueEnum};

mod pdf;

#[derive(Copy, Clone, ValueEnum)]
enum FormatOutput {
    /// Use the debug formatter
    Debug,
    /// Serialize to JSON
    Json,
    /// Generate Rust code
    Rust,
}

#[derive(Copy, Clone, ValueEnum)]
enum FileOutput {
    /// Use the debug formatter
    Debug,
    /// Serialize to JSON
    Json,
    /// Display as a human-readable tree
    Tree,
    /// Display as a filtered flat list
    Flat,
}

#[derive(Parser)]
enum Command {
    /// Dump the format used when decoding files
    Format {
        /// How the format is rendered
        #[arg(long)]
        output: FormatOutput,
        #[arg(long, default_value = None)]
        dest: Option<PathBuf>,
    },
    /// Decode a PDF file
    File {
        /// How decoded values are rendered
        #[arg(long, default_value = "tree")]
        output: FileOutput,
        /// The PDF file to decode
        filename: PathBuf,
        #[arg(long)]
        trace: bool,
    },
    /// Typecheck the PDF FormatModule
    TypeCheck,
}

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
    let level = if cfg!(debug_assertions) {
        log::Level::Debug
    } else {
        log::Level::Error
    };
    stderrlog::new()
        .module(module_path!())
        .verbosity(level)
        .init()
        .unwrap();

    let mut module = FormatModule::new();
    let format = pdf::main(&mut module).call();

    match Command::parse() {
        Command::Format { output, dest } => {
            match output {
                FormatOutput::Debug => println!("{module:?}"),
                FormatOutput::Json => serde_json::to_writer(std::io::stdout(), &module).unwrap(),
                FormatOutput::Rust => print_generated_code(&module, &format, dest),
            }
            Ok(())
        }
        Command::File {
            output,
            filename,
            trace,
        } => {
            let program = Compiler::compile_program(&module, &format)?;
            let input = fs::read(filename)?;
            match output {
                FileOutput::Debug => {
                    let (value, _) = program.run(ReadCtxt::new(&input))?;
                    println!("{value:?}");
                }
                FileOutput::Json => {
                    if trace {
                        let (p_value, _) = program.run_with_loc(ReadCtxt::new(&input))?;
                        serde_json::to_writer(std::io::stdout(), &p_value).unwrap()
                    } else {
                        let (value, _) = program.run(ReadCtxt::new(&input))?;
                        serde_json::to_writer(std::io::stdout(), &value).unwrap()
                    }
                }
                FileOutput::Tree => {
                    if trace {
                        let (p_value, _) = program.run_with_loc(ReadCtxt::new(&input))?;
                        doodle::output::tree::print_parsed_decoded_value(
                            &module, &p_value, &format,
                        );
                    } else {
                        let (value, _) = program.run(ReadCtxt::new(&input))?;
                        doodle::output::tree::print_decoded_value(&module, &value, &format);
                    }
                }
                FileOutput::Flat => {
                    let (value, _) = program.run(ReadCtxt::new(&input))?;
                    doodle::output::flat::print_decoded_value(&module, &value, &format);
                }
            }
            Ok(())
        }
        Command::TypeCheck => Ok(check_all(&module)?),
    }
}

fn check_all(module: &FormatModule) -> AResult<()> {
    for (level, f) in module.iter_formats() {
        if let Some(vt) = typecheck(module, &f).map_err(|err| anyhow!("{err}"))? {
            let mod_vt = module.get_format_type(level);
            assert!(
                vt.unify(&mod_vt).is_ok(),
                "incompatible typings:\ntc: {vt:?}\nmodule: {mod_vt:?}"
            );
        }
    }
    Ok(())
}

fn print_generated_code(module: &FormatModule, top_format: &Format, dest: Option<PathBuf>) {
    let content = generate_code(module, top_format);

    fn write_to(mut f: impl std::io::Write, content: impl ToFragment) -> std::io::Result<()> {
        write!(f, "{}", content.to_fragment())
    }

    match dest {
        None => write_to(std::io::stdout().lock(), content).expect("failed to write"),
        Some(path) => {
            if !path.exists()
                || (path.is_file()
                    && path
                        .file_name()
                        .is_some_and(|s| s.to_string_lossy().contains("gencode")))
            {
                let f = fs::File::create(path).unwrap_or_else(|err| panic!("error: {err}"));
                write_to(f, content).expect("failed to write");
            } else {
                panic!(
                    "will not overwrite directory or protected file: {}",
                    path.to_string_lossy()
                );
            }
        }
    }
}

#[test]
fn test_types() -> Result<(), anyhow::Error> {
    let mut module = FormatModule::new();
    let _ = pdf::main(&mut module);
    check_all(&module)
}
