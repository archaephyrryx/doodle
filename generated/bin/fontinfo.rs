use doodle_gencode::api_helper::*;

pub fn main() -> std::io::Result<()> {
    let args = std::env::args().skip(1).collect::<Vec<String>>();
    let iter: Box<dyn Iterator<Item = String>> = if !args.is_empty() {
        Box::new(args.into_iter())
    } else {
        // TODO - add local font folder to repository or remove this branch
        Box::new(std::iter::empty())
        // Box::new(
        //     std::fs::read_dir("test-images")?
        //         .flatten()
        //         .into_iter()
        //         .map(|entry| format!("test-images/{}", entry.file_name().to_string_lossy())),
        // )
    };
    do_work(iter)
}

fn do_work(iter: impl Iterator<Item = String>) -> std::io::Result<()> {
    let mut accum = Vec::new();
    for name in iter {
        eprint!("[{name}]: ...");
        match analyze_font(name.as_str()) {
            Ok(metric) => {
                eprintln!("Success!");
                accum.push((name, metric))
            }
            Err(e) => {
                eprintln!("Failed! ({e})")
            }
        }
    }
    for (filename, metrics) in accum {
        println!("====== [Font File]: {filename} =======");
        show_opentype_stats(&metrics);
        println!("====== END OF FONT FILE ======\n\n");
    }
    Ok(())
}
