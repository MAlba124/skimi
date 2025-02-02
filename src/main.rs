use std::{
    fs::File,
    io::{Read, Write},
    path::PathBuf,
};

use skimi::{
    evaluator::Evaluator,
    parser::{Expr, Parser},
};

fn repl() {
    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout();
    let mut e = Evaluator::new();
    loop {
        let mut buffer = String::new();
        print!("skimi> ");
        stdout.flush().unwrap();
        stdin.read_line(&mut buffer).unwrap();
        let chars = buffer.chars().collect::<Vec<char>>();
        // println!("{:?}", toks);
        let mut parser = Parser::new(&chars, "stdin".to_owned());
        loop {
            match parser.parse_next() {
                Ok(expr) => {
                    let res = e.eval(expr);
                    match res {
                        Ok(v) => {
                            if v != Expr::Null {
                                println!("{v}");
                            }
                        }
                        Err(err) => eprintln!("{err}"),
                    }
                }
                Err(err) if !err.is_eof() => {
                    eprintln!("{err}");
                    break;
                }
                _ => break,
            }
        }
    }
}

fn evaluate_file(file: &mut File) {
    let mut code = String::new();
    file.read_to_string(&mut code).unwrap();
    let chars = code.chars().collect::<Vec<char>>();
    let mut parser = Parser::new(&chars, "TODO".to_owned());
    let mut evaluator = Evaluator::new();
    loop {
        match parser.parse_next() {
            Ok(expr) => {
                let _ = evaluator.eval(expr).unwrap();
            }
            Err(err) if err.is_eof() => break,
            Err(err) => {
                eprintln!("{err}");
                break;
            }
        }
    }
}

fn main() {
    let mut files_to_evaluate: Vec<File> = Vec::new();

    for arg in std::env::args().skip(1) {
        let pb = PathBuf::from(arg);
        if pb.is_file() {
            files_to_evaluate.push(File::open(pb).unwrap());
        }
    }

    if files_to_evaluate.is_empty() {
        repl();
    } else {
        for mut file in files_to_evaluate.into_iter() {
            evaluate_file(&mut file);
        }
    }
}
