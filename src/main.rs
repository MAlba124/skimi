use std::io::Write;

use skimi::{evaluator::Evaluator, parser::Parser};

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
        let mut parser = Parser::new(&chars);
        while let Ok(expr) = parser.parse_next() {
            // println!("{expr:?}");
            let res = e.eval(expr);
            match res {
                Ok(v) => println!("{v}"),
                Err(err) => eprintln!("{err}"),
            }
        }
    }
}

fn main() {
    repl();
}
