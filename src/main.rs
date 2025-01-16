// References:
//  - https://github.com/rust-bakery/nom/blob/main/examples/s_expression.rs
// Goal: less than 1000 LOC

use std::{io::Write, iter::Peekable, str::Chars};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    OPar,
    CPar,
    Ident(String),
    Num(i64),
    Minus,
    Plus,
    Slash,
    Times,
    Bool(bool),
}

fn is_digit(ch: Option<&char>) -> bool {
    ch.map_or(false, |ch| ch.is_ascii_digit())
}

fn take_number(iter: &mut Peekable<Chars>) -> Option<i64> {
    let mut num_str = String::new();
    while let Some(ch) = iter.peek() {
        match ch {
            ' ' | ')' | '\n' => break,
            '0'..='9' => num_str.push(iter.next().expect("peek() says it's there")),
            _ => return None,
        }
    }
    num_str.parse::<i64>().ok()
}

fn take_ident(iter: &mut Peekable<Chars>) -> Option<String> {
    let mut ident = String::new();
    while let Some(ch) = iter.peek() {
        match ch {
            ' ' | ')' | '\n' => break,
            '-' | 'a'..='z' | 'A'..='Z' => ident.push(iter.next().expect("peek() says it's there")),
            _ => return None,
        }
    }
    Some(ident)
}

fn lex(s: &str) -> Vec<Tok> {
    let mut toks = Vec::new();
    let mut iter = s.chars().peekable();

    while let Some(ch) = iter.peek() {
        if ch.is_ascii_digit() {
            toks.push(Tok::Num(take_number(&mut iter).unwrap()));
            continue;
        } else if ch.is_ascii_alphabetic() {
            toks.push(Tok::Ident(take_ident(&mut iter).unwrap()));
            continue;
        }

        let ch = *ch;
        iter.next().expect("peek() says it's there");

        toks.push(match ch {
            '\n' | ' ' => continue,
            '(' => Tok::OPar,
            ')' => Tok::CPar,
            '+' => Tok::Plus,
            '/' => Tok::Slash,
            '*' => Tok::Times,
            '#' => {
                let next = iter.next().unwrap();
                if next == 'f' {
                    Tok::Bool(false)
                } else if next == 't' {
                    Tok::Bool(true)
                } else {
                    panic!("Illegal #{next}");
                }
            }
            '-' => {
                if is_digit(iter.peek()) {
                    Tok::Num(-take_number(&mut iter).unwrap())
                } else {
                    Tok::Minus
                }
            }
            _ => unreachable!("'{ch}'"),
        });
    }

    toks
}

#[derive(Debug, Clone)]
enum BuiltIn {
    Minus,
    Plus,
    Display,
    Slash,
    Times,
    If,
}

#[derive(Debug, Clone)]
enum Atom {
    Num(i64),
    BuiltIn(BuiltIn),
    Bool(bool),
}

#[derive(Debug, Clone)]
enum Expr {
    Constant(Atom),
    Ident(String),
    Application(Box<Expr>, Vec<Expr>),
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

impl Parser {
    pub fn new(toks: Vec<Tok>) -> Self {
        assert!(!toks.is_empty());
        Self { toks, pos: 0 }
    }

    pub fn parse(&mut self) -> Option<Expr> {
        if self.pos >= self.toks.len() {
            return None;
        }
        let tok = &self.toks[self.pos];
        self.pos += 1;
        Some(match tok {
            Tok::OPar => {
                let mut subs = Vec::new();
                while self.pos < self.toks.len() && self.toks[self.pos] != Tok::CPar {
                    subs.push(self.parse());
                }
                self.pos += 1;
                Expr::Application(
                    Box::new(subs.first().unwrap().clone()?),
                    subs.iter()
                        .skip(1)
                        .cloned()
                        .collect::<Option<Vec<Expr>>>()?,
                )
            }
            Tok::CPar => return None,
            Tok::Ident(i) => match i.as_str() {
                "display" => Expr::Constant(Atom::BuiltIn(BuiltIn::Display)),
                "if" => {
                    let mut subs = vec![self.parse()?, self.parse()?];
                    if let Some(false_branch) = self.parse() {
                        subs.push(false_branch);
                    }

                    Expr::Application(Box::new(Expr::Constant(Atom::BuiltIn(BuiltIn::If))), subs)
                }
                _ => Expr::Ident(i.clone()),
            },
            Tok::Num(n) => Expr::Constant(Atom::Num(*n)),
            Tok::Minus => Expr::Constant(Atom::BuiltIn(BuiltIn::Minus)),
            Tok::Plus => Expr::Constant(Atom::BuiltIn(BuiltIn::Plus)),
            Tok::Slash => Expr::Constant(Atom::BuiltIn(BuiltIn::Slash)),
            Tok::Times => Expr::Constant(Atom::BuiltIn(BuiltIn::Times)),
            Tok::Bool(b) => Expr::Constant(Atom::Bool(*b)),
        })
    }
}

fn get_num_from_expr(e: Expr) -> Option<i64> {
    if let Expr::Constant(Atom::Num(n)) = e {
        Some(n)
    } else {
        None
    }
}

fn get_bool_from_expr(e: Expr) -> Option<bool> {
    if let Expr::Constant(Atom::Bool(b)) = e {
        Some(b)
    } else {
        None
    }
}

fn fmt_expr(e: Expr) -> String {
    match e {
        Expr::Constant(c) => match c {
            Atom::Num(n) => n.to_string(),
            Atom::BuiltIn(bi) => match bi {
                BuiltIn::Minus => String::from("built_in<Minus>"),
                BuiltIn::Plus => String::from("built_in<Plus>"),
                BuiltIn::Slash => String::from("built_in<Slash>"),
                BuiltIn::Times => String::from("built_in<Times>"),
                BuiltIn::Display => String::from("built_in<Display>"),
                BuiltIn::If => String::from("non_printable<If>"),
            },
            Atom::Bool(b) => String::from(if b { "#t" } else { "#f" }),
        },
        Expr::Ident(i) => format!("identifier<{i}>"),
        Expr::Application(_, _) => String::from("non_printable<Application>"),
    }
}

fn eval(expr: Expr) -> Option<Expr> {
    match expr {
        Expr::Constant(_) | Expr::Ident(_) => Some(expr),
        Expr::Application(head, tail) => {
            let reduced_head = eval(*head)?;
            match reduced_head {
                Expr::Constant(Atom::BuiltIn(bi)) => {
                    Some(Expr::Constant(match bi {
                        BuiltIn::Minus => {
                            let reduced_tail =
                                tail.into_iter().map(eval).collect::<Option<Vec<Expr>>>()?;
                            Atom::Num(if let Some(first_elem) = reduced_tail.first().cloned() {
                                let fe = get_num_from_expr(first_elem)?;
                                reduced_tail
                                    .into_iter()
                                    .map(get_num_from_expr)
                                    .collect::<Option<Vec<i64>>>()?
                                    .into_iter()
                                    .skip(1)
                                    .fold(fe, |a, b| a - b)
                            } else {
                                Default::default()
                            })
                        }
                        BuiltIn::Plus => {
                            let reduced_tail =
                                tail.into_iter().map(eval).collect::<Option<Vec<Expr>>>()?;
                            Atom::Num(
                                reduced_tail
                                    .into_iter()
                                    .map(get_num_from_expr)
                                    .collect::<Option<Vec<i64>>>()?
                                    .into_iter()
                                    .sum(),
                            )
                        }
                        BuiltIn::Slash => {
                            let reduced_tail =
                                tail.into_iter().map(eval).collect::<Option<Vec<Expr>>>()?;
                            Atom::Num(if let Some(first_elem) = reduced_tail.first().cloned() {
                                let fe = get_num_from_expr(first_elem)?;
                                reduced_tail
                                    .into_iter()
                                    .map(get_num_from_expr)
                                    .collect::<Option<Vec<i64>>>()?
                                    .into_iter()
                                    .skip(1)
                                    .fold(fe, |a, b| a / b)
                            } else {
                                Default::default()
                            })
                        }
                        BuiltIn::Times => {
                            let reduced_tail =
                                tail.into_iter().map(eval).collect::<Option<Vec<Expr>>>()?;
                            Atom::Num(if let Some(first_elem) = reduced_tail.first().cloned() {
                                let fe = get_num_from_expr(first_elem)?;
                                reduced_tail
                                    .into_iter()
                                    .map(get_num_from_expr)
                                    .collect::<Option<Vec<i64>>>()?
                                    .into_iter()
                                    .skip(1)
                                    .fold(fe, |a, b| a * b)
                            } else {
                                Default::default()
                            })
                        }
                        BuiltIn::Display => {
                            let reduced_tail =
                                tail.into_iter().map(eval).collect::<Option<Vec<Expr>>>()?;
                            for (i, expr) in reduced_tail.iter().enumerate() {
                                print!(
                                    "{}{}",
                                    fmt_expr(expr.clone()),
                                    if i < reduced_tail.len() - 1 { " " } else { "" }
                                );
                            }
                            println!();
                            return None;
                        }
                        BuiltIn::If => {
                            let cond = &tail[0];
                            let true_branch = &tail[1];
                            let reduced_cond = eval(cond.clone());
                            if get_bool_from_expr(reduced_cond.unwrap()).unwrap() {
                                return eval(true_branch.clone());
                            } else if tail.len() > 2 {
                                return eval(tail[2].clone());
                            } else {
                                return None;
                            }
                        }
                    }))
                }
                // Expr::Ident(_) => todo!(),
                _ => unreachable!(),
            }
        }
    }
}

fn repl() {
    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout();
    loop {
        let mut buffer = String::new();
        print!("> ");
        stdout.flush().unwrap();
        stdin.read_line(&mut buffer).unwrap();
        let toks = lex(&buffer);
        // println!("{:?}", toks);
        let mut parser = Parser::new(toks);
        while let Some(expr) = parser.parse() {
            // println!("{expr:?}");
            println!("{:?}", eval(expr));
        }
    }
}

fn main() {
    repl();
}

#[cfg(test)]
mod tests {
    use crate::{is_digit, lex, take_ident, take_number, Tok};

    #[test]
    fn test_is_digit() {
        assert_eq!(is_digit(Some(&'7')), true);
        assert_eq!(is_digit(Some(&'a')), false);
    }

    #[test]
    fn test_take_ident() {
        assert_eq!(
            take_ident(&mut "this-is-an-identifier".chars().peekable()),
            Some(String::from("this-is-an-identifier"))
        );
    }

    #[test]
    fn test_take_num() {
        assert_eq!(take_number(&mut "1234".chars().peekable()), Some(1234),);
        assert_eq!(take_number(&mut "12e4".chars().peekable()), None,);
        assert_eq!(
            take_number(&mut "1241234234)".chars().peekable()),
            Some(1241234234),
        );
    }

    #[test]
    fn test_lex() {
        assert_eq!(
            lex("(1 2 3)"),
            vec![Tok::OPar, Tok::Num(1), Tok::Num(2), Tok::Num(3), Tok::CPar,]
        );
        assert_eq!(
            lex("(+ 1 2)"),
            vec![Tok::OPar, Tok::Plus, Tok::Num(1), Tok::Num(2), Tok::CPar,]
        );
        assert_eq!(
            lex("(+ 1 2 3)"),
            vec![
                Tok::OPar,
                Tok::Plus,
                Tok::Num(1),
                Tok::Num(2),
                Tok::Num(3),
                Tok::CPar,
            ]
        );
        assert_eq!(
            lex("(- 1 2)"),
            vec![Tok::OPar, Tok::Minus, Tok::Num(1), Tok::Num(2), Tok::CPar,]
        );
        assert_eq!(
            lex("(- 1 2 3)"),
            vec![
                Tok::OPar,
                Tok::Minus,
                Tok::Num(1),
                Tok::Num(2),
                Tok::Num(3),
                Tok::CPar,
            ]
        );
        assert_eq!(
            lex("(- 1 2 -3)"),
            vec![
                Tok::OPar,
                Tok::Minus,
                Tok::Num(1),
                Tok::Num(2),
                Tok::Num(-3),
                Tok::CPar,
            ]
        );
        assert_eq!(
            lex("(+ 1 an-identifier)"),
            vec![
                Tok::OPar,
                Tok::Plus,
                Tok::Num(1),
                Tok::Ident(String::from("an-identifier")),
                Tok::CPar,
            ]
        );
    }
}
