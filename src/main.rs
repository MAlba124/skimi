// References:
//  - https://github.com/rust-bakery/nom/blob/main/examples/s_expression.rs
// Goal: less than 1000 LOC

use std::{collections::HashMap, io::Write, iter::Peekable, str::Chars};

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
    Eq,
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
            '=' => Tok::Eq,
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

#[derive(Debug, Clone, PartialEq, Eq)]
enum BuiltIn {
    Minus,
    Plus,
    Display,
    Slash,
    Times,
    If,
    Eq,
    Define,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Atom {
    Num(i64),
    BuiltIn(BuiltIn),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Expr {
    Constant(Atom),
    Ident(String),
    List(Vec<Expr>),
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
                Expr::List(subs.into_iter().collect::<Option<Vec<Expr>>>()?)
            }
            Tok::CPar => return None,
            Tok::Ident(i) => match i.as_str() {
                "display" => Expr::Constant(Atom::BuiltIn(BuiltIn::Display)),
                "if" => {
                    let mut subs = vec![
                        Expr::Constant(Atom::BuiltIn(BuiltIn::If)),
                        self.parse()?,
                        self.parse()?,
                    ];
                    if let Some(false_branch) = self.parse() {
                        subs.push(false_branch);
                    }

                    Expr::List(subs)
                }
                "define" => {
                    Expr::List(vec![
                        Expr::Constant(Atom::BuiltIn(BuiltIn::Define)),
                        self.parse()?,
                        self.parse()?,
                    ])
                }
                _ => Expr::Ident(i.clone()),
            },
            Tok::Num(n) => Expr::Constant(Atom::Num(*n)),
            Tok::Minus => Expr::Constant(Atom::BuiltIn(BuiltIn::Minus)),
            Tok::Plus => Expr::Constant(Atom::BuiltIn(BuiltIn::Plus)),
            Tok::Slash => Expr::Constant(Atom::BuiltIn(BuiltIn::Slash)),
            Tok::Times => Expr::Constant(Atom::BuiltIn(BuiltIn::Times)),
            Tok::Bool(b) => Expr::Constant(Atom::Bool(*b)),
            Tok::Eq => Expr::Constant(Atom::BuiltIn(BuiltIn::Eq)),
        })
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
                BuiltIn::Eq => String::from("built_in<Eq>"),
                BuiltIn::Define => String::from("built_in<Define>"),
            },
            Atom::Bool(b) => String::from(if b { "#t" } else { "#f" }),
        },
        Expr::Ident(i) => format!("identifier<{i}>"),
        Expr::List(_) => String::from("non_printable<List>"), // TODO
    }
}

struct Evaluator {
    variable_stack: Vec<HashMap<String, Expr>>,
}

impl Evaluator {
    pub fn new() -> Self {
        Self {
            variable_stack: vec!(HashMap::new()),
        }
    }

    #[inline]
    fn push_to_current_scope(&mut self, ident: String, val: Expr) {
        match self.variable_stack.last_mut() {
            Some(last) => last.entry(ident).and_modify(|v| *v = val.clone()).or_insert(val),
            None => panic!("Missing scope on the variable stack"),
        };
    }

    #[inline]
    fn get_variable(&self, ident: String) -> Option<Expr> {
        for scope in self.variable_stack.iter().rev() {
            if scope.contains_key(&ident) {
                return scope.get(&ident).cloned();
            }
        }
        None
    }

    #[inline]
    fn get_num_from_expr(&self, e: Expr) -> Option<i64> {
        match e {
            Expr::Constant(Atom::Num(n)) => Some(n),
            Expr::Ident(i) => self.get_num_from_expr(self.get_variable(i)?),
            _ => None,
        }
    }

    #[inline]
    fn get_bool_from_expr(&self, e: Expr) -> Option<bool> {
        match e {
            Expr::Constant(Atom::Bool(b)) => Some(b),
            Expr::Ident(i) => self.get_bool_from_expr(self.get_variable(i)?),
            _ => None,
        }
    }

    #[inline]
    fn get_ident_string(&self, e: Expr) -> Option<String> {
        if let Expr::Ident(i) = e {
            Some(i)
        } else {
            None
        }
    }

    #[inline]
    fn reduce(&mut self, exprs: Vec<Expr>) -> Option<Vec<Expr>> {
        let mut reduced = Vec::new();
        for e in exprs {
            reduced.push(self.eval(e)?);
        }
        Some(reduced)
    }

    #[inline]
    fn display(&mut self, args: Vec<Expr>) {
        let len = args.len();
        for (i, expr) in self.reduce(args).unwrap().iter().enumerate() {
            print!(
                "{}{}",
                fmt_expr(expr.clone()),
                if i < len - 1 { " " } else { "" }
            );
        }
        println!();
    }

    #[inline]
    fn minus(&mut self, args: Vec<Expr>) -> Option<Atom> {
        let reduced_args = self.reduce(args)?;
        Some(Atom::Num(if let Some(first_elem) = reduced_args.first().cloned() {
            let fe = self.get_num_from_expr(first_elem)?;
            reduced_args
                .into_iter()
                .map(|e| self.get_num_from_expr(e))
                .collect::<Option<Vec<i64>>>()?
                .into_iter()
                .skip(1)
                .fold(fe, |a, b| a - b)
        } else {
            Default::default()
        }))
    }

    #[inline]
    fn plus(&mut self, args: Vec<Expr>) -> Option<Atom> {
        Some(Atom::Num(
            self.reduce(args)?
                .into_iter()
                .map(|e| self.get_num_from_expr(e))
                .collect::<Option<Vec<i64>>>()?
                .into_iter()
                .sum(),
        ))
    }

    #[inline]
    fn slash(&mut self, args: Vec<Expr>) -> Option<Atom> {
        let reduced_args = self.reduce(args)?;
        Some(Atom::Num(if let Some(first_elem) = reduced_args.first().cloned() {
            let fe = self.get_num_from_expr(first_elem)?;
            reduced_args
                .into_iter()
                .map(|e| self.get_num_from_expr(e))
                .collect::<Option<Vec<i64>>>()?
                .into_iter()
                .skip(1)
                .fold(fe, |a, b| a / b)
        } else {
            Default::default()
        }))
    }

    #[inline]
    fn times(&mut self, args: Vec<Expr>) -> Option<Atom> {
        Some(Atom::Num(
            self.reduce(args)?
                .into_iter()
                .map(|e| self.get_num_from_expr(e))
                .collect::<Option<Vec<i64>>>()?
                .into_iter()
                .product(),
        ))
    }

    fn eval(&mut self, expr: Expr) -> Option<Expr> {
        match expr {
            Expr::Constant(_) | Expr::Ident(_) => Some(expr),
            Expr::List(l) => {
                let reduced_head = self.eval(l.first()?.clone())?;
                let tail = l.into_iter().skip(1).collect::<Vec<Expr>>();

                Some(Expr::Constant(match reduced_head {
                    Expr::Constant(Atom::BuiltIn(bi)) => match bi {
                        BuiltIn::Minus => self.minus(tail)?,
                        BuiltIn::Plus => self.plus(tail)?,
                        BuiltIn::Slash => self.slash(tail)?,
                        BuiltIn::Times => self.times(tail)?,
                        BuiltIn::Display => {
                            self.display(tail);
                            return None;
                        }
                        BuiltIn::If => {
                            let cond = &tail[0];
                            let true_branch = &tail[1];
                            let reduced_cond = self.eval(cond.clone());
                            if self.get_bool_from_expr(reduced_cond.unwrap()).unwrap() {
                                return self.eval(true_branch.clone());
                            } else if tail.len() > 2 {
                                return self.eval(tail[2].clone());
                            } else {
                                return None;
                            }
                        }
                        BuiltIn::Eq => {
                            let reduced_tail = self.reduce(tail)?;
                            Atom::Bool(
                                reduced_tail
                                    .iter()
                                    .zip(reduced_tail.iter().skip(1))
                                    .all(|(a, b)| a == b),
                            )
                        }
                        BuiltIn::Define => {
                            assert_eq!(tail.len(), 2);
                            let ident = self.get_ident_string(tail[0].clone()).unwrap();
                            let reduced_body = self.eval(tail[1].clone()).unwrap();
                            self.push_to_current_scope(ident, reduced_body);
                            return None;
                        }
                    },
                    Expr::Ident(_) => todo!(),
                    Expr::List(_) => todo!(),
                    _ => todo!(),
                }))
            }
        }
    }
}

fn repl() {
    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout();
    let mut e = Evaluator::new();
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
            println!("{:?}", e.eval(expr));
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
