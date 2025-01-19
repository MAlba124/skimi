use std::{
    collections::HashMap,
    fs::File,
    io::{Read, Write},
    iter::Peekable,
    path::PathBuf,
    str::Chars,
};

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
    Percent,
    Less,
    Greater,
    String(String),
}

fn is_digit(ch: Option<&char>) -> bool {
    ch.map_or(false, |ch| ch.is_ascii_digit())
}

const fn is_terminal(ch: &char) -> bool {
    matches!(ch, '(' | ')' | '\n' | ' ')
}

struct Lexer<'a> {
    iter: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(s: &'a str) -> Lexer<'a> {
        Self {
            iter: s.chars().peekable(),
        }
    }

    fn take_number(&mut self) -> Option<i64> {
        let mut num_str = String::new();
        while let Some(ch) = self.iter.peek() {
            match ch {
                ' ' | ')' | '\n' => break,
                '0'..='9' => num_str.push(self.iter.next().expect("peek() says it's there")),
                _ => return None,
            }
        }
        assert!(self.next_is_terminal());
        num_str.parse::<i64>().ok()
    }

    fn take_ident(&mut self) -> Option<String> {
        let mut ident = String::new();
        while let Some(ch) = self.iter.peek() {
            if is_terminal(ch) {
                break;
            }
            match ch {
                '-' | 'a'..='z' | 'A'..='Z' => {
                    ident.push(self.iter.next().expect("peek() says it's there"))
                }
                _ => return None,
            }
        }
        assert!(self.next_is_terminal());
        Some(ident)
    }

    /// Expects the iterator to have already popped the first `"`.
    fn take_string(&mut self) -> Option<String> {
        let mut s = String::new();
        loop {
            let mut next = self.iter.next()?;
            match next {
                '"' => break,
                '\\' => {
                    next = self.iter.next()?;
                    if next != '"' {
                        return None;
                    }
                }
                _ => (),
            }
            s.push(next);
        }
        assert!(self.next_is_terminal());
        Some(s)
    }

    fn take_until_newline_or_eof(&mut self) {
        for ch in self.iter.by_ref() {
            if ch == '\n' {
                break;
            }
        }
    }

    fn next_is_terminal(&mut self) -> bool {
        self.iter.peek().map_or(true, is_terminal)
    }

    pub fn lex(&mut self) -> Vec<Tok> {
        let mut toks = Vec::new();

        while let Some(ch) = self.iter.peek() {
            if ch.is_ascii_digit() {
                toks.push(Tok::Num(self.take_number().unwrap()));
                continue;
            } else if ch.is_ascii_alphabetic() {
                toks.push(Tok::Ident(self.take_ident().unwrap()));
                continue;
            }

            let ch = *ch;
            self.iter.next().expect("peek() says it's there");

            toks.push(match ch {
                '\n' | ' ' => continue,
                ';' => {
                    self.take_until_newline_or_eof();
                    continue;
                }
                '(' => Tok::OPar,
                ')' => Tok::CPar,
                '+' => Tok::Plus,
                '/' => Tok::Slash,
                '*' => Tok::Times,
                '=' => Tok::Eq,
                '#' => {
                    let next = self.iter.next().unwrap();
                    assert!(self.next_is_terminal());
                    if next == 'f' {
                        Tok::Bool(false)
                    } else if next == 't' {
                        Tok::Bool(true)
                    } else {
                        panic!("Illegal #{next}");
                    }
                }
                '-' => {
                    if is_digit(self.iter.peek()) {
                        Tok::Num(-self.take_number().unwrap())
                    } else {
                        Tok::Minus
                    }
                }
                '%' => Tok::Percent,
                '<' => Tok::Less,
                '>' => Tok::Greater,
                '"' => Tok::String(self.take_string().unwrap()),
                _ => unreachable!("'{ch}'"),
            });
        }

        toks
    }
}

fn lex(s: &str) -> Vec<Tok> {
    Lexer::new(s).lex()
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BuiltIn {
    Minus,
    Plus,
    Display,
    Newline,
    Slash,
    Times,
    If,
    Eq,
    Define,
    List,
    Modulo,
    Less,
    Greater,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Atom {
    Num(i64),
    BuiltIn(BuiltIn),
    Bool(bool),
    String(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Expr {
    Constant(Atom),
    Ident(String),
    List(Vec<Expr>),
    Lambda(Vec<String>, Box<Expr>),
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

// TODO: error reporting
impl Parser {
    pub fn new(toks: Vec<Tok>) -> Self {
        assert!(!toks.is_empty());
        Self { toks, pos: 0 }
    }

    fn pop_opar(&mut self) {
        assert_eq!(self.toks[self.pos], Tok::OPar);
        self.pos += 1;
    }

    fn pop_cpar(&mut self) {
        assert_eq!(self.toks[self.pos], Tok::CPar);
        self.pos += 1;
    }

    fn func_or_literal(&mut self) -> Expr {
        let s = match &self.toks[self.pos] {
            Tok::Ident(i) => match i.as_str() {
                "display" => Expr::Constant(Atom::BuiltIn(BuiltIn::Display)),
                "newline" => Expr::Constant(Atom::BuiltIn(BuiltIn::Newline)),
                "if" => Expr::Constant(Atom::BuiltIn(BuiltIn::If)),
                "define" => Expr::Constant(Atom::BuiltIn(BuiltIn::Define)),
                _ => Expr::Ident(i.clone()),
            },
            Tok::Minus => Expr::Constant(Atom::BuiltIn(BuiltIn::Minus)),
            Tok::Plus => Expr::Constant(Atom::BuiltIn(BuiltIn::Plus)),
            Tok::Slash => Expr::Constant(Atom::BuiltIn(BuiltIn::Slash)),
            Tok::Times => Expr::Constant(Atom::BuiltIn(BuiltIn::Times)),
            Tok::Eq => Expr::Constant(Atom::BuiltIn(BuiltIn::Eq)),
            Tok::Percent => Expr::Constant(Atom::BuiltIn(BuiltIn::Modulo)),
            Tok::Less => Expr::Constant(Atom::BuiltIn(BuiltIn::Less)),
            Tok::Greater => Expr::Constant(Atom::BuiltIn(BuiltIn::Greater)),
            Tok::Num(n) => Expr::Constant(Atom::Num(*n)),
            Tok::Bool(b) => Expr::Constant(Atom::Bool(*b)),
            Tok::String(s) => Expr::Constant(Atom::String(s.clone())),
            _ => panic!("Expected symbol got: {:?}", &self.toks[self.pos]),
        };
        self.pos += 1;
        s
    }

    fn args(&mut self) -> Vec<Expr> {
        let mut args = Vec::new();
        while self.toks[self.pos] != Tok::CPar {
            args.push(self.arg());
        }
        args
    }

    fn arg(&mut self) -> Expr {
        if self.toks[self.pos] == Tok::OPar {
            self.expr()
        } else {
            self.literal()
        }
    }

    fn literal(&mut self) -> Expr {
        let l = match &self.toks[self.pos] {
            Tok::Ident(i) => Expr::Ident(i.clone()),
            Tok::Num(n) => Expr::Constant(Atom::Num(*n)),
            Tok::Bool(b) => Expr::Constant(Atom::Bool(*b)),
            Tok::String(s) => Expr::Constant(Atom::String(s.clone())),
            _ => panic!("Expected literal got: {:?}", &self.toks[self.pos]),
        };
        self.pos += 1;
        l
    }

    fn expr(&mut self) -> Expr {
        self.pop_opar();
        if self.toks[self.pos] == Tok::CPar {
            self.pos += 1;
            return Expr::List(vec![]);
        }
        let func = self.func_or_literal();
        if self.toks[self.pos] == Tok::CPar {
            self.pos += 1;
            return Expr::List(vec![func]);
        }
        let args = self.args();
        self.pop_cpar();

        if let Expr::Ident(ref i) = func {
            match i.as_str() {
                "list" => {
                    let mut list = vec![Expr::Constant(Atom::BuiltIn(BuiltIn::List))];
                    list.extend_from_slice(&args);
                    return Expr::List(list);
                }
                "lambda" => {
                    // println!("func: {:?} args: {:?}", func, args);
                    let mut lambda_arg_names = Vec::new();
                    let first_arg = args.first().unwrap();
                    let Expr::List(names) = first_arg else {
                        panic!("Expected list of argument names got: {:?}", first_arg);
                    };
                    for name in names {
                        let Expr::Ident(name) = name else {
                            panic!("Expected identifier got: {:?}", name);
                        };
                        lambda_arg_names.push(name.clone());
                    }
                    return Expr::Lambda(
                        lambda_arg_names,
                        Box::new(Expr::List(args.into_iter().skip(1).collect::<Vec<Expr>>())),
                    );
                }
                _ => (),
            }
        }

        let mut list = vec![func];
        list.extend_from_slice(&args);
        Expr::List(list)
    }

    pub fn parse(&mut self) -> Option<Expr> {
        if self.pos >= self.toks.len() {
            return None;
        }
        Some(self.expr())
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
                BuiltIn::Newline => String::from("built_in<Newline>"),
                BuiltIn::If => String::from("non_printable<If>"),
                BuiltIn::Eq => String::from("built_in<Eq>"),
                BuiltIn::Define => String::from("built_in<Define>"),
                BuiltIn::List => String::from("built_in<List>"),
                BuiltIn::Modulo => String::from("built_in<Modulo>"),
                BuiltIn::Less => String::from("built_in<Less>"),
                BuiltIn::Greater => String::from("built_in<Greater>"),
            },
            Atom::Bool(b) => String::from(if b { "#t" } else { "#f" }),
            Atom::String(s) => s,
        },
        Expr::Ident(i) => format!("identifier<{i}>"),
        Expr::List(l) => {
            let len = l.len();
            let mut res = String::new();
            for (i, e) in l.into_iter().enumerate() {
                res += &fmt_expr(e);
                if i < len - 1 {
                    res += " ";
                }
            }
            res
        }
        Expr::Lambda(_, _) => String::from("non_printable<Lambda>"),
    }
}

struct Evaluator {
    variable_stack: Vec<HashMap<String, Expr>>,
}

impl Evaluator {
    pub fn new() -> Self {
        Self {
            variable_stack: vec![HashMap::new()],
        }
    }

    #[inline]
    fn push_to_current_scope(&mut self, ident: String, val: Expr) {
        match self.variable_stack.last_mut() {
            Some(last) => last
                .entry(ident)
                .and_modify(|v| *v = val.clone())
                .or_insert(val),
            None => panic!("Missing scope on the variable stack"),
        };
    }

    #[inline]
    fn push_new_scope(&mut self) {
        self.variable_stack.push(HashMap::new());
    }

    #[inline]
    fn pop_scope(&mut self) {
        let _ = self.variable_stack.pop().unwrap();
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
    }

    #[inline]
    fn minus(&mut self, args: Vec<Expr>) -> Option<Atom> {
        let reduced_args = self.reduce(args)?;
        Some(Atom::Num(
            if let Some(first_elem) = reduced_args.first().cloned() {
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
            },
        ))
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
        Some(Atom::Num(
            if let Some(first_elem) = reduced_args.first().cloned() {
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
            },
        ))
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

    #[inline]
    fn eq(&mut self, args: Vec<Expr>) -> Option<Atom> {
        let reduced_args = self.reduce(args)?;
        Some(Atom::Bool(
            reduced_args
                .iter()
                .zip(reduced_args.iter().skip(1))
                .all(|(a, b)| a == b),
        ))
    }

    #[inline]
    fn if_(&mut self, args: Vec<Expr>) -> Option<Expr> {
        let cond = &args[0];
        let true_branch = &args[1];
        let reduced_cond = self.eval(cond.clone());
        if self.get_bool_from_expr(reduced_cond.unwrap()).unwrap() {
            self.eval(true_branch.clone())
        } else if args.len() > 2 {
            self.eval(args[2].clone())
        } else {
            None
        }
    }

    #[inline]
    fn define(&mut self, args: Vec<Expr>) {
        assert_eq!(args.len(), 2);
        let ident = self.get_ident_string(args[0].clone()).unwrap();
        let reduced_body = self.eval(args[1].clone()).unwrap();
        self.push_to_current_scope(ident, reduced_body);
    }

    #[inline]
    fn reduce_list(&mut self, args: Vec<Expr>) -> Option<Expr> {
        let mut reduced = Vec::new();
        for arg in args.into_iter() {
            reduced.push(self.eval(arg).unwrap());
        }
        Some(Expr::List(reduced))
    }

    #[inline]
    fn modulo(&mut self, args: Vec<Expr>) -> Option<Atom> {
        let reduced_args = self.reduce(args)?;
        Some(Atom::Num(
            if let Some(first_elem) = reduced_args.first().cloned() {
                let fe = self.get_num_from_expr(first_elem)?;
                reduced_args
                    .into_iter()
                    .map(|e| self.get_num_from_expr(e))
                    .collect::<Option<Vec<i64>>>()?
                    .into_iter()
                    .skip(1)
                    .fold(fe, |a, b| a % b)
            } else {
                Default::default()
            },
        ))
    }

    #[inline]
    fn compare_ints(
        &mut self,
        args: Vec<Expr>,
        comparison: impl FnMut((i64, i64)) -> bool,
    ) -> Option<Atom> {
        let reduced_args = self.reduce(args)?;
        Some(Atom::Bool(
            reduced_args
                .iter()
                .map(|e| self.get_num_from_expr(e.clone()))
                .collect::<Option<Vec<i64>>>()?
                .into_iter()
                .zip(
                    reduced_args
                        .iter()
                        .skip(1)
                        .map(|e| self.get_num_from_expr(e.clone()))
                        .collect::<Option<Vec<i64>>>()?,
                )
                .all(comparison),
        ))
    }

    #[inline]
    fn less(&mut self, args: Vec<Expr>) -> Option<Atom> {
        self.compare_ints(args, |(a, b)| a < b)
    }

    #[inline]
    fn greater(&mut self, args: Vec<Expr>) -> Option<Atom> {
        self.compare_ints(args, |(a, b)| a > b)
    }

    fn eval(&mut self, expr: Expr) -> Option<Expr> {
        match expr {
            Expr::Constant(_) | Expr::Lambda(_, _) => Some(expr),
            Expr::Ident(i) => self.get_variable(i),
            Expr::List(l) => {
                let head = l.first()?.clone();
                let tail = l.into_iter().skip(1).collect::<Vec<Expr>>();
                if let Expr::Ident(i) = head.clone() {
                    let func = self.get_variable(i.clone()).unwrap();
                    if let Expr::Lambda(arglist, body) = func {
                        self.push_new_scope();
                        let args = self.reduce(tail).unwrap();
                        assert_eq!(arglist.len(), args.len());
                        for (arg_key, arg_val) in arglist.into_iter().zip(args.into_iter()) {
                            self.push_to_current_scope(arg_key, arg_val);
                        }
                        let mut res = None;
                        if let Expr::List(body) = *body {
                            for expr in body {
                                res = self.eval(expr);
                            }
                        } else {
                            panic!("TODO");
                        }
                        self.pop_scope();
                        return res;
                    }
                }
                let reduced_head = self.eval(head)?;
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
                        BuiltIn::If => return self.if_(tail),
                        BuiltIn::Eq => self.eq(tail)?,
                        BuiltIn::Define => {
                            self.define(tail);
                            return None;
                        }
                        BuiltIn::List => {
                            assert_eq!(tail.len(), 1);
                            match &tail[0] {
                                Expr::List(l) => return self.reduce_list(l.clone()),
                                _ => panic!("Expected to get a list but got {:?}", tail[0]),
                            }
                        }
                        BuiltIn::Newline => {
                            assert!(tail.is_empty());
                            println!();
                            return None;
                        }
                        BuiltIn::Modulo => self.modulo(tail)?,
                        BuiltIn::Less => self.less(tail)?,
                        BuiltIn::Greater => self.greater(tail)?,
                    },
                    Expr::List(l) => return self.reduce_list(l),
                    Expr::Constant(_) | Expr::Lambda(_, _) => return Some(reduced_head),
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
        if toks.is_empty() {
            continue;
        }
        // println!("{:?}", toks);
        let mut parser = Parser::new(toks);
        while let Some(expr) = parser.parse() {
            println!("{expr:?}");
            println!("{:?}", e.eval(expr));
        }
    }
}

fn evaluate_file(file: &mut File) {
    let mut code = String::new();
    file.read_to_string(&mut code).unwrap();
    let toks = Lexer::new(&code).lex();
    let mut parser = Parser::new(toks);
    let mut evaluator = Evaluator::new();
    while let Some(expr) = parser.parse() {
        // println!("## {expr:?} ##");
        let _ = evaluator.eval(expr);
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

#[cfg(test)]
mod tests {
    use crate::{is_digit, lex, Lexer, Tok};

    #[test]
    fn test_is_digit() {
        assert!(is_digit(Some(&'7')));
        assert!(!is_digit(Some(&'a')));
    }

    #[test]
    fn test_take_ident() {
        let mut lexer = Lexer::new("this-is-an-identifier");
        assert_eq!(
            lexer.take_ident(),
            Some(String::from("this-is-an-identifier"))
        );
    }

    macro_rules! lexer_take_number {
        ($s:expr, $ex:expr) => {
            let mut lexer = Lexer::new($s);
            assert_eq!(lexer.take_number(), $ex);
        };
    }

    #[test]
    fn test_take_num() {
        lexer_take_number!("1234", Some(1234));
        lexer_take_number!("12e4", None);
        lexer_take_number!("1241234234", Some(1241234234));
    }

    macro_rules! create_take_string_test {
        ($in:expr, $ex:expr) => {
            let mut lexer = Lexer::new($in);
            assert_eq!(lexer.take_string(), Some(String::from($ex)));
        };
    }

    macro_rules! create_take_string_test_none {
        ($in:expr) => {
            let mut lexer = Lexer::new($in);
            assert_eq!(lexer.take_string(), None,);
        };
    }

    #[test]
    fn test_take_string() {
        create_take_string_test!("this is a simple string\"", "this is a simple string");
        create_take_string_test!(
            "this has \\\"escaped quotes\\\"\"",
            "this has \"escaped quotes\""
        );
        create_take_string_test_none!("this is an invalid string\\9\"");
    }

    macro_rules! ident {
        ($i:expr) => {
            Tok::Ident(String::from($i))
        };
    }

    macro_rules! num {
        ($n:expr) => {
            Tok::Num($n)
        };
    }

    macro_rules! opar {
        () => {
            Tok::OPar
        };
    }

    macro_rules! cpar {
        () => {
            Tok::CPar
        };
    }

    #[test]
    fn test_lex() {
        assert_eq!(
            lex("(1 2 3)"),
            vec![opar!(), num!(1), num!(2), num!(3), cpar!(),]
        );
        assert_eq!(
            lex("(+ 1 2)"),
            vec![opar!(), Tok::Plus, num!(1), num!(2), cpar!(),]
        );
        assert_eq!(
            lex("(+ 1 2 3)"),
            vec![opar!(), Tok::Plus, num!(1), num!(2), num!(3), cpar!(),]
        );
        assert_eq!(
            lex("(- 1 2)"),
            vec![opar!(), Tok::Minus, num!(1), num!(2), cpar!(),]
        );
        assert_eq!(
            lex("(- 1 2 3)"),
            vec![opar!(), Tok::Minus, num!(1), num!(2), num!(3), cpar!(),]
        );
        assert_eq!(
            lex("(- 1 2 -3)"),
            vec![opar!(), Tok::Minus, num!(1), num!(2), num!(-3), cpar!(),]
        );
        assert_eq!(lex("#t #f"), vec![Tok::Bool(true), Tok::Bool(false)]);
        assert_eq!(lex("-427"), vec![num!(-427)]);
        assert_eq!(
            lex("(+ 1 an-identifier)"),
            vec![
                opar!(),
                Tok::Plus,
                num!(1),
                ident!("an-identifier"),
                cpar!(),
            ]
        );
        assert_eq!(
            lex("(if (< 1 2) (display 1) (display 0))"),
            vec![
                opar!(),
                ident!("if"),
                opar!(),
                Tok::Less,
                num!(1),
                num!(2),
                cpar!(),
                opar!(),
                ident!("display"),
                num!(1),
                cpar!(),
                opar!(),
                ident!("display"),
                num!(0),
                cpar!(),
                cpar!(),
            ]
        );
    }
}
