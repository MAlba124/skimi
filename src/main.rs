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
    LessOrEq,
    GreaterOrEq,
    Char(char),
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
                '-' | 'a'..='z' | 'A'..='Z' | '!' => {
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
                    if next == 'f' {
                        assert!(self.next_is_terminal());
                        Tok::Bool(false)
                    } else if next == 't' {
                        assert!(self.next_is_terminal());
                        Tok::Bool(true)
                    } else if next == '\\' {
                        let next = self.iter.next().unwrap();
                        assert!(self.next_is_terminal());
                        Tok::Char(next)
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
                '<' => {
                    if self.iter.peek() == Some(&'=') {
                        let _ = self.iter.next().expect("peek() says it's there");
                        Tok::LessOrEq
                    } else {
                        Tok::Less
                    }
                }
                '>' => {
                    if self.iter.peek() == Some(&'=') {
                        let _ = self.iter.next().expect("peek() says it's there");
                        Tok::GreaterOrEq
                    } else {
                        Tok::Greater
                    }
                }
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
    Set,
    LessOrEq,
    GreaterOrEq,
    Cond,
    Cons,
}

macro_rules! bi {
    ($b:ident) => {
        Expr::Atom(Atom::BuiltIn(BuiltIn::$b))
    };
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Atom {
    Num(i64),
    BuiltIn(BuiltIn),
    Bool(bool),
    String(String),
    Char(char),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DoVariable {
    pub ident: String,
    pub init: Expr,
    pub step: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Expr {
    Atom(Atom),
    Ident(String),
    Quoted(Box<Expr>),
    List(Vec<Expr>),
    Cons(Box<Expr>, Box<Expr>),
    Lambda(Vec<String>, Box<Expr>),
    Do(Vec<DoVariable>, Box<Expr>, Vec<Expr>, Vec<Expr>),
    Null,
}

macro_rules! list {
    ($(),+) => {
        Expr::Cons(Box::new(Expr::Null), Box::new(Expr::Null))
        // Expr::List(vec![])
    };
    ($($exprs:expr),+) => {
        // TODO: use idiomatic macro bullshit
        {
            let elems = vec![$($exprs),+];
            let mut l = Expr::Cons(Box::new(elems.last().unwrap().clone()), Box::new(Expr::Null));
            for e in elems.iter().rev().skip(1) {
                l = Expr::Cons(Box::new(e.clone()), Box::new(l));
            }
            l
        }
    };
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
                "display" => bi!(Display),
                "newline" => bi!(Newline),
                "if" => bi!(If),
                "define" => bi!(Define),
                "set!" => bi!(Set),
                "cond" => bi!(Cond),
                "null" => Expr::Null,
                "cons" => bi!(Cons),
                _ => Expr::Ident(i.clone()),
            },
            Tok::Minus => bi!(Minus),
            Tok::Plus => bi!(Plus),
            Tok::Slash => bi!(Slash),
            Tok::Times => bi!(Times),
            Tok::Eq => bi!(Eq),
            Tok::Percent => bi!(Modulo),
            Tok::Less => bi!(Less),
            Tok::Greater => bi!(Greater),
            Tok::LessOrEq => bi!(LessOrEq),
            Tok::GreaterOrEq => bi!(GreaterOrEq),
            Tok::Num(n) => Expr::Atom(Atom::Num(*n)),
            Tok::Bool(b) => Expr::Atom(Atom::Bool(*b)),
            Tok::String(s) => Expr::Atom(Atom::String(s.clone())),
            Tok::Char(c) => Expr::Atom(Atom::Char(*c)),
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
            self.func_or_literal()
        }
    }

    // TODO: make this crap cleaner
    fn expr(&mut self) -> Expr {
        self.pop_opar();
        if self.toks[self.pos] == Tok::CPar {
            self.pos += 1;
            return list![];
        }
        let func = self.arg();
        if self.toks[self.pos] == Tok::CPar {
            self.pos += 1;
            return list![func];
        }
        let args = self.args();
        self.pop_cpar();

        if let Expr::Ident(ref i) = func {
            match i.as_str() {
                "list" => {
                    let mut head = Expr::Cons(Box::new(Expr::Null), Box::new(Expr::Null));
                    for car in args.into_iter().rev() {
                        head = Expr::Cons(Box::new(car), Box::new(head));
                    }
                    return head;
                }
                "lambda" => {
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
                "do" => {
                    let variable_list = match &args[0] {
                        Expr::List(l) => {
                            let mut vars = Vec::new();
                            for var in l {
                                match var {
                                    Expr::List(var) => {
                                        assert_eq!(var.len(), 3);
                                        let Expr::Ident(ident) = var[0].clone() else {
                                            panic!("Expected an identifier got: {:?}", var[0]);
                                        };
                                        let init = var[1].clone();
                                        let step = var[2].clone();
                                        vars.push(DoVariable { ident, init, step });
                                    }
                                    _ => panic!("Expected a list got: {:?}", args[0]),
                                }
                            }
                            vars
                        }
                        _ => panic!("Expected a list got: {:?}", args[0]),
                    };
                    let (test, after_test_exprs) = match &args[1] {
                        Expr::List(l) => {
                            if l.len() > 1 {
                                (l[0].clone(), l[1..].to_vec())
                            } else {
                                (l[0].clone(), Vec::new())
                            }
                        }
                        _ => panic!("Expected a list got: {:?}", args[1]),
                    };
                    let commands = args[2..].to_vec();
                    return Expr::Do(variable_list, Box::new(test), after_test_exprs, commands);
                }
                _ => (),
            }
        }

        let mut list = Expr::Cons(
            Box::new(args.last().unwrap().clone()),
            Box::new(Expr::Null),
        );
        // println!("args={args:?}");
        for e in args.into_iter().rev().skip(1) {
            // println!("e={e:?}");
            list = Expr::Cons(Box::new(e), Box::new(list));
        }
        list = Expr::Cons(Box::new(func), Box::new(list));
        // println!("list={list:?}");
        // let mut list = vec![func];
        // list.extend_from_slice(&args);
        // list
        list
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
        Expr::Atom(c) => match c {
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
                BuiltIn::Set => String::from("built_in<Set>"),
                BuiltIn::LessOrEq => String::from("built_in<LessOrEq>"),
                BuiltIn::GreaterOrEq => String::from("built_in<GreaterOrEq>"),
                BuiltIn::Cond => String::from("built_in<Cond>"),
                BuiltIn::Cons => String::from("built_in<Cons>"),
            },
            Atom::Bool(b) => String::from(if b { "#t" } else { "#f" }),
            Atom::String(s) => s,
            Atom::Char(c) => c.to_string(),
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
        Expr::Do(_, _, _, _) => String::from("non_printable<Do>"),
        Expr::Quoted(_) => todo!(),
        Expr::Cons(_, _) => format!("{e:?}"),
        Expr::Null => String::from("null"),
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
    fn get_variable(&self, ident: &str) -> Option<Expr> {
        for scope in self.variable_stack.iter().rev() {
            if scope.contains_key(ident) {
                return scope.get(ident).cloned();
            }
        }
        None
    }

    #[inline]
    fn has_variable_in_scope(&self, ident: &str) -> bool {
        self.get_variable(ident).is_some()
    }

    #[inline]
    fn get_num_from_expr(&self, e: Expr) -> Option<i64> {
        match e {
            Expr::Atom(Atom::Num(n)) => Some(n),
            Expr::Ident(i) => self.get_num_from_expr(self.get_variable(&i)?),
            _ => None,
        }
    }

    #[inline]
    fn get_bool_from_expr(&self, e: Expr) -> Option<bool> {
        match e {
            Expr::Atom(Atom::Bool(b)) => Some(b),
            Expr::Ident(i) => self.get_bool_from_expr(self.get_variable(&i)?),
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
            reduced.push(self.eval(e));
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
    fn minus(&mut self, args: Vec<Expr>) -> Atom {
        let reduced_args = self.reduce(args).unwrap();
        Atom::Num(if let Some(first_elem) = reduced_args.first().cloned() {
            let fe = self.get_num_from_expr(first_elem).unwrap();
            reduced_args
                .into_iter()
                .map(|e| self.get_num_from_expr(e))
                .collect::<Option<Vec<i64>>>()
                .unwrap()
                .into_iter()
                .skip(1)
                .fold(fe, |a, b| a - b)
        } else {
            Default::default()
        })
    }

    #[inline]
    fn plus(&mut self, args: Vec<Expr>) -> Atom {
        Atom::Num(
            self.reduce(args)
                .unwrap()
                .into_iter()
                .map(|e| self.get_num_from_expr(e))
                .collect::<Option<Vec<i64>>>()
                .unwrap()
                .into_iter()
                .sum(),
        )
    }

    #[inline]
    fn slash(&mut self, args: Vec<Expr>) -> Atom {
        let reduced_args = self.reduce(args).unwrap();
        Atom::Num(if let Some(first_elem) = reduced_args.first().cloned() {
            let fe = self.get_num_from_expr(first_elem).unwrap();
            reduced_args
                .into_iter()
                .map(|e| self.get_num_from_expr(e))
                .collect::<Option<Vec<i64>>>()
                .unwrap()
                .into_iter()
                .skip(1)
                .fold(fe, |a, b| a / b)
        } else {
            Default::default()
        })
    }

    #[inline]
    fn times(&mut self, args: Vec<Expr>) -> Atom {
        Atom::Num(
            self.reduce(args)
                .unwrap()
                .into_iter()
                .map(|e| self.get_num_from_expr(e))
                .collect::<Option<Vec<i64>>>()
                .unwrap()
                .into_iter()
                .product(),
        )
    }

    #[inline]
    fn eq(&mut self, args: Vec<Expr>) -> Atom {
        let reduced_args = self.reduce(args).unwrap();
        Atom::Bool(
            reduced_args
                .iter()
                .zip(reduced_args.iter().skip(1))
                .all(|(a, b)| a == b),
        )
    }

    #[inline]
    fn if_(&mut self, args: Vec<Expr>) -> Expr {
        let cond = &args[0];
        let true_branch = &args[1];
        let reduced_cond = self.eval(cond.clone());
        if self.get_bool_from_expr(reduced_cond).unwrap() {
            self.eval(true_branch.clone())
        } else if args.len() > 2 {
            self.eval(args[2].clone())
        } else {
            Expr::Null
        }
    }

    #[inline]
    fn define(&mut self, args: Vec<Expr>) {
        assert!(
            args.len() == 2,
            "`define` takes 2 arguments got: {}",
            args.len()
        );
        let ident = self.get_ident_string(args[0].clone()).unwrap();
        let reduced_body = self.eval(args[1].clone());
        self.push_to_current_scope(ident, reduced_body);
    }

    #[inline]
    fn set(&mut self, args: Vec<Expr>) {
        assert!(
            args.len() == 2,
            "`set!` takes 2 arguments got: {}",
            args.len()
        );
        let ident = self.get_ident_string(args[0].clone()).unwrap();
        let reduced_body = self.eval(args[1].clone());
        assert!(
            self.has_variable_in_scope(&ident),
            "Attempted to update a variable that is not in scope: {ident}"
        );
        self.push_to_current_scope(ident, reduced_body);
    }

    #[inline]
    fn reduce_list(&mut self, args: Vec<Expr>) -> Expr {
        let mut reduced = Vec::new();
        for arg in args.into_iter() {
            reduced.push(self.eval(arg));
        }
        Expr::List(reduced)
    }

    #[inline]
    fn modulo(&mut self, args: Vec<Expr>) -> Atom {
        let reduced_args = self.reduce(args).unwrap();
        Atom::Num(if let Some(first_elem) = reduced_args.first().cloned() {
            let fe = self.get_num_from_expr(first_elem).unwrap();
            reduced_args
                .into_iter()
                .map(|e| self.get_num_from_expr(e))
                .collect::<Option<Vec<i64>>>()
                .unwrap()
                .into_iter()
                .skip(1)
                .fold(fe, |a, b| a % b)
        } else {
            Default::default()
        })
    }

    #[inline]
    fn compare_ints(
        &mut self,
        args: Vec<Expr>,
        comparison: impl FnMut((i64, i64)) -> bool,
    ) -> Atom {
        let reduced_args = self.reduce(args).unwrap();
        Atom::Bool(
            reduced_args
                .iter()
                .map(|e| self.get_num_from_expr(e.clone()))
                .collect::<Option<Vec<i64>>>()
                .unwrap()
                .into_iter()
                .zip(
                    reduced_args
                        .iter()
                        .skip(1)
                        .map(|e| self.get_num_from_expr(e.clone()))
                        .collect::<Option<Vec<i64>>>()
                        .unwrap(),
                )
                .all(comparison),
        )
    }

    #[inline]
    fn less(&mut self, args: Vec<Expr>) -> Atom {
        self.compare_ints(args, |(a, b)| a < b)
    }

    #[inline]
    fn greater(&mut self, args: Vec<Expr>) -> Atom {
        self.compare_ints(args, |(a, b)| a > b)
    }

    #[inline]
    fn less_or_eq(&mut self, args: Vec<Expr>) -> Atom {
        self.compare_ints(args, |(a, b)| a <= b)
    }

    #[inline]
    fn greater_or_eq(&mut self, args: Vec<Expr>) -> Atom {
        self.compare_ints(args, |(a, b)| a >= b)
    }

    #[inline]
    fn cond(&mut self, args: Vec<Expr>) -> Expr {
        for arg in args {
            match arg {
                Expr::List(l) => {
                    assert!(!l.is_empty());
                    let test = self.eval(l[0].clone());
                    if self.get_bool_from_expr(test).unwrap() {
                        let mut res = Expr::Null;
                        for action in l[1..].iter() {
                            res = self.eval(action.clone());
                        }
                        return res;
                    }
                }
                _ => panic!("`cond` expects a list got: {arg:?}"),
            }
        }
        Expr::Null
    }

    #[inline]
    fn cons_to_vec(&self, cons: Expr) -> Vec<Expr> {
        println!("cons={cons:?}");
        let mut v = Vec::new();
        let mut car = cons;
        loop {
            match car {
                Expr::Atom(_)
                | Expr::Ident(_)
                | Expr::Quoted(_)
                | Expr::Lambda(_, _)
                | Expr::Do(_, _, _, _) => {
                    v.push(car);
                    break;
                }
                Expr::List(_) => todo!(),
                Expr::Cons(c, cdr) => {
                    v.push(*c);
                    car = *cdr;
                }
                Expr::Null => break,
            }
        }
        println!("v={v:?}");
        v
    }

    fn eval(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Atom(_) | Expr::Lambda(_, _) => expr,
            Expr::Ident(i) => match self.get_variable(&i) {
                Some(e) => e,
                None => panic!("Variable `{i}` does not exist"),
            },
            Expr::List(l) => {
                let head = l.first().unwrap().clone();
                let tail = l.into_iter().skip(1).collect::<Vec<Expr>>();
                if let Expr::Ident(i) = head.clone() {
                    let Some(func) = self.get_variable(&i) else {
                        panic!("Variable `{i}` does not exist");
                    };
                    if let Expr::Lambda(arglist, body) = func {
                        self.push_new_scope();
                        let args = self.reduce(tail).unwrap();
                        assert!(
                            arglist.len() == args.len(),
                            "lambda `{i}` takes {} arguments got {}",
                            arglist.len(),
                            args.len()
                        );
                        for (arg_key, arg_val) in arglist.into_iter().zip(args.into_iter()) {
                            self.push_to_current_scope(arg_key, arg_val);
                        }
                        let mut res = Expr::Null;
                        if let Expr::List(body) = *body {
                            for expr in body {
                                res = self.eval(expr);
                            }
                        } else {
                            panic!("Body of lambda `{i}` is not a list");
                        }
                        self.pop_scope();
                        return res;
                    }
                }
                let reduced_head = self.eval(head);
                Expr::Atom(match reduced_head {
                    Expr::Atom(Atom::BuiltIn(bi)) => match bi {
                        BuiltIn::Minus => self.minus(tail),
                        BuiltIn::Plus => self.plus(tail),
                        BuiltIn::Slash => self.slash(tail),
                        BuiltIn::Times => self.times(tail),
                        BuiltIn::Display => {
                            self.display(tail);
                            return Expr::Null;
                        }
                        BuiltIn::If => return self.if_(tail),
                        BuiltIn::Eq => self.eq(tail),
                        BuiltIn::Define => {
                            self.define(tail);
                            return Expr::Null;
                        }
                        BuiltIn::Set => {
                            self.set(tail);
                            return Expr::Null;
                        }
                        BuiltIn::List => return Expr::List(self.reduce(tail).unwrap()),
                        BuiltIn::Newline => {
                            assert!(
                                tail.is_empty(),
                                "`newline` takes 0 arguments got: {}",
                                tail.len()
                            );
                            println!();
                            return Expr::Null;
                        }
                        BuiltIn::Modulo => self.modulo(tail),
                        BuiltIn::Less => self.less(tail),
                        BuiltIn::Greater => self.greater(tail),
                        BuiltIn::LessOrEq => self.less_or_eq(tail),
                        BuiltIn::GreaterOrEq => self.greater_or_eq(tail),
                        BuiltIn::Cond => return self.cond(tail),
                        BuiltIn::Cons => todo!(),
                    },
                    Expr::List(l) => return self.reduce_list(l),
                    Expr::Atom(_) | Expr::Lambda(_, _) => return reduced_head,
                    _ => todo!(),
                })
            }
            Expr::Do(vars, test, after_test_exprs, commands) => {
                self.push_new_scope();
                for var in &vars {
                    self.push_to_current_scope(var.ident.clone(), var.init.clone());
                }
                let mut res = Expr::Null;
                loop {
                    let test_res = self.eval(*test.clone());
                    if self.get_bool_from_expr(test_res).unwrap() {
                        for after_test_expr in after_test_exprs {
                            res = self.eval(after_test_expr);
                        }
                        break;
                    }

                    for command in commands.clone() {
                        self.eval(command);
                    }

                    for var in &vars {
                        let new_val = self.eval(var.step.clone());
                        self.push_to_current_scope(var.ident.clone(), new_val);
                    }
                }
                self.pop_scope();
                res
            }
            Expr::Quoted(_) => todo!(),
            Expr::Cons(car, cdr) => match self.eval(*car.clone()) {
                Expr::Atom(Atom::BuiltIn(bi)) => match bi {
                    BuiltIn::Minus => return Expr::Atom(self.minus(self.cons_to_vec(*cdr))),
                    BuiltIn::Plus => return Expr::Atom(self.plus(self.cons_to_vec(*cdr))),
                    BuiltIn::Display => {
                        self.display(self.cons_to_vec(*cdr));
                        return Expr::Null;
                    }
                    BuiltIn::Newline => {
                        println!();
                        return Expr::Null;
                    }
                    BuiltIn::Slash => return Expr::Atom(self.slash(self.cons_to_vec(*cdr))),
                    BuiltIn::Times => return Expr::Atom(self.times(self.cons_to_vec(*cdr))),
                    BuiltIn::If => return self.if_(self.cons_to_vec(*cdr)),
                    BuiltIn::Eq => return Expr::Atom(self.eq(self.cons_to_vec(*cdr))),
                    BuiltIn::Define => todo!(),
                    BuiltIn::List => todo!(),
                    BuiltIn::Modulo => return Expr::Atom(self.modulo(self.cons_to_vec(*cdr))),
                    BuiltIn::Less => return Expr::Atom(self.less(self.cons_to_vec(*cdr))),
                    BuiltIn::Greater => return Expr::Atom(self.greater(self.cons_to_vec(*cdr))),
                    BuiltIn::Set => todo!(),
                    BuiltIn::LessOrEq => return Expr::Atom(self.less_or_eq(self.cons_to_vec(*cdr))),
                    BuiltIn::GreaterOrEq => return Expr::Atom(self.greater_or_eq(self.cons_to_vec(*cdr))),
                    BuiltIn::Cond => todo!(),
                    BuiltIn::Cons => match *cdr {
                        Expr::Cons(_, _) => return *cdr,
                        _ => panic!("Expected a cons cell, got: {cdr:?}"),
                    },
                },
                Expr::Ident(_) => todo!(),
                Expr::Quoted(_) => todo!(),
                Expr::List(_) => todo!(),
                Expr::Cons(_, _) => todo!(),
                Expr::Lambda(_, _) => todo!(),
                Expr::Do(_, _, _, _) => todo!(),
                _ => panic!("Expected a function, got: {:?}", *car),
            },
            Expr::Null => Expr::Null,
        }
    }
}

fn repl() {
    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout();
    let mut e = Evaluator::new();
    loop {
        let mut buffer = String::new();
        print!("skimi > ");
        stdout.flush().unwrap();
        stdin.read_line(&mut buffer).unwrap();
        let toks = lex(&buffer);
        if toks.is_empty() {
            continue;
        }
        // println!("{:?}", toks);
        let mut parser = Parser::new(toks);
        while let Some(expr) = parser.parse() {
            // println!("{expr:?}");
            let res = e.eval(expr);
            if res != Expr::Null {
                println!("{}", fmt_expr(res));
            }
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
    use crate::{is_digit, lex, Atom, BuiltIn, DoVariable, Evaluator, Expr, Lexer, Parser, Tok};

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
        assert_eq!(lex("identifier-with!"), vec![ident!("identifier-with!")]);
        assert_eq!(lex("set!"), vec![ident!("set!")]);
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
        assert_eq!(lex("<="), vec![Tok::LessOrEq]);
        assert_eq!(lex(">="), vec![Tok::GreaterOrEq]);
        assert_eq!(lex("< <="), vec![Tok::Less, Tok::LessOrEq]);
        assert_eq!(lex("> >="), vec![Tok::Greater, Tok::GreaterOrEq]);
        assert_eq!(lex("<=  1 2"), vec![Tok::LessOrEq, num!(1), num!(2)]);
        assert_eq!(lex(">=  1 2"), vec![Tok::GreaterOrEq, num!(1), num!(2)]);
        assert_eq!(lex("#\\a"), vec![Tok::Char('a')]);
        assert_eq!(lex("#\\a #t"), vec![Tok::Char('a'), Tok::Bool(true)]);
        assert_eq!(lex("#f #\\a"), vec![Tok::Bool(false), Tok::Char('a')]);
    }

    macro_rules! lex_and_parse_eq {
        ($in:expr, $ex:expr) => {
            let mut parser = Parser::new(lex($in));
            assert_eq!(parser.parse(), Some($ex));
            assert_eq!(parser.parse(), None);
        };
    }

    macro_rules! exnum {
        ($n:expr) => {
            Expr::Atom(Atom::Num($n))
        };
    }

    macro_rules! exstr {
        ($s:expr) => {
            Expr::Atom(Atom::String(String::from($s)))
        };
    }

    macro_rules! exbool {
        ($b:expr) => {
            Expr::Atom(Atom::Bool($b))
        };
    }

    macro_rules! exident {
        ($i:expr) => {
            Expr::Ident(String::from($i))
        };
    }

    #[test]
    fn test_parser_addition() {
        lex_and_parse_eq!("(+ 1 2)", list![bi!(Plus), exnum!(1), exnum!(2)]);
    }

    #[test]
    fn test_parser_nested_lists() {
        lex_and_parse_eq!(
            "((1 2) (3 4))",
            list![list![exnum!(1), exnum!(2)], list![exnum!(3), exnum!(4)]]
        );
        lex_and_parse_eq!(
            "((1 (2 3 (4 (5)))))",
            list![list![
                exnum!(1),
                list![exnum!(2), exnum!(3), list![exnum!(4), list![exnum!(5)]]]
            ]]
        );
        lex_and_parse_eq!(
            "(display (1 (2 3 (4 (5)))))",
            list![
                bi!(Display),
                list![
                    exnum!(1),
                    list![exnum!(2), exnum!(3), list![exnum!(4), list![exnum!(5)]]]
                ]
            ]
        );
    }

    #[test]
    fn test_parser_if() {
        lex_and_parse_eq!(
            "(if (< 1 10) (display \"1 is less than 10\"))",
            list![
                bi!(If),
                list![bi!(Less), exnum!(1), exnum!(10)],
                list![bi!(Display), exstr!("1 is less than 10")]
            ]
        );
        lex_and_parse_eq!(
            "(if (< 1 10) (display \"1 is less than 10\") (display \"1 is not less than 10\"))",
            list![
                bi!(If),
                list![bi!(Less), exnum!(1), exnum!(10)],
                list![bi!(Display), exstr!("1 is less than 10")],
                list![bi!(Display), exstr!("1 is not less than 10")]
            ]
        );
    }

    #[test]
    fn test_parser_do() {
        lex_and_parse_eq!(
            "(do ((x 0 (+ x 1))) ((>= x 10) (display \"Loop finished\") (newline)) (display x) (newline))",
            Expr::Do(
                vec![
                    DoVariable { ident: String::from("x"), init: exnum!(0), step: list![bi!(Plus), exident!("x"), exnum!(1)] }
                ],
                Box::new(
                    list![bi!(GreaterOrEq), exident!("x"), exnum!(10)]
                ),
                vec![list![bi!(Display), exstr!("Loop finished")], list!(bi!(Newline))],
                vec![list![bi!(Display), exident!("x")], list![bi!(Newline)]]
            )
        );
    }

    #[test]
    fn test_parse_cond() {
        lex_and_parse_eq!(
            "(cond ((< 1 2) #t) (#t #f))",
            list![
                bi!(Cond),
                list![list![bi!(Less), exnum!(1), exnum!(2)], exbool!(true)],
                list![exbool!(true), exbool!(false)]
            ]
        );
    }

    macro_rules! eval_eq_some {
        ($c:expr, $ex:expr) => {
            let mut parser = Parser::new(lex($c));
            let mut evaluator = Evaluator::new();
            assert_eq!(evaluator.eval(parser.parse().unwrap()), $ex);
            assert_eq!(parser.parse(), None);
        };
    }

    macro_rules! eval_eq_some_many {
        ($c:expr, $ex:expr) => {
            let mut parser = Parser::new(lex($c));
            let mut evaluator = Evaluator::new();
            for ex in $ex {
                assert_eq!(evaluator.eval(parser.parse().unwrap()), Some(ex));
            }
            assert_eq!(parser.parse(), None);
        };
    }

    #[test]
    fn test_eval_arith() {
        // The following tests are generated by an LLM
        eval_eq_some!("(+ 1 2)", exnum!(1 + 2));
        eval_eq_some!("(- 10 2)", exnum!(10 - 2));
        eval_eq_some!("(* 3 2)", exnum!(3 * 2));
        eval_eq_some!("(/ 10 2)", exnum!(10 / 2));
        eval_eq_some!("(+ 1 (* 2 3))", exnum!(1 + (2 * 3)));
        eval_eq_some!("(- 10 (/ 6 2))", exnum!(10 - (6 / 2)));
        eval_eq_some!("(* (+ 2 3) 4)", exnum!((2 + 3) * 4));
        eval_eq_some!("(/ (* 12 3) 4)", exnum!((12 * 3) / 4));
        eval_eq_some!("(+ (* 2 3) (- 5 1))", exnum!((2 * 3) + (5 - 1)));
        eval_eq_some!("(- (* 10 2) (/ 8 2))", exnum!((10 * 2) - (8 / 2)));
        eval_eq_some!("(/ 100 5 2)", exnum!(100 / 5 / 2));
        eval_eq_some!("(- 20 5 3)", exnum!(20 - 5 - 3));
        eval_eq_some!("(+ (* 2 3) (* 4 5))", exnum!((2 * 3) + (4 * 5)));
        eval_eq_some!("(+ 7 8)", exnum!(7 + 8));
        eval_eq_some!("(- 15 5)", exnum!(15 - 5));
        eval_eq_some!("(* 3 9)", exnum!(3 * 9));
        eval_eq_some!("(/ 36 6)", exnum!(36 / 6));
        eval_eq_some!("(+ 10 (* 2 5))", exnum!(10 + (2 * 5)));
        eval_eq_some!("(- 50 (/ 20 4))", exnum!(50 - (20 / 4)));
        eval_eq_some!("(* (+ 1 2) 3)", exnum!((1 + 2) * 3));
        eval_eq_some!("(/ (* 24 2) 8)", exnum!((24 * 2) / 8));
        eval_eq_some!("(+ (* 3 4) (- 10 2))", exnum!((3 * 4) + (10 - 2)));
        eval_eq_some!("(- (* 5 4) (/ 16 4))", exnum!((5 * 4) - (16 / 4)));
        eval_eq_some!("(+ 1 2 3 4 5)", exnum!(1 + 2 + 3 + 4 + 5));
        eval_eq_some!("(* 2 3 5)", exnum!(2 * 3 * 5));
        eval_eq_some!("(/ 120 4 3)", exnum!(120 / 4 / 3));
        eval_eq_some!("(- 30 10 5)", exnum!(30 - 10 - 5));
        eval_eq_some!("(+ (* 2 3) (* 5 6))", exnum!((2 * 3) + (5 * 6)));
        eval_eq_some!("(+ 1 (* 2 (+ 3 4)))", exnum!(1 + (2 * (3 + 4))));
        eval_eq_some!("(- (* 10 2) (+ 5 5))", exnum!((10 * 2) - (5 + 5)));
        eval_eq_some!("(* (+ 1 1) (+ 2 2))", exnum!((1 + 1) * (2 + 2)));
        eval_eq_some!("(/ (+ 100 50) 5)", exnum!((100 + 50) / 5));
        eval_eq_some!("(+ 2 (* 3 4) (- 10 5))", exnum!(2 + (3 * 4) + (10 - 5)));
        eval_eq_some!("(- (* 6 7) (/ 42 7))", exnum!((6 * 7) - (42 / 7)));
        eval_eq_some!(
            "(+ (* 2 2) (* 3 3) (* 4 4))",
            exnum!((2 * 2) + (3 * 3) + (4 * 4))
        );
        eval_eq_some!("(/ (* 5 5) (+ 5 5))", exnum!((5 * 5) / (5 + 5)));
        eval_eq_some!("(* 1 2 3 4 5)", exnum!(1 * 2 * 3 * 4 * 5));
        eval_eq_some!("(/ 1000 10 10)", exnum!(1000 / 10 / 10));
        eval_eq_some!("(- 100 20 30 10)", exnum!(100 - 20 - 30 - 10));
        eval_eq_some!(
            "(+ (* 2 3) (* 3 4) (* 4 5))",
            exnum!((2 * 3) + (3 * 4) + (4 * 5))
        );
        eval_eq_some!(
            "(+ 1 (* 2 (+ 3 4)) (- 10 5))",
            exnum!(1 + (2 * (3 + 4)) + (10 - 5))
        );
        eval_eq_some!("(- (* 8 2) (/ 16 4))", exnum!((8 * 2) - (16 / 4)));
        eval_eq_some!(
            "(+ (* 3 3) (* 2 2) (* 1 1))",
            exnum!((3 * 3) + (2 * 2) + (1 * 1))
        );
        eval_eq_some!("(/ (+ 100 200) 10)", exnum!((100 + 200) / 10));
        eval_eq_some!("(+ 5 (* 2 3))", exnum!(5 + (2 * 3)));
        eval_eq_some!("(- 50 (* 5 2))", exnum!(50 - (5 * 2)));
        eval_eq_some!("(* 7 (+ 1 2))", exnum!(7 * (1 + 2)));
        eval_eq_some!("(/ (* 30 2) 15)", exnum!((30 * 2) / 15));
        eval_eq_some!("(+ 10 (- 5 2))", exnum!(10 + (5 - 2)));
        eval_eq_some!("(- (* 4 5) (+ 10 5))", exnum!((4 * 5) - (10 + 5)));
        eval_eq_some!(
            "(+ (* 3 3) (* 4 4) (* 5 5))",
            exnum!((3 * 3) + (4 * 4) + (5 * 5))
        );
        eval_eq_some!("(/ (+ 200 300) 100)", exnum!((200 + 300) / 100));
        eval_eq_some!("(/ 720 10 12)", exnum!(720 / 10 / 12));
        eval_eq_some!("(- 200 50 25 25)", exnum!(200 - 50 - 25 - 25));
        eval_eq_some!("(+ (* 2 5) (* 3 7))", exnum!((2 * 5) + (3 * 7)));
        eval_eq_some!("(+ 1 (* 2 (+ 3 5)))", exnum!(1 + (2 * (3 + 5))));
        eval_eq_some!("(- (* 9 3) (/ 27 3))", exnum!((9 * 3) - (27 / 3)));
        eval_eq_some!(
            "(+ (* 2 2) (* 3 3) (* 4 4) (* 5 5))",
            exnum!((2 * 2) + (3 * 3) + (4 * 4) + (5 * 5))
        );
        eval_eq_some!("(/ (+ 1000 2000) 100)", exnum!((1000 + 2000) / 100));
        eval_eq_some!("(+ 5 (* 3 4) (- 20 10))", exnum!(5 + (3 * 4) + (20 - 10)));
        eval_eq_some!("(- (* 6 3) (/ 18 3))", exnum!((6 * 3) - (18 / 3)));
        eval_eq_some!(
            "(+ (* 5 5) (* 4 4) (* 3 3) (* 2 2))",
            exnum!((5 * 5) + (4 * 4) + (3 * 3) + (2 * 2))
        );
        eval_eq_some!("(/ (+ 500 500) 100)", exnum!((500 + 500) / 100));
        eval_eq_some!("(+ 10 (* 2 3) (- 15 5))", exnum!(10 + (2 * 3) + (15 - 5)));
        eval_eq_some!("(- (* 8 4) (/ 32 4))", exnum!((8 * 4) - (32 / 4)));
        eval_eq_some!(
            "(+ (* 3 3) (* 2 2) (* 1 1) (* 0 0))",
            exnum!((3 * 3) + (2 * 2) + (1 * 1) + (0 * 0))
        );
        eval_eq_some!("(/ (+ 10000 20000) 1000)", exnum!((10000 + 20000) / 1000));
        eval_eq_some!("(* 1 2 3 4 5 6 7)", exnum!(1 * 2 * 3 * 4 * 5 * 6 * 7));
        eval_eq_some!("(% 10 3)", exnum!(10 % 3));
        eval_eq_some!("(+ 10 (% 20 6))", exnum!(10 + (20 % 6)));
        eval_eq_some!("(- 50 (% 17 5))", exnum!(50 - (17 % 5)));
        eval_eq_some!("(* 3 (% 14 5))", exnum!(3 * (14 % 5)));
        eval_eq_some!("(/ 100 (% 22 7))", exnum!(100 / (22 % 7)));
        eval_eq_some!("(+ (* 2 3) (% 10 4))", exnum!((2 * 3) + (10 % 4)));
        eval_eq_some!("(- (* 5 4) (% 18 5))", exnum!((5 * 4) - (18 % 5)));
        eval_eq_some!("(+ 1 (* 2 (% 9 4)))", exnum!(1 + (2 * (9 % 4))));
        eval_eq_some!("(- (* 6 3) (% 27 4))", exnum!((6 * 3) - (27 % 4)));
        eval_eq_some!(
            "(+ (* 2 2) (* 3 3) (% 10 3))",
            exnum!((2 * 2) + (3 * 3) + (10 % 3))
        );
        eval_eq_some!("(/ (+ 100 200) (% 50 7))", exnum!((100 + 200) / (50 % 7)));
        eval_eq_some!("(+ 5 (* 3 4) (% 20 6))", exnum!(5 + (3 * 4) + (20 % 6)));
        eval_eq_some!("(- (* 8 4) (% 32 5))", exnum!((8 * 4) - (32 % 5)));
        eval_eq_some!(
            "(+ (* 3 3) (* 2 2) (* 1 1) (% 15 4))",
            exnum!((3 * 3) + (2 * 2) + (1 * 1) + (15 % 4))
        );
        eval_eq_some!(
            "(/ (+ 10000 20000) (% 1000 3))",
            exnum!((10000 + 20000) / (1000 % 3))
        );
        eval_eq_some!(
            "(+ 1 2 3 4 5 6 7 8 (% 9 4))",
            exnum!(1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + (9 % 4))
        );
        eval_eq_some!(
            "(* 1 2 3 4 5 (% 30 7))",
            exnum!(1 * 2 * 3 * 4 * 5 * (30 % 7))
        );
        eval_eq_some!("(/ 5040 (% 100 9) 8)", exnum!(5040 / (100 % 9) / 8));
        eval_eq_some!(
            "(- 100 (% 25 6) (% 10 3))",
            exnum!(100 - (25 % 6) - (10 % 3))
        );
        eval_eq_some!(
            "(+ (* 2 3) (* 4 5) (% 12 5))",
            exnum!((2 * 3) + (4 * 5) + (12 % 5))
        );
        eval_eq_some!("(+ 10 (* 2 (% 15 4)))", exnum!(10 + (2 * (15 % 4))));
        eval_eq_some!("(- (* 9 3) (% 27 3))", exnum!((9 * 3) - (27 % 3)));
        eval_eq_some!(
            "(+ (* 5 5) (* 4 4) (* 3 3) (* 2 2) (% 20 6))",
            exnum!((5 * 5) + (4 * 4) + (3 * 3) + (2 * 2) + (20 % 6))
        );
        eval_eq_some!(
            "(/ (+ 500 500) (% 1000 3))",
            exnum!((500 + 500) / (1000 % 3))
        );
    }
}
