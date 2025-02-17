use std::error::Error;

use crate::scanner::{ScanError, Scanner, Token};

macro_rules! list_from_vec {
    ($vec:expr) => {{
        let mut list = Expr::Null;
        for e in $vec.into_iter().rev() {
            list = Expr::Cons(Box::new(e), Box::new(list));
        }
        list
    }};
}

#[cfg(test)]
macro_rules! list {
    ($($exprs:expr),+) => {
        list_from_vec!(vec![$($exprs),+])
    };
}

macro_rules! num {
    ($n:expr) => {
        Expr::Atom(Atom::Num($n))
    };
}

macro_rules! bol {
    ($b:expr) => {
        Expr::Atom(Atom::Bool($b))
    };
}

macro_rules! bi {
    ($v:ident) => {
        Expr::Atom(Atom::BuiltIn(BuiltIn::$v))
    };
}

pub(crate) use bi;
pub(crate) use bol;
#[cfg(test)]
pub(crate) use list;
pub(crate) use list_from_vec;
pub(crate) use num;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BuiltIn {
    Plus,
    Minus,
    Define,
    Newline,
    Eq,
    Greater,
    Less,
    GreaterOrEq,
    LessOrEq,
    Else,
    Modulo,
    Display,
    Set,
    Car,
    Cdr,
    Cons,
    Times,
    Slash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    Num(i64),
    Ident(String),
    String(String),
    BuiltIn(BuiltIn),
    Bool(bool),
}

impl std::fmt::Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::Num(n) => write!(f, "{n}"),
            Atom::Ident(i) => write!(f, "{i}"),
            Atom::String(s) => write!(f, "{s}"),
            Atom::BuiltIn(bi) => write!(f, "{bi:?}"),
            Atom::Bool(b) => write!(f, "{}", if *b { "#t" } else { "#f" }),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DoVariable {
    pub ident: String,
    pub init: Expr,
    pub step: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Atom(Atom),
    Cons(Box<Expr>, Box<Expr>),
    Lambda(Vec<String>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    Cond(Vec<Expr>),
    Do(Vec<DoVariable>, Box<Expr>, Box<Expr>),
    Quoted(Box<Expr>),
    Null,
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Atom(atom) => write!(f, "{atom}"),
            Expr::Cons(car, cdr) => {
                let mut car = car.clone();
                let mut cdr = cdr.clone();
                write!(f, "(")?;
                while *car != Expr::Null {
                    write!(f, "{car}")?;
                    match *cdr {
                        Expr::Cons(ncar, ncdr) => {
                            write!(f, " ")?;
                            car = ncar;
                            cdr = ncdr;
                        }
                        _ => car = cdr.clone(),
                    }
                }
                write!(f, ")")
            }
            Expr::Lambda(_, _) => write!(f, "Lambda"),
            Expr::If(_, _, _) => write!(f, "If"),
            Expr::Null => write!(f, "Null"),
            Expr::Cond(_) => write!(f, "Cond"),
            Expr::Do(_, _, _) => write!(f, "Do"),
            Expr::Quoted(v) => write!(f, "{v}"),
        }
    }
}

#[derive(Debug)]
pub enum ParseError {
    Scan(ScanError),
    FailedToTake,
    UnexpectedToken(Token),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::Scan(scan_error) => write!(f, "{scan_error}"),
            _ => write!(f, "{self:?}"),
        }
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

impl ParseError {
    pub fn is_eof(&self) -> bool {
        match self {
            ParseError::Scan(scan_error) => scan_error.is_eof(),
            _ => false,
        }
    }
}

impl From<ScanError> for ParseError {
    fn from(value: ScanError) -> Self {
        Self::Scan(value)
    }
}

pub struct Parser<'a> {
    scanner: Scanner<'a>,
}

/// A parser that parses the following grammar.
///
/// <expr>        ::= <atom> | <list> | <comment>
/// <atom>        ::= <number> | <ident> | <string> | <builtin> | <bool>
/// <number>      ::= '-'?[0-9]+
/// <ident>       ::= [a-zA-Z][a-zA-Z0-9-]*
/// <string>      ::= '"' char '"'
/// <builtin>     ::= '+' | '-' | 'define' | '>' | '<' | '>=' | '<=' | '%' | 'display'
///                   | 'newline' | 'set!' | 'car' | cdr
/// <bool>        ::= '#t' | '#f'
/// <list>        ::= '(' 'lambda' | <expr>* | <if> | <cond> | <do> ')'
/// <lambda       ::= 'lambda' '(' <ident>* ')' <expr>
/// <if>          ::= 'if' <expr> <expr> [<expr>]
/// <cond>        ::= 'cond' <cond-clause>*
/// <cond-clause> ::= '(' <expr> <expr> ')' | '(' 'else' <expr> ')'
/// <do>          ::= 'do' '(' <do-variable> ')' '(' <expr>* ')' <expr>*
/// <do-variable> ::= '(' <ident> <expr> <expr> ')'
/// <comment>     ::= ';' <EOL>
impl<'a> Parser<'a> {
    pub fn new(src: &'a [char], file_name: String) -> Parser<'a> {
        Self {
            scanner: Scanner::new(src, file_name),
        }
    }

    fn take(&mut self, t: Token) -> Result<(), ParseError> {
        if self.scanner.next_token()? != t {
            Err(ParseError::FailedToTake)
        } else {
            Ok(())
        }
    }

    fn atom(&mut self) -> Result<Expr, ParseError> {
        let next = self.scanner.next_token()?;
        match next {
            Token::Num(n) => Ok(num!(n)),
            Token::Ident(i) => match i.as_str() {
                "define" => Ok(bi!(Define)),
                "else" => Ok(bi!(Else)),
                "display" => Ok(bi!(Display)),
                "set!" => Ok(bi!(Set)),
                "car" => Ok(bi!(Car)),
                "cdr" => Ok(bi!(Cdr)),
                "cons" => Ok(bi!(Cons)),
                _ => Ok(Expr::Atom(Atom::Ident(i))),
            },
            Token::Minus => Ok(bi!(Minus)),
            Token::Plus => Ok(bi!(Plus)),
            Token::String(s) => Ok(Expr::Atom(Atom::String(s))),
            Token::Bool(b) => Ok(bol!(b)),
            Token::Eq => Ok(bi!(Eq)),
            Token::Less => Ok(bi!(Less)),
            Token::Greater => Ok(bi!(Greater)),
            Token::LessOrEq => Ok(bi!(LessOrEq)),
            Token::GreaterOrEq => Ok(bi!(GreaterOrEq)),
            Token::Percent => Ok(bi!(Modulo)),
            Token::Times => Ok(bi!(Times)),
            Token::Slash => Ok(bi!(Slash)),
            _ => Err(ParseError::UnexpectedToken(next)),
        }
    }

    fn list(&mut self) -> Result<Expr, ParseError> {
        self.take(Token::OPar)?;
        let mut exprs = Vec::new();
        while self.scanner.peek_token()? != Token::CPar {
            exprs.push(self.expr()?);
        }
        self.take(Token::CPar)?;

        if exprs.len() == 1 {
            match exprs[0] {
                Expr::Lambda(_, _) => return Ok(exprs[0].clone()),
                _ => (),
            }
        }

        Ok(list_from_vec!(exprs))
    }

    fn lambda(&mut self) -> Result<Expr, ParseError> {
        self.take(Token::Ident(String::from("lambda")))?;
        self.take(Token::OPar)?;
        let mut vars = Vec::new();
        while self.scanner.peek_token()? != Token::CPar {
            let next = self.scanner.next_token()?;
            match next {
                Token::Ident(i) => vars.push(i),
                _ => return Err(ParseError::UnexpectedToken(next)),
            }
        }
        self.take(Token::CPar)?;

        let mut bodies = Vec::new();
        while self.scanner.peek_token()? != Token::CPar {
            bodies.push(self.expr()?);
        }

        Ok(Expr::Lambda(vars, Box::new(list_from_vec!(bodies))))
    }

    fn if_(&mut self) -> Result<Expr, ParseError> {
        self.take(Token::Ident(String::from("if")))?;
        let condition = Box::new(self.expr()?);
        let true_branch = Box::new(self.expr()?);
        let false_branch = if self.scanner.peek_token()? != Token::CPar {
            Some(Box::new(self.expr()?))
        } else {
            None
        };
        Ok(Expr::If(condition, true_branch, false_branch))
    }

    fn newline(&mut self) -> Result<Expr, ParseError> {
        self.take(Token::Ident(String::from("newline")))?;
        Ok(Expr::Atom(Atom::BuiltIn(BuiltIn::Newline)))
    }

    fn cond(&mut self) -> Result<Expr, ParseError> {
        self.take(Token::Ident(String::from("cond")))?;
        let mut clauses = Vec::new();
        while self.scanner.peek_token()? != Token::CPar {
            clauses.push(self.expr()?);
        }
        Ok(Expr::Cond(clauses))
    }

    fn do_variable(&mut self) -> Result<DoVariable, ParseError> {
        let var = self.list()?;
        match var {
            Expr::Cons(ident, cdr) => {
                let Expr::Atom(Atom::Ident(ident)) = *ident else {
                    todo!();
                };
                match *cdr {
                    Expr::Cons(init, step) => {
                        let Expr::Cons(step, should_be_null) = *step else {
                            todo!();
                        };
                        assert_eq!(*should_be_null, Expr::Null);
                        Ok(DoVariable {
                            ident,
                            init: *init,
                            step: *step,
                        })
                    }
                    _ => todo!(),
                }
            }
            _ => todo!(),
        }
    }

    fn do_(&mut self) -> Result<Expr, ParseError> {
        self.take(Token::Ident(String::from("do")))?;
        self.take(Token::OPar)?;
        let mut vars: Vec<DoVariable> = Vec::new();
        while self.scanner.peek_token()? != Token::CPar {
            vars.push(self.do_variable()?);
        }
        self.take(Token::CPar)?;

        let test = self.list()?;

        let mut body = Vec::new();

        while self.scanner.peek_token()? != Token::CPar {
            body.push(self.expr()?);
        }

        Ok(Expr::Do(
            vars,
            Box::new(test),
            Box::new(list_from_vec!(body)),
        ))
    }

    fn quote(&mut self) -> Result<Expr, ParseError> {
        self.take(Token::Tick)?;
        Ok(Expr::Quoted(Box::new(self.expr()?)))
    }

    fn expr(&mut self) -> Result<Expr, ParseError> {
        match self.scanner.peek_token()? {
            Token::Num(_)
            | Token::Minus
            | Token::Plus
            | Token::String(_)
            | Token::Bool(_)
            | Token::Eq
            | Token::Greater
            | Token::Less
            | Token::GreaterOrEq
            | Token::LessOrEq
            | Token::Times
            | Token::Slash
            | Token::Percent => self.atom(),
            Token::Ident(i) => match i.as_str() {
                "lambda" => self.lambda(),
                "if" => self.if_(),
                "newline" => self.newline(),
                "cond" => self.cond(),
                "do" => self.do_(),
                _ => self.atom(),
            },
            Token::OPar => self.list(),
            Token::CPar => Err(ParseError::UnexpectedToken(Token::CPar)),
            Token::Tick => self.quote(),
        }
    }

    pub fn parse_next(&mut self) -> Result<Expr, ParseError> {
        self.expr()
    }
}

#[cfg(test)]
mod tests {
    use crate:: parser::{bi, bol, list, list_from_vec, num, Atom, BuiltIn, DoVariable, Expr, Parser,};

    macro_rules! parse {
        ($in:expr, $ex:expr) => {{
            let in_ = $in.chars().collect::<Vec<char>>();
            let mut parser = Parser::new(&in_, "test".to_owned());
            let mut res = Vec::new();
            loop {
                match parser.parse_next() {
                    Ok(e) => res.push(e),
                    Err(err) if err.is_eof() => break,
                    Err(err) => panic!("{err}"),
                }
            }
            assert_eq!(res, $ex);
        }};
    }

    macro_rules! string {
        ($s:expr) => {
            Expr::Atom(Atom::String(String::from($s)))
        };
    }

    macro_rules! ident {
        ($i:expr) => {
            Expr::Atom(Atom::Ident(String::from($i)))
        };
    }

    macro_rules! cond {
        ($($clauses:expr),+) => {
            Expr::Cond(vec![$($clauses),+])
        };
    }

    #[test]
    fn atom() {
        parse!("123", vec![num!(123)]);
        parse!("some-ident", vec![ident!("some-ident")]);
        parse!("\"some string\"", vec![string!("some string")]);
        parse!("-", vec![bi!(Minus)]);
        parse!("+", vec![bi!(Plus)]);
        parse!("define", vec![bi!(Define)]);
    }

    #[test]
    fn list() {
        parse!("()", vec![Expr::Null]);
        parse!("(123)", vec![list![num!(123)]]);
        parse!("(123 456)", vec![list![num!(123), num!(456)]]);
        parse!("(\"string\")", vec![list![string!("string")]]);
        parse!("(ident)", vec![list![ident!("ident")]]);
    }

    #[test]
    fn complex_list() {
        parse!("(())", vec![list![Expr::Null]]);
        parse!("(()())", vec![list![Expr::Null, Expr::Null]]);
        parse!("(()(123))", vec![list![Expr::Null, list![num!(123)]]]);
        parse!(
            "(()(123 num-and-ident))",
            vec![list![Expr::Null, list![num!(123), ident!("num-and-ident")]]]
        );
        parse!(
            "(()(123 \"num and string\"))",
            vec![list![
                Expr::Null,
                list![num!(123), string!("num and string")]
            ]]
        );
    }

    #[test]
    fn lambda() {
        parse!(
            "(lambda () 10)",
            vec![Expr::Lambda(Vec::new(), Box::new(list!(num!(10))))]
        );
        parse!(
            "(lambda (x) (+ x 1))",
            vec![Expr::Lambda(
                vec![String::from("x")],
                Box::new(list!(list!(bi!(Plus), ident!("x"), num!(1))))
            )]
        );
    }

    #[test]
    fn if_() {
        parse!(
            "(if #t #t)",
            vec![list![Expr::If(
                Box::new(bol!(true)),
                Box::new(bol!(true)),
                None
            )]]
        );
        parse!(
            "(if #t #t #f)",
            vec![list![Expr::If(
                Box::new(bol!(true)),
                Box::new(bol!(true)),
                Some(Box::new(bol!(false)))
            )]]
        );
    }

    #[test]
    fn newline() {
        parse!("(newline)", vec![list!(bi!(Newline))]);
    }

    #[test]
    fn cond() {
        parse!(
            "(cond (else #t))",
            vec![list![cond![list![bi!(Else), bol!(true)]]]]
        );
        parse!(
            "(cond ((< 1 2) #t))",
            vec![list![cond![list![
                list![bi!(Less), num!(1), num!(2)],
                bol!(true)
            ]]]]
        );
        parse!(
            "(cond ((< 1 2) #t) (else #t))",
            vec![list![cond![
                list![list![bi!(Less), num!(1), num!(2)], bol!(true)],
                list![bi!(Else), bol!(true)]
            ]]]
        );
    }

    #[test]
    fn modulo() {
        parse!("%", vec![bi!(Modulo)]);
    }

    #[test]
    fn display() {
        parse!("display", vec![bi!(Display)]);
    }

    #[test]
    fn list_macro() {
        assert_eq!(
            list![bi!(Plus), ident!("x"), num!(10)],
            Expr::Cons(
                Box::new(bi!(Plus)),
                Box::new(Expr::Cons(
                    Box::new(ident!("x")),
                    Box::new(Expr::Cons(Box::new(num!(10)), Box::new(Expr::Null),))
                ))
            )
        );
    }

    #[test]
    fn do_() {
        parse!(
            "(do ((x 0 (+ x 1))) ((> x 10) x) (display x) (newline))",
            vec![list![Expr::Do(
                vec![DoVariable {
                    ident: String::from("x"),
                    init: num!(0),
                    step: list![bi!(Plus), ident!("x"), num!(1)]
                }],
                Box::new(list![
                    list![bi!(Greater), ident!("x"), num!(10)],
                    ident!("x")
                ]),
                Box::new(list![list![bi!(Display), ident!("x")], list![bi!(Newline)]]),
            )]]
        );
    }

    #[test]
    fn set() {
        parse!("set!", vec![bi!(Set)]);
    }

    #[test]
    fn quoted() {
        parse!(
            "'(1 2 3)",
            vec![Expr::Quoted(Box::new(list![num!(1), num!(2), num!(3)]))]
        );
    }

    #[test]
    fn car() {
        parse!("car", vec![bi!(Car)]);
    }

    #[test]
    fn cdr() {
        parse!("cdr", vec![bi!(Cdr)]);
    }

    #[test]
    fn cons() {
        parse!("cons", vec![bi!(Cons)]);
    }

    #[test]
    fn times() {
        parse!("*", vec![bi!(Times)]);
    }

    #[test]
    fn slash() {
        parse!("/", vec![bi!(Slash)]);
    }
}
