use std::error::Error;

use crate::scanner::{ScanError, Scanner, Token};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BuiltIn {
    Plus,
    Minus,
    Define,
    Newline,
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
pub enum Expr {
    Atom(Atom),
    Cons(Box<Expr>, Box<Expr>),
    Lambda(Vec<String>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    Null,
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Atom(atom) => write!(f, "{atom}"),
            Expr::Cons(_, _) => write!(f, "Cons"),
            Expr::Lambda(_, _) => write!(f, "Lambda"),
            Expr::If(_, _, _) => write!(f, "If"),
            Expr::Null => write!(f, "Null"),
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
        write!(f, "{self:?}")
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
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
/// <expr>    ::= <atom> | <list>
/// <atom>    ::= <number> | <ident> | <string> | <builtin> | <bool>
/// <number>  ::= '-'?[0-9]+
/// <ident>   ::= [a-zA-Z][a-zA-Z0-9-]*
/// <string>  ::= '"' char '"'
/// <builtin> ::= '+' | '-' | 'define'
/// <bool>    ::= '#t' | '#f'
/// <list>    ::= '(' 'lambda' | <expr>* | <if> ')'
/// <lambda   ::= 'lambda' '(' <ident>* ')' <expr>
/// <if>      ::= 'if' <expr> <expr> [<expr>]
impl<'a> Parser<'a> {
    pub fn new(src: &'a [char]) -> Parser<'a> {
        Self {
            scanner: Scanner::new(src),
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
            Token::Num(n) => Ok(Expr::Atom(Atom::Num(n))),
            Token::Ident(i) => match i.as_str() {
                "define" => Ok(Expr::Atom(Atom::BuiltIn(BuiltIn::Define))),
                _ => Ok(Expr::Atom(Atom::Ident(i))),
            },
            Token::Minus => Ok(Expr::Atom(Atom::BuiltIn(BuiltIn::Minus))),
            Token::Plus => Ok(Expr::Atom(Atom::BuiltIn(BuiltIn::Plus))),
            Token::String(s) => Ok(Expr::Atom(Atom::String(s))),
            Token::Bool(b) => Ok(Expr::Atom(Atom::Bool(b))),
            _ => Err(ParseError::UnexpectedToken(next)),
        }
    }

    fn list(&mut self) -> Result<Expr, ParseError> {
        self.take(Token::OPar)?;
        let mut exprs = Vec::new();
        while self.scanner.peek_token().unwrap() != Token::CPar {
            exprs.push(self.expr()?);
        }
        let mut list = Expr::Null;
        for expr in exprs.into_iter().rev() {
            list = Expr::Cons(Box::new(expr), Box::new(list));
        }
        self.take(Token::CPar)?;
        Ok(list)
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

        let mut body = Expr::Null;
        for exp in bodies.into_iter().rev() {
            body = Expr::Cons(Box::new(exp), Box::new(body));
        }

        Ok(Expr::Lambda(vars, Box::new(body)))
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

    fn expr(&mut self) -> Result<Expr, ParseError> {
        match self.scanner.peek_token()? {
            Token::Num(_) | Token::Minus | Token::Plus | Token::String(_) | Token::Bool(_) => {
                self.atom()
            }
            Token::Ident(i) => match i.as_str() {
                "lambda" => self.lambda(),
                "if" => self.if_(),
                "newline" => self.newline(),
                _ => self.atom(),
            },
            Token::OPar => self.list(),
            Token::CPar => Err(ParseError::UnexpectedToken(Token::CPar)),
        }
    }

    pub fn parse_next(&mut self) -> Result<Expr, ParseError> {
        self.expr()
    }
}

#[cfg(test)]
mod tests {
    use crate::{parser::{Atom, BuiltIn, Expr, ParseError, Parser}, scanner::ScanError};

    macro_rules! parse {
        ($in:expr, $ex:expr) => {{
            let in_ = $in.chars().collect::<Vec<char>>();
            let mut parser = Parser::new(&in_);
            let mut res = Vec::new();
            loop {
                match parser.parse_next() {
                    Ok(e) => res.push(e),
                    Err(ParseError::Scan(ScanError::Eof)) => break,
                    Err(err) => panic!("{err}"),
                }
            }
            assert_eq!(res, $ex);
        }};
    }

    macro_rules! list {
        ($($exprs:expr),+) => {
            {
                let elems = vec![$($exprs),+];
                let mut list = Expr::Null;
                for e in elems.into_iter().rev() {
                    list = Expr::Cons(Box::new(e), Box::new(list));
                }
                list
            }
        };
    }

    macro_rules! num {
        ($n:expr) => {
            Expr::Atom(Atom::Num($n))
        };
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

    macro_rules! bi {
        ($v:ident) => {
            Expr::Atom(Atom::BuiltIn(BuiltIn::$v))
        };
    }

    macro_rules! bol {
        ($b:expr) => {
            Expr::Atom(Atom::Bool($b))
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
            vec![list![Expr::Lambda(Vec::new(), Box::new(list!(num!(10))))]]
        );
        parse!(
            "(lambda (x) (+ x 1))",
            vec![list![Expr::Lambda(
                vec![String::from("x")],
                Box::new(list!(list!(bi!(Plus), ident!("x"), num!(1))))
            )]]
        );
    }

    #[test]
    fn if_() {
        parse!(
            "(if #t #t)",
            vec![list![
                Expr::If(Box::new(bol!(true)), Box::new(bol!(true)), None)
            ]]
        );
        parse!(
            "(if #t #t #f)",
            vec![list![
                Expr::If(Box::new(bol!(true)), Box::new(bol!(true)), Some(Box::new(bol!(false))))
            ]]
        );
    }

    #[test]
    fn newline() {
        parse!("(newline)", vec![list!(bi!(Newline))]);
    }
}
