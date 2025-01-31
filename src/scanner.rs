use std::error::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    Num(i64),
    OPar,
    CPar,
    Ident(String),
    Minus,
    Plus,
    Eq,
    Greater,
    Less,
    GreaterOrEq,
    LessOrEq,
    String(String),
    Bool(bool),
    Percent,
    Tick,
    Times,
    Slash,
}

#[derive(Debug)]
pub enum ScanErrorReason {
    Eof,
    NumConversion,
    InvalidNumChar(char),
    InvalidIdentChar(char),
    InvalidToken,
    PeekNotFlushed,
    NotABool(char),
    InvalidLess,
    InvalidGreater,
    InvalidPercent,
    InvalidTimes,
    InvalidSlash,
    ExpectedTerminal,
    UnclosedString,
}

#[derive(Debug)]
pub struct ScanError {
    pub reason: ScanErrorReason,
    pub line: String,
    pub col: usize,
    pub line_num: usize,
}

impl ScanError {
    pub fn is_eof(&self) -> bool {
        matches!(self.reason, ScanErrorReason::Eof)
    }
}

impl std::fmt::Display for ScanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let line_num_str = self.line_num.to_string();
        write!(f, "Error: :{}:{}\n", self.line_num, self.col)?;
        write!(f, " {} | {}\n", line_num_str, self.line)?;
        write!(f, "{}^ {:?}" , " ".repeat(4 + line_num_str.len() + self.col - 1), self.reason)
    }
}

impl Error for ScanError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

macro_rules! scan_err {
    ($scanner: expr, $reason: expr) => {
        {
            let (line, line_num, col_num) = $scanner.get_current_line();
            ScanError {
                reason: $reason,
                line: line,
                col: col_num,
                line_num,
            }
        }
    };
}

pub struct Scanner<'a> {
    chars: &'a [char],
    pos: usize,
    scanned: Option<Token>,
}

impl<'a> Scanner<'a> {
    pub fn new(chars: &'a [char]) -> Self {
        Self {
            chars,
            pos: 0,
            scanned: None,
        }
    }

    fn is_at_eof(&self) -> bool {
        self.pos >= self.chars.len()
    }

    fn peek(&self) -> Result<char, ScanError> {
        if !self.is_at_eof() {
            Ok(self.chars[self.pos])
        } else {
            Err(scan_err!(self, ScanErrorReason::Eof))
        }
    }

    fn peek2(&self) -> Result<char, ScanError> {
        if self.pos + 1 < self.chars.len() {
            Ok(self.chars[self.pos + 1])
        } else {
            Err(scan_err!(self, ScanErrorReason::Eof))
        }
    }

    fn next(&mut self) -> Result<char, ScanError> {
        if !self.is_at_eof() {
            self.pos += 1;
            Ok(self.chars[self.pos - 1])
        } else {
            Err(scan_err!(self, ScanErrorReason::Eof))
        }
    }

    // -> (line, line_num, col_num)
    fn get_current_line(&self) -> (String, usize, usize) {
        let mut line = String::new();
        let mut line_num = 1;
        let mut col_num = self.pos + 1;
        let mut pos = self.pos.min(self.chars.len() - 1);
        while pos > 0 && self.chars[pos] != '\n' {
            pos -= 1;
        }

        if pos == 0 && self.chars[pos] == '\n' {
            pos += 1;
        }

        col_num -= pos;

        let mut line_pos = 0;
        while line_pos < pos {
            if self.chars[line_pos] == '\n' {
                line_num += 1;
            }
            line_pos += 1;
        }

        while pos < self.chars.len() && self.chars[pos] != '\n' {
            line.push(self.chars[pos]);
            pos += 1;
        }

        (line, line_num, col_num)
    }

    fn take_identifier(&mut self) -> Result<Token, ScanError> {
        let mut ident = String::from(self.next()?);
        while let Ok(next) = self.peek() {
            match next {
                ' ' | '\n' | '(' | ')' => break,
                'a'..='z' | 'A'..='Z' | '-' | '0'..='9' | '!' => ident.push(self.next()?),
                _ => return Err(scan_err!(self, ScanErrorReason::InvalidIdentChar(next))),
            }
        }
        Ok(Token::Ident(ident))
    }

    fn handle_comment(&mut self) {
        while let Ok(next) = self.next() {
            if next == '\n' {
                break;
            }
        }
    }

    fn take_number(&mut self) -> Result<Token, ScanError> {
        let mut num_str = String::from(self.next()?);
        while let Ok(next) = self.peek() {
            match next {
                ' ' | '\n' | '(' | ')' => break,
                '0'..='9' => num_str.push(self.next()?),
                _ => return Err(scan_err!(self, ScanErrorReason::InvalidNumChar(next))),
            }
        }
        Ok(Token::Num(
            num_str
                .parse::<i64>()
                .map_err(|_| scan_err!(self, ScanErrorReason::NumConversion))?,
        ))
    }

    // TODO: handle escaped characters
    fn take_string(&mut self) -> Result<Token, ScanError> {
        let _ = self.next()?;
        let mut res = String::new();
        while let Ok(next) = self.next() {
            match next {
                '"' => return Ok(Token::String(res)),
                _ => res.push(next),
            }
        }
        Err(scan_err!(self, ScanErrorReason::UnclosedString))
    }

    fn take_minus(&mut self) -> Result<Token, ScanError> {
        let Ok(peek) = self.peek2() else {
            self.pos += 1;
            return Ok(Token::Minus);
        };
        if peek.is_ascii_digit() {
            self.take_number()
        } else if matches!(peek, '\n' | ' ' | '(' | ')') {
            self.pos += 1;
            Ok(Token::Minus)
        } else {
            Err(scan_err!(self, ScanErrorReason::InvalidToken))
        }
    }

    fn peek_terminal(&self) -> Result<(), ScanError> {
        match self.peek() {
            Ok(peek) => match matches!(peek, ' ' | '\n' | '(' | ')') {
                true => Ok(()),
                false => Err(scan_err!(self, ScanErrorReason::ExpectedTerminal)),
            },
            Err(_) => Ok(()),
        }
    }

    fn take_plus(&mut self) -> Result<Token, ScanError> {
        if self.next()? != '+' {
            unreachable!();
        }
        self.peek_terminal()?;
        Ok(Token::Plus)
    }

    fn take_bool(&mut self) -> Result<Token, ScanError> {
        if self.next()? != '#' {
            unreachable!();
        }
        let next = self.next()?;
        let ret = match next {
            't' => Token::Bool(true),
            'f' => Token::Bool(false),
            _ => return Err(scan_err!(self, ScanErrorReason::NotABool(next))),
        };
        self.peek_terminal()?;
        Ok(ret)
    }

    fn take_eq(&mut self) -> Result<Token, ScanError> {
        if self.next()? != '=' {
            unreachable!();
        }
        self.peek_terminal()?;
        Ok(Token::Eq)
    }

    fn take_less(&mut self) -> Result<Token, ScanError> {
        if self.next()? != '<' {
            unreachable!();
        }
        match self.peek() {
            Ok(peek) => match peek {
                ' ' | '\n' | '(' | ')' => Ok(Token::Less),
                '=' => {
                    let _ = self.next()?;
                    self.peek_terminal()?;
                    Ok(Token::LessOrEq)
                }
                _ => Err(scan_err!(self, ScanErrorReason::InvalidLess)),
            },
            _ => Ok(Token::Less),
        }
    }

    fn take_greater(&mut self) -> Result<Token, ScanError> {
        if self.next()? != '>' {
            unreachable!();
        }
        match self.peek() {
            Ok(peek) => match peek {
                ' ' | '\n' | '(' | ')' => Ok(Token::Greater),
                '=' => {
                    let _ = self.next()?;
                    self.peek_terminal()?;
                    Ok(Token::GreaterOrEq)
                }
                _ => Err(scan_err!(self, ScanErrorReason::InvalidGreater)),
            },
            _ => Ok(Token::Greater),
        }
    }

    fn take_percent(&mut self) -> Result<Token, ScanError> {
        if self.next()? != '%' {
            unreachable!();
        }
        self.peek_terminal()?;
        Ok(Token::Percent)
    }

    fn take_tick(&mut self) -> Result<Token, ScanError> {
        if self.next()? != '\'' {
            unreachable!();
        }
        Ok(Token::Tick)
    }

    fn take_times(&mut self) -> Result<Token, ScanError> {
        if self.next()? != '*' {
            unreachable!();
        }
        self.peek_terminal()?;
        Ok(Token::Times)
    }

    fn take_slash(&mut self) -> Result<Token, ScanError> {
        if self.next()? != '/' {
            unreachable!();
        }
        self.peek_terminal()?;
        Ok(Token::Slash)
    }

    pub fn next_token(&mut self) -> Result<Token, ScanError> {
        if let Some(scanned_next) = self.scanned.take() {
            return Ok(scanned_next);
        }

        loop {
            return match self.peek()? {
                '\n' | ' ' => {
                    self.pos += 1;
                    continue;
                }
                '(' => {
                    self.pos += 1;
                    Ok(Token::OPar)
                }
                ')' => {
                    self.pos += 1;
                    Ok(Token::CPar)
                }
                ';' => {
                    self.handle_comment();
                    continue;
                }
                '#' => self.take_bool(),
                '0'..='9' => self.take_number(),
                'a'..='z' | 'A'..='Z' => self.take_identifier(),
                '-' => self.take_minus(),
                '+' => self.take_plus(),
                '"' => self.take_string(),
                '=' => self.take_eq(),
                '<' => self.take_less(),
                '>' => self.take_greater(),
                '%' => self.take_percent(),
                '\'' => self.take_tick(),
                '*' => self.take_times(),
                '/' => self.take_slash(),
                _ => Err(scan_err!(self, ScanErrorReason::Eof)),
            };
        }
    }

    pub fn peek_token(&mut self) -> Result<Token, ScanError> {
        if let Some(scanned) = &self.scanned {
            Ok(scanned.clone())
        } else {
            let next = self.next_token()?;
            self.scanned = Some(next.clone());
            Ok(next)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::scanner::{Scanner, Token};

    macro_rules! zero {
        () => {{
            let a: Vec<Token> = Vec::new();
            a
        }};
    }

    macro_rules! ident {
        ($i:expr) => {
            Token::Ident(String::from($i))
        };
    }

    macro_rules! string {
        ($i:expr) => {
            Token::String(String::from($i))
        };
    }

    macro_rules! scan_eq_vec {
        ($in:expr, $ex:expr) => {
            let temp = $in.chars().collect::<Vec<char>>();
            let mut scanner = Scanner::new(&temp);
            let mut res = Vec::new();
            while let Ok(r) = scanner.next_token() {
                res.push(r);
            }
            assert_eq!($ex, res);
        };
    }

    #[test]
    fn open_close() {
        scan_eq_vec!("()", vec![Token::OPar, Token::CPar]);
        scan_eq_vec!(
            "( ( ) )",
            vec![Token::OPar, Token::OPar, Token::CPar, Token::CPar]
        );
        scan_eq_vec!(
            ") ( ) (",
            vec![Token::CPar, Token::OPar, Token::CPar, Token::OPar]
        );
        scan_eq_vec!("( \n\n )", vec![Token::OPar, Token::CPar]);
    }

    #[test]
    fn comment() {
        scan_eq_vec!("; this is a comment", zero!());
        scan_eq_vec!("; this\n; is\n; a\n; comment", zero!());
    }

    #[test]
    fn number() {
        scan_eq_vec!("1", vec![Token::Num(1)]);
        scan_eq_vec!("12345", vec![Token::Num(12345)]);
        scan_eq_vec!("12345 67890", vec![Token::Num(12345), Token::Num(67890)]);
        scan_eq_vec!("-12345", vec![Token::Num(-12345)]);
        scan_eq_vec!(
            "-12345 -67890",
            vec![Token::Num(-12345), Token::Num(-67890)]
        );
    }

    #[test]
    fn ident() {
        scan_eq_vec!(
            "this-is-an-identifier",
            vec![ident!("this-is-an-identifier")]
        );
        scan_eq_vec!("with!-123", vec![ident!("with!-123")]);
        scan_eq_vec!("something   ", vec![ident!("something")]);
        scan_eq_vec!("\n\nsomething\n\n", vec![ident!("something")]);
    }

    #[test]
    fn minus() {
        scan_eq_vec!("-", vec![Token::Minus]);
        scan_eq_vec!("- - -", vec![Token::Minus, Token::Minus, Token::Minus]);
        scan_eq_vec!("\n-\n", vec![Token::Minus]);
    }

    #[test]
    fn plus() {
        scan_eq_vec!("+", vec![Token::Plus]);
        scan_eq_vec!("+ + +", vec![Token::Plus, Token::Plus, Token::Plus]);
        scan_eq_vec!("\n+\n", vec![Token::Plus]);
    }

    #[test]
    fn string() {
        scan_eq_vec!(
            "\"this is a string literal\"",
            vec![string!("this is a string literal")]
        );
        scan_eq_vec!("   \"str\"   ", vec![string!("str")]);
        scan_eq_vec!("\n\n\"str\"\n\n", vec![string!("str")]);
    }

    #[test]
    fn bool_() {
        scan_eq_vec!("#t", vec![Token::Bool(true)]);
        scan_eq_vec!("#f", vec![Token::Bool(false)]);
        scan_eq_vec!("#t #f", vec![Token::Bool(true), Token::Bool(false)]);
    }

    #[test]
    fn eq() {
        scan_eq_vec!("=", vec![Token::Eq]);
    }

    #[test]
    fn combined() {
        scan_eq_vec!("(ident)", vec![Token::OPar, ident!("ident"), Token::CPar]);
        scan_eq_vec!(
            "(\"string\")",
            vec![Token::OPar, string!("string"), Token::CPar]
        );
    }

    #[test]
    fn less() {
        scan_eq_vec!("<", vec![Token::Less]);
        scan_eq_vec!("<=", vec![Token::LessOrEq]);
    }

    #[test]
    fn greater() {
        scan_eq_vec!(">", vec![Token::Greater]);
        scan_eq_vec!(">=", vec![Token::GreaterOrEq]);
    }

    #[test]
    fn percent() {
        scan_eq_vec!("%", vec![Token::Percent]);
    }

    #[test]
    fn tick() {
        scan_eq_vec!("'", vec![Token::Tick]);
    }

    #[test]
    fn times() {
        scan_eq_vec!("*", vec![Token::Times]);
    }

    #[test]
    fn slash() {
        scan_eq_vec!("/", vec![Token::Slash]);
    }

    #[test]
    fn peek() {
        {
            let in_ = "+".chars().collect::<Vec<char>>();
            let mut scanner = Scanner::new(&in_);
            assert_eq!(scanner.peek_token().unwrap(), Token::Plus);
            assert_eq!(scanner.next_token().unwrap(), Token::Plus);
        }
        {
            let in_ = "+ 123".chars().collect::<Vec<char>>();
            let mut scanner = Scanner::new(&in_);
            assert_eq!(scanner.peek_token().unwrap(), Token::Plus);
            assert_eq!(scanner.next_token().unwrap(), Token::Plus);

            assert_eq!(scanner.peek_token().unwrap(), Token::Num(123));
            assert_eq!(scanner.next_token().unwrap(), Token::Num(123));
        }

        {
            let in_ = "+ 123 (".chars().collect::<Vec<char>>();
            let mut scanner = Scanner::new(&in_);
            assert_eq!(scanner.peek_token().unwrap(), Token::Plus);
            assert_eq!(scanner.next_token().unwrap(), Token::Plus);

            assert_eq!(scanner.peek_token().unwrap(), Token::Num(123));
            assert_eq!(scanner.next_token().unwrap(), Token::Num(123));

            assert_eq!(scanner.next_token().unwrap(), Token::OPar);
        }
    }
}
