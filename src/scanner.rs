use std::error::Error;

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    Num(i64),
    OPar,
    CPar,
    Ident(String),
    Minus,
    Plus,
    String(String),
}

#[derive(Debug)]
pub enum ScannerError {
    Eof,
    NumConversion,
    InvalidNumChar(char),
    InvalidIdentChar(char),
    InvalidToken,
}

impl ScannerError {
    pub fn is_eof(&self) -> bool {
        matches!(self, Self::Eof)
    }
}

impl std::fmt::Display for ScannerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl Error for ScannerError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

pub struct Scanner<'a> {
    chars: &'a [char],
    pos: usize,
}

impl<'a> Scanner<'a> {
    pub fn new(chars: &'a [char]) -> Self {
        Self { chars, pos: 0 }
    }

    fn is_at_eof(&self) -> bool {
        self.pos >= self.chars.len()
    }

    fn peek(&self) -> Result<char, ScannerError> {
        if !self.is_at_eof() {
            Ok(self.chars[self.pos])
        } else {
            Err(ScannerError::Eof)
        }
    }

    fn peek2(&self) -> Result<char, ScannerError> {
        if self.pos + 1 < self.chars.len() {
            Ok(self.chars[self.pos + 1])
        } else {
            Err(ScannerError::Eof)
        }
    }

    fn next(&mut self) -> Result<char, ScannerError> {
        if !self.is_at_eof() {
            self.pos += 1;
            Ok(self.chars[self.pos - 1])
        } else {
            Err(ScannerError::Eof)
        }
    }

    fn take_identifier(&mut self) -> Result<Option<Token>, ScannerError> {
        let mut ident = String::from(self.next()?);
        while let Ok(next) = self.next() {
            match next {
                ' ' | '\n' | '(' | ')' => break,
                'a'..='z' | 'A'..='Z' | '-' | '0'..='9' | '!' => ident.push(next),
                _ => return Err(ScannerError::InvalidIdentChar(next)),
            }
        }
        Ok(Some(Token::Ident(ident)))
    }

    fn handle_comment(&mut self) {
        while let Ok(next) = self.next() {
            if next == '\n' {
                break;
            }
        }
    }

    fn take_number(&mut self) -> Result<Option<Token>, ScannerError> {
        let mut num_str = String::from(self.next()?);
        while let Ok(next) = self.next() {
            match next {
                ' ' | '\n' | '(' | ')' => break,
                '0'..='9' => num_str.push(next),
                _ => return Err(ScannerError::InvalidNumChar(next)),
            }
        }
        Ok(Some(Token::Num(
            num_str
                .parse::<i64>()
                .map_err(|_| ScannerError::NumConversion)?,
        )))
    }

    // TODO: handle escaped characters
    fn take_string(&mut self) -> Result<Option<Token>, ScannerError> {
        let _ = self.next()?;
        let mut res = String::new();
        while let Ok(next) = self.next() {
            match next {
                '"' => break,
                _ => res.push(next),
            }
        }
        Ok(Some(Token::String(res)))
    }

    fn take_minus(&mut self) -> Result<Option<Token>, ScannerError> {
        let Ok(peek) = self.peek2() else {
            self.pos += 1;
            return Ok(Some(Token::Minus));
        };
        if peek.is_ascii_digit() {
            self.take_number()
        } else if matches!(peek, '\n' | ' ' | '(' | ')') {
            self.pos += 1;
            Ok(Some(Token::Minus))
        } else {
            Err(ScannerError::InvalidToken)
        }
    }

    fn take_plus(&mut self) -> Result<Option<Token>, ScannerError> {
        let Ok(peek) = self.peek2() else {
            self.pos += 1;
            return Ok(Some(Token::Plus));
        };
        if !matches!(peek, ' ' | '\n' | '(' | ')') {
            return Err(ScannerError::InvalidToken);
        }
        self.pos += 1;
        Ok(Some(Token::Plus))
    }

    pub fn next_token(&mut self) -> Result<Option<Token>, ScannerError> {
        match self.peek()? {
            '\n' | ' ' => {
                self.pos += 1;
                Ok(None)
            }
            '(' => {
                self.pos += 1;
                Ok(Some(Token::OPar))
            }
            ')' => {
                self.pos += 1;
                Ok(Some(Token::CPar))
            }
            ';' => {
                self.handle_comment();
                Ok(None)
            }
            '0'..='9' => self.take_number(),
            'a'..='z' | 'A'..='Z' => self.take_identifier(),
            '-' => self.take_minus(),
            '+' => self.take_plus(),
            '"' => self.take_string(),
            _ => Err(ScannerError::Eof),
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
                if let Some(r) = r {
                    res.push(r);
                }
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
        scan_eq_vec!("-12345 -67890", vec![Token::Num(-12345), Token::Num(-67890)]);
    }

    #[test]
    fn ident() {
        scan_eq_vec!("this-is-an-identifier", vec![ident!("this-is-an-identifier")]);
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
        scan_eq_vec!("\"this is a string literal\"", vec![string!("this is a string literal")]);
        scan_eq_vec!("   \"str\"   ", vec![string!("str")]);
        scan_eq_vec!("\n\n\"str\"\n\n", vec![string!("str")]);
    }
}
