use std::{collections::HashMap, error::Error};

use crate::parser::{Atom, BuiltIn, Expr};

#[derive(Debug)]
pub enum EvalError {
    NotANumber,
    NotACell,
    MissingArguments,
    NotAnIdent,
    VariableAlreadyExists(String),
    NoVariable(String),
}

impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl Error for EvalError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

fn get_car(cell: &Expr) -> Result<Expr, EvalError> {
    match cell {
        Expr::Cons(car, _) => Ok(*car.clone()),
        _ => Err(EvalError::NotACell),
    }
}

fn get_cons(e: Expr) -> Result<(Box<Expr>, Box<Expr>), EvalError> {
    match e {
        Expr::Cons(car, cdr) => Ok((car, cdr)),
        _ => Err(EvalError::NotACell),
    }
}

pub struct Evaluator {
    scope_stack: Vec<HashMap<String, Expr>>,
}

impl Evaluator {
    pub fn new() -> Self {
        Self {
            scope_stack: vec![HashMap::new()],
        }
    }

    fn push_var(&mut self, ident: String, value: Expr) -> Result<(), EvalError> {
        let i = self.scope_stack.len() - 1;
        if self.scope_stack[i].contains_key(&ident) {
            return Err(EvalError::VariableAlreadyExists(ident));
        }
        assert!(self.scope_stack[i].insert(ident, value).is_none());
        Ok(())
    }

    fn get_variable(&self, ident: &str) -> Result<Expr, EvalError> {
        for scope in self.scope_stack.iter().rev() {
            if scope.contains_key(ident) {
                return Ok(scope.get(ident).expect("It's there").clone());
            }
        }
        Err(EvalError::NoVariable(ident.to_string()))
    }

    fn get_num_from_expr(&self, e: Expr) -> Result<i64, EvalError> {
        match e {
            Expr::Atom(Atom::Num(n)) => Ok(n),
            Expr::Atom(Atom::Ident(i)) => self.get_num_from_expr(self.get_variable(&i)?),
            _ => Err(EvalError::NotANumber),
        }
    }

    fn extract_numbers(&mut self, e: Expr) -> Result<Vec<i64>, EvalError> {
        let mut numbers = Vec::new();
        let mut e = e;
        while e != Expr::Null {
            let reduced = self.eval(get_car(&e)?)?;
            numbers.push(self.get_num_from_expr(reduced)?);
            if let Expr::Cons(_, next_cdr) = e {
                e = *next_cdr;
            }
        }
        if numbers.is_empty() {
            Err(EvalError::MissingArguments)
        } else {
            Ok(numbers)
        }
    }

    fn define(&mut self, arg: Expr) -> Result<Expr, EvalError> {
        let (ident, value) = get_cons(arg)?;
        let Expr::Atom(Atom::Ident(ident)) = *ident else {
            return Err(EvalError::NotAnIdent);
        };
        self.push_var(ident, get_car(&value)?)?;
        Ok(Expr::Null)
    }

    fn eval_cons(&mut self, car: Expr, cdr: Expr) -> Result<Expr, EvalError> {
        let r = self.eval(car)?;
        match r {
            Expr::Cons(_, _) => todo!(),
            Expr::Atom(Atom::BuiltIn(bi)) => match bi {
                BuiltIn::Plus => Ok(Expr::Atom(Atom::Num(
                    self.extract_numbers(cdr)?.iter().sum(),
                ))),
                BuiltIn::Minus => {
                    let numbers = self.extract_numbers(cdr)?;
                    let fe = *numbers.first().expect("Checked");
                    Ok(Expr::Atom(Atom::Num(
                        numbers.iter().skip(1).fold(fe, |a, b| a - b),
                    )))
                }
                BuiltIn::Define => self.define(cdr),
            },
            Expr::Null => todo!(),
            _ => todo!("{r:?}"),
        }
    }

    pub fn eval(&mut self, expr: Expr) -> Result<Expr, EvalError> {
        println!("{:?}", self.scope_stack);
        match expr {
            Expr::Atom(_) | Expr::Null => Ok(expr),
            Expr::Cons(car, cdr) => self.eval_cons(*car, *cdr),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        evaluator::Evaluator,
        parser::{Atom, Expr, Parser},
    };

    macro_rules! eval {
        ($c:expr, $ex:expr) => {
            let in_ = $c.chars().collect::<Vec<char>>();
            let mut parser = Parser::new(&in_);
            let mut evaluator = Evaluator::new();
            assert_eq!(evaluator.eval(parser.parse_next().unwrap()).unwrap(), $ex);
        };
    }

    macro_rules! eval_many {
        ($c:expr, $ex:expr) => {
            let in_ = $c.chars().collect::<Vec<char>>();
            let mut parser = Parser::new(&in_);
            let mut evaluator = Evaluator::new();
            for ex in $ex {
                assert_eq!(evaluator.eval(parser.parse_next().unwrap()).unwrap(), ex);
            }
        };
    }

    macro_rules! num {
        ($n:expr) => {
            Expr::Atom(Atom::Num($n))
        };
    }

    #[test]
    fn arith() {
        eval!("(+ 1 2)", num!(1 + 2));
        eval!("(+ 1 2 3)", num!(1 + 2 + 3));
        eval!("(+ 1 (+ 10 10))", num!(1 + 10 + 10));
        eval!("(+ 1 (+ 10 (+ 10 100)))", num!(1 + 10 + 10 + 100));

        eval!("(- 1 2)", num!(1 - 2));
        eval!("(- 1 2 3)", num!(1 - 2 - 3));
        eval!("(- 1 (- 10 10))", num!(1 - (10 - 10)));
        eval!("(- 1 (- 10 (- 10 100)))", num!(1 - (10 - (10 - 100))));

        eval!("(- (+ 50 50) (+ 10 40))", num!((50 + 50) - (10 + 40)));
    }

    #[test]
    fn define() {
        eval_many!("(define my-var 10)(+ 0 my-var)", vec![Expr::Null, num!(10)]);
        eval_many!(
            "(define my-var 10)(+ 0 my-var)(+ my-var my-var)",
            vec![Expr::Null, num!(10), num!(10 + 10)]
        );
    }
}
