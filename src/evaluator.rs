use std::error::Error;

use crate::parser::{Atom, BuiltIn, Expr};

#[derive(Debug)]
pub enum EvalError {
    NotANumber,
    NotACell,
    MissingArguments,
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

fn get_num_from_expr(e: Expr) -> Result<i64, EvalError> {
    match e {
        Expr::Atom(Atom::Num(n)) => Ok(n),
        _ => Err(EvalError::NotANumber),
    }
}

fn get_car(cell: &Expr) -> Result<Expr, EvalError> {
    match cell {
        Expr::Cons(car, _) => Ok(*car.clone()),
        _ => Err(EvalError::NotACell),
    }
}

pub struct Evaluator {}

impl Evaluator {
    pub fn new() -> Self {
        Self {}
    }

    fn extract_numbers(&mut self, e: Expr) -> Result<Vec<i64>, EvalError> {
        let mut numbers = Vec::new();
        let mut e = e;
        while e != Expr::Null {
            numbers.push(get_num_from_expr(self.eval(get_car(&e)?)?)?);
            match e {
                Expr::Cons(_, next_cdr) => e = *next_cdr,
                _ => (),
            }
        }
        if numbers.is_empty() {
            Err(EvalError::MissingArguments)
        } else {
            Ok(numbers)
        }
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
                    let fe = *numbers.first().expect("It's not empty");
                    Ok(Expr::Atom(Atom::Num(
                        numbers.iter().skip(1).fold(fe, |a, b| a - b),
                    )))
                }
            },
            Expr::Null => todo!(),
            _ => todo!("{r:?}"),
        }
    }

    pub fn eval(&mut self, expr: Expr) -> Result<Expr, EvalError> {
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
}
