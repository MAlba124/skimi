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
    NotALambda(String),
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

    fn push_scope(&mut self) {
        self.scope_stack.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        let _ = self
            .scope_stack
            .pop()
            .expect("Something has gone terribly wrong");
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
        let mut car = get_car(&value)?;
        match car {
            Expr::Cons(ref maybe, _) => match **maybe {
                // Lambdas are the car of a one element cell, take it out to make it easier to deal with
                Expr::Lambda(_, _) => car = *maybe.clone(),
                _ => (),
            },
            _ => (),
        }
        self.push_var(ident, car)?;
        Ok(Expr::Null)
    }

    fn eval_cons(&mut self, car: Expr, cdr: Expr) -> Result<Expr, EvalError> {
        let r = self.eval(car)?;
        match r {
            Expr::Cons(_, _) => todo!(),
            Expr::Atom(Atom::BuiltIn(ref bi)) => match bi {
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
            Expr::Lambda(var_names, body) => {
                let mut var_values = Vec::new();
                let mut cdr = cdr;
                while cdr != Expr::Null {
                    match cdr {
                        Expr::Atom(_) | Expr::Lambda(_, _) => {
                            var_values.push(cdr.clone());
                            cdr = Expr::Null;
                        }
                        Expr::Cons(car, next_cdr) => {
                            var_values.push(self.eval(*car)?);
                            cdr = *next_cdr;
                        }
                        _ => unreachable!(),
                    }
                }

                if var_values.len() != var_names.len() {
                    panic!("TODO: lambda takes _ arguments, got _");
                }

                self.push_scope();

                for (key, value) in var_names.into_iter().zip(var_values.into_iter()) {
                    if let Err(err) = self.push_var(key, value) {
                        self.pop_scope();
                        return Err(err);
                    }
                }

                let ret = self.eval(*body);
                self.pop_scope();

                ret
            }
            _ => {
                let last = self.eval(cdr)?;
                if last == Expr::Null {
                    Ok(r)
                } else {
                    Ok(last)
                }
            }
        }
    }

    pub fn eval(&mut self, expr: Expr) -> Result<Expr, EvalError> {
        match expr {
            Expr::Atom(Atom::Ident(i)) => self.get_variable(&i),
            Expr::Atom(_) | Expr::Null | Expr::Lambda(_, _) => Ok(expr),
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
        eval_many!("(define my-var 10) my-var", vec![Expr::Null, num!(10)]);
        eval_many!(
            "(define my-var 10) my-var (+ my-var my-var)",
            vec![Expr::Null, num!(10), num!(10 + 10)]
        );
    }

    #[test]
    fn lambda() {
        eval_many!("(define my-lambda (lambda () 10)) (my-lambda)", vec![Expr::Null, num!(10)]);
    }
}
