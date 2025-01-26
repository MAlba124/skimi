use std::{collections::HashMap, error::Error};

use crate::parser::{Atom, BuiltIn, DoVariable, Expr};

#[derive(Debug)]
pub enum EvalError {
    NotANumber,
    NotACell,
    MissingArguments,
    NotAnIdent,
    VariableAlreadyExists(String),
    NoVariable(String),
    NotALambda(String),
    UnexpectedArgument(Expr),
    IllegalCondClause,
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

fn get_bool(e: Expr) -> bool {
    match e {
        Expr::Atom(Atom::Bool(b)) => b,
        Expr::Null => false,
        _ => true,
    }
}

fn cons_to_vec(cell: Expr) -> Vec<Expr> {
    let mut r = Vec::new();
    let mut cell = cell;
    loop {
        match cell {
            Expr::Cons(ref car, ref cdr) => {
                r.push(*car.clone());
                if **cdr == Expr::Null {
                    break;
                }
                cell = *cdr.clone();
            }
            _ => r.push(cell.clone()),
        }
    }
    r
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

    fn update_var(&mut self, ident: &str, value: Expr) -> Result<(), EvalError> {
        for scope in self.scope_stack.iter_mut().rev() {
            if scope.contains_key(ident) {
                if let Some(var) = scope.get_mut(ident) {
                    *var = value;
                    return Ok(());
                }
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

    fn eq(&mut self, args: Expr) -> Result<Expr, EvalError> {
        let reduced = cons_to_vec(args)
            .into_iter()
            .map(|e| self.eval(e))
            .collect::<Result<Vec<Expr>, EvalError>>()?;
        Ok(Expr::Atom(Atom::Bool(
            reduced
                .iter()
                .zip(reduced.iter().skip(1))
                .all(|(a, b)| a == b),
        )))
    }

    fn num_cmp(
        &mut self,
        args: Expr,
        cmpf: impl FnMut((&i64, &i64)) -> bool,
    ) -> Result<Expr, EvalError> {
        let reduced = cons_to_vec(args)
            .into_iter()
            .map(|e| {
                let e = self.eval(e)?;
                self.get_num_from_expr(e)
            })
            .collect::<Result<Vec<i64>, EvalError>>()?;
        Ok(Expr::Atom(Atom::Bool(
            reduced.iter().zip(reduced.iter().skip(1)).all(cmpf),
        )))
    }

    fn less(&mut self, args: Expr) -> Result<Expr, EvalError> {
        self.num_cmp(args, |(a, b)| a < b)
    }

    fn greater(&mut self, args: Expr) -> Result<Expr, EvalError> {
        self.num_cmp(args, |(a, b)| a > b)
    }

    fn less_or_eq(&mut self, args: Expr) -> Result<Expr, EvalError> {
        self.num_cmp(args, |(a, b)| a <= b)
    }

    fn greater_or_eq(&mut self, args: Expr) -> Result<Expr, EvalError> {
        self.num_cmp(args, |(a, b)| a >= b)
    }

    fn modulo(&mut self, args: Expr) -> Result<Expr, EvalError> {
        let numbers = self.extract_numbers(args)?;
        let fe = *numbers.first().expect("Checked");
        Ok(Expr::Atom(Atom::Num(
            numbers.iter().skip(1).fold(fe, |a, b| a % b),
        )))
    }

    fn display(&mut self, arg: Expr) -> Result<Expr, EvalError> {
        let r = self.eval(arg)?;
        match r {
            Expr::Cons(car, cdr) => {
                if *cdr != Expr::Null {
                    return Err(EvalError::UnexpectedArgument(*cdr));
                }
                print!("{car}");
            }
            _ => print!("{r}"),
        }
        Ok(Expr::Null)
    }

    fn set(&mut self, arg: Expr) -> Result<Expr, EvalError> {
        match arg {
            Expr::Cons(ident, val) => {
                let Expr::Atom(Atom::Ident(ident)) = *ident else {
                    todo!();
                };
                let val = self.eval(*val)?;
                self.update_var(&ident, val)?;
            }
            _ => todo!(),
        }
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
                BuiltIn::Newline => {
                    if cdr != Expr::Null {
                        return Err(EvalError::UnexpectedArgument(cdr));
                    }
                    println!();
                    Ok(Expr::Null)
                }
                BuiltIn::Eq => self.eq(cdr),
                BuiltIn::Greater => self.greater(cdr),
                BuiltIn::Less => self.less(cdr),
                BuiltIn::GreaterOrEq => self.greater_or_eq(cdr),
                BuiltIn::LessOrEq => self.less_or_eq(cdr),
                BuiltIn::Modulo => self.modulo(cdr),
                BuiltIn::Else => Ok(Expr::Atom(Atom::Bool(true))),
                BuiltIn::Display => self.display(cdr),
                BuiltIn::Set => self.set(cdr),
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
            Expr::If(condition, true_branch, false_branch) => {
                if get_bool(self.eval(*condition)?) {
                    self.eval(*true_branch)
                } else if let Some(false_branch) = false_branch {
                    self.eval(*false_branch)
                } else {
                    Ok(Expr::Null)
                }
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

    fn eval_cond(&mut self, clauses: Vec<Expr>) -> Result<Expr, EvalError> {
        for clause in clauses {
            match clause {
                Expr::Cons(condition, cdr) => {
                    if get_bool(self.eval(*condition)?) {
                        return self.eval(*cdr);
                    }
                }
                _ => return Err(EvalError::IllegalCondClause),
            }
        }
        Ok(Expr::Null)
    }

    fn eval_do(
        &mut self,
        vars: Vec<DoVariable>,
        test: Expr,
        body: Expr,
    ) -> Result<Expr, EvalError> {
        self.push_scope();
        for var in &vars {
            self.push_var((*var.ident).to_string(), var.init.clone())?;
        }

        #[allow(unused_assignments)]
        let mut res = Expr::Null;

        loop {
            match test {
                Expr::Cons(ref condition, ref final_) => {
                    if get_bool(self.eval(*condition.clone())?) {
                        res = self.eval(*final_.clone())?;
                        break;
                    }
                }
                _ => todo!(),
            }

            self.push_scope();

            let _ = self.eval(body.clone())?;

            self.pop_scope();

            for var in &vars {
                let stepped = self.eval(var.step.clone())?;
                self.update_var(&var.ident, stepped)?;
            }
        }

        self.pop_scope();
        Ok(res)
    }

    pub fn eval(&mut self, expr: Expr) -> Result<Expr, EvalError> {
        match expr {
            Expr::Atom(Atom::Ident(i)) => self.get_variable(&i),
            Expr::Atom(_) | Expr::Null | Expr::Lambda(_, _) | Expr::If(_, _, _) => Ok(expr),
            Expr::Cons(car, cdr) => self.eval_cons(*car, *cdr),
            Expr::Cond(clauses) => self.eval_cond(clauses),
            Expr::Do(vars, test, body) => self.eval_do(vars, *test, *body),
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

    macro_rules! bol {
        ($b:expr) => {
            Expr::Atom(Atom::Bool($b))
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
        eval_many!(
            "(define my-lambda (lambda () 10)) (my-lambda)",
            vec![Expr::Null, num!(10)]
        );
        eval_many!(
            "(define my-lambda (lambda (x) x)) (my-lambda 10)",
            vec![Expr::Null, num!(10)]
        );
    }

    #[test]
    fn eq() {
        eval!("(= 1 1)", bol!(true));
        eval!("(= 1 2)", bol!(false));
        eval!("(= 1 1 1 1 1)", bol!(true));
        eval!("(= 1 2 3 4 5)", bol!(false));
        eval!("(= 1 (- 2 1))", bol!(true));
        eval!("(= 1 (- 1 2))", bol!(false));
    }

    #[test]
    fn less() {
        eval!("(< 1 1)", bol!(false));
        eval!("(< 1 2)", bol!(true));
        eval!("(< 1 1 1 1 1)", bol!(false));
        eval!("(< 1 2 3 4 5)", bol!(true));
        eval!("(< 1 (- 2 1))", bol!(false));
        eval!("(< 1 (- 1 2))", bol!(false));
    }

    #[test]
    fn greater() {
        eval!("(> 1 1)", bol!(false));
        eval!("(> 1 2)", bol!(false));
        eval!("(> 2 1)", bol!(true));
        eval!("(> 1 1 1 1 1)", bol!(false));
        eval!("(> 5 4 3 2 1)", bol!(true));
        eval!("(> 1 2 3 4 5)", bol!(false));
        eval!("(> 1 (- 2 1))", bol!(false));
        eval!("(> 1 (- 1 2))", bol!(true));
    }

    #[test]
    fn less_or_eq() {
        eval!("(<= 1 1)", bol!(true));
        eval!("(<= 1 2)", bol!(true));
        eval!("(<= 2 1)", bol!(false));
        eval!("(<= 1 1 1 1 1)", bol!(true));
        eval!("(<= 5 4 3 2 1)", bol!(false));
        eval!("(<= 1 2 3 4 5)", bol!(true));
        eval!("(<= 1 (- 2 1))", bol!(true));
        eval!("(<= 1 (- 1 2))", bol!(false));
    }

    #[test]
    fn greater_or_eq() {
        eval!("(>= 1 1)", bol!(true));
        eval!("(>= 1 2)", bol!(false));
        eval!("(>= 2 1)", bol!(true));
        eval!("(>= 1 1 1 1 1)", bol!(true));
        eval!("(>= 5 4 3 2 1)", bol!(true));
        eval!("(>= 1 2 3 4 5)", bol!(false));
        eval!("(>= 1 (- 2 1))", bol!(true));
        eval!("(>= 1 (- 1 2))", bol!(true));
    }

    #[test]
    fn cond() {
        eval!("(cond ((< 1 2) #t) (else #f))", bol!(true));
        eval!("(cond ((< 2 1) #t) (else #f))", bol!(false));
    }

    #[test]
    fn modulo() {
        eval!("(% 8 4 2)", num!(8 % 4 % 2));
        eval!("(% 12834 23)", num!(12834 % 23));
    }
}
