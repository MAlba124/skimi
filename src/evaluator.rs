use std::error::Error;

use crate::parser::Expr;

#[derive(Debug)]
pub enum EvalError {}

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

pub struct Evaluator {}

impl Evaluator {
    pub fn new() -> Self {
        Self {}
    }

    pub fn eval(&mut self, _expr: Expr) -> Expr {
        Expr::Null
    }
}
