use crate::ast::{AstNode, EvalContext, EvalContextInterval, EvalError, HN};
use crate::{Ty, TyValue};
use std::fmt;

/// AST object representing a piecewise expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Piecewise {
    pub r#if: Vec<(HN, HN)>,
    pub r#else: HN,
}

impl Piecewise {
    /// Constructs a new piecewise expression.
    pub fn new(r#if: Vec<(HN, HN)>, r#else: HN) -> Self {
        Self { r#if, r#else }
    }

    /// Returns the type of the constant value.
    pub fn returns(&self) -> Option<Ty> {
        self.r#else.returns()
    }

    /// Iterates over the conditional branches of the piecewise function.
    pub fn iter_branches(&self) -> impl Iterator<Item = &(HN, HN)> {
        self.r#if.iter()
    }

    /// Mutably iterates over the conditional branches of the piecewise function.
    pub fn iter_branches_mut(&mut self) -> impl Iterator<Item = &mut (HN, HN)> {
        self.r#if.iter_mut()
    }

    /// Returns a reference to the otherwise path of the expression.
    pub fn else_branch(&self) -> &HN {
        &self.r#else
    }
    /// Returns a mutable reference to the otherwise path of the expression.
    pub fn else_branch_mut(&mut self) -> &mut HN {
        &mut self.r#else
    }

    /// Computes a single finite solution, if possible.
    pub fn finite_eval<C: EvalContext>(&self, c: &C) -> Result<TyValue, EvalError> {
        for (e, cond) in self.r#if.iter() {
            match cond.finite_eval(c)? {
                TyValue::Bool(true) => {
                    return e.finite_eval(c);
                }
                TyValue::Bool(false) => {}
                v => {
                    return Err(EvalError::UnexpectedType(vec![v.ty()]));
                }
            }
        }
        self.r#else.finite_eval(c)
    }

    pub fn eval<C: EvalContext>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = TyValue> + '_>, EvalError> {
        for (e, cond) in self.r#if.iter() {
            match cond.finite_eval(ctx)? {
                TyValue::Bool(true) => {
                    return e.eval(ctx);
                }
                TyValue::Bool(false) => {}
                v => {
                    return Err(EvalError::UnexpectedType(vec![v.ty()]));
                }
            }
        }
        self.r#else.eval(ctx)
    }

    pub fn eval_interval<C: EvalContextInterval>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = (TyValue, TyValue)> + '_>, EvalError> {
        for (e, cond) in self.r#if.iter() {
            match cond.eval_interval(ctx)?.next().unwrap().0 {
                TyValue::Bool(true) => {
                    return e.eval_interval(ctx);
                }
                TyValue::Bool(false) => {}
                v => {
                    return Err(EvalError::UnexpectedType(vec![v.ty()]));
                }
            }
        }
        self.r#else.eval_interval(ctx)
    }
}

impl fmt::Display for Piecewise {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (e, cond) in self.r#if.iter() {
            write!(f, "{} if {}; ", e, cond)?;
        }

        write!(f, "otherwise {}}}", self.r#else)
    }
}
