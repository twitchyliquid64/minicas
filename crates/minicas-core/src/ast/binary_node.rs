use crate::ast::{AstNode, EvalContext, EvalError, HN};
use crate::{Ty, TyValue};
use num::CheckedDiv;
use std::fmt;

/// CmpOp enumerations binary operations which compare values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CmpOp {
    Equals,
}

/// BinaryOp enumerates the types of binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    /// Binary addition
    Add,
    /// Binary subtraction
    Sub,
    /// Binary Multiplication
    Mul,
    /// Binary Division
    Div,
    /// Some kind of comparison
    Cmp(CmpOp),
}

impl BinaryOp {
    /// Returns true if the given type is valid as an operand to this node.
    pub fn descendant_compatible(&self, lhs: Option<Ty>, rhs: Option<Ty>) -> bool {
        use BinaryOp::*;
        use Ty::*;
        match (self, lhs, rhs) {
            (Add | Sub | Mul | Div, Some(Rational) | None, Some(Rational) | None) => true,
            (Add | Sub | Mul | Div, _, _) => false,
            (Cmp(CmpOp::Equals), Some(Rational) | None, Some(Rational) | None) => true,
            (Cmp(CmpOp::Equals), Some(Bool) | None, Some(Bool) | None) => true,
            (Cmp(CmpOp::Equals), _, _) => false,
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BinaryOp::*;
        match self {
            Add => write!(f, "+"),
            Sub => write!(f, "-"),
            Mul => write!(f, "*"),
            Div => write!(f, "/"),
            Cmp(CmpOp::Equals) => write!(f, "=="),
        }
    }
}

/// AST object representing an operation over two operands.
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct Binary {
    pub op: BinaryOp,
    pub lhs: HN,
    pub rhs: HN,
}

impl Binary {
    /// Constructs a new binary node for the specified operation.
    pub fn new<V1: Into<HN>, V2: Into<HN>>(op: BinaryOp, lhs: V1, rhs: V2) -> Self {
        Self {
            op,
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }
    /// Constructs a new addition node.
    pub fn add<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Add,
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }
    /// Constructs a new subtraction node.
    pub fn sub<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Sub,
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }
    /// Constructs a new multiplication node.
    pub fn mul<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Mul,
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }
    /// Constructs a new division node.
    pub fn div<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Div,
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }
    /// Constructs a new equals node.
    pub fn equals<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Cmp(CmpOp::Equals),
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }

    /// Returns the type of the value execution yields.
    pub fn returns(&self) -> Option<Ty> {
        use BinaryOp::*;
        match self.op {
            Add => self.lhs.returns(),
            Sub => self.lhs.returns(),
            Mul => self.lhs.returns(),
            Div => self.lhs.returns(),
            Cmp(CmpOp::Equals) => Some(Ty::Bool),
        }
    }

    /// Returns the binary operation this node represents.
    pub fn op(&self) -> BinaryOp {
        return self.op;
    }

    /// Returns a reference to the left operand.
    pub fn lhs(&self) -> &HN {
        return &self.lhs;
    }
    /// Returns a reference to the right operand.
    pub fn rhs(&self) -> &HN {
        return &self.rhs;
    }

    /// Computes a single finite solution, if possible.
    pub fn finite_eval<C: EvalContext>(&self, c: &C) -> Result<TyValue, EvalError> {
        use BinaryOp::*;
        match self.op {
            Add => match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l + r)),
                (lv, rv) => Err(EvalError::UnexpectedType(lv.ty(), rv.ty())),
            },
            Sub => match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l - r)),
                (lv, rv) => Err(EvalError::UnexpectedType(lv.ty(), rv.ty())),
            },
            Mul => match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l * r)),
                (lv, rv) => Err(EvalError::UnexpectedType(lv.ty(), rv.ty())),
            },
            Div => match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => match l.checked_div(&r) {
                    Some(o) => Ok(TyValue::Rational(o)),
                    None => Err(EvalError::DivByZero),
                },
                (lv, rv) => Err(EvalError::UnexpectedType(lv.ty(), rv.ty())),
            },
            Cmp(CmpOp::Equals) => match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Bool(l == r)),
                (TyValue::Bool(l), TyValue::Bool(r)) => Ok(TyValue::Bool(l == r)),
                (lv, rv) => Err(EvalError::UnexpectedType(lv.ty(), rv.ty())),
            },
        }
    }
}

impl fmt::Display for Binary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BinaryOp::*;
        match self.op {
            Add | Sub | Mul | Div => write!(f, "{} {} {}", self.lhs, self.op, self.rhs),
            Cmp(CmpOp::Equals) => write!(f, "{} {} {}", self.lhs, self.op, self.rhs),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_finite_eval() {
        assert_eq!(
            Binary::add::<TyValue, TyValue>(2usize.into(), 3usize.into()).finite_eval(&()),
            Ok((5usize).into())
        );
    }
    #[test]
    fn sub_finite_eval() {
        assert_eq!(
            Binary::sub::<TyValue, TyValue>(2usize.into(), 3usize.into()).finite_eval(&()),
            Ok((-1isize).into())
        );
    }
    #[test]
    fn mul_finite_eval() {
        assert_eq!(
            Binary::mul::<TyValue, TyValue>(2usize.into(), 3usize.into()).finite_eval(&()),
            Ok((6usize).into())
        );
    }
    #[test]
    fn div_finite_eval() {
        assert_eq!(
            Binary::div::<TyValue, TyValue>(4usize.into(), 2usize.into()).finite_eval(&()),
            Ok((2usize).into())
        );
        assert_eq!(
            Binary::div::<TyValue, TyValue>(4usize.into(), 0usize.into()).finite_eval(&()),
            Err(EvalError::DivByZero)
        );
    }
    #[test]
    fn eq_finite_eval() {
        assert_eq!(
            Binary::equals::<TyValue, TyValue>(2usize.into(), 3usize.into()).finite_eval(&()),
            Ok(false.into())
        );
        assert_eq!(
            Binary::equals::<TyValue, TyValue>(2usize.into(), 2usize.into()).finite_eval(&()),
            Ok(true.into())
        );
    }
}
