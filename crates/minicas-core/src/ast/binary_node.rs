use crate::ast::{AstNode, EvalError, HN};
use crate::{Ty, TyValue};
use std::fmt;

/// BinaryOp enumerates the types of binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    /// Binary addition
    Add,
    /// Binary subtraction
    Sub,
}

impl BinaryOp {
    /// Returns true if the given type is valid as an operand to this node.
    pub fn descendant_compatible(&self, ty: Ty) -> bool {
        use BinaryOp::*;
        use Ty::*;
        match (self, ty) {
            (Add | Sub, Rational) => true,
            (Add | Sub, Bool) => false,
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BinaryOp::*;
        match self {
            Add => write!(f, "+"),
            Sub => write!(f, "-"),
        }
    }
}

/// AST object representing an operation over two operands.
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct Binary {
    op: BinaryOp,
    lhs: HN,
    rhs: HN,
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

    /// Returns the type of the value execution yields.
    pub fn returns(&self) -> Ty {
        use BinaryOp::*;
        match self.op {
            Add => self.lhs.returns(),
            Sub => self.lhs.returns(),
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
    pub fn finite_eval(&self) -> Result<TyValue, EvalError> {
        use BinaryOp::*;
        match self.op {
            Add => match (self.lhs.finite_eval()?, self.rhs.finite_eval()?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l + r)),
                _ => Err(()),
            },
            Sub => match (self.lhs.finite_eval()?, self.rhs.finite_eval()?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l - r)),
                _ => Err(()),
            },
        }
    }
}

impl fmt::Display for Binary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BinaryOp::*;
        match self.op {
            Add | Sub => write!(f, "{} {} {}", self.lhs, self.op, self.rhs),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_finite_eval() {
        assert_eq!(
            Binary::add::<TyValue, TyValue>(2usize.into(), 3usize.into()).finite_eval(),
            Ok((5usize).into())
        );
    }
    #[test]
    fn sub_finite_eval() {
        assert_eq!(
            Binary::sub::<TyValue, TyValue>(2usize.into(), 3usize.into()).finite_eval(),
            Ok((-1isize).into())
        );
    }
}
