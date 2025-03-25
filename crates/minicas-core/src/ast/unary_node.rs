use crate::ast::{AstNode, EvalError, HN};
use crate::{Ty, TyValue};
use std::fmt;

/// UnaryOp enumerates the types of unary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Negate,
}

impl UnaryOp {
    /// Returns true if the given type is valid as an operand to this node.
    pub fn descendant_compatible(&self, ty: Ty) -> bool {
        use Ty::*;
        use UnaryOp::*;
        match (self, ty) {
            (Negate, Bool | Rational) => true,
        }
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use UnaryOp::*;
        match self {
            Negate => write!(f, "-"),
        }
    }
}

/// AST object representing an operation over a single operand.
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct Unary {
    pub op: UnaryOp,
    pub val: HN,
}

impl Unary {
    /// Constructs a new unary node.
    pub fn new<V: Into<HN>>(op: UnaryOp, operand: V) -> Self {
        Self {
            op,
            val: operand.into(),
        }
    }
    /// Constructs a new negation node.
    pub fn negate<V: Into<HN>>(operand: V) -> Self {
        Self {
            op: UnaryOp::Negate,
            val: operand.into(),
        }
    }

    /// Returns the type of the value execution yields.
    pub fn returns(&self) -> Ty {
        return self.val.returns();
    }

    /// Returns the unary operation this node represents.
    pub fn op(&self) -> UnaryOp {
        return self.op;
    }

    /// Returns a reference to the operand.
    pub fn operand(&self) -> &HN {
        return &self.val;
    }

    /// Computes a single finite solution, if possible.
    pub fn finite_eval(&self) -> Result<TyValue, EvalError> {
        use UnaryOp::*;
        match self.op {
            Negate => match self.val.finite_eval()? {
                TyValue::Rational(r) => Ok(TyValue::Rational(-r)),
                TyValue::Bool(b) => Ok(TyValue::Bool(!b)),
            },
        }
    }
}

impl fmt::Display for Unary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use UnaryOp::*;
        match self.op {
            Negate => write!(f, "-{}", self.val),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn negate_finite_eval() {
        assert_eq!(
            Unary::negate(TyValue::Bool(true)).finite_eval(),
            Ok(TyValue::Bool(false))
        );
        assert_eq!(
            Unary::negate::<TyValue>(2usize.into()).finite_eval(),
            Ok((-2isize).into())
        );
    }
}
