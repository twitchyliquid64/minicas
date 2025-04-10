use crate::ast::{AstNode, EvalContext, EvalContextInterval, EvalError, HN};
use crate::{Ty, TyValue};
use std::fmt;

/// UnaryOp enumerates the types of unary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Negate,
    Abs,
}

impl UnaryOp {
    /// Returns true if the given type is valid as an operand for this operation.
    pub fn descendant_compatible(&self, ty: Option<Ty>) -> bool {
        use Ty::*;
        use UnaryOp::*;
        match (self, ty) {
            (Negate, Some(Bool) | Some(Rational) | None) => true,
            (Abs, Some(Rational) | None) => true,
            (Abs, Some(Bool)) => false,
        }
    }

    /// Returns whether the operator is left-associative, and its precedence.
    ///
    /// None is returned if precedence is unambiguous.
    pub fn parsing_precedence(&self) -> Option<(bool, usize)> {
        use UnaryOp::*;
        match self {
            Negate => Some((true, 1)),
            Abs => None,
        }
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use UnaryOp::*;
        match self {
            Negate => write!(f, "-"),
            Abs => write!(f, "abs"),
        }
    }
}

/// AST object representing an operation over a single operand.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    /// Constructs a new absolute value node.
    pub fn abs<V: Into<HN>>(operand: V) -> Self {
        Self {
            op: UnaryOp::Abs,
            val: operand.into(),
        }
    }

    /// Returns the type of the value execution yields.
    pub fn returns(&self) -> Option<Ty> {
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
    /// Returns a mutable reference to the operand.
    pub fn operand_mut(&mut self) -> &mut HN {
        return &mut self.val;
    }

    /// Computes a single finite solution, if possible.
    pub fn finite_eval<C: EvalContext>(&self, ctx: &C) -> Result<TyValue, EvalError> {
        use UnaryOp::*;
        match self.op {
            Negate => match self.val.finite_eval(ctx)? {
                TyValue::Rational(r) => Ok(TyValue::Rational(-r)),
                TyValue::Bool(b) => Ok(TyValue::Bool(!b)),
            },
            Abs => {
                use num::Signed;
                match self.val.finite_eval(ctx)? {
                    TyValue::Rational(r) => Ok(TyValue::Rational(r.abs())),
                    TyValue::Bool(_) => Err(EvalError::UnexpectedType(vec![Ty::Bool])),
                }
            }
        }
    }

    pub fn eval<C: EvalContext>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = Result<TyValue, EvalError>> + '_>, EvalError> {
        use UnaryOp::*;
        let iter = self.val.eval(ctx)?;
        Ok(Box::new(iter.map(|v| match self.op {
            Negate => match v {
                Ok(TyValue::Rational(r)) => Ok(TyValue::Rational(-r)),
                Ok(TyValue::Bool(b)) => Ok(TyValue::Bool(!b)),
                Err(e) => Err(e),
            },
            Abs => {
                use num::Signed;
                match v {
                    Ok(TyValue::Rational(r)) => Ok(TyValue::Rational(r.abs())),
                    Ok(TyValue::Bool(_)) => Err(EvalError::UnexpectedType(vec![Ty::Bool])),
                    Err(e) => Err(e),
                }
            }
        })))
    }

    pub fn eval_interval<C: EvalContextInterval>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = (TyValue, TyValue)> + '_>, EvalError> {
        use UnaryOp::*;
        let iter = self.val.eval_interval(ctx)?;
        Ok(Box::new(iter.map(|(min, max)| match self.op {
            Negate => match (min, max) {
                (TyValue::Rational(min), TyValue::Rational(max)) => {
                    (TyValue::Rational(-max), TyValue::Rational(-min))
                }
                _ => unreachable!(),
            },
            Abs => {
                use num::Signed;
                match (min, max) {
                    (TyValue::Rational(min), TyValue::Rational(max)) => {
                        use num::rational::BigRational;
                        let zero = BigRational::from_integer(0.into());

                        if min >= zero {
                            // already correct
                            (TyValue::Rational(min), TyValue::Rational(max))
                        } else if max < zero {
                            (TyValue::Rational(-max), TyValue::Rational(-min))
                        } else {
                            (0.into(), TyValue::Rational(min.abs().max(max.abs())))
                        }
                    }
                    _ => unreachable!(),
                }
            }
        })))
    }

    pub(crate) fn pretty_str(&self, parent_precedence: Option<usize>) -> String {
        match self.op.parsing_precedence() {
            Some((_left_assoc, prec)) => {
                let tmp = match self.op {
                    UnaryOp::Negate => format!("{}{}", self.op, self.val.pretty_str(Some(prec))),
                    _ => unreachable!(),
                };

                if let Some(parent_precedence) = parent_precedence {
                    if parent_precedence > prec {
                        return format!("({})", tmp);
                    }
                }
                tmp
            }
            None => match self.op {
                UnaryOp::Abs => format!("|{}|", self.val.pretty_str(None)),
                _ => unreachable!(),
            },
        }
    }
}

impl fmt::Display for Unary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_str(None))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn negate_finite_eval() {
        assert_eq!(
            Unary::negate(TyValue::Bool(true)).finite_eval(&()),
            Ok(TyValue::Bool(false))
        );
        assert_eq!(
            Unary::negate::<TyValue>(2usize.into()).finite_eval(&()),
            Ok((-2isize).into())
        );
    }

    #[test]
    fn abs_finite_eval() {
        assert_eq!(
            Unary::abs(TyValue::from(-3)).finite_eval(&()),
            Ok(TyValue::from(3))
        );
        assert_eq!(
            Unary::abs(TyValue::from(3)).finite_eval(&()),
            Ok(TyValue::from(3))
        );
    }
}
