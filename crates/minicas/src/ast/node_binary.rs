use crate::ast::{AstNode, EvalContext, EvalError, NodeInner, HN};
use crate::{Ty, TyValue};
use num::CheckedDiv;
use std::fmt;

/// CmpOp enumerations binary operations which compare values.
///
/// A contained bool indicates if the comparison is inclusive:
/// i.e. `LessThan(true)` means less than or equal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CmpOp {
    Equals,
    LessThan(bool),
    GreaterThan(bool),
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
    /// Returns true if the given not-None types are valid as operands for this operation.
    pub fn descendant_compatible(&self, lhs: Option<Ty>, rhs: Option<Ty>) -> bool {
        use BinaryOp::*;
        use Ty::*;
        match (self, lhs, rhs) {
            (Add | Sub | Mul | Div, Some(Rational) | None, Some(Rational) | None) => true,
            (Add | Sub | Mul | Div, _, _) => false,
            (Cmp(CmpOp::Equals), Some(Rational) | None, Some(Rational) | None) => true,
            (Cmp(CmpOp::Equals), Some(Bool) | None, Some(Bool) | None) => true,
            (Cmp(CmpOp::Equals), _, _) => false,
            (Cmp(CmpOp::LessThan(_)), Some(Rational) | None, Some(Rational) | None) => true,
            (Cmp(CmpOp::LessThan(_)), _, _) => false,
            (Cmp(CmpOp::GreaterThan(_)), Some(Rational) | None, Some(Rational) | None) => true,
            (Cmp(CmpOp::GreaterThan(_)), _, _) => false,
        }
    }

    /// Returns whether the operator is left-associative, and its precedence.
    ///
    /// None is returned if precedence is unambiguous.
    pub fn parsing_precedence(&self) -> Option<(bool, usize)> {
        use BinaryOp::*;
        match self {
            Add => Some((true, 2)),
            Sub => Some((true, 2)),
            Mul => Some((true, 3)),
            Div => Some((true, 3)),
            Cmp(CmpOp::Equals) => Some((true, 4)),
            Cmp(CmpOp::LessThan(_)) => Some((true, 4)),
            Cmp(CmpOp::GreaterThan(_)) => Some((true, 4)),
        }
    }

    /// Returns true if the operation is associative, or false otherwise.
    pub fn associative(&self) -> bool {
        use BinaryOp::*;
        match self {
            Add | Mul => true,
            _ => false,
        }
    }

    /// Returns true if the operation is commutative, or false otherwise.
    pub fn commutative(&self) -> bool {
        use BinaryOp::*;
        match self {
            Add | Mul => true,
            _ => false,
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
            Cmp(CmpOp::LessThan(false)) => write!(f, "<"),
            Cmp(CmpOp::LessThan(true)) => write!(f, "<="),
            Cmp(CmpOp::GreaterThan(false)) => write!(f, ">"),
            Cmp(CmpOp::GreaterThan(true)) => write!(f, ">="),
        }
    }
}

/// AST object representing an operation over two operands.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    /// Constructs a new less-than node.
    pub fn lt<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Cmp(CmpOp::LessThan(false)),
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }
    /// Constructs a new less-than-or-equal node.
    pub fn lte<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Cmp(CmpOp::LessThan(true)),
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }
    /// Constructs a new greater-than node.
    pub fn gt<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Cmp(CmpOp::GreaterThan(false)),
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }
    /// Constructs a new greater-than-or-equal node.
    pub fn gte<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Cmp(CmpOp::GreaterThan(true)),
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
            Cmp(CmpOp::LessThan(_)) => Some(Ty::Bool),
            Cmp(CmpOp::GreaterThan(_)) => Some(Ty::Bool),
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
    /// Returns a mutable reference to the left operand.
    pub fn lhs_mut(&mut self) -> &mut HN {
        return &mut self.lhs;
    }
    /// Returns a mutable reference to the right operand.
    pub fn rhs_mut(&mut self) -> &mut HN {
        return &mut self.rhs;
    }

    /// Computes a single finite solution, if possible.
    pub fn finite_eval<C: EvalContext>(&self, c: &C) -> Result<TyValue, EvalError> {
        use BinaryOp::*;
        match self.op {
            Add => match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l + r)),
                (lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),
            },
            Sub => match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l - r)),
                (lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),
            },
            Mul => match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l * r)),
                (lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),
            },
            Div => match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => match l.checked_div(&r) {
                    Some(o) => Ok(TyValue::Rational(o)),
                    None => Err(EvalError::DivByZero),
                },
                (lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),
            },

            Cmp(CmpOp::Equals) => match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Bool(l == r)),
                (TyValue::Bool(l), TyValue::Bool(r)) => Ok(TyValue::Bool(l == r)),
                (lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),
            },
            Cmp(CmpOp::LessThan(false)) => {
                match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                    (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Bool(l < r)),
                    (lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),
                }
            }
            Cmp(CmpOp::LessThan(true)) => {
                match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                    (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Bool(l <= r)),
                    (lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),
                }
            }
            Cmp(CmpOp::GreaterThan(false)) => {
                match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                    (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Bool(l > r)),
                    (lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),
                }
            }
            Cmp(CmpOp::GreaterThan(true)) => {
                match (self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?) {
                    (TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Bool(l >= r)),
                    (lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),
                }
            }
        }
    }

    pub(crate) fn pretty_str(&self, parent_precedence: Option<usize>) -> String {
        // Special-case: multiplication of coefficient and variable
        if self.op == BinaryOp::Mul {
            if let (NodeInner::Const(c), NodeInner::Var(v)) = (&**self.lhs, &**self.rhs) {
                return format!("{}{}", c, v);
            }
        }

        match self.op.parsing_precedence() {
            Some((left_assoc, prec)) => {
                let left_needs_parens = match (self.lhs.parsing_precedence(), left_assoc) {
                    (None, _) => false,
                    (Some((_, _lhs_prec)), false) => todo!(),
                    (Some((_, lhs_prec)), true) => lhs_prec < prec,
                };
                let right_needs_parens = match (self.rhs.parsing_precedence(), left_assoc) {
                    (None, _) => false,
                    (Some((_, _rhs_prec)), false) => todo!(),
                    (Some((_, rhs_prec)), true) => rhs_prec < prec,
                };

                let tmp = format!(
                    "{} {} {}",
                    if left_needs_parens {
                        format!("({})", self.lhs.pretty_str(None))
                    } else {
                        self.lhs.pretty_str(Some(prec))
                    },
                    self.op,
                    if right_needs_parens {
                        format!("({})", self.rhs.pretty_str(None))
                    } else {
                        self.rhs.pretty_str(Some(prec))
                    }
                );

                if let Some(parent_precedence) = parent_precedence {
                    if parent_precedence > prec {
                        return format!("({})", tmp);
                    }
                }
                tmp
            }
            None => format!(
                "{} {} {}",
                self.lhs.pretty_str(None),
                self.op,
                self.rhs.pretty_str(None)
            ),
        }
    }
}

impl fmt::Display for Binary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_str(None))
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
    #[test]
    fn lt_finite_eval() {
        assert_eq!(
            Binary::lt::<TyValue, TyValue>(2usize.into(), 3usize.into()).finite_eval(&()),
            Ok(true.into())
        );
        assert_eq!(
            Binary::lt::<TyValue, TyValue>(2usize.into(), 2usize.into()).finite_eval(&()),
            Ok(false.into())
        );
        assert_eq!(
            Binary::lte::<TyValue, TyValue>(2usize.into(), 2usize.into()).finite_eval(&()),
            Ok(true.into())
        );
    }
    #[test]
    fn gt_finite_eval() {
        assert_eq!(
            Binary::gt::<TyValue, TyValue>(3usize.into(), 2usize.into()).finite_eval(&()),
            Ok(true.into())
        );
        assert_eq!(
            Binary::gt::<TyValue, TyValue>(2usize.into(), 2usize.into()).finite_eval(&()),
            Ok(false.into())
        );
        assert_eq!(
            Binary::gte::<TyValue, TyValue>(2usize.into(), 2usize.into()).finite_eval(&()),
            Ok(true.into())
        );
    }
}
