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
    /// Binary plus or minus
    PlusOrMinus,
    /// Binary Multiplication
    Mul,
    /// Binary Division
    Div,
    /// Some kind of comparison
    Cmp(CmpOp),
    /// Power-of some integer
    Pow,
    /// Root of some integer
    Root,
}

impl BinaryOp {
    /// Returns true if the given not-None types are valid as operands for this operation.
    pub fn descendant_compatible(&self, lhs: Option<Ty>, rhs: Option<Ty>) -> bool {
        use BinaryOp::*;
        use Ty::*;
        match (self, lhs, rhs) {
            (Add | Sub | Mul | Div | PlusOrMinus, Some(Rational) | None, Some(Rational) | None) => {
                true
            }
            (Add | Sub | Mul | Div | PlusOrMinus, _, _) => false,
            (Pow | Root, Some(Rational) | None, Some(Rational) | None) => true,
            (Pow | Root, _, _) => false,
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
            PlusOrMinus => Some((true, 2)),
            Mul => Some((true, 3)),
            Div => Some((true, 3)),
            Pow | Root => None,
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
            PlusOrMinus => write!(f, "±"),
            Mul => write!(f, "*"),
            Div => write!(f, "/"),
            Pow => write!(f, "pow"),
            Root => write!(f, "root"),
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
    /// Constructs a new plus-or-minus node.
    pub fn plus_or_minus<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::PlusOrMinus,
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
    /// Constructs a new power-of node.
    pub fn pow<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Pow,
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }
    /// Constructs a new root node.
    pub fn root<V1: Into<HN>, V2: Into<HN>>(lhs: V1, rhs: V2) -> Self {
        Self {
            op: BinaryOp::Root,
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
            PlusOrMinus => self.lhs.returns(),
            Mul => self.lhs.returns(),
            Div => self.lhs.returns(),
            Pow => self.lhs.returns(),
            Root => self.lhs.returns(),
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

    #[inline]
    fn eval_op(op: &BinaryOp, l: TyValue, r: TyValue) -> Result<TyValue, EvalError> {
        use num::ToPrimitive;
        use BinaryOp::*;
        match (op, l, r) {
            (PlusOrMinus, _, _) => Err(EvalError::Multiple),

            (Add, TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l + r)),
            (Add, lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),

            (Sub, TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l - r)),
            (Sub, lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),

            (Mul, TyValue::Rational(l), TyValue::Rational(r)) => Ok(TyValue::Rational(l * r)),
            (Mul, lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),

            (Div, TyValue::Rational(l), TyValue::Rational(r)) => match l.checked_div(&r) {
                Some(o) => Ok(TyValue::Rational(o)),
                None => Err(EvalError::DivByZero),
            },
            (Div, lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),

            (Pow, TyValue::Rational(l), TyValue::Rational(r)) => {
                if r.is_integer() {
                    use num::traits::Pow;
                    Ok(TyValue::Rational(l.pow(r.numer())))
                } else {
                    Err(EvalError::NonInteger)
                }
            }
            (Pow, lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),
            (Root, TyValue::Rational(l), TyValue::Rational(r)) => {
                if r.is_integer() {
                    let res = l.to_f64().unwrap().powf(r.to_f64().unwrap().recip());
                    Ok(res.into())
                } else {
                    Err(EvalError::NonInteger)
                }
            }
            (Root, lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),

            (Cmp(CmpOp::Equals), TyValue::Rational(l), TyValue::Rational(r)) => {
                Ok(TyValue::Bool(l == r))
            }
            (Cmp(CmpOp::Equals), TyValue::Bool(l), TyValue::Bool(r)) => Ok(TyValue::Bool(l == r)),
            (Cmp(CmpOp::Equals), lv, rv) => Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()])),

            (Cmp(CmpOp::LessThan(false)), TyValue::Rational(l), TyValue::Rational(r)) => {
                Ok(TyValue::Bool(l < r))
            }
            (Cmp(CmpOp::LessThan(false)), TyValue::Bool(l), TyValue::Bool(r)) => {
                Ok(TyValue::Bool(l < r))
            }
            (Cmp(CmpOp::LessThan(false)), lv, rv) => {
                Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()]))
            }

            (Cmp(CmpOp::LessThan(true)), TyValue::Rational(l), TyValue::Rational(r)) => {
                Ok(TyValue::Bool(l <= r))
            }
            (Cmp(CmpOp::LessThan(true)), TyValue::Bool(l), TyValue::Bool(r)) => {
                Ok(TyValue::Bool(l <= r))
            }
            (Cmp(CmpOp::LessThan(true)), lv, rv) => {
                Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()]))
            }

            (Cmp(CmpOp::GreaterThan(false)), TyValue::Rational(l), TyValue::Rational(r)) => {
                Ok(TyValue::Bool(l > r))
            }
            (Cmp(CmpOp::GreaterThan(false)), TyValue::Bool(l), TyValue::Bool(r)) => {
                Ok(TyValue::Bool(l > r))
            }
            (Cmp(CmpOp::GreaterThan(false)), lv, rv) => {
                Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()]))
            }

            (Cmp(CmpOp::GreaterThan(true)), TyValue::Rational(l), TyValue::Rational(r)) => {
                Ok(TyValue::Bool(l >= r))
            }
            (Cmp(CmpOp::GreaterThan(true)), TyValue::Bool(l), TyValue::Bool(r)) => {
                Ok(TyValue::Bool(l >= r))
            }
            (Cmp(CmpOp::GreaterThan(true)), lv, rv) => {
                Err(EvalError::UnexpectedType(vec![lv.ty(), rv.ty()]))
            }
        }
    }

    /// Computes a single finite solution, if possible.
    pub fn finite_eval<C: EvalContext>(&self, c: &C) -> Result<TyValue, EvalError> {
        Binary::eval_op(&self.op, self.lhs.finite_eval(c)?, self.rhs.finite_eval(c)?)
    }

    pub fn eval<C: EvalContext>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = TyValue> + '_>, EvalError> {
        let (l, r) = (self.lhs.eval(ctx)?, self.rhs.eval(ctx)?);

        use BinaryOp::*;
        match self.op {
            PlusOrMinus => Ok(Box::new(
                l.zip(r)
                    .map(|(l, r)| match (l, r) {
                        (TyValue::Rational(l), TyValue::Rational(r)) => [
                            TyValue::Rational(l.clone() + r.clone()),
                            TyValue::Rational(l - r),
                        ],
                        _ => unreachable!(),
                    })
                    .flatten(),
            )),

            _ => Ok(Box::new(l.zip(r).map(|(l, r)| {
                match Binary::eval_op(&self.op, l, r) {
                    Ok(v) => v,
                    Err(e) => panic!("{:?}", e),
                }
            }))),
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
                "{}({}, {})",
                self.op,
                self.lhs.pretty_str(None),
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

    #[test]
    fn pow_finite_eval() {
        assert_eq!(
            Binary::pow::<TyValue, TyValue>(2usize.into(), 3usize.into()).finite_eval(&()),
            Ok(8.into())
        );
    }
    #[test]
    fn root_finite_eval() {
        assert_eq!(
            Binary::root::<TyValue, TyValue>(9usize.into(), 2usize.into()).finite_eval(&()),
            Ok(3.into())
        );
        assert_eq!(
            Binary::root::<TyValue, TyValue>(8usize.into(), 3usize.into()).finite_eval(&()),
            Ok(2.into())
        );
    }
}
