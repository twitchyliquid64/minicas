use num::{BigRational, FromPrimitive, ToPrimitive};
use std::fmt;

/// The type of some data being computed on.
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash)]
pub enum Ty {
    #[default]
    Rational,
    Bool,
}

impl Ty {
    pub fn all() -> &'static [Ty] {
        &[Ty::Rational, Ty::Bool]
    }

    pub fn make_default(&self) -> TyValue {
        match self {
            Ty::Rational => TyValue::Rational(BigRational::from_usize(0).unwrap()),
            Ty::Bool => TyValue::Bool(false),
        }
    }
}

/// Some constant data and its corresponding type.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum TyValue {
    Rational(BigRational),
    Bool(bool),
}

impl Default for TyValue {
    fn default() -> Self {
        TyValue::Rational(BigRational::from_usize(0).unwrap())
    }
}

impl TyValue {
    pub fn ty(&self) -> Ty {
        match self {
            TyValue::Rational(_) => Ty::Rational,
            TyValue::Bool(_) => Ty::Bool,
        }
    }

    pub fn to_usize(&self) -> Option<usize> {
        match self {
            TyValue::Rational(v) => v.to_usize(),
            _ => None,
        }
    }
    pub fn to_f32(&self) -> Option<f32> {
        match self {
            TyValue::Rational(v) => v.to_f32(),
            _ => None,
        }
    }
    pub fn to_f64(&self) -> Option<f64> {
        match self {
            TyValue::Rational(v) => v.to_f64(),
            _ => None,
        }
    }
}

impl fmt::Display for TyValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TyValue::*;
        match self {
            Rational(v) => write!(f, "{}", v),
            Bool(v) => write!(f, "{}", v),
        }
    }
}

impl From<BigRational> for TyValue {
    fn from(input: BigRational) -> Self {
        TyValue::Rational(input)
    }
}
impl From<usize> for TyValue {
    fn from(input: usize) -> Self {
        TyValue::Rational(BigRational::from_usize(input).unwrap())
    }
}
impl From<isize> for TyValue {
    fn from(input: isize) -> Self {
        TyValue::Rational(BigRational::from_isize(input).unwrap())
    }
}
impl From<f32> for TyValue {
    fn from(input: f32) -> Self {
        TyValue::Rational(BigRational::from_f32(input).unwrap())
    }
}
impl From<f64> for TyValue {
    fn from(input: f64) -> Self {
        TyValue::Rational(BigRational::from_f64(input).unwrap())
    }
}

impl From<bool> for TyValue {
    fn from(input: bool) -> Self {
        TyValue::Bool(input)
    }
}
