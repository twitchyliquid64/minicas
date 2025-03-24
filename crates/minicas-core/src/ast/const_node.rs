use crate::{Ty, TyValue};
use std::fmt;

/// AST object representing some constant value.
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct Const(pub(crate) TyValue);

impl Const {
    /// Constructs a new const node.
    pub fn new<V: Into<TyValue>>(val: V) -> Self {
        Self(val.into())
    }

    /// Returns the type of the constant value.
    pub fn returns(&self) -> Ty {
        return self.0.ty();
    }

    /// Returns the constant value.
    pub fn value(&self) -> TyValue {
        return self.0.clone();
    }
}

impl<T: Into<TyValue>> From<T> for Const {
    fn from(input: T) -> Const {
        Const(input.into())
    }
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}
