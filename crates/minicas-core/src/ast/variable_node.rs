use crate::Ty;
use std::fmt;

/// AST object representing some unknown value.
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct Var {
    pub id: String,
    pub ty: Option<Ty>,
}

impl Var {
    /// Constructs a new variable node with an unknown type.
    pub fn new_untyped<V: Into<String>>(identifier: V) -> Self {
        Self {
            id: identifier.into(),
            ty: None,
        }
    }

    /// Constructs a new variable node with the specified type.
    pub fn new_with_type<V: Into<String>>(identifier: V, ty: Ty) -> Self {
        Self {
            id: identifier.into(),
            ty: Some(ty),
        }
    }

    /// Returns the type of the constant value.
    pub fn returns(&self) -> Option<Ty> {
        self.ty
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.id, f)
    }
}
