//! AST types for representing a math formula.
use std::fmt;
use std::ops::{Deref, DerefMut};

use crate::ty::{Ty, TyValue};

mod const_node;
pub use const_node::Const;
mod binary_node;
pub use binary_node::{Binary, BinaryOp};
mod unary_node;
pub use unary_node::{Unary, UnaryOp};

// TODO: Real error type
pub type EvalError = ();

pub trait AstNode: Clone + Sized + std::fmt::Debug {
    /// Returns the type of the value this node yields.
    fn returns(&self) -> Ty;
    /// Returns the types of the operands of this node.
    fn descendant_types(&self) -> impl Iterator<Item = Ty>;
    /// Attempts to evaluate the AST to a single finite value.
    fn finite_eval(&self) -> Result<TyValue, EvalError>;

    /// Recursively executes the given function on every node in the AST.
    /// The walk will end early if the given function returns false.
    fn walk(&self, cb: &mut impl FnMut(&NodeInner) -> bool);
}

/// High-level type representing any node.
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct Node {
    n: NodeInner,
}

impl Node {
    pub fn new(n: NodeInner) -> Self {
        Self { n }
    }
}

impl AstNode for Node {
    fn returns(&self) -> Ty {
        self.n.returns()
    }
    fn descendant_types(&self) -> impl Iterator<Item = Ty> {
        self.n.descendant_types()
    }
    fn finite_eval(&self) -> Result<TyValue, EvalError> {
        self.n.finite_eval()
    }
    fn walk(&self, cb: &mut impl FnMut(&NodeInner) -> bool) {
        self.n.walk(cb)
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.n, f)
    }
}

/// High-level type representing a node on the heap.
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct HN(Box<Node>);

impl HN {
    pub fn new(n: Node) -> HN {
        HN(Box::new(n))
    }

    pub fn make(n: NodeInner) -> HN {
        Self::new(Node { n })
    }

    /// Move out of the heap.
    /// Intended for chaining transformations not covered by `map`.
    pub fn and_then<F>(self, f: F) -> Node
    where
        F: FnOnce(Node) -> Node,
    {
        f(*self.0)
    }

    /// Produce a new `HN` from `self` without reallocating.
    pub fn map<F>(mut self, f: F) -> Self
    where
        F: FnOnce(Node) -> Node,
    {
        let x = f(*self.0);
        *self.0 = x;

        self
    }

    /// Replaces the inner node.
    pub fn replace_with(&mut self, n: Node) {
        *self.0 = n;
    }
    pub fn swap(&mut self, n: Node) -> Node {
        std::mem::replace(&mut self.0, n)
    }
}

impl AstNode for HN {
    fn returns(&self) -> Ty {
        self.0.returns()
    }
    fn descendant_types(&self) -> impl Iterator<Item = Ty> {
        self.0.descendant_types()
    }
    fn finite_eval(&self) -> Result<TyValue, EvalError> {
        self.0.finite_eval()
    }
    fn walk(&self, cb: &mut impl FnMut(&NodeInner) -> bool) {
        self.0.walk(cb)
    }
}

impl Deref for HN {
    type Target = Node;

    fn deref(&self) -> &Node {
        &self.0
    }
}

impl DerefMut for HN {
    fn deref_mut(&mut self) -> &mut Node {
        &mut self.0
    }
}

impl From<Node> for HN {
    fn from(n: Node) -> Self {
        Self(Box::new(n))
    }
}

impl From<NodeInner> for HN {
    fn from(n: NodeInner) -> Self {
        Self(Box::new(Node { n }))
    }
}

impl From<TyValue> for HN {
    fn from(v: TyValue) -> Self {
        let n = Const::new(v).into();
        Self(Box::new(Node { n }))
    }
}

impl fmt::Display for HN {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

/// NodeInner enumerates the varieties of node.
#[derive(Debug, Clone, PartialEq, Hash)]
pub enum NodeInner {
    /// Some constant value, like a coefficient or offset.
    Const(Const),
    /// An operation which takes a single operand.
    Unary(Unary),
    /// An operation which takes two operands.
    Binary(Binary),
}

impl NodeInner {
    /// Returns a ref to the inner [Const] if this node is that variant.
    pub fn as_const(&self) -> Option<&Const> {
        match self {
            Self::Const(c) => Some(c),
            _ => None,
        }
    }
    /// Returns a ref to the inner [Unary] if this node is that variant.
    pub fn as_unary(&self) -> Option<&Unary> {
        match self {
            Self::Unary(c) => Some(c),
            _ => None,
        }
    }
    /// Returns a ref to the inner [Binary] if this node is that variant.
    pub fn as_binary(&self) -> Option<&Binary> {
        match self {
            Self::Binary(b) => Some(b),
            _ => None,
        }
    }
}

impl AstNode for NodeInner {
    fn returns(&self) -> Ty {
        match self {
            Self::Const(c) => c.returns(),
            Self::Unary(u) => u.returns(),
            Self::Binary(b) => b.returns(),
        }
    }

    fn descendant_types(&self) -> impl Iterator<Item = Ty> {
        match self {
            Self::Const(_) => [None, None].into_iter().flatten(),
            Self::Unary(u) => [Some(u.operand().returns()), None].into_iter().flatten(),
            Self::Binary(b) => [Some(b.lhs().returns()), Some(b.lhs().returns())]
                .into_iter()
                .flatten(),
        }
    }
    fn finite_eval(&self) -> Result<TyValue, EvalError> {
        match self {
            Self::Const(c) => Ok(c.value()),
            Self::Unary(u) => u.finite_eval(),
            Self::Binary(b) => b.finite_eval(),
        }
    }

    fn walk(&self, cb: &mut impl FnMut(&NodeInner) -> bool) {
        if !cb(self) {
            return;
        }

        // recurse to sub-expressions
        match self {
            Self::Unary(u) => {
                u.operand().walk(cb);
            }
            Self::Binary(b) => {
                b.lhs().walk(cb);
                b.rhs().walk(cb);
            }

            // nothing contained to walk
            Self::Const(_) => {}
        }
    }
}

impl From<Const> for NodeInner {
    fn from(n: Const) -> Self {
        Self::Const(n)
    }
}
impl From<Unary> for NodeInner {
    fn from(n: Unary) -> Self {
        Self::Unary(n)
    }
}

impl fmt::Display for NodeInner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Const(c) => fmt::Display::fmt(c, f),
            Self::Unary(u) => fmt::Display::fmt(u, f),
            Self::Binary(b) => fmt::Display::fmt(b, f),
        }
    }
}
