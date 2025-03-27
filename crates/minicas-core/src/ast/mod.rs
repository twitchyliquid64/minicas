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
mod variable_node;
pub use variable_node::Var;

mod parse;

mod fold;
pub use fold::fold;
mod typecheck;
pub use typecheck::{typecheck, TypeError};

/// Errors that can occur when evaluating an AST.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EvalError {
    DivByZero,
    UnexpectedType(Ty, Ty),
    UnknownIdent(String),
}

/// Context that needs to be provided for evaluation.
pub trait EvalContext {
    fn resolve_var(&self, id: &str) -> Option<&TyValue>;
}

impl EvalContext for () {
    fn resolve_var(&self, _id: &str) -> Option<&TyValue> {
        None
    }
}

pub trait AstNode: Clone + Sized + std::fmt::Debug {
    /// Returns the type of the value this node yields.
    fn returns(&self) -> Option<Ty>;
    /// Returns the types of the operands of this node.
    fn descendant_types(&self) -> impl Iterator<Item = Option<Ty>>;
    /// Attempts to evaluate the AST to a single finite value.
    fn finite_eval<C: EvalContext>(&self, ctx: &C) -> Result<TyValue, EvalError>;

    /// Recursively executes the given function on every node in the AST.
    /// The walk will end early if the given function returns false and
    /// the invocation was not depth first.
    fn walk(&self, depth_first: bool, cb: &mut impl FnMut(&NodeInner) -> bool);
    /// Recursively executes the given function on every node in the AST.
    /// The walk will end early if the given function returns false and
    /// the invocation was not depth first.
    fn walk_mut(&mut self, depth_first: bool, cb: &mut impl FnMut(&mut NodeInner) -> bool);

    /// Returns the concrete variant this AST node represents.
    fn as_inner(&self) -> &NodeInner;
    /// Iterates through the child nodes of this node.
    fn iter_children(&self) -> impl Iterator<Item = &NodeInner>;

    /// Returns the nested child described by the given sequence.
    ///
    /// Each entry describes where to branch when recursively fetching
    /// the referenced node. A value of 0 means the left-hand side or unary
    /// operand, and a value of 1 means the right-hand side operand.
    fn get<I: Iterator<Item = usize>>(&self, i: I) -> Option<&NodeInner>;
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
    fn returns(&self) -> Option<Ty> {
        self.n.returns()
    }
    fn descendant_types(&self) -> impl Iterator<Item = Option<Ty>> {
        self.n.descendant_types()
    }
    fn finite_eval<C: EvalContext>(&self, ctx: &C) -> Result<TyValue, EvalError> {
        self.n.finite_eval(ctx)
    }
    fn walk(&self, depth_first: bool, cb: &mut impl FnMut(&NodeInner) -> bool) {
        self.n.walk(depth_first, cb)
    }
    fn walk_mut(&mut self, depth_first: bool, cb: &mut impl FnMut(&mut NodeInner) -> bool) {
        self.n.walk_mut(depth_first, cb)
    }
    fn as_inner(&self) -> &NodeInner {
        self.n.as_inner()
    }
    fn iter_children(&self) -> impl Iterator<Item = &NodeInner> {
        self.n.iter_children()
    }
    fn get<I: Iterator<Item = usize>>(&self, mut i: I) -> Option<&NodeInner> {
        self.n.get(&mut i)
    }
}

impl Deref for Node {
    type Target = NodeInner;

    fn deref(&self) -> &NodeInner {
        &self.n
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.n, f)
    }
}

impl From<NodeInner> for Node {
    fn from(n: NodeInner) -> Self {
        Self { n }
    }
}

impl<'a> TryFrom<parse::ParseNode<'a>> for Node {
    type Error = String;

    fn try_from(n: parse::ParseNode<'a>) -> Result<Self, Self::Error> {
        use parse::ParseNode;
        match n {
            ParseNode::Bool(b) => Ok(NodeInner::Const(b.into()).into()),
            ParseNode::Int(i) => Ok(NodeInner::Const(i.into()).into()),
            ParseNode::Float(f) => {
                Ok(NodeInner::Const((num::rational::Ratio::from_float(f).unwrap()).into()).into())
            }

            ParseNode::Ident(i) => Ok(NodeInner::Var(Var::new_untyped(i)).into()),
            // TODO: Should probably somehow represent that this is a coefficient, and hence
            // can only be a numeric quantity (vs say a boolean)
            ParseNode::IdentWithCoefficient(co_eff, i) => Ok(NodeInner::Binary(Binary::mul(
                NodeInner::Const(co_eff.into()),
                NodeInner::Var(Var::new_untyped(i)),
            ))
            .into()),

            ParseNode::Unary { op, operand } => {
                let i = Node::try_from(*operand)?;
                match op {
                    "-" => Ok(NodeInner::Unary(Unary::negate(i)).into()),
                    _ => Err(format!("unknown unary op {}", op)),
                }
            }
            ParseNode::Binary { op, lhs, rhs } => {
                let (l, r) = (Node::try_from(*lhs)?, Node::try_from(*rhs)?);
                match op {
                    "-" => Ok(NodeInner::Binary(Binary::sub(l, r)).into()),
                    "+" => Ok(NodeInner::Binary(Binary::add(l, r)).into()),
                    "*" => Ok(NodeInner::Binary(Binary::mul(l, r)).into()),
                    "/" => Ok(NodeInner::Binary(Binary::div(l, r)).into()),
                    "==" => Ok(NodeInner::Binary(Binary::equals(l, r)).into()),
                    _ => Err(format!("unknown binary op {}", op)),
                }
            }
        }
    }
}

impl<'a> TryFrom<&'a str> for Node {
    type Error = String;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        match parse::parse(s) {
            Ok((_, pn)) => Node::try_from(pn),
            Err(e) => Err(format!("parse err: {}", e)),
        }
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
    fn returns(&self) -> Option<Ty> {
        self.0.returns()
    }
    fn descendant_types(&self) -> impl Iterator<Item = Option<Ty>> {
        self.0.descendant_types()
    }
    fn finite_eval<C: EvalContext>(&self, ctx: &C) -> Result<TyValue, EvalError> {
        self.0.finite_eval(ctx)
    }
    fn walk(&self, depth_first: bool, cb: &mut impl FnMut(&NodeInner) -> bool) {
        self.0.walk(depth_first, cb)
    }
    fn walk_mut(&mut self, depth_first: bool, cb: &mut impl FnMut(&mut NodeInner) -> bool) {
        self.0.walk_mut(depth_first, cb)
    }
    fn as_inner(&self) -> &NodeInner {
        self.0.as_inner()
    }
    fn iter_children(&self) -> impl Iterator<Item = &NodeInner> {
        self.0.iter_children()
    }
    fn get<I: Iterator<Item = usize>>(&self, i: I) -> Option<&NodeInner> {
        self.0.get(i)
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
    /// Some unknown value.
    Var(Var),
}

impl NodeInner {
    pub fn new_const<V: Into<TyValue>>(v: V) -> Self {
        Self::Const(Const::new(v.into()))
    }

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
    /// Returns a ref to the inner [Var] if this node is that variant.
    pub fn as_var(&self) -> Option<&Var> {
        match self {
            Self::Var(b) => Some(b),
            _ => None,
        }
    }

    /// Returns the nested child described by the given sequence.
    ///
    /// Each entry describes where to branch when recursively fetching
    /// the referenced node. A value of 0 means the left-hand side or unary
    /// operand, and a value of 1 means the right-hand side operand.
    fn get<I: Iterator<Item = usize>>(&self, i: &mut I) -> Option<&NodeInner> {
        match i.next() {
            Some(idx) => match (self, idx) {
                (Self::Unary(u), 0) => (*u.operand()).n.get(i),
                (Self::Binary(b), 0) => (*b.lhs()).n.get(i),
                (Self::Binary(b), 1) => (*b.rhs()).n.get(i),
                _ => None,
            },
            None => Some(self),
        }
    }
}

impl AstNode for NodeInner {
    fn returns(&self) -> Option<Ty> {
        match self {
            Self::Const(c) => Some(c.returns()),
            Self::Unary(u) => u.returns(),
            Self::Binary(b) => b.returns(),
            Self::Var(v) => v.returns(),
        }
    }

    fn descendant_types(&self) -> impl Iterator<Item = Option<Ty>> {
        match self {
            Self::Const(_) | Self::Var(_) => [None, None].into_iter().flatten(),
            Self::Unary(u) => [Some(u.operand().returns()), None].into_iter().flatten(),
            Self::Binary(b) => [Some(b.lhs().returns()), Some(b.lhs().returns())]
                .into_iter()
                .flatten(),
        }
    }
    fn finite_eval<C: EvalContext>(&self, ctx: &C) -> Result<TyValue, EvalError> {
        match self {
            Self::Const(c) => Ok(c.value()),
            Self::Unary(u) => u.finite_eval(ctx),
            Self::Binary(b) => b.finite_eval(ctx),
            Self::Var(v) => match ctx.resolve_var(v.ident()) {
                Some(v) => Ok(v.clone()),
                None => Err(EvalError::UnknownIdent(v.ident().to_string())),
            },
        }
    }

    fn walk(&self, depth_first: bool, cb: &mut impl FnMut(&NodeInner) -> bool) {
        if !depth_first {
            if !cb(self) {
                return;
            }
        }

        // recurse to sub-expressions
        match self {
            Self::Unary(u) => {
                u.operand().walk(depth_first, cb);
            }
            Self::Binary(b) => {
                b.lhs().walk(depth_first, cb);
                b.rhs().walk(depth_first, cb);
            }

            // nothing contained to walk
            Self::Const(_) | Self::Var(_) => {}
        }

        if depth_first {
            if !cb(self) {
                return;
            }
        }
    }
    fn walk_mut(&mut self, depth_first: bool, cb: &mut impl FnMut(&mut NodeInner) -> bool) {
        if !depth_first {
            if !cb(self) {
                return;
            }
        }

        // recurse to sub-expressions
        match self {
            Self::Unary(u) => {
                u.operand_mut().walk_mut(depth_first, cb);
            }
            Self::Binary(b) => {
                b.lhs_mut().walk_mut(depth_first, cb);
                b.rhs_mut().walk_mut(depth_first, cb);
            }

            // nothing contained to walk
            Self::Const(_) | Self::Var(_) => {}
        }

        if depth_first {
            if !cb(self) {
                return;
            }
        }
    }

    fn as_inner(&self) -> &NodeInner {
        self
    }

    fn iter_children(&self) -> impl Iterator<Item = &NodeInner> {
        match self {
            Self::Const(_) | Self::Var(_) => [None, None].into_iter().flatten(),
            Self::Unary(u) => [Some(&u.operand().0.n), None].into_iter().flatten(),
            Self::Binary(b) => [Some(&b.lhs().0.n), Some(&b.rhs().0.n)]
                .into_iter()
                .flatten(),
        }
    }

    fn get<I: Iterator<Item = usize>>(&self, mut i: I) -> Option<&NodeInner> {
        NodeInner::get(self, &mut i)
    }
}

impl From<Const> for NodeInner {
    fn from(n: Const) -> Self {
        Self::Const(n)
    }
}
impl From<Binary> for NodeInner {
    fn from(n: Binary) -> Self {
        Self::Binary(n)
    }
}
impl From<Unary> for NodeInner {
    fn from(n: Unary) -> Self {
        Self::Unary(n)
    }
}
impl From<Var> for NodeInner {
    fn from(n: Var) -> Self {
        Self::Var(n)
    }
}

impl fmt::Display for NodeInner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Const(c) => fmt::Display::fmt(c, f),
            Self::Unary(u) => fmt::Display::fmt(u, f),
            Self::Binary(b) => fmt::Display::fmt(b, f),
            Self::Var(v) => fmt::Display::fmt(v, f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_basic() {
        assert_eq!(
            Node::try_from("3 + 5"),
            Ok(Node::new(
                Binary::add::<TyValue, TyValue>(3.into(), 5.into()).into()
            )),
        );
        assert_eq!(
            Node::try_from("-5"),
            Ok(Node::new(Unary::negate::<TyValue>(5.into()).into())),
        );
        assert_eq!(
            Node::try_from("3--5"),
            Ok(Node::new(
                Binary::sub::<TyValue, HN>(
                    3.into(),
                    Node::new(Unary::negate::<TyValue>(5.into()).into()).into(),
                )
                .into()
            )),
        );
        assert_eq!(
            Node::try_from("3==5"),
            Ok(Node::new(
                Binary::equals::<TyValue, TyValue>(3.into(), 5.into()).into()
            )),
        );
        assert_eq!(
            Node::try_from("5x"),
            Ok(Node::new(
                Binary::mul::<TyValue, HN>(
                    5.into(),
                    Node::new(Var::new_untyped("x").into()).into()
                )
                .into()
            )),
        );
    }

    #[test]
    fn fmt_basic() {
        assert_eq!(
            "3 - -5",
            format!(
                "{}",
                Node::new(
                    Binary::sub::<TyValue, HN>(
                        3.into(),
                        Node::new(Unary::negate::<TyValue>(5.into()).into()).into(),
                    )
                    .into()
                )
            )
        );

        assert_eq!(
            "3 - x",
            format!(
                "{}",
                Node::new(
                    Binary::sub::<TyValue, HN>(
                        3.into(),
                        Node::new(Var::new_untyped("x").into()).into(),
                    )
                    .into()
                )
            )
        );
    }

    #[test]
    fn finite_eval_simple() {
        assert_eq!(
            Node::try_from("3.5 + 4.5").unwrap().finite_eval(&()),
            Ok(8.into()),
        );
        assert_eq!(
            Node::try_from("3 - 5").unwrap().finite_eval(&()),
            Ok((-2).into()),
        );
        assert_eq!(
            Node::try_from("9 - 3 * 2").unwrap().finite_eval(&()),
            Ok(3.into()),
        );

        assert_eq!(
            Node::try_from("x").unwrap().finite_eval(&()),
            Err(EvalError::UnknownIdent("x".to_string()))
        );
    }

    #[test]
    fn get() {
        assert_eq!(
            Node::try_from("3 + 2*5").unwrap().get(vec![0].into_iter()),
            Some(&NodeInner::new_const(3)),
        );
        assert_eq!(
            Node::try_from("3 + 2*5")
                .unwrap()
                .get(vec![1, 0].into_iter()),
            Some(&NodeInner::new_const(2)),
        );
        assert_eq!(
            Node::try_from("3 + 2*5").unwrap().get(vec![1].into_iter()),
            Some(Node::try_from("2 * 5").unwrap().as_inner()),
        );
        assert_eq!(
            Node::try_from("3 + 2*5").unwrap().get(vec![].into_iter()),
            Some(Node::try_from("3 + 2 * 5").unwrap().as_inner()),
        );

        assert_eq!(
            Node::try_from("3 + 2*5").unwrap().get(vec![99].into_iter()),
            None,
        );
    }
}
