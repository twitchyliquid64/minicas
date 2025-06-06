//! AST types for representing a math formula.
use crate::ty::{Ty, TyValue};
use crate::Path;
use std::fmt;
use std::iter::once;
use std::ops::{Deref, DerefMut};

mod node_const;
pub use node_const::Const;
mod node_binary;
pub use node_binary::{Binary, BinaryOp, CmpOp};
mod node_unary;
pub use node_unary::{Unary, UnaryOp};
mod node_variable;
pub use node_variable::Var;
mod node_piecewise;
pub use node_piecewise::Piecewise;

mod parse;

mod ac_collect;
pub use ac_collect::{ac_collect, AcError};
mod fold;
pub use fold::fold;
mod typecheck;
pub use typecheck::{typecheck, TypeError};
mod rearrange;
pub use rearrange::make_subject;

/// Errors that can occur when evaluating an AST.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EvalError {
    DivByZero,
    NonInteger,
    UnexpectedType(Vec<Ty>),
    UnknownIdent(String),
    Multiple,
    UnboundedInterval,
    IndeterminatePredicate,
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

impl<S: AsRef<str>> EvalContext for Vec<(S, TyValue)> {
    fn resolve_var(&self, id: &str) -> Option<&TyValue> {
        for (ident, val) in self {
            if ident.as_ref() == id {
                return Some(val);
            }
        }
        None
    }
}

/// [EvalContext] variant for integer arithmetic.
pub trait EvalContextInterval {
    fn resolve_var(&self, id: &str) -> Option<(&TyValue, &TyValue)>;
}

impl EvalContextInterval for () {
    fn resolve_var(&self, _id: &str) -> Option<(&TyValue, &TyValue)> {
        None
    }
}

impl<S: AsRef<str>> EvalContextInterval for Vec<(S, (TyValue, TyValue))> {
    fn resolve_var(&self, id: &str) -> Option<(&TyValue, &TyValue)> {
        for (ident, val) in self {
            if ident.as_ref() == id {
                return Some((&val.0, &val.1));
            }
        }
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
    /// Evaluates all possible values of the AST.
    fn eval<C: EvalContext>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = Result<TyValue, EvalError>> + '_>, EvalError>;
    /// Interval variant of [AstNode::eval].
    fn eval_interval<C: EvalContextInterval>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = Result<(TyValue, TyValue), EvalError>> + '_>, EvalError>;

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
    /// Returns the mutable [NodeInner] described by the given path sequence.
    ///
    /// Each entry describes where to branch when recursively fetching
    /// the referenced node. A value of 0 means the left-hand side or unary
    /// operand, and a value of 1 means the right-hand side operand.
    fn get_mut<I: Iterator<Item = usize>>(&mut self, i: I) -> Option<&mut NodeInner>;

    /// Returns whether the operator is left-associative, and its precedence.
    ///
    /// None is returned if precedence is unambiguous.
    fn parsing_precedence(&self) -> Option<(bool, usize)>;
}

/// High-level type representing any node.
///
/// Wraps a [NodeInner].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    fn eval<C: EvalContext>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = Result<TyValue, EvalError>> + '_>, EvalError> {
        self.n.eval(ctx)
    }
    fn eval_interval<C: EvalContextInterval>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = Result<(TyValue, TyValue), EvalError>> + '_>, EvalError>
    {
        self.n.eval_interval(ctx)
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
    fn get_mut<I: Iterator<Item = usize>>(&mut self, mut i: I) -> Option<&mut NodeInner> {
        self.n.get_mut(&mut i)
    }
    fn parsing_precedence(&self) -> Option<(bool, usize)> {
        self.n.parsing_precedence()
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

            ParseNode::Abs(operand) => {
                let i = Node::try_from(*operand)?;
                Ok(NodeInner::Unary(Unary::abs(i)).into())
            }
            ParseNode::Unary { op, operand } => {
                let i = Node::try_from(*operand)?;
                match op {
                    "-" => Ok(NodeInner::Unary(Unary::negate(i)).into()),
                    _ => Err(format!("unknown unary op {}", op)),
                }
            }

            ParseNode::Root(operand, base) => {
                let o = Node::try_from(*operand)?;
                let b = Node::try_from(*base)?;
                Ok(NodeInner::Binary(Binary::root(o, b)).into())
            }
            ParseNode::Pow(l, r) => {
                let l = Node::try_from(*l)?;
                let r = Node::try_from(*r)?;
                Ok(NodeInner::Binary(Binary::pow(l, r)).into())
            }
            ParseNode::Min(l, r) => {
                let l = Node::try_from(*l)?;
                let r = Node::try_from(*r)?;
                Ok(NodeInner::Binary(Binary::min(l, r)).into())
            }
            ParseNode::Max(l, r) => {
                let l = Node::try_from(*l)?;
                let r = Node::try_from(*r)?;
                Ok(NodeInner::Binary(Binary::max(l, r)).into())
            }
            ParseNode::Binary { op, lhs, rhs } => {
                let (l, r) = (Node::try_from(*lhs)?, Node::try_from(*rhs)?);
                match op {
                    "-" => Ok(NodeInner::Binary(Binary::sub(l, r)).into()),
                    "+" => Ok(NodeInner::Binary(Binary::add(l, r)).into()),
                    "±" => Ok(NodeInner::Binary(Binary::plus_or_minus(l, r)).into()),
                    "*" => Ok(NodeInner::Binary(Binary::mul(l, r)).into()),
                    "/" => Ok(NodeInner::Binary(Binary::div(l, r)).into()),
                    "==" => Ok(NodeInner::Binary(Binary::equals(l, r)).into()),
                    "<" => Ok(NodeInner::Binary(Binary::lt(l, r)).into()),
                    "<=" => Ok(NodeInner::Binary(Binary::lte(l, r)).into()),
                    ">" => Ok(NodeInner::Binary(Binary::gt(l, r)).into()),
                    ">=" => Ok(NodeInner::Binary(Binary::gte(l, r)).into()),
                    _ => Err(format!("unknown binary op {}", op)),
                }
            }
            ParseNode::Piecewise { arms, otherwise } => {
                let otherwise = Node::try_from(*otherwise)?;
                Ok(NodeInner::from(Piecewise::new(
                    arms.into_iter()
                        .map(|(e, c)| Ok((Node::try_from(*e)?.into(), Node::try_from(*c)?.into())))
                        .collect::<Result<Vec<_>, String>>()?,
                    otherwise.into(),
                ))
                .into())
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

/// A [Node] on the heap.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    fn eval<C: EvalContext>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = Result<TyValue, EvalError>> + '_>, EvalError> {
        self.0.eval(ctx)
    }
    fn eval_interval<C: EvalContextInterval>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = Result<(TyValue, TyValue), EvalError>> + '_>, EvalError>
    {
        self.0.eval_interval(ctx)
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
    fn get_mut<I: Iterator<Item = usize>>(&mut self, i: I) -> Option<&mut NodeInner> {
        self.0.get_mut(i)
    }
    fn parsing_precedence(&self) -> Option<(bool, usize)> {
        self.0.parsing_precedence()
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

/// Concrete varieties of a node which together compose an AST.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeInner {
    /// Some constant value, like a coefficient or offset.
    Const(Const),
    /// An operation which takes a single operand.
    Unary(Unary),
    /// An operation which takes two operands.
    Binary(Binary),
    /// Some unknown value.
    Var(Var),
    /// A piecewise function.
    Piecewise(Piecewise),
}

impl NodeInner {
    /// Creates a new constant node with the given value.
    pub fn new_const<V: Into<TyValue>>(v: V) -> Self {
        Self::Const(Const::new(v.into()))
    }
    /// Creates a new variable node with the given identifier.
    pub fn new_var<S: Into<String>>(ident: S) -> Self {
        Self::Var(Var::new_untyped(ident))
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
                (Self::Piecewise(p), idx) => {
                    let num_branches = p.r#if.len();
                    if idx == num_branches * 2 {
                        p.r#else.n.get(i)
                    } else if idx < num_branches * 2 {
                        if idx % 2 == 1 {
                            p.r#if[idx / 2].1.n.get(i)
                        } else {
                            p.r#if[idx / 2].0.n.get(i)
                        }
                    } else {
                        None
                    }
                }
                _ => None,
            },
            None => Some(self),
        }
    }

    /// Returns the mutable [NodeInner] described by the given path sequence.
    ///
    /// Each entry describes where to branch when recursively fetching
    /// the referenced node. A value of 0 means the left-hand side or unary
    /// operand, and a value of 1 means the right-hand side operand.
    fn get_mut<I: Iterator<Item = usize>>(&mut self, i: &mut I) -> Option<&mut NodeInner> {
        match i.next() {
            Some(idx) => match (self, idx) {
                (Self::Unary(u), 0) => (*u.operand_mut()).n.get_mut(i),
                (Self::Binary(b), 0) => (*b.lhs_mut()).n.get_mut(i),
                (Self::Binary(b), 1) => (*b.rhs_mut()).n.get_mut(i),
                (Self::Piecewise(p), idx) => {
                    let num_branches = p.r#if.len();
                    if idx == num_branches * 2 {
                        p.r#else.n.get_mut(i)
                    } else if idx < num_branches * 2 {
                        if idx % 2 == 1 {
                            p.r#if[idx / 2].1.n.get_mut(i)
                        } else {
                            p.r#if[idx / 2].0.n.get_mut(i)
                        }
                    } else {
                        None
                    }
                }
                _ => None,
            },
            None => Some(self),
        }
    }

    /// Returns a neatly-formatted string representation of the AST.
    pub fn pretty_str(&self, parent_precedence: Option<usize>) -> String {
        match self {
            Self::Const(c) => format!("{}", c),
            Self::Unary(u) => u.pretty_str(parent_precedence),
            Self::Binary(b) => b.pretty_str(parent_precedence),
            Self::Var(v) => format!("{}", v),
            Self::Piecewise(p) => format!("{}", p),
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
            Self::Piecewise(p) => p.returns(),
        }
    }

    fn descendant_types(&self) -> impl Iterator<Item = Option<Ty>> {
        match self {
            Self::Const(_) | Self::Var(_) | Self::Piecewise(_) => {
                [None, None].into_iter().flatten()
            }
            Self::Unary(u) => [Some(u.operand().returns()), None].into_iter().flatten(),
            Self::Binary(b) => [Some(b.lhs().returns()), Some(b.lhs().returns())]
                .into_iter()
                .flatten(),
        }
    }
    fn finite_eval<C: EvalContext>(&self, ctx: &C) -> Result<TyValue, EvalError> {
        match self {
            Self::Const(c) => Ok(c.value().clone()),
            Self::Unary(u) => u.finite_eval(ctx),
            Self::Binary(b) => b.finite_eval(ctx),
            Self::Piecewise(p) => p.finite_eval(ctx),
            Self::Var(v) => match ctx.resolve_var(v.ident()) {
                Some(v) => Ok(v.clone()),
                None => Err(EvalError::UnknownIdent(v.ident().to_string())),
            },
        }
    }
    fn eval<C: EvalContext>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = Result<TyValue, EvalError>> + '_>, EvalError> {
        match self {
            Self::Const(c) => Ok(Box::new(once(Ok(c.value().clone())))),
            Self::Unary(u) => u.eval(ctx),
            Self::Binary(b) => b.eval(ctx),
            Self::Piecewise(p) => p.eval(ctx),
            Self::Var(v) => match ctx.resolve_var(v.ident()) {
                Some(v) => Ok(Box::new(once(Ok(v.clone())))),
                None => Err(EvalError::UnknownIdent(v.ident().to_string())),
            },
        }
    }
    fn eval_interval<C: EvalContextInterval>(
        &self,
        ctx: &C,
    ) -> Result<Box<dyn Iterator<Item = Result<(TyValue, TyValue), EvalError>> + '_>, EvalError>
    {
        match self {
            Self::Const(c) => Ok(Box::new(once(Ok((c.value().clone(), c.value().clone()))))),
            Self::Unary(u) => u.eval_interval(ctx),
            Self::Binary(b) => b.eval_interval(ctx),
            Self::Piecewise(p) => p.eval_interval(ctx),
            Self::Var(v) => match ctx.resolve_var(v.ident()) {
                Some((v_min, v_max)) => Ok(Box::new(once(Ok((v_min.clone(), v_max.clone()))))),
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
            Self::Piecewise(p) => {
                for (e, p) in p.iter_branches() {
                    e.walk(depth_first, cb);
                    p.walk(depth_first, cb)
                }
                p.else_branch().walk(depth_first, cb);
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
            Self::Piecewise(p) => {
                for (e, p) in p.iter_branches_mut() {
                    e.walk_mut(depth_first, cb);
                    p.walk_mut(depth_first, cb)
                }
                p.else_branch_mut().walk_mut(depth_first, cb);
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
            Self::Const(_) | Self::Var(_) | Self::Piecewise(_) => {
                [None, None].into_iter().flatten()
            }
            Self::Unary(u) => [Some(&u.operand().0.n), None].into_iter().flatten(),
            Self::Binary(b) => [Some(&b.lhs().0.n), Some(&b.rhs().0.n)]
                .into_iter()
                .flatten(),
        }
    }

    fn get<I: Iterator<Item = usize>>(&self, mut i: I) -> Option<&NodeInner> {
        NodeInner::get(self, &mut i)
    }
    fn get_mut<I: Iterator<Item = usize>>(&mut self, mut i: I) -> Option<&mut NodeInner> {
        NodeInner::get_mut(self, &mut i)
    }
    fn parsing_precedence(&self) -> Option<(bool, usize)> {
        match self {
            Self::Const(_) | Self::Var(_) | Self::Piecewise(_) => None,
            Self::Unary(u) => u.op.parsing_precedence(),
            Self::Binary(b) => b.op.parsing_precedence(),
        }
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
impl From<Piecewise> for NodeInner {
    fn from(p: Piecewise) -> Self {
        Self::Piecewise(p)
    }
}
impl From<Node> for NodeInner {
    fn from(n: Node) -> Self {
        Self::from(n.n)
    }
}

impl fmt::Display for NodeInner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.pretty_str(None))
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
            Node::try_from("3 > 5"),
            Ok(Node::new(
                Binary::gt::<TyValue, TyValue>(3.into(), 5.into()).into()
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

        assert_eq!(
            Node::try_from("x ± 4 * y"),
            Ok(Node::new(
                Binary::plus_or_minus::<HN, HN>(
                    Node::new(Var::new_untyped("x").into()).into(),
                    Node::new(
                        Binary::mul::<TyValue, HN>(
                            4.into(),
                            Node::new(Var::new_untyped("y").into()).into(),
                        )
                        .into()
                    )
                    .into(),
                )
                .into()
            )),
        );

        assert_eq!(
            Node::try_from("sqrt(4)"),
            Ok(Node::new(
                Binary::root::<TyValue, TyValue>(4.into(), 2.into(),).into()
            )),
        );
        assert_eq!(
            Node::try_from("root(8, 3)"),
            Ok(Node::new(
                Binary::root::<TyValue, TyValue>(8.into(), 3.into(),).into()
            )),
        );
    }

    #[test]
    fn parse_piecewise() {
        assert_eq!(
            Node::try_from("{2x if x == 0; otherwise x}"),
            Ok(Node::new(NodeInner::from(Piecewise::new(
                vec![(
                    Node::try_from("2x").unwrap().into(),
                    Node::try_from("x == 0").unwrap().into(),
                )],
                Node::try_from("x").unwrap().into(),
            )))),
        );
    }

    #[test]
    fn fmt_basic() {
        assert_eq!(
            "3 * (a + b)",
            format!(
                "{}",
                Node::new(
                    Binary::mul::<TyValue, HN>(
                        3.into(),
                        Node::new(
                            Binary::add::<HN, HN>(
                                Node::new(Var::new_untyped("a").into()).into(),
                                Node::new(Var::new_untyped("b").into()).into(),
                            )
                            .into()
                        )
                        .into(),
                    )
                    .into()
                )
            )
        );
        assert_eq!(
            "(a + b) * 3",
            format!(
                "{}",
                Node::new(
                    Binary::mul::<HN, TyValue>(
                        Node::new(
                            Binary::add::<HN, HN>(
                                Node::new(Var::new_untyped("a").into()).into(),
                                Node::new(Var::new_untyped("b").into()).into(),
                            )
                            .into()
                        )
                        .into(),
                        3.into(),
                    )
                    .into()
                )
            )
        );
        assert_eq!(
            "3 + a * b",
            format!(
                "{}",
                Node::new(
                    Binary::add::<TyValue, HN>(
                        3.into(),
                        Node::new(
                            Binary::mul::<HN, HN>(
                                Node::new(Var::new_untyped("a").into()).into(),
                                Node::new(Var::new_untyped("b").into()).into(),
                            )
                            .into()
                        )
                        .into(),
                    )
                    .into()
                )
            )
        );
        assert_eq!(
            "a * b + 3",
            format!(
                "{}",
                Node::new(
                    Binary::add::<HN, TyValue>(
                        Node::new(
                            Binary::mul::<HN, HN>(
                                Node::new(Var::new_untyped("a").into()).into(),
                                Node::new(Var::new_untyped("b").into()).into(),
                            )
                            .into()
                        )
                        .into(),
                        3.into(),
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
        assert_eq!(
            "3 ± x",
            format!(
                "{}",
                Node::new(
                    Binary::plus_or_minus::<TyValue, HN>(
                        3.into(),
                        Node::new(Var::new_untyped("x").into()).into(),
                    )
                    .into()
                )
            )
        );

        assert_eq!(
            "3 - (-5)",
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
            "3 - |5|",
            format!(
                "{}",
                Node::new(
                    Binary::sub::<TyValue, HN>(
                        3.into(),
                        Node::new(Unary::abs::<TyValue>(5.into()).into()).into(),
                    )
                    .into()
                )
            )
        );

        assert_eq!(
            "{2x if x == 0; otherwise x}",
            format!(
                "{}",
                Node::new(NodeInner::from(Piecewise::new(
                    vec![(
                        Node::try_from("2x").unwrap().into(),
                        Node::try_from("x == 0").unwrap().into(),
                    )],
                    Node::try_from("x").unwrap().into(),
                )))
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
            Node::try_from("root(8, 3) + sqrt(4)")
                .unwrap()
                .finite_eval(&()),
            Ok(4.into()),
        );
        assert_eq!(
            Node::try_from("min(2 + 1, max(4, 2))")
                .unwrap()
                .finite_eval(&()),
            Ok(3.into()),
        );

        assert_eq!(
            Node::try_from("x").unwrap().finite_eval(&()),
            Err(EvalError::UnknownIdent("x".to_string()))
        );
        assert_eq!(
            Node::try_from("x")
                .unwrap()
                .finite_eval(&vec![("x", 69.into())]),
            Ok(69.into()),
        );
    }

    #[test]
    fn finite_eval_piecewise() {
        assert_eq!(
            Node::try_from("{x if x > y; otherwise y}")
                .unwrap()
                .finite_eval(&vec![("x", 42.into()), ("y", 4.into())]),
            Ok(42.into()),
        );
        assert_eq!(
            Node::try_from("{x if x > y; otherwise y}")
                .unwrap()
                .finite_eval(&vec![("x", 1.into()), ("y", 4.into())]),
            Ok(4.into()),
        );
    }

    #[test]
    fn eval_simple() {
        assert_eq!(
            Node::try_from("3.5 + 4.5")
                .unwrap()
                .eval(&())
                .unwrap()
                .collect::<Result<Vec<_>, _>>(),
            Ok(vec![8.into()]),
        );
        assert_eq!(
            Node::try_from("9 - 3 * 2")
                .unwrap()
                .eval(&())
                .unwrap()
                .collect::<Result<Vec<_>, _>>(),
            Ok(vec![3.into()]),
        );

        assert_eq!(
            Node::try_from("5 ± 1")
                .unwrap()
                .eval(&())
                .unwrap()
                .collect::<Result<Vec<_>, _>>(),
            Ok(vec![6.into(), 4.into()]),
        );
        assert_eq!(
            Node::try_from("2 * (5 ± 1)")
                .unwrap()
                .eval(&())
                .unwrap()
                .collect::<Result<Vec<_>, _>>(),
            Ok(vec![12.into(), 8.into()]),
        );

        assert_eq!(
            Node::try_from("-{0±x if x > y; otherwise y}")
                .unwrap()
                .eval(&vec![("x", 2.into()), ("y", 1.into())])
                .unwrap()
                .collect::<Result<Vec<_>, _>>(),
            Ok(vec![(-2).into(), 2.into()]),
        );
    }

    #[test]
    fn interval_eval() {
        assert_eq!(
            Node::try_from("x - 2y")
                .unwrap()
                .eval_interval(&vec![
                    ("x", (1.into(), 2.into())),
                    ("y", (5.into(), 6.into()))
                ])
                .unwrap()
                .collect::<Result<Vec<_>, _>>(),
            Ok(vec![((-11).into(), (-8).into())]),
        );

        // Smoke test over a large range
        for x in -8..=8 {
            for y in -8..=8 {
                assert!(
                    Node::try_from("sqrt(pow(-2 - x, 2) + pow(3 - y, 2)) + abs(x+y)")
                        .unwrap()
                        .eval_interval(&vec![
                            ("x", (x.into(), (x + 2).into())),
                            ("y", (y.into(), (y + 2).into())),
                        ])
                        .unwrap()
                        .collect::<Result<Vec<_>, _>>()
                        .is_ok(),
                );
            }
        }
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

        // Piecewise
        let p: Node = NodeInner::from(Piecewise::new(
            vec![(
                Node::try_from("x").unwrap().into(),
                Node::try_from("x == 0").unwrap().into(),
            )],
            Node::try_from("0").unwrap().into(),
        ))
        .into();
        assert_eq!(p.get(vec![99].into_iter()), None);
        assert_eq!(
            p.get(vec![0].into_iter()),
            Some(Node::try_from("x").unwrap().as_inner()),
        );
        assert_eq!(
            p.get(vec![1].into_iter()),
            Some(Node::try_from("x == 0").unwrap().as_inner()),
        );
        assert_eq!(
            p.get(vec![2].into_iter()),
            Some(Node::try_from("0").unwrap().as_inner()),
        );
    }
}
