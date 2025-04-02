//! Predicate rules/matching for AST nodes.
use crate::ast::{AstNode, BinaryOp, NodeInner, UnaryOp};
use crate::{Path, TyValue};

/// Describes a predicate on the operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PredicateOp {
    Unary(UnaryOp),
    Binary(BinaryOp),
    Piecewise,
    Const,
    Var,
}

impl PredicateOp {
    /// Indicates if the operation matches that of the given [AstNode].
    pub fn matches<N: AstNode>(&self, n: &N) -> bool {
        match (self, n.as_inner()) {
            (Self::Unary(po), NodeInner::Unary(n)) => po.eq(&n.op),
            (Self::Binary(po), NodeInner::Binary(n)) => po.eq(&n.op),
            (Self::Piecewise, NodeInner::Piecewise(_)) => true,
            (Self::Const, NodeInner::Const(_)) => true,
            (Self::Var, NodeInner::Var(_)) => true,
            _ => false,
        }
    }
}

impl TryFrom<&str> for PredicateOp {
    type Error = ();

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "const" => Ok(Self::Const),
            "var" => Ok(Self::Var),
            "piecewise" => Ok(Self::Piecewise),

            "neg" => Ok(Self::Unary(UnaryOp::Negate)),
            "abs" => Ok(Self::Unary(UnaryOp::Abs)),
            "-" => Ok(Self::Binary(BinaryOp::Sub)),
            "+" => Ok(Self::Binary(BinaryOp::Add)),
            "/" => Ok(Self::Binary(BinaryOp::Div)),
            "*" => Ok(Self::Binary(BinaryOp::Mul)),
            _ => Err(()),
        }
    }
}

/// Describes a predicate on an AST node.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Predicate {
    /// Match only on nodes performing the given operation.
    pub op: Option<PredicateOp>,
    /// Match only on nodes which are NOT the given operation.
    pub not_op: Option<PredicateOp>,

    /// Match if the node is a constant with some value.
    pub const_value: Option<TyValue>,

    /// Match if the descendant nodes specified by the two paths are equal.
    pub equivalent: Vec<(Path, Path)>,

    /// Match only on nodes whos children match the given predicates respectively.
    ///
    /// A `None` value in some position means to skip considering the child in that
    /// place, for instance a `[None, Some(...)]` skips evaluation of a first operand.
    pub children: Vec<Option<Self>>,
}

impl Predicate {
    /// Creates a predicate matching only on the specified op.
    pub fn op(op: PredicateOp) -> Self {
        Self {
            op: Some(op),
            ..Default::default()
        }
    }

    /// Creates a predicate matching only the specified children.
    ///
    /// A `None` value in some position means to skip considering the child in that
    /// place, for instance a `[None, Some(...)]` skips evaluation of a first operand.
    pub fn children(children: Vec<Option<Self>>) -> Self {
        Self {
            children,
            ..Default::default()
        }
    }

    /// Indicates if the predicate matches a given [AstNode].
    pub fn matches<N: AstNode>(&self, n: &N) -> bool {
        if !self.op.map(|po| po.matches(n)).unwrap_or(true) {
            return false;
        }
        if self.not_op.map(|po| po.matches(n)).unwrap_or(false) {
            return false;
        }
        match (self.const_value.as_ref(), n.as_inner()) {
            (None, _) => {}
            (Some(v), NodeInner::Const(c)) => {
                if c.value() != v {
                    return false;
                }
            }
            (Some(_), _) => {
                return false;
            }
        }

        for (l, r) in self.equivalent.iter() {
            let (l, r) = (n.get(l.iter()), n.get(r.iter()));
            if let (Some(l), Some(r)) = (l, r) {
                if l != r {
                    return false;
                }
            } else {
                return false;
            }
        }

        if self.children.len() > 0 {
            // TODO: piecewise shouldnt be special-cased, but supported via
            // iter_children() path.
            if let NodeInner::Piecewise(_) = n.as_inner() {
                let all_meets = self.children.iter().enumerate().all(|(i, pc)| {
                    if let Some(pc) = pc {
                        if let Some(c) = n.get(Path::with_next(i).iter()) {
                            pc.matches(c)
                        } else {
                            false
                        }
                    } else {
                        true
                    }
                });
                if !all_meets {
                    return false;
                }
            } else {
                if !self.children.iter().zip(n.iter_children()).all(|(pc, c)| {
                    if let Some(pc) = pc {
                        pc.matches(c)
                    } else {
                        true
                    }
                }) {
                    return false;
                }
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{CmpOp, Node};

    #[test]
    fn predicate_op_matches() {
        assert_eq!(
            PredicateOp::Binary(BinaryOp::Add).matches(&Node::try_from("3 + 5").unwrap()),
            true,
        );
        assert_eq!(
            PredicateOp::Binary(BinaryOp::Add).matches(&Node::try_from("3 - 5").unwrap()),
            false,
        );
        assert_eq!(
            PredicateOp::Binary(BinaryOp::Add).matches(&Node::try_from("-5").unwrap()),
            false,
        );

        assert_eq!(
            PredicateOp::Unary(UnaryOp::Negate).matches(&Node::try_from("-5").unwrap()),
            true,
        );
        assert_eq!(
            PredicateOp::Const.matches(&Node::try_from("-5").unwrap()),
            false,
        );
        assert_eq!(
            PredicateOp::Const.matches(&Node::try_from("5").unwrap()),
            true,
        );
        assert_eq!(
            PredicateOp::Piecewise.matches(&Node::try_from("{otherwise 5}").unwrap()),
            true,
        );
    }

    #[test]
    fn equivalent_matches() {
        assert_eq!(
            Predicate {
                equivalent: vec![(vec![0].into(), vec![1].into())],
                ..Default::default()
            }
            .matches(&Node::try_from("x + x").unwrap()),
            true,
        );
        assert_eq!(
            Predicate {
                equivalent: vec![(vec![0].into(), vec![1].into())],
                ..Default::default()
            }
            .matches(&Node::try_from("x + 2x").unwrap()),
            false,
        );

        assert_eq!(
            Predicate {
                equivalent: vec![(vec![0].into(), vec![1, 0].into())],
                ..Default::default()
            }
            .matches(&Node::try_from("a * (a + 1)").unwrap()),
            true,
        );
    }

    #[test]
    fn children_matches() {
        assert_eq!(
            Predicate {
                children: vec![],
                ..Default::default()
            }
            .matches(&Node::try_from("3 + 5").unwrap()),
            true,
        );
        assert_eq!(
            Predicate {
                children: vec![None, None],
                ..Default::default()
            }
            .matches(&Node::try_from("3 + 5").unwrap()),
            true,
        );

        assert_eq!(
            Predicate {
                op: Some(PredicateOp::Binary(BinaryOp::Add)),
                children: vec![Some(Predicate::op(PredicateOp::Const))],
                ..Default::default()
            }
            .matches(&Node::try_from("3 + 5").unwrap()),
            true,
        );

        assert_eq!(
            Predicate {
                op: Some(PredicateOp::Binary(BinaryOp::Add)),
                children: vec![
                    Some(Predicate::op(PredicateOp::Const)),
                    Some(Predicate::op(PredicateOp::Const))
                ],
                ..Default::default()
            }
            .matches(&Node::try_from("5 + 3 * 4").unwrap()),
            false,
        );
        assert_eq!(
            Predicate {
                op: Some(PredicateOp::Binary(BinaryOp::Add)),
                children: vec![
                    Some(Predicate::op(PredicateOp::Const)),
                    Some(Predicate::op(PredicateOp::Binary(BinaryOp::Mul))),
                ],
                ..Default::default()
            }
            .matches(&Node::try_from("5 + 3 * 4").unwrap()),
            true,
        );
        assert_eq!(
            Predicate {
                children: vec![Some(Predicate::op(PredicateOp::Const)), None],
                ..Default::default()
            }
            .matches(&Node::try_from("5 + 3 * 5").unwrap()),
            true,
        );

        assert_eq!(
            Predicate {
                children: vec![Some(Predicate::op(PredicateOp::Unary(UnaryOp::Negate)))],
                ..Default::default()
            }
            .matches(&Node::try_from("3 + 5").unwrap()),
            false,
        );
        assert_eq!(
            Predicate {
                children: vec![Some(Predicate::op(PredicateOp::Unary(UnaryOp::Negate)))],
                ..Default::default()
            }
            .matches(&Node::try_from("-3 + 5").unwrap()),
            true,
        );

        // Test matching piecewise function arms / else case
        assert_eq!(
            Predicate {
                children: vec![Some(Predicate::op(PredicateOp::Unary(UnaryOp::Negate)))],
                ..Default::default()
            }
            .matches(&Node::try_from("{otherwise -2}").unwrap()),
            true,
        );
        assert_eq!(
            Predicate {
                children: vec![
                    Some(Predicate::op(PredicateOp::Const)),
                    Some(Predicate::op(PredicateOp::Binary(BinaryOp::Cmp(
                        CmpOp::LessThan(false)
                    )))),
                    Some(Predicate::op(PredicateOp::Unary(UnaryOp::Negate))),
                ],
                ..Default::default()
            }
            .matches(&Node::try_from("{1 if x < 0; otherwise -2}").unwrap()),
            true,
        );

        // Test some deeper nesting
        assert_eq!(
            Predicate {
                children: vec![
                    Some(Predicate::children(vec![Some(Predicate::op(
                        PredicateOp::Const
                    ))])),
                    Some(Predicate::children(vec![
                        Some(Predicate::op(PredicateOp::Const)),
                        Some(Predicate::op(PredicateOp::Const))
                    ]))
                ],
                op: Some(PredicateOp::Binary(BinaryOp::Add)),
                ..Default::default()
            }
            .matches(&Node::try_from("-4 + 2 * 3").unwrap()),
            true,
        );
        assert_eq!(
            Predicate {
                children: vec![
                    Some(Predicate::children(vec![Some(Predicate::op(
                        PredicateOp::Const
                    ))])),
                    Some(Predicate::children(vec![Some(Predicate::op(
                        PredicateOp::Unary(UnaryOp::Negate)
                    ))]))
                ],
                ..Default::default()
            }
            .matches(&Node::try_from("-4 + 2 * 3").unwrap()),
            false,
        );
    }

    #[test]
    fn not_op() {
        assert_eq!(
            Predicate {
                not_op: Some(PredicateOp::Binary(BinaryOp::Mul)),
                ..Default::default()
            }
            .matches(&Node::try_from("3 + 5").unwrap()),
            true,
        );
        assert_eq!(
            Predicate {
                not_op: Some(PredicateOp::Var),
                ..Default::default()
            }
            .matches(&Node::try_from("x").unwrap()),
            false,
        );
    }

    #[test]
    fn const_value() {
        assert_eq!(
            Predicate {
                const_value: Some(TyValue::Bool(true)),
                ..Default::default()
            }
            .matches(&Node::try_from("3").unwrap()),
            false,
        );
        assert_eq!(
            Predicate {
                const_value: Some(TyValue::from(3.5)),
                ..Default::default()
            }
            .matches(&Node::try_from("3.5 + 2").unwrap()),
            false,
        );
        assert_eq!(
            Predicate {
                const_value: Some(TyValue::from(3)),
                ..Default::default()
            }
            .matches(&Node::try_from("3").unwrap()),
            true,
        );
        assert_eq!(
            Predicate {
                const_value: Some(TyValue::from(4)),
                ..Default::default()
            }
            .matches(&Node::try_from("3").unwrap()),
            false,
        );
    }
}
