//! Predicate rules/matching for AST nodes.
use crate::ast::{AstNode, BinaryOp, NodeInner, UnaryOp};

/// Describes a predicate on the operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PredicateOp {
    Unary(UnaryOp),
    Binary(BinaryOp),
    Const,
}

impl PredicateOp {
    /// Indicates if the operation matches that of the given [AstNode].
    pub fn matches<N: AstNode>(&self, n: &N) -> bool {
        match (self, n.as_inner()) {
            (Self::Unary(po), NodeInner::Unary(n)) => po.eq(&n.op),
            (Self::Binary(po), NodeInner::Binary(n)) => po.eq(&n.op),
            (Self::Const, NodeInner::Const(_)) => true,
            _ => false,
        }
    }
}

/// Describes a predicate on an AST node.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Predicate {
    /// Match only on nodes performing the given operation.
    pub op: Option<PredicateOp>,

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
        if self.children.len() > 0 {
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

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Node;

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
}
