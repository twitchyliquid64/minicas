//! Implements typechecking of an AST.
use crate::ast::{AstNode, Binary, BinaryOp, NodeInner, Unary, UnaryOp};
use crate::Ty;

/// Describes issues with an AST due to invalid type + operation combinations.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeError {
    UnaryIncompatible(UnaryOp, Option<Ty>),
    BinaryIncompatible(BinaryOp, Option<Ty>, Option<Ty>),
    PiecewiseCondNotBool(usize, Option<Ty>),
    PiecewiseDifferentBranchTypes(Ty, Ty),
}

/// Checks an AST for type errors.
pub fn typecheck<N: AstNode>(n: &N) -> Result<(), TypeError> {
    let mut err = Ok(());
    n.walk(false, &mut |n| match n {
        NodeInner::Const(_) => true,
        NodeInner::Var(_) => true,

        NodeInner::Unary(Unary { op, val }) => {
            if !op.descendant_compatible(val.returns()) {
                err = Err(TypeError::UnaryIncompatible(op.clone(), val.returns()));
                false
            } else {
                true
            }
        }

        NodeInner::Binary(Binary { op, lhs, rhs }) => {
            if !op.descendant_compatible(lhs.returns(), rhs.returns()) {
                err = Err(TypeError::BinaryIncompatible(
                    op.clone(),
                    lhs.returns(),
                    rhs.returns(),
                ));
                false
            } else {
                true
            }
        }

        NodeInner::Piecewise(p) => {
            let mut arm_ty = None;
            for (i, (e, cond)) in p.iter_branches().enumerate() {
                let ret = cond.returns();
                if ret != Some(Ty::Bool) {
                    err = Err(TypeError::PiecewiseCondNotBool(i, ret));
                    return false;
                }

                match (arm_ty, e.returns()) {
                    (None, Some(b_ty)) => {
                        arm_ty = Some(b_ty);
                    }
                    (Some(last_ty), Some(b_ty)) => {
                        if last_ty != b_ty {
                            err = Err(TypeError::PiecewiseDifferentBranchTypes(last_ty, b_ty));
                            return false;
                        }
                    }
                    _ => {}
                };
            }

            match (arm_ty, p.else_branch().returns()) {
                (Some(arm_ty), Some(else_ty)) => {
                    if arm_ty != else_ty {
                        err = Err(TypeError::PiecewiseDifferentBranchTypes(arm_ty, else_ty));
                        return false;
                    }
                }
                _ => {}
            }
            true
        }
    });

    err
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Node, Piecewise};

    #[test]
    fn basic() {
        assert_eq!(typecheck(&Node::try_from("5").unwrap()), Ok(()),);
        assert_eq!(typecheck(&Node::try_from("x").unwrap()), Ok(()),);
        assert_eq!(typecheck(&Node::try_from("true").unwrap()), Ok(()),);
        assert_eq!(typecheck(&Node::try_from("-5").unwrap()), Ok(()),);
        assert_eq!(typecheck(&Node::try_from("3 + 5 * 11").unwrap()), Ok(()),);

        assert_eq!(
            typecheck(&Node::try_from("true + 1").unwrap()),
            Err(TypeError::BinaryIncompatible(
                BinaryOp::Add,
                Some(Ty::Bool),
                Some(Ty::Rational)
            )),
        );
        assert_eq!(
            typecheck(&Node::try_from("2 * 3 + false").unwrap()),
            Err(TypeError::BinaryIncompatible(
                BinaryOp::Add,
                Some(Ty::Rational),
                Some(Ty::Bool),
            )),
        );

        // A predicate like equals returns a bool, even tho the variable type is not known
        assert_eq!(
            typecheck(&Node::try_from("5 + (x == y)").unwrap()),
            Err(TypeError::BinaryIncompatible(
                BinaryOp::Add,
                Some(Ty::Rational),
                Some(Ty::Bool),
            )),
        );
    }

    #[test]
    fn piecewise() {
        assert_eq!(
            typecheck(&NodeInner::from(Piecewise::new(
                vec![],
                Node::try_from("x").unwrap().into()
            ))),
            Ok(()),
        );
        assert_eq!(
            typecheck(&NodeInner::from(Piecewise::new(
                vec![(
                    Node::try_from("-x").unwrap().into(),
                    Node::try_from("false").unwrap().into()
                )],
                Node::try_from("x").unwrap().into()
            ))),
            Ok(()),
        );

        // Cond is not bool
        assert_eq!(
            typecheck(&NodeInner::from(Piecewise::new(
                vec![(
                    Node::try_from("-x").unwrap().into(),
                    Node::try_from("5").unwrap().into()
                )],
                Node::try_from("x").unwrap().into()
            ))),
            Err(TypeError::PiecewiseCondNotBool(0, Some(Ty::Rational))),
        );
        // Branch arms different types
        assert_eq!(
            typecheck(&NodeInner::from(Piecewise::new(
                vec![
                    (
                        Node::try_from("-5").unwrap().into(),
                        Node::try_from("x == y").unwrap().into()
                    ),
                    (
                        Node::try_from("x == 5").unwrap().into(),
                        Node::try_from("x == y").unwrap().into()
                    )
                ],
                Node::try_from("x").unwrap().into()
            ))),
            Err(TypeError::PiecewiseDifferentBranchTypes(
                Ty::Rational,
                Ty::Bool
            )),
        );
        // Branch arms and else different types
        assert_eq!(
            typecheck(&NodeInner::from(Piecewise::new(
                vec![(
                    Node::try_from("x == 5").unwrap().into(),
                    Node::try_from("x == y").unwrap().into()
                )],
                Node::try_from("5").unwrap().into()
            ))),
            Err(TypeError::PiecewiseDifferentBranchTypes(
                Ty::Bool,
                Ty::Rational
            )),
        );
    }
}
