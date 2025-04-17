//! Implements algorithms for rearranging an equation.
use crate::ast::{AstNode, Binary, BinaryOp, Const, NodeInner, Unary, UnaryOp};
use crate::TyValue;

/// An error when attempting to rearrange an equation.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum RaiseError {
    Unhandled,
    BothTermsNotSupported,
    TargetNotFound,
}

/// An operation to apply when rearranging a equation.
#[derive(PartialEq, Eq, Clone, Debug)]
enum ReverseOp {
    Multiply(NodeInner),
    Divide(NodeInner),
    Add(NodeInner),
    Sub(NodeInner),
    // DivideUnder(NodeInner),
    Power(NodeInner),
    Root(NodeInner, bool),
}

impl ReverseOp {
    fn apply(ops: Vec<Self>, n: &mut NodeInner) {
        for op in ops.into_iter().rev() {
            use ReverseOp::*;
            match op {
                Multiply(i) => {
                    let mut old_n = NodeInner::new_const(false);
                    std::mem::swap(&mut old_n, n);

                    *n = Binary::mul(old_n, i).into();
                }
                Divide(i) => {
                    let mut old_n = NodeInner::new_const(false);
                    std::mem::swap(&mut old_n, n);

                    *n = Binary::div(old_n, i).into();
                }
                Add(i) => {
                    let mut old_n = NodeInner::new_const(false);
                    std::mem::swap(&mut old_n, n);

                    *n = Binary::add(old_n, i).into();
                }
                Sub(i) => {
                    let mut old_n = NodeInner::new_const(false);
                    std::mem::swap(&mut old_n, n);

                    *n = Binary::sub(old_n, i).into();
                }
                Power(i) => {
                    let mut old_n = NodeInner::new_const(false);
                    std::mem::swap(&mut old_n, n);

                    *n = Binary::pow(old_n, i).into();
                }
                Root(i, pm) => {
                    let mut old_n = NodeInner::new_const(false);
                    std::mem::swap(&mut old_n, n);

                    *n = if pm {
                        Binary::plus_or_minus::<TyValue, NodeInner>(
                            0.into(),
                            Binary::root(old_n, i).into(),
                        )
                        .into()
                    } else {
                        Binary::root(old_n, i).into()
                    };
                }
            }
        }
    }
}

/// Attempts to rearrange an equality equation to make the given target the subject.
///
/// `rhs` must contain an expression containing the target. `lhs` will be mutated.
///
/// ```
/// # use minicas_core::ast::*;
/// // Rearrange: y = 3x + 2 (for x)
/// let mut lhs = NodeInner::new_var("y");
/// make_subject(
///     &mut lhs,
///     &Node::try_from("3x + 2").unwrap(),
///     &Node::try_from("x").unwrap()
/// ).unwrap();
/// assert_eq!(&lhs, Node::try_from("(y-2) / 3").unwrap().as_inner());
/// ```
pub fn make_subject(
    lhs: &mut NodeInner,
    rhs: &NodeInner,
    target: &NodeInner,
) -> Result<(), RaiseError> {
    match raise_for(rhs, target)? {
        None => Err(RaiseError::TargetNotFound),
        Some(ops) => {
            ReverseOp::apply(ops, lhs);
            Ok(())
        }
    }
}

/// Computes the set of operations needed to make the target
/// the subject of the expression.
fn raise_for(n: &NodeInner, target: &NodeInner) -> Result<Option<Vec<ReverseOp>>, RaiseError> {
    if n == target {
        return Ok(Some(Vec::with_capacity(6)));
    }

    match n.as_inner() {
        NodeInner::Unary(Unary {
            op: UnaryOp::Negate,
            val,
        }) => {
            let o = raise_for(val, target)?;
            match o {
                None => Ok(None),
                Some(mut ops) => {
                    ops.push(ReverseOp::Multiply(
                        Unary::negate(NodeInner::new_const::<TyValue>(1.into())).into(),
                    ));
                    Ok(Some(ops))
                }
            }
        }

        NodeInner::Binary(Binary {
            op: BinaryOp::Add,
            lhs,
            rhs,
        }) => {
            let l = raise_for(lhs, target)?;
            let r = raise_for(rhs, target)?;
            match (l, r) {
                (Some(_), Some(_)) => Err(RaiseError::BothTermsNotSupported),
                (None, None) => Ok(None),
                (Some(mut ops), _) => {
                    ops.push(ReverseOp::Sub(rhs.as_inner().clone()));
                    Ok(Some(ops))
                }
                (_, Some(mut ops)) => {
                    ops.push(ReverseOp::Sub(lhs.as_inner().clone()));
                    Ok(Some(ops))
                }
            }
        }

        NodeInner::Binary(Binary {
            op: BinaryOp::Sub,
            lhs,
            rhs,
        }) => {
            let l = raise_for(lhs, target)?;
            let r = raise_for(rhs, target)?;
            match (l, r) {
                (Some(_), Some(_)) => Err(RaiseError::BothTermsNotSupported),
                (None, None) => Ok(None),
                (Some(mut ops), _) => {
                    ops.push(ReverseOp::Add(rhs.as_inner().clone()));
                    Ok(Some(ops))
                }
                (_, Some(mut ops)) => {
                    ops.push(ReverseOp::Add(lhs.as_inner().clone()));
                    Ok(Some(ops))
                }
            }
        }

        NodeInner::Binary(Binary {
            op: BinaryOp::Mul,
            lhs,
            rhs,
        }) => {
            let l = raise_for(lhs, target)?;
            let r = raise_for(rhs, target)?;
            match (l, r) {
                (Some(_), Some(_)) => Err(RaiseError::BothTermsNotSupported),
                (None, None) => Ok(None),
                (Some(mut ops), _) => {
                    ops.push(ReverseOp::Divide(rhs.as_inner().clone()));
                    Ok(Some(ops))
                }
                (_, Some(mut ops)) => {
                    ops.push(ReverseOp::Divide(lhs.as_inner().clone()));
                    Ok(Some(ops))
                }
            }
        }

        NodeInner::Binary(Binary {
            op: BinaryOp::Div,
            lhs,
            rhs,
        }) => {
            let l = raise_for(lhs, target)?;
            let r = raise_for(rhs, target)?;
            match (l, r) {
                (Some(_), Some(_)) => Err(RaiseError::BothTermsNotSupported),
                (None, None) => Ok(None),
                (Some(mut ops), _) => {
                    ops.push(ReverseOp::Multiply(rhs.as_inner().clone()));
                    Ok(Some(ops))
                }
                (_, Some(mut ops)) => {
                    ops.push(ReverseOp::Multiply(lhs.as_inner().clone()));
                    Ok(Some(ops))
                }
            }
        }

        NodeInner::Binary(Binary {
            op: BinaryOp::Pow,
            lhs,
            rhs,
        }) => {
            let l = raise_for(lhs, target)?;
            let r = raise_for(rhs, target)?;
            match (l, r) {
                (Some(_), Some(_)) => Err(RaiseError::BothTermsNotSupported),
                (None, None) | (_, Some(_)) => Ok(None),
                (Some(mut ops), _) => {
                    use num::ToPrimitive;
                    ops.push(ReverseOp::Root(
                        rhs.as_inner().clone(),
                        match rhs.as_inner() {
                            NodeInner::Const(Const(TyValue::Rational(v))) => {
                                let v = v % num::BigRational::from_integer(2.into());
                                v.to_usize().unwrap() == 0
                            }
                            // By default, do not assume the base is even
                            _ => false,
                        },
                    ));
                    Ok(Some(ops))
                }
            }
        }
        NodeInner::Binary(Binary {
            op: BinaryOp::Root,
            lhs,
            rhs,
        }) => {
            let l = raise_for(lhs, target)?;
            let r = raise_for(rhs, target)?;
            match (l, r) {
                (Some(_), Some(_)) => Err(RaiseError::BothTermsNotSupported),
                (None, None) | (_, Some(_)) => Ok(None),
                (Some(mut ops), _) => {
                    ops.push(ReverseOp::Power(rhs.as_inner().clone()));
                    Ok(Some(ops))
                }
            }
        }

        NodeInner::Const(_) | NodeInner::Var(_) => Ok(None),
        _ => Err(RaiseError::Unhandled),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Node;

    #[test]
    fn raise_for_basic() {
        assert_eq!(
            raise_for(&Node::try_from("x").unwrap(), &Node::try_from("x").unwrap()),
            Ok(Some(vec![]))
        );
        assert_eq!(
            raise_for(
                &Node::try_from("-x").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(Some(vec![ReverseOp::Multiply(
                Node::try_from("-1").unwrap().into()
            )]))
        );

        assert_eq!(
            raise_for(
                &Node::try_from("x + y").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(Some(vec![ReverseOp::Sub(
                Node::try_from("y").unwrap().into()
            )]))
        );
        assert_eq!(
            raise_for(
                &Node::try_from("y + x").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(Some(vec![ReverseOp::Sub(
                Node::try_from("y").unwrap().into()
            )]))
        );
        assert_eq!(
            raise_for(
                &Node::try_from("x * y").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(Some(vec![ReverseOp::Divide(
                Node::try_from("y").unwrap().into()
            )]))
        );
        assert_eq!(
            raise_for(
                &Node::try_from("pow(x, 2)").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(Some(vec![ReverseOp::Root(
                Node::try_from("2").unwrap().into(),
                true,
            )]))
        );

        assert_eq!(
            raise_for(
                &Node::try_from("x * (y-5)").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(Some(vec![ReverseOp::Divide(
                Node::try_from("y-5").unwrap().into()
            ),]))
        );
    }

    #[test]
    fn raise_for_chained() {
        assert_eq!(
            raise_for(
                &Node::try_from("(x-6) * y").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(Some(vec![
                ReverseOp::Add(Node::try_from("6").unwrap().into()),
                ReverseOp::Divide(Node::try_from("y").unwrap().into()),
            ]))
        );

        assert_eq!(
            raise_for(
                &Node::try_from("(x-6) / y").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(Some(vec![
                ReverseOp::Add(Node::try_from("6").unwrap().into()),
                ReverseOp::Multiply(Node::try_from("y").unwrap().into()),
            ]))
        );
    }

    #[test]
    fn make_subject_basic() {
        let mut lhs = NodeInner::new_const::<TyValue>(0.into());
        assert_eq!(
            make_subject(
                &mut lhs,
                &Node::try_from("y").unwrap(),
                &Node::try_from("y").unwrap()
            ),
            Ok(())
        );
        assert_eq!(&lhs, Node::try_from("0").unwrap().as_inner());

        let mut lhs = NodeInner::new_const::<TyValue>(0.into());
        assert_eq!(
            make_subject(
                &mut lhs,
                &Node::try_from("y + 5").unwrap(),
                &Node::try_from("y").unwrap()
            ),
            Ok(())
        );
        assert_eq!(&lhs, Node::try_from("0-5").unwrap().as_inner());

        let mut lhs = NodeInner::new_var("y");
        assert_eq!(
            make_subject(
                &mut lhs,
                &Node::try_from("3x + 2").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(())
        );
        assert_eq!(&lhs, Node::try_from("(y-2) / 3").unwrap().as_inner());

        let mut lhs = NodeInner::new_var("y");
        assert_eq!(
            make_subject(
                &mut lhs,
                &Node::try_from("sqrt(x)").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(())
        );
        assert_eq!(&lhs, Node::try_from("pow(y, 2)").unwrap().as_inner());
    }

    #[test]
    fn make_subject_pows() {
        let mut lhs = NodeInner::new_const::<TyValue>(4.into());
        assert_eq!(
            make_subject(
                &mut lhs,
                &Node::try_from("pow(x, 2)").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(())
        );
        assert_eq!(&lhs, Node::try_from("0 ± sqrt(4)").unwrap().as_inner());
        let mut lhs = NodeInner::new_const::<TyValue>(99.into());
        assert_eq!(
            make_subject(
                &mut lhs,
                &Node::try_from("pow(x, 5)").unwrap(),
                &Node::try_from("x").unwrap()
            ),
            Ok(())
        );
        assert_eq!(&lhs, Node::try_from("root(99, 5)").unwrap().as_inner());
    }

    #[test]
    fn make_subject_distance_formula() {
        // distance formula
        // d                            = sqrt( (x2 - x1)^2 + (y2 - y1)^2 )
        // d^2                          = (x2 - x1)^2 + (y2 - y1)^2
        // d^2 - (y2 - y1)^2            = (x2 - x1)^2
        // sqrt(d^2 - (y2 - y1)^2)      =  x2 - x1
        // sqrt(d^2 - (y2 - y1)^2) + x1 =  x2
        let mut lhs = NodeInner::new_var("d");
        assert_eq!(
            make_subject(
                &mut lhs,
                &Node::try_from("sqrt(pow(x2 - x1, 2) + pow(y2 - y1, 2))").unwrap(),
                &Node::try_from("x2").unwrap()
            ),
            Ok(())
        );
        assert_eq!(
            &lhs,
            Node::try_from("0 ± sqrt(pow(d, 2) - pow(y2 - y1, 2)) + x1")
                .unwrap()
                .as_inner(),
            "mismatch, got: {}\n",
            lhs
        );
    }
}
