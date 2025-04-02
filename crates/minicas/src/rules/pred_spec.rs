use crate::ast::{Const, Node};
use crate::pred::{Predicate, PredicateOp};
use serde::Deserialize;
use std::convert::TryInto;

#[derive(Deserialize, Default, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct EqualPair {
    l: Vec<usize>,
    #[serde(alias = "and")]
    r: Vec<usize>,
}

/// Describes how a predicate is specified in a rule file.
#[derive(Deserialize, Default, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct PredSpec {
    pub op: Option<String>,
    pub not_op: Option<String>,

    #[serde(alias = "const")]
    pub const_val: Option<String>,

    #[serde(alias = "equivalent")]
    pub equal: Option<Vec<EqualPair>>,

    #[serde(alias = "operand")]
    pub lhs: Option<Box<PredSpec>>,
    pub rhs: Option<Box<PredSpec>>,

    #[serde(alias = "num_arms")]
    pub arity: Option<usize>,

    pub children: Option<Vec<PredSpec>>,
}

impl TryInto<Predicate> for PredSpec {
    type Error = String;

    fn try_into(self) -> Result<Predicate, Self::Error> {
        let mut children = match (self.lhs, self.rhs) {
            (Some(lhs), None) => vec![Some((*lhs).try_into().map_err(|e| format!("lhs: {}", e))?)],
            (Some(lhs), Some(rhs)) => vec![
                Some((*lhs).try_into().map_err(|e| format!("lhs: {}", e))?),
                Some((*rhs).try_into().map_err(|e| format!("rhs: {}", e))?),
            ],
            (None, Some(rhs)) => vec![
                None,
                Some((*rhs).try_into().map_err(|e| format!("rhs: {}", e))?),
            ],
            (None, None) => vec![],
        };
        if children.len() > 0 && self.children.is_some() {
            return Err("both lhs/rhs/operand and children[] specified".into());
        }
        if let Some(c) = self.children {
            children = c
                .into_iter()
                .enumerate()
                .map(|(i, p)| match p.try_into() {
                    Ok(p) => Ok(Some(p)),
                    Err(e) => Err(format!("children.{}: {}", i, e)),
                })
                .collect::<Result<Vec<Option<Predicate>>, Self::Error>>()?;
        }

        let equivalent = self
            .equal
            .map(|v| v.into_iter().map(|p| (p.l.into(), p.r.into())).collect())
            .unwrap_or(vec![]);

        Ok(Predicate {
            op: match self.op {
                Some(op) => Some(
                    op.as_str()
                        .try_into()
                        .map_err(|_| format!("unknown op: {}", op))?,
                ),
                None => {
                    if self.const_val.is_some() {
                        Some(PredicateOp::Const)
                    } else {
                        None
                    }
                }
            },
            not_op: match self.not_op {
                Some(not_op) => Some(
                    not_op
                        .as_str()
                        .try_into()
                        .map_err(|_| format!("unknown op: {}", not_op))?,
                ),
                None => None,
            },
            const_value: match self.const_val {
                Some(s) => match Node::try_from(s.as_str())?.as_const() {
                    Some(Const(tv)) => Some(tv.clone()),
                    None => {
                        return Err(format!("const value {} is not a constant expression", s));
                    }
                },
                None => None,
            },
            arity: self.arity,
            equivalent,
            children,
            ..Predicate::default()
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{BinaryOp, UnaryOp},
        TyValue,
    };
    use toml::de;

    #[test]
    fn op() {
        assert_eq!(
            de::from_str::<PredSpec>(r#"op = '/'"#).unwrap().try_into(),
            Ok(Predicate::op(PredicateOp::Binary(BinaryOp::Div)))
        );
    }
    #[test]
    fn not_op() {
        assert_eq!(
            de::from_str::<PredSpec>(r#"not_op = '*'"#)
                .unwrap()
                .try_into(),
            Ok(Predicate {
                not_op: Some(PredicateOp::Binary(BinaryOp::Mul)),
                ..Predicate::default()
            })
        );
    }

    #[test]
    fn const_val() {
        assert_eq!(
            de::from_str::<PredSpec>(r#"const = '2'"#)
                .unwrap()
                .try_into(),
            Ok(Predicate {
                const_value: Some(TyValue::from(2)),
                ..Predicate::op(PredicateOp::Const)
            })
        );
        assert_eq!(
            de::from_str::<PredSpec>(r#"const = 'true'"#)
                .unwrap()
                .try_into(),
            Ok(Predicate {
                const_value: Some(TyValue::from(true)),
                ..Predicate::op(PredicateOp::Const)
            })
        );
    }

    #[test]
    fn nested() {
        assert_eq!(
            de::from_str::<PredSpec>(r#"lhs = {const = '2'}"#)
                .unwrap()
                .try_into(),
            Ok(Predicate {
                children: vec![Some(Predicate {
                    const_value: Some(TyValue::from(2)),
                    ..Predicate::op(PredicateOp::Const)
                })],
                ..Predicate::default()
            })
        );
        assert_eq!(
            de::from_str::<PredSpec>(r#"operand = {op = 'neg'}"#)
                .unwrap()
                .try_into(),
            Ok(Predicate {
                children: vec![Some(Predicate::op(PredicateOp::Unary(UnaryOp::Negate)))],
                ..Predicate::default()
            })
        );
        assert_eq!(
            de::from_str::<PredSpec>(r#"rhs = {op = 'neg'}"#)
                .unwrap()
                .try_into(),
            Ok(Predicate {
                children: vec![
                    None,
                    Some(Predicate::op(PredicateOp::Unary(UnaryOp::Negate)))
                ],
                ..Predicate::default()
            })
        );
        assert_eq!(
            de::from_str::<PredSpec>(
                r#"
            	rhs = {op = 'neg'}
            	lhs = {op = 'abs'}"#
            )
            .unwrap()
            .try_into(),
            Ok(Predicate {
                children: vec![
                    Some(Predicate::op(PredicateOp::Unary(UnaryOp::Abs))),
                    Some(Predicate::op(PredicateOp::Unary(UnaryOp::Negate)))
                ],
                ..Predicate::default()
            })
        );
    }
}
