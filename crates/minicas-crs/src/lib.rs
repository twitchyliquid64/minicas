//! Mechanical simplification / factorization rules for algebraic expressions.
//!
//! Companion crate to [minicas_core].
//!
//! ```
//! # use minicas_crs::simplify;
//! # use minicas_core::ast::*;
//! let mut n = Node::try_from("5x * 2x").unwrap();
//!
//! // true means apply the full set of rules (i.e. factorization rules)
//! simplify(&mut n, true).unwrap();
//!
//! assert_eq!(n, Node::try_from("10 * pow(x, 2)").unwrap());
//! ```

use lazy_static::lazy_static;
use minicas_core::ast::{AstNode, Node};
use minicas_core::rules::{Rule, RuleSpec};
use std::collections::HashMap;
use toml::de;

include!(concat!(env!("OUT_DIR"), "/rules.rs"));

/// Returns all CRS rules.
fn rules() -> HashMap<String, RuleSpec> {
    de::from_str::<HashMap<String, RuleSpec>>(RULES_SRC).unwrap()
}

lazy_static! {
    static ref RULES: HashMap<String, Rule> = rules()
        .into_iter()
        .map(|(name, spec)| { (name, spec.try_into().unwrap()) })
        .collect();
}

/// Iteratively applies the simplification rules to the given node until none match.
///
/// When `all` is true, factorization and more aggressive simplification rules are additionally applied.
///
/// ```
/// # use minicas_crs::simplify;
/// # use minicas_core::ast::{AstNode, Node};
/// let mut n = Node::try_from("(a - a) / b").unwrap();
/// simplify(&mut n, false).unwrap();
/// assert_eq!(n, Node::try_from("0").unwrap());
/// ```
pub fn simplify(n: &mut Node, all: bool) -> Result<(), ()> {
    let (mut rule_matched, mut i) = (true, 0usize);
    while rule_matched && i < 50 {
        rule_matched = false;
        i += 1;

        n.walk_mut(true, &mut |n| {
            for (_name, rule) in RULES.iter() {
                if (all && !rule.meta.alt_form) || rule.meta.is_simplify {
                    rule_matched |= rule.eval(n).unwrap(); // TODO: dont just unwrap
                }
            }

            true
        });
    }

    if i >= 50 {
        Err(())
    } else {
        Ok(())
    }
}

#[cfg(test)]
fn do_test_rule(name: &str) {
    let rule = RULES.get(name).expect("rule doesnt exist");
    if let Err((idx, e)) = rule.self_test() {
        panic!("failed test at index {}: {}", idx, e);
    }
}

#[cfg(test)]
#[test]
fn test_simplify_rules() {
    // Shouldnt try and do constant folding
    let mut n = Node::try_from("1 + 1").unwrap();
    simplify(&mut n, false).unwrap();
    assert_eq!(n, Node::try_from("1 + 1").unwrap());

    // Two steps: a-a to 0, then 0/b to 0.
    let mut n = Node::try_from("(a - a) / b").unwrap();
    simplify(&mut n, false).unwrap();
    assert_eq!(n, Node::try_from("0").unwrap());

    // Combining coefficients
    let mut n = Node::try_from("3 * 5x").unwrap();
    simplify(&mut n, true).unwrap();
    assert_eq!(n, Node::try_from("15x").unwrap());

    let mut n = Node::try_from("5x -- 2x").unwrap();
    simplify(&mut n, true).unwrap();
    assert_eq!(n, Node::try_from("7x").unwrap());
    let mut n = Node::try_from("5x * 2x").unwrap();
    simplify(&mut n, true).unwrap();
    assert_eq!(n, Node::try_from("10 * pow(x, 2)").unwrap());
}
