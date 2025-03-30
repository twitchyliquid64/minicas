use lazy_static::lazy_static;
use minicas::ast::{AstNode, Node};
use minicas::rules::{Rule, RuleSpec};
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
pub fn simplify(n: &mut Node) -> Result<(), ()> {
    let mut rule_matched = true;
    while rule_matched {
        rule_matched = false;

        n.walk_mut(true, &mut |n| {
            for (_name, rule) in RULES.iter() {
                if rule.meta.is_simplify {
                    rule_matched |= rule.eval(n).unwrap(); // TODO: dont just unwrap
                }
            }

            true
        });
    }

    Ok(())
}

#[cfg(test)]
fn do_test_rule(name: &str) {
    let rule = RULES.get(name).expect("rule doesnt exist");
    if let Err(idx) = rule.self_test() {
        panic!("failed test at index {}", idx);
    }
}

#[cfg(test)]
#[test]
fn test_simplify_rules() {
    // Shouldnt try and do constant folding
    let mut n = Node::try_from("1 + 1").unwrap();
    simplify(&mut n).unwrap();
    assert_eq!(n, Node::try_from("1 + 1").unwrap());

    // Two steps: a-a to 0, then 0/b to 0.
    let mut n = Node::try_from("(a - a) / b").unwrap();
    simplify(&mut n).unwrap();
    assert_eq!(n, Node::try_from("0").unwrap());
}
