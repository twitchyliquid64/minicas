use lazy_static::lazy_static;
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

#[cfg(test)]
fn do_test_rule(name: &str) {
    let rule = RULES.get(name).expect("rule doesnt exist");
    if let Err(idx) = rule.self_test() {
        panic!("failed test at index {}", idx);
    }
}
