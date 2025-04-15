use std::env;
use std::fs;
use std::io::Write;
use std::path::Path;

use minicas_core::rules::RuleSpec;
use std::collections::BTreeMap;
use toml::de;

fn main() {
    let out_dir = env::var_os("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("rules.rs");
    let mut out = fs::File::create(dest_path).unwrap();

    let rules_dir = Path::new("rules");

    if !rules_dir.exists() || !rules_dir.is_dir() {
        eprintln!("rules directory not found or is not a directory");
        return;
    }

    out.write(b"const RULES_SRC: &'static str = r#\"\n")
        .unwrap();
    let mut rule_names = BTreeMap::<String, ()>::new();
    for entry in fs::read_dir(rules_dir).expect("Failed to read rules directory") {
        match entry {
            Ok(entry) => {
                let path = entry.path();
                if path.extension().and_then(|s| s.to_str()) == Some("toml") {
                    let data = fs::read(path).unwrap();

                    // Validate
                    let s = std::str::from_utf8(&data).expect("failed decoding utf8");
                    let rules = de::from_str::<BTreeMap<String, RuleSpec>>(s)
                        .expect("failed parsing TOML to a rule spec");

                    out.write(&data).unwrap();
                    out.write(b"\n").unwrap();

                    for name in rules.keys() {
                        if rule_names.get(name).is_some() {
                            println!("cargo::error=Duplicate rule with name {}", name);
                        } else {
                            rule_names.insert(name.clone(), ());
                        }
                    }
                }
            }
            Err(err) => {
                eprintln!("Error reading entry in rules directory: {}", err);
            }
        }
    }
    out.write(b"\n\"#;\n\n").unwrap();

    for name in rule_names.keys() {
        out.write(
            format!(
                r"
            #[test]
            fn r#{}() {{
            ",
                name.replace('-', "_"),
            )
            .as_bytes(),
        )
        .unwrap();
        out.write(format!(r#"do_test_rule("{}");"#, name).as_bytes())
            .unwrap();
        out.write(b"\n}\n").unwrap();
    }

    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rerun-if-changed=rules");
}
