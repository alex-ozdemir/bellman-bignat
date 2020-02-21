extern crate bellman_bignat;
extern crate bincode;
extern crate serde;

use std::path::PathBuf;

use bellman_bignat::set::int_set::exp::parallel::{ParExpComb};

fn main() {
    let dir = std::env::var("CARGO_MANIFEST_DIR")
        .expect("Missing CARGO_MANIFEST_DIR env variable (needed for ParExpComb)\nPlease run using cargo.");
    let mut pbuf = PathBuf::from(dir);
    pbuf.push("lib");
    pbuf.push("pcb_dflt");
    let path = pbuf.to_str().unwrap();
    let pcb = ParExpComb::deserialize(path);
    let monty = ParExpComb::from(pcb);
    monty.serialize(path);

    // read it back in just to double check
    let test = ParExpComb::deserialize(path);
    assert_eq!(monty, test);
}
