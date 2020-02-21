extern crate bellman_bignat;
extern crate bincode;
extern crate docopt;
extern crate serde;

use bellman_bignat::set::int_set::exp::parallel::ParExpComb;

use serde::Deserialize;
const USAGE: &str = "
Serialize Bases

Usage:
  serialize_bases <input_file>  <log_spacing> <output_file>
  set_bench (-h | --help)

";

#[derive(Deserialize)]
struct Args {
    arg_log_spacing: usize,
    arg_input_file: String,
    arg_output_file: String,
}

fn main() {
    let args: Args = docopt::Docopt::new(USAGE)
        .and_then(|d| d.deserialize())
        .unwrap_or_else(|e| e.exit());

    let pcb = ParExpComb::from_file(&args.arg_input_file, args.arg_log_spacing);
    pcb.serialize(&args.arg_output_file);

    // read it back in just to double check
    let test = ParExpComb::deserialize(&args.arg_output_file);
    assert_eq!(pcb, test);
}
