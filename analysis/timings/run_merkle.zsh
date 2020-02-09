#!/usr/bin/env zsh
set -e

# Run from analysis

# Header
echo "set,swaps,log2_capacity,init,param,psynth,pcrypto,ver"

c=20
set=merkle
for t in 1 500 1000 1500; do
    # Filter out parameter generation log message with "points" in it
    ${0:a:h}/../../target/release/examples/set_proof -f $set $t $c | rg -v points;
done

