#!/usr/bin/env zsh
set -e

# Run from analysis

# Header
echo "set,swaps,log2_capacity,init,param,psynth,pcrypto,ver"

c=20
for t in 1 1000 2000; do
    for set in merkle rsa; do
        # Filter out parameter generation log message with "points" in it
        ${0:a:h}/../../target/release/examples/set_proof $set $t $c | rg -v points;
    done
done

