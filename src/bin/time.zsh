#!/usr/bin/env zsh
o=$(cargo run --release --example rsa_set_init 1 $1 | ts '%.s')
e=$(echo $o | rg 'Done with re' | awk '{print $1}')
s=$(echo $o | rg 'Start multiexp' | awk '{print $1}')
echo 'Time: ' $(($e - $s))


