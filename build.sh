#!/usr/bin/sh
cargo run $1
llc main.bc --relocation-model pic
gcc -I/usr/include/gc /usr/lib/libgc.so main.s -o main
./main
