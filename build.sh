#!/usr/bin/sh
cargo run main.jam
llc main.bc --relocation-model pic
gcc -I/usr/include/gc /usr/lib/libgc.so main.s -o main
./main
