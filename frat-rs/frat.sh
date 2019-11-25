#!/bin/sh

cadical $1 $2 --lrat=true
cargo run --release elab $1 $2 $3
lrat-check $1 $3