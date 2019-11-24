#!/bin/sh

cadical $1 $2 --lrat=true
cargo run --bin elab $1 $2 $3
lrat-check $1 $3