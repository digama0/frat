#!/bin/sh
../../cadical/build/cadical $1 $2 --lrat=true
# ../../minisat/build/debug/bin/minisat_core $1 $2
case $? in
  10) echo "SATISFIABLE";;
  20) # ../drat-trim/drat-trim $1 $2 -C -l $2 > /dev/null
      cargo run --bin elab --release -- $1 $2 $3 && \
      ../../drat-trim/lrat-check $1 $3;;
      # cargo run --bin frat-rs --release -- $2;;
  *)  echo ERROR
      return -1;;
esac
