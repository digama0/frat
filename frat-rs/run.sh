#!/bin/sh
cadical $1 $2 --lrat=true 
# case $? in
#   10) echo "SATISFIABLE";;
#   20) # ../drat-trim/drat-trim $1 $2 -C -l $2 > /dev/null
#       cargo run --bin elab --release -- $1 $2 $3 && \
#       ../../drat-trim/lrat-check $1 $3;;
#   *)  echo ERROR
#       return -1;;
# esac
