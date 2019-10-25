#!/bin/sh
cadical $1 $2 > /dev/null
case $? in
  10) echo "SATISFIABLE";;
  20) # ../drat-trim/drat-trim $1 $2 -C -l $2 > /dev/null
      cargo run $1 $2;;
  *)  echo ERROR
      return -1;;
esac
