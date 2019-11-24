#!/bin/sh

cadical $1 $2 
drat-trim $1 $2 -L $3
lrat-check $1 $3