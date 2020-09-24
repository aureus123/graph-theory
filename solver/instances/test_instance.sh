#!/bin/bash

echo Testing $1...

../solver 0 $1.graph >log
../cliquer/cl -s -u output.dimacs >cl 2>>log
echo -n "," >>output
cat cl | cut -f1 -d"," | cut -f2 -d"=" | tr -d \\n >>output
echo -n "," >>output
cat log | tail -1 | cut -f1 -d"s" | cut -f2 -d")" | cut -f3 -d" " >>output
mv cl ../exp/$1.cl
mv log ../exp/$1.log
mv certificate.v ../exp/$1.v

