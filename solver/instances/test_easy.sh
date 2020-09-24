#!/bin/bash

cp ../*.template .

./test_instance.sh myciel3
./test_instance.sh myciel4
./test_instance.sh queen5_5
./test_instance.sh 1-FullIns_3
./test_instance.sh queen6_6
./test_instance.sh 2-Insertions_3
./test_instance.sh myciel5
./test_instance.sh queen7_7

mv output ../exp/output.easy
rm *.template
rm output.dimacs

