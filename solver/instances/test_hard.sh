#!/bin/bash

cp ../*.template .

./test_instance.sh 2-FullIns_3
./test_instance.sh 3-Insertions_3
./test_instance.sh queen8_8
./test_instance.sh 1-Insertions_4
./test_instance.sh huck
./test_instance.sh 4-Insertions_3
./test_instance.sh 3-FullIns_3
./test_instance.sh jean
./test_instance.sh queen9_9
./test_instance.sh david
./test_instance.sh mug88_1
./test_instance.sh mug88_25
./test_instance.sh 1-FullIns_4
./test_instance.sh myciel6
./test_instance.sh queen8_12
./test_instance.sh mug100_1
./test_instance.sh mug100_25
./test_instance.sh queen10_10

mv output ../exp/output.hard
rm *.template
rm output.dimacs

