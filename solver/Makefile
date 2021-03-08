
# Makefile

CC = g++

CCOPT = -O9 -fPIC -fno-strict-aliasing -fexceptions -fpermissive -DNDEBUG -DIL_STD -Wall -std=c++11 -Wno-write-strings -g
CCLNFLAGS = -lm -pthread

all: solver

solver: solver.cpp
	$(CC) -o $@ $^ $(CCOPT) $(CCLNFLAGS)

.PHONY: clean

clean:
	rm -f solver
