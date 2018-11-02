#!/bin/sh

make clean_arch arch=crestBranch
make arch=crestBranch
cd testing/ptest
./move crestBranch

