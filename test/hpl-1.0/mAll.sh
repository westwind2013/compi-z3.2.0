#!/bin/sh

cd ./bin/crestAll
rm branches cfg cfg_branches cfg_func_map coverage funcount *.cil.* idcount illegal_inputs stmtcount input szd* .target_rank .world_size_indices .rank_indices 

cd ../..
make clean_arch arch=crestAll
make arch=crestAll
cd testing/ptest
./move crestAll
