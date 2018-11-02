// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
// Copyright (c) 2018, Hongbo Li (hli035@cs.ucr.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include <assert.h>
#include <fstream>
#include <string>
#include <sys/time.h>
#include <vector>
#include <iostream>
#include <cstdio>
#include <unistd.h>

#include "base/symbolic_interpreter.h"
#include "libcrest/crest.h"


using std::vector;
using namespace crest;

// The symbolic interpreter. */
static SymbolicInterpreter* SI;

// Have we read an input yet?  Until we have, generate only the
// minimal instrumentation necessary to track which branches were
// reached by the execution path.
static int pre_symbolic;

// Tables for converting from operators defined in libcrest/crest.h to
// those defined in base/basic_types.h.
static const int kOpTable[] =
{ // binary arithmetic
    ops::ADD, ops::SUBTRACT, ops::MULTIPLY, ops::CONCRETE, ops::CONCRETE,
    // binary bitwise operators
    ops::CONCRETE, ops::CONCRETE, ops::CONCRETE, ops::SHIFT_L, ops::CONCRETE,
    // binary logical operators
    ops::CONCRETE, ops::CONCRETE,
    // binary comparison
    ops::EQ, ops::NEQ, ops::GT, ops::LE, ops::LT, ops::GE,
    // unhandled binary operators
    ops::CONCRETE,
    // unary operators
    ops::NEGATE, ops::BITWISE_NOT, ops::LOGICAL_NOT
};


static void __CrestAtExit();


void __CrestInit() {
    
    //sleep(20);
    // Initialize the random number generator.
    struct timeval tv;
    gettimeofday(&tv, NULL);
    srand((tv.tv_sec * 1000000) + tv.tv_usec);

    // Read the input.
    vector<value_double_t> input;
    //system("cat input");

    std::ifstream in("input");
    value_double_t val;
    while (in >> val) {
        input.push_back(val);
    }
    in.close();

    // The number of execution times
    size_t num_iters = 0;
    std::ifstream infile(".num_iters");
    infile >> num_iters;
    infile.close();

    SI = new SymbolicInterpreter(input, num_iters);

    pre_symbolic = 1;

    assert(!atexit(__CrestAtExit));
}


void __CrestAtExit() {

    // hEdit: debug
//fprintf(stderr, "\nAtExit\n");
//fflush(stdout);
//fflush(stderr);

    string outfile_name("szd_execution");
    const SymbolicExecution& ex = SI->execution();
    // Write the execution out to file 'szd_execution'.

    string buff;
    buff.reserve(1<<26);

    if (SI->rank_ == SI->target_rank_) ex.Serialize(&buff);
    else  ex.SerializeBranches(&buff);

    if (SI->rank_ != SI->target_rank_) outfile_name += std::to_string((long long)SI->rank_); 

    // debug
    //std::cout << outfile_name << std::endl;

    std::ofstream out(outfile_name.c_str(), std::ios::trunc | std::ios::out | std::ios::binary);
    out.write(buff.data(), buff.size());
    assert(!out.fail());
    out.close();

    //
    // hEdit: delete the object
    // 
    delete SI;
}

void __CrestGetMPIInfo() {

    std::ifstream infile(".target_rank");
    infile >> SI->target_rank_;
    infile.close();

    MPI_Comm_rank(MPI_COMM_WORLD, &(SI->rank_));
    MPI_Comm_size(MPI_COMM_WORLD, &(SI->world_size_));

    /*
    // open all the logging files
    if (SI->target_rank_ == SI->rank_) {
    SI->outfile_rank_indices.open(".rank_indices", std::ofstream::out |
    std::ofstream::trunc);
    SI->outfile_world_size_indices.open(".world_size_indices", std::ofstream::out |
    std::ofstream::trunc);
    }
     */
    /*
       if (SI->target_rank_ == SI->rank_) {
       std::cout << "target_rank = " << SI->target_rank_ << std::endl;
       std::cout << "rank = " << SI->rank_ << std::endl;
       std::cout << "world_size = " << SI->world_size_ << std::endl;
       }*/
}

//
// Instrumentation functions.
//

void __CrestLoad(__CREST_ID id, __CREST_ADDR addr, __CREST_VALUE val) {
    if (!pre_symbolic)
        SI->Load(id, addr, val);
}

void __CrestLoadFD(__CREST_ID id, __CREST_ADDR addr, __CREST_VALUE_DOUBLE val) {
    if (!pre_symbolic)
        SI->Load(id, addr, val);
}

void __CrestStore(__CREST_ID id, __CREST_ADDR addr, __CREST_BOOL b) {
    if (!pre_symbolic)
        SI->Store(id, addr, static_cast<bool>(b));
}


void __CrestClearStack(__CREST_ID id) {
    if (!pre_symbolic)
        SI->ClearStack(id);
}


void __CrestApply1(__CREST_ID id, __CREST_OP op, __CREST_VALUE val) {
    assert((op >= __CREST_NEGATE) && (op <= __CREST_L_NOT));

    if (!pre_symbolic)
        SI->ApplyUnaryOp(id, static_cast<unary_op_t>(kOpTable[op]), val);
}


void __CrestApply2(__CREST_ID id, __CREST_OP op, __CREST_VALUE val) {
    assert((op >= __CREST_ADD) && (op <= __CREST_CONCRETE));

    if (pre_symbolic)
        return;

    if ((op >= __CREST_ADD) && (op <= __CREST_L_OR)) {
        SI->ApplyBinaryOp(id, static_cast<binary_op_t>(kOpTable[op]), val);
    } else {
        SI->ApplyCompareOp(id, static_cast<compare_op_t>(kOpTable[op]), val);
    }
}


void __CrestApply2FD(__CREST_ID id, __CREST_OP op, __CREST_VALUE_DOUBLE val) {
    assert((op >= __CREST_ADD) && (op <= __CREST_CONCRETE));

    if (pre_symbolic)
        return;

    SI->ApplyBinaryOp(id, static_cast<binary_op_t>(kOpTable[op]), val);
}


void __CrestBranch(__CREST_ID id, __CREST_BRANCH_ID bid, __CREST_BOOL b) {
    if (pre_symbolic) {
        // Precede the branch with a fake (concrete) load.
        SI->Load(id, 0, (value_t)b);
    }

    SI->Branch(id, bid, static_cast<bool>(b));
}


// 
// hEdit: this function would only be used when instrumenting only branches 
//
void __CrestBranchOnly(__CREST_BRANCH_ID bid) {
    SI->BranchOnly(bid);
}

void __CrestCall(__CREST_ID id, __CREST_FUNCTION_ID fid) {
    SI->Call(id, fid);
}


void __CrestReturn(__CREST_ID id) {
    SI->Return(id);
}


void __CrestHandleReturn(__CREST_ID id, __CREST_VALUE val) {
    if (!pre_symbolic)
        SI->HandleReturn(id, val);
}

void __CrestHandleReturnFD(__CREST_ID id, __CREST_VALUE_DOUBLE val) {
    if (!pre_symbolic)
        SI->HandleReturn(id, val);
}


//
// Symbolic input functions.
//

void __CrestUChar(unsigned char* x) {
    pre_symbolic = 0;
    *x = (unsigned char)SI->NewInput(types::U_CHAR, (addr_t)x);
}

void __CrestUCharWithLimit(unsigned char* x, __CREST_VALUE_DOUBLE limit) {
    pre_symbolic = 0;
    *x = (unsigned char)SI->NewInputWithLimit(types::U_CHAR, (addr_t)x, limit);
}

void __CrestUShort(unsigned short* x) {
    pre_symbolic = 0;
    *x = (unsigned short)SI->NewInput(types::U_SHORT, (addr_t)x);
}

void __CrestUShortWithLimit(unsigned short* x, __CREST_VALUE_DOUBLE limit) {
    pre_symbolic = 0;
    *x = (unsigned short)SI->NewInputWithLimit(types::U_SHORT, (addr_t)x, limit);
}

void __CrestUInt(unsigned int* x) {
    pre_symbolic = 0;
    *x = (unsigned int)SI->NewInput(types::U_INT, (addr_t)x);
}

void __CrestUIntWithLimit(unsigned int* x, __CREST_VALUE_DOUBLE limit) {
    pre_symbolic = 0;
    *x = (unsigned int)SI->NewInputWithLimit(types::U_INT, (addr_t)x, limit);
}

void __CrestChar(char* x) {
    pre_symbolic = 0;
    *x = (char)SI->NewInput(types::CHAR, (addr_t)x);
}

void __CrestCharWithLimit(char* x, __CREST_VALUE_DOUBLE limit) {
    pre_symbolic = 0;
    *x = (char)SI->NewInputWithLimit(types::CHAR, (addr_t)x, limit);
}

void __CrestShort(short* x) {
    pre_symbolic = 0;
    *x = (short)SI->NewInput(types::SHORT, (addr_t)x);
}

void __CrestShortWithLimit(short* x, __CREST_VALUE_DOUBLE limit) {
    pre_symbolic = 0;
    *x = (short)SI->NewInputWithLimit(types::SHORT, (addr_t)x, limit);
}

void __CrestInt(int* x) {
    pre_symbolic = 0;
    *x = (int)SI->NewInput(types::INT, (addr_t)x);
}

void __CrestIntWithLimit(int* x, __CREST_VALUE_DOUBLE limit) {
    pre_symbolic = 0;
    *x = (int)SI->NewInputWithLimit(types::INT, (addr_t)x, limit);
}

void __CrestLong(int* x) {
    pre_symbolic = 0;
    *x = (int)SI->NewInput(types::LONG, (addr_t)x);
}

void __CrestLongWithLimit(int* x, __CREST_VALUE_DOUBLE limit) {
    pre_symbolic = 0;
    *x = (int)SI->NewInputWithLimit(types::LONG, (addr_t)x, limit);
}

void __CrestFloat(float* x) {
    pre_symbolic = 0;
    *x = (float)SI->NewInputFD(types::FLOAT, (addr_t)x);
}

void __CrestFloatWithLimit(float* x, __CREST_VALUE_DOUBLE limit) {
    pre_symbolic = 0;
    *x = (float)SI->NewInputWithLimitFD(types::FLOAT, (addr_t)x, limit);
}

void __CrestDouble(double* x) {
    pre_symbolic = 0;
    *x = (double)SI->NewInputFD(types::DOUBLE, (addr_t)x);
}

void __CrestDoubleWithLimit(double* x, __CREST_VALUE_DOUBLE limit) {
    pre_symbolic = 0;
    *x = (double)SI->NewInputWithLimitFD(types::DOUBLE, (addr_t)x, limit);
}

//
// hEdit: symbolic input function used to mark MPI rank in MPI_COMM_WORLD
// 
void __CrestRank(int* x) {
    pre_symbolic = 0;
    *x = (int)SI->NewInputRank(types::U_INT, (addr_t)x);
}

//
// hEdit: symbolic input function used to mark MPI rank in communicators
// other than the default MPI_COMM_WORLD
// 
void __CrestRankNonDefaultComm1(int* x, __CREST_BOOL b) {
    pre_symbolic = 0;
    *x = (int)SI->NewInputRankNonDefaultComm(types::U_INT, (addr_t)x, 
        static_cast<bool>(b));
}

// 
// hEdit: 
// 
void __CrestRankNonDefaultComm2(MPI_Comm comm, int *x) {

    int size = 0;
    int *pComm = NULL;
    int is_focus = -1, focus = -1;

    MPI_Comm_size(comm, &size);
    if (SI->rank_ == SI->target_rank_) {
        is_focus = *x;
        pComm = new int [size];
    }
    MPI_Allreduce(&is_focus, &focus, 1, MPI_INT, MPI_MAX, comm);
    //fprintf(stderr, "focus all print %d: \n", focus);

    // return if this is not the communicator of interest, i.e., the communicator
    // that includes the target rank
    if(focus < 0) return;

    // rank 0 gathers the result
    MPI_Gather(&(SI->rank_), 1, MPI_INT, pComm, 1, MPI_INT, focus, comm);

    if (SI->rank_ == SI->target_rank_) {
        //
        // hEdit: debug
        //
        //fprintf(stderr, "new comm %zu: \n", comm);
        //for (int i = 0; i < size; i++) fprintf(stderr, "%d  ", pComm[i]);
        //fprintf(stderr, "\n");	
        vector<int> rank_map;
        rank_map.resize(size);
        for (int i = 0; i < size; i++)
            rank_map[i] = pComm[i];

        SI->ex_.rank_non_default_comm_map_.push_back(rank_map);
        delete [] pComm;

        int index = SI->num_inputs_ - 1;
        (*(SI->ex_.mutable_inputs()))[index] = *x;
        SI->ex_.limits_[index] = size;
    }
}

//
// hEdit: symbolic input function used to mark the size of 
// MPI_COMM_WORLD.
// 
void __CrestWorldSize(int* x) {
    pre_symbolic = 0;
    *x = (int)SI->NewInputWorldSize(types::U_INT, (addr_t)x);
}

void __CrestWorldSizeWithLimit(int* x, __CREST_VALUE limit) {
    pre_symbolic = 0;
    *x = (int)SI->NewInputWorldSizeWithLimit(types::U_INT, (addr_t)x, limit);
}
