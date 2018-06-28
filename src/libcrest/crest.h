/* Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
 *
 * This file is part of CREST, which is distributed under the revised
 * BSD license.  A copy of this license can be found in the file LICENSE.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
 * for details.
 */

#ifndef LIBCREST_CREST_H__
#define LIBCREST_CREST_H__

/*
* During instrumentation, the folowing function calls are inserted in the
* C code under test.
*
* These calls (loosely) correspond to an execution of the program
* under test by a stack machine.  It is intended that these calls be
* used to symbolically execute the program under test, by maintaining
* a a symbolic stack (along with a symbolic memory map).  Specifically:
*
*  - A C expression (with no side effects) generates a series of Load
*    and Apply calls corresponding to the "postfix" evaluation of the
*    expression, using a stack (i.e. a Load indicates that a value is
*    pushed onto the stack, and unary and binary operations are applied
*    to one/two values popped off the stack).  For example, the expression
*    "a*b > 3+c" would generate the instrumentation:
*        Load(&a, a)
*        Load(&b, b)
*        ApplyBinOp(MULTIPLY, a*b)
*        Load(0, 3)
*        Load(&c, c)
*        ApplyBinOp(ADD, 3+c)
*        ApplyBinOp(GREATER_THAN, a*b > 3+c)
*    Note that each Load and Apply call includes the concrete value either
*    loaded or computed.  Also note that constants are treated as having
*    address "0".
*
* - Entering the then- or else-block of an if statement generates a Branch
*   call indicating which branch was taken.  The branch is on the value
*   popped from the stack.  For example, "if (a*b > 3+c) ..." generates
*   the series of Load and Apply calls above, plus one of:
*       Branch(true_id,  1)
*       Branch(false_id, 0)
*
* - An assignment statement generates a single Store call, indicating
*   that a value is popped off the stack and stored in the given address.
*   For example, "a = 3 + b" generates:
*        Load(0, 3)
*        Load(&b, b)
*        ApplyBinOp(ADD, 3+b)
*        Store(&a)
*
* - The instrumentation for function calls is somewhat complicated,
*   because we have to handle the case where an instrumented code
*   calls an un-instrumented function.  (We currently forbid
*   un-instrumented code from calling back into instrumented code.)
*
*   * For all calls, the actual function arguments are pushed onto
*     the stack.  In the body of the called function (if
*     instrumented), these values are Stored in the formal
*     parameters.  (See example below.)
*
*   * In the body of the called function, "return e" generates the
*     instrumentation for expression "e", followed by a call to
*     Return.  An void "return" statement similary generates a call
*     to Return.
*
*   * If the returned value is assigned to some variable -- e.g.
*     "z = max(a, 7)" -- then two calls are generated:
*         HandleReturn([concrete returned value])
*         Store(&z)
*     If, instead, the return value is ignored -- e.g. "max(a, 7);"
*     -- a single call to ClearStack is generated.

*     [The difficultly here is that, if the called function was not
*      instrumented, HandleReturn must clean up the stack -- which
*      will still contain the arguments to the function -- and then
*      load the concrete returned value onto the stack to then be
*      stored.  If the called function is instrumented, then HandleReturn
*      need not modify the stack -- it already contains a single element
*      (the returned value).]
*
*    * Full example:  Consider the function "add(x, y) { return x+y; }".
*      A call "z = add(a, 7)" generates instrumentation calls:
*          Load(&a, a)
*          Load(0, 7)
*          Call(add)
*          Store(&y)
*          Store(&x)
*          Load(&x, x)
*          Load(&y, y)
*          ApplyBinOp(ADD, x+y)
*          Return()
*          HandleReturn(z)
*          Store(&z)
*
* - A symbolic input generates a call to create a new symbol (passing
        *   the conrete initial value for that symbol).
*
*   [We pass the conrete value and have signed/unsigned versions only
*   to make it easier to exactly capture/print the concrete inputs to
*   the program under test.]
*/
#include "mpi.h"

#ifdef __cplusplus
#define EXTERN extern "C"
#else
#define EXTERN extern
#endif

/*
 * Type definitions.
 *
 * These macros must be kept in sync with the definitions in base/basic_types.h.
 * We use these obscure MACRO's rather than the definitions in basic_types.h
 * in an attempt to avoid clashing with names in instrumented programs
 * (and also because C does not support namespaces).
 */
#define __CREST_ID int
#define __CREST_BRANCH_ID int
#define __CREST_FUNCTION_ID unsigned int
#define __CREST_VALUE long long int
#define __CREST_ADDR unsigned long int

#define __CREST_OP int
#define __CREST_BOOL unsigned char

//
// hEdit: the support of floating point data type is in need of a data type DOUBLE
// due to the input capping design -- the data type of caps, or limits, is set as DOUBLE
// 
#define __CREST_VALUE_DOUBLE double

/*
 * Constants representing possible C operators.
 *
 * TODO(jburnim): Arithmetic versus bitwise right shift?
 */
typedef enum {
    /* binary arithmetic */
    __CREST_ADD = 0,
    __CREST_SUBTRACT = 1,
    __CREST_MULTIPLY = 2,
    __CREST_DIVIDE = 3,
    __CREST_MOD = 4,
    /* binary bitwise operators */
    __CREST_AND = 5,
    __CREST_OR = 6,
    __CREST_XOR = 7,
    __CREST_SHIFT_L = 8,
    __CREST_SHIFT_R = 9,
    /* binary logical operators */
    __CREST_L_AND = 10,
    __CREST_L_OR = 11,
    /* binary comparison */
    __CREST_EQ = 12,
    __CREST_NEQ = 13,
    __CREST_GT = 14,
    __CREST_LEQ = 15,
    __CREST_LT = 16,
    __CREST_GEQ = 17,
    /* unhandled binary operators */
    __CREST_CONCRETE = 18,
    /* unary operators */
    __CREST_NEGATE = 19,
    __CREST_NOT = 20,
    __CREST_L_NOT = 21,
};

/*
 * Short-cut to indicate that a function should be skipped during
 * instrumentation.
 */
#define __SKIP __attribute__((crest_skip))

/*
 * Instrumentation functions.
 */
EXTERN void __CrestInit() __SKIP;
EXTERN void __CrestGetMPIInfo() __SKIP;
EXTERN void __CrestLoad(__CREST_ID, __CREST_ADDR, __CREST_VALUE) __SKIP;
EXTERN void __CrestStore(__CREST_ID, __CREST_ADDR) __SKIP;
EXTERN void __CrestClearStack(__CREST_ID) __SKIP;
EXTERN void __CrestApply1(__CREST_ID, __CREST_OP, __CREST_VALUE) __SKIP;
EXTERN void __CrestApply2(__CREST_ID, __CREST_OP, __CREST_VALUE) __SKIP;
EXTERN void __CrestBranch(__CREST_ID, __CREST_BRANCH_ID, __CREST_BOOL) __SKIP;
EXTERN void __CrestBranchOnly(__CREST_BRANCH_ID) __SKIP;
EXTERN void __CrestCall(__CREST_ID, __CREST_FUNCTION_ID) __SKIP;
EXTERN void __CrestReturn(__CREST_ID) __SKIP;
EXTERN void __CrestHandleReturn(__CREST_ID, __CREST_VALUE) __SKIP;

//
// hEdit: support floating point data types
EXTERN void __CrestLoadFD(__CREST_ID, __CREST_ADDR, __CREST_VALUE_DOUBLE) __SKIP;
EXTERN void __CrestApply2FD(__CREST_ID, __CREST_OP, __CREST_VALUE_DOUBLE) __SKIP;
EXTERN void __CrestHandleReturnFD(__CREST_ID, __CREST_VALUE_DOUBLE) __SKIP;

/*
 * Functions (macros) for obtaining symbolic inputs.
 */
#define COMPI_unsigned_char(x) __CrestUChar(&x)
#define COMPI_unsigned_char_with_limit(x, limit) __CrestUCharWithLimit(&x, limit)
#define COMPI_unsigned_short(x) __CrestUShort(&x)
#define COMPI_unsigned_short_with_limit(x, limit) __CrestUShortWithLimit(&x, limit)
#define COMPI_unsigned_int(x) __CrestUInt(&x)
#define COMPI_unsigned_int_with_limit(x, limit) __CrestUIntWithLimit(&x, limit)
#define COMPI_char(x) __CrestChar(&x)
#define COMPI_char_with_limit(x, limit) __CrestCharWithLimit(&x, limit)
#define COMPI_short(x) __CrestShort(&x)
#define COMPI_short_with_limit(x, limit) __CrestShortWithLimit(&x, limit)
#define COMPI_int(x) __CrestInt(&x)
#define COMPI_int_with_limit(x, limit) __CrestIntWithLimit(&x, limit)
#define COMPI_float(x) __CrestFloat(&x)
#define COMPI_float_with_limit(x, limit) __CrestFloatWithLimit(&x, limit)
#define COMPI_double(x) __CrestDouble(&x)
#define COMPI_double_with_limit(x, limit) __CrestDoubleWithLimit(&x, limit)

//
// hEdit: symbolic input function for MPI rank and 
// the size of MPI_COMM_WORLD
//
#define COMPI_rank(x) __CrestRank(&x)
#define COMPI_world_size(x) __CrestWorldSize(&x)
#define COMPI_world_size_with_limit(x, limit) __CrestWorldSizeWithLimit(&x, limit)


EXTERN void __CrestUChar(unsigned char* x) __SKIP;
EXTERN void __CrestUCharWithLimit(unsigned char* x, __CREST_VALUE_DOUBLE limit) __SKIP;
EXTERN void __CrestUShort(unsigned short* x) __SKIP;
EXTERN void __CrestUShortWithLimit(unsigned short* x, __CREST_VALUE_DOUBLE limit) __SKIP;
EXTERN void __CrestUInt(unsigned int* x) __SKIP;
EXTERN void __CrestUIntWithLimit(unsigned int* x, __CREST_VALUE_DOUBLE limit) __SKIP;
EXTERN void __CrestChar(char* x) __SKIP;
EXTERN void __CrestCharWithLimit(char* x, __CREST_VALUE_DOUBLE limit) __SKIP;
EXTERN void __CrestShort(short* x) __SKIP;
EXTERN void __CrestShortWithLimit(short* x, __CREST_VALUE_DOUBLE limit) __SKIP;
EXTERN void __CrestInt(int* x) __SKIP;
EXTERN void __CrestIntWithLimit(int* x, __CREST_VALUE_DOUBLE limit) __SKIP;
EXTERN void __CrestFloat(float* x) __SKIP;
EXTERN void __CrestFloatWithLimit(float* x, __CREST_VALUE_DOUBLE limit) __SKIP;
EXTERN void __CrestDouble(double* x) __SKIP;
EXTERN void __CrestDoubleWithLimit(double* x, __CREST_VALUE_DOUBLE limit) __SKIP;

//
// hEdit: symbolic input function for MPI rank and 
// the size of MPI_COMM_WORLD
//
EXTERN void __CrestRank(int* x) __SKIP;
EXTERN void __CrestRankNonDefaultComm1(int* x) __SKIP;
EXTERN void __CrestRankNonDefaultComm2(MPI_Comm comm, int *x) __SKIP;
EXTERN void __CrestWorldSize(int* x) __SKIP;
EXTERN void __CrestWorldSizeWithLimit(int* x, __CREST_VALUE limit) __SKIP;

#endif  /* LIBCREST_CREST_H__ */
