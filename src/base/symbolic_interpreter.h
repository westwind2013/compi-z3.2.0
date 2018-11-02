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

#ifndef BASE_SYMBOLIC_INTERPRETER_H__
#define BASE_SYMBOLIC_INTERPRETER_H__

#include <stdio.h>
#include <climits>

#include <ext/hash_map>
#include <map>
#include <vector>

#include "base/basic_types.h"
#include "base/symbolic_execution.h"
#include "base/symbolic_expression.h"
#include "base/symbolic_path.h"
#include "base/symbolic_predicate.h"

using std::map;
using std::vector;
using __gnu_cxx::hash_map;

namespace crest {

	class SymbolicInterpreter {
		public:
			SymbolicInterpreter();
			explicit SymbolicInterpreter(const vector<value_double_t>& input, size_t exec_times);
			~SymbolicInterpreter();

			void ClearStack(id_t id);
			void Load(id_t id, addr_t addr, value_t value);
			void Load(id_t id, addr_t addr, value_double_t value);
			void Store(id_t id, addr_t addr, bool value);

			void ApplyUnaryOp(id_t id, unary_op_t op, value_t value);
			void ApplyBinaryOp(id_t id, binary_op_t op, value_t value);
			void ApplyBinaryOp(id_t id, binary_op_t op, value_double_t value);
			void ApplyCompareOp(id_t id, compare_op_t op, value_t value);

			void Call(id_t id, function_id_t fid);
			void Return(id_t id);
			void HandleReturn(id_t id, value_t value);
			void HandleReturn(id_t id, value_double_t value);

			void Branch(id_t id, branch_id_t bid, bool pred_value);
			void BranchOnly(branch_id_t bid);

			value_t NewInput(type_t type, addr_t addr, value_double_t limit = INT_MAX);
			value_t NewInputWithLimit(type_t type, addr_t addr, value_double_t limit);

            // 
            // hEdit: Supporting the floating point data type
            // 
			value_double_t NewInputFD(type_t type, addr_t addr, value_double_t limit = INT_MAX);
			value_double_t NewInputWithLimitFD(type_t type, addr_t addr, value_double_t limit);

			// 
			// hEdit: this method takes special care of input variables  
			// that indicate MPI ranks (MPI_COMM_WORLD)
			//
			value_t NewInputRank(type_t type, addr_t addr);
			value_t NewInputRankNonDefaultComm(type_t type, addr_t addr, bool isGlobal);

			// 
			// hEdit: this method takes special care of input variables  
			// that indicate the size of MPI_COMM_WORLD
			//
			value_t NewInputWorldSize(type_t type, addr_t addr);
			value_t NewInputWorldSizeWithLimit(type_t type, addr_t addr, value_double_t limit);
			
			// Accessor for symbolic execution so far.
			const SymbolicExecution& execution() const { return ex_; }

			// Debugging.
			void DumpMemory();
			void DumpPath();

			// 
			// hEdit
			//
			// the size of MPI_COMM_WORLD
			int world_size_;
			// the rank of this process
			int rank_;
			// the rank being tested
			int target_rank_;
			// logging files
			std::ofstream outfile_rank_indices;
			std::ofstream outfile_world_size_indices;
			
			// The symbolic execution (program path and inputs).
			SymbolicExecution ex_;
			
			// Number of symbolic inputs so far.
			unsigned int num_inputs_;


		private:
			struct StackElem {
				bool isFloat;
                SymbolicExpr* expr;  // NULL to indicate concrete.
				value_t concrete;
				value_double_t concreteFD;
			};

			// Stack.
			vector<StackElem> stack_;

			// Predicate register (for when top of stack is a symbolic predicate).
			SymbolicPred* pred_;

			// Is the top of the stack a function return value?
			bool return_value_;

			// Memory map.
			map<addr_t,SymbolicExpr*> mem_;

            // Local symbolic variables
            set<addr_t> localSymbols;
            
			//
			// hEdit
			//
			// parameters passed by users
			vector<int> rand_params_;
			// the indices of MPI ranks in non-default communicator
			vector<int> rank_in_non_default_indices;

			// Helper functions.
			inline void PushConcrete(value_t value);
			inline void PushSymbolic(SymbolicExpr* expr, value_t value);
			inline void ClearPredicateRegister();

            // 
            // hEdit: support floating point data type
            // 
			inline void PushConcrete(value_double_t value);
			inline void PushSymbolic(SymbolicExpr* expr, value_double_t value);
	};

}  // namespace crest

#endif  // BASE_SYMBOLIC_INTERPRETER_H__
