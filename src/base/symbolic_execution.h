// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#ifndef BASE_SYMBOLIC_EXECUTION_H__
#define BASE_SYMBOLIC_EXECUTION_H__

#include <istream>
#include <ostream>
#include <utility>
#include <vector>
#include <unordered_map>

#include "base/basic_types.h"
#include "base/symbolic_path.h"

using std::istream;
using std::make_pair;
using std::ostream;
using std::vector;
using std::unordered_map;


namespace crest {

	class SymbolicExecution {
		public:
			//
			// hEdit: logging information used specifically by MPI
			//
			unordered_map<id_t, value_double_t> limits_;
			vector<id_t> rank_indices_;
			vector<id_t> rank_non_default_comm_indices_;
			vector<vector<id_t>> rank_non_default_comm_map_;
			vector<id_t> world_size_indices_;
			size_t execution_tag_;

			SymbolicExecution();
			explicit SymbolicExecution(bool pre_allocate);
			~SymbolicExecution();

			void Swap(SymbolicExecution& se);

			void Serialize(string* s) const;
			void SerializeBranches(string* s) const;
			bool Parse(istream& s);
			bool ParseBranches(istream& s);

			const map<var_t,type_t>& vars() const { return vars_; }
			const vector<value_double_t>& inputs() const { return inputs_; }
			const SymbolicPath& path() const      { return path_; }

			map<var_t,type_t>* mutable_vars() { return &vars_; }
			vector<value_double_t>* mutable_inputs() { return &inputs_; }
			SymbolicPath* mutable_path() { return &path_; }

		private:
			map<var_t,type_t>  vars_;
			vector<value_double_t> inputs_;
			SymbolicPath path_;  
	};

}  // namespace crest

#endif  // BASE_SYMBOLIC_EXECUTION_H__
