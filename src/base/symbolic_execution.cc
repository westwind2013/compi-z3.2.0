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

#include <utility>

#include "base/symbolic_execution.h"

namespace crest {

	SymbolicExecution::SymbolicExecution() { }

	SymbolicExecution::SymbolicExecution(bool pre_allocate)
		: path_(pre_allocate) { }

	SymbolicExecution::~SymbolicExecution() { }

	void SymbolicExecution::Swap(SymbolicExecution& se) {

		limits_.swap(se.limits_);
		rank_indices_.swap(se.rank_indices_);
		rank_non_default_comm_indices_.swap(se.rank_non_default_comm_indices_);
		rank_non_default_comm_map_.swap(se.rank_non_default_comm_map_);
		world_size_indices_.swap(se.world_size_indices_);
		std::swap(execution_tag_, se.execution_tag_);

		vars_.swap(se.vars_);
		inputs_.swap(se.inputs_);
		path_.Swap(se.path_);
	}

	void SymbolicExecution::Serialize(string* s) const {
		typedef map<var_t,type_t>::const_iterator VarIt;

		// Write the inputs.
		size_t len = vars_.size();

		s->append((char*)&len, sizeof(len));
		for (VarIt i = vars_.begin(); i != vars_.end(); ++i) {
			s->push_back(static_cast<char>(i->second));
			s->append((char*)&inputs_[i->first], sizeof(value_double_t));
//fprintf(stderr, "inputs_[%d] = %lf\n", i->first, inputs_[i->first]);
        }
                
        // Wirte the execution tag
        s->append((char*)&execution_tag_, sizeof(size_t));

        // write the specified limits
        len = limits_.size();
        s->append((char*)&len, sizeof(len));
        for (auto i: limits_) {
            s->append((char*)&i.first, sizeof(id_t));          
            s->append((char*)&i.second, sizeof(value_double_t));          

//fprintf(stderr, "limits_[%d] = %lf\n", i.first, i.second);
        } 

        // Wirte MPI info
        len = rank_indices_.size();
        s->append((char*)&len, sizeof(len));
        for (size_t i = 0; i < rank_indices_.size(); i++) {
            s->append((char*)&rank_indices_[i], sizeof(id_t));          
        }   

        len = rank_non_default_comm_indices_.size();
        s->append((char*)&len, sizeof(len));
        for (size_t i = 0; i < rank_non_default_comm_indices_.size(); i++) {
            s->append((char*)&rank_non_default_comm_indices_[i], sizeof(id_t));         
        }   

        // the number of rows
        len = rank_non_default_comm_map_.size();
        s->append((char*)&len, sizeof(len));
        for (auto tmpV: rank_non_default_comm_map_) {
            len = tmpV.size();
            s->append((char*)&len, sizeof(len));
            for (size_t j = 0; j < tmpV.size(); j++) {
                s->append((char*)&tmpV[j], sizeof(id_t));         
            }   
        }

        len = world_size_indices_.size();
        s->append((char*)&len, sizeof(len));
        for (size_t i = 0; i < world_size_indices_.size(); i++) {
            s->append((char*)&world_size_indices_[i], sizeof(id_t));            
        }

/*
//
// hEdit: debug
//
fprintf(stderr, "Serialization info: inputs size: %zu\n "
	"limits size: %zu\n rank_indices size: %zu \n"
	"rank_non_default_comm_indices size: %zu \n"
	"world_size_indices size: %zu \n\n", 
	vars_.size(), limits_.size(), rank_indices_.size(), 
	rank_non_default_comm_indices_.size(), 
	world_size_indices_.size());
*/

		// Write the path.
		path_.Serialize(s);
	}

	void SymbolicExecution::SerializeBranches(string* s) const {
		/*
		typedef map<var_t,type_t>::const_iterator VarIt;

		// Write the inputs.
		size_t len = vars_.size();

		//
		// hEdit:: debug
		//
		printf("vars_.size(): %d\n", len);

		s->append((char*)&len, sizeof(len));
		for (VarIt i = vars_.begin(); i != vars_.end(); ++i) {
			s->push_back(static_cast<char>(i->second));
			s->append((char*)&inputs_[i->first], sizeof(value_t));
		}*/

		// Write the path.
		path_.SerializeBranches(s);
	}

    bool SymbolicExecution::Parse(istream& s) {
        // Read the inputs.
        size_t len;
        s.read((char*)&len, sizeof(len));
        vars_.clear();
        inputs_.resize(len);
        for (size_t i = 0; i < len; i++) {
            vars_[i] = static_cast<type_t>(s.get());
            s.read((char*)&inputs_[i], sizeof(value_double_t));
//fprintf(stderr, "inputs_[%d] = %lf\n", i, inputs_[i]);
        }

        // Read the execution tag
        s.read((char*)&execution_tag_, sizeof(size_t));

        // Read user-specified limits
        s.read((char*)&len, sizeof(len));
        limits_.clear();
        id_t first;
        value_double_t second;
        for (size_t i = 0; i < len; i++) {
            s.read((char*)&first, sizeof(id_t));
            s.read((char*)&second, sizeof(value_double_t));
            limits_[first] = second;
//fprintf(stderr, "limits_[%d] = %lf\n", first, second);
        }

        // Read MPI info
        s.read((char*)&len, sizeof(len));
        rank_indices_.clear();
        rank_indices_.resize(len);
        for (size_t i = 0; i < len; i++) {
            s.read((char*)&rank_indices_[i], sizeof(id_t));
        }

        s.read((char*)&len, sizeof(len));
        rank_non_default_comm_indices_.clear();
        rank_non_default_comm_indices_.resize(len);
        for (size_t i = 0; i < len; i++) {
            s.read((char*)&rank_non_default_comm_indices_[i], sizeof(id_t));
        }

        s.read((char*)&len, sizeof(len));
        rank_non_default_comm_map_.clear();
        for (size_t i = 0; i < len; i++) {
            size_t len2;	
            s.read((char*)&len2, sizeof(len2));

            vector<id_t> tmpV;
            tmpV.resize(len2);
            for (size_t j = 0; j < len2; j++) {
                s.read((char*)&tmpV[j], sizeof(id_t));
            }	
            rank_non_default_comm_map_.push_back(tmpV);
        }

        s.read((char*)&len, sizeof(len));
        world_size_indices_.clear();
        world_size_indices_.resize(len);
        for (size_t i = 0; i < len; i++) {
            s.read((char*)&world_size_indices_[i], sizeof(id_t));
        }

        // Write the path.
        return (path_.Parse(s) && !s.fail());
    }

	bool SymbolicExecution::ParseBranches(istream& s) {
		// Read the inputs.
		/*
		size_t len;
		s.read((char*)&len, sizeof(len));
		vars_.clear();
		inputs_.resize(len);
		for (size_t i = 0; i < len; i++) {
			vars_[i] = static_cast<type_t>(s.get());
			s.read((char*)&inputs_[i], sizeof(value_t));
		}
		*/
		// Write the path.
		return (path_.ParseBranches(s) && !s.fail());
	}

}  // namespace crest
