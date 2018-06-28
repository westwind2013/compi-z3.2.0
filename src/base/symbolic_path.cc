// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include "base/symbolic_path.h"
#include <fstream>

namespace crest {

	SymbolicPath::SymbolicPath() { }

	SymbolicPath::SymbolicPath(bool pre_allocate) {
		if (pre_allocate) {
			// To cut down on re-allocation.
			branches_.reserve(4000000);
			constraints_idx_.reserve(50000);
			constraints_.reserve(50000);
		}
//fprintf(stderr, "constraints_idx: %d, constraints_: %d, branches_: %zu\n", 
//	constraints_idx_.size(), constraints_.size(), branches_.size());
	}

	SymbolicPath::~SymbolicPath() {
		for (size_t i = 0; i < constraints_.size(); i++)
			delete constraints_[i];
	}

	void SymbolicPath::Swap(SymbolicPath& sp) {
		branches_.swap(sp.branches_);
		constraints_idx_.swap(sp.constraints_idx_);
		constraints_.swap(sp.constraints_);
	}

	void SymbolicPath::Push(branch_id_t bid) {
		branchesSet_.insert(bid);
	}

    void SymbolicPath::Push(branch_id_t bid, SymbolicPred* constraint, 
            branch_state_t state) {

        if (constraint) {
            //fprintf(stderr, "bid: %d, state: %d, branches' size: %d\n", bid, state, branches_.size());

            if (branchesHash.find(bid) == branchesHash.end() || 
                    branchesHash[bid] != state) {

                branchesHash[bid] = state;
                constraints_.push_back(constraint);
                constraints_idx_.push_back(branches_.size());
            }
        }

        branches_.push_back(bid);
        // 
        // hEdit: debug
        // 
        //string tmp;
        //constraint->AppendToString(&tmp);
        //fprintf(stderr, "%s @ branch %d \n\n", tmp.c_str(), bid);
    }

    void SymbolicPath::Serialize(string* s) const {
        typedef vector<SymbolicPred*>::const_iterator ConIt;

        //fprintf(stderr, "branches' size: %zu\n"
        //		"constraints' size: %zu\n", 
        //		branches_.size(), constraints_.size());

        //hEdit: print the constraints
        //for (auto c: constraints_) {
        //	string str;
        //	c->AppendToString(&str);
        //	fprintf(stderr, "%s\n", str.c_str());	
        //}
        //fprintf(stderr, "\n\n\n");
        //fflush(stderr);

        // Write the path.
        size_t len = branches_.size();

        //
        // hEdit:: debug
        //
        //printf("branches_.size(): %d\n", len);

        s->append((char*)&len, sizeof(len));
        s->append((char*)&branches_.front(), branches_.size() * sizeof(branch_id_t));

        // Write the path constraints.
        len = constraints_.size();

        //
        // hEdit:: debug
        //
        //printf("constraints_.size(): %d\n", len);

        s->append((char*)&len, sizeof(len));
        s->append((char*)&constraints_idx_.front(), constraints_.size() * sizeof(size_t));
        for (ConIt i = constraints_.begin(); i != constraints_.end(); ++i) {
            (*i)->Serialize(s);
        }
    }

	void SymbolicPath::SerializeBranches(string* s) const {
		//typedef vector<SymbolicPred*>::const_iterator ConIt;

		vector<branch_id_t> branches (branchesSet_.begin(), branchesSet_.end());
		// Write the path.
		size_t len = branches.size();
		
		//
		// hEdit:: debug
		//
		//printf("branches_.size(): %d\n", len);
		
		s->append((char*)&len, sizeof(len));
		s->append((char*)&branches.front(), branches.size() * sizeof(branch_id_t));
		
		//
		// hEdit:: debug
		//
		//printf("Wirte %lld\n", branches_.size() * sizeof(branch_id_t));

		/*
		// Write the path constraints.
		len = constraints_.size();

		//
		// hEdit:: debug
		//
		printf("constraints_.size(): %d\n", len);

		s->append((char*)&len, sizeof(len));
		s->append((char*)&constraints_idx_.front(), constraints_.size() * sizeof(size_t));
		for (ConIt i = constraints_.begin(); i != constraints_.end(); ++i) {
			(*i)->Serialize(s);
		}*/
	}

	bool SymbolicPath::Parse(istream& s) {
		typedef vector<SymbolicPred*>::iterator ConIt;
		size_t len;

		// Read the path.
		s.read((char*)&len, sizeof(size_t));
		branches_.resize(len);
		s.read((char*)&branches_.front(), len * sizeof(branch_id_t));
		// 
		// hEdit: temporary fix for Bug (1): core dump at assert () that 
		// checks abnormal reading over a stream whose reason is suspected to
		// that the size of available data to be read is less than expected. 
		// Note this fix spreads across multiple places. 
		//
		// Fix(1.b): the same as Fix (1.a)
		if (s.fail()) {

			size_t available = s.gcount();

			if ( s.rdstate() & std::ifstream::failbit) 
				fprintf(stderr, "Failbit\n Expect to read %zu bytes "
					"while only %zu bytes are available\n", 
					len * sizeof(branch_id_t), available);
			if ( s.rdstate() & std::ifstream::badbit) 
				fprintf(stderr, "Badbit\n Expect to read %zu bytes "
					"while only %zu bytes are available\n", 
					len * sizeof(branch_id_t), available);
			fflush(stderr);
			
			branches_.resize(available / sizeof(branch_id_t));
			
			return false;
		}

		// Clean up any existing path constraints.
		for (size_t i = 0; i < constraints_.size(); i++)
			delete constraints_[i];

		// Read the path constraints.
		s.read((char*)&len, sizeof(size_t));
		constraints_idx_.resize(len);
		constraints_.resize(len);
		s.read((char*)&constraints_idx_.front(), len * sizeof(size_t));
		for (ConIt i = constraints_.begin(); i != constraints_.end(); ++i) {
			*i = new SymbolicPred();
			if (!(*i)->Parse(s))
				return false;
		}

		return !s.fail();
	}

	bool SymbolicPath::ParseBranches(istream& s) {
		
		// 
		// hEdit: debug
		//
		/*
		if (s.fail()) {
			if ( s.rdstate() & std::ifstream::failbit) 
				printf("Failbiti before reading %lld\n");
			if ( s.rdstate() & std::ifstream::badbit) 
				printf("Badbit before reading \n");
			fflush(stdout);

			return false;
		}
		*/


		//typedef vector<SymbolicPred*>::iterator ConIt;
		size_t len;

		// Read the path.
		s.read((char*)&len, sizeof(size_t));
		branches_.resize(len);
		s.read((char*)&branches_.front(), len * sizeof(branch_id_t));
		
		// 
		// hEdit: temporary fix for Bug (1): core dump at assert () that 
		// checks abnormal reading over a stream whose reason is suspected to
		// that the size of available data to be read is less than expected. 
		// Note this fix spreads across multiple places. 
		// 
		// Fix (1.a): log error message and adjust the size of the recording
		// array branches_. 
		//
		if (s.fail()) {

			// obatin the real amount of reading from the stream s. 
			size_t available = s.gcount();

			// output error message to be checked later
			if ( s.rdstate() & std::ifstream::failbit) 
				fprintf(stderr, "Failbit\n Expect to read %zu bytes "
					"while only %zu bytes are available\n", 
					len * sizeof(branch_id_t), available);
			if ( s.rdstate() & std::ifstream::badbit) 
				fprintf(stderr, "Badbit\n Expect to read %zu bytes "
					"while only %zu bytes are available\n", 
					len * sizeof(branch_id_t), available);
			fflush(stderr);
			
			// adjust the size of branches_ to make sure it reflects 
			// its real size. 
			branches_.resize(available / sizeof(branch_id_t));
		
			// return false to denote a failure. 
			return false;
		}

		/*
		// Clean up any existing path constraints.
		for (size_t i = 0; i < constraints_.size(); i++)
			delete constraints_[i];

		// Read the path constraints.
		s.read((char*)&len, sizeof(size_t));
		constraints_idx_.resize(len);
		constraints_.resize(len);
		s.read((char*)&constraints_idx_.front(), len * sizeof(size_t));
		for (ConIt i = constraints_.begin(); i != constraints_.end(); ++i) {
			*i = new SymbolicPred();
			if (!(*i)->Parse(s))
				return false;
		}*/

		return !s.fail();
	}

}  // namespace crest
