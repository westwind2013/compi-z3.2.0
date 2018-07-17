// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include <algorithm>
#include <assert.h>
#include <stdio.h>
#include <utility>
#include <vector>
#include <fstream>
#include <iostream>
#include <unistd.h>

#include <cmath>

#include "mpi.h"

#include "base/symbolic_interpreter.h"
#include "base/z3_solver.h"

using std::make_pair;
using std::swap;
using std::vector;

//#define DEBUG_H

#ifdef DEBUG_H
#define IFDEBUG_H(x) x
#else
#define IFDEBUG_H(x)
#endif

//#define DEBUG

#ifdef DEBUG
#define IFDEBUG(x) x
#else
#define IFDEBUG(x)
#endif

namespace crest {

    set<addr_t> hongbo;

	typedef map<addr_t, SymbolicExpr*>::const_iterator ConstMemIt;

	SymbolicInterpreter::SymbolicInterpreter() :
		ex_(true), num_inputs_(0), pred_(NULL), return_value_(false) {
			stack_.reserve(16);

		}

	SymbolicInterpreter::SymbolicInterpreter(const vector<value_double_t>& input, size_t exec_times) :
		ex_(true), num_inputs_(0), pred_(NULL), return_value_(false) {
			stack_.reserve(16);
			ex_.mutable_inputs()->assign(input.begin(), input.end());

			// set the execution tag 
			ex_.execution_tag_ = exec_times;
//fprintf(stderr, "Execution tag = %zu\n\n", ex_.execution_tag_);
			
			//
			// hEdit: read the random values stored by the tool in file ".rand_params"
			// and save them to vector "rand_params"
			//
			/*
			if (input.empty()) {
				std::ifstream infile(".rand_params");
				if (!infile) {
					fprintf(stderr, "There is not such file (.rand_params)\n");
					fflush(stderr);
					//exit(-1);
				} else {
					string s1, s2;
					int times, value;
					while (infile >> s1 && infile >> s2) {
						times = std::stoi(s1);
						value = std::stoi(s2);
						while (times--) {
							rand_params_.push_back(value);
						}
					}
				}

				infile.close();
			}
			*/

		}

	SymbolicInterpreter::~SymbolicInterpreter() {
/*
		if (rank_ == target_rank_) {
			outfile_rank_indices.close();
			outfile_world_size_indices.close();
		}
*/	}

	void SymbolicInterpreter::DumpMemory() {
		for (ConstMemIt i = mem_.begin(); i != mem_.end(); ++i) {
			string s;
			i->second->AppendToString(&s);
			fprintf(stderr, "%lu: %s [%d]\n", i->first, s.c_str(),
					*(int*) (i->first));
		}
		for (size_t i = 0; i < stack_.size(); i++) {
			string s;
			if (stack_[i].expr) {
				stack_[i].expr->AppendToString(&s);
			} else if ((i == stack_.size() - 1) && pred_) {
				pred_->AppendToString(&s);
			}
            if ((i == (stack_.size() - 1)) && return_value_) {
                if (stack_[i].isFloat)
                    fprintf(stderr, "s%d: %lf [ %s ] (RETURN VALUE)\n", i,
                            stack_[i].concreteFD, s.c_str());
                else 
                    fprintf(stderr, "s%d: %lld [ %s ] (RETURN VALUE)\n", i,
                            stack_[i].concrete, s.c_str());
            } else {
                if (stack_[i].isFloat)
                    fprintf(stderr, "s%d: %lf [ %s ]\n", i, 
                            stack_[i].concreteFD, s.c_str());
                else
                    fprintf(stderr, "s%d: %lld [ %s ]\n", i, 
                        stack_[i].concrete, s.c_str());
            }
		}
		if ((stack_.size() == 0) && return_value_) {
			fprintf(stderr, "MISSING RETURN VALUE\n");
		}
	}

	void SymbolicInterpreter::ClearStack(id_t id) {
		IFDEBUG(fprintf(stderr, "clear\n"));
		
        for (vector<StackElem>::const_iterator it = stack_.begin();
				it != stack_.end(); ++it) {
			delete it->expr;
		}
		stack_.clear();
		ClearPredicateRegister();
		return_value_ = false;
		IFDEBUG(DumpMemory());
	}

	void SymbolicInterpreter::Load(id_t id, addr_t addr, value_t value) {
		IFDEBUG(fprintf(stderr, "load %lu %lld\n", addr, value));
	
        ConstMemIt it = mem_.find(addr);

        if (it != mem_.end()) {

if (it->second && it->second->VarExist(133))
{
    fprintf(stderr, "Load ID: %d, Addr: %p, Val: %d\n", id, addr, value);
    it->second->Print();

    hongbo.insert(addr);
}

            if (!it->second->IsFloat() ) {
                PushSymbolic(new SymbolicExpr(*it->second), value);
/*                if (id == 13567 || id == 13568) {
                    fprintf(stderr, "%d, symb, val: %ld\n", stack_.size(), value);
                    stack_.back().expr->Print();
                }
*/
            } else {
                //mem_.erase(it);
                SymbolicExpr* pExpr = new SymbolicExpr(*it->second);
                pExpr->FD2INT();
                PushSymbolic(pExpr, value);
                
                //PushConcrete(value);
/*                if (id == 13567 || id == 13568) {
                    fprintf(stderr, "%d, conc1, val: %ld\n", stack_.size(), value);
                    stack_.back().expr->Print();
                }
*/            
            }
        } else {
            PushConcrete(value);
/*            if (id == 13567 || id == 13568) {
                fprintf(stderr, "%d, conc2\n", stack_.size());
            }
*/        
        }
        fflush(stderr);
/*
        if (it == mem_.end()) {
			PushConcrete(value);
if (id == 14856 || id == 14857) {
    fprintf(stderr, "%d, conc\n", stack_.size());
    stack_.back().expr->Print();
}
		} else {
			PushSymbolic(new SymbolicExpr(*it->second), value);
if (id == 14856 || id == 14857) {
    fprintf(stderr, "%d, symb\n", stack_.size());
    stack_.back().expr->Print();
}
        }
*/

		ClearPredicateRegister();
		IFDEBUG(DumpMemory());
	}

	void SymbolicInterpreter::Load(id_t id, addr_t addr, value_double_t value) {
		IFDEBUG(fprintf(stderr, "load %lu %lf\n", addr, value));
		
        ConstMemIt it = mem_.find(addr);

if (it->second && it->second->VarExist(133))
{
    fprintf(stderr, "LoadFD ID: %d, Addr: %p, Val: %d\n", id, addr, value);
    it->second->Print(); 
    
    hongbo.insert(addr);
}

        if (it != mem_.end()) {
            if (it->second->IsFloat() ) {
                PushSymbolic(new SymbolicExpr(*it->second), value);
                if (it->second->VarExist(133) ) it->second->Print();
/*                if (id == 13567 || id == 13568) {
                    fprintf(stderr, "%d, symb, val: %ld\n", stack_.size(), value);
                    stack_.back().expr->Print();
                }
*/            } else {
                //mem_.erase(it);
                SymbolicExpr* pExpr = new SymbolicExpr(*it->second);
                pExpr->syncFD();
                PushSymbolic(pExpr, value);
                if (it->second->VarExist(133) ) it->second->Print();
                
                //PushConcrete(value);
/*                if (id == 13567 || id == 13568) {
                    fprintf(stderr, "%d, conc1, val: %ld\n", stack_.size(), value);
                    stack_.back().expr->Print();
                }
*/            }
        } else {
            PushConcrete(value);
/*            if (id == 13567 || id == 13568) {
                fprintf(stderr, "%d, conc2\n", stack_.size());
            }
*/        
        }
/*		if (it == mem_.end()) {
			PushConcrete(value);
		} else {
			PushSymbolic(new SymbolicExpr(*it->second), value);
		}
*/
		ClearPredicateRegister();
		IFDEBUG(DumpMemory());
	}
	
    void SymbolicInterpreter::Store(id_t id, addr_t addr, bool isF) {
		IFDEBUG(fprintf(stderr, "store %lu\n", addr));
		
        assert(stack_.size() > 0);

		const StackElem& se = stack_.back();
		if (se.expr) {
			if (!se.expr->IsConcrete()) {
				if (isF) {
                    // make this expression a floating point data type
                    (*se.expr) += 0.0;
                    mem_[addr] = se.expr;
                } else {
                    if (!se.expr->IsFloat() ) {
                        mem_[addr] = se.expr;
                    } else {
                        se.expr->FD2INT();
                        mem_[addr] = se.expr;
                        //mem_.erase(addr);
                        //delete se.expr;
                    }
                }
			} else {
				if (hongbo.find(addr) != hongbo.end() )
                    fprintf(stderr, "Store: ID %d, Addr %p "
                    "removed from symbolic "
                    "memory (1)\n", id, addr);
                mem_.erase(addr);
				delete se.expr;
			}
		} else {
            if (hongbo.find(addr) != hongbo.end() )
                fprintf(stderr, "Store: ID %d, Addr %p "
                "removed from symbolic "
                "memory (2)\n", id, addr);
			mem_.erase(addr);
		}

		stack_.pop_back();
		ClearPredicateRegister();
		IFDEBUG(DumpMemory());
	}

	void SymbolicInterpreter::ApplyUnaryOp(id_t id, unary_op_t op, value_t value) {
		IFDEBUG(fprintf(stderr, "apply1 %d %lld\n", op, value));
		
        assert(stack_.size() >= 1);
		StackElem& se = stack_.back();

//bool tag = false;
//if (se.expr->VarExist(133) ) tag = true;

		if (se.expr) {
			switch (op) {
				case ops::NEGATE:
					se.expr->Negate();
					ClearPredicateRegister();
					break;
				case ops::LOGICAL_NOT:
					if (pred_) {
						pred_->Negate();
						break;
					}
					// Otherwise, fall through to the concrete case.
				default:
//if (tag) {
//    fprintf(stderr, "UNARY:  id: %d, value: %d", id, value);    
//    se.expr->Print();
//}
					// Concrete operator.
					delete se.expr;

					//
					// hComment: make the expression NULL so that this 
					// expression is a concrete value
					//
					se.expr = NULL;
					ClearPredicateRegister();
			}
		}

		se.concrete = value;
		IFDEBUG(DumpMemory());
	}

	void SymbolicInterpreter::ApplyBinaryOp(id_t id, binary_op_t op,
			value_t value) {
		IFDEBUG(fprintf(stderr, "apply2 %d %lld\n", op, value));
		
        assert(stack_.size() >= 2);
		StackElem& a = *(stack_.rbegin() + 1);
		StackElem& b = stack_.back();

/*
bool tag = false;
if (a.expr && a.expr->VarExist(133)) {
    fprintf(stderr, "Binary 1: id: %d, a.expr", id);
    a.expr->Print();
    tag = true;

    if (b.expr) b.expr->Print();
    else fprintf(stderr, "%d, %f\n", b.concrete, b.concreteFD);
}
if (b.expr && b.expr->VarExist(133)) {
    fprintf(stderr, "Binary 1: id: %d, b.expr", id);
    b.expr->Print();
    tag = true;

    if (a.expr) a.expr->Print();
    else fprintf(stderr, "%d, %f\n", a.concrete, a.concreteFD);
}
*/

		if (a.expr || b.expr) {
			switch (op) {
				case ops::ADD:
					if (a.expr == NULL) {
						swap(a, b);
						*a.expr += b.concrete;
					} else if (b.expr == NULL) {
						*a.expr += b.concrete;
/*if (tag) {
    fprintf(stderr, "add\n");
    a.expr->Print(); 
}*/
					} else {
						*a.expr += *b.expr;
						delete b.expr;
					}
					break;

				case ops::SUBTRACT:
					if (a.expr == NULL) {
						b.expr->Negate();
						swap(a, b);
						*a.expr += b.concrete;
					} else if (b.expr == NULL) {
						*a.expr -= b.concrete;
/*if (tag) {
    fprintf(stderr, "sub\n");
    a.expr->Print(); 
} */
					} else {
						*a.expr -= *b.expr;
						delete b.expr;
					}
					break;

				case ops::SHIFT_L:
					if (a.expr != NULL) {
						// Convert to multiplication by a (concrete) constant.
						*a.expr *= (1LL << b.concrete);
/*if (tag) {
    fprintf(stderr, "shl\n");
    a.expr->Print(); 
} */
					}
					delete b.expr;
					break;

				case ops::MULTIPLY:
					if (a.expr == NULL) {
						swap(a, b);
						*a.expr *= b.concrete;
					} else if (b.expr == NULL) {
						*a.expr *= b.concrete;
/*if (tag) {
    fprintf(stderr, "mul\n");
    a.expr->Print(); 
}*/
					} else {
						swap(a, b);
						*a.expr *= b.concrete;
						delete b.expr;
					}
					break;

				default:
					// Concrete operator.
					delete a.expr;
					delete b.expr;
					a.expr = NULL;
			}
		}

/*if (tag && !a.expr) {
    fprintf(stderr, "Destroyed\n\n");
}*/
        // 
        // hEdit: not a float
        //
        a.isFloat = false;
		
        a.concrete = value;
		stack_.pop_back();
		ClearPredicateRegister();
		IFDEBUG(DumpMemory());
	}


	void SymbolicInterpreter::ApplyBinaryOp(id_t id, binary_op_t op,
			value_double_t value) {
		IFDEBUG(fprintf(stderr, "apply2 %d %lf\n", op, value));

//fprintf(stderr, "value = %lf\n", value);

        assert(stack_.size() >= 2);
		StackElem& a = *(stack_.rbegin() + 1);
		StackElem& b = stack_.back();

/*
bool tag = false;
if (a.expr && a.expr->VarExist(133)) {
    fprintf(stderr, "Binary 2: id: %d, a.expr", id);
    a.expr->Print();
    tag = true;
}
if (b.expr && b.expr->VarExist(133)) {
    fprintf(stderr, "Binary 2: id: %d, b.expr", id);
    b.expr->Print();
    tag = true;
}
*/
/*
if (a.expr) {
    string s;
    a.expr->AppendToString(&s);
    fprintf(stderr, "Expr: %s\n", s.c_str());
} else {
    fprintf(stderr, "Null expression!\n");
}
if (b.expr) {
    string s;
    b.expr->AppendToString(&s);
    fprintf(stderr, "Expr: %s\n", s.c_str());
} else {
    fprintf(stderr, "Null expression!\n");
}
*/
		if (a.expr || b.expr) {
			switch (op) {
				case ops::ADD:
					if (a.expr == NULL) {
						swap(a, b);
						if (b.isFloat) *a.expr += b.concreteFD;
                        else *a.expr += b.concrete;
					} else if (b.expr == NULL) {
						if (b.isFloat) *a.expr += b.concreteFD;
                        else *a.expr += b.concrete;
					} else {
						*a.expr += *b.expr;
						delete b.expr;
					}
					break;

				case ops::SUBTRACT:
					if (a.expr == NULL) {
						b.expr->Negate();
						swap(a, b);
						if (b.isFloat) *a.expr += b.concreteFD;
                        else *a.expr += b.concrete;
					} else if (b.expr == NULL) {
						if (b.isFloat) *a.expr -= b.concreteFD;
                        else *a.expr -= b.concrete;
					} else {
						*a.expr -= *b.expr;
						delete b.expr;
					}
					break;


				case ops::MULTIPLY:
					if (a.expr == NULL) {
						swap(a, b);
						if (b.isFloat) *a.expr *= b.concreteFD;
                        else *a.expr *= b.concrete;
					} else if (b.expr == NULL) {
						if (b.isFloat) *a.expr *= b.concreteFD;
                        else *a.expr *= b.concrete;
					} else {
						swap(a, b);
						if (b.isFloat) *a.expr *= b.concreteFD;
                        else *a.expr *= b.concrete;
						
                        delete b.expr;
					}
					break;

				default:
					// Concrete operator.
					delete a.expr;
					delete b.expr;
					a.expr = NULL;
			}
		}
        
/*if (tag && !a.expr) {
    fprintf(stderr, "Destroyed\n\n");
}*/
        a.isFloat = true;
		a.concreteFD = value;

/*
if (a.expr) {
    string s;
    a.expr->AppendToString(&s);
    fprintf(stderr, "Expr: %s\n", s.c_str());
} else {
    fprintf(stderr, "Null expression!\n");
}
*/		
        stack_.pop_back();
		ClearPredicateRegister();
		IFDEBUG(DumpMemory());
	}

	void SymbolicInterpreter::ApplyCompareOp(id_t id, compare_op_t op,
			value_t value) {
		IFDEBUG(fprintf(stderr, "compare2 %d %lld\n", op, value));
		
        assert(stack_.size() >= 2);
		StackElem& a = *(stack_.rbegin() + 1);
		StackElem& b = stack_.back();

        if (a.expr || b.expr) {
			// Symbolically compute "a -= b".
			if (a.expr == NULL) {
				b.expr->Negate();
				swap(a, b);
                if (b.isFloat) *a.expr += b.concreteFD;
                else *a.expr += b.concrete;
			} else if (b.expr == NULL) {
                if (b.isFloat) *a.expr -= b.concreteFD;
                else *a.expr -= b.concrete;
			} else {
				*a.expr -= *b.expr;
				delete b.expr;
			}
			// Construct a symbolic predicate (if "a - b" is symbolic), and
			// store it in the predicate register.
			if (!a.expr->IsConcrete()) {
				pred_ = new SymbolicPred(op, a.expr);
			} else {
				ClearPredicateRegister();
				delete a.expr;
			}
			// We leave a concrete value on the stack.
			a.expr = NULL;
		}
       
        a.isFloat = false;
		a.concrete = value;

		stack_.pop_back();
		IFDEBUG(DumpMemory());
	}

	void SymbolicInterpreter::Call(id_t id, function_id_t fid) {
		IFDEBUG(fprintf(stderr, "call %u\n", fid));
		
        ex_.mutable_path()->Push(kCallId);
		IFDEBUG(DumpMemory());
	}


	void SymbolicInterpreter::Return(id_t id) {
		IFDEBUG(fprintf(stderr, "return\n"));

		ex_.mutable_path()->Push(kReturnId);

//
// hEdit: temporary solution for a bug occuring when testing susy-hmc
// 
if (stack_.size() > 1) {
    StackElem e = stack_.back();
    stack_.clear();
    stack_.push_back(e);
}

		// There is either exactly one value on the stack -- the current function's
		// return value -- or the stack is empty.
		assert(stack_.size() <= 1);

		return_value_ = (stack_.size() == 1);

		IFDEBUG(DumpMemory());
	}

	void SymbolicInterpreter::HandleReturn(id_t id, value_t value) {
		IFDEBUG(fprintf(stderr, "handle_return %lld\n", value));

        
		if (return_value_) {
			// We just returned from an instrumented function, so the stack
			// contains a single element -- the (possibly symbolic) return value.
			assert(stack_.size() == 1);
            stack_.back().isFloat = false;
			return_value_ = false;
		} else {
			// We just returned from an uninstrumented function, so the stack
			// still contains the arguments to that function.  Thus, we clear
			// the stack and push the concrete value that was returned.
			ClearStack(-1);
			PushConcrete(value);
		}

		IFDEBUG(DumpMemory());
	}

	void SymbolicInterpreter::HandleReturn(id_t id, value_double_t value) {
		IFDEBUG(fprintf(stderr, "handle_return %lf\n", value));

		if (return_value_) {
			// We just returned from an instrumented function, so the stack
			// contains a single element -- the (possibly symbolic) return value.
			assert(stack_.size() == 1);
            stack_.back().isFloat = true;
			return_value_ = false;
		} else {
			// We just returned from an uninstrumented function, so the stack
			// still contains the arguments to that function.  Thus, we clear
			// the stack and push the concrete value that was returned.
			ClearStack(-1);
			PushConcrete(value);
		}

		IFDEBUG(DumpMemory());
	}

	void SymbolicInterpreter::Branch(id_t id, branch_id_t bid, bool pred_value) {
		IFDEBUG(fprintf(stderr, "branch %d %d\n", bid, pred_value));
//
// hEdit: debug
//
//if (stack_.size() != 1) {
//	fprintf(stderr, "branch: %d %d; stack'size: %d\n", 
//		bid, pred_value, stack_.size());
//}
        stack_.clear();
		
		//assert(stack_.size() == 1);
		//stack_.pop_back();

		if (pred_ && !pred_value) {
			pred_->Negate();
		}

		// 
		// hEdit: reduce constraint set size
		//
		//ex_.mutable_path()->Push(bid, pred_);
		ex_.mutable_path()->Push(bid, pred_, 
			pred_value? TRUE : FALSE);
		pred_ = NULL;
		IFDEBUG(DumpMemory());
	}

	void SymbolicInterpreter::BranchOnly(branch_id_t bid) {
		ex_.mutable_path()->Push(bid);
	}

    
    value_t SymbolicInterpreter::NewInput(type_t type, addr_t addr, value_double_t limit) {
        IFDEBUG(fprintf(stderr, "symbolic_input %d %lu\n", type, addr));

        mem_[addr] = new SymbolicExpr(1LL, num_inputs_);
        ex_.mutable_vars()->insert(make_pair(num_inputs_, type));

        value_t ret = 0;
        if (num_inputs_ < ex_.inputs().size()) {
            ret = CastTo(static_cast<value_t>(ex_.inputs()[num_inputs_]), type);
//fprintf(stderr, "ret: %d, %ld\n", num_inputs_, ret);
        } else {
            //
            // hEdit: get random paramters obtained from the tool
            //

            //if (rand_params_.size() > num_inputs_)
            //	ret = CastTo(rand_params_[num_inputs_], type);
            //else
            //{
            // When new marked variables is found, we need to
            // generate new values for them. 
            ret = CastTo(rand() % (int)limit, type);	
            // 
            // hEdit: synchronize the value among all processes
            //
            MPI_Bcast(&ret, 1, MPI_LONG_LONG_INT, 0, MPI_COMM_WORLD);

            //}
            ex_.mutable_inputs()->push_back(ret);
        }

        num_inputs_++;

        IFDEBUG(DumpMemory());
        return ret;
    }

	value_t SymbolicInterpreter::NewInputWithLimit(type_t type, addr_t addr, value_double_t limit) {
	
		ex_.limits_[num_inputs_] = limit;
		return NewInput(type, addr, limit);
	}


    value_double_t SymbolicInterpreter::NewInputFD(type_t type, addr_t addr, value_double_t limit) {
        IFDEBUG(fprintf(stderr, "symbolic_input %d %lu\n", type, addr));

        mem_[addr] = new SymbolicExpr(1.0f, num_inputs_);
        ex_.mutable_vars()->insert(make_pair(num_inputs_, type));

        value_double_t ret = 0;
        if (num_inputs_ < ex_.inputs().size()) {
            ret = static_cast<double>(ex_.inputs()[num_inputs_]);
        } else {
            //
            // hEdit: get random paramters obtained from the tool
            //

            //if (rand_params_.size() > num_inputs_)
            //	ret = CastTo(rand_params_[num_inputs_], type);
            //else
            //{
            // When new marked variables is found, we need to
            // generate new values for them. 
            ret = static_cast<double>(rand() % (int)limit);	
            // 
            // hEdit: synchronize the value among all processes
            //
            MPI_Bcast(&ret, 1, MPI_LONG_LONG_INT, 0, MPI_COMM_WORLD);

            //}
            ex_.mutable_inputs()->push_back(ret);
        }

        num_inputs_++;

        IFDEBUG(DumpMemory());
        return ret;
    }

	value_double_t SymbolicInterpreter::NewInputWithLimitFD(type_t type, addr_t addr, value_double_t limit) {
	
		ex_.limits_[num_inputs_] = limit;
		return NewInputFD(type, addr, limit);
	}
	
	
	// 
	// hEdit: this method takes special care of input variables  
	// that indicate MPI ranks in MPI_COMM_WORLD
	//
	value_t SymbolicInterpreter::NewInputRank(type_t type, addr_t addr) {
		IFDEBUG(fprintf(stderr, "symbolic_input %d %lu\n", type, addr));

		mem_[addr] = new SymbolicExpr(1LL, num_inputs_);
		ex_.mutable_vars()->insert(make_pair(num_inputs_, type));

		value_t ret = 0;
		if (num_inputs_ < ex_.inputs().size()) {
			ret = CastTo(rank_, type);
			(*ex_.mutable_inputs())[num_inputs_] = ret;
		} else {
			//
			// hEdit: process of MPI rank 0 is first tested
			//
			ret = CastTo(rank_, type);
			ex_.mutable_inputs()->push_back(ret);

			//
                        // hEdit: padd the vecotor *rand_params_* so as to make
                        // other variables marked as symbolic take the CORRECT
                        // values from the vector. 
                        //
                        //if (num_inputs_ < rand_params_.size())
			//	rand_params_.insert(rand_params_.begin() + num_inputs_, rank_);
			//else
			//	rand_params_.push_back(rank_);

		}
		
		//
		// hEdit: wirte the index of variables of MPI rank into a file for
		// later use
		//
		if (target_rank_ == rank_) {
			ex_.rank_indices_.push_back(num_inputs_);
			//outfile_rank_indices << num_inputs_ << std::endl;
		}

		num_inputs_++;

		IFDEBUG(DumpMemory());
		return ret;
	}




	// 
	// hEdit: this method takes special care of input variables  
	// that indicate MPI ranks in MPI_COMM_WORLD
	//
	value_t SymbolicInterpreter::NewInputRankNonDefaultComm(type_t type, addr_t addr) {
		IFDEBUG(fprintf(stderr, "symbolic_input %d %lu\n", type, addr));

		mem_[addr] = new SymbolicExpr(1LL, num_inputs_);
		ex_.mutable_vars()->insert(make_pair(num_inputs_, type));

if (num_inputs_ == 133) {
    hongbo.insert(addr);
    fprintf(stderr, "Appear on the symbolic memory: %p\n", addr);
    mem_[addr]->Print();    
}

		value_t ret = 0;
		if (num_inputs_ < ex_.inputs().size()) {
			ret = CastTo(ex_.inputs()[num_inputs_], type);
		} else {
			//
			// hEdit: the value will be overwritten by the call of MPI_Comm_rank
			// and thus it is given 0
			//
			ret = CastTo(0, type);
			ex_.mutable_inputs()->push_back(ret);

			//
                        // hEdit: padd the vecotor *rand_params_* so as to make
                        // other variables marked as symbolic take the CORRECT
                        // values from the vector. 
                        //
                        //if (num_inputs_ < rand_params_.size())
			//	rand_params_.insert(rand_params_.begin() + num_inputs_, rank_);
			//else
			//	rand_params_.push_back(rank_);


		}
		
		//
		// hEdit: wirte the index of variables of MPI rank into a file for
		// later use
		//
		if (target_rank_ == rank_) { 
			ex_.rank_non_default_comm_indices_.push_back(num_inputs_);
//fprintf(stderr, "non_default: %d\n", num_inputs_);
		}

		num_inputs_++;

		IFDEBUG(DumpMemory());
		return ret;
	}


	// 
	// hEdit: this method takes special care of input variables  
	// that indicates the size of MPI_COMM_WORLD
	//
	value_t SymbolicInterpreter::NewInputWorldSize(type_t type, addr_t addr) {
		IFDEBUG(fprintf(stderr, "symbolic_input %d %lu\n", type, addr));

		mem_[addr] = new SymbolicExpr(1LL, num_inputs_);
		ex_.mutable_vars()->insert(make_pair(num_inputs_, type));

		value_t ret = 0;
		if (num_inputs_ < ex_.inputs().size()) {
			ret = CastTo(ex_.inputs()[num_inputs_], type);
		} else {
			//
			// hEdit:  we first make the size of MPI_COMM_WORLD 4
			//
			ret = CastTo(world_size_, type);
			ex_.mutable_inputs()->push_back(ret);
			//std::cout << "debug: world_size" << ret 
			//	<< " : target_rank " << target_rank_ 
			//	<< " : rank " << rank_ << std::endl;
 			
			//
                        // hEdit: padd the vecotor *rand_params_* so as to make
                        // other variables marked as symbolic take the CORRECT
                        // values from the vector. 
                        //
                        //if (num_inputs_ < rand_params_.size())
			//	rand_params_.insert(rand_params_.begin() + num_inputs_, world_size_);
			//else 
			//	rand_params_.push_back(world_size_);
		}

		//
		// hEdit: wirte the index of variables of MPI_COMM_WORLD
		// size into a file for later use
		//
		if (target_rank_ == rank_) {
			ex_.world_size_indices_.push_back(num_inputs_);			
			//outfile_world_size_indices << num_inputs_ << std::endl;
		}

		num_inputs_++;

		IFDEBUG(DumpMemory());
		return ret;
	}

	value_t SymbolicInterpreter::NewInputWorldSizeWithLimit(type_t type, addr_t addr, value_double_t limit) {
		
		ex_.limits_[num_inputs_] = limit;
		return NewInputWorldSize(type, addr);
	}

	void SymbolicInterpreter::PushConcrete(value_t value) {
		PushSymbolic(NULL, value);
	}

	void SymbolicInterpreter::PushConcrete(value_double_t value) {
		PushSymbolic(NULL, value);
	}
    
    void SymbolicInterpreter::PushSymbolic(SymbolicExpr* expr, value_t value) {
		stack_.push_back(StackElem());
		StackElem& se = stack_.back();

        se.isFloat = false;
		se.expr = expr;
		
        se.concrete = value;
		se.concreteFD = 0.0;
	}

    void SymbolicInterpreter::PushSymbolic(SymbolicExpr* expr, value_double_t value) {
		stack_.push_back(StackElem());
		StackElem& se = stack_.back();
		
        se.isFloat = true;
        se.expr = expr;
		
        se.concreteFD = value;
		se.concrete = 0;
	}

	void SymbolicInterpreter::ClearPredicateRegister() {
		delete pred_;
		pred_ = NULL;
	}

}  // namespace crest
