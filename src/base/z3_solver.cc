// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include <iostream>
#include <algorithm>
#include <assert.h>
#include <limits>
#include <queue>
#include <set>
#include <fstream>
#include <stdio.h>
#include <stdlib.h>
#include <utility>

#include <cstdio>
#include <unistd.h>

#include <z3.h>
#include "base/z3_solver.h"

using std::make_pair;
using std::numeric_limits;
using std::queue;
using std::set;

#define DEBUG(x)

#define USE_RANGE_CHECK 1

namespace crest {

	typedef vector<const SymbolicPred*>::const_iterator PredIt;

	Z3Solver::Z3Solver() {	
	}

	Z3Solver::~Z3Solver() {

		// Bug: Memory leakage
		//for (vector<SymbolicExpr *>::iterator iter = exprsMPI.begin(); 
		//	iter < exprsMPI.end(); iter++) {
		//	delete *iter;	
		//}

		for (vector<SymbolicPred *>::iterator iter = constraintsMPI.begin(); 
				iter < constraintsMPI.end(); iter++) {
			delete *iter;	
		}
	}

	//
	// hEdit: generate additional constraints for MPI rank 
	// 
	void Z3Solver::GenerateConstraintsMPI(const SymbolicExecution& ex) {

		// 1. clear the old contents
		for (size_t i = 0; i < constraintsMPI.size(); i++) {
			delete constraintsMPI[i];	
		}
		constraintsMPI.clear();
	
		
		// 2. build new contents
		SymbolicExpr *world_size_first = NULL, *world_size_other = NULL;
		SymbolicExpr *rank_first = NULL, *rank_other = NULL, *tmp_expr = NULL;
		SymbolicPred *tmpPred = NULL;
		
		// construct the constraints:
		// (1) make all the variables representing the size of MPI_COMM_WORLD 
		// equivalent
		if (!ex.world_size_indices_.empty()) {
			world_size_first = new SymbolicExpr(1LL, ex.world_size_indices_[0]);
			for (size_t i = 1; i < ex.world_size_indices_.size(); i++) {
				world_size_other = new SymbolicExpr(1LL, ex.world_size_indices_[i]);
				*world_size_other -= *world_size_first; 

				tmpPred = new SymbolicPred(ops::EQ, world_size_other);
				constraintsMPI.push_back(tmpPred);
			}
		}

		// (2) make all the variables for MPI ranks in the MPI_COMM_WORLD 
		// equivalent
		if(!ex.rank_indices_.empty()) {
			rank_first = new SymbolicExpr(1LL, ex.rank_indices_[0]);
			///SymbolicExpr  *rank_first_ = new SymbolicExpr(1, rank_indices_[0]);
			for (size_t i = 1; i < ex.rank_indices_.size(); i++) {
				rank_other = new SymbolicExpr(1LL, ex.rank_indices_[i]);
				*rank_other -= *rank_first; 

				//exprsMPI.push_back(rank_other);
				tmpPred = new SymbolicPred(ops::EQ, rank_other);
				constraintsMPI.push_back(tmpPred);

				//string str;
				//tmpPred->AppendToString(&str);
				//printf("%s\n", str.c_str());	

			}
		}
		//
		// remove this part as we make the MPI rank an unsigned int
		//	
		// (3) MPI rank >= 0
		//tmpPred = new SymbolicPred(ops::GE, rank_first_);
		//constraintsMPI.push_back(tmpPred);

		// (4) MPI rank < the size of MPI_COMM_WORLD
		if (rank_first && world_size_first) {
			*rank_first -= *world_size_first; 
			//exprsMPI.push_back(rank_first);
			tmpPred = new SymbolicPred(ops::LT, rank_first);
			constraintsMPI.push_back(tmpPred);

			// delete unwanted resources
			delete world_size_first;
		}

		// (5) the size of MPI_COMM_WORLD must be smaller than 
		//if (world_size_first) {
		//	*world_size_first -= 4;
		//	tmpPred = new SymbolicPred(ops::LE, world_size_first);
		//	constraintsMPI.push_back(tmpPred);
		//}

		if (!ex.limits_.empty()) {
			for (auto limit: ex.limits_) {
                tmp_expr = new SymbolicExpr(1LL, limit.first);
                if ((*ex.mutable_vars() )[limit.first] == types::FLOAT || 
                    (*ex.mutable_vars() )[limit.first] == types::DOUBLE)
                    *tmp_expr -= limit.second;
                else *tmp_expr -= static_cast<value_t>(limit.second);
				
                tmpPred = new SymbolicPred(ops::LE, tmp_expr);
				constraintsMPI.push_back(tmpPred);
			}
		}

		//string str;
		//tmpPred->AppendToString(&str);
		//printf("%s\n", str.c_str());	

		//for (vector<SymbolicPred*>::iterator iter = constraintsMPI.begin(); 
		//		iter < constraintsMPI.end(); iter++) {
		//	string str;
		//	(*iter)->AppendToString(&str);
		//	printf("%s\n", str.c_str());	
		//}
		return;
	}


	bool Z3Solver::IncrementalSolve(const vector<value_double_t>& old_soln,
			const map<var_t,type_t>& vars,
			vector<const SymbolicPred*>& constraints,
			map<var_t,value_double_t>* soln) {
		
		const SymbolicPred* pointer2Last = constraints.back();

        //
        // hEdit: debug 
        // 
        fprintf(stderr, "The size of constraintsMPI is %zu \n"
        	"The size of constraints is %zu \n\n", 
        	constraintsMPI.size(), constraints.size());
            
		
		//
		// hEdit: insert the MPI constraints
		//
		for (vector<SymbolicPred*>::iterator iter = constraintsMPI.begin(); 
				iter < constraintsMPI.end(); iter++) {
			//constraints.insert(constraints.end()-1, *iter);	
			constraints.push_back(*iter);
		}

        //
        // hEdit: print the constraints
        //
        //for (PredIt iter = constraints.begin(); iter < constraints.end(); iter++) {
        //	string str;
        //	(*iter)->AppendToString(&str);
        //	fprintf(stderr, "%s\n", str.c_str());	
        //}
        //fprintf(stderr, "constraintsMPI.size() = %d", constraintsMPI.size());
        //fprintf(stderr, "\n\n\n");
        //fflush(stderr);

		set<var_t> tmp;
		typedef set<var_t>::const_iterator VarIt;

		// Build a graph on the variables, indicating a dependence when two
		// variables co-occur in a symbolic predicate.
		vector< set<var_t> > depends(vars.size());
		for (PredIt i = constraints.begin(); i != constraints.end(); ++i) {
			tmp.clear();
			(*i)->AppendVars(&tmp);
			for (VarIt j = tmp.begin(); j != tmp.end(); ++j) {
				//fprintf(stderr, "%d\n", j);
                //fflush(stderr);
                
                depends[*j].insert(tmp.begin(), tmp.end());
			}
		}

		// Initialize the set of dependent variables to those in the constraints.
		// (Assumption: Last element of constraints is the only new constraint.)
		// Also, initialize the queue for the BFS.
		map<var_t,type_t> dependent_vars;
		queue<var_t> Q;
		tmp.clear();
		//
		// hComment: get the last constraint and store all the variables into tmp
		//
		pointer2Last->AppendVars(&tmp);
		//
		// hComment: insert the variables used in the last constraint
		//
		for (VarIt j = tmp.begin(); j != tmp.end(); ++j) {
			dependent_vars.insert(*vars.find(*j));
			Q.push(*j);
		}
		// Run the BFS.
		while (!Q.empty()) {
			var_t i = Q.front();
			Q.pop();
			//
			// hComment: add the variable into the queue if it is relevant to
			// the last constraint
			//
			for (VarIt j = depends[i].begin(); j != depends[i].end(); ++j) {
				if (dependent_vars.find(*j) == dependent_vars.end()) {
					Q.push(*j);
					dependent_vars.insert(*vars.find(*j));
				}
			}
		}
		// Generate the list of dependent constraints
		vector<const SymbolicPred*> dependent_constraints;
		for (PredIt i = constraints.begin(); i != constraints.end(); ++i) {
			if ((*i)->DependsOn(dependent_vars))
				dependent_constraints.push_back(*i);
		}
            
        //
        // hEdit: print the constraints
        //
        fprintf(stderr, "dependent constraints\n");
        for (PredIt iter = dependent_constraints.begin(); iter < dependent_constraints.end(); iter++) {
        	string str;
        	(*iter)->AppendToString(&str);
        	fprintf(stderr, "%s\n", str.c_str());	
        }
        fprintf(stderr, "\n\n\n");
        fflush(stderr);

		
		soln->clear();
		if (Solve(dependent_vars, dependent_constraints, soln)) {

            // 
            // hEdit: print the target constraint
            // 
            string str;
            pointer2Last->AppendToString(&str);
            fprintf(stderr, "Target constraint: %s: YES\n", str.c_str());	
                    
			// Merge in the constrained variables.
			for (PredIt i = constraints.begin(); i != constraints.end(); ++i) {
				(*i)->AppendVars(&tmp);
			}
			
			//
			// hEdit: pop out the MPI constraints
			//
			for (size_t i = 0; i < constraintsMPI.size(); i++) {
				constraints.pop_back();
			}

            // 
			// hComment: if the variable is not present in the current solution, 
            // its old assignment from the old solution will be taken
			//
			for (set<var_t>::const_iterator i = tmp.begin(); i != tmp.end(); ++i) {
				if (soln->find(*i) == soln->end()) {
					soln->insert(make_pair(*i, old_soln[*i]));
				}
			}
		
			return true;
		}

        // 
        // hEdit: print the target constraint
        // 
        string str;
        pointer2Last->AppendToString(&str);
        fprintf(stderr, "Target constraint: %s: NO\n", str.c_str());	
		//
		// hEdit: pop out the MPI constraints
		//
		for (size_t i = 0; i < constraintsMPI.size(); i++) {
			constraints.pop_back();
		}
        
		return false;
	}

//////////////////////////////////////////////////////////////////////////////////////
   
    //
    // hEdit: exit gracefully in case of error
    //
    void exitf(const char* message) {
        fprintf(stderr,"BUG: %s.\n", message);
        exit(1);
    }

    //
    // hEdit: error handler
    //
    void error_handler(Z3_context ctx, Z3_error_code e) {
        fprintf(stderr, "Decoded error code: %s\n", Z3_get_error_msg(ctx, e) ); 
        exitf("incorrect use of Z3");
    }

    // 
    // hEdit: exit if unreachable code was reached
    //
    void unreachable() {
        exitf("unreachable code was reached");
    }

    Z3_solver mk_solver(Z3_context ctx) 
    {
        Z3_solver s = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, s);
        return s;
    }
    
    void del_solver(Z3_context ctx, Z3_solver s)
    {
        Z3_solver_dec_ref(ctx, s);
    }

    //
    // hEdit; create a logical context
    // 
    static Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err) {
        Z3_context ctx;

        // Enable model construction
        Z3_set_param_value(cfg, "MODEL", "true");
        // Create a context using the above configuration
        ctx = Z3_mk_context(cfg);
#ifdef TRACING
        // Enable tracing to stderr
        Z3_trace_to_stderr(ctx);
#endif
        // register an error handler
        Z3_set_error_handler(ctx, err);

        return ctx;
    }

    //
    // hEdit: create a logical context
    //
    static Z3_context mk_context() {
        Z3_config  cfg;
        Z3_context ctx;
        // Create a configuration
        cfg = Z3_mk_config();
        // Create a context
        ctx = mk_context_custom(cfg, error_handler);

        // Delete the configuration after the use of it
        Z3_del_config(cfg);

        return ctx;
    }

    //
    // hEdit: create a variable using the given name and type.
    //
    Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty) 
    {
        Z3_symbol   s  = Z3_mk_string_symbol(ctx, name); 
        // Declare and create a constant
        return Z3_mk_const(ctx, s, ty);
    }

    //
    // hEdit: create an integer variable using the given name.
    //
    Z3_ast mk_int_var(Z3_context ctx, const char * name) {
        // Create the integer type (a  machine integer can be represented 
        // using bit-vectors)
        Z3_sort ty = Z3_mk_int_sort(ctx);
        return mk_var(ctx, name, ty);
    }

    //
    // hEdit: create a Z3 integer node using a C int. 
    //
    Z3_ast mk_int(Z3_context ctx, int v) {
        Z3_sort ty = Z3_mk_int_sort(ctx);
        return Z3_mk_int(ctx, v, ty);
    }


/*
    //
    // hEdit: check whether the logical context is satisfiable, and compare 
    // the result with the expected result. If the context is satisfiable, 
    // then display the model.
    //
    void check(Z3_context ctx, Z3_lbool expected_result)
    {
        Z3_model m      = 0;
        // Check if the logical context is satisfiable or not
        Z3_lbool result = Z3_check_and_model_get(ctx, &m);
        switch (result) {
            case Z3_L_FALSE:
                printf("unsat\n");
                break;
            case Z3_L_UNDEF:
                printf("unknown\n");
                printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
                break;
            case Z3_L_TRUE:
                printf("sat\n%s\n", Z3_model_to_string(ctx, m));
                break;
        }
        if (m) {
            Z3_del_model(ctx, m);
        }
        if (result != expected_result) {
            exitf("unexpected result");
        }
    }

*/

    //
    // hEdit: display a symbol in the given output stream.
    //
    void display_symbol(Z3_context c, FILE * out, Z3_symbol s)
    {
        switch (Z3_get_symbol_kind(c, s)) {
            case Z3_INT_SYMBOL:
                fprintf(out, "#%d", Z3_get_symbol_int(c, s));
                break;
            case Z3_STRING_SYMBOL:
                fprintf(out, Z3_get_symbol_string(c, s));
                break;
            default:
                unreachable();
        }
    }

    //
    // hEdit: display the given type.
    //
    void display_sort(Z3_context c, FILE * out, Z3_sort ty)
    {
        switch (Z3_get_sort_kind(c, ty)) {
            case Z3_UNINTERPRETED_SORT:
                display_symbol(c, out, Z3_get_sort_name(c, ty));
                break;
            case Z3_BOOL_SORT:
                fprintf(out, "bool");
                break;
            case Z3_INT_SORT:
                fprintf(out, "int");
                break;
            case Z3_REAL_SORT:
                fprintf(out, "real");
                break;
            case Z3_BV_SORT:
                fprintf(out, "bv%d", Z3_get_bv_sort_size(c, ty));
                break;
            case Z3_ARRAY_SORT:
                fprintf(out, "[");
                display_sort(c, out, Z3_get_array_sort_domain(c, ty));
                fprintf(out, "->");
                display_sort(c, out, Z3_get_array_sort_range(c, ty));
                fprintf(out, "]");
                break;
            case Z3_DATATYPE_SORT:
                if (Z3_get_datatype_sort_num_constructors(c, ty) != 1)
                {
                    fprintf(out, "%s", Z3_sort_to_string(c,ty));
                    break;
                }
                {
                    unsigned num_fields = Z3_get_tuple_sort_num_fields(c, ty);
                    unsigned i;
                    fprintf(out, "(");
                    for (i = 0; i < num_fields; i++) {
                        Z3_func_decl field = Z3_get_tuple_sort_field_decl(c, ty, i);
                        if (i > 0) {
                            fprintf(out, ", ");
                        }
                        display_sort(c, out, Z3_get_range(c, field));
                    }
                    fprintf(out, ")");
                    break;
                }
            default:
                fprintf(out, "unknown[");
                display_symbol(c, out, Z3_get_sort_name(c, ty));
                fprintf(out, "]");
                break;
        }
    }

    //
    // hEdit: custom ast pretty printer. 
    // This function demonstrates how to use the API to navigate terms.
    //
    void display_ast(Z3_context c, FILE * out, Z3_ast v)
    {
        switch (Z3_get_ast_kind(c, v)) {
        case Z3_NUMERAL_AST: {
            Z3_sort t;
            fprintf(out, Z3_get_numeral_string(c, v));
            t = Z3_get_sort(c, v);
            fprintf(out, ":");
            display_sort(c, out, t);
            break;
        }
        case Z3_APP_AST: {
            unsigned i;
            Z3_app app = Z3_to_app(c, v);
            unsigned num_fields = Z3_get_app_num_args(c, app);
            Z3_func_decl d = Z3_get_app_decl(c, app);
            fprintf(out, Z3_func_decl_to_string(c, d));
            if (num_fields > 0) {
                fprintf(out, "[");
                for (i = 0; i < num_fields; i++) {
                    if (i > 0) {
                        fprintf(out, ", ");
                    }
                    display_ast(c, out, Z3_get_app_arg(c, app, i));
                }
                fprintf(out, "]");
            }
            break;
        }
        case Z3_QUANTIFIER_AST: {
            fprintf(out, "quantifier");
            ;
        }
        default:
            fprintf(out, "#unknown");
        }
    }

    //
    // hEdit: custom function interpretations pretty printer.
    //
    void display_function_interpretations(Z3_context c, FILE * out, Z3_model m)
    {
        unsigned num_functions, i;

        fprintf(out, "function interpretations:\n");

        num_functions = Z3_model_get_num_funcs(c, m);
        for (i = 0; i < num_functions; i++) {
            Z3_func_decl fdecl;
            Z3_symbol name;
            Z3_ast func_else;
            unsigned num_entries = 0, j;

            Z3_func_interp_opt finterp;

            fdecl = Z3_model_get_func_decl(c, m, i);
            finterp = Z3_model_get_func_interp(c, m, fdecl);
            Z3_func_interp_inc_ref(c, finterp);
            name = Z3_get_decl_name(c, fdecl);
            display_symbol(c, out, name);
            fprintf(out, " = {");
            if (finterp)
                num_entries = Z3_func_interp_get_num_entries(c, finterp);
            for (j = 0; j < num_entries; j++) {
                unsigned num_args, k;
                Z3_func_entry fentry = Z3_func_interp_get_entry(c, finterp, j);
                Z3_func_entry_inc_ref(c, fentry);
                if (j > 0) { 
                    fprintf(out, ", ");
                }
                num_args = Z3_func_entry_get_num_args(c, fentry);
                fprintf(out, "(");
                for (k = 0; k < num_args; k++) {
                    if (k > 0) { 
                        fprintf(out, ", ");
                    }
                    display_ast(c, out, Z3_func_entry_get_arg(c, fentry, k)); 
                }
                fprintf(out, "|->");
                display_ast(c, out, Z3_func_entry_get_value(c, fentry));
                fprintf(out, ")");
                Z3_func_entry_dec_ref(c, fentry);
            }
            if (num_entries > 0) { 
                fprintf(out, ", ");
            }
            fprintf(out, "(else|->");
            func_else = Z3_func_interp_get_else(c, finterp);
            display_ast(c, out, func_else);
            fprintf(out, ")}\n");
            Z3_func_interp_dec_ref(c, finterp);
        }    
    }


/*
void display_function_interpretations(Z3_context c, FILE * out, Z3_model m)
    {
        unsigned num_functions, i;

        fprintf(out, "function interpretations:\n");

        num_functions = Z3_model_get_num_funcs(c, m);
        for (i = 0; i < num_functions; i++) {
            Z3_func_decl fdecl;
            Z3_symbol name;
            Z3_ast func_else;
            unsigned num_entries, j;

            fdecl = Z3_model_get_func_decl(c, m, i);
            name = Z3_get_decl_name(c, fdecl);
            display_symbol(c, out, name);
            fprintf(out, " = {");
            num_entries = Z3_model_get_func_num_entries(c, m, i);
            for (j = 0; j < num_entries; j++) {
                unsigned num_args, k;
                if (j > 0) {
                    fprintf(out, ", ");
                }
                num_args = Z3_model_get_func_entry_num_args(c, m, i, j);
                fprintf(out, "(");
                for (k = 0; k < num_args; k++) {
                    if (k > 0) {
                        fprintf(out, ", ");
                    }
                    display_ast(c, out, Z3_model_get_func_entry_arg(c, m, i, j, k));
                }
                fprintf(out, "|->");
                display_ast(c, out, Z3_model_get_func_entry_value(c, m, i, j));
                fprintf(out, ")");
            }
            if (num_entries > 0) {
                fprintf(out, ", ");
            }
            fprintf(out, "(else|->");
            func_else = Z3_model_get_func_else(c, m, i);
            display_ast(c, out, func_else);
            fprintf(out, ")}\n");
        }
    }
 */
    //
    // hEdit: custom model pretty printer.
    //
    void display_model(Z3_context c, FILE * out, Z3_model m)
    {
        unsigned num_constants;
        unsigned i;

        if (!m) return;

        num_constants = Z3_model_get_num_consts(c, m);
        for (i = 0; i < num_constants; i++) {
            Z3_symbol name;
            Z3_func_decl cnst = Z3_model_get_const_decl(c, m, i);
            Z3_ast a, v;
            Z3_bool ok;
            name = Z3_get_decl_name(c, cnst);
            display_symbol(c, out, name);
            fprintf(out, " = ");
            a = Z3_mk_app(c, cnst, 0, 0);
            v = a;
            ok = Z3_model_eval(c, m, a, 1, &v);
            display_ast(c, out, v);
            fprintf(out, "\n");
        }
        display_function_interpretations(c, out, m);
    }

 
    /*
    void display_model(Z3_context c, FILE * out, Z3_model m)
    {
        unsigned num_constants;
        unsigned i;

        num_constants = Z3_model_get_num_constants(c, m);
        for (i = 0; i < num_constants; i++) {
            Z3_symbol name;
            Z3_func_decl cnst = Z3_model_get_constant(c, m, i);
            Z3_ast a, v;
            Z3_bool ok;
            name = Z3_get_decl_name(c, cnst);
            display_symbol(c, out, name);
            fprintf(out, " = ");
            a = Z3_mk_app(c, cnst, 0, 0);
            v = a;
            ok = Z3_eval(c, m, a, &v);
            display_ast(c, out, v);
            fprintf(out, "\n");
        }
        display_function_interpretations(c, out, m);
    }
    */

//////////////////////////////////////////////////////////////////////////////////////

    static Z3_ast ParseStatement(Z3_context &ctx, map<var_t,Z3_ast>& vars, string& stmt, int *pos)
    {
        Z3_ast pred[2];
        Z3_ast ret;

        DEBUG(fprintf(stderr, "%d, %s: %s\n", *pos, __FUNCTION__, stmt.substr(*pos).c_str()));
        
//fprintf(stderr, "%d, %s: %s\n", *pos, __FUNCTION__, stmt.substr(*pos).c_str());
        
        while (*pos < stmt.size() && stmt[*pos] == ' ') *pos += 1;
        if (stmt[*pos] == '(') {
            /* statement */
            /* compare ops */
            *pos = *pos + 1;
            DEBUG(fprintf(stderr, "stmt[*pos] = %c\n", stmt[*pos]));
            if (!stmt.compare(*pos, 2, "= ")) {
                *pos = *pos + 2;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
                
                ret = Z3_mk_eq(ctx, pred[0], pred[1]);
            } else if (!stmt.compare(*pos, 2, "/=")) {
                *pos = *pos + 3;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
                
                ret = Z3_mk_eq(ctx, pred[0], pred[1]);
                ret = Z3_mk_not(ctx, ret);
            } else if (!stmt.compare(*pos, 2, "> ")) {
                *pos = *pos + 2;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
                
                ret = Z3_mk_gt(ctx, pred[0], pred[1]);
            } else if (!stmt.compare(*pos, 2, "<=")) {
                *pos = *pos + 3;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
                
                ret = Z3_mk_le(ctx, pred[0], pred[1]);
            } else if (!stmt.compare(*pos, 2, "< ")) {
                *pos = *pos + 2;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
                
                ret = Z3_mk_lt(ctx, pred[0], pred[1]);
            } else if (!stmt.compare(*pos, 2, ">=")) {
                *pos = *pos + 3;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
                
                ret = Z3_mk_ge(ctx, pred[0], pred[1]);
            } else if (!stmt.compare(*pos, 2, "+ ")) {
                *pos = *pos + 2;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
//fprintf(stderr, "left: %s\n", Z3_ast_to_string(ctx, pred[0]));
//fprintf(stderr, "right: %s\n", Z3_ast_to_string(ctx, pred[1]));
                
                ret = Z3_mk_add(ctx, 2, pred);
            } else if (!stmt.compare(*pos, 2, "- ")) {
                *pos = *pos + 2;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
//fprintf(stderr, "left: %s\n", Z3_ast_to_string(ctx, pred[0]));
//fprintf(stderr, "right: %s\n", Z3_ast_to_string(ctx, pred[1]));
                
                ret = Z3_mk_sub(ctx, 2, pred);
            } else if (!stmt.compare(*pos, 2, "* ")) {
                *pos = *pos + 2;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
//fprintf(stderr, "left: %s\n", Z3_ast_to_string(ctx, pred[0]));
//fprintf(stderr, "right: %s\n", Z3_ast_to_string(ctx, pred[1]));
//fflush(stderr); 
                
                ret = Z3_mk_mul(ctx, 2, pred);
            } 
            /*else if (!stmt.compare(*pos, 3, "div")) {
                *pos = *pos + 4;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
                ret = Z3_mk_div(ctx, pred[0], pred[1]);
            } else if (!stmt.compare(*pos, 3, "mod")) {
                *pos = *pos + 4;
                pred[0] = ParseStatement(ctx, vars, stmt, pos);
                pred[1] = ParseStatement(ctx, vars, stmt, pos);
                ret = Z3_mk_mod(ctx, pred[0], pred[1]);
            }*/
            else {
                fprintf(stderr, "ERROR: unknown commands: %s\n", stmt.c_str());
            }
            
//fprintf(stderr, "pos = %d\n", *pos);
            
            /* close the bracket */
            int start = *pos;
            int endpos = stmt.find(')', *pos) + 2;
            *pos += (endpos - start);
            //*pos = stmt.find(')', *pos) + 1;

        } else if(stmt[*pos] == 'x') {
            /* variable */
            var_t vid;
            int start = *pos;
            int end = stmt.find(' ', start);
            string val = stmt.substr(start+1, end-start);
            sscanf(val.c_str(), "%d", &vid);
            *pos =  *pos + (end - start) + 1;
//fprintf(stderr, "x%d\n", vid);
            
            ret = vars[vid];
        } else if(stmt[*pos] >= '0' && stmt[*pos] <= '9') {
            /* constant */
            Z3_sort ty;
            int start = *pos;
            int end = stmt.find(' ', start) + 1;
            *pos = end;
            //*pos = *pos + (end - start);
            string val = stmt.substr(start, end-start-1);
            
            if (val.find('.') == string::npos) ty = Z3_mk_int_sort(ctx);
            else ty = Z3_mk_real_sort(ctx);
            //else ty = Z3_mk_fpa_sort_64(ctx);

            ret = Z3_mk_numeral(ctx, const_cast<char*>(val.c_str()), ty);
        } else if (stmt[*pos] == '-' || stmt[*pos] == '+') {
            /* unary */
            Z3_sort ty;
            int start = *pos;
            int end = stmt.find(' ', start) + 1;
            *pos = end;
            string val = stmt.substr(start, end-start-1);

            if (val.find('.') == string::npos) ty = Z3_mk_int_sort(ctx);
            else ty = Z3_mk_real_sort(ctx);
            //else ty = Z3_mk_fpa_sort_64(ctx);

            ret = Z3_mk_numeral(ctx, const_cast<char*>(val.c_str()), ty);
        }
        
        DEBUG(fprintf(stderr, "pos: %d, AST: %s\n", *pos, Z3_ast_to_string(ctx, ret)));
        
        return ret;
    }

    bool Z3Solver::Solve(const map<var_t,type_t>& vars,
            const vector<const SymbolicPred*>& constraints,
            map<var_t,value_double_t>* soln) {

        typedef map<var_t,type_t>::const_iterator VarIt;

        // Create a logical context 
        Z3_context ctx_z3 = mk_context();
        assert(ctx_z3);
        // Create a solver
        Z3_solver slv_z3 = mk_solver(ctx_z3); 
        // Create an integer type
        Z3_sort int_ty_z3 = Z3_mk_int_sort(ctx_z3);
        Z3_sort real_ty_z3 = Z3_mk_real_sort(ctx_z3);
        //Z3_sort f32_ty_z3 = Z3_mk_fpa_sort_32(ctx_z3);
        //Z3_sort f64_ty_z3 = Z3_mk_fpa_sort_64(ctx_z3);

        // Type limits.
        vector<Z3_ast> min_expr_z3(types::LONG_LONG+1);
        vector<Z3_ast> max_expr_z3(types::LONG_LONG+1);

        // Set limits for each data type (integer)
        for (int i = types::U_CHAR; i <= types::LONG_LONG; i++) {
            min_expr_z3[i] = Z3_mk_numeral(ctx_z3, 
                const_cast<char*>(kMinValueStr[i]), int_ty_z3);
            max_expr_z3[i] = Z3_mk_numeral(ctx_z3, 
                const_cast<char*>(kMaxValueStr[i]), int_ty_z3);
            assert(min_expr_z3[i]);
            assert(max_expr_z3[i]);
        }

        // Variable declarations.
        map<var_t,Z3_ast> x_expr_z3;

        for (VarIt i = vars.begin(); i != vars.end(); ++i) {
            
            char buff[32];
            Z3_ast min, max;
            // Set a name for the current variable
            snprintf(buff, sizeof(buff), "x%d", i->first);
            
            if (i->second == types::FLOAT || i->second == types::DOUBLE) { 
                // Create an floating point  variable 
                x_expr_z3[i->first] = mk_var(ctx_z3, buff, real_ty_z3);
                continue;
            } else {
                // Create an integer variable 
                x_expr_z3[i->first] = mk_var(ctx_z3, buff, int_ty_z3);
            }
            // Set limits for the current variable
            min = Z3_mk_ge(ctx_z3, x_expr_z3[i->first], min_expr_z3[i->second]);
            max = Z3_mk_le(ctx_z3, x_expr_z3[i->first], max_expr_z3[i->second]);

#if USE_RANGE_CHECK
            // Assert the two constraints into the logical context
            Z3_solver_assert(ctx_z3, slv_z3, min);
            Z3_solver_assert(ctx_z3, slv_z3, max);
            DEBUG(fprintf(stderr, "MIN AST: %s\n", Z3_ast_to_string(ctx_z3, min)));
            DEBUG(fprintf(stderr, "MAX AST: %s\n", Z3_ast_to_string(ctx_z3, max)));
#endif
        }
        
        // Create an integer "0"
        Z3_ast zero_z3 = mk_int(ctx_z3, 0);
        assert(zero_z3);
        { 
            // Constraints.
            vector<Z3_ast> terms_z3;
            for (PredIt i = constraints.begin(); i != constraints.end(); ++i) {
                // const SymbolicExpr& se = (*i)->expr();

                string s = "";
                (*i)->AppendToString(&s);
                DEBUG(fprintf(stderr, "pred: %s\n", s.c_str()));

                int pos = 0;
                Z3_ast pred_z3 = ParseStatement(ctx_z3, x_expr_z3, s, &pos);
                DEBUG(fprintf(stderr, "CHECK AST: %s\n", 
                    Z3_ast_to_string(ctx_z3, pred_z3)));
                
                Z3_solver_assert(ctx_z3, slv_z3, pred_z3);
            }
        }

        Z3_model model_z3 = 0;
        // Check if the logical context is satisfiable
        Z3_lbool success_z3 = Z3_solver_check(ctx_z3, slv_z3);

        // Constraint set is satisfiable
        if (Z3_L_TRUE == success_z3) {
            
            model_z3 = Z3_solver_get_model(ctx_z3, slv_z3);

            // Get the number of constants assigned by the model
            int num_constraints = Z3_model_get_num_consts(ctx_z3, model_z3);
//fprintf(stderr, "Entering solver: %d\n", num_constraints);
            
            for (int i = 0; i < num_constraints; i++) {
                int idx;
                double val;
                Z3_symbol name;
                Z3_ast a, v;
                Z3_bool ok;

                // Get the i-th constant in the model
                Z3_func_decl cnst = Z3_model_get_const_decl(ctx_z3, model_z3, i);
                DEBUG(display_model(ctx_z3, stderr, model_z3));

                // Get the constant declaration name 
                name = Z3_get_decl_name(ctx_z3, cnst);
                // Create a constant
                a = Z3_mk_app(ctx_z3, cnst, 0, 0);
                v = a;
                ok = Z3_model_eval(ctx_z3, model_z3, a, Z3_FALSE, &v);
                sscanf(Z3_get_symbol_string(ctx_z3, name), "x%d", &idx);
                
                if (vars[idx] == types::FLOAT || vars[idx] == types::DOUBLE)
                    val = strtod(Z3_get_numeral_decimal_string(ctx_z3, v, 15), NULL);
                else val = strtoll(Z3_get_numeral_decimal_string(ctx_z3, v, 15), NULL, 0);

                DEBUG(fprintf(stderr, "%s %s | x%d %lf\n",
                            Z3_get_symbol_string(ctx_z3, name),
                            Z3_get_numeral_decimal_string(ctx_z3, v, 15),
                            idx, val));
                soln->insert(make_pair(idx, val));
//fprintf(stderr, "sat: %d, %lf\n", idx, val);

            }
        } else if (success_z3 == Z3_L_FALSE) {
            DEBUG(fprintf(stderr, "ERR:  fail to solve\n"));
        } else {
            DEBUG(fprintf(stderr, "ERR: unknown\n"));
            DEBUG(display_model(ctx_z3, stderr, model_z3));
        }

        del_solver(ctx_z3, slv_z3);
        Z3_del_context(ctx_z3);
        
        return Z3_L_TRUE == success_z3;
    }
}  // namespace crest
