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
#include <cmath>
#include <fstream>
#include <functional>
#include <limits>
#include <stdio.h>
#include <stdlib.h>
#include <queue>
#include <utility>
#include <iostream>
#include <ctime>
#include <sys/wait.h>
#include <sys/types.h>
#include <string>
#include <cstring>
#include <unistd.h>

#include "base/z3_solver.h"
#include "run_crest/concolic_search.h"

using std::binary_function;
using std::ifstream;
using std::ios;
using std::min;
using std::max;
using std::numeric_limits;
using std::pair;
using std::queue;
using std::random_shuffle;
using std::stable_sort;

// 
// hEdit: set the time limit for a command running
//
long long TIMEOUT_IN_SECONDS = 120;

float solver_time = 0.0;

size_t threshold = 100;

namespace crest {

    namespace {

        typedef pair<size_t, int> ScoredBranch;

        struct ScoredBranchComp: public binary_function<ScoredBranch, ScoredBranch, bool> {
            bool operator()(const ScoredBranch& a, const ScoredBranch& b) const {
                return (a.second < b.second);
            }
        };

    }  // namespace

	////////////////////////////////////////////////////////////////////////
	//// Search ////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////

	Search::Search(const string& program, int max_iterations, int comm_world_size,
        int target_rank) : program_(program), max_iters_(max_iterations), num_iters_(0), 
        is_first_run(true),  comm_world_size_(comm_world_size),
        target_rank_(target_rank), solver(new Z3Solver()),
        execution_tag_(0) {

        start_time_ = time(NULL);

        { // Read in the set of branches.
            max_branch_ = 0;
            max_function_ = 0;
            branches_.reserve(100000);
            branch_count_.reserve(100000);
            branch_count_.push_back(0);

            ifstream in("branches");
            assert(in);
            function_id_t fid;
            int numBranches;
            while (in >> fid >> numBranches) {
                branch_count_.push_back(2 * numBranches);
                branch_id_t b1, b2;
                for (int i = 0; i < numBranches; i++) {
                    assert(in >> b1 >> b2);
                    branches_.push_back(b1);
                    branches_.push_back(b2);
                    max_branch_ = max(max_branch_, max(b1, b2));
                }
            }
            in.close();
            max_branch_++;
            max_function_ = branch_count_.size();
        }

        // Compute the paired-branch map.
        paired_branch_.resize(max_branch_);
        for (size_t i = 0; i < branches_.size(); i += 2) {
            paired_branch_[branches_[i]] = branches_[i + 1];
            paired_branch_[branches_[i + 1]] = branches_[i];
        }

        // Compute the branch-to-function map.
        branch_function_.resize(max_branch_);
        {
            size_t i = 0;
            for (function_id_t j = 0; j < branch_count_.size(); j++) {
                for (size_t k = 0; k < branch_count_[j]; k++) {
                    branch_function_[branches_[i++]] = j;
                }
            }
        }

        // Initialize all branches to "uncovered" (and functions to "unreached").
        total_num_covered_ = num_covered_ = 0;
        reachable_functions_ = reachable_branches_ = 0;
        covered_.resize(max_branch_, false);
        total_covered_.resize(max_branch_, false);
        reached_.resize(max_function_, false);

#if 1
        { // Read in any previous coverage (for faster debugging).
            ifstream in("coverage");
            branch_id_t bid;
            while (in >> bid) {
                covered_[bid] = true;
                num_covered_ ++;
                if (!reached_[branch_function_[bid]]) {
                    reached_[branch_function_[bid]] = true;
                    reachable_functions_ ++;
                    reachable_branches_ += branch_count_[branch_function_[bid]];
                }
            }

            total_num_covered_ = num_covered_;
            total_covered_ = covered_;
        }
#endif

        // Print out the initial coverage.
        fprintf(stderr,
                "Iteration 0 (0s): covered %u branches [%u reach funs, %u reach branches].\n",
                num_covered_, reachable_functions_, reachable_branches_);

        // Sort the branches.
        sort(branches_.begin(), branches_.end());


        outfile_illegal_inputs.open("illegal_inputs");
    }

	Search::~Search() {
		outfile_illegal_inputs.close();
		delete solver;
	}

	int Search::hRand() {

		return rand() % 10000;
	}

/*
	//
	// hEdit: change the format of input file so that this format is
	// the same as that of our designated input file. Upon error, we 
	// can directly use this input file to reproduce the generated bug. 
	//
	void Search::WriteInputToFileOrDie_debug(const string& file,
			const vector<value_t>& input) {
		FILE* f = fopen(file.c_str(), "w");
		if (!f) {
			fprintf(stderr, "Failed to open %s.\n", file.c_str());
			perror("Error: ");
			exit(-1);
		}
		
		if (input.empty()) return;
		size_t i = 0, j = 0;	
		for (; j < input.size(); j++) {
			if (rank_indices_.find(i) == rank_indices_.end() && 
					world_size_indices_.find(i) == world_size_indices_.end() &&
					input[i] == input[j])
				continue;

			fprintf(f, "%lld  %lld\n", j - i, input[i]);
			i = j + 1;
		}
		if (j != i) fprintf(f, "%lld  %lld\n", j - i, input[i]);

		fclose(f);
	}
*/	

	void Search::WriteInputToFileOrDie(const string& file,
			const vector<value_double_t>& input) {
		FILE* f = fopen(file.c_str(), "w");
		if (!f) {
			fprintf(stderr, "Failed to open %s.\n", file.c_str());
			perror("Error: ");
			exit(-1);
		}
		
		for (size_t j = 0; j < input.size(); j++) {
			fprintf(f, "%.15lf\n", input[j]);
		}

		fclose(f);
	}

	void Search::WriteCoverageToFileOrDie(const string& file) {
		FILE* f = fopen(file.c_str(), "w");
		if (!f) {
			fprintf(stderr, "Failed to open %s.\n", file.c_str());
			perror("Error: ");
			exit(-1);
		}

		for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
			if (total_covered_[*i]) {
				fprintf(f, "%d\n", *i);
			}
		}

		fclose(f);
	}


    //
    // hEdit: pass synchronized inputs to all processes. The 
    // input is generated randomly for the first run, and 
    // then it is obtained from the TESTED process in later runs.
    //
    void Search::LaunchProgram(const vector<value_double_t>& inputs) {

        string program_clean = program_ + "_c";
        string command;

        // Fix the focus in the first threshold tests  
        if (!world_size_indices_.empty() &&
                inputs[*world_size_indices_.begin()] <= 16) {
            // determine the size of MPI_COMM_WORLD
            comm_world_size_ = inputs[*world_size_indices_.begin()];
        }
        if (num_iters_ > threshold && !rank_indices_.empty()) {
            // determine which MPI rank to be tested
            target_rank_ = inputs[*rank_indices_.begin()];
        }
        if(target_rank_ >= comm_world_size_) target_rank_ = 0;

        if (!is_first_run) WriteInputToFileOrDie("input", inputs);


        // assemble the command together
        char* command2[20];
        int i = 0;

        command2[i++] = "/usr/bin/mpirun";
        if (0 != target_rank_) {
            command2[i++] = "-np";
            command2[i++] = const_cast<char *> (
                    (std::to_string((long long)target_rank_)).c_str());
            command2[i++] = const_cast<char *> (program_clean.c_str());
            command2[i++] = ":";

            command2[i++] = "-np";
            command2[i++] = "1";
            command2[i++] = const_cast<char *> (program_.c_str());
            if (target_rank_ + 1 < comm_world_size_) {

                command2[i++] = ":";
                command2[i++] = "-np";
                command2[i++] = const_cast<char *> (
                        (std::to_string((long long)comm_world_size_
                                        - target_rank_ - 1)).c_str());
                command2[i++] = const_cast<char *> (program_clean.c_str());
            }
        } else {
            command2[i++] = "-np";
            command2[i++] = "1";
            command2[i++] = const_cast<char *> (program_.c_str());
            command2[i++] = ":";

            command2[i++] = "-np";
            command2[i++] = const_cast<char *> (
                    (std::to_string((long long)comm_world_size_
                                    - 1)).c_str());
            command2[i++] = const_cast<char *> (program_clean.c_str());
        }
        command2[i++] = NULL;

        std::ofstream outfile(".target_rank");
        outfile << target_rank_;
        outfile.close();

        for (int j = 0; j < i; j++) {
            fprintf(stderr, "%s ", command2[j]);
        }
        fprintf(stderr, "\n");

        int ret = 0;
        int id = fork();
        if (id < 0){
            fprintf(stderr, "failed to fork\n");
        } else if (id == 0) {
            fprintf(stderr, "Child\n");
            execv(command2[0], command2);
            exit(0);
        } else {
            int pid, status;
            bool time_over = false;
            time_t begin = time(NULL);
            while(waitpid(id, &status, WNOHANG) != -1) {
                if (time(NULL) - begin > TIMEOUT_IN_SECONDS) {
                    kill (id, 9);
                    time_over = true;
                }
            }
            if (time_over) {
                fprintf(stderr, "TIMEOUT: KILLED (%d)\n",
                        time(NULL) - begin);
                ret = -1;
                waitpid(id, &status, 0);
            } else if (WIFSIGNALED(status) != 0) {
                ret = -2;
            } else if (WIFEXITED(status) != 0) {
                ret = WEXITSTATUS(status);
            } else {
                ret = -3;
            }

            fprintf(stderr, "Parent\n");
        }
        // if the command is terminated by the specified timeout
        if (0 != ret) {
            // log the triggered input 
            outfile_illegal_inputs << num_iters_ <<
                "Return value" << ret << std::endl;
            outfile_illegal_inputs << command << std::endl << std::endl;
            string tmp("mv input input.");
            tmp += std::to_string(num_iters_);
            system(tmp.c_str() );
        }

        // debug
        command += "\n";
        is_first_run = false;
    }


/*    void Search::LaunchProgram(const vector<value_double_t>& inputs) {

        string program_clean = program_ + "_c";
        string command;

        // Temporary fix for a bug that occurs at a rare chance. This bug manifests as too many processes run. 
        int tmp_rank = target_rank_, tmp_size = comm_world_size_;
        // determine which MPI rank to be tested
        target_rank_ = rank_indices_.empty() ? target_rank_: inputs[*rank_indices_.begin()];
        // determine the size of MPI_COMM_WORLD
        comm_world_size_ = world_size_indices_.empty() ? comm_world_size_: inputs[*world_size_indices_.begin()];
        if (target_rank_ < 0 || target_rank_ >= tmp_size || tmp_size > 16) {
            target_rank_ = tmp_rank;
            comm_world_size_ = tmp_size; 
        }


        if (!is_first_run) WriteInputToFileOrDie("input", inputs);

        // assemble the command together
        if (0 != target_rank_) {
            command += "mpirun.mpich -np " + std::to_string((long long)target_rank_) + " "
                + program_clean + " : -np 1 " + program_;
            if (target_rank_ + 1 < comm_world_size_) {
                command += " : -np " + std::to_string((long long)comm_world_size_ - target_rank_ - 1)
                    + " " + program_clean;
            }
        } else {
            command += "mpirun.mpich -np 1 " + program_ + " : -np "
                + std::to_string((long long)comm_world_size_ - 1) + " " + program_clean;
        }

        std::ofstream outfile(".target_rank");
        outfile << target_rank_;
        outfile.close();

        // apply a time limit to a command
        command = string("timeout ") + string(std::to_string(TIMEOUT_IN_SECONDS) + "s ") + command;
        int status = system(command.c_str()); 

        // if the command is terminated by the specified timeout
        if (0 != status) {
            // log the triggered input 
            outfile_illegal_inputs << num_iters_ << "Return value" << status << std::endl;
            outfile_illegal_inputs << command << std::endl << std::endl;
            string tmp("mv input input.");
            tmp += std::to_string(num_iters_);
            system(tmp.c_str() );
        }

        // debug
        command += "\n";
        fprintf(stderr, "%s\n", command.c_str());
        //inputs_str += "\n";
        //fprintf(stdout, inputs_str.c_str());

        // Disable this branch in further runs 
        is_first_run = false;
        //}
    }
*/


	void Search::RunProgram(const vector<value_double_t>& inputs, SymbolicExecution* ex) {
		if (++num_iters_ > max_iters_) {
fprintf(stderr, "\nThe total time for constraint solving is %f seconds\n\n", solver_time);
			// TODO(jburnim): Devise a better system for capping the iterations.
			exit(0);
		}
		
		// 
		// hEdit: log out the the number of iterations that could be used as a tag 
		// to differentiate if two executions are the same or not
		//
		std::ofstream outfile(".num_iters");
		outfile << num_iters_;
		outfile.close();


		// Run the program.
		LaunchProgram(inputs);

		// Read the execution from the program.
		// Want to do this with sockets.  (Currently doing it with files.)
		ifstream in("szd_execution", ios::in | ios::binary);
		
		// 
		// hEdit: temporary fix for Bug (1): core dump at assert() 
		// that checks abnormal reading over a stream whose reason 
		// is suspected to that the size of available data to be 
		// read is less than expected. Note this fix spreads across 
		// multiple places. 
		//
		// Fix (1.c): replace assert to tolerate reading failure, 
		// i.e., only log the error and skip it. 
		//
		if (!in || !ex->Parse(in)) {
			fprintf(stderr, "szd_execution\n");
		}
		// assert(in && ex->Parse(in));
		in.close();

		/*
		   for (size_t i = 0; i < ex->path().branches().size(); i++) {
		   fprintf(stderr, "%d ", ex->path().branches()[i]);
		   }
		   fprintf(stderr, "\n");
		 */
		
		//
		// hEdit: debug
		// 
		fprintf(stderr, "\nThe size of the constraint set of the current "
			"execution is %zu\n", ex->path().constraints().size());
	}

	bool Search::UpdateCoverage(SymbolicExecution& ex) {
		return UpdateCoverage(ex, NULL);
		//return UpdateCoverageUponTarget(ex, NULL);
	}


	
	// 
	// hedit: update the coverage only based on all the MPI ranks
	// 
	bool Search::UpdateCoverage(SymbolicExecution& ex, 
        set<branch_id_t>* new_branches) {

		//
		// hEdit: merge all the branches being found
		//vector<SymbolicExecution> ex_all_others;
		vector<SymbolicExecution *> ex_all_others;
		string base_name("szd_execution"), extended_name;

		for (int i = 0; i < comm_world_size_; i++) {
			if (i == target_rank_) continue;

			//SymbolicExecution ex_tmp;
			SymbolicExecution * ex_tmp = new SymbolicExecution();
			extended_name = base_name + std::to_string((long long)i);

			ifstream in(extended_name.c_str(), ios::in | ios::binary);
		
			// 
			// hEdit: temporary fix for Bug (1): core dump at assert() 
			// that checks abnormal reading over a stream whose reason 
			// is suspected to that the size of available data to be 
			// read is less than expected. Note this fix spreads across 
			// multiple places. 
			//
			// Fix (1.d): as shown in Fix (1.c). 
			//
			//if (!in || !ex_tmp.ParseBranches(in)) {
			if (!in || !ex_tmp->ParseBranches(in)) {
				in.close();
				fprintf(stderr, "%s\n", extended_name.c_str());	
				continue;
			}
			// assert(in && ex_tmp.ParseBranches(in));
			
			in.close();

			ex_all_others.push_back(ex_tmp);
		}

		const unsigned int prev_covered_ = num_covered_;
		const vector<branch_id_t>& branches = ex.path().branches();
		
		for (BranchIt i = branches.begin(); i != branches.end(); ++i) {
			if ((*i > 0) && !covered_[*i]) {
				covered_[*i] = true;
				num_covered_++;
				if (new_branches) {
					new_branches->insert(*i);
				}
				if (!reached_[branch_function_[*i]]) {
					reached_[branch_function_[*i]] = true;
					reachable_functions_++;
					reachable_branches_ += branch_count_[branch_function_[*i]];
				}
			}
			if ((*i > 0) && !total_covered_[*i]) {
				total_covered_[*i] = true;
				total_num_covered_++;
			}
		}
		

		for (size_t j = 0; j < ex_all_others.size(); j++) {
			
			//const vector<branch_id_t>& branches = ex_all_others[j].path().branches();
			const vector<branch_id_t>& branches = ex_all_others[j]->path().branches();

			//
			// hEdit: debug
			//
			//printf("debug: branches_size = %d\n", branches.size());

			for (BranchIt i = branches.begin(); i != branches.end(); ++i) {
				if ((*i > 0) && !covered_[*i]) {
					covered_[*i] = true;
					num_covered_++;
					if (new_branches) {
						new_branches->insert(*i);
					}
					if (!reached_[branch_function_[*i]]) {
						reached_[branch_function_[*i]] = true;
						reachable_functions_++;
						reachable_branches_ += branch_count_[branch_function_[*i]];
					}
				}
				if ((*i > 0) && !total_covered_[*i]) {
					total_covered_[*i] = true;
					total_num_covered_++;
				}
			}
		} 

		for (size_t j = 0; j < ex_all_others.size(); j++) {
			delete ex_all_others[j];
		}

		fprintf(stderr,
				"Iteration %d (%lds): covered %u branches [%u reach funs, %u reach branches].\n",
				num_iters_, time(NULL) - start_time_, total_num_covered_,
				reachable_functions_, reachable_branches_);

		bool found_new_branch = (num_covered_ > prev_covered_);
		if (found_new_branch) {
			WriteCoverageToFileOrDie("coverage");
		}

		return found_new_branch;
	}



	// 
	// hedit: update the coverage only based on the target rank
	// 
	bool Search::UpdateCoverageUponTarget(SymbolicExecution& ex,
			set<branch_id_t>* new_branches) {

		// record the previous coverage
		const unsigned int prev_covered_ = num_covered_;
		// obtain the branches covered by the current execution
		const vector<branch_id_t>& branches = ex.path().branches();
		for (BranchIt i = branches.begin(); i != branches.end(); ++i) {
			if ((*i > 0) && !covered_[*i]) {
				covered_[*i] = true;
				num_covered_++;
				if (new_branches) {
					new_branches->insert(*i);
				}
				// if find this branch is in a new function
				if (!reached_[branch_function_[*i]]) {
					reached_[branch_function_[*i]] = true;
					reachable_functions_++;
					reachable_branches_ += branch_count_[branch_function_[*i]];
				}
			}
			if ((*i > 0) && !total_covered_[*i]) {
				total_covered_[*i] = true;
				total_num_covered_++;
			}
		}

		fprintf(stderr,
				"Iteration %d (%lds): covered %u branches [%u reach funs, %u reach branches].\n",
				num_iters_, time(NULL) - start_time_, total_num_covered_,
				reachable_functions_, reachable_branches_);

		bool found_new_branch = (num_covered_ > prev_covered_);
		if (found_new_branch) {
			WriteCoverageToFileOrDie("coverage");
		}

		return found_new_branch;
	}



	bool Search::SolveAtBranch(const SymbolicExecution& ex, size_t branch_idx,
			vector<value_double_t>* input) {

		const vector<SymbolicPred*>& constraints = ex.path().constraints();

		// Optimization: If any of the previous constraints are idential to the
		// branch_idx-th constraint, immediately return false.
		for (int i = static_cast<int>(branch_idx) - 1; i >= 0; i--) {
			if (constraints[branch_idx]->Equal(*constraints[i]))
				return false;
		}

		vector<const SymbolicPred*> cs(constraints.begin(),
				constraints.begin() + branch_idx + 1);
		map<var_t, value_double_t> soln;
		constraints[branch_idx]->Negate();

		if (execution_tag_ != ex.execution_tag_) {	
            //fprintf(stderr, "\nExecution tag: %zu -> %zu \n", execution_tag_, ex.execution_tag_);

			execution_tag_ = ex.execution_tag_;	

			world_size_indices_ = ex.world_size_indices_; 
			rank_indices_ = ex.rank_indices_;
			rank_non_default_comm_indices_ = ex.rank_non_default_comm_indices_;

			solver->GenerateConstraintsMPI(ex);
		}

        clock_t tmp_time = clock();
        // fprintf(stderr, "Yices . . . ");
        bool success = solver->IncrementalSolve(ex.inputs(), ex.vars(), cs,
                &soln);
        tmp_time = clock() - tmp_time;
        solver_time += (float)tmp_time / CLOCKS_PER_SEC;

        // fprintf(stderr, "%d\n", success);
		constraints[branch_idx]->Negate();

        if (success) {
            // Merge the solution with the previous input to get the next
            // input.  
            *input = ex.inputs();

            vector<value_t> original_rank_non_default;
            for (size_t i = 0; i < rank_non_default_comm_indices_.size(); i++) 
                original_rank_non_default.push_back(
                        (*input)[rank_non_default_comm_indices_[i]]);

            typedef map<var_t, value_double_t>::const_iterator SolnIt;
            for (SolnIt i = soln.begin(); i != soln.end(); ++i) {
                (*input)[i->first] = i->second;

                for (size_t i = 0; i < rank_non_default_comm_indices_.size(); i++) {
                    if (original_rank_non_default[i] != 
                            (*input)[rank_non_default_comm_indices_[i]]){

                        int x = i;
                        int y = (*input)[rank_non_default_comm_indices_[i]];

//fprintf(stderr, "x: %d, y:%d\n", x, y);
//fprintf(stderr, "x*:%d\n", ex.rank_non_default_comm_map_.size());
//for (int i = 0; i < ex.rank_non_default_comm_map_.size(); i++)
//fprintf(stderr, "y*:%d\n", ex.rank_non_default_comm_map_[i].size());
//fflush(stderr);
                        int global_rank = ex.rank_non_default_comm_map_[x][y];

                        //if (!rank_indices_.empty()) 
                        for (size_t i = 0; i < rank_indices_.size(); i++) {
                            (*input)[rank_indices_[i]] = global_rank;
                        }
                        break;
                    }	
                }
            }
            return true;
        }

		return false;
	}

	bool Search::CheckPrediction(const SymbolicExecution& old_ex,
			const SymbolicExecution& new_ex, size_t branch_idx) {

		if ((old_ex.path().branches().size() <= branch_idx)
				|| (new_ex.path().branches().size() <= branch_idx)) {
			return false;
		}

		for (size_t j = 0; j < branch_idx; j++) {
			if (new_ex.path().branches()[j] != old_ex.path().branches()[j]) {
				return false;
			}
		}
		return (new_ex.path().branches()[branch_idx]
				== paired_branch_[old_ex.path().branches()[branch_idx]]);
	}

	////////////////////////////////////////////////////////////////////////
	//// BoundedDepthFirstSearch ///////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////

	BoundedDepthFirstSearch::BoundedDepthFirstSearch(const string& program,
			int max_iterations, int comm_world_size, int target_rank, int max_depth) :
		Search(program, max_iterations, comm_world_size, target_rank), max_depth_(
				max_depth) {
		}

	BoundedDepthFirstSearch::~BoundedDepthFirstSearch() {
	}

	void BoundedDepthFirstSearch::Run() {
		// Initial execution (on empty/random inputs).
		SymbolicExecution ex;
		RunProgram(vector<value_double_t>(), &ex);
		UpdateCoverage(ex);

		while (true) {
			DFS(0, max_depth_, ex);
		// DFS(0, ex);
		}
	}

/*
void BoundedDepthFirstSearch::DFS(int depth, SymbolicExecution& prev_ex) {
SymbolicExecution cur_ex;
vector<value_t> input;

const SymbolicPath& path = prev_ex.path();

int last = min(max_depth_, static_cast<int>(path.constraints().size()) - 1);
for (int i = last; i >= depth; i--) {
// Solve constraints[0..i].
if (!SolveAtBranch(prev_ex, i, &input)) {
continue;
}

// Run on those constraints.
RunProgram(input, &cur_ex);
UpdateCoverage(cur_ex);

// Check for prediction failure.
size_t branch_idx = path.constraints_idx()[i];
if (!CheckPrediction(prev_ex, cur_ex, branch_idx)) {
fprintf(stderr, "Prediction failed!\n");
continue;
}

// Recurse.
DFS(i+1, cur_ex);
}
}
*/

	void BoundedDepthFirstSearch::DFS(size_t pos, int depth,
			SymbolicExecution& prev_ex) {
		SymbolicExecution cur_ex;
		vector<value_double_t> input;

		const SymbolicPath& path = prev_ex.path();

		for (size_t i = pos; (i < path.constraints().size()) && (depth > 0); i++) {
			// Solve constraints[0..i].
			if (!SolveAtBranch(prev_ex, i, &input)) {
//fprintf(stderr, "FAIL: %u\n", i);
				continue;
			}
//fprintf(stderr, "SUCCESS: %u\n", i);

			// Run on those constraints.
			RunProgram(input, &cur_ex);
			UpdateCoverage(cur_ex);

			// Check for prediction failure.
			size_t branch_idx = path.constraints_idx()[i];
			if (!CheckPrediction(prev_ex, cur_ex, branch_idx)) {
				fprintf(stderr, "Prediction failed!\n");
				continue;
			}

			// We successfully solved the branch, recurse.
			depth--;

            DFS(i + 1, depth, cur_ex);
		}
	}

////////////////////////////////////////////////////////////////////////
//// RandomInputSearch /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

	RandomInputSearch::RandomInputSearch(const string& program, int max_iterations,
			int comm_world_size, int target_rank) :
		Search(program, max_iterations, comm_world_size, target_rank) {
		
		world_size_index = -1;
		world_size_max = 10;
	}

	RandomInputSearch::~RandomInputSearch() {
	}

	void RandomInputSearch::Run() {
		vector<value_double_t> input;
		RunProgram(input, &ex_);

		while (true) {
			UpdateCoverage(ex_);
			if (!ex_.world_size_indices_.empty()) {
				world_size_index = ex_.world_size_indices_[0];
			}
			RandomInput(ex_.vars(), &input);
			RunProgram(input, &ex_);
		}
	}


	void RandomInputSearch::RandomInput(const map<var_t, type_t>& vars,
			vector<value_double_t>* input) {
		input->resize(vars.size());

		for (map<var_t, type_t>::const_iterator it = vars.begin(); it != vars.end();
				++it) {
			unsigned long long val = 0;

			for (size_t j = 0; j < 8; j++)
				val = (val << 8) + (rand() / 256);
				//val = (val << 8) + (hRand() / 256);

			if (it->first == world_size_index) {
				// world_size_max must be smaller than 128 under
				// our assumption
				input->at(it->first) = val % world_size_max;
				continue;
			}

			switch (it->second) {
				case types::U_CHAR:
					input->at(it->first) = (unsigned char) val;
					break;
				case types::CHAR:
					input->at(it->first) = (char) val;
					break;
				case types::U_SHORT:
					input->at(it->first) = (unsigned short) val;
					break;
				case types::SHORT:
					input->at(it->first) = (short) val;
					break;
				case types::U_INT:
					input->at(it->first) = (unsigned int) val;
					break;
				case types::INT:
					input->at(it->first) = (int) val;
					break;
				case types::U_LONG:
					input->at(it->first) = (unsigned long) val;
					break;
				case types::LONG:
					input->at(it->first) = (long) val;
					break;
				case types::U_LONG_LONG:
					input->at(it->first) = (unsigned long long) val;
					break;
				case types::LONG_LONG:
					input->at(it->first) = (long long) val;
					break;
				case types::FLOAT:
					input->at(it->first) = (float) val;
					break;
				case types::DOUBLE:
					input->at(it->first) = (double) val;
					break;
			}
		}
	}
////////////////////////////////////////////////////////////////////////
//// RandomSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

	RandomSearch::RandomSearch(const string& program, int max_iterations,
			int comm_world_size, int target_rank) :
		Search(program, max_iterations, comm_world_size, target_rank) {
	}

	RandomSearch::~RandomSearch() {
	}

	void RandomSearch::Run() {
		SymbolicExecution next_ex;

		while (true) {
			// Execution (on empty/random inputs).
			fprintf(stderr, "RESET\n");
			vector<value_double_t> next_input;
			RunProgram(next_input, &ex_);
			UpdateCoverage(ex_);

			// Do some iterations.
			int count = 0;
			while (count++ < 10000) {
				// fprintf(stderr, "Uncovered bounded DFS.\n");
				// SolveUncoveredBranches(0, 20, ex_);

				size_t idx;
				if (SolveRandomBranch(&next_input, &idx)) {
					RunProgram(next_input, &next_ex);
					bool found_new_branch = UpdateCoverage(next_ex);
					bool prediction_failed = !CheckPrediction(ex_, next_ex,
							ex_.path().constraints_idx()[idx]);

					if (found_new_branch) {
						count = 0;
						ex_.Swap(next_ex);
						if (prediction_failed)
							fprintf(stderr, "Prediction failed (but got lucky).\n");
					} else if (!prediction_failed) {
						ex_.Swap(next_ex);
					} else {
						fprintf(stderr, "Prediction failed.\n");
					}
				}
			}
		}
	}


	bool RandomSearch::SolveRandomBranch(vector<value_double_t>* next_input, size_t* idx) {

		vector<size_t> idxs(ex_.path().constraints().size());
		for (size_t i = 0; i < idxs.size(); i++)
			idxs[i] = i;

		for (int tries = 0; tries < 1000; tries++) {
			// Pick a random index.
			if (idxs.size() == 0)
				break;
			size_t r = rand() % idxs.size();
			size_t i = idxs[r];
			swap(idxs[r], idxs.back());
			idxs.pop_back();

			if (SolveAtBranch(ex_, i, next_input)) {
				fprintf(stderr, "Solved %zu/%zu\n", i, idxs.size());
				*idx = i;
				return true;
			}
//fprintf(stderr, "Tries %d times\n", tries);
		}

		// We failed to solve a branch, so reset the input.
		fprintf(stderr, "FAIL\n");
		next_input->clear();
		return false;
	}

/*
// junk code at the beginning of the above function
const SymbolicPath& p = ex_.path();
vector<ScoredBranch> zero_branches, other_branches;
zero_branches.reserve(p.constraints().size());
other_branches.reserve(p.constraints().size());

vector<size_t> idxs(p.constraints().size());
for (size_t i = 0; i < idxs.size(); i++) {
idxs[i] = i;
}
random_shuffle(idxs.begin(), idxs.end());

vector<int> seen(max_branch_);
for (vector<size_t>::const_iterator i = idxs.begin(); i != idxs.end(); ++i) {
branch_id_t bid = p.branches()[p.constraints_idx()[*i]];
if (!covered_[paired_branch_[bid]]) {
zero_branches.push_back(make_pair(*i, seen[bid]));
} else {
other_branches.push_back(make_pair(*i, seen[bid]));
}
seen[bid] += 1;
}

stable_sort(zero_branches.begin(), zero_branches.end(), ScoredBranchComp());

int tries = 1000;
for (size_t i = 0; (i < zero_branches.size()) && (tries > 0); i++, tries--) {
if (SolveAtBranch(ex_, zero_branches[i].first, next_input))
return;
}

stable_sort(other_branches.begin(), other_branches.end(), ScoredBranchComp());
for (size_t i = 0; (i < other_branches.size()) && (tries > 0); i++, tries--) {
if (SolveAtBranch(ex_, other_branches[i].first, next_input))
return;
}
*/

	void RandomSearch::SolveUncoveredBranches(size_t i, int depth,
			const SymbolicExecution& prev_ex) {
		if (depth < 0)
			return;

		fprintf(stderr, "position: %zu/%zu (%d)\n", i,
				prev_ex.path().constraints().size(), depth);

		SymbolicExecution cur_ex;
		vector<value_double_t> input;

		int cnt = 0;

		for (size_t j = i; j < prev_ex.path().constraints().size(); j++) {
			size_t bid_idx = prev_ex.path().constraints_idx()[j];
			branch_id_t bid = prev_ex.path().branches()[bid_idx];
			if (covered_[paired_branch_[bid]])
				continue;

			if (!SolveAtBranch(prev_ex, j, &input)) {
				if (++cnt == 1000) {
					cnt = 0;
					fprintf(stderr, "Failed to solve at %zu/%zu.\n", j,
							prev_ex.path().constraints().size());
				}
				continue;
			}
			cnt = 0;

			RunProgram(input, &cur_ex);
			UpdateCoverage(cur_ex);
			if (!CheckPrediction(prev_ex, cur_ex, bid_idx)) {
				fprintf(stderr, "Prediction failed.\n");
				continue;
			}

			SolveUncoveredBranches(j + 1, depth - 1, cur_ex);
		}
	}


/*
   bool RandomSearch::SolveUncoveredBranches(SymbolicExecution& prev_ex) {
   SymbolicExecution cur_ex;
   vector<value_t> input;

   bool success = false;

   int cnt = 0;

   for (size_t i = 0; i < prev_ex.path().constraints().size(); i++) {

   size_t bid_idx = prev_ex.path().constraints_idx()[i];
   branch_id_t bid = prev_ex.path().branches()[bid_idx];
   if (covered_[paired_branch_[bid]])
   continue;

   if (!SolveAtBranch(prev_ex, i, &input)) {
   if (++cnt == 1000) {
   cnt = 0;
   fprintf(stderr, "Failed to solve at %u/%u.\n",
   i, prev_ex.path().constraints().size());
   }
   continue;
   }
   cnt = 0;

   RunProgram(input, &cur_ex);
   UpdateCoverage(cur_ex);
   if (!CheckPrediction(prev_ex, cur_ex, bid_idx)) {
   fprintf(stderr, "Prediction failed.\n");
   continue;
   }

   success = true;
   cur_ex.Swap(prev_ex);
   }

   return success;
   }
 */



////////////////////////////////////////////////////////////////////////
//// RandomSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

	UniformRandomSearch::UniformRandomSearch(const string& program,
		int max_iterations, int comm_world_size, int target_rank, size_t max_depth) :
		Search(program, max_iterations, comm_world_size, target_rank), max_depth_(
			max_depth) {
	}

	UniformRandomSearch::~UniformRandomSearch() {
	}

	void UniformRandomSearch::Run() {
		// Initial execution (on empty/random inputs).
		RunProgram(vector<value_double_t>(), &prev_ex_);
		UpdateCoverage(prev_ex_);

		while (true) {
			fprintf(stderr, "RESET\n");

			// Uniform random path.
			DoUniformRandomPath();
		}
	}

	void UniformRandomSearch::DoUniformRandomPath() {
		vector<value_double_t> input;

		size_t i = 0;
		size_t depth = 0;
		fprintf(stderr, "%zu constraints.\n", prev_ex_.path().constraints().size());
		while ((i < prev_ex_.path().constraints().size()) && (depth < max_depth_)) {
			if (SolveAtBranch(prev_ex_, i, &input)) {
				fprintf(stderr, "Solved constraint %zu/%zu.\n", (i + 1),
						prev_ex_.path().constraints().size());
				depth++;

				// With probability 0.5, force the i-th constraint.
				if (rand() % 2 == 0) {
					RunProgram(input, &cur_ex_);
					UpdateCoverage(cur_ex_);
					size_t branch_idx = prev_ex_.path().constraints_idx()[i];
					if (!CheckPrediction(prev_ex_, cur_ex_, branch_idx)) {
						fprintf(stderr, "prediction failed\n");
						depth--;
					} else {
						cur_ex_.Swap(prev_ex_);
					}
				}
			}

			i++;
		}
	}

////////////////////////////////////////////////////////////////////////
//// HybridSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

	HybridSearch::HybridSearch(const string& program, int max_iterations,
			int comm_world_size, int target_rank, int step_size) :
		Search(program, max_iterations, comm_world_size, target_rank), step_size_(
				step_size) {
	}

	HybridSearch::~HybridSearch() {
	}

	void HybridSearch::Run() {
		SymbolicExecution ex;

		while (true) {
			// Execution on empty/random inputs.
			RunProgram(vector<value_double_t>(), &ex);
			UpdateCoverage(ex);

			// Local searches at increasingly deeper execution points.
			for (size_t pos = 0; pos < ex.path().constraints().size(); pos +=
					step_size_) {
				RandomLocalSearch(&ex, pos, pos + step_size_);
			}
		}
	}

	void HybridSearch::RandomLocalSearch(SymbolicExecution *ex, size_t start,
			size_t end) {
		for (int iters = 0; iters < 100; iters++) {
			if (!RandomStep(ex, start, end))
				break;
		}
	}

	bool HybridSearch::RandomStep(SymbolicExecution *ex, size_t start, size_t end) {

		if (end > ex->path().constraints().size()) {
			end = ex->path().constraints().size();
		}
		assert(start < end);

		SymbolicExecution next_ex;
		vector<value_double_t> input;

		fprintf(stderr, "%zu-%zu\n", start, end);
		vector<size_t> idxs(end - start);
		for (size_t i = 0; i < idxs.size(); i++) {
			idxs[i] = start + i;
		}

		for (int tries = 0; tries < 1000; tries++) {
			// Pick a random index.
			if (idxs.size() == 0)
				break;
			size_t r = rand() % idxs.size();
			size_t i = idxs[r];
			swap(idxs[r], idxs.back());
			idxs.pop_back();

			if (SolveAtBranch(*ex, i, &input)) {
				RunProgram(input, &next_ex);
				UpdateCoverage(next_ex);
				if (CheckPrediction(*ex, next_ex,
							ex->path().constraints_idx()[i])) {
					ex->Swap(next_ex);
					return true;
				}
			}
		}

		return false;
	}

////////////////////////////////////////////////////////////////////////
//// CfgBaselineSearch /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

	CfgBaselineSearch::CfgBaselineSearch(const string& program, int max_iterations,
			int comm_world_size, int target_rank) :
		Search(program, max_iterations, comm_world_size, target_rank) {
		}

	CfgBaselineSearch::~CfgBaselineSearch() {
	}

	void CfgBaselineSearch::Run() {
		SymbolicExecution ex;

		while (true) {
			// clear the state of MPI info used at launching time
			rank_indices_.clear();
			world_size_indices_.clear();
			
			// Execution on empty/random inputs.
			fprintf(stderr, "RESET\n");
			RunProgram(vector<value_double_t>(), &ex);
			UpdateCoverage(ex);

			while (DoSearch(5, 250, 0, ex)) {
				// As long as we keep finding new branches . . . .
				ex.Swap(success_ex_);
			}
		}
	}

	bool CfgBaselineSearch::DoSearch(int depth, int iters, int pos,
			const SymbolicExecution& prev_ex) {

		// For each symbolic branch/constraint in the execution path, we will
		// compute a heuristic score, and then attempt to force the branches
		// in order of increasing score.
		vector<ScoredBranch> scoredBranches(
				prev_ex.path().constraints().size() - pos);
		for (size_t i = 0; i < scoredBranches.size(); i++) {
			scoredBranches[i].first = i + pos;
		}

		{ // Compute (and sort by) the scores.
			random_shuffle(scoredBranches.begin(), scoredBranches.end());
			map<branch_id_t, int> seen;
			for (size_t i = 0; i < scoredBranches.size(); i++) {
				size_t idx = scoredBranches[i].first;
				size_t branch_idx = prev_ex.path().constraints_idx()[idx];
				branch_id_t bid =
					paired_branch_[prev_ex.path().branches()[branch_idx]];
				if (covered_[bid]) {
					scoredBranches[i].second = 100000000 + seen[bid];
				} else {
					scoredBranches[i].second = seen[bid];
				}
				seen[bid] += 1;
			}
		}
		stable_sort(scoredBranches.begin(), scoredBranches.end(),
				ScoredBranchComp());

		// Solve.
		SymbolicExecution cur_ex;
		vector<value_double_t> input;
		for (size_t i = 0; i < scoredBranches.size(); i++) {
			if (iters <= 0) {
				return false;
			}

			if (!SolveAtBranch(prev_ex, scoredBranches[i].first, &input)) {
				continue;
			}

			RunProgram(input, &cur_ex);
			iters--;

			if (UpdateCoverage(cur_ex, NULL)) {
				success_ex_.Swap(cur_ex);
				return true;
			}
		}

		return false;
	}

////////////////////////////////////////////////////////////////////////
//// CfgHeuristicSearch ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

	CfgHeuristicSearch::CfgHeuristicSearch(const string& program,
		int max_iterations, int comm_world_size, int target_rank) :
		Search(program, max_iterations, comm_world_size, target_rank), cfg_(
			max_branch_), cfg_rev_(max_branch_), dist_(max_branch_) {

		// Read in the CFG.
		ifstream in("cfg_branches", ios::in | ios::binary);
		assert(in);
		size_t num_branches;
		in.read((char*) &num_branches, sizeof(num_branches));
		assert(num_branches == branches_.size());
		for (size_t i = 0; i < num_branches; i++) {
			branch_id_t src;
			size_t len;
			in.read((char*) &src, sizeof(src));
			in.read((char*) &len, sizeof(len));
			cfg_[src].resize(len);
			in.read((char*) &cfg_[src].front(), len * sizeof(branch_id_t));
		}
		in.close();

		// Construct the reversed CFG.
		for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
			for (BranchIt j = cfg_[*i].begin(); j != cfg_[*i].end(); ++j) {
				cfg_rev_[*j].push_back(*i);
			}
		}
	}

	CfgHeuristicSearch::~CfgHeuristicSearch() {
	}

	void CfgHeuristicSearch::Run() {
		set<branch_id_t> newly_covered_;
		SymbolicExecution ex;

		while (true) {
			// clear the state of MPI info used at launching time
			rank_indices_.clear();
			world_size_indices_.clear();
			
			covered_.assign(max_branch_, false);
			//num_covered_ = 0;

			// Execution on empty/random inputs.
			fprintf(stderr, "RESET\n");
			RunProgram(vector<value_double_t>(), &ex);
			if (UpdateCoverage(ex)) {
				UpdateBranchDistances();
				PrintStats();
			}

			// while (DoSearch(3, 200, 0, kInfiniteDistance+10, ex)) {
			while (DoSearch(5, 30, 0, kInfiniteDistance, ex)) {
				// while (DoSearch(3, 10000, 0, kInfiniteDistance, ex)) {
				PrintStats();
				// As long as we keep finding new branches . . . .
				UpdateBranchDistances();
				ex.Swap(success_ex_);
			}
			PrintStats();
		}
	}

	bool CfgHeuristicSearch::DoSearch(int depth, int iters, int pos, int maxDist,
			const SymbolicExecution& prev_ex) {

		fprintf(stderr, "DoSearch(%d, %d, %d, %zu)\n", depth, pos, maxDist,
				prev_ex.path().branches().size());

		if (pos >= static_cast<int>(prev_ex.path().constraints().size()))
			return false;

		if (depth == 0)
			return false;

		// For each symbolic branch/constraint in the execution path, we will
		// compute a heuristic score, and then attempt to force the branches
		// in order of increasing score.
		vector<ScoredBranch> scoredBranches(
				prev_ex.path().constraints().size() - pos);
		for (size_t i = 0; i < scoredBranches.size(); i++) {
			scoredBranches[i].first = i + pos;
		}

		{ // Compute (and sort by) the scores.
			random_shuffle(scoredBranches.begin(), scoredBranches.end());
			map<branch_id_t, int> seen;
			for (size_t i = 0; i < scoredBranches.size(); i++) {
				size_t idx = scoredBranches[i].first;
				size_t branch_idx = prev_ex.path().constraints_idx()[idx];
				branch_id_t bid =
					paired_branch_[prev_ex.path().branches()[branch_idx]];

				scoredBranches[i].second = dist_[bid] + seen[bid];
				seen[bid] += 1;

				/*
				   if (dist_[bid] == 0) {
				   scoredBranches[i].second = 0;
				   } else {
				   scoredBranches[i].second = dist_[bid] + seen[bid];
				   seen[bid] += 1;
				   }
				 */
			}
		}
		stable_sort(scoredBranches.begin(), scoredBranches.end(),
				ScoredBranchComp());

		// Solve.
		SymbolicExecution cur_ex;
		vector<value_double_t> input;
		for (size_t i = 0; i < scoredBranches.size(); i++) {
			if ((iters <= 0) || (scoredBranches[i].second > maxDist))
				return false;

			num_inner_solves_++;

			if (!SolveAtBranch(prev_ex, scoredBranches[i].first, &input)) {
				num_inner_unsats_++;
				continue;
			}

			RunProgram(input, &cur_ex);
			iters--;

			size_t b_idx = prev_ex.path().constraints_idx()[scoredBranches[i].first];
			branch_id_t bid = paired_branch_[prev_ex.path().branches()[b_idx]];
			set<branch_id_t> new_branches;
			bool found_new_branch = UpdateCoverage(cur_ex, &new_branches);
			bool prediction_failed = !CheckPrediction(prev_ex, cur_ex, b_idx);

			if (found_new_branch && prediction_failed) {
				fprintf(stderr, "Prediction failed.\n");
				fprintf(stderr, "Found new branch by forcing at "
						"distance %zu (%d) [lucky, pred failed].\n", dist_[bid],
						scoredBranches[i].second);

				// We got lucky, and can't really compute any further stats
				// because prediction failed.
				num_inner_lucky_successes_++;
				num_inner_successes_pred_fail_++;
				success_ex_.Swap(cur_ex);
				return true;
			}

			if (found_new_branch && !prediction_failed) {
				fprintf(stderr,
						"Found new branch by forcing at distance %zu (%d).\n",
						dist_[bid], scoredBranches[i].second);
				size_t min_dist = MinCflDistance(b_idx, cur_ex, new_branches);
				// Check if we were lucky.
				if (FindAlongCfg(b_idx, dist_[bid], cur_ex, new_branches)) {
					assert(min_dist <= dist_[bid]);
					// A legitimate find -- return success.
					if (dist_[bid] == 0) {
						num_inner_zero_successes_++;
					} else {
						num_inner_nonzero_successes_++;
					}
					success_ex_.Swap(cur_ex);
					return true;
				} else {
					// We got lucky, but as long as there were no prediction failures,
					// we'll finish the CFG search to see if that works, too.
					assert(min_dist > dist_[bid]);
					assert(dist_[bid] != 0);
					num_inner_lucky_successes_++;
				}
			}

			if (prediction_failed) {
				fprintf(stderr, "Prediction failed.\n");
				if (!found_new_branch) {
					num_inner_pred_fails_++;
					continue;
				}
			}

			// If we reached here, then scoredBranches[i].second is greater than 0.
			num_top_solves_++;
			if ((dist_[bid] > 0)
					&& SolveAlongCfg(b_idx, scoredBranches[i].second - 1, cur_ex)) {
				num_top_solve_successes_++;
				PrintStats();
				return true;
			}

			if (found_new_branch) {
				success_ex_.Swap(cur_ex);
				return true;
			}

			/*
			   if (DoSearch(depth-1, 5, scoredBranches[i].first+1, scoredBranches[i].second-1, cur_ex)) {
			   num_inner_recursive_successes_ ++;
			   return true;
			   }
			 */
		}

		return false;
	}


	void CfgHeuristicSearch::PrintStats() {
		fprintf(stderr,
				"Cfg solves: %u/%u (%u lucky [%u continued], %u on 0's, %u on others,"
				"%u unsats, %u prediction failures)\n",
				(num_inner_lucky_successes_ + num_inner_zero_successes_
				 + num_inner_nonzero_successes_ + num_top_solve_successes_),
				num_inner_solves_, num_inner_lucky_successes_,
				(num_inner_lucky_successes_ - num_inner_successes_pred_fail_),
				num_inner_zero_successes_, num_inner_nonzero_successes_,
				num_inner_unsats_, num_inner_pred_fails_);
		fprintf(stderr, "    (recursive successes: %u)\n",
				num_inner_recursive_successes_);
		fprintf(stderr, "Top-level SolveAlongCfg: %u/%u\n",
				num_top_solve_successes_, num_top_solves_);
		fprintf(stderr,
				"All SolveAlongCfg: %u/%u  (%u all concrete, %u no paths)\n",
				num_solve_successes_, num_solves_, num_solve_all_concrete_,
				num_solve_no_paths_);
		fprintf(stderr,
				"    (sat failures: %u/%u)  (prediction failures: %u) (recursions: %u)\n",
				num_solve_unsats_, num_solve_sat_attempts_, num_solve_pred_fails_,
				num_solve_recurses_);
	}

	void CfgHeuristicSearch::UpdateBranchDistances() {
		// We run a BFS backward, starting simultaneously at all uncovered vertices.
		queue<branch_id_t> Q;
		for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
			if (!covered_[*i]) {
				dist_[*i] = 0;
				Q.push(*i);
			} else {
				dist_[*i] = kInfiniteDistance;
			}
		}

		while (!Q.empty()) {
			branch_id_t i = Q.front();
			size_t dist_i = dist_[i];
			Q.pop();

			for (BranchIt j = cfg_rev_[i].begin(); j != cfg_rev_[i].end(); ++j) {
				if (dist_i + 1 < dist_[*j]) {
					dist_[*j] = dist_i + 1;
					Q.push(*j);
				}
			}
		}
	}


	size_t CfgHeuristicSearch::MinCflDistance(size_t i, const SymbolicExecution& ex,
			const set<branch_id_t>& bs) {

		const vector<branch_id_t>& p = ex.path().branches();

		if (i >= p.size())
			return numeric_limits<size_t>::max();

		if (bs.find(p[i]) != bs.end())
			return 0;

		vector<size_t> stack;
		size_t min_dist = numeric_limits<size_t>::max();
		size_t cur_dist = 1;

		fprintf(stderr, "Found uncovered branches at distances:");
		for (BranchIt j = p.begin() + i + 1; j != p.end(); ++j) {
			if (bs.find(*j) != bs.end()) {
				min_dist = min(min_dist, cur_dist);
				fprintf(stderr, " %zu", cur_dist);
			}

			if (*j >= 0) {
				cur_dist++;
			} else if (*j == kCallId) {
				stack.push_back(cur_dist);
			} else if (*j == kReturnId) {
				if (stack.size() == 0)
					break;
				cur_dist = stack.back();
				stack.pop_back();
			} else {
				fprintf(stderr, "\nBad branch id: %d\n", *j);
				exit(1);
			}
		}

		fprintf(stderr, "\n");
		return min_dist;
	}

	bool CfgHeuristicSearch::FindAlongCfg(size_t i, unsigned int dist,
			const SymbolicExecution& ex, const set<branch_id_t>& bs) {

		const vector<branch_id_t>& path = ex.path().branches();

		if (i >= path.size())
			return false;

		branch_id_t bid = path[i];
		if (bs.find(bid) != bs.end())
			return true;

		if (dist == 0)
			return false;

		// Compute the indices of all branches on the path that immediately
		// follow the current branch (corresponding to the i-th constraint)
		// in the CFG. For example, consider the path:
		//     * ( ( ( 1 2 ) 4 ) ( 5 ( 6 7 ) ) 8 ) 9
		// where '*' is the current branch.  The branches immediately
		// following '*' are : 1, 4, 5, 8, and 9.
		vector<size_t> idxs;
		{
			size_t pos = i + 1;
			CollectNextBranches(path, &pos, &idxs);
		}

		for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end();
				++j) {
			if (FindAlongCfg(*j, dist - 1, ex, bs))
				return true;
		}

		return false;
	}

	bool CfgHeuristicSearch::SolveAlongCfg(size_t i, unsigned int max_dist,
			const SymbolicExecution& prev_ex) {
		num_solves_++;

		fprintf(stderr, "SolveAlongCfg(%zu,%u)\n", i, max_dist);
		SymbolicExecution cur_ex;
		vector<value_double_t> input;
		const vector<branch_id_t>& path = prev_ex.path().branches();

		// Compute the indices of all branches on the path that immediately
		// follow the current branch (corresponding to the i-th constraint)
		// in the CFG. For example, consider the path:
		//     * ( ( ( 1 2 ) 4 ) ( 5 ( 6 7 ) ) 8 ) 9
		// where '*' is the current branch.  The branches immediately
		// following '*' are : 1, 4, 5, 8, and 9.
		bool found_path = false;
		vector<size_t> idxs;
		{
			size_t pos = i + 1;
			CollectNextBranches(path, &pos, &idxs);
			// fprintf(stderr, "Branches following %d:", path[i]);
			for (size_t j = 0; j < idxs.size(); j++) {
				// fprintf(stderr, " %d(%u,%u,%u)", path[idxs[j]], idxs[j],
				//      dist_[path[idxs[j]]], dist_[paired_branch_[path[idxs[j]]]]);
				if ((dist_[path[idxs[j]]] <= max_dist)
						|| (dist_[paired_branch_[path[idxs[j]]]] <= max_dist))
					found_path = true;
			}
			//fprintf(stderr, "\n");
		}

		if (!found_path) {
			num_solve_no_paths_++;
			return false;
		}

		bool all_concrete = true;
		num_solve_all_concrete_++;

		// We will iterate through these indices in some order (random?
		// increasing order of distance? decreasing?), and try to force and
		// recurse along each one with distance no greater than max_dist.
		random_shuffle(idxs.begin(), idxs.end());
		for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end();
				++j) {
			// Skip if distance is wrong.
			if ((dist_[path[*j]] > max_dist)
					&& (dist_[paired_branch_[path[*j]]] > max_dist)) {
				continue;
			}

			if (dist_[path[*j]] <= max_dist) {
				// No need to force, this branch is on a shortest path.
				num_solve_recurses_++;
				if (SolveAlongCfg(*j, max_dist - 1, prev_ex)) {
					num_solve_successes_++;
					return true;
				}
			}

			// Find the constraint corresponding to branch idxs[*j].
			vector<size_t>::const_iterator idx = lower_bound(
					prev_ex.path().constraints_idx().begin(),
					prev_ex.path().constraints_idx().end(), *j);
			if ((idx == prev_ex.path().constraints_idx().end()) || (*idx != *j)) {
				continue;  // Branch is concrete.
			}
			size_t c_idx = idx - prev_ex.path().constraints_idx().begin();

			if (all_concrete) {
				all_concrete = false;
				num_solve_all_concrete_--;
			}

			if (dist_[paired_branch_[path[*j]]] <= max_dist) {
				num_solve_sat_attempts_++;
				// The paired branch is along a shortest path, so force.
				if (!SolveAtBranch(prev_ex, c_idx, &input)) {
					num_solve_unsats_++;
					continue;
				}
				RunProgram(input, &cur_ex);
				if (UpdateCoverage(cur_ex)) {
					num_solve_successes_++;
					success_ex_.Swap(cur_ex);
					return true;
				}
				if (!CheckPrediction(prev_ex, cur_ex, *j)) {
					num_solve_pred_fails_++;
					continue;
				}

				// Recurse.
				num_solve_recurses_++;
				if (SolveAlongCfg(*j, max_dist - 1, cur_ex)) {
					num_solve_successes_++;
					return true;
				}
			}
		}

		return false;
	}

	void CfgHeuristicSearch::SkipUntilReturn(const vector<branch_id_t> path,
			size_t* pos) {
		while ((*pos < path.size()) && (path[*pos] != kReturnId)) {
			if (path[*pos] == kCallId) {
				(*pos)++;
				SkipUntilReturn(path, pos);
				if (*pos >= path.size())
					return;
				assert(path[*pos] == kReturnId);
			}
			(*pos)++;
		}
	}

	void CfgHeuristicSearch::CollectNextBranches(const vector<branch_id_t>& path,
			size_t* pos, vector<size_t>* idxs) {
		// fprintf(stderr, "Collect(%u,%u,%u)\n", path.size(), *pos, idxs->size());

		// Eat an arbitrary sequence of call-returns, collecting inside each one.
		while ((*pos < path.size()) && (path[*pos] == kCallId)) {
			(*pos)++;
			CollectNextBranches(path, pos, idxs);
			SkipUntilReturn(path, pos);
			if (*pos >= path.size())
				return;
			assert(path[*pos] == kReturnId);
			(*pos)++;
		}

		// If the sequence of calls is followed by a branch, add it.
		if ((*pos < path.size()) && (path[*pos] >= 0)) {
			idxs->push_back(*pos);
			(*pos)++;
			return;
		}

		// Alternatively, if the sequence is followed by a return, collect the branches
		// immediately following the return.
		/*
		   if ((*pos < path.size()) && (path[*pos] == kReturnId)) {
		   (*pos)++;
		   CollectNextBranches(path, pos, idxs);
		   }
		 */
	}

	bool CfgHeuristicSearch::DoBoundedBFS(int i, int depth,
			const SymbolicExecution& prev_ex) {
		if (depth <= 0)
			return false;

		fprintf(stderr, "%d (%d: %d) (%d: %d)\n", depth, i - 1,
				prev_ex.path().branches()[prev_ex.path().constraints_idx()[i - 1]],
				i, prev_ex.path().branches()[prev_ex.path().constraints_idx()[i]]);

		SymbolicExecution cur_ex;
		vector<value_double_t> input;
		const vector<SymbolicPred*>& constraints = prev_ex.path().constraints();
		for (size_t j = static_cast<size_t>(i); j < constraints.size(); j++) {
			if (!SolveAtBranch(prev_ex, j, &input)) {
				continue;
			}

			RunProgram(input, &cur_ex);
			iters_left_--;
			if (UpdateCoverage(cur_ex)) {
				success_ex_.Swap(cur_ex);
				return true;
			}

			if (!CheckPrediction(prev_ex, cur_ex,
						prev_ex.path().constraints_idx()[j])) {
				fprintf(stderr, "Prediction failed!\n");
				continue;
			}

			return (DoBoundedBFS(j + 1, depth - 1, cur_ex)
					|| DoBoundedBFS(j + 1, depth - 1, prev_ex));
		}

		return false;
	}

}  // namespace crest
