// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#ifndef BASE_SYMBOLIC_EXPRESSION_H__
#define BASE_SYMBOLIC_EXPRESSION_H__

#include <istream>
#include <map>
#include <ostream>
#include <set>
#include <string>

#include "base/basic_types.h"

using std::istream;
using std::map;
using std::ostream;
using std::set;
using std::string;

namespace crest {

	class SymbolicExpr {
		public:
			// Constructs a symbolic expression for the constant 0.
			SymbolicExpr();

			// Constructs a symbolic expression for the given constant 'c'.
			explicit SymbolicExpr(value_t c);
			explicit SymbolicExpr(value_double_t c);

			// Constructs a symbolic expression for the singleton 'c' * 'v'.
			SymbolicExpr(value_t c, var_t v);
			SymbolicExpr(value_double_t c, var_t v);

			// Copy constructor.
			SymbolicExpr(const SymbolicExpr& e);

			// Desctructor.
			~SymbolicExpr();

			void Negate();
			//
			// hComment: this expression is concrete if coeff_ is empty
			//
			bool IsConcrete() const {
				return coeff_.empty() && coeff_FD_.empty();
			}
			
			bool IsFloat() const {
				return isFloat;
			}

            void FD2INT();
            void syncFD();

            // hDel: redundant code
            /*
            size_t Size() const {
				return (1 + coeff_.size());
			}
            */

			void AppendVars(set<var_t>* vars) const;
			bool DependsOn(const map<var_t, type_t>& vars) const;
            bool VarExist(var_t var) const; 

			void AppendToString(string* s) const;
            void Print() const;

			void Serialize(string* s) const;
			bool Parse(istream& s);

			// Arithmetic operators.
			const SymbolicExpr& operator+=(const SymbolicExpr& e);
			const SymbolicExpr& operator-=(const SymbolicExpr& e);
			const SymbolicExpr& operator+=(value_t c);
			const SymbolicExpr& operator-=(value_t c);
			const SymbolicExpr& operator*=(value_t c);
			const SymbolicExpr& operator+=(value_double_t c);
			const SymbolicExpr& operator-=(value_double_t c);
			const SymbolicExpr& operator*=(value_double_t c);
			bool operator==(const SymbolicExpr& e) const;

            // hDel: unused code sgement
            /*
            // Accessors.
            value_double_t const_term() const {
            return const_;
            }
            const map<var_t, value_double_t>& terms() const {
            return coeff_;
            }
            typedef map<var_t, value_double_t>::const_iterator TermIt;
             */
		
        private:
            
            // 
            // hEdit: is this expression float?
            // 
            bool isFloat;
			
            value_t const_;
			//
			// hComment: coeff_->first holds the index of one marked
			// variable by the marking order coeff_->second holds the 
			// coefficient of this variable
			//
			map<var_t, value_t> coeff_;
			
            
            // 
            // hEdit: support floating point 
            // 
            value_double_t const_FD_;
            map<var_t, value_double_t> coeff_FD_;


            // 
            // hEdit: support floating point data type
            // 
			void AppendToStringInt(string* s) const;
			void AppendToStringFD(string* s);
	};

}  // namespace crest

#endif  // BASE_SYMBOLIC_EXPRESSION_H__
