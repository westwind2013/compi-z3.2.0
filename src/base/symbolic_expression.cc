// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include <assert.h>
#include <stdio.h>

#include <cmath>

#include "base/symbolic_expression.h"

namespace crest {

	typedef map<var_t,value_t>::iterator It;
	typedef map<var_t,value_t>::const_iterator ConstIt;

	typedef map<var_t,value_double_t>::iterator ItFD;
	typedef map<var_t,value_double_t>::const_iterator ConstItFD;
	
    SymbolicExpr::~SymbolicExpr() { }

	SymbolicExpr::SymbolicExpr() : 
        isFloat(false), const_(0), const_FD_(0.0) { }

	SymbolicExpr::SymbolicExpr(value_t c) : 
        isFloat(false), const_(c), const_FD_(0.0) { }

	SymbolicExpr::SymbolicExpr(value_double_t c) : 
        isFloat(true), const_(0), const_FD_(c) { }

	SymbolicExpr::SymbolicExpr(value_t c, var_t v) : 
        isFloat(false), const_(0), const_FD_(0.0) {
		
        coeff_[v] = c;
	}

	SymbolicExpr::SymbolicExpr(value_double_t c, var_t v) : 
        isFloat(true), const_(0), const_FD_(0.0) {

		coeff_FD_[v] = c;
	}
	
    SymbolicExpr::SymbolicExpr(const SymbolicExpr& e) : 
        isFloat(e.isFloat), const_(e.const_), coeff_(e.coeff_), 
        const_FD_(e.const_FD_), coeff_FD_(e.coeff_FD_) { }


	//
	// hComment: negate the coefficient, i.e. a --> -a, where a is
	// a marked variable
	//
	void SymbolicExpr::Negate() {
		const_ = -const_;
		for (It i = coeff_.begin(); i != coeff_.end(); ++i) {
			i->second = -i->second;
		}

		const_FD_ = -const_FD_;
		for (ItFD i = coeff_FD_.begin(); i != coeff_FD_.end(); ++i) {
			i->second = -i->second;
		}
	}

	//
	// hComment: find the set of marked variables without redundancy
	//
	void SymbolicExpr::AppendVars(set<var_t>* vars) const {
		for (ConstIt i = coeff_.begin(); i != coeff_.end(); ++i) {
			vars->insert(i->first);
		}
        
		for (ConstItFD i = coeff_FD_.begin(); i != coeff_FD_.end(); ++i) {
			vars->insert(i->first);
		}
	}

	// 
	// hComment: check if any variables used in the expression exists 
	// in vars
	//
	bool SymbolicExpr::DependsOn(const map<var_t,type_t>& vars) const {
		for (ConstIt i = coeff_.begin(); i != coeff_.end(); ++i) {
			if (vars.find(i->first) != vars.end())
				return true;
		}
		
        for (ConstItFD i = coeff_FD_.begin(); i != coeff_FD_.end(); ++i) {
			if (vars.find(i->first) != vars.end())
				return true;
		}

		return false;
	}

    void SymbolicExpr::AppendToStringInt(string* s) const {
		
        char buff[32];
		sprintf(buff, "%lld", const_);
		s->append(buff);


		for (ConstIt i = coeff_.begin(); i != coeff_.end(); ++i) {

			sprintf(buff, " (* %lld x%u )", i->second, i->first);
			s->append(buff);
		    *s = "(+ " + *s + " )";
        }
/*		for (ConstIt i = coeff_.begin(); i != coeff_.end(); ++i) {

			sprintf(buff, " (* %lld x%u ) ", i->second, i->first);
			s->append(buff);
		    *s = "(+ " + *s + ") ";
        }*/
	}
	
    void SymbolicExpr::AppendToStringFD(string* s) {

        for (ConstIt i = coeff_.begin(); i != coeff_.end(); ++i) {
            if (coeff_FD_.find(i->first) != coeff_FD_.end()) {
                coeff_FD_[i->first] += static_cast<value_double_t>(i->second); 
            } else {
                coeff_FD_[i->first] = static_cast<value_double_t>(i->second); 
            }
        }
        const_FD_ += const_;
        const_ = 0;
        coeff_.clear();

        char buff[32];
        sprintf(buff, "%lf ", const_FD_);
        s->append(buff);

        for (ConstItFD i = coeff_FD_.begin(); i != coeff_FD_.end(); ++i) {

            sprintf(buff, " (* %lf x%u )", i->second, i->first);
            s->append(buff);
            *s = "(+ " + *s + " )";
        }
    }

    void SymbolicExpr::AppendToString(string* s) const {
	
        switch(isFloat) {
            case false:
                AppendToStringInt(s);
                break;
            case true: 
                AppendToStringFD(s);
                break;
        }
	}


	void SymbolicExpr::Serialize(string* s) const {

//fprintf(stderr, "coeff_.size = %d\n", coeff_.size());
		
        assert(coeff_.size() < 128);

        s->push_back(static_cast<char>(isFloat));

		s->push_back(static_cast<char>(coeff_.size()));
		s->append((char*)&const_, sizeof(value_t));
		for (ConstIt i = coeff_.begin(); i != coeff_.end(); ++i) {
			s->append((char*)&i->first, sizeof(var_t));
			s->append((char*)&i->second, sizeof(value_t));
		}
		
        s->push_back(static_cast<char>(coeff_FD_.size()));
		s->append((char*)&const_FD_, sizeof(value_double_t));
		for (ConstItFD i = coeff_FD_.begin(); i != coeff_FD_.end(); ++i) {
			s->append((char*)&i->first, sizeof(var_t));
			s->append((char*)&i->second, sizeof(value_double_t));
		}
	}


	bool SymbolicExpr::Parse(istream& s) {
        

        s.read((char*)&isFloat, sizeof(char));

        size_t len = static_cast<size_t>(s.get());
		s.read((char*)&const_, sizeof(value_t));
		if (s.fail()) return false;

		coeff_.clear();
		for (size_t i = 0; i < len; i++) {
			var_t v;
			value_t c;
			s.read((char*)&v, sizeof(v));
			s.read((char*)&c, sizeof(c));
			coeff_[v] = c;
		}
		
        len = static_cast<size_t>(s.get());
		s.read((char*)&const_FD_, sizeof(value_double_t));
		if (s.fail()) return false;

		coeff_FD_.clear();
		for (size_t i = 0; i < len; i++) {
			var_t v;
			value_double_t c;
			s.read((char*)&v, sizeof(v));
			s.read((char*)&c, sizeof(c));
			coeff_FD_[v] = c;
		}

//fprintf(stderr, "coeff_.size = %d\n", coeff_.size());

		return !s.fail();
	}


    const SymbolicExpr& SymbolicExpr::operator+=(const SymbolicExpr& e) {
        isFloat |= e.isFloat;

        const_ += e.const_;
        for (ConstIt i = e.coeff_.begin(); i != e.coeff_.end(); ++i) {
            It j = coeff_.find(i->first);
            if (j == coeff_.end()) {
                coeff_.insert(*i);
            } else {
                j->second += i->second;
                if (j->second == 0) {
                    coeff_.erase(j);
                }
            }
        }

        const_FD_ += e.const_FD_;
        for (ConstItFD i = e.coeff_FD_.begin(); i != e.coeff_FD_.end(); ++i) {
            ItFD j = coeff_FD_.find(i->first);
            if (j == coeff_FD_.end()) {
                coeff_FD_.insert(*i);
            } else {
                j->second += i->second;
                if (fabs(j->second) < EPSILON){
                    coeff_FD_.erase(j);
                }
            }
        }

        return *this;
    }


	const SymbolicExpr& SymbolicExpr::operator-=(const SymbolicExpr& e) {
		isFloat |= e.isFloat;
		
        const_ -= e.const_;
        for (ConstIt i = e.coeff_.begin(); i != e.coeff_.end(); ++i) {
            It j = coeff_.find(i->first);
            if (j == coeff_.end()) {
                coeff_[i->first] = -i->second;
            } else {
                j->second -= i->second;
                if (j->second == 0) {
                    coeff_.erase(j);
                }
            }
        }
        
        const_FD_ -= e.const_FD_;
		for (ConstItFD i = e.coeff_FD_.begin(); i != e.coeff_FD_.end(); ++i) {
			ItFD j = coeff_FD_.find(i->first);
			if (j == coeff_FD_.end()) {
				coeff_FD_[i->first] = -i->second;
			} else {
				j->second -= i->second;
                if (fabs(j->second) < EPSILON){
                    coeff_FD_.erase(j);
                }
			}
		}

		return *this;
	}

	const SymbolicExpr& SymbolicExpr::operator+=(value_t c) {
		const_ += c;
		return *this;
	}


	const SymbolicExpr& SymbolicExpr::operator-=(value_t c) {
		const_ -= c;
		return *this;
	}


	const SymbolicExpr& SymbolicExpr::operator+=(value_double_t c) {
		isFloat = true;
        const_FD_ += c;

		return *this;
	}


	const SymbolicExpr& SymbolicExpr::operator-=(value_double_t c) {
		isFloat = true;
        const_FD_ -= c;

		return *this;
	}
    
    
    const SymbolicExpr& SymbolicExpr::operator*=(value_t c) {
        if (c == 0) {
            coeff_.clear();
            const_ = 0;
            coeff_FD_.clear();
            const_FD_ = 0;
        } else {
            const_ *= c;
            for (It i = coeff_.begin(); i != coeff_.end(); ++i) {
                i->second *= c;
            }
            
            const_FD_ *= c;
            for (ItFD i = coeff_FD_.begin(); i != coeff_FD_.end(); ++i) {
                i->second *= c;
            }
        }

        return *this;
    }



	const SymbolicExpr& SymbolicExpr::operator*=(value_double_t c) {
		isFloat = true;
        
        if (fabs(c) < EPSILON) {
			coeff_.clear();
            const_ = 0;
            coeff_FD_.clear();
			const_FD_ = 0;
		} else {
			const_FD_ = (const_FD_ + const_) * c;
            const_ = 0;

            for (ItFD i = coeff_FD_.begin(); i != coeff_FD_.end(); ++i) {
                i->second *= c;
            }
			for (It i = coeff_.begin(); i != coeff_.end(); ++i) {
				if (coeff_FD_.find(i->first) == coeff_FD_.end())
                    coeff_FD_[i->first] = i->second * c;
                else
                    coeff_FD_[i->first] += i->second * c;

                coeff_.erase(i);
			}
		}
		return *this;
	}
	
    bool SymbolicExpr::operator==(const SymbolicExpr& e) const {
		return isFloat? 
            ((fabs(const_ - e.const_) < EPSILON) && 
                (coeff_ == e.coeff_)) :
            ((const_ == e.const_) && (coeff_ == e.coeff_));
	}

}  // namespace crest
