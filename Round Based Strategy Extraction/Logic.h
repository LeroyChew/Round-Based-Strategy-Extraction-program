#pragma once
#include <iostream>
#include "Linked List.h"
#include <cmath>
using namespace std;
#define Var int 

struct Lit {
	Var var;
	bool is_pos;
	Lit() {
		var = 0;
		is_pos = 1;
	}
	Lit(int l) {
		var = abs(l);
		if (l <  0) {
			is_pos = 0;
		}
		else {
			is_pos = 1;
		}
	}

	Lit(Var v, bool b) {
		var=v;
		is_pos=b;
	}


	int ordered_value() const{
		int value = 2 * var;
		if (!is_pos) {
			value--;
		}
		return value;
	}

	bool operator >(Lit p) const {
		return (ordered_value() > p.ordered_value());
	}

	bool operator ==(Lit p) const {
		return (ordered_value() == p.ordered_value());
	}
	

	int DIMACS() {
		if (is_pos == 0) {
			return -var;
		}
		else {
			return var;
		}
	}

	

	void display() {
		std::cout << DIMACS();
	}
};

Lit operator -(Lit p) {
	Lit l;
	l.var = p.var;
	if (p.is_pos) {
		l.is_pos = 0;
	}
	else {
		l.is_pos = 1;
	}
	return l;
}

struct Clause : LinkL<Lit> {
	void display() {
		Link1<Lit>* current = head;
		while (current != NULL) {
			current->data.display();
			cout << " ";
			current= current->next;
		}
		cout << 0;
	}

	void sortlist() {
		bool is_swapped = 1;
		while (is_swapped) {
			is_swapped = 0;
			Link1<Lit>* current = head;
			Link1<Lit>* index = current->next;
			while (index != NULL) {
				if (current->data > index->data) {
					is_swapped = 1;
					Lit spare_data = current->data;
					current->data = index->data;
					index->data = spare_data;
				}
				current = current->next;
				index = index->next;
			}

		}
	}

	void norepeats() {
		bool is_contracted = 1;
		while (is_contracted) {
			is_contracted = 0;
			Link1<Lit>* current = head;
			Link1<Lit>* index = current->next;
			while (index != NULL) {
				if (current->data == index->data) {
					rmvnode(index);
					index = current->next;
					is_contracted = 1;
				}
				else
				{
					current = current->next;
					index = index->next;
				}

			}
		}

	}

	Var max_var() {
		int max = 0;
		Link1<Lit>* current = head;
		while (current != NULL) {
			Var index = current->data.var;
			if (index > max) {
				max = index;
			}
			current = current->next;
		}
		return max;
	}
};

struct Cnf : LinkL<Clause> {
	Var max_var() {
		int max = 0;
		Link1<Clause>* current = head;

		while (current != NULL) {
			Var index = current->data.max_var();
			if (index > max) {
				max = index;
			}
			current = current->next;
		}

		return max;
	}
};

struct AbsType {
	int type_no;
	AbsType() {
		type_no = 0;
	}
	AbsType(int x) {
		type_no = x;
	}
	bool operator ==(AbsType p) const {
		return (type_no == p.type_no);
	}
};

#define BASE   AbsType(0) //contains a literal
#define MEMBERSHIP   AbsType(1) // level, line_no, position
#define TAUTOLOGICAL   AbsType(2) // level, line_no
#define SELON   AbsType(3)// level, line_no
#define SELVAL   AbsType(4)// level, line_no
#define DESCENDANT  AbsType(5)// level, line_no, line_no
#define ANCESTOR   AbsType(6)// level, line_no, line_no
#define STRATEGY   AbsType(7)// level, variable
#define XNAND   AbsType(8)// variable, variable
#define XANCESTORSELON   AbsType(9)// level, line_no, line_no
#define XANCESTORSELVAL0   AbsType(10)// level, line_no, line_no
#define XANCESTORSELVAL1   AbsType(11)// level, line_no, line_no
#define XANCESTORMEMBERSHIP   AbsType(12)// level, line_no, position

struct AbsLit {
	AbsType type;
	//Var var; //used for base
	bool is_pos; //used in all
	int level;
	int index1;
	int index2;
};

struct AbsClause : LinkL<AbsLit> {

};

struct Rule {
	int rule_no;
	int arity;
	Rule() {
		rule_no = 0;
	}
	Rule(int x, int y) {
		rule_no = x;
		arity = y;
	}

	bool operator ==(Rule p) {
		return (rule_no == p.rule_no);
	}
	void display();
};

#define AXIOM  Rule(0,0)
#define CONTRACTION  Rule(1,1)
#define EXCHANGE  Rule(2,1)
#define REDUCTION  Rule(3,1)
#define RESOLUTION Rule(4,2)

void Rule::display() {
	if (operator==(AXIOM)) {
		cout << "Ax";
	}
	if (operator==(RESOLUTION)) {
		cout << "Res";
	}
	if (operator==(REDUCTION)) {
		cout << "Red";
	}
}

template <typename T> struct Line {
	T clause;
	Rule rule;
	int litpos0;
	int litpos1;
	int parent0;
	int parent1;

	Line<T>() {
		clause = T();
		rule == AXIOM;
		litpos0 = -1;
		litpos1 = -1;
		parent0 = -1;
		parent1= -1;

	}
	Line<T>(T x) {
		clause = x;
		rule == AXIOM;
		litpos0 = -1;
		litpos1 = -1;
		parent0 = -1;
		parent1 = -1;
	}
};

template <typename T> struct Proof :  LinkL<Line<T>> {
	//various rules generations
	//void addnode(Line<T>) ;

	//	addnode(Line<T>(clause));
};



Clause copy(Clause C) {
	Link1<Lit>* current = C.head;
	Clause D = Clause();
	while (current != NULL) {
		D.addnode(current->data);
		current = current->next;
	}
	return D;
}

Clause resolve(Clause C1, Clause C2, Lit p) {// returns the resolvent of two clauses based on literal, C_1 always contains the negative literal
	bool found_pivot1 = 0;
	bool found_pivot2 = 0;
	Link1<Lit>* current = C1.head;
	Clause D = Clause();
	while (current!=NULL) {
		if (current->data == -p) {
			found_pivot1 = 1;
		}
		else {
			D.addnode(current->data);
		}
		current = current->next;
	}
	current = C2.head;
	while (current != NULL) {
		if (current->data == p) {
			found_pivot2 = 1;
		}
		else {
			D.addnode(current->data);
		}
		current = current->next;
	}
	if (found_pivot1) {
		if (found_pivot2) {
			D.sortlist();
			D.norepeats();
			return D;
		}
		else {
			return copy(C2);
		}
	}
	else {
		return copy(C1);
	}
}

Clause reduce(Clause C, Var u) {//purely reduces a variable
	Link1<Lit>* current = C.head;
	Clause D = Clause();
	while (current != NULL) {
		if (current->data.var != u) {
			D.addnode(current->data);
		}
		current = current->next;
	}
	return D;
}

struct ClausalProof : Proof<Clause> {
	void display() {
		Link1<Line<Clause>>* current = head;
		while (current != NULL) {
			current->data.rule.display();
			cout << ": ";
			current->data.clause.display();
			cout << endl;
			current = current->next;
		}


	}
	void addline(Clause C) {
		addnode(Line<Clause>(C));
	}

	void add_ax(Clause C) {
		Clause D = copy(C);
		addline(D);
	}

	void add_red(int line, Var u){
		Line L = operator[](line);
		Clause C = L.clause;
		Clause D = reduce(C, u);
		Link1<Lit>* current = C.head;
		int redpos0 = -1;
		int redpos1 = -1;
		while (current != NULL) {
			if (current->data == -Lit(u)) {
				redpos0 = current->position;
			}
			if (current->data == Lit(u)) {
				redpos0 = current->position;
			}
			current = current->next;
		}
		Line<Clause>* temp = new Line<Clause>;
		temp->clause = D;
		temp->rule = REDUCTION;
		temp->parent0 = line;
		temp->litpos0 = redpos0;
		temp->litpos1 = redpos1;
		addnode(*temp);
	}

	void add_res(int line0, int line1, Lit p) {
		Line<Clause> L0 = operator[](line0);
		Clause C0 = L0.clause;
		Line<Clause> L1 = operator[](line1);
		Clause C1 = L1.clause;
		Clause D = resolve(C0, C1, p);
		int pivot0 = -1;
		int pivot1 = -1;
		Link1<Lit>* current = C0.head;
		while (current != NULL) {
			if (current->data == -p) {
				pivot0 = current->position;
			}
			current = current->next;
		}
		current = C1.head;
		while (current != NULL) {
			if (current->data == p) {
				pivot1 = current->position;
			}
			current = current->next;
		}
		Line<Clause>* temp = new Line<Clause>;
		temp->clause = D;
		temp->rule = RESOLUTION;
		temp->parent0 = line0;
		temp->parent1 = line1;
		temp->litpos0 = pivot0;
		temp->litpos1 = pivot1;
		addnode(*temp);
 	}

	

	//void display() {
	//	Link1<Line<Clause>>* current = head;
	//	while (current!=NULL) {
	//		current->data.clause.display();
	//		cout << endl;
	//		current = current->next;
	//	}
	//}
};

Cnf copy(Cnf input) {
	Cnf output;
	Link1<Clause>* current = input.head;
	while (current != NULL) {
		output.addnode(current->data);
		current = current->next;
	}
	return output;
}

 int find_a_position(Lit target, Clause the_list) {
	Link1<Lit>* current = the_list.head;
	while (current != NULL) {
		if (current->data == target) {
			return current->position;
		}
		current = current->next;
	}
	return -1;
}