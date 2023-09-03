#pragma once
#include "Logic.h"

struct Quantifier {
	bool is_universal;
	int level;
	Var var;
	Quantifier() {
		is_universal = 0;
		level = 0;
		var = 0;
	}
	Quantifier(int x) {
		is_universal = 0;
		if (x < 0) {
			is_universal = 1;
		}
		level = 0;
		var = abs(x);
	}

	Quantifier(bool is_universal, int level, const Var& var)
		: is_universal(is_universal), level(level), var(var)
	{
	}

};
struct Prefix : LinkL<Quantifier> {
	void addvar(int x) {
		bool is_tail_universal = 0;
		int tail_level;
		if (tail==NULL){
			tail_level = 0;
			
		}
		else {
			tail_level=tail->data.level;
			is_tail_universal = tail->data.is_universal;
		}
		
		Quantifier temp = Quantifier(x);
		temp.level = tail_level;
		if (tail != NULL) {
			if (is_tail_universal != temp.is_universal) {
				temp.level++;
			}
		}
		else {
			temp.level++;
		}
		addnode(temp);
	}
	int lvl(Var v) {
		Link1<Quantifier>* current = head;
		while (current != NULL) {
			if (current->data.var == v) {
				return current->data.level;
			}
		}
		return 0;
	}

	void display() {
		Link1<Quantifier>* current = head;
		int lvl = 0;
		while (current!=NULL) {
			if (current->data.level > lvl) {
				lvl = current->data.level;
				if (current->data.is_universal) {
					cout << "A ";
				}
				else {
					cout << "E ";
				}
			}
			cout << current->data.var <<" ";
			current = current->next;
		}
	}
};

Prefix copy(Prefix input) {
	Prefix output;
	Link1<Quantifier>* current = input.head;
	while (current != NULL) {
		output.addnode(current->data);
		current = current->next;
	}
	return output;
}

int universal_index(Var u, Prefix P) {
	Link1<Quantifier>* current = P.head;
	int i = 0;
	while (current != NULL) {
		if (current->data.var == u) {
			return i;
		}
		current = current->next;
	}
	return -1;
}

struct QCNF {
	Prefix prefix;
	Cnf matrix;
};

