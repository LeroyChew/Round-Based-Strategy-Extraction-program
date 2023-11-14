#pragma once
#include "Logic.h"
#include<fstream>

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
			current = current->next;
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

	void print_qdimacs(const char* filename) {
		fstream newfile;
		newfile.open(filename, ios::app );
		Link1<Quantifier>* current = head;
		int lvl = 0;
		while (current != NULL) {
			if (current->data.level > lvl) {
				lvl = current->data.level;
				if (current->data.is_universal) {
					newfile <<"a ";
				}
				else {
					newfile <<"e ";
				}
			}
			newfile << current->data.var << " ";
			current = current->next;
			if (current != NULL) {
				if (current->data.level > lvl) {
					newfile << "0" << "\n";
				}
			}
			else {
				newfile << "0" << "\n";
			}
		}
	}

	void print(FILE* file) {
		Link1<Quantifier>* current = head;
		int lvl = 0;
		while (current != NULL) {
			if (current->data.level > lvl) {
				lvl = current->data.level;
				if (current->data.is_universal) {
					fprintf(file, "a ");
				}
				else {
					fprintf(file, "e ");
				}
			}
			fprintf(file, "%i", current->data.var);
			fprintf(file, " ");
			current = current->next;
			if (current != NULL) {
				if (current->data.level > lvl) {
					fprintf(file, "0\n");
				}
			}
			else {
				fprintf(file, "0\n");
			}
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

bool is_universal(Var u, Prefix P) {
	Link1<Quantifier>* current = P.head;
	while (current != NULL) {
		if ((current->data.var == u) && (current->data.is_universal) ) {
			return 1;
		}
		current = current->next;
	}
	return 0;
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
	
	void print(FILE* file) {
		matrix.print_preamble(file);
		fprintf(file, "\n");
		prefix.print(file);
		matrix.print(file);
	}
};

void print_qrc(FILE* file, QCNF formula, ClausalProof proof) {
	fprintf(file, "p qrp ");
	fprintf(file, "%i", formula.matrix.mvar);
	fprintf(file, " ");
	fprintf(file, "%i", formula.matrix.length);
	fprintf(file, "\n");
	formula.prefix.print(file);
	Link1<Line<Clause>>* current = proof.head;
	while (current != NULL) {
		fprintf(file, "%i", current->position + 1);
		fprintf(file, " ");
		current->data.clause.print(file);
		fprintf(file, " ");
		if (current->data.parent0 > -1) {
			fprintf(file, "%i", current->data.parent0 + 1);
			fprintf(file, " ");
		}
		if (current->data.parent1 > -1) {
			fprintf(file, "%i", current->data.parent1 + 1);
			fprintf(file, " ");
		}
		fprintf(file, "0");
		fprintf(file, "\n");
		current = current->next;
	}
	if (proof.tail->data.clause.length == 0) {
		fprintf(file, "r unsat");
	}
}
