#pragma once
#include "QBF.h"
#include <fstream>
#include <cstring>

struct QRAT_Rule {
	int rule_no;

	QRAT_Rule() {
		rule_no = 0;
	}
	QRAT_Rule(int rule) {
		rule_no = rule;
	}

	bool operator==(const QRAT_Rule& other) const
	{
		return rule_no==other.rule_no;
	}
};

bool propagation(Cnf Phi) {
	Cnf Phicopy = ccopy( Phi);
	Link1<Clause>* currentC = Phicopy.head;
	while (currentC!=NULL) {
		if (currentC->data.length < 2) {
			if (currentC->data.length < 1) {
				return 0;
			}
			Lit unit = currentC->data.head->data;
			Link1<Clause>* currentC1 = Phicopy.head;
			while (currentC1 != NULL) {
				Link1<Lit>* currentC1l = currentC1->data.head;
				bool is_subsumed = 0;
				while (currentC1l != NULL) {
					if (currentC1l->data==-unit) {
						Link1<Lit>* currentC1lnext = currentC1l->next;
						currentC1->data.rmvnode(currentC1l);
						currentC1l = currentC1lnext;
					}
					else {
						if (currentC1l->data == unit) {
							currentC1->data.clear();
							Link1<Clause>* removable = currentC1;
							currentC1 = currentC1->next;
							Phicopy.rmvnode(removable);
							is_subsumed = 1;
							break;
						}
						currentC1l = currentC1l->next;
					}
					
				}
				if (!is_subsumed) {
					currentC1 = currentC1->next;
				}
			}
			currentC = Phicopy.head;
		}
		else {
			currentC = currentC->next;
		}
	}
	return 1;
}

#define ruleATA QRAT_Rule(1)
#define ruleATE QRAT_Rule(2)
#define ruleQRATA QRAT_Rule(3)
#define ruleQRATE QRAT_Rule(4)
#define ruleQRATU QRAT_Rule(5)
#define ruleEUR QRAT_Rule(6)
#define ruleDeletion QRAT_Rule(7)

struct QRAT_Line {
	Clause clause;
	QRAT_Line* prev;
	QRAT_Line* next;
	QRAT_Rule rule;
	int position;
	int parent;
	Lit literal;
	QRAT_Line() {
		clause = Clause();
		prev = NULL;
		next = NULL;
		rule = QRAT_Rule();
		position = 0;
		parent = -1;
		literal = Lit(0);
	}


	QRAT_Line( Clause clause, QRAT_Line* prev, QRAT_Line* next, QRAT_Rule rule, int position, Lit literal)
		: clause(clause), prev(prev), next(next), rule(rule), position(position), literal(literal)
	{
	}
	void display() {
		clause.display();
		cout << " ";
		if (rule == ruleQRATA) {
			cout << " c QRATA on ";
			literal.display();
			cout << " ";
		}
	}
	void print(FILE* file) {
		Link1<Lit>* current = clause.head;
		while (current != NULL) {
			fprintf(file, "%i", current->data.DIMACS());
			fprintf(file, " ");
			current = current->next;
		}
	}
};

struct QRAT_Proof {
	QRAT_Line* head;
	QRAT_Line* tail;
	QCNF Phi;
	Prefix* extended_prefix;
	int length;
	LinkL<Comment> commentary;
	QRAT_Proof() {
		head = NULL;
		tail = NULL;
		Phi = QCNF();
		length = 0;
		commentary = LinkL<Comment>();
		extended_prefix = &Phi.prefix;
	}

	void add_comment(const char* comment) {
		Comment temp = Comment(length, comment);
		commentary.addnode(temp);
	}

	void ATA(Clause C) {
		Clause D = ccopy(C);
		D.sortlist();
		QRAT_Line* temp = new QRAT_Line(D, tail, NULL, ruleATA, length, Lit(0));
		if (head == NULL) {
			head = temp;
		}
		else {
			tail->next = temp;
		}
		tail = temp;
		length++;
	}


	bool checkATA(QRAT_Line* line, Cnf* phi) {
		Clause C = line->clause;
		Cnf checkingcnf = ccopy(phi);
		Link1<Lit>* currentl = C.head;
		while (currentl != NULL) {
			Clause barl = Clause();
			Lit l = currentl->data;
			barl.addnode(-l);
			checkingcnf.addnode(barl);
			currentl = currentl->next;
		}
		
		bool result= !propagation(checkingcnf);
		checkingcnf.clear();
		return result;

	}

	bool checkATA(QRAT_Line* line) {
		Clause C = line->clause;
		Cnf checkingcnf;
		QRAT_Line* currentD = head;
		while (currentD->position < line->position) {
			if ((currentD->rule == ruleATA) || (currentD->rule == ruleQRATA)){
				checkingcnf.addnode(currentD->clause);
			}
			if ((currentD->rule == ruleQRATU) || (currentD->rule == ruleEUR)) {
				checkingcnf.rmvnode(checkingcnf.findnode(currentD->parent));
				checkingcnf.addnode(currentD->clause);
			}
			if ((currentD->rule == ruleATE) || ((currentD->rule == ruleQRATE) || (currentD->rule == ruleDeletion))) {
				checkingcnf.rmvnode(checkingcnf.findnode(currentD->parent));
			}
			currentD = currentD->next;
		}
		Link1<Lit>* currentl = C.head;
		while (currentl!=NULL) {
			Clause barl = Clause();
			Lit l = currentl->data;
			barl.addnode(-l);
			checkingcnf.addnode(barl);
			currentl = currentl->next;
		}
		return !propagation(checkingcnf);
	}

	void QRATA(Clause C, Lit l) {
		Clause D = ccopy(C);
		D.sortlist();
		QRAT_Line* temp = new QRAT_Line(D, tail, NULL, ruleQRATA, length, l);
		if (head == NULL) {
			head = temp;
		}
		else {
			tail->next = temp;
		}
		tail = temp;
		length++;
	}

	bool checkQRATA(QRAT_Line* line, Cnf* phi) {// maintains Cnf phi, while checking QRATA line
		Link1<Clause>* currentD = phi->head;
		Clause C = line->clause;
		Lit linelit = line->literal;
		bool is_not_QRAT = 0;
		while (currentD != NULL) {
			Clause D = currentD->data;
			if (contains(-linelit, D)) {
				Link1<Lit>* currentl = D.head;
				Cnf checkingcnfD = ccopy(*phi);
				while (currentl != NULL) {
					Lit l = currentl->data;
					if ((l != linelit)&& (Phi.prefix.lvl(linelit.var) >= Phi.prefix.lvl(l.var))) {
						Clause barl = Clause();
						barl.addnode(-l);
						checkingcnfD.addnode(barl);
					}
					currentl = currentl->next;
				}
				Link1<Lit>* currentc = C.head;
				while (currentc != NULL) {
					Lit c = currentc->data;
						Clause barc = Clause();
						barc.addnode(-c);
						checkingcnfD.addnode(barc);
					currentc = currentc->next;
				}
				is_not_QRAT = (is_not_QRAT || propagation(checkingcnfD));
				checkingcnfD.clear();
			}
			currentD = currentD->next;
		}
		phi->addnode(line->clause);
		return !is_not_QRAT;
	}

	bool checkQRATA(QRAT_Line* line) {
		Clause C = line->clause;
		Cnf checkingcnf;
		QRAT_Line* currentL = head;
		while (currentL->position < line->position) {
			if ((currentL->rule == ruleATA) || (currentL->rule == ruleQRATA)) {
				checkingcnf.addnode(currentL->clause);
			}
			if ((currentL->rule == ruleQRATU) || (currentL->rule == ruleEUR)) {
				checkingcnf.rmvnode(checkingcnf.findnode(currentL->parent));
				checkingcnf.addnode(currentL->clause);
			}
			if ((currentL->rule == ruleATE) || ((currentL->rule == ruleQRATE) || (currentL->rule == ruleDeletion))) {
				checkingcnf.rmvnode(checkingcnf.findnode(currentL->parent));
			}
			currentL = currentL->next;
		}
		

	}

	void QRATA(Clause C, Lit l, const char* comment) {
		Clause D = ccopy(C);
		D.sortlist();
		add_comment(comment);
		QRAT_Line* temp = new QRAT_Line(D, tail, NULL, ruleQRATA, length, l);
		if (head == NULL) {
			head = temp;
		}
		else {
			tail->next = temp;
		}
		tail = temp;
		length++;
	}

	void NewEVariable(Var v, int definition_lvl) {
		Link1<Quantifier>* current = extended_prefix->head;
		while ((current != NULL)&&(current->data.level<= definition_lvl)) {

			current = current->next;
		}
		Link1<Quantifier>* before = current->prev;
		int v_level = definition_lvl;
		if (before->data.is_universal) {
			v_level++;
		}
		Quantifier entry_v = Quantifier(0, v_level, v);
		extended_prefix->insertafter(before, entry_v);
	}

	bool full_check() {
		Cnf current_cnf = ccopy(Phi.matrix);
		QRAT_Line* current= head;
		bool is_rolling_checked=1;
		while (current != NULL) {
			bool is_local_check = 0;
			if (current->rule == ruleATA) {
				is_local_check = checkATA(current, &current_cnf);
			}
			if (current->rule == ruleQRATA) {
				is_local_check = checkQRATA(current, &current_cnf);
			}
			
			if (is_local_check) {
			}
			else {
				cout << endl;
				current->clause.display();
				cout << " verification failed";
			}
			is_rolling_checked = (is_rolling_checked && is_local_check);
			current = current->next;
		}
		return is_rolling_checked;
	}

	void display() {
		QRAT_Line* current = head;
		Link1<Comment>* current_comment_head = commentary.head;
		while (current != NULL) {
			int current_pos = current->position;
			Link1<Comment>* current_comment = current_comment_head;
			while (current_comment != NULL) {
				int comment_pos = current_comment->data.line_no;
				if (comment_pos > current_pos) {
					break;
				}
				else {
					current_comment_head = current_comment;
					if (comment_pos == current_pos) {
						current_comment->data.display();
					}
				}
				current_comment = current_comment->next;
			}
			current->display();
			cout << endl;
			current = current->next;
		}
	}
	void print(FILE* file) {
		QRAT_Line* current = head;
		Link1<Comment>* current_comment_head = commentary.head;
		while (current != NULL) {
			int current_pos = current->position;
			Link1<Comment>* current_comment = current_comment_head;
			while (current_comment != NULL) {
				int comment_pos = current_comment->data.line_no;
				if (comment_pos > current_pos) {
					break;
				}
				else {
					current_comment_head = current_comment;
					if (comment_pos == current_pos) {
						current_comment->data.print(file);
					}
				}
				current_comment = current_comment->next;
			}

			current->print(file);
			fprintf(file, "0 \n");
			current = current-> next;
		}
	}

	
};
