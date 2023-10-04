#pragma once
#include <iostream>
#include "Linked List.h"
#include <cmath>
#include <fstream>
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

	void stream_dimacs(std::fstream newfile) {
		if (newfile.is_open()) {
			Link1<Lit>* current = head;
			while (current != NULL) {
				current->data.display();
				newfile << " ";
				current = current->next;
			}
			newfile << 0;
		}
	}

	void print(FILE* file) {
		Link1<Lit>* current = head;
		while (current != NULL) {
			fprintf(file, "%i", current->data.DIMACS());
			fprintf(file, " ");
			current = current->next;
		}
		fprintf(file, "0");
	}

	void sortlist() {
		bool is_swapped = 1;
		while (is_swapped) {
			is_swapped = 0;
			if (head != NULL) {
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
	}

	void norepeats() {
		bool is_contracted = 1;
		while (is_contracted) {
			is_contracted = 0;
			if (head != NULL) {
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

	void clear() {
		while (tail != NULL) {
			rmvnode(tail);
		}
	}
};

struct Comment {
	int line_no;
	const char* comment;
	Comment() {
		int line_no = 0;
		comment = NULL;
	}

	Comment(int line_no, const char* comment)
		: line_no(line_no), comment(comment)
	{
	}
	void display() {
		cout << "c " << comment << endl;
	}
	void print(FILE* file) {
		fprintf(file, "c "); 
		fprintf(file, comment); 
		fprintf(file, "\n");
	}
};

struct Cnf : LinkL<Clause> {
	LinkL<Comment> commentary;
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
	Cnf() {
		head = NULL;
		tail = NULL;
		length = 0;
		commentary= LinkL<Comment>();
	}

	void clear() {
		while (tail != NULL) {
			tail->data.clear();
			rmvnode(tail);
		}
	}

	void display() {
		Link1<Clause>* current = head;
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
			current->data.display();
			cout << endl;
			current = current->next;
		}
	}

	void print_preamble(FILE* file) {
		fprintf(file, "p cnf ");
		fprintf(file, "%i", max_var());
		fprintf(file, " ");
		fprintf(file, "%i", length);
	}


	void print(FILE* file) {
		Link1<Clause>* current = head;
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
			current->data.print(file);
			fprintf(file, "\n");
			current = current->next;
		}
	}



	void add_comment(const char* comment) {
		Comment temp = Comment(length, comment);
		commentary.addnode(temp);
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
		rule = AXIOM;
		litpos0 = -1;
		litpos1 = -1;
		parent0 = -1;
		parent1= -1;

	}
	Line<T>(T x) {
		clause = x;
		rule = AXIOM;
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

bool contains(Lit l, Clause C) {
	Link1<Lit>* current =C.head;
	while (current != NULL) {
		if (current->data == l) {
			return 1;
		}
		current = current->next;
	}
	return 0;

}

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

struct Blocked_Set {
	Var universal;
	LinkL<Var>* existentials;

	Blocked_Set() {
		universal = 0;
		existentials = new LinkL<Var>();
	}
	void display() {
		cout << universal << ": ";
		Link1<Var>* current = existentials->head;
		while (current != NULL) {
			cout << current->data << " ";
			current = current->next;
		}
	}
};

struct D_Scheme {
	LinkL<Blocked_Set>* blocked_sets;

	D_Scheme() {
		blocked_sets = new LinkL<Blocked_Set>;
	}

	bool is_universal(Var u) {
		Link1<Blocked_Set>* current = blocked_sets->head;
		while (current != NULL) {
			if (current->data.universal == u) {
				return 1;
			}
			current = current -> next;
		}
		return 0;
	}

	bool is_pair(Var universal, Var existential) {
		bool output = 0;
		Link1<Blocked_Set>* current1 = blocked_sets->head;
		while (current1 != NULL) {
			if (current1->data.universal == universal) {
				Link1<Var>* current2 = current1->data.existentials->head;
				while (current2 != NULL) {
					if (current2->data == existential) {
						return 1;
					}
					current2 = current2->next;
				}
			}
			current1 = current1->next;
		}
		return 0;
	}

	void display() {
		Link1<Blocked_Set>* current = blocked_sets->head;
		while (current != NULL) {
			current->data.display();
			cout << endl;
			current = current->next;
		}
	}

};

bool u_blocked_in_clause(Var u, Clause C, D_Scheme D) {
	Link1<Lit>* current = C.head;
	while (current != NULL) {
		Var v = current->data.var;
		if (D.is_pair(u, v)) {
			return 1;
		}
		current = current->next;
	}
	return 0;
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

	void addclause_scheme(Clause C, D_Scheme D) {// unfinished and untested
		Link1<Line<Clause>>* current_line1 = head;
		while (current_line1 != NULL) {
			
			int pivot_position0 = -1;
			Link1<Lit>* current_lit1 = current_line1->data.clause.head;
			int current_lit1_pos = 0;
			bool is_current_lit1_in_C = 0;
			LinkL<Var> stray_universals1 = LinkL<Var>();//memory leak?
			while ((current_lit1 != NULL) && (pivot_position0 != -2)) {
				Link1<Lit>* current_litC = C.head;
				bool is_current_lit1_in_C = 0;
				while ((current_litC != NULL) && is_current_lit1_in_C == 0) {
					if (current_litC->data == current_lit1->data) {
						is_current_lit1_in_C = 1;

					}
					current_litC = current_litC->next;
				}
				if (!is_current_lit1_in_C) {
					if (D.is_universal(current_lit1->data.var)) {
						//add to some list to deal with later
						stray_universals1.addnode(current_lit1->data.var);
					}
					else {//existential must mean pivot
						if (pivot_position0 == -1) {
							pivot_position0 = current_lit1_pos;
						}
						else {
							pivot_position0 = -2;
						}
					}
				}
				current_lit1_pos++;
				current_lit1 = current_lit1->next;
			}
			if (pivot_position0 > -2) {
				//check all universals for reduction
				Link1<Var>* current_u = stray_universals1.head;
				bool is_no_blocked = 1;
				while ((current_u != NULL)&& is_no_blocked) {
					if (u_blocked_in_clause(current_u->data, C, D))
					{
						is_no_blocked = 0;
					}
					current_u = current_u->next;
				}
				if (is_no_blocked) {
					if (pivot_position0 == -1) {
						addline(C);
						tail->data.rule = REDUCTION;
						tail->data.parent0 = current_line1->position;
						while (stray_universals1.tail != NULL) {
							stray_universals1.rmvnode(stray_universals1.tail);
						}
						return;
					}
					else {
						Lit left_pivot = current_line1->data.clause[pivot_position0];
						Link1<Line<Clause>>* current_line2 = current_line1;
						while (current_line2 != NULL) {
							int pivot_position1 = -1;
							Link1<Lit>* current_lit2 = current_line2->data.clause.head;
							int current_lit2_pos = 0;
							bool is_current_line_2_partner = 1;
							LinkL<Var> stray_universals2 = LinkL<Var>();
							while ((current_lit2 != NULL) && (is_current_line_2_partner)) {
								if (current_lit2->data == -left_pivot) { //check for literal being pivot
									pivot_position1 = current_lit2_pos;
								}
								else {
									Link1<Lit>* current_litC = C.head;
									bool is_current_lit2_in_C = 0;
									while ((current_litC != NULL) && (is_current_lit2_in_C == 0)) { //checks for literal in C
										if (current_litC->data == current_lit2->data) {
											is_current_lit2_in_C = 1;
										}
										current_litC = current_litC->next;
									}
									if (!is_current_lit2_in_C) {
										if (D.is_universal(current_lit2->data.var)) {
											//add to some list to deal with later
											stray_universals2.addnode(current_lit2->data.var);
										}
										else {
											is_current_line_2_partner = 0;
										}
									}
								}

								current_lit2 = current_lit2->next;
								current_lit2_pos++;
							}

							if (is_current_line_2_partner) {
								Link1<Var>* current_u = stray_universals2.head;
								bool is_no_blocked2 = 1;
								while ((current_u != NULL) && is_no_blocked2) {
									if (u_blocked_in_clause(current_u->data, C, D))
									{
										is_no_blocked2 = 0;
									}
									current_u = current_u->next;
								}
								if (is_no_blocked2) {


									if (current_lit2_pos == -1) {
										addline(C);
										tail->data.rule = REDUCTION;
										tail->data.parent0 = current_line2->position;
										while (stray_universals1.tail != NULL) {
											stray_universals1.rmvnode(stray_universals1.tail);
										}
										while (stray_universals2.tail != NULL) {
											stray_universals2.rmvnode(stray_universals2.tail);
										}
										return;
									}
									else {
										add_res(current_line1->position, current_line2->position, -left_pivot);
										if ((stray_universals1.length != 0) || (stray_universals1.length != 0)) {
											addline(C);
											tail->data.rule = REDUCTION;
											tail->data.parent0 = current_line2->position;
											while (stray_universals1.tail != NULL) {
												stray_universals1.rmvnode(stray_universals1.tail);
											}
											while (stray_universals2.tail != NULL) {
												stray_universals2.rmvnode(stray_universals2.tail);
											}
										}
										return;
									}
								}
							}
							while (stray_universals2.tail != NULL) {
								stray_universals2.rmvnode(stray_universals2.tail);
							}
							current_line2 = current_line2->next;
						}
						
					}
					
				}
			}
			while (stray_universals1.tail != NULL) {
				stray_universals1.rmvnode(stray_universals1.tail);
			}
			current_line1 = current_line1->next;
		}
		addline(C);
	}

	void addline_prop(Clause C) {
		Link1<Line<Clause>>* current_line1 = head;
		while (current_line1 != NULL) {
			int pivot_position0 = -1;
			Link1<Lit>* current_lit1 = current_line1->data.clause.head;
			int current_lit1_pos = 0;
			while ((current_lit1 != NULL) && (pivot_position0 != -2)) {
				Link1<Lit>* current_litC = C.head;
				bool is_current_lit1_in_C = 0;
				while ((current_litC!=NULL) && is_current_lit1_in_C == 0) {
					if (current_litC->data== current_lit1->data) {
						is_current_lit1_in_C = 1;

					}
					current_litC = current_litC->next;
				}
				if(!is_current_lit1_in_C){
					if (pivot_position0 == -1) {
						pivot_position0 = current_lit1_pos;
					}
					else {
						pivot_position0 = -2;
					}
				}
				current_lit1 = current_lit1->next;
				current_lit1_pos++;
			}
	
			if (pivot_position0 > -1) { //Now search for resolution partner
				Link1<Line<Clause>>* current_line2= current_line1;
				Lit left_pivot= current_line1->data.clause[pivot_position0];
				while (current_line2 != NULL) {
					int pivot_position1= -1;
					Link1<Lit>* current_lit2 = current_line2->data.clause.head;
					int current_lit2_pos = 0;
					bool is_current_line_2_partner = 1;
					while ((current_lit2!=NULL)&& (is_current_line_2_partner)) {
						if(current_lit2->data==-left_pivot){ //check for literal being pivot
							pivot_position1 = current_lit2_pos;
						}
						else {
							Link1<Lit>* current_litC = C.head;
							bool is_current_lit2_in_C = 0;
							while ((current_litC != NULL) && (is_current_lit2_in_C == 0)) { //checks for literal in C
								if (current_litC->data == current_lit2->data) {
									is_current_lit2_in_C = 1;
								}
								current_litC = current_litC->next;
							}
							if (!is_current_lit2_in_C) {
								is_current_line_2_partner = 0;
							}
						}

						current_lit2 = current_lit2->next;
						current_lit2_pos++;
					}
					if (is_current_line_2_partner) {
						add_res(current_line1->position, current_line2->position, -left_pivot);
						return;
					}

					current_line2 = current_line2->next;
				}
			}
			current_line1 = current_line1->next;
		}
		addline(C);
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

	void print(FILE* file) {
		fprintf(file, "p qrp ");
		fprintf(file, "\n");
		Link1<Line<Clause>>* current = head;
		while (current != NULL) {
			fprintf(file, "%i", current->position+ 1);
			fprintf(file, " ");
			current->data.clause.print(file);
			fprintf(file, " ");
			if (current->data.parent0> -1) {
				fprintf(file , "%i", current->data.parent0 + 1);
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
		Clause C = copy(current->data);
		output.addnode(C);
		current = current->next;
	}
	return output;
}

void copyinto(Cnf* output, Cnf* input) {
	Link1<Clause>* current = input->head;
	while (current != NULL) {
		output->addnode(current->data);
		current = current->next;
	}
}

Cnf copy(Cnf *input) {
	Cnf output;
	Link1<Clause>* current = input->head;
	while (current != NULL) {
		Clause C = copy(current->data);
		output.addnode(C);
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