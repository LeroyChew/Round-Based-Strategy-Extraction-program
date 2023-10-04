#pragma once
#include "Linked List.h"
#include "QBF.h"
namespace idx {
	struct Index1_1 {// house for each membership literal
		bool is_membership_defined;
		Var membership;
		Cnf* def_membership;
		Lit lit;


		bool* is_overlevel_proved;
		Cnf* proof_overlevel;

		Index1_1() {
			is_membership_defined = 0;
			membership = 0;
			lit = Lit();
			def_membership = new Cnf;
			is_overlevel_proved = new bool;
			*is_overlevel_proved = 0;
			proof_overlevel = new Cnf();
		}
	};

	struct Index1 { // house for each line
		bool is_membership_defined;
		bool is_tautological_defined;
		bool is_selon_defined;
		bool is_selval_defined;

		
		LinkL<Index1_1>* memberships;
		

		Var membership_start;
		Var membership_end;
		Var tautological;
		Cnf* def_tautological;
		
		Var selon;
		Cnf* def_selon;
		Var selval;
		Cnf* def_selval;

		Index1() {
			is_membership_defined=0;
			is_tautological_defined=0;
			is_selon_defined=0;
			is_selval_defined=0;
			
			membership_start=0;
			membership_end = 0;
			tautological = 0;
			selon=0;
			selval = 0;
			memberships = new LinkL < Index1_1>;
			def_tautological= new Cnf;
			def_selon= new Cnf;
			def_selval= new Cnf;
			
		}
	};

	struct Index2_1 { //house for children of line_1
		int line_no;
		int parent;
		int polarity;
		bool* is_adequivalence_proven;
		bool* is_line2child_proven;
		Cnf* adequivalence0;//aselval and dselval are equivalent
		Cnf* line2child; //dselval clauses for Parents and C, where C is second argument, changes from res to red


		Index2_1() {
			line_no = -1;
			parent = NULL;
			polarity = -1;
			is_adequivalence_proven = new bool();
			*is_adequivalence_proven = 0;
			is_line2child_proven = new bool();
			*is_line2child_proven = 0;
		}


		Index2_1(int line_no, int parent, int polarity)
			: line_no(line_no), parent(parent), polarity(polarity)
		{
		}

		Index2_1(int line_no, int parent, int polarity,  Cnf* adequivalence0, Cnf* line2child)
			: line_no(line_no), parent(parent), polarity(polarity),  adequivalence0(adequivalence0), line2child(line2child)
		{
		}
	};

	struct Index2_2 {//house for literals when showing independence
		Lit l;
		bool* is_independence_proved;
		Cnf* proof_independence;

	

		Index2_2(){
			Lit l = Lit(0);
			is_independence_proved = new bool;
			*is_independence_proved = 0;
			proof_independence = new Cnf();
			
		}
	};

	struct Index2 { //house for each pair of lines
		bool is_descendant_defined;
		bool is_ancestor_defined;
		bool is_xselval0_defined;
		bool is_xselval1_defined;

		bool* is_a_equals_d_proved;

		Var descendant;
		Cnf* def_descendant;
		Var ancestor;
		Cnf* def_ancestor;
		//Var xselon;
		Var aselval1;
		Cnf* def_aselval1;
		Var aselval0;
		Cnf* def_aselval0;
		Var dselval0;
		Cnf* def_dselval0;
		Var dselval1;
		Cnf* def_dselval1;

		Cnf* proof_a_equals_d;

		LinkL<Index2_1>* childrenof1;
		LinkL<Index2_2>* indep_literals;

		Index2() {
			is_descendant_defined=0;
			is_ancestor_defined = 0;
			is_xselval0_defined = 0;
			is_xselval1_defined = 0;
			is_a_equals_d_proved = new bool();
			*is_a_equals_d_proved = 0;
			descendant = 0;
			ancestor = 0;
			//xselon = 0;
			aselval1 = 0;
			aselval0 = 0;
			dselval1 = 0;
			dselval0 = 0;
			def_descendant = new Cnf;
			def_ancestor = new Cnf;
			def_aselval1 = new Cnf;
			def_aselval0 = new Cnf;
			def_dselval1 = new Cnf;
			def_dselval0 = new Cnf;
			childrenof1 = new LinkL<Index2_1>;
			proof_a_equals_d = new Cnf;
		}
	};

	struct Index3_1 { //house for each axiom
		bool is_xmembershipdefined;
		Var xmembership;
		Cnf* def_xmembership;
		int line_no;

		Index3_1() {
			is_xmembershipdefined = 0;
			xmembership = 0;
			line_no = -1;
			def_xmembership= new Cnf;

		}

	};

	struct Index3 { //house for each universal variable
		bool is_xmembership_defined;
		bool is_strategy_defined;
		Var u;

		LinkL<Index3_1> * disjuncts;

		Var xmembership_start;
		Var xmembership_end;
		Var strategy;
		Cnf* def_strategy;

		Index3() {
			is_xmembership_defined = 0;
			is_strategy_defined=0;

			xmembership_start = 0;
			xmembership_end = 0;
			strategy = 0;
			def_strategy = new Cnf;

			disjuncts = new LinkL <Index3_1>;
		}

	};

	struct Index4_1 {
		Lit entry_lit;
		int entry_lit_pos;
		bool is_drrs_calculated;
		LinkL<Lit>* DrrsLits;
	};

	struct Index4 {
		int drrs_calculated;
		Clause* clause;
		LinkL<Lit>* DrrsLits;
		LinkL<Index4_1>* entrycases;

		Index4() {
			int drrs_calculated = 0;
			Clause* clause= new Clause();
			DrrsLits = new LinkL< Lit>;
			entrycases = new LinkL<Index4_1>;
		}

		int reverse_entry_index(Lit l) {
			if (entrycases == NULL) {
				return -2;
			}
			Link1<Index4_1>* current = entrycases->head;
			int i = 0;
			while (current != NULL) {
				if (current->data.entry_lit == l) {
					return i;
				}
				i++;
				current = current->next;
			}
			return -1;

		}
	};


	//made after long break may be buggy
	void drrs_axiom_entry(Lit entry, Link1<Index4>* input, LinkL<Index4>* axioms, int level, Prefix* pi) {
		Link1<Index4>* currentI = axioms->head;
		while (currentI != NULL) {
			Link1<Lit>* current_lit_other = currentI->data.clause->head;
			while (current_lit_other != NULL) {
				Link1<Lit>* current_lit_self = input->data.clause->head;
				Lit q = current_lit_other->data;
				if (pi->lvl(q.var) > level) {
					while (current_lit_self != NULL) {
						current_lit_self = current_lit_self->next;
						Lit p = current_lit_self->data;
						if (p == -q) {
							drrs_axiom_entry(-p, currentI, axioms, level, pi);
							int q_pos = currentI->data.reverse_entry_index(-p);
							//need to modify Linked List to concatenate;
						}
					}
				}
				current_lit_other = current_lit_other->next;
			}

			currentI = currentI->next;
		}
	}

	void drrs_axiom(Link1<Index4>* input, LinkL<Index4>* axioms, int level, Prefix* pi) {
		Link1<Index4>* currentI = axioms->head;
		while (currentI != NULL) {
			Link1<Lit>* current_lit_other = currentI->data.clause->head;
			while (current_lit_other != NULL) {
				Link1<Lit>* current_lit_self = input->data.clause->head;
				Lit q = current_lit_other->data;
				if (pi->lvl(q.var)> level){
				while (current_lit_self != NULL) {
					current_lit_self = current_lit_self->next;
					Lit p = current_lit_self->data;
					if (p==-q) {
						drrs_axiom_entry(-p, currentI, axioms, level, pi);
					}
				}
				}
				current_lit_other = current_lit_other->next;
			}
			
			currentI = currentI->next;
		}
	}

	void drrs_axioms(LinkL<Index4>* axioms, int level, Prefix* pi) {
		Link1<Index4>* current = axioms->head;
		while (current != NULL) {
			drrs_axiom(current, axioms, level, pi);
			current = current->next;
		}
	}


	void calculate_drrs(Index4* input, LinkL<Index4>* axioms, Prefix* Pi) {

	}


	void increment(Var* max_var, Prefix* P, Var* idx) {//adds a new extension variable
		int new_val= *max_var+1;
		*max_var = new_val;
		P->addvar(new_val);
		*idx= new_val;
	}

	int add_literal1(Var max_var, Index1* idx_line, Prefix* P, Clause C, int position) {
		Index1_1* temp = new Index1_1();
		increment(&max_var, P,&(temp->membership));
		temp->lit = C[position];
		idx_line->memberships->addnode(*temp);
		return max_var;
	}

	int add_line1(Var max_var, LinkL<Index1>* idx_layer, Prefix* P, ClausalProof* pi, int line_no) {// add an entry on memberships, taut and sel
		Index1* temp = new Index1();
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		Link1<Lit>* current = C.head;
		int position = 0;

		if (L.rule == RESOLUTION) {
			increment(&max_var, P, &(temp->selon));
			increment(&max_var, P, &(temp->selval));
		}
		increment(&max_var, P, &(temp->tautological));
		if (C.length > 0) {
			temp->membership_start = max_var + 1;
			while (current != NULL) {
				max_var = add_literal1(max_var, temp, P, C, position);
				current = current->next;
				position++;
			}
			temp->membership_end = max_var;
		}
		
		//if res
		
		//
		idx_layer->addnode(*temp);
		return max_var;
	}


	int add_layer1(Var max_var, LinkL<LinkL<Index1> >* idx_proof, Prefix* P, ClausalProof* pi) {
		LinkL<Index1>* temp = new LinkL<Index1>();
		Link1<Line<Clause>>* current = pi->head;
		int line_no = 0;
		while (current != NULL) {
			max_var= add_line1(max_var, temp, P, pi, line_no);
			current = current->next;
			line_no++;
		}
		idx_proof->addnode(*temp);
		return max_var;
	};

	int add_cell2(Var max_var, LinkL<Index2>* idx_row, Prefix* P, ClausalProof* pi, int line_no1, int line_no2) {
		Index2* temp = new Index2;
		increment(&max_var, P, &(temp->descendant));
		if (pi->operator[](line_no1).rule == RESOLUTION) {
			increment(&max_var, P, &(temp->dselval0));
			increment(&max_var, P, &(temp->dselval1));
		}
		idx_row->addnode(*temp);
		return max_var;
	}

	int add_row2(Var max_var, LinkL<LinkL<Index2>>* idx_array, Prefix* P, ClausalProof* pi, int line_no) {
		LinkL<Index2>* temp = new LinkL<Index2>;
		Link1<Line<Clause>>* current = pi->head;
		int line_no2=0;
		while (current != NULL) {
			max_var = add_cell2(max_var, temp, P, pi, line_no, line_no2);
			line_no2++;
			current = current->next;
		}
		idx_array->addnode(*temp);
		return max_var;
	}

	int backdef_array2(Var max_var, LinkL<LinkL<Index2>>* idx_array, Prefix* P, ClausalProof* pi) {
		//start at bot, bot
		int botpos = pi->tail->position;
		for (int j = botpos; j >= 0; j--) {//j is the second (column) index 
			for (int i = botpos; i >= 0; i--) {//i is the first (row) index
				LinkL <Index2> idx_row = idx_array->operator[](i);
				Link1<Index2>* idx_cell = idx_row.findnode(j);
				increment(&max_var, P, &(idx_cell->data.ancestor));
				if (pi->operator[](i).rule == RESOLUTION) {
					//increment(&max_var, P, &(idx_cell->data.xselon));
					increment(&max_var, P, &(idx_cell->data.aselval0));
					increment(&max_var, P, &(idx_cell->data.aselval1));
				}

			}
		}
		return max_var;
	}

	int add_array2(Var max_var, LinkL<LinkL<LinkL<Index2>>>* idx_conn, Prefix* P, ClausalProof* pi) {
		LinkL<LinkL<Index2>>* temp = new LinkL<LinkL<Index2>>();
		//need temp properties
		Link1<Line<Clause>>* current = pi->head;
		int line_no = 0;
		while (current != NULL) {
			max_var = add_row2(max_var, temp, P, pi, line_no);
			line_no++;
			current = current->next;
		}
		max_var = backdef_array2(max_var, temp, P, pi);
		idx_conn->addnode(*temp);
		
		return max_var;
	}



	int add_disjunct3(Var max_var, Index3* idx_u, Prefix* P, int line_no) {
		Index3_1* temp= new Index3_1;
		temp->line_no = line_no;
		increment(&max_var, P, &(temp->xmembership));
		idx_u->disjuncts->addnode(*temp);
		return max_var;
	}

	int add_u3(Var max_var, LinkL<Index3>* idx_strat, Prefix* P, ClausalProof* pi, Var u) {

		Index3* temp = new Index3();
		temp->u = u;
		Link1<Line<Clause>>* current = pi->head;
		temp->xmembership_start = max_var + 1;
		bool found_axiom = 0;
		while (current != NULL) {
			if (current->data.rule == AXIOM) {
				//check all literals
				Link1<Lit>* current_lit = current->data.clause.head;
				int upos=-1;
				while(current_lit != NULL) {
					if (current_lit->data == Lit(u)) {
						
						upos = current_lit->position;
					}
					current_lit = current_lit->next;
				}
				if (upos != -1) {
					found_axiom = 1;
					max_var= add_disjunct3(max_var, temp, P, current->position);
				}
			}
			current = current->next;
		}
		if (found_axiom) {
			temp->xmembership_end = max_var;
		}
		else {
			temp->xmembership_start = 0;
		}
		increment(&max_var, P, &(temp->strategy));
		idx_strat->addnode(*temp);
		return max_var;
	}

	struct Index {
		int base_max_var;
		int idx_max_var;
		Prefix* idx_prefix;
		LinkL<LinkL<Index1> >* Idx_Proof; //indices: level, line_no
		LinkL<LinkL<LinkL<Index2>>>* Idx_Conn;// indices: level, line_no1, line_no2;
		LinkL<Index3>* Idx_Strategy;// indices: universal


		Index() {
			idx_prefix = new Prefix();
			base_max_var = 0;
			idx_max_var = 0;
			Idx_Proof = new LinkL<LinkL<Index1> >;
			Idx_Conn = new LinkL<LinkL<LinkL<Index2>>>;
			Idx_Strategy = new LinkL<Index3>;
		};

		Index(QCNF phi, ClausalProof* pi) {
			idx_prefix = new Prefix();
			base_max_var = phi.matrix.max_var();
			Idx_Proof = new LinkL<LinkL<Index1> >;
			Idx_Conn = new LinkL<LinkL<LinkL<Index2>>>;
			Idx_Strategy = new LinkL<Index3>;
			int max_var = base_max_var;
			Link1<Quantifier>* currentQ = phi.prefix.head;
			//zeroeth level
			//create a layer (<LinkL<Index1>) for Idx_Proof
				//create lines (<Index1>) for the layer
					//create idx 1_1 for the lines
					//add each idx 1_1 addnode()
				//add each line
			//add each layer
			max_var = add_layer1(max_var, Idx_Proof, idx_prefix, pi);
			max_var = add_array2(max_var, Idx_Conn, idx_prefix, pi);
			while (currentQ != NULL) {
				if (currentQ->data.is_universal) {// add strategy
					max_var = add_u3(max_var, Idx_Strategy, idx_prefix, pi, currentQ->data.var);
				}


				//add the base variables to idx_prefix
				if (currentQ->data.is_universal) {
					idx_prefix->addvar(-currentQ->data.var);
				}
				else {
					idx_prefix->addvar(currentQ->data.var);
				}
				bool is_next_quant_a_change = 1;
				if (currentQ->next != NULL) {
					if (currentQ->next->data.is_universal == currentQ->data.is_universal) {
						is_next_quant_a_change = 0;
					}
				}

				if (is_next_quant_a_change) {// add restricted proof
					max_var = add_layer1(max_var, Idx_Proof, idx_prefix, pi);
					max_var = add_array2(max_var, Idx_Conn, idx_prefix, pi);

				}
				currentQ = currentQ->next;
			}
			idx_max_var = max_var;
		}

		void display(Prefix P) {
			int proof_length = Idx_Conn->head->data.length;
			Link1<Quantifier>* currentQ = P.head;
			int i = 0;
			while (currentQ != NULL) {
				bool is_next_quant_a_change = 1;
				if (currentQ->next != NULL) {
					if (currentQ->next->data.is_universal == currentQ->data.is_universal) {
						is_next_quant_a_change = 0;
					}
				}
				
				if (is_next_quant_a_change) {
					cout << endl << "E \t \t";
					for (int i = 0; i < proof_length; i++) {
						cout << "line" << i << "\t";
					}
					cout << endl;
					cout<< "membership:\t"; display(MEMBERSHIP, i);
					cout << "tautological:\t"; display(TAUTOLOGICAL, i);
					cout << "sel on:\t\t"; display(SELON, i);
					cout << "sel val:\t"; display(SELVAL, i);
					cout << endl << "    \t";
					for (int i = 0; i < proof_length; i++) {
						cout << "line" << i << "\t";
					}
					cout << endl;
					cout << "descendant:\n";
					display(DESCENDANT, i);
					cout << "ancestor:\n";
					display(ANCESTOR, i);
					//cout << "xselon:\n";
					//display(XANCESTORSELON, i);
					cout << "xselval0:\n";
					display(XANCESTORSELVAL0, i);
					cout << "xselval1:\n";
					display(XANCESTORSELVAL1, i);

					i++;
				}
				if (currentQ->data.is_universal) {
					cout << "E Strategy: ";
					display(XANCESTORMEMBERSHIP, currentQ->data.var);
					cout << "\t";
					display(STRATEGY, currentQ->data.var);
					cout << endl;
					cout << "A";
				}
				else {
					cout << "E";
				}
				cout << currentQ->data.var;
				currentQ = currentQ->next;
			}
		}


		void display(AbsType a, int level) {// displays all indices for a specified type
			if ((a == TAUTOLOGICAL) || (a== SELON) || (a==SELVAL) || (a==MEMBERSHIP)) {
				LinkL<Index1> layer = Idx_Proof->operator[](level);
				Link1<Index1>* current = layer.head;
				while (current != NULL) {
					if ((a == TAUTOLOGICAL) && (current->data.tautological > 0)) {
						cout << current->data.tautological;
					}
					if ((a == SELON) && (current->data.selon > 0)) {
						cout << current->data.selon;
					}
					if ((a == SELVAL) && (current->data.selval > 0)) {
						cout << current->data.selval;
					}
					if ((a == MEMBERSHIP) && (current->data.membership_start > 0)) {
						cout << current->data.membership_start << "-"<< current->data.membership_end;
					}
					cout<< "\t";
					current = current->next;
				}
				cout << endl;
			}
			if ((a == DESCENDANT) || (a == ANCESTOR) || (a == XANCESTORSELON) || (a == XANCESTORSELVAL0) || (a == XANCESTORSELVAL1)) {
				LinkL<LinkL<Index2>> layer = Idx_Conn->operator[](level);
				Link1<LinkL<Index2>>* current_row = layer.head;
				int row_no = 0;
				while (current_row != NULL) {
					Link1<Index2>* current_cell = current_row->data.head;
					cout << "line"<< row_no << "\t";
					row_no++;
					for (int i = 0;  i < layer.length; i++) {
						if (i >= 0) {
							if ((a == DESCENDANT) && (current_cell->data.descendant > 0)) {
								cout << current_cell->data.descendant;
							}
							if ((a == ANCESTOR) && (current_cell->data.ancestor > 0)) {
								cout << current_cell->data.ancestor;
							}
							/*if ((a == XANCESTORSELON) && (current_cell->data.xselon > 0)) {
								cout << current_cell->data.xselon;
							}*/
							if ((a == XANCESTORSELVAL0) && (current_cell->data.aselval0 > 0)) {
								cout << current_cell->data.aselval0;
							}
							if ((a == XANCESTORSELVAL1) && (current_cell->data.aselval1 > 0)) {
								cout << current_cell->data.aselval1;
							}
							current_cell = current_cell->next;
						}
						else {
							cout << "X";
						}
						cout << "\t";
					}
					cout << endl;
					current_row = current_row->next;
				}
			}
			if ((a == STRATEGY) || (a == XANCESTORMEMBERSHIP)) {
				Var u = level;
				Index3 layer= Idx_Strategy->operator[](universal_index(u, *idx_prefix));
				if ((a == XANCESTORMEMBERSHIP) && (layer.xmembership_start > 0)) {
					cout << layer.xmembership_start << "-" << layer.xmembership_end;
				}
				if ((a == STRATEGY) && (layer.strategy > 0)) {
					cout << layer.strategy;
				}
				
			}

		}
	};

	Lit AbsIdx(AbsLit input, Index* I, Prefix* P, ClausalProof* pi) {
		bool b = input.is_pos;
		if (input.type == BASE) {
			return Lit(input.level, b);
		}
		if ((input.type == STRATEGY) || (input.type== XANCESTORMEMBERSHIP)) {
			int u = input.level;
			int u_lvl= universal_index(u,*P);
			Index3 layer = I->Idx_Strategy->operator[](u_lvl);
			if ((input.type == STRATEGY) && (layer.strategy > 0)) {
				return Lit(layer.strategy, b);
			}
			if ((input.type == XANCESTORMEMBERSHIP) && (layer.xmembership_end > 0)) {
				Link1<Index3_1>* current = layer.disjuncts->head;
				while (current!=NULL) {
					if (input.index1 == current->data.line_no) {
						return Lit(current->data.xmembership, b);
					}
					current = current->next;
				}
			}
		}
		else {
			if ((input.type == TAUTOLOGICAL) || (input.type == SELON) || (input.type == SELVAL) || (input.type == MEMBERSHIP)) {
				LinkL<Index1> layer = I->Idx_Proof->operator[](input.level);
				Index1 current = layer.operator[](input.index1);
				
					if ((input.type == TAUTOLOGICAL) && (current.tautological > 0)) {
						return Lit(current.tautological, b);
					}
					if ((input.type == SELON) && (current.selon > 0)) {
						return Lit(current.selon, b);
					}
					if ((input.type == SELVAL) && (current.selval > 0)) {
						return Lit(current.selon, b);
					}
					if ((input.type == MEMBERSHIP) && (current.membership_start > 0)) {
						Index1_1 member = current.memberships->operator[](input.index2);
						if (member.membership > 0) {
							return Lit(member.membership, b);
						}
					}
			}
			else {
				if ((input.type == DESCENDANT) || (input.type == ANCESTOR) || (input.type == XANCESTORSELON) || (input.type == XANCESTORSELVAL0) || (input.type == XANCESTORSELVAL1)) {
					LinkL<LinkL<Index2>> layer = I->Idx_Conn->operator[](input.level);
					LinkL<Index2> row = layer[input.index1];
					Index2 cell = row[input.index2];
					if ((input.type == DESCENDANT) && (cell.descendant > 0)) {
						return Lit(cell.descendant, b);
					}
					if ((input.type == ANCESTOR) && (cell.ancestor > 0)) {
						return Lit(cell.ancestor, b);
					}
					//if ((input.type == XANCESTORSELON) && (cell.xselon > 0)) {
					//	return Lit(cell.xselon, b);
					//}
					if ((input.type == XANCESTORSELVAL0) && (cell.aselval0 > 0)) {
						return Lit(cell.aselval0, b);
					}
					if ((input.type == XANCESTORSELVAL1) && (cell.aselval1 > 0)) {
						return Lit(cell.aselval1, b);
					}
				}
			}
		}
	}

}