#pragma once
#pragma once
#include "QRAT.h"
#include "File.h"
#include "Circuits.h"
using namespace ccircuits;
namespace circuitmultilinear {
	struct IndexLit {
		Lit lit;
		

		bool bzeromem;
		bool bonemem;
		bool bmem;

		Var vzeromem;
		Var vonemem;
		Var vmem;

		Circuit* czeromem;
		Circuit* conemem;
		Circuit* cmem;

		IndexLit() {
			lit = Lit();

			bzeromem = 0;
			bonemem = 0;
			bmem = 0;

			vzeromem = 0;
			vonemem = 0;
			vmem = 0;

			czeromem = new Circuit();
			conemem = new Circuit();
			cmem = new Circuit();
		}

		void display() {
			cout << lit.DIMACS() << ":" << vmem << " ";
		}

	};
	struct IndexLine {
		LinkL<IndexLit>* memberships;
		
		bool bnp1;
		bool bx0p1;
		bool bseloff;
		bool bprevon;
		bool bvalonprev;
		bool b1selval;
		bool b0selval;
		bool bltrigger;
		bool brtrigger;
		bool bancestor;
		bool bzeroexsel;
		bool boneexsel;

		Var vnp1;
		Var vx0p1;
		Var vseloff;
		Var vprevon;
		Var vvalonprev;
		Var v1selval;
		Var v0selval;
		Var vltrigger;
		Var vrtrigger;
		Var vancestor;
		Var vzeroexsel;
		Var voneexsel;


		Circuit* cnp1;
		Circuit* cx0p1;
		Circuit* cseloff;
		Circuit* cprevon;
		Circuit* cvalonprev;
		Circuit* c1selval;
		Circuit* c0selval;
		Circuit* cltrigger;
		Circuit* crtrigger;
		Circuit* cancestor;
		Circuit* czeroexsel;
		Circuit* coneexsel;

		IndexLine() {
			memberships = new LinkL < IndexLit>;

			bnp1=0;
			bx0p1 = 0;
			bseloff = 0;
			bprevon = 0;
			bvalonprev = 0;
			b1selval = 0;
			b0selval = 0;
			bltrigger = 0;
			brtrigger = 0;
			bancestor = 0;
			bzeroexsel = 0;
			boneexsel = 0;

			vnp1 = 0;
			vx0p1 = 0;
			vseloff = 0;
			vprevon = 0;
			vvalonprev = 0;
			v1selval = 0;
			v0selval = 0;
			vltrigger = 0;
			vrtrigger = 0;
			vancestor = 0;
			vzeroexsel = 0;
			voneexsel = 0;

			cnp1 = new Circuit();
			cx0p1 = new Circuit();
			cseloff = new Circuit();
			cprevon = new Circuit();
			cvalonprev = new Circuit();
			c1selval = new Circuit();
			c0selval = new Circuit();
			cltrigger = new Circuit();
			crtrigger = new Circuit();
			cancestor = new Circuit();
			czeroexsel = new Circuit();
			coneexsel = new Circuit();

		}

		void display() {
			Link1<IndexLit>* current = memberships->head;
			while (current != NULL) {
				cout << current->data.lit.DIMACS() ;
				current = current->next;
				if (1) {
					cout << " ";
				}
			}
			cout << "0 \t";
			if (memberships->length ==2 ) {
				if (memberships->operator[](0).lit.is_pos || memberships->operator[](1).lit.is_pos) {
					cout << "\t";
				}
			}
			//cout << "0 ";
			cout << "np1:" << vnp1 << " ";
			cout << "x0p1:" << vx0p1 << " ";
			cout << "seloff:" << vseloff << " ";
			cout << "prevon:" << vprevon << " ";
			cout << "valonprev:" << vvalonprev << " ";
			cout << "1selval:" << v1selval << " ";
			cout << "0selval:" << v0selval << " ";
			cout << "ltrigger:" << vltrigger << " ";
			cout << "rtrigger:" << vrtrigger << " ";
			cout << "ancestor:" << vancestor << " ";
			cout << "zeroexsel:" << vzeroexsel << " ";
			cout << "oneexsel:" << voneexsel << " ";
			current = memberships->head;
			while (current != NULL) {
				current->data.display();
				current = current->next;
			}
		}
	};
	struct IndexStrat {
		Var u;
		bool bsigma;
		Var vsigma;
		Circuit* csigma;
		//Circuit* circ_strategy;
		LinkL<int>* axioms;
		LinkL<int>* ucommitments;

		IndexStrat() {
			u = 0;
			bsigma = 0;
			vsigma = 0;
			csigma = new Circuit();
			//circ_strategy = new Circuit;

			axioms = new LinkL <int>;
			ucommitments = new LinkL <int>;
		}

	};
	struct Strategy_Extractor {
		QCNF* input_QBF;
		ClausalProof* input_proof;
		LinkL<Circuit>* output_circuit;
		Cnf* extension_clauses;
		Cnf* negated_assumptions;
		Cnf* output_cnf;
		QRAT_Proof* output_QRAT;
		LinkL<LinkL<IndexLine>>* main_index;
		LinkL<IndexStrat>* strategy_index;
		int base_max_var;
		int idx_max_var;
		Prefix* long_prefix;

		Strategy_Extractor() {
			input_QBF = new QCNF;
			input_proof = new ClausalProof;
			output_circuit = new LinkL<Circuit>;
			extension_clauses = new Cnf;
			negated_assumptions = new Cnf;
			output_cnf = new Cnf;
			output_cnf = new Cnf;
			output_QRAT = new QRAT_Proof();
			main_index = new LinkL<LinkL<IndexLine>>;
			strategy_index = new LinkL<IndexStrat>;
			base_max_var = 0;
			idx_max_var = 0;
			long_prefix = new Prefix;
		}
		Strategy_Extractor(QCNF* phi, ClausalProof* pi) {
			input_QBF = new QCNF();
			input_QBF->matrix = ccopy(phi->matrix);
			input_QBF->prefix = copy(phi->prefix);
			input_proof = pi;
			output_circuit = new LinkL<Circuit>;
			output_cnf = new Cnf;
			extension_clauses = new Cnf;
			negated_assumptions = new Cnf;
			output_QRAT = new QRAT_Proof();
			output_QRAT->Phi = *input_QBF;
			main_index = new LinkL<LinkL<IndexLine>>;
			strategy_index = new LinkL<IndexStrat>;
			base_max_var = phi->matrix.mvar;
			idx_max_var = base_max_var;
			long_prefix = new Prefix;
		}

		Link1<IndexStrat>* findu(Var u) {
			Link1<IndexStrat>* current = strategy_index->head;
			while (current != NULL) {
				if (current->data.u == u) {
					return current;
				}
				current = current->next;
			}
			return current;
		}

		void load_output_cnf_negated() {
			output_cnf->makeempty();
			copyinto(output_cnf, &(input_QBF->matrix));
			copyinto(output_cnf, extension_clauses);
			copyinto(output_cnf, negated_assumptions);
		}

		void display_index() {
			Link1<LinkL<IndexLine>>* current_layer = main_index->head;
			int level = 0;
			while (current_layer != NULL) {
				cout<< "Displaying for level: " << level << endl;
				Link1<IndexLine>* current = current_layer->data.head;
				while (current != NULL) {
					current->data.display();
					cout << endl;
					current = current->next;
				}

				current_layer = current_layer->next;
				level++;
			}
		}
	};

	//label assgnments
	void increment(Var* max_var, Prefix* P, Var* idx) {//adds a new circuit label
		int new_val = *max_var + 1;
		*max_var = new_val;
		P->addvar(new_val);
		*idx = new_val;
	}
	int add_literal1(Var max_var, IndexLine* idx_line, Prefix* P, Clause C, int position) {
		IndexLit* temp = new IndexLit();
		increment(&max_var, P, &(temp->vonemem));
		increment(&max_var, P, &(temp->vzeromem));
		increment(&max_var, P, &(temp->vmem));
		temp->lit = C[position];
		idx_line->memberships->addnode(*temp);
		
		return max_var;
	}
	int add_IndexLine(Var max_var, LinkL<IndexLine>* idx_layer, Prefix* P, ClausalProof* pi, int line_no) {// add an entry on memberships, taut and sel
		IndexLine* temp = new IndexLine();
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		Link1<Lit>* current = C.head;
		int position = 0;
		if (L.rule == RESOLUTION) {
			increment(&max_var, P, &(temp->vnp1));
			increment(&max_var, P, &(temp->vx0p1));
			increment(&max_var, P, &(temp->vprevon));
			increment(&max_var, P, &(temp->vvalonprev));
			increment(&max_var, P, &(temp->v1selval));
			increment(&max_var, P, &(temp->vseloff));
			increment(&max_var, P, &(temp->v0selval));
			increment(&max_var, P, &(temp->vltrigger));
			increment(&max_var, P, &(temp->vrtrigger));
			increment(&max_var, P, &(temp->vancestor));
			increment(&max_var, P, &(temp->vzeroexsel));
			increment(&max_var, P, &(temp->voneexsel));
		}
		if (C.length > 0) {
			//temp->membership_start = max_var + 1;
			while (current != NULL) {
				max_var = add_literal1(max_var, temp, P, C, position);
				current = current->next;
				position++;
			}
			//temp->membership_end = max_var;
		}
		idx_layer->addnode(*temp);
		return max_var;
	}


	int backdef_IndexLine(Var max_var, LinkL<IndexLine>* idx_column, Prefix* P, ClausalProof* pi) {
		int botpos = pi->tail->position;
		for (int i = botpos; i >= 0; i--) {//i is the first (row) index
			Link1<IndexLine>* idx_cell = idx_column->findnode(i);
			increment(&max_var, P, &(idx_cell->data.vancestor));
			if (pi->operator[](i).rule == RESOLUTION) {
				//increment(&max_var, P, &(idx_cell->data.xselon));
				increment(&max_var, P, &(idx_cell->data.vzeroexsel));
				increment(&max_var, P, &(idx_cell->data.voneexsel));
			}
		}
		return max_var;
	}
	int add_layer(Var max_var, LinkL<LinkL<IndexLine> >* idx_proof, Prefix* P, ClausalProof* pi) {
		LinkL<IndexLine>* temp = new LinkL<IndexLine>();
		Link1<Line<Clause>>* current = pi->head;
		int line_no = 0;
		while (current != NULL) {
			max_var = add_IndexLine(max_var, temp, P, pi, line_no);
			current = current->next;
			line_no++;
		}
		max_var = backdef_IndexLine(max_var, temp, P, pi);
		idx_proof->addnode(*temp);
		
		return max_var;
	};
	int add_disjunct(Var max_var, IndexStrat* idx_u, Prefix* P, int line_no) {
		int* temp = new int;
		*temp = line_no;
		idx_u->axioms->addnode(*temp);
		return max_var;
	}
	int add_universal(Var max_var, LinkL<IndexStrat>* idx_strat, Prefix* P, ClausalProof* pi, Var u) {
		IndexStrat* temp = new IndexStrat();
		temp->u = u;
		Link1<Line<Clause>>* current = pi->head;
		//temp->xmembership_start = max_var + 1;
		bool found_axiom = 0;
		while (current != NULL) {
			if (current->data.rule == AXIOM) {
				Link1<Lit>* current_lit = current->data.clause.head;
				int upos = -1;
				while (current_lit != NULL) {
					if (current_lit->data == -Lit(u)) {

						upos = current_lit->position;
					}
					current_lit = current_lit->next;
				}
				if (upos != -1) {
					found_axiom = 1;
					max_var = add_disjunct(max_var, temp, P, current->position);
				}
			}
			current = current->next;
		}
		increment(&max_var, P, &(temp->vsigma));
		idx_strat->addnode(*temp);
		return max_var;
	}


	void def_line(Strategy_Extractor* SE, IndexLine read, int level, int line_no) {
		Prefix P = SE->input_QBF->prefix;
		ClausalProof* pi = SE->input_proof;
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		QRAT_Proof* qrat = SE->output_QRAT;
		int position = 0;
		if (L.rule == AXIOM) {
			if (C.length > 0) {
				Link1<Lit>* current = C.head;
				while (current != NULL) {
					Lit l = current->data;
					int d = l.var;
					int ml = read.memberships->operator[](position).vmem;
					if (P.lvl(l.var) <= level) {
						if (is_universal(l.var, P)) {
							d= SE->findu(l.var)->data.vsigma;
						}
						if (l.is_pos) {
							read.memberships->operator[](position).cmem->defequiv(ml, d);
						}
						else {
							read.memberships->operator[](position).cmem->defNOT(ml, d);
						}
						
						//meml=x
					}
					else {
						read.memberships->operator[](position).cmem->def1(ml);
						
						//meml is true
					}
					current = current->next;
					position++;
				}
			}
		}
		if (L.rule == RESOLUTION) {
			int parent0 = L.parent0;
			int litpos0 = L.litpos0;
			int parent1 = L.parent1;
			int litpos1 = L.litpos1;
			int p0 = SE->main_index->operator[](level).operator[](parent0).memberships->operator[](litpos0).vmem;
			int p1 = SE->main_index->operator[](level).operator[](parent1).memberships->operator[](litpos1).vmem;
			
			read.cnp1->defNOT(read.vnp1, p1);
			read.cx0p1->defAND(read.vx0p1, p0, read.vnp1);
			//read.cseloff->defAND(read.vseloff, p0, p1);
			

			

			if (level > 0) {
				read.cprevon->defNOT(read.vprevon, SE->main_index->operator[](level - 1).operator[](line_no).vseloff);
				read.cvalonprev->defAND(read.vvalonprev, read.vprevon, SE->main_index->operator[](level - 1).operator[](line_no).v1selval);
				read.c1selval->defOR(read.v1selval, read.vx0p1, read.vvalonprev);
				LinkL<int> selofftriple;
				selofftriple.addnode(p0);
				selofftriple.addnode(p1);
				selofftriple.addnode(SE->main_index->operator[](level - 1).operator[](line_no).vseloff);
				read.cseloff->defAND(read.vseloff, selofftriple);
				selofftriple.makeempty();
				//selon= prevvon or -p0 or -p1
				//selval= (prevvon and prevval) or (p0 and -p1)
			}
			else {
				read.c1selval->defequiv(read.v1selval, read.vx0p1);
				read.cseloff->defAND(read.vseloff, p0, p1);

				//selon= -p0 or -p1
				//selval= p0 and -p1
			}
			read.c0selval->defNOT(read.v0selval, read.v1selval);//why is this not working
			read.cltrigger->defOR(read.vltrigger, read.v0selval, read.vseloff);
			read.crtrigger->defOR(read.vrtrigger, read.v1selval, read.vseloff);

			Clause P0 = pi->operator[](parent0).clause;
			Clause P1 = pi->operator[](parent1).clause;
			Link1<Lit>* current = L.clause.head;
			int lit_counter = 0;
			while (current != NULL) {
				Lit l = current->data;
				int pos0 = find_a_position(l, P0);
				int pos1 = find_a_position(l, P1);
				int mem =  read.memberships->operator[](lit_counter).vmem;
				int lmem = read.memberships->operator[](lit_counter).vzeromem;
				int rmem = read.memberships->operator[](lit_counter).vonemem;
			
				if ((pos0 == -1) && (pos1 != -1)) {
					int mem1 = SE->main_index->operator[](level).operator[](parent1).memberships->operator[](pos1).vmem;
					read.memberships->operator[](lit_counter).conemem->defAND(rmem, mem1, read.vrtrigger);
					read.memberships->operator[](lit_counter).czeromem->def0(lmem);

					//meml= mem1 and (-selval or -selon)
				}
				if ((pos0 != -1) && (pos1 == -1)) {
					int mem0 = SE->main_index->operator[](level).operator[](parent0).memberships->operator[](pos0).vmem;
					read.memberships->operator[](lit_counter).czeromem->defAND(lmem, mem0, read.vltrigger);
					read.memberships->operator[](lit_counter).conemem->def0(rmem);

					//meml= mem0 and (selval or -selon)
				}
				if ((pos0 != -1) && (pos1 != -1)) {
					int mem0 = SE->main_index->operator[](level).operator[](parent0).memberships->operator[](pos0).vmem;
					int mem1 = SE->main_index->operator[](level).operator[](parent1).memberships->operator[](pos1).vmem;
					read.memberships->operator[](lit_counter).czeromem->defAND(lmem, mem0, read.vltrigger);
					read.memberships->operator[](lit_counter).conemem->defAND(rmem, mem1, read.vrtrigger);

					//meml= (mem0 and (-selval or -selon)) or (mem1 and (-selval or selon))
				}
				read.memberships->operator[](lit_counter).cmem->defOR(mem, lmem, rmem);
				lit_counter++;
				current = current->next;
			}

		}
		if (L.rule == REDUCTION) {
			int parent = L.parent0;
			Clause P = pi->operator[](parent).clause;
			Link1<Lit>* current = L.clause.head;
			int lit_counter = 0;
			while (current != NULL) {
				Lit l = current->data;
				int pos = find_a_position(l, P);
				int meml = read.memberships->operator[](lit_counter).vmem;
				int parl = SE->main_index->operator[](level).operator[](parent).memberships->operator[](pos).vmem;
				read.memberships->operator[](lit_counter).cmem->defequiv(meml, parl);
				//meml= parl
				lit_counter++;
				current = current->next;
			}
		}
	}

	void backdef_cell(Strategy_Extractor* SE, IndexLine cell, int level, int line_no1, int new_sink, LinkL<int>* backwards_list) {
		ClausalProof* pi = SE->input_proof;
		Prefix P = SE->input_QBF->prefix;
		int line_no2 = new_sink;
		int al = cell.vancestor;
		Line<Clause> L1 = pi->operator[](line_no1);
		if (line_no1 >= line_no2) {
			if (line_no1 == line_no2) {
				cell.cancestor->def1(cell.vancestor);
				//al is trivially true
			}
			else {
				cell.cancestor->def0(cell.vancestor);
				//al is trivially false
			}
		}
		else {
			Link1<int>* current_int_container = backwards_list->head;
			LinkL<int>ancdisj = LinkL<int>();
			while (current_int_container != NULL) {
				int i = current_int_container->data;
				Line L1child = pi->operator[](i);
				
				if (L1child.rule == REDUCTION) {
					if (L1child.parent0 == line_no1) {
						ancdisj.addnode(SE->main_index->operator[](level).operator[](i).vancestor);
						//al= achild
					}
				}
				if (L1child.rule == RESOLUTION) {
					if (L1child.parent0 == line_no1) {
						ancdisj.addnode(SE->main_index->operator[](level).operator[](i).vzeroexsel);
					}
					if (L1child.parent1 == line_no1) {
						ancdisj.addnode(SE->main_index->operator[](level).operator[](i).voneexsel);
					}
					//a = big disjunction
				}
				current_int_container = current_int_container->next;
			}
			cell.cancestor->defOR(cell.vancestor, ancdisj);

		}
		if (L1.rule == RESOLUTION) {
			cell.czeroexsel->defAND(cell.vzeroexsel, cell.vancestor, cell.vltrigger);
			cell.coneexsel->defAND(cell.voneexsel, cell.vancestor, cell.vrtrigger);
			//ext0l= a and (-selon or -selval)
			//ext1l= a and (-selon or selval)
			

		}
	}


	void def_universal(Strategy_Extractor* SE, LinkL <IndexStrat>* idx_strat, Var u, int a_base, bool is_unsat) {//version for a_base
		Link1<IndexStrat>* current_u = idx_strat->head;
		Prefix P = SE->input_QBF->prefix;
		while (current_u != NULL) {
			if (current_u->data.u == u) {
				Link1<int>* current_line = current_u->data.axioms->head;
				LinkL<int> sigmadisj;
				Lit ul = Lit(current_u->data.vsigma);
				int level = P.lvl(u) - 1;
				while (current_line != NULL) {
					int axpos = current_line->data;
					int conn = SE->main_index->operator[](level).operator[](axpos).vancestor;
					sigmadisj.addnode(conn);
					current_line = current_line->next;
				}
				current_u->data.csigma->defOR(current_u->data.vsigma, sigmadisj);
				sigmadisj.makeempty();
				
				//sigmau= big_or conn(negative u)
				Clause uforward;
				uforward.addnode(-ul);
				uforward.addnode(Lit(u));
				SE->negated_assumptions->addnode(uforward);//not acceptable in QRAT
				Clause ubackward;
				ubackward.addnode(ul);
				ubackward.addnode(-Lit(u));
				SE->negated_assumptions->addnode(ubackward);//not acceptable in QRAT
			}
			current_u = current_u->next;
		}
	
	}
	void while_load(Circuit* temp, Strategy_Extractor* SE, int a_base, int i, LinkL<int>* connected_lines) {

		//connected_lines->addnode(a_base);
		ClausalProof* proof_address = SE->input_proof;
		// = connectedlines(proof_address, a_base);
		Link1<int>* current = connected_lines->head;


		int max_lvl = SE->input_QBF->prefix.tail->data.level;
		current = connected_lines->tail;
		while (current != NULL) {
			//load all clauses systematically
			IndexLine lineindex = SE->main_index->operator[](i).operator[](current->data);
			//SE->output_cnf->add_comment("Defining restricted proof line:");
			//SE->output_cnf->add_comment("selon:");
			//copyinto(output, lineindex.def_selon);
			// 
			//SE->output_cnf->add_comment("selval:");
			//copyinto(output, lineindex.def_selval);
			temp->addcircuit(*(lineindex.cnp1));
			temp->addcircuit(*(lineindex.cx0p1));
			temp->addcircuit(*(lineindex.cprevon));
			temp->addcircuit(*(lineindex.cvalonprev));
			temp->addcircuit(*(lineindex.c1selval));
			temp->addcircuit(*(lineindex.cseloff));
			
			
			temp->addcircuit(*(lineindex.c0selval));
			temp->addcircuit(*(lineindex.cltrigger));
			temp->addcircuit(*(lineindex.crtrigger));



			//SE->output_cnf->add_comment("membership:");
			Link1<IndexLit>* litindex = lineindex.memberships->head;
			while (litindex != NULL) {
				//copyinto(output, litindex->data.def_membership);
				temp->addcircuit(*(litindex->data.czeromem));
				temp->addcircuit(*(litindex->data.conemem));
				temp->addcircuit(*(litindex->data.cmem));
				litindex = litindex->next;
			}

			current = current->prev;
		}
		current = connected_lines->head;
		while (current != NULL) {
			//SE->output_cnf->add_comment("Defining connectivity from a_base");
			IndexLine lineindex = SE->main_index->operator[](i).operator[](current->data);
			//SE->output_cnf->add_comment("anc:");
			temp->addcircuit(*(lineindex.cancestor));
			temp->addcircuit(*(lineindex.czeroexsel));
			temp->addcircuit(*(lineindex.coneexsel));
			current = current->next;
		}
		return;
	}

	void load_universal(Circuit* temp, Strategy_Extractor* SE, LinkL <IndexStrat>* idx_strat, Var u, int a_base, bool is_unsat) {
		Link1<IndexStrat>* current_u = idx_strat->head;
		Prefix P = SE->input_QBF->prefix;
		while (current_u != NULL) {
			if (current_u->data.u == u) {
				
				Link1<IndexStrat>* previous_u = current_u->prev;
				temp->addcircuit(*(current_u->data.csigma));
				Circuit temp2 = Circuit();
				temp2.addcircuit(*temp);
				SE->output_circuit->addnode(temp2);
				return;
			}

			current_u = current_u->next;
		}
	}

	void def_layer(Strategy_Extractor* SE, LinkL<LinkL<IndexLine> >* idx_proof, Prefix P, ClausalProof* pi, int level, int new_sink, LinkL<int>* backwards_list) {
		LinkL<IndexLine>* read = &SE->main_index->findnode(level)->data;
		Link1<IndexLine>* current = read->head;
		int botpos = pi->tail->position;
		int line_no = 0;
		while (current != NULL) {//cycles through all lines
			def_line(SE, current->data, level, line_no);
			current = current->next;
			line_no++;
		}
		current = read->tail;
		line_no = botpos;
		while (current != NULL) {//cycles through all lines
			backdef_cell(SE, current->data, level, line_no, new_sink, backwards_list);
			current = current->prev;
			line_no--;
		}
		//idx_proof->addnode(*temp);
		return;
	};

	bool is_last_universal(Link1<Quantifier>* inputQ) {
		if (inputQ == NULL) {
			return 0;
		}
		if (inputQ->data.is_universal == 0) {
			return 0;
		}

		Link1<Quantifier>* currentQ = inputQ->next;
		while (currentQ != NULL) {
			if (currentQ->data.is_universal == 1) {
				return 0;
			}
			currentQ = currentQ->next;
		}
		return 1;
	}

	LinkL<int>* connectedlines(ClausalProof* proof_address, int a_base) {
		LinkL<int>* connected_lines = new LinkL<int>;
		connected_lines->addnode(a_base);
		Link1<int>* current = connected_lines->head;
		while (current != NULL) {//while empty list
			int parent0 = proof_address->operator[](current->data).parent0;
			if (parent0 > -1) {
				bool is_repeat = 0;
				Link1<int>* current2 = connected_lines->head;
				while (current2 != NULL) {

					if (current2->data == parent0) {
						is_repeat = 1;
					}
					current2 = current2->next;
				}
				if (!is_repeat) {
					connected_lines->addnode(parent0);
				}
			}
			int parent1 = proof_address->operator[](current->data).parent1;
			if (parent1 > -1) {
				bool is_repeat = 0;
				Link1<int>* current2 = connected_lines->head;
				while (current2 != NULL) {

					if (current2->data == parent1) {
						is_repeat = 1;
					}
					current2 = current2->next;
				}
				if (!is_repeat) {
					connected_lines->addnode(parent1);
				}
			}
			current = current->next;
		}
		return connected_lines;
	}

	void negatebase(Cnf* output, Strategy_Extractor* SE, int a_base, bool is_unsat) {
		if (is_unsat) {
			ClausalProof* proof = SE->input_proof;
			Clause clause = proof->operator[](a_base).clause;
			Link1<Lit>* current = clause.head;
			while (current != NULL) {
				Lit l = current->data;
				Clause unit;
				unit.addnode(-l);
				output->addnode(unit);
				current = current->next;
			}
		}
		return;
	}


	Strategy_Extractor* Extract(QCNF* phi, ClausalProof* pi, int a_base, bool is_unsat) {
		Strategy_Extractor* output = new Strategy_Extractor(phi, pi);
		output->main_index = new LinkL<LinkL<IndexLine>>;
		Circuit* temp = new Circuit();
		output->strategy_index = new LinkL<IndexStrat>;
		int max_var = output->base_max_var;
		Link1<Quantifier>* currentQ = phi->prefix.head;
		int layer_level = 0;
		LinkL<int>* backwards_list = connectedlines(pi, a_base);
		max_var = add_layer(max_var, output->main_index, output->long_prefix, pi);
		def_layer(output, output->main_index, output->input_QBF->prefix, pi, layer_level, a_base, backwards_list);
		while_load(temp, output, a_base, layer_level, backwards_list);
		while (currentQ != NULL) {
			if (currentQ->data.is_universal) {// add strategy
				max_var = add_universal(max_var, output->strategy_index, output->long_prefix, pi, currentQ->data.var);
				def_universal(output, output->strategy_index, currentQ->data.var, a_base, is_unsat);
				load_universal(temp, output, output->strategy_index, currentQ->data.var, a_base, is_unsat);
				if (is_last_universal(currentQ)) {
					//negatebase(output->negated_assumptions, output, a_base, is_unsat);
					negatebase(output->negated_assumptions, output, a_base, is_unsat);
					output->idx_max_var = max_var;
					Cnf load = ccircuits::extclauses(*temp);
					copyinto(output->extension_clauses, &(load));
					return output;
				}
				//look ahead for any more universals
				//while loop for 
				//
			}
			//add the base variables to idx_prefix
			if (currentQ->data.is_universal) {
				output->long_prefix->addvar(-currentQ->data.var);
			}
			else {
				output->long_prefix->addvar(currentQ->data.var);
			}
			bool is_next_quant_a_change = 1;
			if (currentQ->next != NULL) {

				if (currentQ->next->data.is_universal == currentQ->data.is_universal) {
					is_next_quant_a_change = 0;
				}
			}

			if (is_next_quant_a_change) {// add restricted proof
				layer_level++;
				max_var = add_layer(max_var, output->main_index, output->long_prefix, pi);
				def_layer(output, output->main_index, output->input_QBF->prefix, pi, layer_level, a_base, backwards_list);
				while_load(temp, output, a_base, layer_level, backwards_list);
			}
			currentQ = currentQ->next;
		}
		negatebase(output->negated_assumptions, output, a_base, is_unsat);
		output->idx_max_var = max_var;
		Cnf load = ccircuits::extclauses(*temp);
		copyinto(output->extension_clauses, &(load));
		return output;
	}

	ClausalProof restricted_proof(Strategy_Extractor* SE, LinkL<int> input, int level) {
		
		//calculate level
		//padd out input,  with warnings
		//start building temp circuit
		Circuit* temp= new Circuit();
		ClausalProof output = ClausalProof();
		Link1<LinkL<IndexLine>>* layer = SE->main_index->head;
		Prefix P = SE->input_QBF->prefix;
		for (int i = 0; i < level; i++) {
			Link1<IndexStrat>* strat = SE->strategy_index->head;
			while (strat != NULL) {
				int u = strat->data.u;
				if (P.lvl(u) == i) {
					temp->addcircuit(*(strat->data.csigma));
				}
				strat = strat->next;
			}
			Link1<IndexLine>* current = layer->data.head;
			while (current != NULL) {
				//full load on temp;
				temp->addcircuit(*(current->data.cnp1));
				temp->addcircuit(*(current->data.cx0p1));
				
				temp->addcircuit(*(current->data.cprevon));
				temp->addcircuit(*(current->data.cvalonprev));
				temp->addcircuit(*(current->data.c1selval));
				temp->addcircuit(*(current->data.cseloff));
				temp->addcircuit(*(current->data.c0selval));
				temp->addcircuit(*(current->data.cltrigger));
				temp->addcircuit(*(current->data.crtrigger));
				Link1<IndexLit>* currentmem = current->data.memberships->head;
				while (currentmem != NULL) {
					temp->addcircuit(*(currentmem->data.czeromem));
					temp->addcircuit(*(currentmem->data.conemem));
					temp->addcircuit(*(currentmem->data.cmem));
					currentmem = currentmem->next;
				}

				current = current->next;
			}
			while (current != NULL) {
				temp->addcircuit(*(current->data.cancestor));
				temp->addcircuit(*(current->data.czeroexsel));
				temp->addcircuit(*(current->data.coneexsel));

				current = current->prev;
			}
			layer = layer->next;
		}
		LinkL<int> linput = temp->compute(input);
		Link1<IndexLine>* current = layer->data.head;
		while (current != NULL) {
			//full load on temp;
			int line_no = current->position;
			Line<Clause> L = SE->input_proof->operator[](line_no);
			Rule rule = L.rule;
			
			int lcnp1 = current->data.cnp1->int_compute(linput);
			linput.addnode(lcnp1);
			//temp->addcircuit(*(current->data.cnp1));
			int lcx0p1 = current->data.cx0p1->int_compute(linput);
			linput.addnode(lcx0p1);
			//temp->addcircuit(*(current->data.cx0p1));
			if (level > 0) {
				int lprevon = current->data.cprevon->int_compute(linput);
				linput.addnode(lprevon);
				//temp->addcircuit(*(current->data.cprevon));
				if (lprevon > 0 && (level == 1) && (rule == RESOLUTION)) {
					cout << "warning, level 0 selon on line " << line_no << endl;
				}
				int lvalonprev = current->data.cvalonprev->int_compute(linput);
				linput.addnode(lvalonprev);
				//temp->addcircuit(*(current->data.cvalonprev));
				if (lvalonprev>0 && (level == 1) && (rule == RESOLUTION)) {
					cout << "warning, level 0 missing lit on line " << line_no << endl;
				}
			}
			
			int l1selval = current->data.c1selval->int_compute(linput);
			linput.addnode(l1selval);
			//temp->addcircuit(*(current->data.c1selval));
			bool bselval = 0;
			if (rule == RESOLUTION) {
				bselval = temp->bool_compute(input);
			}

			int lseloff = current->data.cseloff->int_compute(linput);
			linput.addnode(lseloff);
			//temp->addcircuit(*(current->data.cseloff));
			if (L.rule == RESOLUTION) {
				bool bseloff = (lseloff > 0);
				if (!bseloff) {
					rule = SELECT;
				}
			}

			int l0selval = current->data.c0selval->int_compute(linput);
			linput.addnode(l0selval);
			//temp->addcircuit(*(current->data.c0selval));
			bool bnselval = 1;
			if (L.rule == RESOLUTION) {
				bnselval = (l0selval > 0);
			}

			int lltrigger = current->data.cltrigger->int_compute(linput);
			linput.addnode(lltrigger);
			//temp->addcircuit(*(current->data.cltrigger));
			bool bltrigger = (lltrigger > 0);
			//temp->addcircuit(*(current->data.crtrigger));
			int lrtrigger = current->data.crtrigger->int_compute(linput);
			linput.addnode(lrtrigger);
			bool brtrigger = (lrtrigger > 0);
			if ((L.rule == RESOLUTION) && !bselval && !bnselval) {
				cout << "error on law of excluded middle on Line " << line_no << endl;
			}
			if ((L.rule == RESOLUTION) && !bltrigger && !brtrigger) {
				cout << "error no selection on Line " << line_no << endl;
			}
			Clause C = Clause();
			Link1<IndexLit>* currentmem = current->data.memberships->head;
			while (currentmem != NULL) {
				int lzeromem = currentmem->data.czeromem->int_compute(linput);
				linput.addnode(lzeromem);
				int lonemem = currentmem->data.conemem->int_compute(linput);
				linput.addnode(lonemem);
				int lmem = currentmem->data.cmem->int_compute(linput);
				linput.addnode(lmem);
				bool bmem = (lmem > 0);
				if (bmem) {
					C.addnode(currentmem->data.lit);
				}
				currentmem = currentmem->next;
			}
			output.addline(C);
			
			output.tail->data.rule = rule;
			current = current->next;
		}
		/*
		while (current != NULL) {
			temp->addcircuit(*(current->data.cancestor));
			temp->addcircuit(*(current->data.czeroexsel));
			temp->addcircuit(*(current->data.coneexsel));

			current = current->prev;
		}
		*/
		
		return output;
	}

}
