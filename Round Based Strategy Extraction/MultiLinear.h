#pragma once
#include "QRAT.h"
namespace multilinear {
	struct IndexLit {
		bool is_membership_defined;
		Var membership;
		Cnf* def_membership;
		Lit lit;

		IndexLit() {
			is_membership_defined = 0;
			membership = 0;
			lit = Lit();
			def_membership = new Cnf;
		}
	};
	struct IndexLine {
		//bool is_tautological_defined;
		bool is_selon_defined;
		bool is_selval_defined;
		bool is_ancestor_defined;
		bool is_xselval0_defined;
		bool is_xselval1_defined;

		LinkL<IndexLit>* memberships;

		Var membership_start;
		Var membership_end;


		//Var tautological;
		//Cnf* def_tautological;

		Var selon;
		Cnf* def_selon;
		Var selval;
		Cnf* def_selval;

		Var ancestor;
		Cnf* def_ancestor;
		Var xselval0;
		Cnf* def_xselval0;
		Var xselval1;
		Cnf* def_xselval1;
	

		IndexLine() {
			//is_tautological_defined = 0;
			is_selon_defined = 0;
			is_selval_defined = 0;
			is_ancestor_defined =0;
			is_xselval0_defined =0;
			is_xselval1_defined =0;
			membership_start = 0;
			membership_end = 0;
			//tautological = 0;
			selon = 0;
			selval = 0;
			memberships = new LinkL < IndexLit>;
			//def_tautological = new Cnf;
			def_selon = new Cnf;
			def_selval = new Cnf;

			ancestor = 0;;
			def_ancestor = new Cnf;
			xselval0 = 0;;
			def_xselval0 = new Cnf;
			xselval1 = 0;;
			def_xselval1 = new Cnf;
		}
	};

	struct IndexStrat {
		Var u;
		bool is_strategy_defined;
		Var strategy;
		Cnf* def_strategy;
		LinkL<int>* axioms;

		IndexStrat() {
			is_strategy_defined = 0;
			strategy = 0;
			def_strategy = new Cnf;

			axioms = new LinkL <int>;
		}
	};

	struct Strategy_Extractor {
		QCNF* input_QBF;
		ClausalProof* input_proof;
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
			input_QBF->matrix = copy(phi->matrix);
			input_QBF->prefix = copy(phi->prefix);
			input_proof = pi;
			output_cnf = new Cnf;
			copyinto(output_cnf, &(phi->matrix));
			output_QRAT = new QRAT_Proof();
			output_QRAT->Phi = *input_QBF;
			base_max_var = phi->matrix.max_var();
			idx_max_var = base_max_var;
			long_prefix = new Prefix;
		}
	};

	void increment(Var* max_var, Prefix* P, Var* idx) {//adds a new extension variable
		int new_val = *max_var + 1;
		*max_var = new_val;
		P->addvar(new_val);
		*idx = new_val;
	}

	int add_literal1(Var max_var, IndexLine* idx_line, Prefix* P, Clause C, int position) {
		IndexLit* temp = new IndexLit();
		increment(&max_var, P, &(temp->membership));
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
			increment(&max_var, P, &(temp->selon));
			increment(&max_var, P, &(temp->selval));
		}
		//increment(&max_var, P, &(temp->tautological));
		if (C.length > 0) {
			temp->membership_start = max_var + 1;
			while (current != NULL) {
				max_var = add_literal1(max_var, temp, P, C, position);
				current = current->next;
				position++;
			}
			temp->membership_end = max_var;
		}
		idx_layer->addnode(*temp);
		return max_var;
	}

	int backdef_IndexLine(Var max_var, LinkL<IndexLine>* idx_column, Prefix* P, ClausalProof* pi) {
		//start at bot, bot
		int botpos = pi->tail->position;
			for (int i = botpos; i >= 0; i--) {//i is the first (row) index
				Link1<IndexLine>* idx_cell = idx_column->findnode(i);
				increment(&max_var, P, &(idx_cell->data.ancestor));
				if (pi->operator[](i).rule == RESOLUTION) {
					//increment(&max_var, P, &(idx_cell->data.xselon));
					increment(&max_var, P, &(idx_cell->data.xselval0));
					increment(&max_var, P, &(idx_cell->data.xselval1));
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
				//check all literals
				Link1<Lit>* current_lit = current->data.clause.head;
				int upos = -1;
				while (current_lit != NULL) {
					if (current_lit->data == Lit(u)) {

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
		increment(&max_var, P, &(temp->strategy));
		idx_strat->addnode(*temp);
		return max_var;
	}

	void def_line(Strategy_Extractor* SE, IndexLine read, int level, int line_no) {// add an entry on memberships, taut and sel
		//Index1* temp = new Index1();
		Prefix P = SE->input_QBF->prefix;
		ClausalProof* pi = SE->input_proof;
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		QRAT_Proof* qrat = SE->output_QRAT;
		int position = 0;
		if (L.rule == AXIOM) {
			//Clause taut_long;
			//Lit taut = Lit(read.tautological);//tautological implies clause less than level
			//taut_long.addnode(-taut);
			if (C.length > 0) {

				Link1<Lit>* current = C.head;
				while (current != NULL) {
					//def_literal1(max_var, temp, P, C, position);
					Lit l = current->data;
					Lit ml = Lit(read.memberships->operator[](position).membership);
					if (P.lvl(l.var) <= level) {
						//Clause taut_short;// any satisfied literal implies tautological
						//taut_short.addnode(-l);
						//taut_short.addnode(taut);
						//read.def_tautological->addnode(taut_short);//RATA on taut: trivial
						//qrat->QRATA(taut_short, taut);
						Clause mem_equiv1; //literal implies membership
						mem_equiv1.addnode(-l);
						mem_equiv1.addnode(ml);
						Clause mem_equiv2; //literal implies membership
						mem_equiv2.addnode(l);
						mem_equiv2.addnode(-ml);
						read.memberships->operator[](position).def_membership->addnode(mem_equiv1);//RATA on ml: trivial
						qrat->QRATA(mem_equiv1, ml);
						read.memberships->operator[](position).def_membership->addnode(mem_equiv2);//RATA on -ml: l, -l blocked on mem_equiv1
						qrat->QRATA(mem_equiv2, -ml);
						//taut_long.addnode(l);

					}
					else {
						Clause mem_assertion;
						mem_assertion.addnode(ml);
						read.memberships->operator[](position).def_membership->addnode(mem_assertion);//RATA on ml: trivial
						qrat->QRATA(mem_assertion, ml);
					}


					current = current->next;
					position++;
				}
			}
			//read.def_tautological->addnode(taut_long);//RATA on -taut: l, -l blocked on each taut_short
			//qrat->QRATA(taut_long, -taut);
		}
		if (L.rule == RESOLUTION) {


			int parent0 = L.parent0;
			int litpos0 = L.litpos0;
			int parent1 = L.parent1;
			int litpos1 = L.litpos1;
			Lit p0 = Lit(SE->main_index->operator[](level).operator[](parent0).memberships->operator[](litpos0).membership, 1);
			Lit p1 = Lit(SE->main_index->operator[](level).operator[](parent1).memberships->operator[](litpos1).membership, 1);
			Lit selonl = Lit(read.selon);
			Lit selvall = Lit(read.selval);
			Clause selon_long;//defines when selon is false i.e. none of the triggers
			selon_long.addnode(-selonl);

			Clause selon_p0;//asserts selon true when missing pivot at parent0
			selon_long.addnode(-p0);
			selon_p0.addnode(p0);
			selon_p0.addnode(selonl);
			read.def_selon->addnode(selon_p0);//RATA on selonl: trivial
			qrat->QRATA(selon_p0, selonl);
			Clause selon_p1;//asserts selon true when missing pivot at parent1
			selon_long.addnode(-p1);
			selon_p1.addnode(p1);
			selon_p1.addnode(selonl);
			read.def_selon->addnode(selon_p1);//RATA on selonl: trivial
			qrat->QRATA(selon_p1, selonl);
			Clause selval_0andnot1; //asserts selval when only pivot1 is missing;
			selval_0andnot1.addnode(selvall);
			selval_0andnot1.addnode(-p0);
			selval_0andnot1.addnode(p1);
			read.def_selval->addnode(selval_0andnot1);//RATA on selvall: trivial
			qrat->QRATA(selval_0andnot1, selvall);
			if (level > 0) {
				Lit prevon = Lit(SE->main_index->operator[](level - 1).operator[](line_no).selon, 1);
				Lit prevval = Lit(SE->main_index->operator[](level - 1).operator[](line_no).selval, 1);
				Clause selon_prev; //triggers if previous selon is true
				selon_long.addnode(prevon);
				selon_prev.addnode(-prevon);
				selon_prev.addnode(selonl);
				read.def_selon->addnode(selon_prev);//RATA on selonl: trivial
				qrat->QRATA(selon_prev, selonl);

				Clause selval_prevs;//triggers if previous selon is true and selval already true
				selval_prevs.addnode(-prevon);
				selval_prevs.addnode(-prevval);
				selval_prevs.addnode(selvall);
				read.def_selval->addnode(selval_prevs);//RATA on selvall: trivial
				qrat->QRATA(selval_prevs, selvall);

				Clause selval_0on;// sets selval FALSE if previous sel is off and current parent0 missing pivot
				Clause selval_0val;// sets selval FALSE if previous val is false and current parent0 missing pivot
				Clause selval_1on;// sets selval FALSE if previous sel is off and current parent1 contains pivot
				Clause selval_1val;// sets selval FALSE if previous val is false and current parent1 contains pivot

				selval_0on.addnode(-selvall);
				selval_0on.addnode(prevon);
				selval_0on.addnode(p0);
				read.def_selval->addnode(selval_0on);//RATA on -selvall, blocked by -prevon on selval_prevs, blocked by -p0 on selval_0andnot1
				qrat->QRATA(selval_0on, -selvall);


				selval_0val.addnode(-selvall);
				selval_0val.addnode(prevval);
				selval_0val.addnode(p0);
				read.def_selval->addnode(selval_0val);//RATA on -selvall, blocked by -prevval on selval_prevs, blocked by -p0 on selval_0andnot1
				qrat->QRATA(selval_0val, -selvall);

				selval_1on.addnode(-selvall);
				selval_1on.addnode(prevon);
				selval_1on.addnode(-p1);
				read.def_selval->addnode(selval_1on);//RATA on -selvall, blocked by -prevon on selval_prevs, blocked by p1 on selval_0andnot1
				qrat->QRATA(selval_1on, -selvall);

				selval_1val.addnode(-selvall);
				selval_1val.addnode(prevval);
				selval_1val.addnode(-p1);
				read.def_selval->addnode(selval_1val);//RATA on -selvall, blocked by -prevval on selval_prevs, blocked by p1 on selval_0andnot1
				qrat->QRATA(selval_1val, -selvall);
			}
			else {
				Clause selval_0;// sets selval FALSE if current parent0 missing pivot
				selval_0.addnode(-selvall);
				selval_0.addnode(p0);
				read.def_selval->addnode(selval_0);//RATA on -selvall, blocked by p0;
				qrat->QRATA(selval_0, -selvall);
				Clause selval_1;// sets selval FALSE if current parent1 contains pivot
				selval_1.addnode(-selvall);
				selval_1.addnode(-p1);
				read.def_selval->addnode(selval_1);//RATA on -selvall, blocked by p1;
				qrat->QRATA(selval_1, -selvall);
			}

			read.def_selon->addnode(selon_long);//RATA on -selonl: blocked on each short clause
			qrat->QRATA(selon_long, -selonl);

			//taut
			//Lit tautl = Lit(read.tautological);
			//Lit taut_parent0 = Lit(I->Idx_Proof->operator[](level).operator[](parent0).tautological);
			//Lit taut_parent1 = Lit(I->Idx_Proof->operator[](level).operator[](parent1).tautological);

			//Clause taut_forwardoff0;
			//taut_forwardoff0.addnode(selonl);
			//taut_forwardoff0.addnode(-taut_parent0);
			//taut_forwardoff0.addnode(tautl);
			//read.def_tautological->addnode(taut_forwardoff0);//RATA on tautl: trivial
			//qrat->QRATA(taut_forwardoff0, tautl);

			//Clause taut_forwardoff1;
			//taut_forwardoff1.addnode(selonl);
			//taut_forwardoff1.addnode(-taut_parent1);
			//taut_forwardoff1.addnode(tautl);
			//read.def_tautological->addnode(taut_forwardoff1);//RATA on tautl: trivial
			//qrat->QRATA(taut_forwardoff1, tautl);

			//Clause taut_forwardon0;
			//taut_forwardon0.addnode(-selonl);
			//taut_forwardon0.addnode(selvall);
			//taut_forwardon0.addnode(-taut_parent0);
			//taut_forwardon0.addnode(tautl);
			///read.def_tautological->addnode(taut_forwardon0);//RATA on tautl: trivial
			//qrat->QRATA(taut_forwardon0, tautl);

			//Clause taut_forwardon1;
			//taut_forwardon1.addnode(-selonl);
			//taut_forwardon1.addnode(-selvall);
			//taut_forwardon1.addnode(-taut_parent1);
			//taut_forwardon1.addnode(tautl);
			//read.def_tautological->addnode(taut_forwardon1);//RATA on tautl: trivial
			//qrat->QRATA(taut_forwardon1, tautl);

			//Clause taut_backwardoff;
			//taut_backwardoff.addnode(selonl);
			//taut_backwardoff.addnode(taut_parent0);
			//taut_backwardoff.addnode(taut_parent1);
			//taut_backwardoff.addnode(-tautl);
			//read.def_tautological->addnode(taut_backwardoff);//RATA on -tautl: 0 blocked on -taut_parent0, 1 blocked on -taut_parent1
			//qrat->QRATA(taut_backwardoff, -tautl);

			//Clause taut_backwardon0;
			//taut_backwardon0.addnode(-selonl);
			//taut_backwardon0.addnode(selvall);
			//taut_backwardon0.addnode(taut_parent0);
			//taut_backwardon0.addnode(-tautl);
			//read.def_tautological->addnode(taut_backwardon0); //RATE on -taul: 0 blocked on -taut_parent0, off1 blocked by selonl, on1 blocked by selvall
			//qrat->QRATA(taut_backwardon0, -tautl);

			//Clause taut_backwardon1;
			//taut_backwardon1.addnode(-selonl);
			//taut_backwardon1.addnode(-selvall);
			//taut_backwardon1.addnode(taut_parent1);
			//taut_backwardon1.addnode(-tautl);
			//read.def_tautological->addnode(taut_backwardon1); //RATA on -tautl: 1 blocked on -taut_parent1, off0 blocked by selonl, on0 blocked by selvall
			//qrat->QRATA(taut_backwardon1, -tautl);
			//members
			Clause P0 = pi->operator[](parent0).clause;
			Clause P1 = pi->operator[](parent1).clause;
			Link1<Lit>* current = L.clause.head;
			int lit_counter = 0;
			while (current != NULL) {
				Lit l = current->data;
				int pos0 = find_a_position(l, P0);
				int pos1 = find_a_position(l, P1);
				Lit meml = Lit(read.memberships->operator[](lit_counter).membership);
				if ((pos0 == -1) && (pos1 != -1)) {
					Lit l1 = Lit(SE->main_index->operator[](level).operator[](parent1).memberships->operator[](pos1).membership);
					Clause mem_val;
					mem_val.addnode(-selvall);
					mem_val.addnode(-l1);
					mem_val.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_val);//RATA on meml, trivial;
					qrat->QRATA(mem_val, meml);
					Clause mem_on;
					mem_on.addnode(selonl);
					mem_on.addnode(-l1);
					mem_on.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_on);//RATA on meml, trivial;
					qrat->QRATA(mem_on, meml);
					Clause mem_parent;
					mem_parent.addnode(l1);
					mem_parent.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_parent);//RATA on -meml, blocked by -l1 in both clauses
					qrat->QRATA(mem_parent, -meml);
					Clause mem_sel;
					mem_sel.addnode(-selonl);
					mem_sel.addnode(selvall);
					mem_sel.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_sel);//RATA on -meml, blocked by selonl on mem_on and -selvall in mem_val
					qrat->QRATA(mem_sel, -meml);
					//add equivalence for parent1
				}
				if ((pos0 != -1) && (pos1 == -1)) {
					Lit l0 = Lit(SE->main_index->operator[](level).operator[](parent0).memberships->operator[](pos0).membership);
					//add equivalence for parent0
					Clause mem_val;
					mem_val.addnode(selvall);
					mem_val.addnode(-l0);
					mem_val.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_val);//RATA on meml, trivial;
					qrat->QRATA(mem_val, meml);
					Clause mem_on;
					mem_on.addnode(selonl);
					mem_on.addnode(-l0);
					mem_on.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_on);//RATA on meml, trivial;
					qrat->QRATA(mem_on, meml);
					Clause mem_parent;
					mem_parent.addnode(l0);
					mem_parent.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_parent);//RATA on -meml, blocked by -l0 in both clauses
					qrat->QRATA(mem_parent, -meml);
					Clause mem_sel;
					mem_sel.addnode(-selonl);
					mem_sel.addnode(-selvall);
					mem_sel.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_sel);//RATA on -meml, blocked by selonl on mem_on and -selvall in mem_val
					qrat->QRATA(mem_sel, -meml);
					//add equivalence for parent1

				}
				if ((pos0 != -1) && (pos1 != -1)) {
					Lit l0 = Lit(SE->main_index->operator[](level).operator[](parent0).memberships->operator[](pos0).membership);
					Lit l1 = Lit(SE->main_index->operator[](level).operator[](parent1).memberships->operator[](pos1).membership);
					//disjunctive reasoning except for selon
					Clause mem_val0;
					mem_val0.addnode(selvall);
					mem_val0.addnode(-l0);
					mem_val0.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_val0);//RATA on meml, trivial;
					qrat->QRATA(mem_val0, meml);
					Clause mem_val1;
					mem_val1.addnode(-selvall);
					mem_val1.addnode(-l0);
					mem_val1.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_val1);//RATA on meml, trivial;
					qrat->QRATA(mem_val1, meml);

					Clause mem_off0;
					mem_off0.addnode(selonl);
					mem_off0.addnode(-l0);
					mem_off0.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_off0);//RATA on meml, trivial;
					qrat->QRATA(mem_off0, meml);

					Clause mem_off1;
					mem_off1.addnode(selonl);
					mem_off1.addnode(-l1);
					mem_off1.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_off1);//RATA on meml, trivial;
					qrat->QRATA(mem_off1, meml);

					Clause mem_parent;
					mem_parent.addnode(l0);
					mem_parent.addnode(l1);
					mem_parent.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_parent);//RATA on -meml, blocked by -l1 in 1 clause,, blocked by -l0 in 0 clauses
					qrat->QRATA(mem_parent, -meml);

					Clause mem_on0;
					mem_on0.addnode(-selonl);
					mem_on0.addnode(-selvall);
					mem_on0.addnode(l0);
					mem_on0.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_on0);//RATA on -meml, blocked by selon in off, by selval in val1, by -l0 in val0
					qrat->QRATA(mem_on0, -meml);
					Clause mem_on1;
					mem_on1.addnode(-selonl);
					mem_on1.addnode(selvall);
					mem_on1.addnode(l1);
					mem_on1.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_on1);//RATA on -meml, blocked by selon in off, by selval in val0, by -l1 in val1
					qrat->QRATA(mem_on1, -meml);
				}
				lit_counter++;
				current = current->next;
			}

			//check if present in parent0 and find index
			//check if present in parent1 and find index




		}
		if (L.rule == REDUCTION) {
			int parent = L.parent0;
			Clause P = pi->operator[](parent).clause;
			//taut
			//Lit tautl = Lit(read.tautological);
			//Lit taut_parent = Lit(I->Idx_Proof->operator[](level).operator[](parent).tautological);

			//Clause taut_forward;
			//taut_forward.addnode(-taut_parent);
			//taut_forward.addnode(tautl);
			//read.def_tautological->addnode(taut_forward);//RATA on tautl: trivial
			//qrat->QRATA(taut_forward, tautl);

			//Clause taut_backward;
			//taut_backward.addnode(taut_parent);
			//taut_backward.addnode(-tautl);
			//read.def_tautological->addnode(taut_backward);//RATA on -tautl: -taut_parent blocked;
			//qrat->QRATA(taut_backward, -tautl);

			Link1<Lit>* current = L.clause.head;
			int lit_counter = 0;
			while (current != NULL) {
				Lit l = current->data;
				int pos = find_a_position(l, P);
				Lit meml = Lit(read.memberships->operator[](lit_counter).membership);
				Lit parl = Lit(SE->main_index->operator[](level).operator[](parent).memberships->operator[](pos).membership);
				Clause mem_forward;
				mem_forward.addnode(-parl);
				mem_forward.addnode(meml);
				read.memberships->operator[](lit_counter).def_membership->addnode(mem_forward);//RATA on meml: trivial
				qrat->QRATA(mem_forward, meml);
				Clause mem_backward;
				mem_backward.addnode(parl);
				mem_backward.addnode(-meml);
				read.memberships->operator[](lit_counter).def_membership->addnode(mem_backward);//RATA on meml: -parl blocked
				qrat->QRATA(mem_backward, meml);
				current = current->next;
				lit_counter++;
			}
		}
		//

		return;
	}


	void backdef_cell(Strategy_Extractor* SE, IndexLine cell , int level, int line_no1) {
		ClausalProof* pi = SE->input_proof;
		Prefix P = SE->input_QBF->prefix;
		int line_no2 = pi->tail->position;
		Lit al = Lit(cell.ancestor);
		Line L1 = pi->operator[](line_no1);
		QRAT_Proof* qrat = SE->output_QRAT;
		if (line_no1 == line_no2) {
			Clause a_assert;
			a_assert.addnode(al);
			cell.def_ancestor->addnode(a_assert);//RATA on al: trivial
			qrat->QRATA(a_assert, al);
		}
		else {

			Clause a_long;
			a_long.addnode(-al);
			for (int i = line_no1 + 1; i <= line_no2; i++) {
				Line L1child = pi->operator[](i);
				if (L1child.rule == REDUCTION) {
					if (L1child.parent0 == line_no1) {
						Lit a_child = Lit(SE->main_index->operator[](level).operator[](i).ancestor);
						a_long.addnode(a_child);
						Clause a_short = Clause();
						a_short.addnode(-a_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
				}
				if (L1child.rule == RESOLUTION) {
					//output->output_cnf->add_comment("ancestor resolution");
					if (L1child.parent0 == line_no1) {
						Lit cond_child = Lit(SE->main_index->operator[](level).operator[](i).xselval0);
						a_long.addnode(cond_child);
						Clause a_short = Clause();
						a_short.addnode(-cond_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
					if (L1child.parent1 == line_no1) {
						Lit cond_child = Lit(SE->main_index->operator[](level).operator[](i).xselval1);
						a_long.addnode(cond_child);
						Clause a_short = Clause();
						a_short.addnode(-cond_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
				}
			}
			cell.def_ancestor->addnode(a_long);//RATA on -al: blocked on each cond
			qrat->QRATA(a_long, -al);


		}
		if (L1.rule == RESOLUTION) {
			Lit ext0l = Lit(cell.xselval0);
			Lit ext1l = Lit(cell.xselval1);
			Lit selonl = Lit(SE->main_index->operator[](level).operator[](line_no1).selon);
			Lit selvall = Lit(SE->main_index->operator[](level).operator[](line_no1).selval);


			Clause extOFF0;
			extOFF0.addnode(selonl);
			extOFF0.addnode(-al);
			extOFF0.addnode(ext0l);
			cell.def_xselval0->addnode(extOFF0);//RATA on ext0l: trivial
			qrat->QRATA(extOFF0, ext0l);

			Clause extval0;
			extval0.addnode(selvall);
			extval0.addnode(-al);
			extval0.addnode(ext0l);
			cell.def_xselval0->addnode(extval0);//RATA on ext0l: trivial
			qrat->QRATA(extval0, ext0l);

			Clause extanc0;
			extanc0.addnode(al);
			extanc0.addnode(-ext0l);
			cell.def_xselval0->addnode(extanc0);//RATA on -ext0l: blocked on -al
			qrat->QRATA(extanc0, -ext0l);

			Clause extsel0;
			extsel0.addnode(-selonl);
			extsel0.addnode(-selvall);
			extsel0.addnode(-ext0l);
			cell.def_xselval0->addnode(extsel0);//RATA on -ext0l: blocked on selonl, blocked on selvall
			qrat->QRATA(extsel0, -ext0l);

			Clause extOFF1;
			extOFF1.addnode(selonl);
			extOFF1.addnode(-al);
			extOFF1.addnode(ext1l);
			cell.def_xselval1->addnode(extOFF1);//RATA on ext1l: trivial
			qrat->QRATA(extOFF1, ext1l);

			Clause extval1;
			extval1.addnode(-selvall);
			extval1.addnode(-al);
			extval1.addnode(ext1l);
			cell.def_xselval1->addnode(extval1);//RATA on ext1l: trivial
			qrat->QRATA(extval1, ext1l);

			Clause extanc1;
			extanc1.addnode(al);
			extanc1.addnode(-ext1l);
			cell.def_xselval1->addnode(extanc1);//RATA on -ext1l: blocked on al
			qrat->QRATA(extanc1, -ext1l);

			Clause extsel1;
			extsel1.addnode(-selonl);
			extsel1.addnode(selvall);
			extsel1.addnode(-ext1l);
			cell.def_xselval1->addnode(extsel1);//RATA on -ext1l: blocked on selonl, blocked on -selvall
			qrat->QRATA(extsel1, -ext1l);
		}

	}

	void def_layer(Strategy_Extractor* SE, LinkL<LinkL<IndexLine> >* idx_proof, Prefix P, ClausalProof* pi, int level) {
		LinkL<IndexLine> read = SE->main_index->operator[](level);
		Link1<IndexLine>* current = read.head;
		int botpos = pi->tail->position;
		int line_no = 0;
		while (current != NULL) {//cycles through all lines
			def_line(SE, current->data, level, line_no);
			current = current->next;
			line_no++;
		}
		current = read.tail;
		line_no = botpos;
		while (current != NULL) {//cycles through all lines
			backdef_cell(SE, current->data, level, line_no);
			current = current->prev;
			line_no--;
		}
		//idx_proof->addnode(*temp);
		return;
	};

	void MemberCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no, int position);

	void SelonCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no) {
		IndexLine lineidx = SE->main_index->operator[](level).operator[](line_no);
		ClausalProof* pi = SE->input_proof;
		Line L = pi->operator[](line_no);
		if (lineidx.is_selon_defined == 0) {
			lineidx.is_selon_defined = 1;
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no);
			layer2->data.is_selon_defined = 1;
			MemberCnfLoad(output, SE, level, L.parent0, L.litpos0);
			MemberCnfLoad(output, SE, level, L.parent1, L.litpos1);
			if (level > 0) {
				SelonCnfLoad(output, SE, level - 1, line_no);

			}
			copyinto(output, lineidx.def_selon);
		}
	}
	void SelvalCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no) {
		IndexLine lineidx = SE->main_index->operator[](level).operator[](line_no);
		ClausalProof* pi = SE->input_proof;
		Line L = pi->operator[](line_no);
		if (lineidx.is_selval_defined == 0) {
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no);
			layer2->data.is_selval_defined = 1;
			MemberCnfLoad(output, SE, level, L.parent0, L.litpos0);
			MemberCnfLoad(output, SE, level, L.parent1, L.litpos1);
			if (level > 0) {
				SelonCnfLoad(output, SE, level - 1, line_no);
				SelvalCnfLoad(output, SE, level - 1, line_no);

			}
			copyinto(output, lineidx.def_selval);
		}
	}

	void MemberCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no, int position) {
		ClausalProof* pi = SE->input_proof;
		Prefix P = SE->input_QBF->prefix;
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		Lit l = C.operator[](position);
		IndexLine lineidx = SE->main_index->operator[](level).operator[](line_no);
		IndexLit memidx = lineidx.memberships->operator[](position);
		if (memidx.is_membership_defined == 0) {
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no);
			Link1<IndexLit>* layer3 = layer2->data.memberships->findnode(position);
			layer3->data.is_membership_defined = 1;
			if (L.rule == AXIOM) {
				//if (P.lvl(C.operator[](position).var)< level) {}
				//else {}


			}
			if (L.rule == REDUCTION) {
				Line<Clause> L0 = pi->operator[](L.parent0);
				Clause P0 = L0.clause;
				int pos0 = find_a_position(l, P0);
				MemberCnfLoad(output, SE, level, L.parent0, pos0);

			}
			if (L.rule == RESOLUTION) {
				Line<Clause> L0 = pi->operator[](L.parent0);
				Clause P0 = L0.clause;
				int pos0 = find_a_position(l, P0);
				Line<Clause> L1 = pi->operator[](L.parent1);
				Clause P1 = L1.clause;
				int pos1 = find_a_position(l, P1);
				SelonCnfLoad(output, SE, level, line_no);
				SelvalCnfLoad(output, SE, level, line_no);
				if (pos0 != -1) {
					MemberCnfLoad(output, SE, level, L.parent0, pos0);
				}
				if (pos1 != -1) {
					MemberCnfLoad(output, SE, level, L.parent1, pos1);
				}
			}
			copyinto(output, memidx.def_membership);
		}

	}

	void ConnCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no1);

	void XSelCnfLoad(bool val, Cnf* output, Strategy_Extractor* SE, int level, int line_no1) {
		IndexLine cell = SE->main_index->operator[](level).operator[](line_no1);
		ClausalProof* pi = SE->input_proof;
		Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
		Link1<IndexLine>* layer2 = layer1->data.findnode(line_no1);
		if (val) {
			if (cell.is_xselval1_defined == 0) {
				layer2->data.is_xselval1_defined = 1;
				ConnCnfLoad(output, SE, level, line_no1);
				SelonCnfLoad(output, SE, level, line_no1);
				SelvalCnfLoad(output, SE, level, line_no1);
				copyinto(output, cell.def_xselval1);

			}
		}
		else {
			if (cell.is_xselval0_defined == 0) {
				layer2->data.is_xselval0_defined = 1;
				ConnCnfLoad(output, SE, level, line_no1);
				SelonCnfLoad(output, SE, level, line_no1);
				SelvalCnfLoad(output, SE, level, line_no1);
				copyinto(output, cell.def_xselval0);
			}
		}
	}

	void ConnCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no1) {
		IndexLine cell = SE->main_index->operator[](level).operator[](line_no1);
		if (cell.is_ancestor_defined == 0) {
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no1);
			layer2->data.is_ancestor_defined = 1;
			ClausalProof* pi = SE->input_proof;
			int line_no2 = pi->tail->position;
			if (line_no1 == line_no2) {
			}
			else {
				for (int i = line_no1 + 1; i <= line_no2; i++) {
					Line L1child = pi->operator[](i);
					if (L1child.rule == REDUCTION) {
						if (L1child.parent0 == line_no1) {
							ConnCnfLoad(output, SE, level, i);
						}
					}
					if (L1child.rule == RESOLUTION) {
						if (L1child.parent0 == line_no1) {
							XSelCnfLoad(0, output, SE, level, i);
						}
						if (L1child.parent1 == line_no1) {
							XSelCnfLoad(1, output, SE, level, i);
						}
					}
				}

			}
			copyinto(output, cell.def_ancestor);
		}
	}

	void StrategyCnfLoad(Cnf* output, Strategy_Extractor* SE, Var u) {
		//StrategyCnfLoad
		Link1<IndexStrat>* current_u = SE->strategy_index->head;
		while (current_u != NULL) {
			if (current_u->data.u == u) {
				if (current_u->data.is_strategy_defined == 0) {
					current_u->data.is_strategy_defined = 1;
					Link1<int>* current_line = current_u->data.axioms->head;
					while (current_line != NULL) {
						int level = SE->input_QBF->prefix.lvl(u) - 1;
						int axpos = current_line->data;
						//int botpos = SE->input_proof->tail->position;
						ConnCnfLoad(output, SE, level, axpos);
						current_line = current_line->next;
					}

					copyinto(output, current_u->data.def_strategy);
				}
			}
			current_u = current_u->next;

		}


	}

	void def_universal(Strategy_Extractor* SE, LinkL <IndexStrat>* idx_strat,  Var u) {
		Link1<IndexStrat>* current_u = idx_strat->head;
		Prefix P = SE->input_QBF->prefix;
		ClausalProof* pi = SE->input_proof;
		QRAT_Proof* qrat = SE->output_QRAT;
		while (current_u != NULL) {
			if (current_u->data.u == u) {
				SE->output_cnf->add_comment("Strategy clauses:");
				qrat->add_comment("Strategy clauses:");
				int level = P.lvl(u) - 1;
				Link1<int>* current_line = current_u->data.axioms->head;
				Lit ul = Lit(current_u->data.strategy);
				Clause stratlong;
				stratlong.addnode(ul);
				while (current_line != NULL) {
					//define 

					int axpos = current_line->data;
					int upos = find_a_position(Lit(u), pi->operator[](axpos).clause);
					int botpos = pi->tail->position;
					Lit conn = Lit(SE->main_index->operator[](level).operator[](axpos).ancestor);
					//Lit uinA = Lit(I->Idx_Proof->operator[](level).operator[](axpos).memberships->operator[](upos).membership);
					//Lit ex = Lit(current_line->data.xmembership);
					/*
					Clause xdisjunct;
					xdisjunct.addnode(-conn);
					xdisjunct.addnode(-uinA);
					xdisjunct.addnode(-ex);
					output->output_cnf->addnode(xdisjunct);//RATA on -ex; trivial
					qrat->QRATA(xdisjunct, -ex);
					Clause xconn;
					xconn.addnode(conn);
					xconn.addnode(ex);
					output->output_cnf->addnode(xconn);//RATA on ex; blocked on -conn
					qrat->QRATA(xconn, ex);
					Clause xuinA;
					xuinA.addnode(uinA);
					xuinA.addnode(ex);
					output->output_cnf->addnode(xuinA);//RATA on ex; blocked on uinA
					qrat->QRATA(xuinA, ex);
					*/
					Clause stratshort;
					stratshort.addnode(-conn);
					stratshort.addnode(-ul);
					current_u->data.def_strategy->addnode(stratshort);//RATA on -ul; trivial
					qrat->QRATA(stratshort, -ul);
					stratlong.addnode(conn);

					current_line = current_line->next;
				}
				current_u->data.def_strategy->addnode(stratlong);//RATA on ul; each blocked on ex;
				qrat->QRATA(stratlong, ul, "Long Strategy Clause");
				//clauses not destined for qrat, only for propositional checks
				//output->output_cnf->add_comment("equivalence clauses for universal");
				Clause uforward;
				uforward.addnode(-ul);
				uforward.addnode(Lit(u));
				SE->output_cnf->addnode(uforward);//not acceptable in QRAT
				Clause ubackward;
				ubackward.addnode(ul);
				ubackward.addnode(-Lit(u));
				SE->output_cnf->addnode(ubackward);//not acceptable in QRAT

				StrategyCnfLoad(SE->output_cnf, SE, u);

			}
			current_u = current_u->next;
		}

	}

	Strategy_Extractor* Extract(QCNF* phi, ClausalProof* pi) {
		Strategy_Extractor* output = new Strategy_Extractor(phi, pi);
		*(output->output_cnf) = copy(phi->matrix);
		output->main_index = new LinkL<LinkL<IndexLine>>;
		output->strategy_index = new LinkL<IndexStrat>;
		int max_var = output->base_max_var;
		Link1<Quantifier>* currentQ = phi->prefix.head;
		//zeroeth level
		//create a layer (<LinkL<Index1>) for Idx_Proof
			//create lines (<Index1>) for the layer
				//create idx 1_1 for the lines
				//add each idx 1_1 addnode()
			//add each line
		//add each layer
		int layer_level = 0;
		max_var = add_layer(max_var, output->main_index, output->long_prefix, pi);
		def_layer(output, output->main_index, output->input_QBF->prefix, pi, layer_level);
		//add_layer1 but for definition clauses
		//max_var = add_array2(max_var, output->main_index->Idx_Conn, output->main_index->idx_prefix, pi);
		//def_array2(output->main_index, output, output->main_index->Idx_Conn, phi->prefix, pi, layer_level);

		//add_array2 but for definition clauses
		while (currentQ != NULL) {
			if (currentQ->data.is_universal) {// add strategy
				max_var = add_universal(max_var, output->strategy_index, output->long_prefix, pi, currentQ->data.var);
				def_universal (output, output->strategy_index, currentQ->data.var);
				//while loop for 

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
				def_layer(output, output->main_index, output->input_QBF->prefix, pi, layer_level);
			}
			currentQ = currentQ->next;
		}
		output->idx_max_var = max_var;
		return output;
	}



}