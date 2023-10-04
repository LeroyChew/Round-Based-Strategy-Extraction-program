#pragma once
#include "Index.h"
#include "QRAT.h"

namespace idx {

	struct Strategy_Extractor {
		QCNF* QBF;
		ClausalProof* input_proof;
		Cnf* output_cnf;
		QRAT_Proof* output_QRAT;
		LinkL<AbsClause>* Abs_Strat_Prop;
		idx::Index* main_index;
		Strategy_Extractor() {
			QBF = new QCNF;
			input_proof = new ClausalProof;
			output_cnf = new Cnf;
			output_QRAT = new QRAT_Proof();
			Abs_Strat_Prop = new LinkL<AbsClause>;
			main_index = new idx::Index;
		}
		Strategy_Extractor(QCNF* phi, ClausalProof* pi) {
			QBF = new QCNF();
			QBF->matrix = copy(phi->matrix);
			QBF->prefix = copy(phi->prefix);
			input_proof = pi;
			output_cnf = new Cnf;
			output_QRAT = new QRAT_Proof();
			output_QRAT->Phi = *QBF;
		}

		void print(FILE* file) {
			
		}
	};



	void MemberCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no, int position);

	void SelonCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no) {
		Index1 lineidx = SE->main_index->Idx_Proof->operator[](level).operator[](line_no);
		ClausalProof* pi = SE->input_proof;
		Line L = pi->operator[](line_no);
		if(lineidx.is_selon_defined == 0) {
			lineidx.is_selon_defined = 1;
			Link1<LinkL<Index1>>* layer1 = SE->main_index->Idx_Proof->findnode(level);
			Link1<Index1>* layer2 = layer1->data.findnode(line_no);
			layer2->data.is_selon_defined = 1;
			MemberCnfLoad(output,  SE, level, L.parent0, L.litpos0);
			MemberCnfLoad(output, SE, level, L.parent1, L.litpos1);
			if (level > 0) {
				SelonCnfLoad(output, SE, level - 1, line_no);
				
			}
			copyinto(output, lineidx.def_selon);
		}
	}
	void SelvalCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no) {
		Index1 lineidx = SE->main_index->Idx_Proof->operator[](level).operator[](line_no);
		ClausalProof* pi = SE->input_proof;
		Line L = pi->operator[](line_no);
		if (lineidx.is_selval_defined == 0) {
			Link1<LinkL<Index1>>* layer1 = SE->main_index->Idx_Proof->findnode(level);
			Link1<Index1>* layer2 = layer1->data.findnode(line_no);
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
		Prefix P = SE->QBF->prefix;
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		Lit l = C.operator[](position);
		Index1 lineidx = SE->main_index->Idx_Proof->operator[](level).operator[](line_no);
		Index1_1 memidx = lineidx.memberships->operator[](position);
		if (memidx.is_membership_defined == 0){
			Link1<LinkL<Index1>>* layer1 =SE->main_index->Idx_Proof->findnode(level);
			Link1<Index1>* layer2 = layer1->data.findnode(line_no);
			Link1<Index1_1>* layer3 = layer2->data.memberships->findnode(position);
			layer3->data.is_membership_defined =1;
			if (L.rule == AXIOM) {
				//if (P.lvl(C.operator[](position).var)< level) {}
				//else {}

				
			}
			if (L.rule == REDUCTION) {
				Line<Clause> L0 = pi->operator[](L.parent0);
				Clause P0=L0.clause;
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

	void def_line1(Index* I, Strategy_Extractor* output, Index1 read, Prefix P, ClausalProof* pi, int level, int line_no) {// add an entry on memberships, taut and sel
		//Index1* temp = new Index1();
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		QRAT_Proof* qrat = output->output_QRAT;
		int position = 0;
		if (L.rule == AXIOM) {
			Clause taut_long;
			Lit taut = Lit(read.tautological);//tautological implies clause less than level
			taut_long.addnode(-taut); 
			if (C.length > 0) {

				Link1<Lit>* current = C.head;
				while (current != NULL) {
					//def_literal1(max_var, temp, P, C, position);
					Lit l= current->data;
					Lit ml = Lit(read.memberships->operator[](position).membership);
					if (P.lvl(l.var) <= level) {
						Clause taut_short;// any satisfied literal implies tautological
						taut_short.addnode(-l);
						taut_short.addnode(taut);
						read.def_tautological->addnode(taut_short);//RATA on taut: trivial
						qrat->QRATA(taut_short, taut);
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
						taut_long.addnode(l);
						
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
			read.def_tautological->addnode(taut_long);//RATA on -taut: l, -l blocked on each taut_short
			qrat->QRATA(taut_long, -taut);
		}
		if (L.rule == RESOLUTION) {


			int parent0 = L.parent0;
			int litpos0 = L.litpos0;
			int parent1 = L.parent1;
			int litpos1 = L.litpos1;
			Lit p0 = Lit(I->Idx_Proof->operator[](level).operator[](parent0).memberships->operator[](litpos0).membership, 1);
			Lit p1 = Lit(I->Idx_Proof->operator[](level).operator[](parent1).memberships->operator[](litpos1).membership, 1);
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
				Lit prevon = Lit(I->Idx_Proof->operator[](level-1).operator[](line_no).selon, 1);
				Lit prevval = Lit(I->Idx_Proof->operator[](level-1).operator[](line_no).selval, 1);
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
			Lit tautl = Lit(read.tautological);
			Lit taut_parent0 = Lit(I->Idx_Proof->operator[](level).operator[](parent0).tautological);
			Lit taut_parent1 = Lit(I->Idx_Proof->operator[](level).operator[](parent1).tautological);

			Clause taut_forwardoff0;
			taut_forwardoff0.addnode(selonl);
			taut_forwardoff0.addnode(-taut_parent0);
			taut_forwardoff0.addnode(tautl);
			read.def_tautological->addnode(taut_forwardoff0);//RATA on tautl: trivial
			qrat->QRATA(taut_forwardoff0, tautl);

			Clause taut_forwardoff1;
			taut_forwardoff1.addnode(selonl);
			taut_forwardoff1.addnode(-taut_parent1);
			taut_forwardoff1.addnode(tautl);
			read.def_tautological->addnode(taut_forwardoff1);//RATA on tautl: trivial
			qrat->QRATA(taut_forwardoff1, tautl);

			Clause taut_forwardon0;
			taut_forwardon0.addnode(-selonl);
			taut_forwardon0.addnode(selvall);
			taut_forwardon0.addnode(-taut_parent0);
			taut_forwardon0.addnode(tautl);
			read.def_tautological->addnode(taut_forwardon0);//RATA on tautl: trivial
			qrat->QRATA(taut_forwardon0, tautl);

			Clause taut_forwardon1;
			taut_forwardon1.addnode(-selonl);
			taut_forwardon1.addnode(-selvall);
			taut_forwardon1.addnode(-taut_parent1);
			taut_forwardon1.addnode(tautl);
			read.def_tautological->addnode(taut_forwardon1);//RATA on tautl: trivial
			qrat->QRATA(taut_forwardon1, tautl);

			Clause taut_backwardoff;
			taut_backwardoff.addnode(selonl);
			taut_backwardoff.addnode(taut_parent0);
			taut_backwardoff.addnode(taut_parent1);
			taut_backwardoff.addnode(-tautl);
			read.def_tautological->addnode(taut_backwardoff);//RATA on -tautl: 0 blocked on -taut_parent0, 1 blocked on -taut_parent1
			qrat->QRATA(taut_backwardoff, -tautl);

			Clause taut_backwardon0;
			taut_backwardon0.addnode(-selonl);
			taut_backwardon0.addnode(selvall);
			taut_backwardon0.addnode(taut_parent0);
			taut_backwardon0.addnode(-tautl);
			read.def_tautological->addnode(taut_backwardon0); //RATE on -taul: 0 blocked on -taut_parent0, off1 blocked by selonl, on1 blocked by selvall
			qrat->QRATA(taut_backwardon0, -tautl);

			Clause taut_backwardon1;
			taut_backwardon1.addnode(-selonl);
			taut_backwardon1.addnode(-selvall);
			taut_backwardon1.addnode(taut_parent1);
			taut_backwardon1.addnode(-tautl);
			read.def_tautological->addnode(taut_backwardon1); //RATA on -tautl: 1 blocked on -taut_parent1, off0 blocked by selonl, on0 blocked by selvall
			qrat->QRATA(taut_backwardon1, -tautl);
			//members
			Clause P0 = pi->operator[](parent0).clause;
			Clause P1 = pi->operator[](parent1).clause;
			Link1<Lit>* current = L.clause.head;
			int lit_counter = 0;
			while(current != NULL) {
				Lit l = current->data;
				int pos0 = find_a_position(l, P0);
				int pos1 = find_a_position(l, P1);
				Lit meml = Lit(read.memberships->operator[](lit_counter).membership);
				if ((pos0 == -1) && (pos1 != -1)) {
					Lit l1= Lit(I->Idx_Proof->operator[](level).operator[](parent1).memberships->operator[](pos1).membership);
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
					Lit l0 = Lit(I->Idx_Proof->operator[](level).operator[](parent0).memberships->operator[](pos0).membership);
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
					qrat->QRATA(mem_on,meml);
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
					Lit l0 = Lit(I->Idx_Proof->operator[](level).operator[](parent0).memberships->operator[](pos0).membership);
					Lit l1 = Lit(I->Idx_Proof->operator[](level).operator[](parent1).memberships->operator[](pos1).membership);
					//disjunctive reasoning except for selon
					Clause mem_val0;
					mem_val0.addnode(selvall);
					mem_val0.addnode(-l0);
					mem_val0.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_val0);//RATA on meml, trivial;
					qrat->QRATA(mem_val0, meml);
					Clause mem_val1;
					mem_val1.addnode(-selvall);
					mem_val1.addnode(-l1);
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
					mem_on0.addnode(selvall);
					mem_on0.addnode(l0);
					mem_on0.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_on0);//RATA on -meml, blocked by selon in off, by selval in val1, by -l0 in val0
					qrat->QRATA(mem_on0, -meml);
					Clause mem_on1;
					mem_on1.addnode(-selonl);
					mem_on1.addnode(-selvall);
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
			Lit tautl = Lit(read.tautological);
			Lit taut_parent = Lit(I->Idx_Proof->operator[](level).operator[](parent).tautological);

			Clause taut_forward;
			taut_forward.addnode(-taut_parent);
			taut_forward.addnode(tautl);
			read.def_tautological->addnode(taut_forward);//RATA on tautl: trivial
			qrat->QRATA(taut_forward, tautl);

			Clause taut_backward;
			taut_backward.addnode(taut_parent);
			taut_backward.addnode(-tautl);
			read.def_tautological->addnode(taut_backward);//RATA on -tautl: -taut_parent blocked;
			qrat->QRATA(taut_backward, -tautl);

			Link1<Lit>* current = L.clause.head;
			int lit_counter = 0;
			while (current != NULL) {
				Lit l = current->data;
				int pos = find_a_position(l, P);
				Lit meml = Lit(read.memberships->operator[](lit_counter).membership);
				Lit parl = Lit(I->Idx_Proof->operator[](level).operator[](parent).memberships->operator[](pos).membership);
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

	void def_layer1(Index* I, Strategy_Extractor* output, LinkL<LinkL<Index1> >* idx_proof, Prefix P, ClausalProof* pi, int level) {
		LinkL<Index1> read = I->Idx_Proof->operator[](level);
		Link1<Index1>* current = read.head;
		int line_no = 0;
		while (current != NULL) {//cycles through all lines
			def_line1(I, output, current->data, P, pi, level, line_no);
			current = current->next;
			line_no++;
		}
		//idx_proof->addnode(*temp);
		return;
	};

	void def_cell2(Index* I, Strategy_Extractor* output, Index2 cell,Prefix P, ClausalProof* pi, int level, int line_no1, int line_no2) {
		Lit dl = Lit(cell.descendant);
		QRAT_Proof* qrat = output->output_QRAT;
		if (line_no1 > line_no2) {
			Clause d_assert;
			d_assert.addnode(-dl);
			cell.def_descendant->addnode(d_assert);//RATA on -dl: trivial
			qrat->QRATA(d_assert, dl);
		}
		else {
			if (line_no1 == line_no2) {
				Clause d_assert;
				d_assert.addnode(dl);
				cell.def_descendant->addnode(d_assert);//RATA on dl: trivial
				qrat->QRATA(d_assert, dl);
			}
			else {
				Line L2 = pi->operator[](line_no2);
				if (L2.rule == AXIOM) {
					Clause d_negassert;
					d_negassert.addnode(-dl);//RATA on dl: trivial
					cell.def_descendant->addnode(d_negassert);//RATA on -dl: trivial
					qrat->QRATA(d_negassert, -dl);
				}
				if (L2.rule == REDUCTION) {
					int parent = L2.parent0;
					Lit d_parent;
					if (parent >= line_no1) {
						d_parent = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent).descendant);
						Clause dforward;
						dforward.addnode(-d_parent);
						dforward.addnode(dl);
						cell.def_descendant->addnode(dforward);//RATA on dl: trivial
						qrat->QRATA(dforward, dl);
						Clause dbackward;
						dbackward.addnode(d_parent);
						dbackward.addnode(-dl);
						cell.def_descendant->addnode(dbackward);//RATA on -dl: blocked by -d_parent
						qrat->QRATA(dbackward, -dl);
					}
					else {
						Clause dbackward;
						dbackward.addnode(-dl);//RATA on -dl:
					}

				}
				if (L2.rule == RESOLUTION) {
					int parent0 = L2.parent0;
					int parent1 = L2.parent1;
					Lit d_parent0;
					Lit d_parent1;
					Lit selonl = Lit(I->Idx_Proof->operator[](level).operator[](line_no2).selon);
					Lit selvall = Lit(I->Idx_Proof->operator[](level).operator[](line_no2).selval);

					d_parent0 = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent0).descendant);
					d_parent1 = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent1).descendant);
					Clause dOFF0;
					dOFF0.addnode(selonl);
					dOFF0.addnode(-d_parent0);
					dOFF0.addnode(dl);
					cell.def_descendant->addnode(dOFF0);//RATA on dl: trivial
					qrat->QRATA(dOFF0, dl);
					Clause dval0;
					dval0.addnode(selvall);
					dval0.addnode(-d_parent0);
					dval0.addnode(dl);
					cell.def_descendant->addnode(dval0);//RATA on dl: trivial
					qrat->QRATA(dval0, dl);
					Clause dOFF1;
					dOFF1.addnode(selonl);
					dOFF1.addnode(-d_parent1);
					dOFF1.addnode(dl);
					cell.def_descendant->addnode(dOFF1);//RATA on dl: trivial
					qrat->QRATA(dOFF1, dl);
					Clause dval1;
					dval1.addnode(-selvall);
					dval1.addnode(-d_parent1);
					dval1.addnode(dl);
					cell.def_descendant->addnode(dval1);//RATA on dl: trivial
					qrat->QRATA(dval1, dl);

					Clause dsel0;
					dsel0.addnode(-selonl);
					dsel0.addnode(selvall);
					dsel0.addnode(d_parent0);
					dsel0.addnode(-dl);
					cell.def_descendant->addnode(dsel0);//RATA on -dl: blocked by -d_parent0 on val0 and OFF0, blocked by selonl for doff1, by selvall for dval1,
					qrat->QRATA(dsel0, -dl);

					Clause dsel1;
					dsel1.addnode(-selonl);
					dsel1.addnode(-selvall);
					dsel1.addnode(d_parent1);
					dsel1.addnode(-dl);
					cell.def_descendant->addnode(dsel1);//RATA on -dl: blocked by -d_parent1 on val1 and OFF1, blocked by selonl for doff0, by -selvall for dval0,
					qrat->QRATA(dsel1, -dl);

					Clause dpar;
					dpar.addnode(d_parent0);
					dpar.addnode(d_parent1);
					dpar.addnode(-dl);
					cell.def_descendant->addnode(dpar);//RATA on -dl: blocked by -dparent0 on 0, and -d_parent1 on 1
					qrat->QRATA(dpar, -dl);


		
					/*if (parent0 < line_no1) {// unnecessary cases
						if (parent1 < line_no1) {
							Clause d_negassert;
							d_negassert.addnode(-dl);//RATA on dl: trivial
							cell.def_descendant->addnode(d_negassert);//RATA on dl: trivial
							qrat->QRATA(d_negassert, dl);
						}
						else {
							d_parent1 = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent1).descendant);
							Clause dOFF;
							dOFF.addnode(selonl);
							dOFF.addnode(-d_parent1);
							dOFF.addnode(dl);
							cell.def_descendant->addnode(dOFF);//RATA on dl: trivial
							qrat->QRATA(dOFF, dl);
							Clause dval;
							dval.addnode(-selvall);
							dval.addnode(-d_parent1);
							dval.addnode(dl);
							cell.def_descendant->addnode(dval);//RATA on dl: trivial
							qrat->QRATA(dval, dl);
							Clause dsel;
							dsel.addnode(selvall);
							dsel.addnode(-selonl);
							dsel.addnode(-dl);
							cell.def_descendant->addnode(dsel);//RATA on -dl: blocked by selonl for doff, by -selvall for dval
							qrat->QRATA(dsel, -dl);
							Clause dpar;
							dpar.addnode(d_parent1);
							dpar.addnode(-dl);
							cell.def_descendant->addnode(dpar);//RATA on -dl: blocked by -dparent1
							qrat->QRATA(dpar, -dl);
						}
					}
					else {
						if (parent1 < line_no1) {
							d_parent0 = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent0).descendant);
							Clause dOFF;
							dOFF.addnode(selonl);
							dOFF.addnode(-d_parent0);
							dOFF.addnode(dl);
							cell.def_descendant->addnode(dOFF);//RATA on dl: trivial
							qrat->QRATA(dOFF, dl);
							Clause dval;
							dval.addnode(selvall);
							dval.addnode(-d_parent0);
							dval.addnode(dl);
							cell.def_descendant->addnode(dval);//RATA on dl: trivial
							qrat->QRATA(dval, dl);
							Clause dsel;
							dsel.addnode(-selvall);
							dsel.addnode(-selonl);
							dsel.addnode(-dl);
							cell.def_descendant->addnode(dsel);//RATA on -dl: blocked by selonl for doff, by selvall for dval
							qrat->QRATA(dsel, -dl);
							Clause dpar;
							dpar.addnode(d_parent0);
							dpar.addnode(-dl);
							cell.def_descendant->addnode(dpar);//RATA on -dl: blocked by -dparent0
							qrat->QRATA(dpar, -dl);
						}
						else {
							d_parent0 = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent0).descendant);
							d_parent1 = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent1).descendant);
							Clause dOFF0;
							dOFF0.addnode(selonl);
							dOFF0.addnode(-d_parent0);
							dOFF0.addnode(dl);
							cell.def_descendant->addnode(dOFF0);//RATA on dl: trivial
							qrat->QRATA(dOFF0, dl);
							Clause dval0;
							dval0.addnode(selvall);
							dval0.addnode(-d_parent0);
							dval0.addnode(dl);
							cell.def_descendant->addnode(dval0);//RATA on dl: trivial
							qrat->QRATA(dval0, dl);
							Clause dOFF1;
							dOFF1.addnode(selonl);
							dOFF1.addnode(-d_parent1);
							dOFF1.addnode(dl);
							cell.def_descendant->addnode(dOFF1);//RATA on dl: trivial
							qrat->QRATA(dOFF1, dl);
							Clause dval1;
							dval1.addnode(-selvall);
							dval1.addnode(-d_parent1);
							dval1.addnode(dl);
							cell.def_descendant->addnode(dval1);//RATA on dl: trivial
							qrat->QRATA(dval1, dl);

							Clause dsel0;
							dsel0.addnode(-selonl);
							dsel0.addnode(selvall);
							dsel0.addnode(d_parent0);
							dsel0.addnode(-dl);
							cell.def_descendant->addnode(dsel0);//RATA on -dl: blocked by -d_parent0 on val0 and OFF0, blocked by selonl for doff1, by selvall for dval1,
							qrat->QRATA(dsel0, -dl);

							Clause dsel1;
							dsel1.addnode(-selonl);
							dsel1.addnode(-selvall);
							dsel1.addnode(d_parent1);
							dsel1.addnode(-dl);
							cell.def_descendant->addnode(dsel1);//RATA on -dl: blocked by -d_parent1 on val1 and OFF1, blocked by selonl for doff0, by -selvall for dval0,
							qrat->QRATA(dsel1, -dl);

							Clause dpar;
							dpar.addnode(d_parent0);
							dpar.addnode(d_parent1);
							dpar.addnode(-dl);
							cell.def_descendant->addnode(dpar);//RATA on -dl: blocked by -dparent0 on 0, and -d_parent1 on 1
							qrat->QRATA(dpar, -dl);

						}
					}

					*/
				}
			}
		}
		if (pi->operator[](line_no1).rule==RESOLUTION) {
			Lit ext0l = Lit(cell.dselval0);
			Lit ext1l = Lit(cell.dselval1);
			Lit selonl = Lit(I->Idx_Proof->operator[](level).operator[](line_no1).selon);
			Lit selvall = Lit(I->Idx_Proof->operator[](level).operator[](line_no1).selval);


			Clause extOFF0;
			extOFF0.addnode(selonl);
			extOFF0.addnode(-dl);
			extOFF0.addnode(ext0l);
			cell.def_dselval0->addnode(extOFF0);//RATA on ext0l: trivial
			qrat->QRATA(extOFF0, ext0l);

			Clause extval0;
			extval0.addnode(selvall);
			extval0.addnode(-dl);
			extval0.addnode(ext0l);
			cell.def_dselval0->addnode(extval0);//RATA on ext0l: trivial
			qrat->QRATA(extval0, ext0l);

			Clause extanc0;
			extanc0.addnode(dl);
			extanc0.addnode(-ext0l);
			cell.def_dselval0->addnode(extanc0);//RATA on -ext0l: blocked on -al
			qrat->QRATA(extanc0, -ext0l);

			Clause extsel0;
			extsel0.addnode(-selonl);
			extsel0.addnode(-selvall);
			extsel0.addnode(-ext0l);
			cell.def_dselval0->addnode(extsel0);//RATA on -ext0l: blocked on selonl, blocked on selvall
			qrat->QRATA(extsel0, -ext0l);

			Clause extOFF1;
			extOFF1.addnode(selonl);
			extOFF1.addnode(-dl);
			extOFF1.addnode(ext1l);
			cell.def_dselval1->addnode(extOFF1);//RATA on ext1l: trivial
			qrat->QRATA(extOFF1, ext1l);

			Clause extval1;
			extval1.addnode(-selvall);
			extval1.addnode(-dl);
			extval1.addnode(ext1l);
			cell.def_dselval1->addnode(extval1);//RATA on ext1l: trivial
			qrat->QRATA(extval1, ext1l);

			Clause extanc1;
			extanc1.addnode(dl);
			extanc1.addnode(-ext1l);
			cell.def_dselval1->addnode(extanc1);//RATA on -ext1l: blocked on al
			qrat->QRATA(extanc1, -ext1l);

			Clause extsel1;
			extsel1.addnode(-selonl);
			extsel1.addnode(selvall);
			extsel1.addnode(-ext1l);
			cell.def_dselval1->addnode(extsel1);//RATA on -ext1l: blocked on selonl, blocked on -selvall
			qrat->QRATA(extsel1, -ext1l);
		}
	}

	void ConnCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no1, int line_no2);

	void XSelCnfLoad(bool val, Cnf* output, Strategy_Extractor* SE, int level, int line_no1, int line_no2){
		Index2 cell = SE->main_index->Idx_Conn->operator[](level).operator[](line_no1).operator[](line_no2);
		ClausalProof* pi = SE->input_proof;
		Index1 line_idx = SE->main_index->Idx_Proof->operator[](level).operator[](line_no1);
		Link1<LinkL<LinkL<Index2>>>* layer1 = SE->main_index->Idx_Conn->findnode(level);
		Link1<LinkL<Index2>>* layer2 = layer1->data.findnode(line_no1);
		Link1<Index2>* layer3 = layer2->data.findnode(line_no2);
		if (val) {
			if (cell.is_xselval1_defined == 0) {
				layer3->data.is_xselval1_defined = 1;
				ConnCnfLoad(output, SE, level, line_no1, line_no2);
				SelonCnfLoad(output, SE, level, line_no1);
				SelvalCnfLoad(output, SE, level, line_no1);
				copyinto(output, cell.def_aselval1);

			}
		}
		else {
			if (cell.is_xselval0_defined == 0) {
				layer3->data.is_xselval0_defined = 1;
				ConnCnfLoad(output, SE, level, line_no1, line_no2);
				SelonCnfLoad(output, SE, level, line_no1);
				SelvalCnfLoad(output, SE, level, line_no1);
				copyinto(output, cell.def_aselval0);
			}
		}
	}

	void ConnCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no1, int line_no2) {
		Index2 cell = SE->main_index->Idx_Conn->operator[](level).operator[](line_no1).operator[](line_no2);
		if (cell.is_ancestor_defined == 0) {
			Link1<LinkL<LinkL<Index2>>>* layer1 = SE->main_index->Idx_Conn->findnode(level);
			Link1<LinkL<Index2>>* layer2 = layer1->data.findnode(line_no1);
			Link1<Index2>* layer3 = layer2->data.findnode(line_no2);
			layer3->data.is_ancestor_defined = 1;
			ClausalProof *pi = SE->input_proof;
			
			if (line_no1 >= line_no2) {
			}
			else {
				for (int i = line_no1 + 1; i <= line_no2; i++) {
					Line L1child = pi->operator[](i);
					if (L1child.rule == REDUCTION) {
						if (L1child.parent0 == line_no1) {
							ConnCnfLoad(output, SE, level, i, line_no2);
						}
					}
					if (L1child.rule == RESOLUTION) {
						if (L1child.parent0 == line_no1) {
							XSelCnfLoad(0,output, SE, level, i, line_no2);
						}
						if (L1child.parent1 == line_no1) {
							XSelCnfLoad(1,output, SE, level, i, line_no2);
						}
					}
				}
				
			}
			copyinto(output, cell.def_ancestor);
		}
	}

	void backdef_cell2(Index* I, Strategy_Extractor* output, Index2 cell, Prefix P, ClausalProof* pi, int level, int line_no1, int line_no2) {
		Lit al = Lit(cell.ancestor);
		Line L1 = pi->operator[](line_no1);
		QRAT_Proof* qrat = output->output_QRAT;
		//if (line_no1 > line_no2) {
		//	Clause a_assert;
		//	a_assert.addnode(-al);
		//	cell.def_ancestor->addnode(a_assert);//RATA on -al: trivial
		//	qrat->QRATA(a_assert, -al);
		//}
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
				int mode;
				if (L1child.rule == REDUCTION) {
					if (L1child.parent0 == line_no1) {
						mode = 2;
						Cnf* ad_equiv = new Cnf;
						Cnf* child_equiv = new Cnf;
						//add CNFs here
						//are any actually necessary?
						cell.childrenof1->addnode(Index2_1(i, line_no1, 2, ad_equiv, child_equiv));//replace with more defs
						Lit a_child =Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).ancestor);
						Lit d_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).descendant);
						//ad_equivalence already done by a=d
						//child_equivalence already done by d definition

						a_long.addnode(a_child);
						Clause a_short= Clause();
						a_short.addnode(-a_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
				}
				if (L1child.rule == RESOLUTION) {
					//output->output_cnf->add_comment("ancestor resolution");
					Lit cond_child;
					Lit dcond_child;
					int parent0 = pi->operator[](line_no2).parent0;
					Lit dcond_parent0;
					int parent1 = pi->operator[](line_no2).parent0;
					Lit dcond_parent1;
					if (L1child.parent0 == line_no1) {
						mode = 0;
						if (parent0 > -1) {
							dcond_parent0 = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent0).dselval0);
						}
						if (parent1 > -1) {
							dcond_parent1 = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent1).dselval0);
						}
						cond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).aselval0);
						dcond_child= Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).dselval0);
						
						a_long.addnode(cond_child);
						Clause a_short = Clause();
						a_short.addnode(-cond_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
					if (L1child.parent1 == line_no1) {
						mode = 1;
						if (parent0 > -1) {
							Lit dcond_parent0 = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent0).dselval1);
						}
						if (parent1 > -1) {
							Lit dcond_parent1 = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent1).dselval1);
						}

						cond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).aselval1);
						dcond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).dselval1);
						a_long.addnode(cond_child);
						Clause a_short = Clause();
						a_short.addnode(-cond_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}


					
					
					//cell.childrenof1->addnode(Index2_1(i, line_no1, mode, ad_equiv, child_equiv));
				}
			}
			cell.def_ancestor->addnode(a_long);//RATA on -al: blocked on each cond
			qrat->QRATA(a_long, -al);

			
		}
		if (L1.rule == RESOLUTION) {
			Lit ext0l = Lit(cell.aselval0);
			Lit ext1l = Lit(cell.aselval1);
			Lit selonl = Lit(I->Idx_Proof->operator[](level).operator[](line_no1).selon);
			Lit selvall = Lit(I->Idx_Proof->operator[](level).operator[](line_no1).selval);


			Clause extOFF0;
			extOFF0.addnode(selonl);
			extOFF0.addnode(-al);
			extOFF0.addnode(ext0l);
			cell.def_aselval0->addnode(extOFF0);//RATA on ext0l: trivial
			qrat->QRATA(extOFF0, ext0l);

			Clause extval0;
			extval0.addnode(selvall);
			extval0.addnode(-al);
			extval0.addnode(ext0l);
			cell.def_aselval0->addnode(extval0);//RATA on ext0l: trivial
			qrat->QRATA(extval0, ext0l);

			Clause extanc0;
			extanc0.addnode(al);
			extanc0.addnode(-ext0l);
			cell.def_aselval0->addnode(extanc0);//RATA on -ext0l: blocked on -al
			qrat->QRATA(extanc0, -ext0l);

			Clause extsel0;
			extsel0.addnode(-selonl);
			extsel0.addnode(-selvall);
			extsel0.addnode(-ext0l);
			cell.def_aselval0->addnode(extsel0);//RATA on -ext0l: blocked on selonl, blocked on selvall
			qrat->QRATA(extsel0, -ext0l);

			Clause extOFF1;
			extOFF1.addnode(selonl);
			extOFF1.addnode(-al);
			extOFF1.addnode(ext1l);
			cell.def_aselval1->addnode(extOFF1);//RATA on ext1l: trivial
			qrat->QRATA(extOFF1, ext1l);

			Clause extval1;
			extval1.addnode(-selvall);
			extval1.addnode(-al);
			extval1.addnode(ext1l);
			cell.def_aselval1->addnode(extval1);//RATA on ext1l: trivial
			qrat->QRATA(extval1, ext1l);

			Clause extanc1;
			extanc1.addnode(al);
			extanc1.addnode(-ext1l);
			cell.def_aselval1->addnode(extanc1);//RATA on -ext1l: blocked on al
			qrat->QRATA(extanc1, -ext1l);

			Clause extsel1;
			extsel1.addnode(-selonl);
			extsel1.addnode(selvall);
			extsel1.addnode(-ext1l);
			cell.def_aselval1->addnode(extsel1);//RATA on -ext1l: blocked on selonl, blocked on -selvall
			qrat->QRATA(extsel1, -ext1l);
		}
		
	}


	

	void def_array2(Index* I, Strategy_Extractor* output, LinkL <LinkL<LinkL<Index2>>>* idx_conn, Prefix P, ClausalProof* pi, int level) {
		LinkL<LinkL<Index2>>* temp = new LinkL<LinkL<Index2>>();
		//need temp properties
		Link1<Line<Clause>>* current1 = pi->head;
		int line_no1 = 0;
		while (current1 != NULL) {
			Link1<Line<Clause>>* current2 = pi->head;
			int line_no2 = 0;
			while (current2 != NULL) {
				//define def clauses for cell on descendant
					Index2 cell = I->Idx_Conn->operator[](level).operator[](line_no1).operator[](line_no2);
					def_cell2(I, output, cell, P, pi, level, line_no1, line_no2);
				line_no2++;
				current2 = current2->next;
			}
			line_no1++;
			current1 = current1->next;
		}
		int botpos = pi->tail->position;
		for (int j = botpos; j >= 0; j--) {//j is the second (column) index 
			for (int i = botpos; i >= 0; i--) {//i is the first (row) index
				LinkL <Index2> idx_row = I->Idx_Conn->operator[](level).operator[](i);
				Index2 idx_cell = idx_row[j];
				//increment(&max_var, P, &(idx_cell->data.ancestor));
				//if (pi->operator[](i).rule == RESOLUTION) {
					backdef_cell2(I, output, idx_cell, P, pi, level, i, j);
					//increment(&max_var, P, &(idx_cell->data.xselon));
					//increment(&max_var, P, &(idx_cell->data.xselval0));
					//increment(&max_var, P, &(idx_cell->data.xselval1));
				//}

			}
		}

		
		//back_array2(max_var, temp, P, pi);
		// backdef_array2
		//idx_conn->addnode(*temp);

		//return max_var;
	}

	

	void StrategyCnfLoad(Cnf* output, Strategy_Extractor* SE, Var u) {
		//StrategyCnfLoad
		Link1<Index3>* current_u = SE->main_index->Idx_Strategy->head;
		while (current_u != NULL) {
			if (current_u->data.u == u) {
				if (current_u->data.is_strategy_defined==0) {
					current_u->data.is_strategy_defined = 1;
					Link1<Index3_1>* current_line = current_u->data.disjuncts->head;
					while (current_line != NULL) {
						int level = SE->QBF->prefix.lvl(u) - 1;
						int axpos = current_line->data.line_no;
						int botpos = SE->input_proof->tail->position;
						ConnCnfLoad(output, SE, level, axpos, botpos);
						current_line = current_line->next;
					}

					copyinto(output, current_u->data.def_strategy);
				}
			}
			current_u = current_u->next;

		}

		
	}

	void def_u3(Index* I, Strategy_Extractor* output, LinkL <Index3>* idx_strat, Prefix P, ClausalProof* pi, Var u) {
		Link1<Index3>* current_u = idx_strat->head;
		QRAT_Proof* qrat = output->output_QRAT;
		while(current_u != NULL) {
			if (current_u->data.u == u) {
				output->output_cnf->add_comment("Strategy clauses:");
				qrat->add_comment("Strategy clauses:");
				int level = P.lvl(u)-1;
				Link1<Index3_1>*current_line = current_u->data.disjuncts->head;
				Lit ul = Lit(current_u->data.strategy);
				Clause stratlong;
				stratlong.addnode(ul);
				while (current_line != NULL) {
					//define 
					
					int axpos = current_line->data.line_no;
					int upos = find_a_position(Lit(u), pi->operator[](axpos).clause);
					int botpos = pi->tail->position;
					Lit conn = Lit(I->Idx_Conn->operator[](level).operator[](axpos).operator[](botpos).ancestor);
					Lit uinA = Lit(I->Idx_Proof->operator[](level).operator[](axpos).memberships->operator[](upos).membership);
					Lit ex = Lit(current_line->data.xmembership);
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
				output->output_cnf->addnode(uforward);//not acceptable in QRAT
				Clause ubackward;
				ubackward.addnode(ul);
				ubackward.addnode(-Lit(u));
				output->output_cnf->addnode(ubackward);//not acceptable in QRAT

				StrategyCnfLoad(output->output_cnf, output, u);

			}
			current_u = current_u->next;
		}

	}



	Strategy_Extractor* Extract(QCNF* phi, ClausalProof* pi) {
		Strategy_Extractor* output = new Strategy_Extractor(phi, pi);
		*(output->output_cnf) = copy(phi->matrix);
		output->main_index = new Index;
		output->main_index->idx_prefix = new Prefix();
		output->main_index->base_max_var = phi->matrix.max_var();
		output->main_index->Idx_Proof = new LinkL<LinkL<Index1> >;
		output->main_index->Idx_Conn = new LinkL<LinkL<LinkL<Index2>>>;
		output->main_index->Idx_Strategy = new LinkL<Index3>;
		int max_var = output->main_index->base_max_var;
		Link1<Quantifier>* currentQ = phi->prefix.head;
		//zeroeth level
		//create a layer (<LinkL<Index1>) for Idx_Proof
			//create lines (<Index1>) for the layer
				//create idx 1_1 for the lines
				//add each idx 1_1 addnode()
			//add each line
		//add each layer
		int layer_level = 0;
		max_var = add_layer1(max_var, output->main_index->Idx_Proof, output->main_index->idx_prefix, pi);
		def_layer1(output->main_index, output, output->main_index->Idx_Proof, phi->prefix, pi, layer_level );
		//add_layer1 but for definition clauses
		max_var = add_array2(max_var, output->main_index->Idx_Conn, output->main_index->idx_prefix, pi);
		def_array2(output->main_index, output, output->main_index->Idx_Conn, phi->prefix, pi, layer_level);

		//add_array2 but for definition clauses
		while (currentQ != NULL) {
			if (currentQ->data.is_universal) {// add strategy
				max_var = add_u3(max_var, output->main_index->Idx_Strategy, output->main_index->idx_prefix, pi, currentQ->data.var);
				def_u3(output->main_index, output, output->main_index->Idx_Strategy, phi->prefix, pi, currentQ->data.var);
				//while loop for 
			
			}


			//add the base variables to idx_prefix
			if (currentQ->data.is_universal) {
				output->main_index->idx_prefix->addvar(-currentQ->data.var);
			}
			else {
				output->main_index->idx_prefix->addvar(currentQ->data.var);
			}
			bool is_next_quant_a_change = 1;
			if (currentQ->next != NULL) {
				
				if (currentQ->next->data.is_universal == currentQ->data.is_universal) {
					is_next_quant_a_change = 0;
				}
			}

			if (is_next_quant_a_change) {// add restricted proof
				layer_level++;
				max_var = add_layer1(max_var, output->main_index->Idx_Proof, output->main_index->idx_prefix, pi);
				def_layer1(output->main_index, output, output->main_index->Idx_Proof, phi->prefix, pi, layer_level);
				max_var = add_array2(max_var, output->main_index->Idx_Conn, output->main_index->idx_prefix, pi);
				def_array2(output->main_index, output, output->main_index->Idx_Conn, phi->prefix, pi, layer_level);
			}
			currentQ = currentQ->next;
		}
		output->main_index->idx_max_var = max_var;
		return output;
	}
}