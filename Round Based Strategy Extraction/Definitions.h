#pragma once
#include "Index.h"

namespace idx {

	struct Strategy_Extractor {
		QCNF* QBF;
		ClausalProof* input_proof;
		Cnf* output_cnf;
		LinkL<AbsClause>* Abs_Strat_Prop;
		idx::Index* main_index;
		Strategy_Extractor() {
			QBF = new QCNF;
			input_proof = new ClausalProof;
			output_cnf = new Cnf;
			Abs_Strat_Prop = new LinkL<AbsClause>;
			main_index = new idx::Index;
		}
		Strategy_Extractor(QCNF* phi, ClausalProof* pi) {
			QBF->matrix = copy(phi->matrix);
			QBF->prefix = copy(phi->prefix);
			input_proof = pi;
		}
	};

	void def_literal1(Index I, Strategy_Extractor* output, Index1* idx_line, Prefix* P, Clause C, int position) {
		Index1_1* temp = new Index1_1();
		//increment(&max_var, P, &(temp->membership));
		temp->lit = C[position];
		idx_line->memberships->addnode(*temp);
		return;
	}

	void def_line1(Index I, Strategy_Extractor* output, Index1 read, Prefix P, ClausalProof* pi, int level, int line_no) {// add an entry on memberships, taut and sel
		//Index1* temp = new Index1();
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		
		int position = 0;
		if (L.rule == AXIOM) {
			Clause taut_long;
			Lit taut = Lit(read.tautological);//tautological implies cluse less than level
			taut_long.addnode(-taut); 
			if (C.length > 0) {

				Link1<Lit>* current = C.head;
				while (current != NULL) {
					//def_literal1(max_var, temp, P, C, position);
					Lit l= current->data;
					Lit ml = Lit(read.memberships->operator[](position).membership);
					if (P.lvl(l.var) <= level) {
						Clause mem_equiv1; //literal implies membership
						mem_equiv1.addnode(-l);
						mem_equiv1.addnode(ml);
						Clause mem_equiv2; //literal implies membership
						mem_equiv2.addnode(l);
						mem_equiv2.addnode(-ml);
						output->output_cnf->addnode(mem_equiv1);//RATA on ml: trivial
						output->output_cnf->addnode(mem_equiv2);//RATA on -ml: l, -l blocked on mem_equiv1
						taut_long.addnode(l);
						Clause taut_short;// any satisfied literal implies tautological
						taut_short.addnode(-l);
						taut_short.addnode(taut);
						output->output_cnf->addnode(taut_short);//RATA on taut: trivial

					}
					else {
						Clause mem_assertion;
						mem_assertion.addnode(ml);
						output->output_cnf->addnode(mem_assertion);//RATA on ml: trivial
					}


					current = current->next;
					position++;
				}
			}
			output->output_cnf->addnode(taut_long);//RATA on taut: l, -l blocked on each taut_short

		}





		
		//increment(&max_var, P, &(temp->tautological));
		//if res
		if (L.rule == RESOLUTION) {


			int parent0 = L.parent0;
			int litpos0 = L.litpos0;
			int parent1 = L.parent1;
			int litpos1 = L.litpos1;
			Lit p0 = Lit(I.Idx_Proof->operator[](level).operator[](parent0).memberships->operator[](litpos0).membership, 1);
			Lit p1 = Lit(I.Idx_Proof->operator[](level).operator[](parent1).memberships->operator[](litpos1).membership, 1);
			Lit selonl = Lit(read.selon);
			Lit selvall = Lit(read.selval);
			Clause selon_long;//defines when selon is false i.e. none of the triggers
			selon_long.addnode(-selonl);

			Clause selon_p0;//asserts selon true when missing pivot at parent0
			selon_long.addnode(-p0);
			selon_p0.addnode(p0);
			selon_p0.addnode(selonl);
			output->output_cnf->addnode(selon_p0);//RATA on selonl: trivial

			Clause selon_p1;//asserts selon true when missing pivot at parent1
			selon_long.addnode(-p1);
			selon_p1.addnode(p1);
			selon_p1.addnode(selonl);
			output->output_cnf->addnode(selon_p1);//RATA on selonl: trivial

			Clause selval_0andnot1; //asserts selval when only pivot1 is missing;
			selval_0andnot1.addnode(selvall);
			selval_0andnot1.addnode(-p0);
			selval_0andnot1.addnode(p1);
			output->output_cnf->addnode(selval_0andnot1);//RATA on selvall: trivial

			if (level > 0) {
				Lit prevon = Lit(I.Idx_Proof->operator[](level).operator[](line_no).selon, 1);
				Lit prevval = Lit(I.Idx_Proof->operator[](level).operator[](line_no).selval, 1);
				Clause selon_prev; //triggers if previous selon is true
				selon_long.addnode(prevon);
				selon_prev.addnode(-prevon);
				selon_prev.addnode(selvall);
				output->output_cnf->addnode(selon_prev);//RATA on selonl: trivial

				Clause selval_prevs;//triggers if previous selon is true and selval already true
				selval_prevs.addnode(selvall);
				selval_prevs.addnode(-prevon);
				selval_prevs.addnode(-prevval);
				output->output_cnf->addnode(selval_prevs);//RATA on selvall: trivial

				Clause selval_0on;// sets selval FALSE if previous sel is off and current parent0 missing pivot
				Clause selval_0val;// sets selval FALSE if previous val is false and current parent0 missing pivot
				Clause selval_1on;// sets selval FALSE if previous sel is off and current parent1 contains pivot
				Clause selval_1val;// sets selval FALSE if previous val is false and current parent1 contains pivot

				selval_0on.addnode(-selvall);
				selval_0on.addnode(prevon);
				selval_0on.addnode(p0);
				output->output_cnf->addnode(selval_0on);//RATA on -selvall, blocked by -prevon on selval_prevs, blocked by -p0 on selval_0andnot1

				selval_0val.addnode(-selvall);
				selval_0val.addnode(prevval);
				selval_0val.addnode(p0);
				output->output_cnf->addnode(selval_0val);//RATA on -selvall, blocked by -prevval on selval_prevs, blocked by -p0 on selval_0andnot1

				selval_1on.addnode(-selvall);
				selval_1on.addnode(prevon);
				selval_1on.addnode(-p1);
				output->output_cnf->addnode(selval_1on);//RATA on -selvall, blocked by -prevon on selval_prevs, blocked by p1 on selval_0andnot1

				selval_1val.addnode(-selvall);
				selval_1val.addnode(prevval);
				selval_1val.addnode(-p1);
				output->output_cnf->addnode(selval_1val);//RATA on -selvall, blocked by -prevval on selval_prevs, blocked by p1 on selval_0andnot1
			}
			else {
				Clause selval_0;// sets selval FALSE if current parent0 missing pivot
				selval_0.addnode(-selvall);
				selval_0.addnode(p0);
				output->output_cnf->addnode(selval_0);//RATA on -selvall, blocked by p0;
				Clause selval_1;// sets selval FALSE if current parent1 contains pivot
				selval_1.addnode(-selvall);
				selval_1.addnode(-p1);
				output->output_cnf->addnode(selval_0);//RATA on -selvall, blocked by p1;
			}

			output->output_cnf->addnode(selon_long);//RATA on -selonl: blocked on each short clause


			//taut
			Lit tautl = Lit(read.tautological);
			Lit taut_parent0 = Lit(I.Idx_Proof->operator[](level).operator[](parent0).tautological);
			Lit taut_parent1 = Lit(I.Idx_Proof->operator[](level).operator[](parent1).tautological);

			Clause taut_forwardoff0;
			taut_forwardoff0.addnode(selonl);
			taut_forwardoff0.addnode(-taut_parent0);
			taut_forwardoff0.addnode(tautl);
			output-> output_cnf->addnode(taut_forwardoff0);//RATA on tautl: trivial

			Clause taut_forwardoff1;
			taut_forwardoff1.addnode(selonl);
			taut_forwardoff1.addnode(-taut_parent1);
			taut_forwardoff1.addnode(tautl);
			output->output_cnf->addnode(taut_forwardoff1);//RATA on tautl: trivial

			Clause taut_forwardon0;
			taut_forwardon0.addnode(-selonl);
			taut_forwardon0.addnode(selvall);
			taut_forwardon0.addnode(-taut_parent0);
			taut_forwardon0.addnode(tautl);
			output->output_cnf->addnode(taut_forwardon0);//RATA on tautl: trivial

			Clause taut_forwardon1;
			taut_forwardon1.addnode(-selonl);
			taut_forwardon1.addnode(-selvall);
			taut_forwardon1.addnode(-taut_parent1);
			taut_forwardon1.addnode(tautl);
			output->output_cnf->addnode(taut_forwardon1);//RATA on tautl: trivial

			Clause taut_backwardoff;
			taut_backwardoff.addnode(selonl);
			taut_backwardoff.addnode(taut_parent0);
			taut_backwardoff.addnode(taut_parent1);
			taut_backwardoff.addnode(-tautl);
			output->output_cnf->addnode(taut_backwardoff);//RATA on -tautl: 0 blocked on -taut_parent0, 1 blocked on -taut_parent1

			Clause taut_backwardon0;
			taut_backwardon0.addnode(-selonl);
			taut_backwardon0.addnode(selvall);
			taut_backwardon0.addnode(taut_parent0);
			taut_backwardon0.addnode(-tautl);
			output->output_cnf->addnode(taut_backwardon0); //RATE on -taul: 0 blocked on -taut_parent0, off1 blocked by selonl, on1 blocked by selvall

			Clause taut_backwardon1;
			taut_backwardon1.addnode(-selonl);
			taut_backwardon1.addnode(-selvall);
			taut_backwardon1.addnode(taut_parent1);
			taut_backwardon1.addnode(-tautl);
			output->output_cnf->addnode(taut_backwardon1); //RATE on -taul: 1 blocked on -taut_parent1, off0 blocked by selonl, on0 blocked by selvall

			//members
			Clause P0 = pi->operator[](parent0).clause;
			Clause P1 = pi->operator[](parent1).clause;
			Link1<Lit>* current = L.clause.head;
			int lit_counter = 0;
			while(current != NULL) {
				Lit l = current->data;
				int pos0 = find_a_position(l, P0);
				int pos1 = find_a_position(l, P1);
				if ((pos0 == -1) && (pos1 != -1)) {
					Lit l1= Lit(I.Idx_Proof->operator[](level).operator[](parent1).memberships->operator[](pos1).membership);
					Clause mem_val;
					mem_val.addnode(-selvall);
					mem_val.addnode(-l1);
					mem_val.addnode(l);
					output->output_cnf->addnode(mem_val);//RATA on l, trivial;
					Clause mem_on;
					mem_on.addnode(selonl);
					mem_on.addnode(-l1);
					mem_on.addnode(l);
					output->output_cnf->addnode(mem_on);//RATA on l, trivial;
					Clause mem_parent;
					mem_parent.addnode(l1);
					mem_parent.addnode(-l);
					output->output_cnf->addnode(mem_parent);//RATA on -l, blocked by -l1 in both clauses
					Clause mem_sel;
					mem_sel.addnode(-selonl);
					mem_sel.addnode(selvall);
					mem_sel.addnode(-l);
					output->output_cnf->addnode(mem_sel);//RATA on -l, blocked by selonl on mem_on and -selvall in mem_val
					//add equivalence for parent1
				}
				if ((pos0 != -1) && (pos1 == -1)) {
					Lit l0 = Lit(I.Idx_Proof->operator[](level).operator[](parent0).memberships->operator[](pos0).membership);
					//add equivalence for parent0
				}
				if ((pos0 != -1) && (pos1 != -1)) {
					Lit l0 = Lit(I.Idx_Proof->operator[](level).operator[](parent0).memberships->operator[](pos0).membership);
					Lit l1 = Lit(I.Idx_Proof->operator[](level).operator[](parent1).memberships->operator[](pos1).membership);
					//disjunctive reasoning except for selon
				}
				lit_counter++;
				current = current->next;
			}

			//check if present in parent0 and find index
			//check if present in parent1 and find index




		}
		//
		
		return;
	}

	void def_layer1(Index I, Strategy_Extractor* output, LinkL<LinkL<Index1> >* idx_proof, Prefix P, ClausalProof* pi, int level) {
		LinkL<Index1> read = I.Idx_Proof->operator[](level);
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


	Strategy_Extractor* Extract(QCNF* phi, ClausalProof* pi) {
		Strategy_Extractor* output = new Strategy_Extractor(phi, pi);
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
		max_var = add_layer1(max_var, output->main_index->Idx_Proof, output->main_index->idx_prefix, pi);
		//add_layer1 but for definition clauses
		max_var = add_array2(max_var, output->main_index->Idx_Conn, output->main_index->idx_prefix, pi);
		//add_array2 but for definition clauses
		while (currentQ != NULL) {
			if (currentQ->data.is_universal) {// add strategy
				max_var = add_u3(max_var, output->main_index->Idx_Strategy, output->main_index->idx_prefix, pi, currentQ->data.var);
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
				max_var = add_layer1(max_var, output->main_index->Idx_Proof, output->main_index->idx_prefix, pi);
				max_var = add_array2(max_var, output->main_index->Idx_Conn, output->main_index->idx_prefix, pi);

			}
			currentQ = currentQ->next;
		}
		output->main_index->idx_max_var = max_var;
		return output;
	}
}