#pragma once
#include "Definitions.h"

namespace idx {

	void backproof_cell2(Index* I, Strategy_Extractor* output, Index2 cell, ClausalProof* pi, int level, int line_no1, int line_no2) {
		Lit al = Lit(cell.ancestor);
		Lit dl = Lit(cell.descendant);
		Line L1 = pi->operator[](line_no1);
		QRAT_Proof* qrat = output->output_QRAT;
		//if (line_no1 > line_no2) {
		//	Clause a_assert;
		//	a_assert.addnode(-al);
		//	cell.def_ancestor->addnode(a_assert);//RATA on -al: trivial
		//	qrat->QRATA(a_assert, -al);
		//}
		if (line_no1 == line_no2) {
			Clause adbackward;
			adbackward.addnode(-dl);
			adbackward.addnode(al);
			Clause adforward;
			adforward.addnode(dl);
			adforward.addnode(-al);
			cell.proof_a_equals_d->addnode(adbackward); //ATA -dl
			cell.proof_a_equals_d->addnode(adforward); //ATA all the children -dl force singleton -al
			qrat->ATA(adbackward);
			qrat->ATA(adforward);
		}
		else {
			
			
			if (pi->operator[](line_no2).rule == AXIOM) {
				Clause adbackward;
				adbackward.addnode(-dl);
				adbackward.addnode(al);
				Clause adforward;
				adforward.addnode(dl);
				adforward.addnode(-al);
				cell.proof_a_equals_d->addnode(adbackward); //ATA -dl
				cell.proof_a_equals_d->addnode(adforward); //ATA all the children -dl force singleton -al
				qrat->ATA(adbackward);
				qrat->ATA(adforward);
			}
			if (pi->operator[](line_no2).rule == REDUCTION) {
				Clause nota_defined_by_ext_aparent;
				nota_defined_by_ext_aparent.addnode(-al);
				//remainder not needed as -dAC implies each -ext_aparent through binary clauses
				Clause adforward;
				adforward.addnode(dl);
				adforward.addnode(-al);

				Clause adbackward;
				adbackward.addnode(-dl);
				adbackward.addnode(al);
				
				//Lit dpl = Lit(I->Idx_Conn->operator[](level).operator[](line_no1).operator[](parent2_red).descendant);

				int parent2_red = pi->operator[](line_no2).parent0;

				for (int i = line_no1 + 1; i <= line_no2; i++) {
					Line L1child = pi->operator[](i);
					Lit acond_child;
					Lit dcond_child;
					Lit dcond_parent;
					Lit acond_parent;
					/*
					if (L1child.rule == REDUCTION) {
						if (L1child.parent0 == line_no1) {
							
							acond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).ancestor);
							dcond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).descendant);
							//nota_defined_by_ext_d.addnode(dcond_child);
							
							//dcond_parent = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent2_red).descendant);
							//nota_defined_by_ext_dparent.addnode(dcond_parent);

							acond_parent = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent2_red).ancestor);
							nota_defined_by_ext_aparent.addnode(acond_parent);
						}
					}
					if (L1child.rule == RESOLUTION) {
						if (L1child.parent0 == line_no1) {
							acond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).aselval0);
							dcond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).dselval0);
							//nota_defined_by_ext_d.addnode(dcond_child);

							//dcond_parent = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent2_red).dselval0);
							//nota_defined_by_ext_dparent.addnode(dcond_parent);

							acond_parent = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent2_red).aselval0);
							nota_defined_by_ext_aparent.addnode(acond_parent);
						}
						if (L1child.parent1 == line_no1) {
							acond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).aselval1);
							dcond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).dselval1);
							//nota_defined_by_ext_d.addnode(dcond_child);
							//dcond_parent = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent2_red).dselval1);
							//nota_defined_by_ext_dparent.addnode(dcond_parent);

							acond_parent = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent2_red).aselval1);
							nota_defined_by_ext_aparent.addnode(acond_parent);
						}
					}
					*/
					
				}
				//cell.proof_a_equals_d->addnode(nota_defined_by_ext_d); //ATA resolving with binary clauses
					//cell.proof_a_equals_d->addnode(nota_defined_by_ext_dparent); //ATA
					//cell.proof_a_equals_d->addnode(nota_defined_by_ext_aparent); //ATA
				cell.proof_a_equals_d->addnode(adforward); //ATA 
				cell.proof_a_equals_d->addnode(adbackward); //ATA uses propagation through -extension variables not possible the other direction
				//qrat->ATA(nota_defined_by_ext_d);
				//qrat->ATA(nota_defined_by_ext_dparent);
				//qrat->ATA(nota_defined_by_ext_aparent);
				qrat->ATA(adforward);
				qrat->ATA(adbackward);
			}
			if (pi->operator[](line_no2).rule == RESOLUTION) {
				Lit selonc = Lit(I->Idx_Proof->operator[](level).operator[](line_no2).selon);
				Lit selvalc = Lit(I->Idx_Proof->operator[](level).operator[](line_no2).selval);
				Clause adbackward;
				adbackward.addnode(-dl);
				adbackward.addnode(al);
				Clause adbackwardon;
				adbackwardon.addnode(-dl);
				adbackwardon.addnode(selonc);
				Clause adbackwardval0;
				adbackwardval0.addnode(-dl);
				adbackwardval0.addnode(-selonc);
				adbackwardval0.addnode(selvalc);
				Clause adbackwardval1;
				adbackwardval1.addnode(-dl);
				adbackwardval1.addnode(-selonc);
				adbackwardval1.addnode(-selvalc);
				Clause adforwardon;
				adforwardon.addnode(-al);
				adforwardon.addnode(dl);
				adforwardon.addnode(selonc);
				Clause adforwardval0;
				adforwardon.addnode(-al);
				adforwardval0.addnode(dl);
				adforwardval0.addnode(-selonc);
				adforwardval0.addnode(selvalc);
				Clause adforwardval1;
				adforwardon.addnode(-al);
				adforwardval1.addnode(dl);
				adforwardval1.addnode(-selonc);
				adforwardval1.addnode(-selvalc);
				Clause adforward;
				adforward.addnode(dl);
				adforward.addnode(-al);


				for (int i = line_no1 + 1; i <= line_no2; i++) {
					Line L1child = pi->operator[](i);
					Lit acond_child;
					Lit dcond_child;
					Lit dcond_parent;
					Lit acond_parent;

					if (L1child.rule == REDUCTION) {
						if (L1child.parent0 == line_no1) {
							//acond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).ancestor);
							dcond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).descendant);
							adbackwardon.addnode(dcond_child);
							adbackwardval0.addnode(dcond_child);
							adbackwardval1.addnode(dcond_child);
						}
					}
					if (L1child.rule == RESOLUTION) {
						if (L1child.parent0 == line_no1) {
							dcond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).dselval0);
							adbackwardon.addnode(dcond_child);
							adbackwardval0.addnode(dcond_child);
							adbackwardval1.addnode(dcond_child);
						}
						if (L1child.parent1 == line_no1) {
							dcond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).dselval1);
							adbackwardon.addnode(dcond_child);
							adbackwardval0.addnode(dcond_child);
							adbackwardval1.addnode(dcond_child);
						}
					}
				}
				cell.proof_a_equals_d->addnode(adforwardon);//ata propagates all the way back to definition of al
				cell.proof_a_equals_d->addnode(adforwardval0);//ata
				cell.proof_a_equals_d->addnode(adforwardval1);//ata
				cell.proof_a_equals_d->addnode(adforward);//ata reduces the final three to a case analysis starting with selon
				
				//ATA 
				cell.proof_a_equals_d->addnode(adbackwardon);//ata
				cell.proof_a_equals_d->addnode(adbackwardval0);//ata
				cell.proof_a_equals_d->addnode(adbackwardval1);//ata
				cell.proof_a_equals_d->addnode(adbackward); //ata

				qrat->ATA(adforwardon);
				qrat->ATA(adforwardval0);
				qrat->ATA(adforwardval1);
				qrat->ATA(adforward);

				qrat->ATA(adbackwardon);
				qrat->ATA(adbackwardval0);
				qrat->ATA(adbackwardval1);
				qrat->ATA(adbackward);
			}
			
			Clause nota_defined_by_parents;
			nota_defined_by_parents.addnode(-al);
			Clause ad_forward = Clause();
			Clause ad_backward = Clause();
			for (int i = line_no1 + 1; i <= line_no2; i++) {
				Line L1child = pi->operator[](i);
				int mode=-1;
				if (L1child.rule == REDUCTION) {
					if (L1child.parent0 == line_no1) {
						mode = 2;
						Cnf* ad_equiv = new Cnf;
						Cnf* child_equiv = new Cnf;
						
						//add CNFs here
						//are any actually necessary?
						cell.childrenof1->addnode(Index2_1(i, line_no1, 2, ad_equiv, child_equiv));//replace with more defs
						Lit a_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).ancestor);
						Lit d_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).descendant);
						
						
						//ad_equivalence already done by a=d
						//child_equivalence already done by d definition
						

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
						dcond_child = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](line_no2).dselval0);
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
					}
					//nota_defined_by_ext_d.addnode(dcond_child);
					//create equivalence 
					if (mode > -1) {

						ad_forward.addnode(-cond_child);
						ad_forward.addnode(dcond_child);

						ad_backward.addnode(cond_child);
						ad_backward.addnode(-dcond_child);


						Cnf* child_equiv = new Cnf;
						if (pi->operator[](line_no2).rule == AXIOM) {
							//not needed
						}

						if (pi->operator[](line_no2).rule == REDUCTION) {
							int parent0 = pi->operator[](line_no2).parent0;
							Lit dcond_parent0 = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent0).dselval0);
							Clause d_forward = Clause();
							d_forward.addnode(-dcond_child);
							d_forward.addnode(dcond_parent0);
							Clause d_backward = Clause();
							d_backward.addnode(dcond_child);
							d_backward.addnode(-dcond_parent0);
							child_equiv->addnode(d_forward);
							child_equiv->addnode(d_backward);
							qrat->ATA(d_forward);
							qrat->ATA(d_backward);
						}
						if (pi->operator[](line_no2).rule == RESOLUTION) {
							Line child_line = pi->operator[](line_no2);
							int parent0 = pi->operator[](line_no2).parent0;
							Line parent_line = pi->operator[](parent0);
							Index2 parent_cell = I->Idx_Conn->operator[](level).operator[](i).operator[](parent0);
							int parent1 = pi->operator[](line_no2).parent1;
							Lit dcond_parent0; 
							Lit dcond_parent1;
							if (L1child.parent0 == line_no1) {
								dcond_parent0 = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent0).dselval0);
								dcond_parent1 = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent1).dselval0);
							}
							if (L1child.parent1 == line_no1) {
								dcond_parent0 = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent0).dselval1);
								dcond_parent1 = Lit(I->Idx_Conn->operator[](level).operator[](i).operator[](parent1).dselval1);
							}

							if (dcond_parent0.DIMACS() == 0) {
								cout << "dcond error level:" << level << " line1: " << line_no1 << " line2: " << parent0 << endl;
							}

							Lit selonc = Lit(I->Idx_Proof->operator[](level).operator[](line_no2).selon);
							Lit selvalc = Lit(I->Idx_Proof->operator[](level).operator[](line_no2).selval);
							
							//possibvly inversion of selon
							qrat->add_comment("seven dcond clauses");
							Clause cond_lines;
							cond_lines.addnode(-dcond_child);
							cond_lines.addnode(dcond_parent0);
							cond_lines.addnode(dcond_parent1);
							child_equiv->addnode(cond_lines);
							qrat->ATA(cond_lines);
							Clause cond_P0;
							cond_P0.addnode(-dcond_child);
							cond_P0.addnode(dcond_parent0);
							cond_P0.addnode(-selonc);
							cond_P0.addnode(selvalc);
							child_equiv->addnode(cond_P0);
							qrat->ATA(cond_P0);
							Clause cond_P1;
							cond_P1.addnode(-dcond_child);
							cond_P1.addnode(dcond_parent1);
							cond_P1.addnode(-selonc);
							cond_P1.addnode(-selvalc);
							child_equiv->addnode(cond_P1);
							qrat->ATA(cond_P1);

							Clause cond_on0;
							cond_on0.addnode(-dcond_parent0);
							cond_on0.addnode(dcond_child);
							cond_on0.addnode(selonc);
							child_equiv->addnode(cond_on0);
							qrat->ATA(cond_on0);
							Clause cond_val0;
							cond_val0.addnode(-dcond_parent0);
							cond_val0.addnode(dcond_child);
							cond_val0.addnode(selvalc);
							child_equiv->addnode(cond_val0);
							qrat->ATA(cond_val0);
							Clause cond_on1;
							cond_on1.addnode(-dcond_parent1);
							cond_on1.addnode(dcond_child);
							cond_on1.addnode(selonc);
							child_equiv->addnode(cond_on1);
							qrat->ATA(cond_on1);
							Clause cond_val1;
							cond_val1.addnode(-dcond_parent1);
							cond_val1.addnode(dcond_child);
							cond_val1.addnode(selvalc);
							child_equiv->addnode(cond_val1);
							
							qrat->ATA(cond_val1);
						}
						Cnf* ad_equiv = new Cnf;
						ad_equiv->addnode(ad_forward);
						ad_equiv->addnode(ad_backward);
						qrat->ATA(ad_forward);
						qrat->ATA(ad_backward);
						cell.childrenof1->addnode(Index2_1(i, line_no1, mode, ad_equiv, child_equiv));
						
					}
				}
			}

			
		}
		if (L1.rule == RESOLUTION) {

		}

	}


	void equivalence_by_distance(Index* I, Strategy_Extractor* output, ClausalProof* pi, int level) {
		int proof_length = pi->length;
		for (int distance = 1 - proof_length; distance < proof_length; distance++) {
			for (int line_no1 = 0; line_no1 < proof_length; line_no1++) {
				int line_no2 = line_no1 + distance;
				if ((line_no2 >= 0) && (line_no2 < proof_length)) {
					backproof_cell2(I, output, I->Idx_Conn->operator[](level).operator[](line_no1).operator[](line_no2),  pi, level, line_no1, line_no2);
				}
			}
		}
	}

	void all_equivalence_by_distance(Strategy_Extractor* output) {
		int level = 0;
		Index* I = output->main_index;
		ClausalProof* pi = output->input_proof;
		Link1<LinkL<LinkL<Index2>>>* current = I->Idx_Conn->head;
		while (current != NULL){
			equivalence_by_distance( I,  output,  pi, level);
			level++;
			current = current->next;
		}
	}
}