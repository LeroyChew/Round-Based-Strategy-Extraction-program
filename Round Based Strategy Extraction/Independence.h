#pragma once
#include "Connectivity.h"



struct Drrs_Clause_Check {
	Clause clause;
	int entry_times;
	Lit last_entry;

	Drrs_Clause_Check() {
		clause = Clause();
		entry_times = 0;
		last_entry = Lit(0);
	}

	Drrs_Clause_Check(Clause C) {
		clause = C;
		entry_times = 0;
		last_entry = Lit(0);
	}
};

void resolution_path(Var u, Link1< Drrs_Clause_Check>* C, Lit entry_lit, LinkL< Drrs_Clause_Check>* Clauses, Prefix Pi);

void resolution_path_p(Lit p, Var u, Link1< Drrs_Clause_Check>* C, LinkL< Drrs_Clause_Check>* Clauses, Prefix Pi) {
	Var pv = p.var;
	int ulvl = Pi.lvl(u);
	int plvl = Pi.lvl(pv);
	if ((plvl > ulvl)&&(p!=C->data.last_entry)) {
		Link1< Drrs_Clause_Check>* currentc = Clauses->head;
		while (currentc != NULL) {
			if (currentc->data.entry_times < 1) {
				Link1<Lit>* currentcl = currentc->data.clause.head;
				while (currentcl != NULL) {
					Lit cl = currentcl->data;
					if (cl == -p) {
						resolution_path(u, currentc, cl, Clauses, Pi);
						currentcl = NULL;
					}
					else {
						currentcl = currentcl->next;
					}
				}
			}
			Lit entry_lit = currentc->data.last_entry;
			if ((currentc->data.entry_times == 1) && (-p != entry_lit)) {
				Link1<Lit>* currentcl = currentc->data.clause.head;
				while (currentcl != NULL) {
					Lit cl = currentcl->data;
					if (cl == -p) {
						currentc->data.entry_times++;
						currentc->data.last_entry = cl;
						resolution_path_p(entry_lit, u, currentc, Clauses, Pi);
						currentcl = NULL;
					}
					else {
						currentcl = currentcl->next;
					}
				}
			}
			currentc = currentc->next;
		}
	}

}

void resolution_path(Var u, Link1< Drrs_Clause_Check>* C, Lit entry_lit, LinkL< Drrs_Clause_Check>* Clauses, Prefix Pi) {
	C->data.entry_times++;
	C->data.last_entry = entry_lit;
	
	Link1<Lit>* currentl =C->data.clause.head;
	while (currentl != NULL) {
		Lit p = currentl->data;
		Var pv = p.var;
		int plvl =Pi.lvl(pv);
		resolution_path_p(p, u, C, Clauses, Pi);
		currentl = currentl->next;
	}
}

bool is_on_resolution_path(Lit x, LinkL<Drrs_Clause_Check>* clauses) {
	Link1< Drrs_Clause_Check>* currentc = clauses->head;
	while (currentc != NULL) {
		if (currentc->data.entry_times>0) {
		Link1<Lit>* currentcl = currentc->data.clause.head;
			while (currentcl != NULL) {
				if (currentcl->data == x) {
					if (currentc->data.entry_times>1 || currentc->data.last_entry!= x) {// check x is not entry literal
						return 1;
					}
				}
				currentcl = currentcl->next;
			}
		}
		currentc = currentc->next;
	}
	return 0;
}

Blocked_Set calculate_Drrs(Var u, Prefix Pi, Cnf Phi) {
	Link1<Clause>* currentC = Phi.head;
	LinkL<Drrs_Clause_Check>* clauses_pos= new LinkL<Drrs_Clause_Check>;
	LinkL<Drrs_Clause_Check>* clauses_neg = new LinkL<Drrs_Clause_Check>;
	//initialise Clause checkers
	while (currentC != NULL) {
		clauses_pos->addnode(Drrs_Clause_Check(currentC->data));
		clauses_neg->addnode(Drrs_Clause_Check(currentC->data));
		currentC = currentC->next;
	}
	//cycle through clauses to find u and bar u clauses
	Link1<Drrs_Clause_Check>* currentc = clauses_pos->head;
	Link1<Drrs_Clause_Check>* currentnc = clauses_neg->head;
	while (currentc != NULL) {
		Link1<Lit>* currentl = currentc->data.clause.head; {
			while (currentl != NULL) {
				Lit l = currentl->data;
				Lit ul = Lit(u);
				if (l == ul) {
					resolution_path(u, currentc, Lit(u), clauses_pos, Pi);
				}
				if (l == -ul) {
					resolution_path(u, currentnc, -Lit(u), clauses_neg, Pi);
				}
				currentl = currentl->next;
			}
		}
		currentc = currentc->next;
		currentnc = currentnc->next;
	}
	
	//compare lists the find blocking variables
	Blocked_Set rrs;
	Link1<Quantifier>* currentq = Pi.head;
	rrs.universal = u;
	while (currentq != NULL) {
		if (currentq->data.level>Pi.lvl(u)) {
			Var x = currentq->data.var;
			if ( (( is_on_resolution_path(Lit(x), clauses_pos) ) && (is_on_resolution_path(-Lit(x), clauses_neg)) ) || ((is_on_resolution_path(-Lit(x), clauses_pos)) && (is_on_resolution_path(Lit(x), clauses_neg)))) {
				rrs.existentials->addnode(x);
			}

		}
		currentq = currentq->next;
	}
	return rrs;
}

D_Scheme calculate_Drrs(Prefix Pi, Cnf Phi) {
	Link1<Quantifier>* quant_current = Pi.head;
	D_Scheme output = D_Scheme();;
	while (quant_current != NULL) {
		if (quant_current->data.is_universal) {
			Var u = quant_current->data.var;
			Blocked_Set Du = calculate_Drrs(u,  Pi,  Phi);
			output.blocked_sets->addnode(Du);
		}
		quant_current = quant_current->next;
	}
	return output;
}

D_Scheme calculate_Drrs(QCNF Psi) {
	return calculate_Drrs(Psi.prefix, Psi.matrix);
}

namespace idx{

	void prove_notinvar(Index* I, Strategy_Extractor* output, Index1 linecell, ClausalProof* pi, int level, int line_no, int pos) {
		Line L = pi->operator[](line_no);
		Rule rule = L.rule;
		Lit(meml) = I->Idx_Proof->operator[](level).operator[](line_no).memberships->operator[](pos).membership;
		Lit l = L.clause[pos];
		//cases based on L.rule needed filling out!
		Clause notin;
		notin.addnode(-l);
		notin.addnode(-meml);
		linecell.memberships->operator[](pos).proof_overlevel->addnode(notin);
	}

	void prove_notindl(Index* I, Strategy_Extractor* output, Index2 cell, ClausalProof* pi, int level, int axiom, int line_no2, int pos){
		Line L = pi->operator[](line_no2);
		Rule rule = L.rule;
		Lit meml = I->Idx_Proof->operator[](level).operator[](line_no2).memberships->operator[](pos).membership;
		Lit dl = I->Idx_Conn->operator[](level).operator[](axiom).operator[](line_no2).descendant;
		Index2_2 membership_cell= I->Idx_Conn->operator[](level).operator[](axiom).operator[](line_no2).indep_literals->operator[](pos);
		if (rule == RESOLUTION) {
			Lit l = L.clause[pos];
			int parent0 = L.parent0;
			Line L0= pi->operator[](parent0);
			int pivpos0 = L.litpos0;
			int litpos0 = find_a_position(l, L0.clause);

			int parent1 = L.parent1;
			Line L1 = pi->operator[](parent1);
			int pivpos1 = L.litpos1;
			int litpos1 = find_a_position(l, L1.clause);

			Lit selonc = I->Idx_Proof->operator[](level).operator[](line_no2).selon;
			Lit selvalc = I->Idx_Proof->operator[](level).operator[](line_no2).selval;

			Lit memP0;
			Lit memP1;
			Lit dP0;
			Lit dP1;
			if (litpos0 > -1) {
				memP0 = I->Idx_Proof->operator[](level).operator[](parent0).memberships->operator[](litpos0).membership;
				dP0 = I->Idx_Conn->operator[](level).operator[](axiom).operator[](parent0).descendant;
			}
			if (litpos1 > -1) {
				memP1 = I->Idx_Proof->operator[](level).operator[](parent1).memberships->operator[](litpos1).membership;
				dP1 = I->Idx_Conn->operator[](level).operator[](axiom).operator[](parent1).descendant;
			}

			Clause on0;
			on0.addnode(-selonc);
			on0.addnode(selvalc);
			on0.addnode(-dl);
			on0.addnode(-meml);
			membership_cell.proof_independence->addnode(on0);
			Clause on1;
			on1.addnode(-selonc);
			on1.addnode(-selvalc);
			on1.addnode(-dl);
			on1.addnode(-meml);
			membership_cell.proof_independence->addnode(on1);





			//this might be buggy
			if ((litpos0 < 0) || (litpos1 < 0)) {// single inheritance
				Clause off;
				off.addnode(-meml);
				off.addnode(-dl);
				off.addnode(selonc);
				membership_cell.proof_independence->addnode(off);//ata by equivalence, but what about dl coming from other side
			}
			else{ //dual inheritance
				Clause offsel;
				offsel.addnode(-dl);
				offsel.addnode(selonc);
				membership_cell.proof_independence->addnode(offsel);
				//for low level pivot, seloff implies both pivots, BUT prove_notinvar creates a contradiction
				//for high level pivot with no drrs, seloff implies both pivots but then no connectivity implies -dl
				//for high level pivot with partial drrs, ????
				// for high level pivot with drrs 
			}
		}
		if (rule == REDUCTION) {
			//notin doesn't require anything
		}
		if (rule == AXIOM) {
			//(-dl)  is trivial in most cases
			//if dl is true, we cannot select meml
		}
		Clause notin;
		notin.addnode(-dl);
		notin.addnode(-meml);
		membership_cell.proof_independence->addnode(notin);
	}
}