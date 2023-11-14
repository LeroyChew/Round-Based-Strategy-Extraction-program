#pragma once
#include "Logic.h"
#include "QBF.h"
struct AnnoLit {
	Lit Elit;
	LinkL<Lit> Aanno;
	AnnoLit() {
		Elit = Lit();
		Aanno = LinkL<Lit>();
	}
	AnnoLit(int l) {
		Elit = Lit(l);
		Aanno = LinkL<Lit>();
	}

	void clear_anno() {
		while (Aanno.tail != NULL) {
			Aanno.rmvnode(Aanno.tail);
		}
	}



	void sortlist() {
		bool is_swapped = 1;
		while (is_swapped) {
			is_swapped = 0;
			if (Aanno.head != NULL) {
				Link1<Lit>* current = Aanno.head;
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

	AnnoLit* copy() const {
		AnnoLit* output =new AnnoLit(Elit.DIMACS());
		Link1<Lit>* current = Aanno.head;
		while (current != NULL) {
			output->Aanno.addnode(current->data);
		}
		return output;
	}

	void ordered_annolit() {
			bool is_swapped = 1;
			while (is_swapped) {
				is_swapped = 0;
				if (Aanno.head != NULL) {
					Link1<Lit>* current = Aanno.head;
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

	bool operator ==(AnnoLit p) const {
		AnnoLit* l_copy = copy();
		AnnoLit* p_copy = p.copy();
		bool is_different = 0;
		if (l_copy->Elit == p_copy->Elit) {
			if (l_copy->Aanno.length == p_copy->Aanno.length) {
				l_copy->ordered_annolit();
				p_copy->ordered_annolit();

				Link1<Lit>* current_l = l_copy->Aanno.head;
				Link1<Lit>* current_p = p_copy->Aanno.head;
				
				while (current_l!=NULL) {
					if (current_l->data != current_p->data) {
						is_different = 1;
					}
					current_l = current_l->next;
					current_p = current_p->next;
				}
			}			
			else {
				is_different = 1;
			}
		}
		else {
			is_different = 1;
		}
		l_copy->clear_anno();
		p_copy->clear_anno();
		return !is_different;
	}

	void inst( LinkL<Lit> alpha, Prefix P) {
		Link1<Lit>* alpha_current= alpha.head;
		while (alpha_current!=NULL) {
			if (P.lvl(alpha_current->data.var)< P.lvl(Elit.var)) {
				Link1<Lit>* A_current = Aanno.head;
				bool is_match_found= 0 ;
				while (A_current!=NULL) {
					if (A_current->data.var== A_current->data.var) {
						is_match_found = 1;
					}
					A_current = A_current->next;
				}
				if (!is_match_found) {
					Aanno.addnode(A_current->data);
				}
			}
			alpha_current = alpha_current->next;
		}
	}
};

AnnoLit operator -(AnnoLit p) {
	AnnoLit l;
	l.Elit.var = p.Elit.var;
	if (p.Elit.is_pos) {
		l.Elit.is_pos = 0;
	}
	else {
		l.Elit.is_pos = 1;
	}
	return l;
}

struct Index_Anno {
	Var int_lit;
	AnnoLit anno_lit;

	Index_Anno() {
		int_lit = 0;
		anno_lit = AnnoLit();
	}

	Index_Anno(Var x, AnnoLit y) {
		int_lit = x;
		anno_lit = y;
	}
};

Cnf QuickDef(LinkL<Index_Anno> input) {
	Cnf f = Cnf();
	Link1<Index_Anno>* current = input.head;
	while (current != NULL) {
		Clause forward;
		Clause backward;
		forward.addnode(-current->data.int_lit);
		forward.addnode(current->data.anno_lit.Elit);
		backward.addnode(current->data.int_lit);
		backward.addnode(-current->data.anno_lit.Elit);
		f.addnode(forward);
		f.addnode(backward);
		current = current->next;
	}
	return f;
}


Lit annotolit(AnnoLit p, LinkL<Index_Anno> I ) {
	Link1<Index_Anno>* current = I.head;
	while (current != NULL) {
		if (current->data.anno_lit== p) {
			return current->data.int_lit;
		}
		if (current->data.anno_lit == -p) {
			return -(current->data.int_lit);
		}
	}
	return Lit();
}

AnnoLit littoanno(Lit p, LinkL<Index_Anno> I) {
	Link1<Index_Anno>* current = I.head;
	while (current != NULL) {
		if (current->data.int_lit == p) {
			return current->data.anno_lit;
		}
		if (current->data.int_lit == -p) {
			return -(current->data.anno_lit);
		}
	}
	return AnnoLit();
}


AnnoLit inst(AnnoLit p, LinkL<Lit> alpha, Prefix P) {
	AnnoLit* l = p.copy();
	l->inst(alpha, P);
	return *l;
}
LinkL<AnnoLit> inst(LinkL<AnnoLit> C, LinkL<Lit> alpha, Prefix P) {
	LinkL<AnnoLit> D= LinkL<AnnoLit>();
	Link1<AnnoLit>* current = C.head;
	while (current != NULL) {
		AnnoLit* l = current->data.copy();
		D.addnode(inst(*l, alpha, P));
		delete l;
		current = current->next;
	}
	return D;
}


QCNF ExpansionClauses(Prefix P, ClausalProof pi, LinkL<Index_Anno> I) {
	QCNF output;

	Link1<Quantifier>* currentP = P.head;
	while (currentP != NULL) {
		Var v = currentP->data.var;
		if (currentP->data.is_universal) {
			output.prefix.addvar(-v);
		}
		else {
			Link1<Index_Anno>* currentI = I.head;
			while (currentI != NULL) {
				if (currentI->data.anno_lit.Elit.var == v) {
					output.prefix.addvar(currentI->data.int_lit);
				}
				currentI = currentI->next;
			}
		}
		currentP = currentP->next;
	}
	Link1<Line<Clause>>* currentline = pi.head;
	while (currentline != NULL) {
		if (currentline->data.rule==AXIOM) {
			Clause C = currentline->data.clause;
			output.matrix.addnode(C);
		}
		currentline = currentline->next;
	}
	output.matrix.update_max_var();
	return output;
}

struct ExpResProof {
	QCNF Phi;
	QCNF ExpPhi;
	ClausalProof pi;
	LinkL<Index_Anno> index;

	int findAxiom(int proof_idx) {
		for (int i = 0; i < Phi.matrix.length; i++) {
			if (CheckAxiom(i, proof_idx)) {
				return i;
			}
		}
		return -1;
	}

	bool CheckAxiom(int cnf_idx, int proof_idx) {
		Clause C = Phi.matrix.operator[](cnf_idx);
		Clause D = pi.operator[](proof_idx).clause;
		
		LinkL<Lit> assumed_annotation;// check each annotated literal to see if 
		Link1<Lit>* currentD = D.head;
		while (currentD!=NULL) {
			Lit x = currentD->data;
			AnnoLit yt = littoanno(x, index);
			Link1<Lit>* current_D_anno = yt.Aanno.head;
			bool is_annotation_new = 0;
			while (current_D_anno!=NULL) {
				
				if (Phi.prefix.lvl(yt.Elit.var) < Phi.prefix.lvl(current_D_anno->data.var)) {//check if illegal
					return 0;
				}
				else {
					Link1<Lit>* current_assumed_anno = assumed_annotation.head;
					bool is_match_found = 0;
					while (current_assumed_anno != NULL) {
						if (current_D_anno->data == current_assumed_anno->data) {
							is_match_found = 1;
						}
						if (current_D_anno->data == -current_assumed_anno->data) {
							return 0;
						}
						current_assumed_anno = current_assumed_anno->next;
					}
					if (!is_match_found) {
						assumed_annotation.addnode(current_D_anno->data);
						is_annotation_new = 1;//start over
					}
					else {
						//return to 
					}
				}
				current_D_anno = current_D_anno->next;
			}
			if (is_annotation_new) {
				currentD = D.head;
			}
			else {
				currentD = currentD->next;
			}
			
			//then need to check that full annotation is applied correctly to all literals
		}
		currentD = D.head;
		while (currentD != NULL) {
			Lit x = currentD->data;
			AnnoLit yt = littoanno(x, index);
			Lit baselit = yt.Elit;
			if (yt.Elit == Lit()) {
				baselit = x;
			}
			else {
				Link1<Lit>* current_assumed_anno = assumed_annotation.head;
				while (current_assumed_anno != NULL) {
					if (Phi.prefix.lvl(yt.Elit.var) > Phi.prefix.lvl(current_assumed_anno->data.var)) {
						Link1<Lit>* current_D_anno = yt.Aanno.head;
						bool is_anno_found = 0;
						while (current_D_anno != NULL) {
							if (current_D_anno->data == current_assumed_anno->data) {
								is_anno_found = 1;
							}
							current_D_anno = current_D_anno->next;
						}
						if (!is_anno_found) {
							return 0;
						}

					}
					current_assumed_anno = current_assumed_anno->next;
				}
				
			}
			//Now check to see if originating from a propositional literal
			Link1<Lit>* currentC = C.head;
			bool is_parent_found = 0;
			while (currentC!=NULL) {
				if (currentC->data==baselit) {
					is_parent_found = 1;
				}
				currentC = currentC->next;
			}
			if (!is_parent_found) {
				return 0;
			}
			currentD = currentD->next;
		}

		return 1;
	}

};

