#pragma once
#include "QRAT.h"
void addxor(Cnf* the_cnf, Var a, Var b, Var abxor) {
	Lit la = Lit(a);
	Lit lb = Lit(b);
	Lit lx = Lit(abxor);

	Clause xNeg;
	xNeg.addnode(la);
	xNeg.addnode(lb);
	xNeg.addnode(-lx);
	the_cnf->addnode(xNeg);

	Clause AllNeg;
	AllNeg.addnode(-la);
	AllNeg.addnode(-lb);
	AllNeg.addnode(-lx);
	the_cnf->addnode(AllNeg);

	Clause aNeg;
	aNeg.addnode(-la);
	aNeg.addnode(lb);
	aNeg.addnode(lx);
	the_cnf->addnode(aNeg);

	Clause bNeg;
	bNeg.addnode(la);
	bNeg.addnode(-lb);
	bNeg.addnode(lx);
	the_cnf->addnode(bNeg);

	
}

QCNF QParity(int n) {
	QCNF qparity;
	Cnf* matrix = &qparity.matrix;
	for (int i = 1; i < n + 1; i++) {
		qparity.prefix.addvar(i);
	}
	qparity.prefix.addvar(-(n + 1));
	for (int i = n+2; i < (2*n + 1); i++) {
		qparity.prefix.addvar(i);
	}
	addxor(matrix, 1, 2, n + 2);
	for (int i = 3; i < n + 1; i++) {
		addxor(matrix, i, n + i - 1, n + i);
	}
	Clause pos;
	pos.addnode(Lit(n + 1));
	pos.addnode(Lit(2*n));
	matrix->addnode(pos);
	Clause neg;
	neg.addnode(-Lit(n + 1));
	neg.addnode(-Lit(2 * n ));
	matrix->addnode(neg);
	return qparity;
}

ClausalProof lqrcQParity(int n) {
	QCNF qparity= QParity(n);
	ClausalProof short_proof = ClausalProof();
	Link1<Clause>* current = qparity.matrix.head;
	while (current != NULL) {
		short_proof.add_ax(current->data);
		current = current->next;
	}
	int currentend = short_proof.length;
	short_proof.add_res(4 * (n - 2), 4 * (n - 2) + 4, Lit(2 * n));
	short_proof.add_res(4 * (n - 2) + 1, 4 * (n - 2) + 4, Lit(2 * n));
	short_proof.add_res(4 * (n - 2) + 2, 4 * (n - 2) + 5, -Lit(2 * n));
	short_proof.add_res(4 * (n - 2) + 3, 4 * (n - 2) + 5, -Lit(2 * n));
	short_proof.add_res(currentend, currentend + 2, -Lit(n));
	short_proof.add_res(currentend+1, currentend + 3, Lit(n));
	currentend = currentend + 6;
	for (int i = n - 1; i > 2; i--) {
		int past_xors = i - 2;
		short_proof.add_res(4 * past_xors, currentend - 2, Lit(n + i));
		short_proof.add_res(4 * past_xors + 1, currentend - 2, Lit(n + i));
		short_proof.add_res(4 * past_xors + 2, currentend - 1, -Lit(n + i));
		short_proof.add_res(4 * past_xors + 3, currentend - 1, -Lit(n + i));
		short_proof.add_res(currentend, currentend + 2, -Lit(i));
		short_proof.add_res(currentend + 1, currentend + 3, Lit(i));
		currentend = currentend + 6;
	}
	short_proof.add_res(0, currentend - 2, Lit(n + 2));
	short_proof.add_res(1, currentend - 2, Lit(n + 2));
	short_proof.add_res(2, currentend - 1, -Lit(n + 2));
	short_proof.add_res(3, currentend - 1, -Lit(n + 2));
	short_proof.add_res(currentend, currentend + 2, -Lit(1));
	short_proof.add_res(currentend + 1, currentend + 3, Lit(1));
	short_proof.add_res(currentend + 4, currentend + 5, -Lit(2));
	short_proof.add_red(currentend + 6, n + 1);
	return short_proof;
}