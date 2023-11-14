#pragma once
#include "QRAT.h"
#include "Exp.h"
#include "Circuits.h"

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
	matrix->update_max_var();
	return qparity;
}


ExpResProof expQParity(int n){
	ExpResProof output;
	output.Phi = QParity(n);
	for (int i = 1; i < n + 1; i++) {
		//add one
		AnnoLit l=AnnoLit(i);
		Index_Anno I= Index_Anno((2 * n) + i, l);
		output.index.addnode(I);
	}
	for (int i = 2; i < n + 1; i++) {
		//add two assignments
		AnnoLit l0 = AnnoLit(n+i);
		l0.Aanno.addnode(Lit(-(n + 1)));
		AnnoLit l1 = AnnoLit(n+i);
		l0.Aanno.addnode(Lit((n + 1)));
		Index_Anno I0 = Index_Anno((3 * n) + i, l0);
		Index_Anno I1 = Index_Anno((4 * n) + i, l1);
		output.index.addnode(I0);
		output.index.addnode(I1);
	}
	for (int i = 2; i < n + 1; i++) {
		int cpe = output.pi.length - 1;
		Lit ti0 = Lit((3 * n) + i);
		Lit ti1 = Lit((4 * n) + i);
		Lit ti0prev = Lit((3 * n) + i-1);
		Lit ti1prev = Lit((4 * n) + i-1);
		if (i == 2) {
			ti0prev = Lit((2 * n) + i - 1);
			ti1prev = Lit((2 * n) + i - 1);
		}
		Lit xi = Lit(2*n+i);

		Clause not1st0;
		not1st0.addnode(-ti0prev);
		not1st0.addnode(xi);
		not1st0.addnode(ti0);
		Clause not2nd0;
		not2nd0.addnode(ti0prev);
		not2nd0.addnode(-xi);
		not2nd0.addnode(ti0);
		Clause not3rd0;
		not3rd0.addnode(ti0prev);
		not3rd0.addnode(xi);
		not3rd0.addnode(-ti0);
		Clause notall0;
		notall0.addnode(-ti0prev);
		notall0.addnode(-xi);
		notall0.addnode(-ti0);

		Clause not1st1;
		not1st1.addnode(-ti1prev);
		not1st1.addnode(xi);
		not1st1.addnode(ti1);
		Clause not2nd1;
		not2nd1.addnode(ti1prev);
		not2nd1.addnode(-xi);
		not2nd1.addnode(ti1);
		Clause not3rd1;
		not3rd1.addnode(ti1prev);
		not3rd1.addnode(xi);
		not3rd1.addnode(-ti1);
		Clause notall1;
		notall1.addnode(-ti1prev);
		notall1.addnode(-xi);
		notall1.addnode(-ti1);

		output.pi.add_ax(not1st0);
		output.pi.add_ax(not2nd0);
		output.pi.add_ax(not3rd0);
		output.pi.add_ax(notall0);
		output.pi.add_ax(not1st1);
		output.pi.add_ax(not2nd1);
		output.pi.add_ax(not3rd1);
		output.pi.add_ax(notall1);

		output.pi.add_res(cpe + 1, cpe + 8,-xi );//-t0-t1 t0 -t1
		output.pi.add_res(cpe + 2, cpe + 7, xi);//t0 t1 t0 -t1
		output.pi.add_res(cpe + 3, cpe + 6, -xi);//t0 t1 -t0 t1
		output.pi.add_res(cpe + 4, cpe + 5, xi);//-t0-t1 -t0 t1
		if (cpe > -1) {
			output.pi.add_res(cpe - 1, cpe + 8 + 1, -ti0prev);
			output.pi.add_res(cpe, cpe + 8 + 2, ti0prev);
			output.pi.add_res(cpe, cpe + 8 + 3, ti0prev);
			output.pi.add_res(cpe - 1, cpe + 8 + 4, -ti0prev);
			output.pi.add_res(cpe + 8 + 4 + 1, cpe + 8 + 4 + 2, ti1prev);
			output.pi.add_res(cpe + 8 + 4 + 3, cpe + 8 + 4 + 4, -ti1prev);
		}
		else {
			output.pi.add_res(cpe + 8 + 1, cpe + 8 + 2, ti0prev);
			output.pi.add_res(cpe + 8 + 3, cpe + 8 + 4, -ti0prev);
		}
	}
	Lit u = Lit(n + 1);
	Lit tn0 = Lit(4 * n);
	Lit tn1 = Lit(5 * n);
	int cpe = output.pi.length - 1;
	Clause pos;
	pos.addnode(u);
	pos.addnode(tn0);
	Clause neg;
	neg.addnode(-u);
	neg.addnode(-tn1);
	output.pi.add_ax(pos);
	output.pi.add_ax(neg);
	output.pi.add_red(cpe + 1, n + 1);
	output.pi.add_red(cpe + 2, n + 1);
	output.pi.add_res(cpe, cpe+3, tn0);
	output.pi.add_res(cpe+5, cpe + 4, -tn1);

	output.Phi.matrix.mvar= 5*n;

	output.ExpPhi = ExpansionClauses(output.Phi.prefix, output.pi, output.index);
	return output;
}

ClausalProof q_uniform_proof (QCNF qf, int n) {
	int universal_variable = n + 1;
	int last_tseitin = qf.matrix.mvar;
	int first_tseitin = n+2;
	int double_tseitin = last_tseitin - universal_variable;
	int single_tseitin = double_tseitin / 2;

	int zeroeth_s = n + 1;
	int first_s = first_tseitin;
	int last_s = universal_variable + single_tseitin;

	int zeroeth_t = last_s;
	int first_t = first_tseitin + single_tseitin;
	int last_t = last_tseitin;
	ClausalProof pi;
	//unfinished
	return pi;

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