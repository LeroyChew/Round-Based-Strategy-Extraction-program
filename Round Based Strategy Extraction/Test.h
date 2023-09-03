#include "Round Based Strategy Extraction.h"
using namespace std;

#define endline cout<<endl;
void testproof(int level) {
	Lit x = Lit(1);
	Lit u = Lit(2);
	Lit t = Lit(3);
	Clause A1; A1.addnode(-x); A1.addnode(-u); A1.addnode(-t);
	Clause A2; A2.addnode(x); A2.addnode(u); A2.addnode(-t);
	Clause A3; A3.addnode(t);
	Cnf F; F.addnode(A1); F.addnode(A2); F.addnode(A3);
	Prefix P; P.addvar(1); P.addvar(-2); P.addvar(3);
	QCNF Phi; Phi.matrix = F; Phi.prefix = P;

	ClausalProof pi; pi.add_ax(A1); pi.add_ax(A2); pi.add_ax(A3);
	pi.add_res(0,1,x);
	pi.add_red(2, 2);
	pi.add_res(4, 2, t);
	

	idx::Index testIndex =idx::Index(Phi, &pi);
	if (level < 2) {
		testIndex.idx_prefix->display(); endline;
	}
	if (level < 3) {
		P.display(); endline;
		pi.display();
		
		testIndex.display(MEMBERSHIP, 1);
		testIndex.display(TAUTOLOGICAL, 1);
		testIndex.display(SELON, 1);
		testIndex.display(SELVAL, 1);
		testIndex.display(DESCENDANT, 1);
		testIndex.display(ANCESTOR, 1);
		testIndex.display(XANCESTORSELON, 1);
		testIndex.display(XANCESTORSELVAL0, 1);
		testIndex.display(XANCESTORSELVAL1, 1);
		testIndex.display(XANCESTORMEMBERSHIP, 2);
		testIndex.display(STRATEGY, 2);
		
	}
	if (level < 4) {
		testIndex.display(P);
	}
}

void testbed(int  display) {
	Lit tl1 = Lit(-1);
	Lit tl2 = Lit(1);
	Lit tl3 = Lit(2);
	Lit tl4 = Lit(-3);
	Clause tc1 = Clause();
	tc1.addnode(tl1);
	tc1.addnode(tl3);
	tc1.addnode(tl4);
	Clause tc2 = Clause();
	tc2.addnode(tl4);
	tc2.addnode(tl4);
	tc2.addnode(tl3);
	tc2.addnode(tl2);
	tc2.addnode(tl4);
	tc2.sortlist();
	tc2.norepeats();
	Clause tc3 = resolve(tc1, tc2, 1);
	ClausalProof pi;
	pi.addline(tc1);
	pi.addline(tc2);
	Line<Clause> tline1 = pi[1];
	Var x;
	Var y;
	x = 4;
	y = 3;
	Prefix* P = new Prefix();
	cout << "pre increment" << x << " " << y << endl;
	idx::increment(&x, P, &y);
	cout << "post increment" << x << " " << y << endl;
	if (display < 1) {
		

		tl1.display(); endline;
		tl2.display(); endline;
		tl3.display(); endline;
		tl4.display(); endline;
	}
	if (display < 2) {
		tc1.display(); endline;
		tc2.display(); endline;
		tc3.display(); endline;
		cout<< tc1.max_var(); endline;
	}
	if (display < 3) {
		pi.display();
		tline1.clause[2].display(); endline;
		cout<< tline1.clause.findnode(2)->position; endline;
		
	}
}