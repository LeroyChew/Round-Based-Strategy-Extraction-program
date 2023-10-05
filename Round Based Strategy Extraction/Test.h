#include "Round Based Strategy Extraction.h"

#include "Examples.h"
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
	Cnf G = copy(F);
	Prefix P; P.addvar(1); P.addvar(-2); P.addvar(3);
	QCNF Phi; Phi.matrix = F; Phi.prefix = P;
	ClausalProof pi; pi.add_ax(A1); pi.add_ax(A2); pi.add_ax(A3);
	pi.add_res(0, 1, x);//3
	pi.add_red(3, 2);//4
	pi.add_res(4, 2, t);//5
	//Cnf tstread1 = read_dimacs("input.txt");
	Cnf tstread2 = read_dimacs("testdimacs.txt");
	//QCNF tstread3 = read_qdimacs("testdimacs.txt");
	//testread("qdimacs.txt");
	//tstread3.matrix.display();
	const char* testfilename = "qdimacstest.qcnf";

	if (remove(testfilename) != 0)
	{
		printf("No file to replace creating new %s file\n", testfilename);
	}
	
	FILE* qdm = fopen(testfilename, "w");
	F.print_preamble(qdm);
	P.print(qdm);
	fprintf(qdm, "\n");
	F.print(qdm);
	QCNF testqbf = QParity(5);
	const char* testfilename2 = "qparitytest.qcnf";
	/*if (remove(testfilename2) != 0)
	{
		printf("No file to replace creating new %s file\n", testfilename);
	}
	fclose(qdm);
	
	FILE* qpar = fopen(testfilename2, "w+");
	testqbf.print(qpar);
	fclose(qpar);
	*/
	//FILE* testfile = fopen(testfilename2, "w+");
	FILE* testfile = fopen(testfilename2, "r");
	QCNF tstread4 = read_qdimacs(testfile);
	fclose(testfile);
	//tstread4.matrix.display();
	
	
	ClausalProof testproof = lqrcQParity(5);
	//FILE* qrcprooffile = fopen("prooftest.qrc", "w+");
	//print_qrc(qrcprooffile, testqbf, testproof);
	//fclose(qrcprooffile);

	FILE* qrcprooffile2 = fopen("prooftest.qrc", "r");
	ClausalProof testproofagain= read_qrc(qrcprooffile2);
	testproofagain.display();
	fclose(qrcprooffile2);

	D_Scheme testdscheme = calculate_Drrs(Phi);
	propagation(F);

	idx::Strategy_Extractor* SE = idx::Extract(&testqbf, &testproof);
	idx::all_equivalence_by_distance(SE);
	if (remove("QRATtest.qrat") != 0) {
		printf("No file to replace creating new %s file\n", "QRATtest.qrat");
	}
	else {
		puts("File succesfully deleted");
	}

	if (remove("QRATtest.cnf") != 0) {
		printf("No file to replace creating new %s file\n", "QRATtest.cnf");
	}
	else {
		puts("File succesfully deleted");
	}

	FILE* test_output = fopen("QRATtest.qrat", "w");
	SE->output_QRAT->print(test_output);
	fclose(test_output);
	FILE* test_outputcnf = fopen("QRATtest.cnf", "w");
	SE->output_cnf->print(test_outputcnf);
	fclose(test_outputcnf);
	

	idx::Index testIndex =idx::Index(Phi, &pi);
	
	

	if (0) {
		//SE->main_index->display(testqbf.prefix);
	}
	else {
		if (level < 2) {
			testIndex.idx_prefix->display(); endline;
			//tstread1.display();
			tstread2.display();
		}
		if (level < 4) {
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
		if (level < 6) {
			testIndex.display(P);
			cout << endl;
			testdscheme.display();
			//SE->output_QRAT->full_check();

		}
		if (level < 5) {
			cout << endl;
			SE->output_cnf->display();
			
			//SE->output_QRAT->display();
		}
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