#include "Round Based Strategy Extraction.h"

#include "Examples.h"
using namespace std;
using namespace ccircuits;
#define endline cout<<endl;

void circuit_truth_table(Circuit C, LinkL<int>* assignment, int n ) {
	if (n == 0) {
		int answer= C.int_compute(*assignment);
		Link1<int>* current = assignment->head;
		while (current != NULL) {
			cout << current->data << " ";
			current = current->next;
		}
		cout << answer << endl;
	}
	else {
		LinkL<int>* ass0 = new LinkL<int>;
		assignment->copy(ass0);
		ass0->addnode(-n);
		circuit_truth_table(C, ass0, n - 1);

		LinkL<int>* ass1 = new LinkL<int>;
		assignment->copy(ass1);
		ass1->addnode(n);
		circuit_truth_table(C, ass1, n - 1);
	}
}


void circuittest(int level) {
	/*
	Circuit tcirc = Circuit(10);
	tcirc.addAND(1, 2);//11
	tcirc.addXOR(2, 5);//12
	tcirc.addNOT(4);//13
	tcirc.addXOR(3, 6);//14
	tcirc.addOR(5, 7);//15
	LinkL<int> triple; triple.addnode(8); triple.addnode(9); triple.addnode(10); tcirc.addOR(triple);//16
	tcirc.addXOR(12, 13);//17
	tcirc.addXOR(13, 14);//18
	tcirc.addAND(15, 16);//19
	tcirc.addAND(11, 17); //20
	tcirc.addAND(17, 18); //21
	tcirc.addOR(21, 19);//22
	tcirc.addAND(20, 22);
	LinkL<int> full_input;
	full_input.addnode(1);
	full_input.addnode(2);
	full_input.addnode(3);
	full_input.addnode(4);
	full_input.addnode(-5);
	full_input.addnode(-6);
	full_input.addnode(7);
	full_input.addnode(-8);
	full_input.addnode(-9);
	full_input.addnode(10);
	LinkL<int> return_value = tcirc.compute(full_input);
	*/
	QCNF testqbf = QParity(4);
	ClausalProof testproof = lqrcQParity(4);
	circuitmultilinear::Strategy_Extractor* SE = circuitmultilinear::Extract(&testqbf, &testproof, testproof.length - 1, 1);
	if (remove("multilocal.cnf") != 0) {
		printf("No file to replace creating new %s file\n", "QRATtest.qrat");
	}
	FILE* test_output = fopen("multilocal.cnf", "w");
	SE->load_output_cnf_negated();
	SE->output_cnf->print(test_output);
	fclose(test_output);

	if (level < 1) {
		//SE->main_index->tail->data.tail->prev->data.display();
		SE->display_index();
		//circuit_truth_table(SE->output_circuit->head->data, new LinkL<int>, 50);
		LinkL<int> trial_input;
		for (int i = 1; i < 5; i++) {
			trial_input.addnode(i);
		}
		//testproof.display();
		
		//ClausalProof r0proof = circuitmultilinear::restricted_proof(SE, trial_input, 0);
		//r0proof.display();
		
		ClausalProof r1proof= circuitmultilinear::restricted_proof(SE, trial_input, 1);
		r1proof.display();
		
		
		//Link1<int>* current = return_value.head;
		//while (current != NULL) {
		//	cout << current->data << " ";
		//	current = current->next;
		//}
		//cout << endl;
	}
}


void exprestest(int level) {
	ExpResProof eproof = expQParity(4);
	multilinear::Strategy_Extractor* SE = multilinear::Extract(&(eproof.ExpPhi), &(eproof.pi), eproof.pi.length - 1, 1);
	Cnf output;
	output = ccopy(eproof.Phi.matrix);
	Cnf quickdef = QuickDef(eproof.index);
	copyinto(&output, &quickdef);
	copyinto(&output, SE->extension_clauses);
	if (remove("sat.cnf") != 0) {
		printf("No file to replace creating new %s file\n", "sat.cnf");
	}
	FILE* file_output = fopen("sat.cnf", "w");
	output.print(file_output);
	fclose(file_output);

	if (remove("unsat.cnf") != 0) {
		printf("No file to replace creating new %s file\n", "unsat.cnf");
	}
	copyinto(&output, SE->negated_assumptions);
	FILE* file_output2 = fopen("unsat.cnf", "w");
	output.print(file_output2);
	fclose(file_output2);

	eproof.ExpPhi.prefix.display();
	endline
	eproof.ExpPhi.matrix.display();
	endline
	endline
	eproof.pi.display();
	//endline
	//SE->extension_clauses->display();
	endline
	SE->negated_assumptions->display();
	return;
}

void whilemultitest(int level) {
	QCNF testqbf = QParity(50);
	ClausalProof testproof = lqrcQParity(50);
	multilinear::Strategy_Extractor* SE = multilinear::Extract(&testqbf, &testproof, testproof.length-1, 1);
	//multilinear::while_load(SE->output_cnf, SE, testproof.length - 1);
	if (remove("multilocal.cnf") != 0) {
		printf("No file to replace creating new %s file\n", "QRATtest.qrat");
	}
	FILE* test_output = fopen("multilocal.cnf", "w");
	SE->load_output_cnf_negated();
	SE->output_cnf->print(test_output);
	fclose(test_output);
}

void testmultilinear(int level) {
	//generate output
	const char* output_qdimacs = "formulatest.qdimacs";
	const char* output_qrc = "prooftest.qrc";
	
	/*
	if (remove(output_qdimacs) != 0)
	{
		printf("No file to replace creating new %s file\n", output_qdimacs);
	}
	if (remove(output_qrc) != 0)
	{
		printf("No file to replace creating new %s file\n", output_qrc);
	}
	

	QCNF testqbf = QParity(5);
	ClausalProof testproof = lqrcQParity(5);
	

	FILE* qdimacsfile = fopen(output_qdimacs, "w+");
	testqbf.print(qdimacsfile);
	fclose(qdimacsfile);

	FILE* qrcfile = fopen(output_qrc, "w+");
	print_qrc(qrcfile, testqbf, testproof);
	fclose(qrcfile);
	*/

	//calculate input
	const char* input_qdimacs = output_qdimacs;
	const char* input_qrc = output_qrc;
	const char* output_cnf = "output.cnf";
	if (remove(output_cnf) != 0)
	{
		printf("No file to replace creating new %s file\n", output_cnf);
	}

	FILE* cnffile = fopen(output_cnf, "w+");
	Cnf* output = multilinear::StrategyCnf(input_qdimacs, input_qrc);
	output->print_dimacs(cnffile);
	fclose(cnffile);
}

void testproof(int level) {
	Lit x = Lit(1);
	Lit u = Lit(2);
	Lit t = Lit(3);
	Clause A1; A1.addnode(-x); A1.addnode(-u); A1.addnode(-t);
	Clause A2; A2.addnode(x); A2.addnode(u); A2.addnode(-t);
	Clause A3; A3.addnode(t);
	Cnf F; F.addnode(A1); F.addnode(A2); F.addnode(A3);
	Cnf G = ccopy(F);
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