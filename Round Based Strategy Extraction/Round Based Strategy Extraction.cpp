// Round Based Strategy Extraction.cpp : Defines the entry point for the application.
//

#include "Round Based Strategy Extraction.h"

#include "Test.h"
#include <ctime>        // std::time

using namespace std;



void pseudomain(int argc, char** argv ) {
	bool file_writing = 0;
	bool file_reading = 1;
	char* outputname= NULL;
	char* qdimacsname = NULL;
	char* qrcname = NULL;
	double duration;
	std::clock_t start;
	if (argc > 1) {
		if (argv[1][0] == '-') { printf("c first parameter needs to be qdimacs file name\n"); return; }
		qdimacsname = argv[1];
	}
	if (argc > 2) {
		if (argv[1][0] == '-') { printf("c second parameter needs to be qdimacs file name\n"); return; }
		qdimacsname = argv[1];
	}
	else {
		printf("Not enough arguments, defaulting to example mode: QPARITY(100)");
		file_reading = 0;
	}
	
	for (int i = 1; i < argc; i++) {
		if (argv[i][0] == '-') {
			if (argv[i][1] == 'o') {
				file_writing = 1;
				if (argc == i + 1) {
					printf("c file name missing after -o\n");
					return;
					//strcat(fname, to_cstr(std::move(ss).str()));
				}
				else {
					outputname = argv[i + 1];
				}
			}
		}
	}
	Cnf* output;
	QCNF formula;
	ClausalProof proof;

	if (file_reading) {

		FILE* qdimacs = fopen(qdimacsname, "r");
		formula = read_qdimacs(qdimacs);
		fclose(qdimacs);

		FILE* qrc = fopen(qrcname, "r");
		proof = read_qrc(qrc);
		fclose(qrc);
	}
		
	else{
		formula = QParity(100);
		proof = lqrcQParity(100);

		if (file_writing) {
			const char* default_qdimacs = "formula.qdimacs";
			const char* default_qrc = "proof.qrc";
			if (remove(default_qdimacs) != 0)
			{
				printf("No file to replace creating new %s file\n", default_qdimacs);
			}
			if (remove(default_qrc) != 0)
			{
				printf("No file to replace creating new %s file\n", default_qrc);
			}

			FILE* qdimacsfile = fopen(default_qdimacs, "w+");
			formula.print(qdimacsfile);
			fclose(qdimacsfile);

			FILE* qrcfile = fopen(default_qrc, "w+");
			print_qrc(qrcfile, formula, proof);
			fclose(qrcfile);
		}
	}

	start = std::clock();
	multilinear::Strategy_Extractor* ClausalExtractor = multilinear::Extract(&formula, &proof, proof.length-1, 1);
	*(ClausalExtractor->output_cnf) = ccopy(formula.matrix);
	copyinto((ClausalExtractor->output_cnf), (ClausalExtractor->extension_clauses));
	copyinto((ClausalExtractor->output_cnf), (ClausalExtractor->negated_assumptions));
	ClausalExtractor->output_cnf->update_max_var();
	output = ClausalExtractor->output_cnf;
	duration = (std::clock() - start) / (double)CLOCKS_PER_SEC;
		
	if (file_writing) {
		FILE* cnffile = fopen(outputname, "w+");
		output->print_dimacs(cnffile);
		fclose(cnffile);
	}
	else {//comment out for release
		std::cout << endl << "DEBUG TOOL: printing to output.cnf, DISABLE on release"<< endl;
		FILE* cnffile = fopen("output.cnf", "w+");
		output->print_dimacs(cnffile);
		fclose(cnffile);
	}
	std::cout << endl<< "time for constructing CNF " << duration << endl;
	std::cout << endl << "number of new variables " << output->calculate_max_var() -formula.matrix.mvar << endl;
}

int main(int argc, char** argv)
{
	//whilemultitest(5);
	//exprestest(5);
	circuittest(0);
	//pseudomain(argc, argv);
	//cout << "Hello CMake." << endl;
	//testmultilinear(5);
	return 0;
}