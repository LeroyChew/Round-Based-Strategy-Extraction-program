#pragma once
#include "QRAT.h"
#include <string.h>
#include <fstream>
//#include <stdlib.h>
//#include <stdio.h>
//#include <zlib.h>
#include<string>

void testread(const char* filename ) {
	fstream newfile;
	newfile.open(filename, ios::out);  // open a file to perform write operation using file object
	if (newfile.is_open()) //checking whether the file is open 
	{
		newfile << "Tutorials point \n"; //inserting text
	newfile.close(); //close the file object
	}
	newfile.open(filename, ios::in); //open a file to perform read operation using file object
	if (newfile.is_open()) { //checking whether the file is open
		string tp;
		while (std::getline(newfile, tp)) 
		{ //read data from file object and put it into string.
			cout << tp << "\n"; //print the data of the string
		}
	newfile.close(); //close the file object.
	}
}

/*
static const int buffer_size = 1048576;


class StreamBuffer {
	//gzFile        in;
	FILE in;
	unsigned char buf[buffer_size];
	int           pos;
	int           size;

	void assureLookahead() {
		if (pos >= size) {
			pos = 0;
			fopen(in);
			//size = gzread(in, buf, sizeof(buf));
		}
	}

public:
	explicit StreamBuffer(FILE i) : in(i), pos(0), size(0) { assureLookahead(); }

	int  operator *  () const { return (pos >= size) ? EOF : buf[pos]; }
	void operator ++ () { pos++; assureLookahead(); }
	int  position() const { return pos; }
};

static inline bool isEof(StreamBuffer& in) { return *in == EOF; }
static inline bool isEof(const char* in) { return *in == '\0'; }

static void skipWhitespace(StreamBuffer in) {
	while ((*in >= 9 && *in <= 13) || *in == 32)
		++in;
}

static void skipWhitespace(fstream in) {
	while ((*in >= 9 && *in <= 13) || *in == 32)
		in.right;
}

static void skipLine(StreamBuffer in) {
	for (;;) {
		if (isEof(in)) return;
		if (*in == '\n') { ++in; return; }
		++in;
	}
}


static bool eagerMatch(StreamBuffer in, const char* str) {
	for (; *str != '\0'; ++str, ++in)
		if (*str != *in)
			return false;
	return true;
}


static int parseInt(StreamBuffer in) {
	int     val = 0;
	bool    neg = false;
	skipWhitespace(in);
	if (*in == '-') neg = true, ++in;
	else if (*in == '+') ++in;
	if (*in < '0' || *in > '9') fprintf(stderr, "PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
	while (*in >= '0' && *in <= '9')
		val = val * 10 + (*in - '0'),
		++in;
	return neg ? -val : val;
}


static void readClause(StreamBuffer in, Cnf S, Clause lits) {
	int     parsed_lit, var;
	lits.clear();
	for (;;) {
		parsed_lit = parseInt(in);
		Lit l = Lit(parsed_lit);
		if (parsed_lit == 0) break;
		var = l.var;
		//while (var >= S.nVars()) S.newVar();
		lits.addnode(l);
	}
}


static void parse_DIMACS_main(StreamBuffer in, Cnf S) {
	Clause lits;
	int vars = 0;
	int clauses = 0;
	int cnt = 0;
	for (;;) {
		skipWhitespace(in);
		if (*in == EOF) break;
		else if (*in == 'p') {
			if (eagerMatch(in, "p cnf")) {
				vars = parseInt(in);
				clauses = parseInt(in);
				// SATRACE'06 hack
				// if (clauses > 4000000)
				//     S.eliminate(true);
			}
			else {
				printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
			}
		}
		else if (*in == 'c' || *in == 'p')
			skipLine(in);
		else {
			cnt++;
			readClause(in, S, lits);
			S.addnode(lits);
		}
	}
	//if (vars != S.nVars())
	//	fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of variables.\n");
	//if (cnt != clauses)
	//	fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of clauses.\n");
}
*/



Cnf read_dimacs(const char* cnfname) {//broken
	std:ifstream myfile(cnfname, std::ios_base::in);
	int read_int;
	wchar_t read_char;

	int max_var;
	int max_clauses;

	int preamble_end_int;
	streampos preamble_end;
	Cnf output;
	Clause temp;
	//while (myfile >> read_char) {
	//if (read_char == 'p') {
	myfile >> max_var;
	myfile >> max_clauses;
	//		break;
	//	}
	//}
	//myfile.seekg(preamble_end);
	//myfile= ifstream(cnfname, std::ios_base::in);
	while (myfile >> read_int) {
			if (read_int == 0) {
				output.addnode(temp);
				temp = Clause();
			}
			else {
				temp.addnode(Lit(read_int));
			}
	}
	return output;
}
ClausalProof read_qrc(FILE* file){
	char p_label[10], cnf_label[10];
	int max_var, max_clauses;
	ClausalProof output = ClausalProof();
	rewind(file);
	fscanf(file, "%s %s %d %d", p_label, cnf_label, &max_var, &max_clauses);
	char* ch;
	char str[10];
	int block_counter = 0;
	int v = -1;
	while (fscanf(file, "%s", str) != EOF) {

		//*ch = str[0];
		if (str[0] == 101) {//e
			fscanf(file, "%d", &v);
			while (v != 0) {
				//output.prefix.addnode(Quantifier(v));
				fscanf(file, "%d", &v);

			}
			block_counter++;
		}
		if (str[0] == 97) {//a
			fscanf(file, "%d", &v);
			while (v != 0) {
				//output.prefix.addnode(Quantifier(-v));
				fscanf(file, "%d", &v);

			}
			block_counter++;
		}
	}
	rewind(file);
	int i = 0;
	while (i < block_counter) {
		fscanf(file, "%s", str);
		if (str[0] == '0') {
			i++;
		}
	}
	fscanf(file, "%s", str);
	Line<Clause> temp= Line<Clause>();
	while (fscanf(file, "%s", str) != EOF) {
		v = atoi(str);
		if (v == 0) {
			output.addnode(temp);
			temp = Line<Clause>();
			fscanf(file, "%s", str);
			v = atoi(str);
			int parent_no = 0;
			while (v != 0 && parent_no<2) {
				if (parent_no == 0) {
					temp.parent0 = v - 1;
				}
				if (parent_no == 1) {
					temp.parent0 = v - 1;
				}
				parent_no++;
				fscanf(file, "%s", str);
				v = atoi(str);
			}
			fscanf(file, "%s", str);
		}
		else {
			temp.clause.addnode(Lit(v));
		}

	}
	return output;
}

QCNF read_qdimacs(FILE* file) {
	char p_label[10], cnf_label[10];
	int max_var, max_clauses;
	QCNF output = QCNF();
	rewind(file);
	fscanf(file, "%s %s %d %d", p_label, cnf_label, &max_var, &max_clauses);
	//cout << p_label << " " << cnf_label << " " << max_var << " " << max_clauses << endl;
	char *ch;
	char str[10];
	int block_counter = 0;
	int v = -1;
	while (fscanf(file, "%s", str) != EOF) {
		
		//*ch = str[0];
		if (str[0] == 101) {//e
			fscanf(file, "%d", &v);
			while (v!=0) {
				output.prefix.addnode(Quantifier(v));
				fscanf(file, "%d", &v);
				
			}
			block_counter++;
		}
		if (str[0] == 97) {//a
			fscanf(file, "%d", &v);
			while (v != 0) {
				output.prefix.addnode(Quantifier(-v));
				fscanf(file, "%d", &v);
				
			}
			block_counter++;
		}
	}
	rewind(file);
	int i = 0;
	while (i< block_counter) {
		fscanf(file, "%s", str);
		if (str[0] == '0') {
			i++;
		}
	}
	Clause temp = Clause();
	while (fscanf(file, "%s", str) != EOF) {
		v = atoi(str);
		if (v == 0) {
			output.matrix.addnode(temp);
			temp = Clause();
		}
		else {
			temp.addnode(Lit(v));
		}

	}
	
	return output;
}

/*QCNF read_qdimacs(const char* qcnfname) {
	std:ifstream myfile(qcnfname, std::ios_base::in);
	//loop to count all a's
	//loop to count all e's
	//myfile.open(qcnfname, std::ios_base::in);
	int max_var;
	int max_clauses;
	//myfile >> max_var;
	//myfile >> max_clauses;


	int a_counter=0;
	int e_counter = 0;
	bool first_found = 0;
	bool e_first=1;
	wchar_t read_char;

	while (myfile >> read_char) {
		if (read_char == "e") {
			e_counter++;
			if (!first_found) {
				first_found = 1;
			}
		}
		if (read_char == "a") {
			a_counter++;
			if (!first_found) {
				first_found = 1;
				e_first = 0;
			}
		}
	}

	int read_int;
	myfile = ifstream(qcnfname, std::ios_base::in);
	int i=0;
	QCNF output;
	Clause temp;
	while ( myfile >> read_int) {
		if (i < a_counter + e_counter) {
			if (read_int == 0) {
				i++;
				e_first = !e_first;

			}
			else {
				if (e_first) {
					output.prefix.addnode(Quantifier(read_int));
				}
				else {
					output.prefix.addnode(Quantifier(-read_int));
				}
			}
		}
		else {
			if (read_int == 0) {
				output.matrix.addnode(temp);
				temp = Clause();
			}
			else {
				temp.addnode(Lit(read_int));
			}
		}

	}
	return output;
}
*/

ClausalProof read_no_anno(const char* prooffilenname){
	std:fstream myfile(prooffilenname, std::ios_base::in);
	int a;
	int i = 0;
	Clause temp;
	ClausalProof output;
	D_Scheme trivial_scheme;
	while (myfile >> a) {
		if (a == 0) {
			output.addclause_scheme(temp, trivial_scheme );
			temp = Clause();
		}
		else {
			temp.addnode(Lit(a));
			
		}
		i++;
	}
	return output;
}