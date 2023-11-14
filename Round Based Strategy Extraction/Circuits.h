#pragma once
#include <iostream>
#include "Linked List.h"
#include "Logic.h"
namespace ccircuits {
	struct Gate {
		int label;//the positive integer for the new variable taht outputs from the gate
		int fanin;
		int symbol; //0 for false, 1 for true 2 for NOT, 3 for AND, 4 for OR
		LinkL<int> input;//Linked List with the positive input integers

		Gate() {
			label = 1;
			symbol = 0;
			fanin = 0;
			input = LinkL<int>();
		}

		Gate(int l, int s) {
			label = l;
			symbol = s;
			fanin = 0;
			input = LinkL<int>();
		}

		Gate(int l, int s, int n) {
			label = l;
			symbol = s;
			fanin = n;
			input = LinkL<int>();
			for (int i = 0; i < n; i++) {
				input.addnode(-(i + 1));
			}
		}

		void add_input(int x) {
			input.addnode(x);
			fanin++;
		}

		bool compute(LinkL<bool> vec) const {
			if (symbol == 0) {
				return 0;
			}

			if (symbol == 1) {
				return 1;
			}

			if (symbol == 2) {
				return !(vec.head->data);
			}
			if (symbol == 3) {
				bool bool_output = 1;
				Link1<bool>* current = vec.head;
				while (current != NULL) {
					bool_output = (bool_output) && (current->data);
					current = current->next;
				}
				return bool_output;
			}
			if (symbol == 4) {
				bool bool_output = 0;
				Link1<bool>* current = vec.head;
				while (current != NULL) {
					bool_output = (bool_output) || (current->data);
					current = current->next;
				}
				return bool_output;
			}
		}

		bool compute(LinkL<int> vec) const {
			LinkL<bool> bool_vec;
			LinkL<bool> is_assigned;
			while (bool_vec.length < input.length) {
				bool_vec.addnode(0);// assumes empty information is negative
				is_assigned.addnode(0);
			}
			Link1<int>* current = vec.head; //go through each vec
			while (current != NULL) {
				int inp_label = abs(current->data);
				int idx = -1;
				bool is_in_input_list = 0;
				Link1<int>* current_inp = input.head;
				while (current_inp != NULL) {
					if (current_inp->data == inp_label) {
						is_in_input_list = 1;
						is_assigned.findnode(current_inp->position)->data = 1;
						idx = current_inp->position;//we found the position of input that matches with each vec
					}
					current_inp = current_inp->next;
				}

				if (is_in_input_list) {
					Link1<bool>* edit_pos = bool_vec.findnode(idx);
					if (current->data > 0) {
						edit_pos->data = (bool)1;
					}
					else {
						edit_pos->data = (bool)0;
					}
				}
				current = current->next;
			}
			Link1<bool>* current_bool = is_assigned.head;
			while (current_bool != NULL) {
				if (current_bool->data== 0) {
					int inp_val = input[current_bool->position];
					std::cout << "warning: undefined " << inp_val << " for " <<  symbol << " gate " <<  label << endl;
				}
				current_bool = current_bool->next;
			}
			return compute(bool_vec);
		}
		int int_compute(LinkL<bool> vec) const {
			bool b = compute(vec);
			if (b) {
				return label;
			}
			else {
				return -label;
			}
		}

		int int_compute(LinkL<int> vec) const {
			bool b = compute(vec);
			if (b) {
				return label;
			}
			else {
				return -label;
			}
		}
	};

	Cnf extclauses(Gate g) {
		Cnf output;
		Clause longclause;
		if (g.symbol == 0) {
			longclause.addnode(-Lit(g.label));
		}
		if (g.symbol == 1) {
			longclause.addnode(Lit(g.label));
		}
		if (g.symbol == 2) {
			longclause.addnode(-Lit(g.label));
		}
		if (g.symbol == 3) {
			longclause.addnode(Lit(g.label));
		}
		if (g.symbol == 4) {
			longclause.addnode(-Lit(g.label));
		}

		Link1<int>* current= g.input.head;
		while (current != NULL) {
			Clause shortclause;
			if ((g.symbol == 2) && (current->position == 0)) {
				longclause.addnode(-Lit(current->data));
				shortclause.addnode(Lit(g.label));
				shortclause.addnode(Lit(current->data));
				output.addnode(shortclause);
			}
			if (g.symbol == 3) {
				longclause.addnode(-Lit(current->data));
				shortclause.addnode(-Lit(g.label));
				shortclause.addnode(Lit(current->data));
				output.addnode(shortclause);
			}
			if (g.symbol == 4) {
				longclause.addnode(Lit(current->data));
				shortclause.addnode(Lit(g.label));
				shortclause.addnode(-Lit(current->data));
				output.addnode(shortclause);
			}
			current = current->next;
		}
		output.addnode(longclause);
		return output;
	}

	struct Circuit {
		LinkL<Gate> list;
		int max_gate;

		void print(FILE* file) {
			fprintf(file, "aag ");
			fprintf(file, "%i", max_gate);//M
			//I don't understand the AIGER format
		}

		LinkL<int> compute(LinkL<int> input) {
			LinkL<int>* linput = new LinkL<int>;
			input.copy(linput);
			Link1<Gate>* current = list.head;
			while (current != NULL) {
				int new_data = current->data.int_compute(*linput);
				if (0) {
					cout << new_data << "=" << current->data.symbol << ":";
					Link1<int>* cinp = current->data.input.head;
					while (cinp != NULL) {
						//search for linput
						Link1<int>* clinp = linput->head;
						while (clinp != NULL) {
							if (abs(clinp->data) == cinp->data) {
								cout << " " << clinp->data;
							}
							clinp = clinp->next;
						}
						cinp = cinp->next;
					}
					cout << endl;
				}
				linput->addnode(new_data);
				current = current->next;
			}
			return *linput;
		}

		int int_compute(LinkL<int> input) {
			return compute(input).tail->data;
		}

		int compute(LinkL<int> input, int idx) {
			return compute(input)[idx];
		}

		bool bool_compute(LinkL<int> input) {
			int i = int_compute(input);
			if (i > 0) {
				return 1;
			}
			else
			{
				return 0;
			}
		}

		Circuit() {
			max_gate = 0;
			list = LinkL<Gate>();
		}
		Circuit(int no_of_inputs) {
			max_gate = no_of_inputs;
			list = LinkL<Gate>();
		}

		void addNOT(int input_gate) {
			max_gate++;
			Gate temp = Gate(max_gate, 2);
			temp.add_input(input_gate);
			list.addnode(temp);
		}

		void def0(int name) {
			if (name > max_gate) {
				max_gate = name;
			}
			Gate temp = Gate(name, 0);
			list.addnode(temp);
		}

		void def1(int name) {
			if (name > max_gate) {
				max_gate = name;
			}
			Gate temp = Gate(name, 1);
			list.addnode(temp);
		}

		void defNOT(int name, int input_gate) {
			if (name > max_gate) {
				max_gate = name;
			}
			Gate temp = Gate(name, 2);
			temp.add_input(input_gate);
			list.addnode(temp);
		}

		void defequiv(int name, int input_gate) {
			if (name > max_gate) {
				max_gate = name;
			}
			Gate temp = Gate(name, 4);
			temp.add_input(input_gate);
			list.addnode(temp);
		}

		void addAND(LinkL<int> input_gates) {
			max_gate++;
			Gate temp = Gate(max_gate, 3);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
		}

		void defAND(int name, LinkL<int> input_gates) {
			if (name > max_gate) {
				max_gate = name;
			}
			Gate temp = Gate(name, 3);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
		}

		void addAND(int x, int y) {
			max_gate++;
			Gate temp = Gate(max_gate, 3);
			LinkL<int> input_gates = LinkL<int>();
			input_gates.addnode(x);
			input_gates.addnode(y);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
			input_gates.rmvnode(input_gates.tail);
			input_gates.rmvnode(input_gates.tail);
		}

		void defAND(int name, int x, int y) {
			if (name > max_gate) {
				max_gate = name;
			}
			Gate temp = Gate(name, 3);
			LinkL<int> input_gates = LinkL<int>();
			input_gates.addnode(x);
			input_gates.addnode(y);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
		}
		void addOR(LinkL<int> input_gates) {
			max_gate++;
			Gate temp = Gate(max_gate, 4);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);

		}

		void defOR(int name, LinkL<int> input_gates) {
			if (name > max_gate) {
				max_gate = name;
			}
			Gate temp = Gate(name, 4);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
		}


		void addOR(int x, int y) {
			max_gate++;
			Gate temp = Gate(max_gate, 4);
			LinkL<int> input_gates = LinkL<int>();
			input_gates.addnode(x);
			input_gates.addnode(y);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
			input_gates.rmvnode(input_gates.tail);
			input_gates.rmvnode(input_gates.tail);
		}

		void defOR(int name, int x, int y) {
			if (name > max_gate) {
				max_gate = name;
			}
			Gate temp = Gate(name, 4);
			LinkL<int> input_gates = LinkL<int>();
			input_gates.addnode(x);
			input_gates.addnode(y);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
		}
		void addXOR(LinkL<int> input_gates) {
			max_gate++;
			Gate temp = Gate(max_gate, 5);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
		}
		void defXOR(int name, LinkL<int> input_gates) {
			if (name > max_gate) {
				max_gate = name;
			}
			Gate temp = Gate(name, 5);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
		}

		void addXOR(int x, int y) {
			max_gate++;
			Gate temp = Gate(max_gate, 5);
			LinkL<int> input_gates = LinkL<int>();
			input_gates.addnode(x);
			input_gates.addnode(y);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
			input_gates.rmvnode(input_gates.tail);
			input_gates.rmvnode(input_gates.tail);
		}
		void defXOR(int name, int x, int y) {
			if (name > max_gate) {
				max_gate = name;
			}
			Gate temp = Gate(name, 5);
			LinkL<int> input_gates = LinkL<int>();
			input_gates.addnode(x);
			input_gates.addnode(y);
			Link1<int>* current = input_gates.head;
			while (current != NULL) {
				temp.add_input(abs(current->data));
				current = current->next;
			}
			list.addnode(temp);
		}

		void addcircuit(Circuit c) {
			if (max_gate < c.max_gate) {
				max_gate = c.max_gate;
			}
			Link1<Gate>* current = c.list.head;
			while (current != NULL) {
				list.addnode(current->data);
				current = current->next;
			}
		}
	};

	Cnf extclauses(Circuit C) {
		Link1<Gate>* current = C.list.head;
		Cnf output;
		while (current != NULL) {
			Gate g = current->data;
			Cnf f = extclauses(g);
			copyinto(&output, &f);
			current = current->next;
		}
		return output;
	}

	bool nonoverlapping(Circuit x, Circuit y) {
		Link1<Gate>* current1 = x.list.head;
		while (current1 != NULL) {
			Link1<Gate>* current2 = y.list.head;
			while (current2 != NULL) {
				if (current1->data.label==current2->data.label) {
					return 0;
				}

				current2 = current2->next;
			}
			current1 = current1->next;
		}
		return 1;
	}
}