#pragma once
template <typename T> struct Link1{// 1 dimensional linked list element
public:
	T data;
	int position;
	Link1<T>* next;
	Link1<T>* prev;

	Link1<T>() {
		data = T();
		next = NULL;
		prev = NULL;
		position = 0;
	}
	Link1<T>(T input) {
		data = input;
		next = NULL;
		prev = NULL;
		position = 0;
	}
};



template <typename T> struct LinkL {
	Link1<T>* head;
	Link1<T>* tail;
	int length;

	LinkL() {
		head = NULL;
		tail = NULL;
		length = 0;
	}

	void addnode(T end_element) {
		Link1 <T> *temp= new Link1 <T>;
		temp->data = end_element;
		temp->position = length;
		if (head == NULL) {
			head = temp;
		}
		else {
			tail->next = temp;
			
		}
		temp->prev = tail;
		tail = temp;
		length++;
	}

	void rmvnode(Link1 <T>* rmvable) {
		if (rmvable == NULL) {
			return;
		}
		else {
			
			Link1 <T>* back = rmvable->prev;
			Link1 <T>* forward = rmvable->next;
			if (back == NULL) {
				head = forward;
			}
			else {
				back->next = forward;
			}
			if (forward == NULL) {
				tail = back;
			}
			else {
				forward->prev = back;
				Link1 <T>* current = forward;
				while (current != NULL) {
					current->position--;
					current = current->next;
				}
			}
			length--;
			delete rmvable;
		}
	}

	Link1 <T>* findnode(int idx) {
		Link1 <T>* current = head;
		 while(current!=NULL) {
			if (idx == 0) {
				 return current;
			}
			current = current->next;
			idx--;
		}
	}

	T operator [](int idx) {
		return findnode(idx)->data;
	}
};

template <typename T> struct Link2 {// 2 dimensional linked array element
	T data;
	int position1;
	Link2<T>* next1;
	Link2<T>* prev1;
	int position2;
	Link2<T>* next2;
	Link2<T>* prev2;

	Link2<T>() {
		data = T();
		next1 = NULL;
		prev1 = NULL;
		position1 = 0;
		next2 = NULL;
		prev2 = NULL;
		position2 = 0;
	}
};

template<typename T> struct Link2R {//2 dimensional linked array row
	int length;
	int position1;
	Link2R<T>* next1;
	Link2R<T>* prev1;
	Link2<T>* head;
	Link2<T>* tail;
};

template<typename T> LinkL<T> copy(LinkL<T> input) {
	LinkL<T> output;
	Link1<T>* current = input.head;
	while (current != NULL) {
		output.addnode(current->data);
		current = current->next;
	}
	return output;
}
