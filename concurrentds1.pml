/*
This is a comment
*/


#define N 16
#define MIN_VAL 0 /* No data will have value lower than or equal to this value */
#define MAX_VAL 255 /* No data will have value higher than or equal to this value */
#define MIN_INDEX 0 /* No element of the list will have a next index less than or equal to this value */
#define MAX_INDEX N /* No element of the list will have value higher than or equal to this value */

typedef NODE {
	byte value;
	byte next;
}

NODE list[N] /* Declare an array of N elements */

byte HEAD;
byte TAIL;
byte EMPTY = 3; /* assumption is that all positions from this point onwards are available */


inline initialize() {

	HEAD = MIN_INDEX + 1
	TAIL = MIN_INDEX + 2
	list[HEAD].value = MIN_VAL
	list[HEAD].next = TAIL
	list[TAIL].value = MAX_VAL
	list[TAIL].next = MIN_INDEX
	
	}


inline print_list() {
	i = HEAD;

	printf("\nBegin List\n")
	do
		:: true ->
			next = list[i].next
			if 
				:: (i != HEAD) -> 
					printf("\n--(%d, %d, %d)\n", i, list[i].value, list[i].next)
				:: else
					printf("\n--Head Node\n")
			fi

			if 
				:: (next == TAIL) -> 
					break;
				:: else
					i = next
			fi
	od;
	printf("\nEnd List\n")
}


inline insert(val) {
	/* Keep traversing. when the next item has a value higher than what we want to insert, we insert there */
	i = HEAD;

	printf("\nTo insert: %d\n", val)
	do
		:: true ->
			next = list[i].next
			if 
				:: (i != HEAD) -> 
					printf("\nCurrent: (%d, %d, %d)", i, list[i].value, list[i].next)
					printf(" Next: (%d, %d, %d)\n", next, list[next].value, list[next].next)
				:: else
					printf("\nCurrent: Head Node")
					printf(" Next: (%d, %d, %d)\n", next, list[next].value, list[next].next)
			fi

			if 
				:: (list[next].value >= val) ->
					/* Get a free node to use for this insertion */
						d_step {
							current = EMPTY;
							EMPTY = EMPTY + 1;
						}
					/* Insert after the current node */
						list[current].value = val;
						list[current].next = next;
						list[i].next = current;
						break;
				:: (list[next].value == val) -> 
						printf("Same value found!")
						break
				:: else
					i = next
			fi;
	od;
	printf("\nInserted.\n")
}

proctype child() {
	int i;
	int current;
	int next;

	/* print_list () */
	insert ( 3 ) 
	insert ( 4 )
	insert ( 5 )

}

active proctype parent() {
	int i;
	int next;
	pid n;
	n = _nr_pr;

	initialize ()

	run child();
	run child();
	(n == _nr_pr);

	print_list ()
}