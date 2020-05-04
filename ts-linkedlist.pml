/*
This is a comment
*/


#define N 160
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

int critical_val = MAX_VAL // Tracks whether the invariants continue to hold. critical_val must be > 0 at all times

inline initialize() {

	HEAD = MIN_INDEX + 1
	TAIL = MIN_INDEX + 2
	list[HEAD].value = MIN_VAL
	list[HEAD].next = TAIL
	list[TAIL].value = MAX_VAL
	list[TAIL].next = MIN_INDEX
	printf("\nCritical Value: %d", critical_val)
	
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
					// Check if this number is same as next, should never happen
					assert(list[i].value != list[next].value)
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

inline print_memory() {
	i = HEAD;
	printf("\nStart Memory print\n")
	for (i : HEAD .. EMPTY) {
		printf("\nLocation: %d, Value: %d, Next: %d", i, list[i].value, list[i].next)
	}
	printf("\nEnd Memory print\n")
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
					printf("\n(%d)Current: (%d, %d, %d), Next: (%d, %d, %d)\n", _pid, i, list[i].value, list[i].next, next, list[next].value, list[next].next)

				:: else
					printf("\n(%d)Current: Head Node, Next: (%d, %d, %d)\n", _pid, next, list[next].value, list[next].next)
			fi

			if 
				:: (list[next].value > val) ->
					/* Get a free node to use for this insertion */
						d_step {
							current = EMPTY;
							EMPTY = EMPTY + 1;
						}
					/* Update the invariant: Assume we are inserting c between a and b. So critical_value will 
						have a factor (b-a) already. We divide by (b-a) and multiply by (c - a) and (b - a) 
						to get the new value of critical_value*/
					d_step {
						printf("(%d)Critical Value (before): %d, a: %d, b: %d,  c:%d", _pid, critical_val, list[i].value, list[next].value, val )
						critical_val = (critical_val/(list[next].value - list[i].value)) * (val - list[i].value) * (list[next].value - val)
						
					}

					/* Insert after the current node */
						list[current].value = val;
						list[current].next = next;
						list[i].next = current;
						break;
				:: (list[next].value == val) -> 
						printf("(%d)Same value found!", _pid)
						break
				:: else
					i = next
			fi;
	od;
	printf("\n(%d)Inserted.\n", _pid)
}

proctype child() {
	int i, j;
	int current;
	int next;
	

	/* print_list () 
	insert ( 3 ) 
	insert ( 4 )
	insert ( 5 )
	*/
	for (j: 1 .. 5) {
		insert ( j )

	}

}

active proctype parent() {
	int i;
	int next;
	pid n;
	n = _nr_pr;

	int x;
	initialize ()

	run child();
	run child();
	(n == _nr_pr);

	print_list ()
	print_memory()
}