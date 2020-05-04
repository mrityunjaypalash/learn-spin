/* 
	Thoughts on the paper

1. Why does the hub tell the process which node to insert? Ideally, the process
has a node to insert and hub only says go ahead or not, essentially acting 
as a traffic light - stop or go. If the hub could instruct which node to 
insert, there will be no duplication by design and there won't be any contention
I think either.

I am assuming that the hub doesn't control which number is to be inserted, it
just says whether to go ahead or not go ahead. This seems more realistic, and
more interesting problem. 

2. How does this whole thing bootstrap? The hub sends a message to start? 
How does the hub know which processes are connected to it, is there a 
registration process using some well-known channel?

I am assuming that a god controller tells the hub controller about 2 processes
that need to be controlled, and hub controller starts by sending a (1,1) 
message to the processes. 

3. What happens when one of the process is done - it has nothing else to do?
I guess this arises because of my assumption of #1, that processes control
what they need to do, not the controller. 

I am assuming that if the processes have nothing to do, they will send an over 
message. 

*/

#include "linkedlistlib.pml"
#define MQLENGTH 20

mtype = {S_IDLE, S_SEARCH, S_INSERT, S_OVER}
mtype = {O_INSERT, O_CONTINUE}

/*
	Transition system for the process

	State
		k: key to be inserted
		l: Location being accessed
		m: mode (Done, Search, Insert)

	U
		c: command 0 or 1
		o: operation to be performed

	f: U x State --> 
	f ((k, l, m), (c, o)) 
		= (k, l, m) if c = 0 or (m = Done and o = ⊥)
		= (k', head, Search) if m = Done and o = insert(k 0 ) 
		= (k, l.next, m), if m = Search and l.next.key < key
		= (k, l, Insert), if m = Search and l.next.key > key
		= (⊥, ⊥, Done), if m = Insert

*/
typedef Pstate {

	byte k; // key to be inserted
	byte l; // location to work operation
	mtype m; // Kind of operation

}

typedef Pinput {

	bool c; // 0: don't do anything, 1: do your stuff
	mtype o; // operation
}

/*	
	Transition system for the Hub controller
	
	State
		c1: Command to process 1
		c2: Command to process 2

	U
		k1: key for process 1
		l1: location for process 1
		m1: mode for process 1
		k2:
		l2:
		m2:

	f: U x State
		= (0, 1), if m A = m B = Insert, l A = l B and k A < k B
		= (1, 0), if m A = m B = Insert, l A = l B and k A > k B
		= (1, 1), otherwise

*/

/* For a process, we track 2 things: what command was sent, and whether
the process is now done. */

typedef Hblock {
	bool c;
	mtype o;
	bool isOver;
}
typedef Hstate {

	Hblock proc[2]

}

typedef Hinput {

	Pstate proc[2]; // Hold 2 process's states as input

}

/*

typedef Hinput {
	byte k1; // key to be inserted
	byte l1; // location to work operation
	mtype:p_state m1; // Kind of operation
	byte k2; // key to be inserted
	byte l2; // location to work operation
	mtype:p_state m2; // Kind of operation
}

/* 
	Let's setup the communication channel. We will have dedicated channels for each process, 
	one for each direction. So 4 channels in all
	H will send U to P, P will send U to H
*/


//chan ch_PtoH = [MQLENGTH] of {byte, Pstate}
chan ch_PtoH = [MQLENGTH] of {byte, Pstate}
chan ch_HtoP = [MQLENGTH] of {byte, Pinput}

inline do_insert(L_val, loc) {
    
	next = list[loc].next
    
	/* 
		We may reach here even when val = next value, in which case we have to skip insert but
		update the state assuming we inserted 
	*/
	if 
	:: (list[next].value == L_val) ->
		printf("\nCP(%d): %d already exists at index %d. Skipping the insert", id, L_val, next)
		/* 	
			We will behave as if it has now been inserted. After this call returns, 
			we anway set the state correctly so we are good 
		*/

	:: else ->
		/* Get a free node to use for this insertion */
		d_step {
			current = EMPTY;
			EMPTY = EMPTY + 1;
		}
		/* Update the invariant: Assume we are inserting c between a and b. So critical_value will 
			have a factor (b-a) already. We divide by (b-a) and multiply by (c - a) and (b - a) 
			to get the new value of critical_value*/
		d_step {
			printf("CP(%d): Critical Value (before): %d, a: %d, b: %d,  c:%d", _pid, critical_val, list[loc].value, list[next].value, L_val )
			critical_val = (critical_val/(list[next].value - list[loc].value)) * (L_val - list[loc].value) * (list[next].value - L_val)
			
		}

		/* Insert after the current node */
		list[current].value = L_val;
		list[current].next = next;
		list[loc].next = current;
	fi
}

inline do_search(L_val, loc) {
    /* 	Check the next. If it is < val, then continue in search, otherwise 
    	we are ready to insert 
	*/

	next = list[loc].next
	nextval = list[next].value
	// printf("\nCP(%d): Search: loc = %d, val = %d, nextloc = %d, nextval = %d", id, loc, L_val, next, nextval)
	if
	:: (nextval < L_val) ->
		lnext = next
		
		mnext = S_SEARCH
	:: (nextval >= L_val) ->
		lnext = loc
		mnext = S_INSERT
	fi
	// printf("lnext = %d, mnext = %d", lnext, mnext )
}

inline proc_newstate(newk, newl, newm, c, o) {
	printf("\nCP(%d): (%d,%d,%e)----(%d,%e)---->(%d,%d,%e)",
			id, p_state.k, p_state.l, p_state.m,
			c, o,
			newk, newl, newm)

	p_state.k = newk
	p_state.l = newl
	p_state.m = newm
}

inline next_to_insert() {
	if 
	:: (to_insert > max_insert) ->
		printf("\nCP(%d): No more insertions!", id)
		newk = 0
	:: else ->
		newk = insert_list[to_insert]
		to_insert = to_insert + 1
	fi
}

/* Create the processes and implement the transition function

	f: U x State --> 
	f ((k, l, m), (c, o)) 
		= (k, l, m) if c = 0 or (m = Done and o = ⊥)
		= (k', head, Search) if m = Done and o = insert(k 0 ) 
		= (k, l.next, m), if m = Search and l.next.key < key
		= (k, l, Insert), if m = Search and l.next.key > key
		= (⊥, ⊥, Done), if m = Insert

 */

proctype ChildProcess(byte id) {

	Pinput p_input
	Pstate p_state
	byte lnext, mnext, next, newk, nextval
	byte to_insert, max_insert
	bool cmd
	mtype ops
	byte k, l, m
	byte current
	byte insert_list[6];
	
	printf("\nCP(%d) Started.", id)
	insert_list[0] = 50
	insert_list[1] = 51
	insert_list[2] = id
	insert_list[3] = id + 1
	insert_list[4] = 60
	insert_list[5] = 61
	
	to_insert = 0
	max_insert = 5

	// Initialize the state
	p_state.k = 0
	p_state.l = 0
	p_state.m = S_IDLE

	do 
	:: ch_HtoP ?? eval(id), p_input ->
		cmd = p_input.c
		ops = p_input.o

		k = p_state.k
		l = p_state.l
		m = p_state.m

		// printf("\nCP(%d): command: %d, ops: %e", id, cmd, ops )
		
		if
		:: (cmd == true) ->
			// Make the transition
			if
			:: (m == S_IDLE) ->
				if 
				:: (ops == O_CONTINUE) -> 
					proc_newstate(k, l, m, cmd, ops) 
				:: (ops == O_INSERT) ->
					next_to_insert()
					if
					:: (newk == 0) -> // Nothing left to insert
						proc_newstate(0, 0, S_OVER, cmd, ops) 
					:: else ->
						proc_newstate( newk , HEAD , S_SEARCH, cmd, ops )
					fi
				fi

			:: (m == S_SEARCH) ->
				do_search(k, l)
				proc_newstate(k, lnext, mnext, cmd, ops)

			:: (m == S_INSERT) ->
				do_insert(k, l)
				proc_newstate(0, 0, S_IDLE, cmd, ops)

			:: (m == S_OVER) ->
				printf("\nCP(%d): Received message in S_OVER state,exiting now..", id)
				break;
			
			fi
		:: (cmd == false) ->
				proc_newstate(k, l, m, cmd, ops)

		fi

		// send the state to Hub controller
		ch_PtoH ! id, p_state
		printf("\nCP(%d): Message sent (%d, %d, %e)", id, p_state.k, p_state.l, p_state.m)
			



	od
	
	printf("\nCP(%d) Exited.", id)
	
}

/*
	f: U x State
		= (0, 1), if m A = m B = Insert, l A = l B and k A < k B
		= (1, 0), if m A = m B = Insert, l A = l B and k A > k B
		= (1, 1), otherwise

*/

inline hub_nextstate() {

	k1 = h_input.proc[0].k
	l1 = h_input.proc[0].l
	m1 = h_input.proc[0].m
	k2 = h_input.proc[1].k
	l2 = h_input.proc[1].l
	m2 = h_input.proc[1].m
	
	if
	:: (m1 == S_INSERT) && (m2 == S_INSERT) && (l1 == l2) ->
		if
		:: (k1 < k2) ->
			c1 = 0
			c2 = 1
		:: (k1 > k2) ->
			c1 = 1
			c2 = 0
		:: (k1 == k2) ->
			if // Any one of them should go ahead this time but not both
			:: (k1 > 0) -> // Will be always true
				c1 = 1
				c2 = 0
			:: (k2 > 0) -> // Will be always true
				c2 = 1
				c1 = 0
			fi
		fi
	:: else ->
		c1 = 1
		c2 = 1
	fi

	// Check if one or both of them are over
	if
	:: (m1 == S_OVER) ->
		isOver1 = true
	:: else ->
		isOver1 = false
	fi

	if
	:: (m2 == S_OVER) ->
		isOver2 = true
	:: else ->
		isOver2 = false
	fi

	// Check if a process is idle, we can then ask it to insert
	if
	:: (m1 == S_IDLE) ->
		o1 = O_INSERT
	:: else ->
		o1 = O_CONTINUE
	fi

	if
	:: (m2 == S_IDLE) ->
		o2 = O_INSERT
	:: else ->
		o2 = O_CONTINUE
	fi


	printf("\nHC: [(%d,%e,%d),(%d,%e,%d)]----[(%d,%d,%e),(%d,%d,%e)]---->[(%d,%e,%d),(%d,%e,%d)]",
			h_state.proc[0].c, h_state.proc[0].o, h_state.proc[0].isOver,
			h_state.proc[1].c, h_state.proc[1].o, h_state.proc[1].isOver,
			h_input.proc[0].k, h_input.proc[0].l, h_input.proc[0].m,
			h_input.proc[1].k, h_input.proc[1].l, h_input.proc[1].m,
			c1,o1,isOver1, c2,o2,isOver2)
	
	h_state.proc[0].c = c1
	h_state.proc[0].o = o1
	h_state.proc[0].isOver = isOver1

	h_state.proc[1].c = c2
	h_state.proc[1].o = o2
	h_state.proc[1].isOver = isOver2

}

inline hub_updatestate(loc) {
	// We mark this guy as good to go because the other process is over. 
	c1 = 1
	
	// We also check if this process is over after this or not
	if
	:: (h_input.proc[loc].m == S_OVER) ->
		isOver1 = true

	:: else ->
		isOver1 = false
	fi

	// Check if the incoming m was IDLE, then we have to ask them to insert. Otherwise 
	// continue doing whatever they were doing
	if
	:: (h_input.proc[loc].m == S_IDLE) ->
		o1 = O_INSERT

	:: else ->
		o1 = O_CONTINUE
	fi

	printf("\nHC: [(%d,%e,%d),(S_OVER)]----[(%d,%d,%e),(S_OVER))]---->[(%d,%e,%d),(S_OVER)]",
			h_state.proc[loc].c, h_state.proc[loc].o, h_state.proc[loc].isOver,
			h_input.proc[loc].k, h_input.proc[loc].l, h_input.proc[loc].m,
			c1, o1, isOver1)

	
	h_state.proc[loc].c = c1
	h_state.proc[loc].o = o1
	h_state.proc[loc].isOver = isOver1
	
}

inline send_message_to_proc(loc, id) {
	h_send.c = h_state.proc[loc].c
	h_send.o = h_state.proc[loc].o
	ch_HtoP ! id, h_send
	printf("\nHC: Message sent (%d, %e) to CP(%d)", h_send.c, h_send.o, id)  
}

inline copy_to_hstate(loc, p_state) {
	h_input.proc[loc].k = p_state.k
	h_input.proc[loc].l = p_state.l
	h_input.proc[loc].m = p_state.m
	
	
}
proctype HubController(byte id1; byte id2) {
	Hstate h_state;
	Hinput h_input;
	Pinput h_send;
	byte k1, l1, m1, k2, l2, m2, c1, c2, isOver1, isOver2, o1, o2;
	Pstate p_state1, p_state2;
	printf("\nHC Started with 2 processes %d and %d.", id1, id2)
	
	/* Initialize the state */
	h_state.proc[0].c = 1
	h_state.proc[0].o = O_INSERT
	h_state.proc[0].isOver = false
	
	h_state.proc[1].c = 1
	h_state.proc[1].o = O_INSERT
	h_state.proc[1].isOver = false
	
	// Send initial message to get the 2 processes going
	send_message_to_proc(0, id1)
	send_message_to_proc(1, id2)


	do 
		:: ch_PtoH ?? eval(id1), h_input.proc[0] ->
			//copy_to_hstate(0, p_state1)
			if
			:: ch_PtoH ?? eval(id2), h_input.proc[1] ->
				//copy_to_hstate(1, p_state2)
				/* Got the two messages, work on them */
				hub_nextstate()
				
				send_message_to_proc(0, id1)
				send_message_to_proc(1, id2)

			:: (h_state.proc[1].isOver == true) ->
				/* Only P1 is active, just let it proceed */
				hub_updatestate(0)
				
				send_message_to_proc(0, id1)
			fi
		:: ch_PtoH ?? eval(id2), h_input.proc[1] ->
			//copy_to_hstate(1, p_state2)
			
			if
			:: ch_PtoH ?? eval(id1), h_input.proc[0] ->
				//copy_to_hstate(0, p_state1)
			
				// Got the two messages, work on them 
				hub_nextstate()

				send_message_to_proc(0, id1)
				send_message_to_proc(1, id2)

			:: (h_state.proc[0].isOver == true) ->
				// Only P2 is active, just let it proceed 
				hub_updatestate(1)

				send_message_to_proc(1, id2)
			fi
		:: ((h_state.proc[0].isOver == true) && (h_state.proc[1].isOver == true)) ->
			printf("\nHC: We should exit - both processes are done!")
			break;
		
	od	

	printf("\nHC Exited")

}
active proctype parent() {
	int i;
	int next;
	pid n;
	n = _nr_pr;

	int x;
	initialize ()
	print_list()
	print_memory()

	run ChildProcess(1);
	run ChildProcess(2);
	run HubController(1, 2)
	(n == _nr_pr);
		print_list ()
		print_memory()
}


