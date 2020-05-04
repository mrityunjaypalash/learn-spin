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
#define MQLENGTH 5

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
chan ch_PtoH = [MQLENGTH] of {byte, mtype}


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
	byte k1, l1, k2, l2, c1, c2, isOver1, isOver2;
    mtype m1, m2, o1, o2;
	Pstate p_state1, p_state2;
	printf("\nHC Started with 2 processes %d and %d.", id1, id2)
	
	/* Initialize the state */
	h_state.proc[0].c = 1
	h_state.proc[0].o = O_INSERT
	h_state.proc[0].isOver = false
	
	h_state.proc[1].c = 1
	h_state.proc[1].o = O_INSERT
	h_state.proc[1].isOver = false


	do 
		:: ch_PtoH ? id1, m1 ->
			//copy_to_hstate(0, p_state1)
				
				send_message_to_proc(0, id1)
				send_message_to_proc(1, id2)

		
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

	ch_PtoH ! 1, S_IDLE
	ch_PtoH ! 2, S_IDLE
	ch_PtoH ! 1, S_SEARCH
	ch_PtoH ! 2, S_SEARCH
	
	
		
	//run ChildProcess(1);
	//run ChildProcess(2);
	run HubController(1, 2)
	(n == _nr_pr);
		print_list ()
		print_memory()
}


