/*
	One hub controller (server), 8 clients. 
	Each client sends a message to the hub, hub responds with the message it received. 
*/

#define N 2 // Number of clients


#define MQLENGTH 100

// mtype = {START_CLIENT, COMPUTE_REQUEST, COMPUTE_RESPONSE, STOP_CLIENT, STOP_HUB}
mtype = {FOR_CLIENT, FOR_SERVER, S_IDLE, S_SEARCH, S_INSERT, S_OVER, O_INSERT, O_CONTINUE, STOP_CLIENT, STOP_HUB}

/*
typedef ClientRequest {
	byte num;
}

typedef HubResponse {
	bool isNull; // To indicate whether there is data or not. Set True for START and STOP messages
	int id;
	byte num;
	int sqnum;
}


typedef IdList {
	byte ids[N]; // Use to store the ids assigned to each client process
}


IdList idlist;

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

chan ch_clientrequest = [MQLENGTH] of {mtype, byte, Pstate} // Hub listens to this
// chan ch_hubresponse = [MQLENGTH] of {mtype, byte, HubResponse} // Clients read from this

int message_served = 0


proctype Hub() {
	// Hub sends a start message to each client, and then keeps responding to what it receives
	mtype msgtype
	byte client_id
	int i
	byte num
	Pstate p_state
	Hstate h_state;
	Hinput h_input;
	Pinput h_send;

	byte k1, l1, m1, k2, l2, m2, c1, c2, isOver1, isOver2, o1, o2;
	Pstate p_state1, p_state2;
	//printf("\nHC Started with 2 processes %d and %d.", id1, id2)
	
	/* Initialize the state */
	h_state.proc[0].c = 1
	h_state.proc[0].o = O_INSERT
	h_state.proc[0].isOver = false
	
	h_state.proc[1].c = 1
	h_state.proc[1].o = O_INSERT
	h_state.proc[1].isOver = false

	
	// All of the clients have been started. Now wait for the message and respond appropriately
	do
	:: ch_clientrequest ?? msgtype, 1, h_state.proc[0] ->
		printf("\nHub Controller. Received - MsgType: %e", msgtype)
		if
		:: (msgtype == FOR_SERVER) ->
			if
			:: ch_clientrequest ?? msgtype, 2, h_state.proc[1] ->
				printf("\nHubController received second message!")
			fi
		:: (msgtype == STOP_HUB) ->
			break;

		fi

	od


	printf("\nServer exiting.")	
}

active proctype Main() {
	// Start the clients and give them an id to use
	//ClientRequest c;
	Pstate p_state;
	pid n;
	n = _nr_pr;
	byte i

	p_state.k = 0
	p_state.l = 1
	p_state.m = S_IDLE

	p_state.k = 2
	ch_clientrequest ! FOR_SERVER(1, p_state)
	p_state.k = 3
	ch_clientrequest ! FOR_SERVER(2, p_state)
	p_state.k = 4
	ch_clientrequest ! FOR_SERVER(1, p_state)
	p_state.k = 5
	ch_clientrequest ! FOR_SERVER(2, p_state)
	ch_clientrequest ! STOP_HUB(1, p_state)
	
			
	// Start the hub and give it the list of ids

	run Hub()

	// Wait for all processes to exit
	(n == _nr_pr); 
	printf("\nAll processes have exited!")
}

