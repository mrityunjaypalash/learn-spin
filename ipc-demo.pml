/*
	One hub controller (server), 8 clients. 
	Each client sends a message to the hub, hub responds with the message it received. 
*/

#define N 4 // Number of clients

#define MQLENGTH 100

/*
#define START_CLIENT 		1
#define COMPUTE_REQUEST	2
#define COMPUTE_RESPONSE	3
#define STOP_CLIENT		4
#define STOP_HUB			5

*/

mtype = {START_CLIENT, COMPUTE_REQUEST, COMPUTE_RESPONSE, STOP_CLIENT, STOP_HUB}

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

chan ch_clientrequest = [MQLENGTH] of {mtype, byte, ClientRequest} // Hub listens to this
chan ch_hubresponse = [MQLENGTH] of {mtype, byte, HubResponse} // Clients read from this

int message_served = 0


active [N] proctype Client(byte id) {
	// A client reads the message and responds to it
	mtype msgtype
	HubResponse hub_response
	ClientRequest client_request
	
	do
	:: ch_hubresponse ?? msgtype, eval(id), hub_response ->
		printf("\nClient Id: %d, Received - MsgType: %e", id, msgtype)
		if
		:: (msgtype == COMPUTE_RESPONSE) ->
			// print the message
			printf("\nClient Id: %d, Received - num = %d, sqnum = %d", id, hub_response.num, hub_response.sqnum)
			// send another message. new num = sqnum
			client_request.num = hub_response.sqnum % 256// To keep it as byte
			if
			:: (client_request.num < 2) ->
				client_request.num = 2
			:: else ->
				skip
			fi

			ch_clientrequest ! COMPUTE_REQUEST(id, client_request)
			printf("\nClient Id: %d, Sent - num = %d", id, client_request.num)
			

		:: (msgtype == STOP_CLIENT) ->
			// break from the do loop
			break;
		:: (msgtype == START_CLIENT) ->
			client_request.num = id // Start with num = id
			ch_clientrequest ! COMPUTE_REQUEST(id, client_request)
			printf("\nClient Id: %d, Sent - num = %d", id, client_request.num)

		fi

	od

	printf("\nClient exiting. Id = %d", id)

}

proctype Hub(IdList idlist) {
	// Hub sends a start message to each client, and then keeps responding to what it receives
	HubResponse hr
	ClientRequest client_request
	mtype msgtype
	byte client_id
	int i
	byte num


	for (i: 0 .. ( N - 1) ) {
		// Send a start message
		hr.isNull = true

		ch_hubresponse ! START_CLIENT(idlist.ids[i], hr) // Send a start message
	}
	// All of the clients have been started. Now wait for the message and respond appropriately
	do
	:: ch_clientrequest ? msgtype, client_id, client_request ->
		printf("\nHub Controller. Received - MsgType: %e", msgtype)
		if
		:: (msgtype == COMPUTE_REQUEST) ->
			// handle the message
			num = client_request.num
			hr.isNull = false
			hr.id = client_id
			hr.num = num
			hr.sqnum = num * num
			ch_hubresponse ! COMPUTE_RESPONSE(client_id, hr) // Send a response message
			message_served ++

		:: (msgtype == STOP_HUB) ->
			// break from the do loop, send stop message to all clients, and exit
			break;
		fi

	od

	// loop through the ids and send stop message
	for (i: 0 .. ( N - 1) ) {
		// Send a start message
		hr.isNull = true
		ch_hubresponse ! STOP_CLIENT(idlist.ids[i], hr) // Send a start message
	}

	printf("\nServer exiting.")	
}

active proctype Main() {
	// Start the clients and give them an id to use
	IdList idlist;
	ClientRequest c
	pid n;
	n = _nr_pr;
	byte i

	for (i: 1.. N ) {
		run Client(i)
		idlist.ids[i-1] = i
	}

	// Start the hub and give it the list of ids

	run Hub(idlist)


	// Send a message to Hub to stop serving
	(message_served >= 100);
	ch_clientrequest ! STOP_HUB(0, c) 

	// Wait for all processes to exit
	(n == _nr_pr); 
	printf("\nAll processes have exited!")
}

