mtype = {FOR_CLIENT, FOR_SERVER, S_IDLE, S_SEARCH, S_INSERT, S_OVER, O_INSERT, O_CONTINUE, STOP_CLIENT, STOP_HUB}

typedef Pstate {

	byte k; // key to be inserted
	byte l; // location to work operation
	mtype m; // Kind of operation

}

active proctype Main() {
	Pstate p_state
	byte n
	byte a[2]

    printf("\nValues: %d, %d, %e, %d, %d, %d", p_state.k, p_state.l, p_state.m, n, a[0], a[1])
}