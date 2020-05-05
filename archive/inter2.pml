byte n;

proctype P(byte id; byte incr) {
	byte temp;
	temp = n + incr;
	n = temp;
	printf("Process P%d, n = %d\n", id, n);
}

init {
	n = 0
	atomic {
		run P(1,10);
		run P(2, 15);
	}
}

