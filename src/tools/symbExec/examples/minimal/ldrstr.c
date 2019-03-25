void main (void) {
	__asm ("str w0, [sp, #12]");
	__asm ("ldr w1, [sp, #12]");
}
