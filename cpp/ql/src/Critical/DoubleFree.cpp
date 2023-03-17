int* f() {
	int *buff = malloc(SIZE*sizeof(int));
	do_stuff(buff);
	free(buff);
	int *new_buffer = malloc(SIZE*sizeof(int));
	free(buff); // If new_buffer is the same as buffer,
	            // the memory allocator will free the new buffer memory region, leading
	            // to use-after-free problems and memory corruption.
	return new_buffer;
}
