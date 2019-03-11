#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int our_code_starts_here() asm("our_code_starts_here");
extern int print(int val) asm("print");

int* HEAP;


int print(int val) {
  // COPY YOUR IMPLEMENTATION FROM DIAMONDBACK
  return val;
}

/*

COPY YOUR IMPLEMENTATION FROM DIAMONDBACK

*/


// main should remain unchanged
// You can pass in a numeric argument to your program when you run it,
// to specify the size of the available heap.  You may find this useful
// for debugging...
int main(int argc, char** argv) {
  int size = 100000;
  if (argc > 1) { size = atoi(argv[1]); }
  if (size < 0 || size > 1000000) { size = 0; }
  HEAP = calloc(size, sizeof (int));

  int result = our_code_starts_here(HEAP, size);
  print(result);
  free(HEAP);
  return 0;
}
