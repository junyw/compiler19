#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int our_code_starts_here() asm("our_code_starts_here");
extern int print(int val) asm("print");

int print(int val) {
  // COPY YOUR IMPLEMENTATION FROM DIAMONDBACK
  return val;
}

/*

COPY YOUR IMPLEMENTATION FROM DIAMONDBACK

*/


// main should remain unchanged
int main(int argc, char** argv) {
  int result = our_code_starts_here();
  print(result);
  return 0;
}
