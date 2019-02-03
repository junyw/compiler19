#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int our_code_starts_here() asm("our_code_starts_here");
extern int print(int val) asm("print");
extern void error(int errCode) asm("error");

const int BOOL_TAG   = 0x00000001;
const int BOOL_TRUE  = 0xFFFFFFFF; // These must be the same values
const int BOOL_FALSE = 0x7FFFFFFF; // as chosen in compile.ml

const int E_ARITH_NOT_INT = 1;
const int E_COMPARISON_NOT_INT = 2;
const int E_IF_NOT_BOOL = 3;
const int E_LOGIC_NOT_BOOL = 4;

int print(int val) {
  if ((val & BOOL_TAG) == 0) { // val is even ==> number
    printf("%d\n", val >> 1);  // shift bits right to remove tag
  } else if (val == BOOL_TRUE) {
    printf("true\n");
  } else if (val == BOOL_FALSE) {
    printf("false\n");
  } else {
    printf("Unknown value: %#010x\n", val); // print unknown val in hex
  }
  return val;
}
void error(int errCode) {
  if(errCode == E_ARITH_NOT_INT) {
    fprintf(stderr, "Error: arithmetic expected a number");
    exit(1);
  } else if(errCode == E_COMPARISON_NOT_INT) {
    fprintf(stderr, "Error: comparison expected a number");
    exit(1);
  } else if(errCode == E_IF_NOT_BOOL) {
    fprintf(stderr, "Error: if expected a boolean");
    exit(1);
  } else if(errCode == E_LOGIC_NOT_BOOL) {
    fprintf(stderr, "Error: logic expected a boolean");
    exit(1);
  } else {
    fprintf(stderr, "Error: unknown error");
    exit(1);
  }
}
int main(int argc, char** argv) {
  int result = our_code_starts_here();
  print(result);
  return 0;
}
