#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h> 

extern int our_code_starts_here() asm("our_code_starts_here");
extern int print(int val) asm("print");
extern int input(int val) asm("input");
extern int equals(int val1, int val2) asm("equals");
extern int printstack(int val, int* EBP, int* ESP) asm("printstack");
extern void error(int errCode, int val) asm("error");

int* HEAP;

/*
Tagged values:
Numbers: 0 in least significant bit
Booleans: 111 in least three significant bits
Tuples: 001 in least three significant bits
*/

const int BOOL_TAG   = 0x00000001;
const int BOOL_TRUE  = 0xFFFFFFFF; // These must be the same values
const int BOOL_FALSE = 0x7FFFFFFF; // as chosen in compile.ml

const int E_ARITH_NOT_NUM = 1;
const int E_COMPARISON_NOT_NUM = 2;
const int E_IF_NOT_BOOL = 3;
const int E_LOGIC_NOT_BOOL = 4;
const int E_ARITH_OVERFLOW = 5;

extern int STACK_BOTTOM;
int STACK_BOTTOM = 0;

void print_tagged_value(int val) {
  if ((val & BOOL_TAG) == 0) { 
    // is number
    printf("%d", val >> 1);  // shift bits right to remove tag
  } else if (val == BOOL_TRUE) {
    printf("true");
  } else if (val == BOOL_FALSE) {
    printf("false");
  } else if ((val & BOOL_TAG) == 1) {
    if (val == BOOL_TAG) {
      printf("nil");
      return;
    }
    // is tuple 
    int* p = (int*)(val - 0x1);
    int size = *p;
    printf("(");
    for(int i = 0; i < size; i++) {
      print_tagged_value(*(p+(i+1)));
      if(size < 2 || i != size - 1) printf(",");
    }
    printf(")");
  } else {
    printf("%#010x", val); 
  }
  return;
}
/* why this must be implemented as a EPrim1 and not as a EApp expression?
  Diamondback does not have pointers, therefore printstack must be implemented 
  in C to have direct access to memory.
*/
int printstack(int val, int* EBP, int* ESP) {
  printf("printstack\n");
  printf("STACK_BOTTOM: %p\n", (void*)STACK_BOTTOM);
  printf("ESP: %p ==> %d\n", ESP, (unsigned int)ESP);
  printf("EBP: %p ==> %d\n", EBP, (unsigned int)EBP);
  printf("(difference: %d)\n", (unsigned int)ESP-(unsigned int)EBP);
  printf("Requested return val(raw): %#010x\n\n", val);

  int* current_stack_ebp = EBP;
  int* last_stack_ebp = NULL;
  while(true) {
    printf("%p: %#010x   ==>   ", ESP, *ESP);
    if(ESP == current_stack_ebp) {
      printf("saved ebp");
      if((int)ESP == STACK_BOTTOM) printf(" (STACK_BOTTOM)");
      last_stack_ebp = current_stack_ebp;
      current_stack_ebp = (void*)*ESP;
    }
    else if(ESP == last_stack_ebp + 1) {
      printf("saved return address");
      printf("\n-");
    }
    else {
      print_tagged_value((int)*ESP);
    }
    printf("\n");
    if((int)ESP == STACK_BOTTOM) break;
    ESP++;
  }
  printf("- End of printstack\n");
  return val; 
}

int input(int val) {
  // the argument is discarded
  // get an user input as an integer
  int n;
  printf("Please input an integer value: ");
  scanf ("%d",&n);
  printf("You entered: %d\n", n);

  return n << 1;
}

bool istuple(int val) {
  if ((val & 0x00000111) == 0x00000001) { 
    return true;
  }
  return false;
}

int equals(int val1, int val2) {
  // content equality
  if (istuple(val1) && istuple(val2)) {
      // compare tuples - does not handle cyclic tuples
      if ((val1 == BOOL_TAG) || (val2 == BOOL_TAG)) {
        // if some tuple is nil
        if (val1 == val2) return BOOL_TRUE; else return BOOL_FALSE;
      } 
      int* p1 = (int*)(val1 - 0x1);
      int size1 = *p1;

      int* p2 = (int*)(val2 - 0x1);
      int size2 = *p2;

      if (size1 != size2) return BOOL_FALSE;
      
      for(int i = 0; i < size1; i++) {
        // The return value of equals is tagged boolean.
        int eq = equals(*(p1+(i+1)), *(p2+(i+1)));
        if (eq == BOOL_FALSE) return BOOL_FALSE;
      }
      return BOOL_TRUE;
  } else  {
    // not a tuple    
    if (val1 == val2) return BOOL_TRUE; else return BOOL_FALSE;
  } 
}

int print(int val) {
  if ((val & BOOL_TAG) == 0 || val == BOOL_TRUE || val == BOOL_FALSE || (val & BOOL_TAG) == 1) {
    print_tagged_value(val);
    printf("\n");
  } else {
    printf("Unknown value: ");
    print_tagged_value(val);
    printf("\n");
  }
  return val;
}
void error(int errCode, int val) {
  if(errCode == E_ARITH_NOT_NUM) {
    fprintf(stderr, "Error: arithmetic expected a number, but got %010x\n", val);
  } else if(errCode == E_COMPARISON_NOT_NUM) {
    fprintf(stderr, "Error: comparison expected a number, but got %010x\n", val);
  } else if(errCode == E_IF_NOT_BOOL) {
    fprintf(stderr, "Error: if expected a boolean, but got %d\n", val >> 1);
  } else if(errCode == E_LOGIC_NOT_BOOL) {
    fprintf(stderr, "Error: logic expected a boolean, but got %d\n", val >> 1);
  } else if(errCode == E_ARITH_OVERFLOW) {
    fprintf(stderr, "Error: Integer overflow\n");
  } else {
    fprintf(stderr, "Error: unknown error");
  }
  exit(1);
}
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
