#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h> 

extern int our_code_starts_here() asm("our_code_starts_here");
extern int print(int val) asm("print");
extern void error(int errCode, int val) asm("error");
extern int printstack(int val, int* EBP, int* ESP) asm("printstack");

const int BOOL_TAG   = 0x00000001;
const int BOOL_TRUE  = 0xFFFFFFFF; // These must be the same values
const int BOOL_FALSE = 0x7FFFFFFF; // as chosen in compile.ml

const int E_ARITH_NOT_NUM = 1;
const int E_COMPARISON_NOT_NUM = 2;
const int E_IF_NOT_BOOL = 3;
const int E_LOGIC_NOT_BOOL = 4;
const int E_ARITH_OVERFLOW = 5;

extern int ebp_of_main;
int ebp_of_main = 0;


bool is_tagged_value(int val) {
  if ((val & BOOL_TAG) == 0 || val == BOOL_TRUE || val == BOOL_FALSE) return true;
  return false;
}
void print_tagged_value(int val) {
  if ((val & BOOL_TAG) == 0) { 
    printf("%d", val >> 1);  // shift bits right to remove tag
  } else if (val == BOOL_TRUE) {
    printf("true");
  } else if (val == BOOL_FALSE) {
    printf("false");
  } else {
    printf("%#010x", val); 
  }
  return;
}

int printstack(int val, int* EBP, int* ESP) {
  printf("print_stack\n");
  printf("ebp_of_main: %p\n", (void*)ebp_of_main);
  printf("ESP: %p ==> %d\n", ESP, (unsigned int)ESP);
  printf("EBP: %p ==> %d\n", EBP, (unsigned int)EBP);
  printf("(difference: %d)\n", (unsigned int)ESP-(unsigned int)EBP);
  printf("Requested return val: %#010x\n", val);

  int* current_stack_ebp = EBP;
  int* last_stack_ebp = NULL;
  while(true) {
    printf("%p: %#010x   ==>   ", ESP, *ESP);
    if(ESP == current_stack_ebp) {
      printf("saved EBP");
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
    if((int)ESP == ebp_of_main) break;
    ESP++;
  }
  return val; 
}
int print(int val) {
  if ((val & BOOL_TAG) == 0 || val == BOOL_TRUE || val == BOOL_FALSE) {
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
int main(int argc, char** argv) {
  int result = our_code_starts_here();
  print(result);
  return 0;
}
