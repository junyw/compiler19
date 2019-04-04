#include <stdio.h>
#include <stdlib.h>
#include "gc.h"

extern int our_code_starts_here() asm("our_code_starts_here");
extern void error() asm("error");
extern int print(int val) asm("print");
extern int g_PrintStack(int val, int* esp, int* ebp, int args) asm("print_stack");
extern int equal(int val1, int val2) asm("equal");
extern int* try_gc(int* alloc_ptr, int amount_needed, int* first_frame, int* stack_top) asm("try_gc");
extern int* HEAP_END asm("HEAP_END");
extern int* HEAP asm("HEAP");
extern int* STACK_BOTTOM asm("STACK_BOTTOM");

/*
Tagged values:
Numbers: 0 in least significant bit
Booleans: 111 in least three significant bits
Tuples: 001 in least three significant bits
Lambda: 101 in least three significant bits
Forwarding: 011 in least three significant bits
*/

const int NUM_TAG_MASK     = 0x00000001;
const int BOOL_TAG_MASK    = 0x00000007;
const int TUPLE_TAG_MASK   = 0x00000007;
const int CLOSURE_TAG_MASK = 0x00000007;
const int FORWARD_TAG_MASK = 0x00000007;
const int NUM_TAG          = 0x00000000;
const int BOOL_TAG         = 0x00000007;
const int TUPLE_TAG        = 0x00000001;
const int FORWARD_TAG      = 0x00000003;
const int CLOSURE_TAG      = 0x00000005;
const int BOOL_TRUE        = 0xFFFFFFFF;
const int BOOL_FALSE       = 0x7FFFFFFF;
const int NIL              = ((int)NULL | TUPLE_TAG);

const int ERR_COMP_NOT_NUM     = 1;
const int ERR_ARITH_NOT_NUM    = 2;
const int ERR_LOGIC_NOT_BOOL   = 3;
const int ERR_IF_NOT_BOOL      = 4;
const int ERR_OVERFLOW         = 5;
const int ERR_GET_NOT_TUPLE    = 6;
const int ERR_GET_LOW_INDEX    = 7;
const int ERR_GET_HIGH_INDEX   = 8;
const int ERR_NIL_DEREF        = 9;
const int ERR_OUT_OF_MEMORY    = 10;
const int ERR_SET_NOT_TUPLE    = 11;
const int ERR_SET_LOW_INDEX    = 12;
const int ERR_SET_HIGH_INDEX   = 13;
const int ERR_CALL_NOT_CLOSURE = 14;
const int ERR_CALL_ARITY_ERR   = 15;

typedef unsigned int uint;

size_t HEAP_SIZE;
int* STACK_BOTTOM;
int* HEAP;
int* HEAP_END;

int* FROM_S;
int* FROM_E;
int* TO_S;
int* TO_E;

int equal(int val1, int val2) {
  if (val1 == val2) { return BOOL_TRUE; }
  if (val1 == NIL || val2 == NIL) { return BOOL_FALSE; }
  if ((val1 & TUPLE_TAG_MASK) == TUPLE_TAG && (val2 & TUPLE_TAG_MASK) == TUPLE_TAG) {
    int *tup1 = (int*)(val1 - TUPLE_TAG);
    int *tup2 = (int*)(val2 - TUPLE_TAG);
    if (tup1[0] != tup2[0]) { return BOOL_FALSE; }
    for (int i = 1; i <= tup1[0] / 2; i++) {
      if (equal(tup1[i], tup2[i]) == BOOL_FALSE)
        return BOOL_FALSE;
    }
    return BOOL_TRUE;
  }
  return BOOL_FALSE;
}

int tupleCounter = 0;
void printHelp(FILE *out, int val) {
  if (val == NIL) {
    fprintf(out, "nil");
  }
  else if((val & NUM_TAG_MASK) == NUM_TAG) {
    fprintf(out, "%d", val >> 1);
  }
  else if(val == BOOL_TRUE) {
    fprintf(out, "true");
  }
  else if(val == BOOL_FALSE) {
    fprintf(out, "false");
  }
  else if ((val & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
    int* addr = (int*)(val - CLOSURE_TAG);
    fprintf(out, "[%p - 5] ==> <function arity %d, closed %d, fn-ptr %p>",
            (int*)val, addr[0] / 2, addr[1] / 2, (int*)addr[2]);
    /* fprintf(out, "\nClosed-over values:\n"); */
    /* for (int i = 0; i < addr[1] / 2; i++) { */
    /*   if (i > 0) { fprintf(out, "\n"); } */
    /*   if ((addr[3 + i] & TUPLE_TAG_MASK) == 5) { */
    /*     fprintf(out, "<closure %p>", (int*)addr[3 + i]); */
    /*   } else { */
    /*     printHelp(out, addr[3 + i]); */
    /*   } */
    /* } */
  }
  else if ((val & TUPLE_TAG_MASK) == 3) { 
    fprintf(out, "forwarding to "); 
    fflush(out); 
    fprintf(out, "%p", (int*)(val - 3)); 
    fflush(out); 
    return; 
  } 
  else if ((val & TUPLE_TAG_MASK) == TUPLE_TAG) {
    int* addr = (int*)(val - 1);
    // Check whether we've visited this tuple already
    if ((*addr & 0x80000000) != 0) {
      fprintf(out, "<cyclic tuple %d>", (int)(*addr & 0x7FFFFFFF));
      return;
    }
    /* if (!(addr >= FROM_S && addr < FROM_E) && !(addr >= TO_S && addr < TO_E)) { */
    /*   fprintf(out, "DANGLING POINTER %p", addr); */
    /*   return; */
    /* } */
    // Mark this tuple: save its length locally, then mark it
    int len = addr[0]; // length is encoded
    if (len & 0x1) { // actually, it's a forwarding pointer
      fprintf(out, "forwarding to %p", (int*)(len - 1));
      return;
    }
    /* fprintf(out, "Heap is:\n"); */
    /* naive_print_heap(HEAP, HEAP_END); */
    /* fprintf(out, "%p-->(len=%d)", (int*)(val - 1), len / 2); */
    /* fflush(out); */
    *(addr) = 0x80000000 | (++tupleCounter);
    fprintf(out, "(");
    for (int i = 1; i <= len / 2; i++) {
      if (i > 1) fprintf(out, ", ");
      printHelp(out, addr[i]);
    }
    fprintf(out, ")");
    // Unmark this tuple: restore its length
    *(addr) = len; // length is encoded
  }
  else {
    fprintf(out, "Unknown value: %#010x", val);
  }
}

int print(int val) {
  printHelp(stdout, val);
  printf("\n");
  return val;
}

int g_PrintStack(int val, int* esp, int* ebp, int args) {
  printf("ESP: %p\t==>  ", esp); fflush(stdout);
  printHelp(stdout, *esp); fflush(stdout);
  printf("\nEBP: %p\t==>  ", ebp); fflush(stdout);
  printHelp(stdout, *ebp); fflush(stdout);
  printf("\n(difference: %d)\n", esp - ebp); fflush(stdout);
  printf("Requested return val: %p ==> ", (int*)val); fflush(stdout);
  printHelp(stdout, val); fflush(stdout);
  printf("\n"); fflush(stdout);
  printf("Num args: %d\n", args);

  if (esp > ebp) {
    printf("Error: ESP and EBP are not properly oriented\n"); fflush(stdout);
  } else {
    for (int* cur = esp; cur < STACK_BOTTOM + 3; cur++) {
      if (cur == STACK_BOTTOM) {
        printf("BOT %#010x: %#010x\t==>  old ebp\n", (uint)cur, *cur); fflush(stdout);
      } else if (cur == ebp) {
        printf("EBP %#010x: %#010x\t==>  old ebp\n", (uint)cur, *cur); fflush(stdout);
      } else if (cur == ebp + 1) {
        printf("    %#010x: %#010x\t==>  saved ret\n", (uint)cur, *cur); fflush(stdout);
        esp = ebp + 2;
        ebp = (int*)(*ebp);
      } else if (cur == STACK_BOTTOM + 2) {
        printf("    %#010x: %p\t==>  heap\n", (uint)cur, (int*)*cur); fflush(stdout);
      } else {
        printf("    %p: %#010x\t==>  ", cur, *cur); fflush(stdout);
        printHelp(stdout, *cur); fflush(stdout);
        printf("\n"); fflush(stdout);
      }
    }
  }
  return val;
}



void error(int i, int val) {
  switch (i) {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number\n");
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number\n");
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "Error logic expected a boolean\n");
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean\n");
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: Integer overflow\n");
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "Error: get expected tuple\n");
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to get\n");
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to get\n");
    break;
  case ERR_NIL_DEREF:
    fprintf(stderr, "Error: tried to access component of nil\n");
    break;
  case ERR_OUT_OF_MEMORY:
    fprintf(stderr, "Error: out of memory\n");
    break;
  case ERR_SET_NOT_TUPLE:
    fprintf(stderr, "Error: set expected tuple\n");
    break;
  case ERR_SET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to set\n");
    break;
  case ERR_SET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to set\n");
    break;
  case ERR_CALL_NOT_CLOSURE:
    fprintf(stderr, "Error: tried to call a non-closure value\n");
    break;
  case ERR_CALL_ARITY_ERR:
    fprintf(stderr, "Error: arity mismatch in call\n");
    break;
  default:
    fprintf(stderr, "Error: Unknown error code: %d\n", i);
  }
  fprintf(stderr, "%p ==> ", (int*)val);
  printHelp(stderr, val);
  fprintf(stderr, "\n");
  fflush(stderr);
  naive_print_heap(HEAP, HEAP_END);
  fflush(stdout);
  exit(i);
}

/*
  Try to reserve the desired number of bytes of memory, and free garbage if
  needed.  Fail (and exit the program) if there is insufficient memory.  Does 
  not actually allocate the desired number of bytes of memory; the caller 
  will do that.

  Arguments:

    int* alloc_ptr - the current top of the heap (which we store in ESI), where
                     the next allocation should occur, if possible
    int bytes_needed - the number of bytes of memory we want to allocate
                       (including padding)
    int* cur_frame - the base pointer of the topmost stack frame of our code
                     (i.e., EBP)
    int* cur_stack_top - the stack pointer of the topmost stack frame of our
                         code (i.e., ESP)

  Returns:
    The new top of the heap (i.e. the new value of ESI) after garbage collection.  
    Does not actually allocate bytes_needed space.

  Side effect:
    Also updates HEAP_END to point to the new end of the heap, if it's changed
*/
int* try_gc(int* alloc_ptr, int bytes_needed, int* cur_frame, int* cur_stack_top) {
  fprintf(stderr, "%s\n", "try_gc");
  fflush(stderr);

  int* new_heap = (int*)calloc(HEAP_SIZE + 7, sizeof(int));
  int* old_heap = HEAP;
  int* old_heap_end = HEAP_END;

  int* new_esi = (int*)(((int)new_heap + 7) & ~0x7);
  int* new_heap_end = new_esi + HEAP_SIZE;

  FROM_S = (int*)(((int)HEAP + 7) & ~0x7);
  FROM_E = HEAP_END;
  TO_S = new_esi;
  TO_E = new_heap_end;

  printf("cur_frame = %p, cur_stack_top = %p\n", cur_frame, cur_stack_top);
  printf("FROM_S = %p, FROM_E = %p, TO_S = %p, TO_E = %p\n", FROM_S, FROM_E, TO_S, TO_E); 
  // naive_print_heap(FROM_S, FROM_E); 
  g_PrintStack(BOOL_TRUE, cur_stack_top, cur_frame, 0); 

  // Abort early, if we can't allocate a new to-space
  if (new_heap == NULL) {
    fprintf(stderr, "Out of memory: could not allocate a new semispace for garbage collection\n");
    fflush(stderr);
    if (old_heap != NULL) free(old_heap);
    exit(ERR_OUT_OF_MEMORY);
  }

  printf("before gc---------------------------------\n");
  smarter_print_heap(old_heap, old_heap_end, new_heap, new_heap_end);
  printf("---------------------------------\n");

  new_esi = gc(STACK_BOTTOM, cur_frame, cur_stack_top, FROM_S, FROM_E, TO_S);
  
  printf("after gc---------------------------------\n");
  smarter_print_heap(old_heap, old_heap_end, new_heap, new_heap_end);
  printf("---------------------------------\n");


  HEAP = new_heap;
  HEAP_END = new_heap_end;
  free(old_heap);

  // Note: strict greater-than is correct here: if new_esi + (bytes_needed / 4) == HEAP_END,
  // that does not mean we're *using* the byte at HEAP_END, but rather that it would be the
  // next free byte, which is still ok and not a heap-overflow.
  if (bytes_needed / 4 > HEAP_SIZE) {
    fprintf(stderr, "Allocation error: needed %d words, but the heap is only %d words\n",
            bytes_needed / 4, HEAP_SIZE);
    fflush(stderr);
    if (new_heap != NULL) free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  } else if((new_esi + (bytes_needed / 4)) > HEAP_END) {
    fprintf(stderr, "Out of memory: needed %d words, but only %d remain after collection\n",
            bytes_needed / 4, (HEAP_END - new_esi));
    fflush(stderr);
    if (new_heap != NULL) free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  } else {
    /* fprintf(stderr, "new_esi = %p\n", new_esi); */
    /* naive_print_heap(HEAP, HEAP_END); */
    return new_esi;
  }
}

int main(int argc, char** argv) {
  HEAP_SIZE = 100000;
  if (argc > 1) { HEAP_SIZE = atoi(argv[1]); }
  if (HEAP_SIZE < 0 || HEAP_SIZE > 1000000) { HEAP_SIZE = 0; }
  HEAP = (int*)calloc(HEAP_SIZE + 7, sizeof (int));

  int* aligned = (int*)(((int)HEAP + 7) & ~0x7);
  HEAP_END = aligned + HEAP_SIZE;
  /* printf("HEAP = %p, aligned = %p, HEAP_END = %p\n", HEAP, aligned, HEAP_END); */
  int result = our_code_starts_here(aligned);
  /* smarter_print_heap(aligned, HEAP_END, TO_S, TO_E); */
  print(result);

  free(HEAP);
  return 0;
}

