#include <stdio.h>
#include <string.h>
#include "gc.h"

void naive_print_heap(int* heap, int* heap_end) {
  int size = (int)heap_end - (int)heap;
  for(int* cur = heap; cur <= heap_end; cur++) {
    printf("  %p: %p ", cur, (int*)(*cur));
    printHelp(stdout, *cur);
    printf("\n");
  }
}

// Implement the functions below

void smarter_print_heap(int* from_start, int* from_end, int* to_start, int* to_end) {
  // Print out the entire heap (both semispaces), and
  // try to print values readably when possible
  printf("from-space\n");  
  naive_print_heap(from_start, from_end);
  printf("to-space\n");
  naive_print_heap(to_start, to_end);
}

/*
  Copies a Garter value from the given address to the new heap, 
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter value,
                     i.e. a tagged word.  
                     It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at 
    its old location (on the heap) with a forwarding pointer to its new location, 
    and replace the value at garter_val_addr (on the stack) with the new location in 
    to-space, with tagging

 */
int* copy_if_needed(int* garter_val_addr, int* heap_top) {
  

  printf("copy_if_needed\n");
  printf("garter_val_addr = %p, heap_top = %p\n", garter_val_addr, heap_top);
  
  int garter_val = *garter_val_addr;

  printf("the value being examined = ");  
  printHelp(stdout, garter_val);
  printf("\n");

  // If garter_val is a primitive (number or boolean), 
  // return the unchanged heap_top; nothing needs to be allocated.
  if (garter_val == NIL) {
    printf("value is nil - no copy is needed\n");
    return heap_top;
  }
  else if((garter_val & NUM_TAG_MASK) == NUM_TAG) {
    printf("value is number - no copy is needed\n");
    return heap_top;
  }
  else if(garter_val == BOOL_TRUE) {
    printf("value is true - no copy is needed\n");
    return heap_top;
  }
  else if(garter_val == BOOL_FALSE) {
    printf("value is false - no copy is needed\n");
    return heap_top;
  }

  // If garter_val is a (tagged) pointer to a heap-allocated Garter value (tuple or closure): 
  // Call the pointed-to value heap_thing, such that untag(garter_val) = heap_thing_addr, then
  else if ((garter_val & TUPLE_TAG_MASK) == TUPLE_TAG) {
    int* heap_thing_addr = (int*)(garter_val - 1);
    int  heap_thing = garter_val;
    
    printf("heap_thing_addr = %p\n", heap_thing_addr);
    printf("heap_thing = ");
    printHelp(stdout, heap_thing);
    printf("\n");
    
    // 1. Copy the full contents of heap_thing to heap_top.
    int len = heap_thing_addr[0]; // encoded length
    if (len & 0x1) { // actually, it's a forwarding pointer
      fprintf(stdout, "forwarding to %p", (int*)(len - 1));
      return heap_top;
    }
    len = len / 2; // real length of the tuple 
    int heap_thing_size = (1 + len) * 4 /* 4 bytes */;
    int* memcpy_dest = heap_top;
    int* memcpy_src = heap_thing_addr;
    memcpy(memcpy_dest, memcpy_src, heap_thing_size);

    // 2. Update the value at garter_val_addr with the value of heap_top.
    // needs to be tagged
    *garter_val_addr = (int)heap_top + 0x1;
    // 3. Replace the value at heap_thing_addr (i.e., the location referred to by garter_val) with a forwarding pointer to heap_top.
    *heap_thing_addr = (int)heap_top + 0x3;
    // 4. Increment heap_top as needed to record the allocation.
    heap_top += 1 + len;
    printf("new heap_top %p\n", heap_top);
    // 5. For each field within heap_thing at the new location, recursively call copy_if_needed. (Be careful about using the return value of those calls correctly!)
    
    // 6. Return the current heap_top.
    return heap_top;

  }
  else if ((garter_val & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
    //TODO
    return heap_top;
  }
  // If garter_val is a (tagged) pointer to a heap_thing that is now a forwarding pointer, 
  // replace the value at  garter_val_addr with the appropriately tagged version of 
  // that forwarding pointer. Return the unchanged heap_top.


  // no-op for now
  return heap_top;
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Garter frame
    top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
int* gc(int* bottom_frame, int* top_frame, int* top_stack, int* from_start, int* from_end, int* to_start) {
  printf("gc\n");
  printf("bottom_frame = %p, top_frame = %p, top_stack = %p\n", bottom_frame, top_frame, top_stack);
  for (int* cur_word = top_stack /* maybe need a +1 here? */; cur_word < top_frame; cur_word++) {
    to_start = copy_if_needed(cur_word, to_start);
  }

  if (top_frame < bottom_frame)
    to_start = gc(bottom_frame,
                  (int*)(*top_frame), // [top_frame] points to the saved EBP, which is the next stack frame
                  top_frame + 2 * 4 /* word_size = 4 */,      
                                      // [top_frame+4] points to the return address
                                      // so [top_frame+8] is the next frame's stack-top
                  from_start,
                  from_end,
                  to_start); // to_start has been changed to include any newly copied data
  // after copying the remaining stack frames, return the new allocation starting point
  return to_start;       
}

