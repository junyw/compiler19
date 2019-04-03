#ifndef MAIN_H
#define MAIN_H

extern const int NUM_TAG_MASK;
extern const int BOOL_TAG_MASK;
extern const int TUPLE_TAG_MASK;
extern const int CLOSURE_TAG_MASK;
extern const int NUM_TAG;
extern const int BOOL_TAG;
extern const int TUPLE_TAG;
extern const int CLOSURE_TAG;
extern const int BOOL_TRUE;
extern const int BOOL_FALSE;
extern const int NIL;

void printHelp(FILE *out, int val);

#endif /* MAIN_H */
