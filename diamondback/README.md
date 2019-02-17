## Tail-call
 
Tail-call optimization is implemented for 
1. self-recursive tail-calls.
2. arbitrary tail-calls, when the number of arguments is the same between caller and callee.

```bash
$ make output/even_odd.run
$ output/even_odd.run

$ make output/fact_tail.run
$ output/fact_tail.run
```

## Stack

On MacOS, esp should be 16-byte aligned before function calls. The '-mstackrealign' flag automatically aligns the stack.

