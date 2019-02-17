Tail-call optimization is implemented for 
1. self-recursive tail-calls.
2. arbitrary tail-calls, when the number of arguments is the same between caller and callee.


On macos, esp should be 16-byte aligned before function calls. The '-mstackrealign' flag automatically aligns the stack.