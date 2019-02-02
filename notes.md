## Expression with tags
```ocaml
let rec tag (expr : 'a expr) (t : tag) : (tag expr * tag)
```

## Evaluate binary operations
(2+3)+1

```assembly
mov eax 2
add eax 3
add eax 1
```
(2+3)*(5-4)
```assembly
mov eax 2
add eax 3
mov [esp-4] eax
mov eax 5
sub eax 4
mov [esp-8]
mov eax [esp-4]
...?
```
Convert to let expressions.
It encodes the execution order of the code. 
```ocaml
let temp1 = 2 + 3 in
  let temp2 = 5 - 4 in
    temp1 * temp2
````
Put $ before the temp variable name to avoid naming collisions.

Check if an expression is ready
```ocaml
let rec isANF e = 
  match e with
  | Num (_) | Id (_) -> true
  | Let (binds, body) -> List.for_all (fun (_, bind) -> isANF bind)) binds && isANF body
  | Prim1 (_, e1) -> isANF e1
  | Prim2 (_, e1, e2) -> isANF e1 && is_immediate e2 

let is_immediate e = 
  match e with
  | Num (_) | Id (_) -> true
  | _ -> false

```
To make the ANF unique, add the requirement: on the right-hand of any binding, there is atmost one operation.
```ocaml
let rec isANF e = 
  match e with
  | Num (_) | Id (_) -> true
  | Let (binds, body) -> List.for_all (fun (_, bind) -> isANF bind)) binds && isANF body
  | Prim1 (_, e1) -> is_immediate e1
  | Prim2 (_, e1, e2) -> is_immediate e1 && is_immediate e2 
```
How to produce an ANF?
Translate an expression to ANF. tag information is discarded because the tree is transformed.
Create a helper function: take a tree, return a tuple of an immediate value and a list of bindings that are required to get that immediate.
```ocaml
let rec anf (e : tag expr) : unit expr = 
  let rec_helper (e : tag expr) : (unit expr * binding list) = 
      match e with
      | Num (n) -> (Num n, [])
      | Id x -> (id x, [])
      | Prim2 (op, e1, e2) -> let (e1_anf, e1_ctxt) = helper e1 in
                              let (e2_anf, e2_ctxt) = helper e2 in
                              let temp = sprintf "$temp_%d" tag in
                              (Id(temp), e1_ctxt @ e2_ctxt)
...                                                           
```
Handle the body of if expressions. To avoid code duplication, split ANF into three levels: 
immediates, let-able, complex expressions.
Allow if to be let-ables. 

ANF is equivalent to SSA and CPS. 

## Add booleans to the language

```ocaml
type expr = 
| Num of int
| Bool of bool
| Prim1 ...
| Prim2 ...
| Let 
| If 
```
32 bits, reserve 1 bit to distinguish bool and int. 
use the least significant bit, 0 for int and 1 for bool.

### Representation of int
translate(n1 + n2) = translate(n1) + translate(n2)
use translate function to convert number to tagged value.
1 -> 2
5 -> 10
6 -> 12
...
translate: left-shift by 1 bit (lsl)
addition
multiplication can be implemented by mul and shift to the right
shr
sar: shift arithmeticaly, perserves sign.

comparing numbers: =, !=, >, <, ... still works
but needs to produce a boolean value.


### Representation of bool
Use the most significant bit, 1 for true and 0 for false.
true: 0x80000001
false: 0x00000001
Operators on boolean can be implemented:
and -> bitwise and, the tag is preserved
or  -> bitwise or, the tag is preserved
not -> xor with 0x80000000

### type checking

1. static time: adding a new phase to check types
should be done after scope check and before anf.

2. run time: should print a error message.
run time function to handle errors: can be called with an error code. 

Next steps: 
tagging values, calling functions, run-time function.

tagging allows garbage collection.

### Compiling with tagged values

```
a < b
```
Use assembly instruction: cmp 
The result is stored in a flag register. 

```assembly
mov EAX [ESP-4] ;load a
cmp EAX [ESP-8] ;compare with b
mov EAX 0x80000001 ;true
jl  done           ;jump less than
mov EAX 0x00000001 ;false
```

An alternative way to get the right answer.
However it fails when there is overflow
```
mov EAX [ESP-4]
sub EAX [ESP-8]
and EAX 0x80000000
or  EAX 0x00000001 ;covert the result to boolean
```
min_int: 0x80000000
max_int: 0x7ffffffe
min_int > max_int = true with the above implementation.

Compiling add1(x). 
We need to check the operand is a number.
```assembly
mov  EAX _
test EAX 0x00000001 ;check it is a number
jnz  error
add  EAX 0x1
```
if the operand is not a number, call a function to print an error message.

```c
/* main.c */
const int E_NOT_INT = 1;
int error(int code) {
  if(code == E_NOT_INT) {
    printf("Not int\n")
    exit(1);
  } else {}
}
```

### Calling convention of x86
When calling a function, push the arguments in reverse order.
```
...
local_2
local_1 <- ESP
arg_1
arg_2
arg_3
...
```

Count the number of local variables.

Use register EBP
```
locals <- ESP-4
EBP    <- ESP
----
return adress <- ESP+4
args 
```
Calling steps:
Caller: 
- set up arguments (use `push` instruction, `push EAX`)
- set up the return address (`call` instruction does this)

Callee: 
- push the value of EBP to stack (save the EBP value the caller is using)
- save ESP to EBP
- reserve N slots

the stack after callee setting EBP
```
locals <- ESP, EBP
EBP    
----
return adress 
args 
```

Return steps:
callee:
- restore ESP from EBP
- pop saved EBP from stack
- return

caller:
- pop off arguments (use the `add` instruction, e.g. `add ESP 4`)

