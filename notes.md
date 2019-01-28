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




