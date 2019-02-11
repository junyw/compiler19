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
```
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

## Function definition
Use an Environment to map function name to a number(arity).

Scoping rule for functions.

Cases that needs to be considered:

Functions with same names.
Functions with same names but different arity.
Recursive functions and mutually recursive functions.
Local function declarations.
Same argument names, e.g. f(x, x).

## Diamond-back changes (https://gist.github.com/nik-sm/c65e8db254d1b8dfe890cfac7e34cacd)

First item - Improving the ability to debug.

We will try to give ourselves the ability to print all stages of the compilation and all intermediate representations.

To do this, we will define a new data type.

Below is a sketch of how we will engineer this:

    type phase = 
    | Source of string
    | Parsed of sourcespan expr
    | Anfed of sourcespan expr
    | Tagged of tag expr
    | ...
    | FinalResult of instruction list

    let string_of_phase = 
    ...


    We would also like to record all phases of our pipeline.
    We need to be able to represent failures (we have been throwing exceptions)

    type failure = exn list * phase list
    (* The list of exceptions we got, and the list of phases that succeeded up to that point *)
    (* We could use a CompileError type that we define instead of "exn", and give this appropriate constructors *)

    type 'a pipeline = (failure * ('a * phase list)) either 
    (* Idiomatically, we use Right to represent a success. Here, right is some intermediate result from the compiler *)


    Finally, we need to be able to able to take in a pipeline (which has a few stages), and return another pipeline extended by one more stage/failure

    Note the pipeline operator:

    x |> f |> g ...

    says apply f to x, then apply g to that result, etc


    At the end of the day, we want to do:

    'a pipeline -> 'b pipeline

    let add_phase (log: 'b -> phase) (next: 'a -> 'b pipeline) (trace: 'a pipeline) : 'b pipeline =
    ...

    (Right source)
    |> (add_phase tag_parse parse)  (* tag_parse takes a string and makes a Source of that string *)
    |> (add_phase tag_tagged tag)   (* tag_tagged takes a Source and makes an expr of that *)
    |> (add_phase tag_anfed anf)

    (* Notice that the 3rd argument is the output from the previous pipeline operator *)
    (*  NOTE: use parens here! The precedence rules are very fragile for this operator *)

    Instead of throwing an exception, we'll pass it back as a Left(...).
    This will still be used to stop execution, though


    Sometimes, we should be able to detect ALL of a certain type of error.
    - Find and collect all unbound variables, all instances of shadowing, etc.

    Notice that OCaml stops and gives just one type error - this is because after having one problematic type inference, all downstream inferences may be junk.



Previously:

  We talked about calling conventions and how to call an error function in our C runtime.
  We went over the bookkeeping involved with passing arguments, and managing ESP and EBP.


Now - calling arbitrary functions. At the moment, the only possible place where functions might live is in our C runtime.

Currently, we only have the "error" function - the user writing an input program cannot directly call this function.
(Though they can CAUSE an error that results in the call of this function)

We have Prim1's, that resemble function calls. 
  We can try to re-use Prim1 for invoking functions
  We can also add a new expression form to handle function calls.


type 'a expr
| ECall of string * 'a expr list * 'a
          (* expr *)

    Digression on variable arity, lists, and trees:
      "First child, next sibling" representation of trees

    type 'a bt = 
    | Node of 'a * 'a list * 'a bt
    | Leaf


    type 'a rose =
    | Node of 'a * 'a rose list



We have changed the syntax of our language. Our recipe for changes, as always, is:
- New concrete syntax examples
- Add support for this at each phase of our compiler
- This will affect ANF conversion. Calling a function requires loading args on the stack. We can only load an immediate value
    We have to decide now whether our semantics for function calling is EAGER or LAZY
    We also have to decide the order of evaluation.
    Unspecified order of evaluation probably means the compiler designer was lazy.
    We COULD make the argument for unspecified evaluation - in this case, provide a special expression form so the program writer knows
- This will affect code generation (pushing args on the stack, etc)
- Resolving function names - this could be handled in our "check_scope" function
- We need to be sure that the function is called with the correct # of args
- Type-checking the function arguments (could handle this at runtime, the function could check the "tag" bits of the args)
    The type checking could be done at every invocation of the function (but this will be duplicated code).
    Ideally, this check should be in the callee
    Even better would be to have a static type system... To be discussed later...


Overall, we have 2 pieces of info:
  Signature of the function, including types
  Arity of function. 

When should we do the name resolution?
  Before ANF - we saw that ANF can change scopes, so we should check this before modifying scopes.
  We want to still have source location info so we can give useful info

Notice we now have 2 environments:
  The LET bindings (name <-> stack_index)
  The available function names (name <-> arity)

  Do we have one shared namespace or two distinct name-spaces?
  In order to have first-class functions, we need to have a shared namespace. (To be discussed later...)

  LISP:
    LISP-1 has 1 unified namespace
    LISP-2 has variable namespace and function namespace

We'll simply replace the stage of "check_scope" with a "well-formed" check

Parsing problems:
  Looking at 
  "f(4+2) * 3", why is this not broken into:
  "f" and "(4+2) * 3"

  We will handle this by being sensitive to the whitespace:
  "f(" different from "f ("


Are we done with Prim1's after we implement function calls?
  Our function calls will become many lines of generated code, and having baked-in Prim1's will be more efficient
  It will only be worthwhile to keep Prim1's for a select few operations (negation, ++, etc)


Notice that the handling of ANF for ELet will be very similar to how we handle ANF conversion for ECall

## Typed ANF

Define the immediate types:

```ocaml
type immexpr = 
  | ImmNum of int
  | ImmBool of bool
  | ImmId of string
```
And the ANF expression.

First try:
```ocaml
type aexpr = 
  | EPrim1 of prim1 * immexpr
  | EPrim2 of prim2 * immexpr * immexpr
  | EIf of immexpr * aexpr * aexpr
  | ELet of string * aexpr (* get rid of multiple bindings *)
  | EImm of immexpr
```
We can improve this by making some changes.
```ocaml
(* compound expressions *)
(* can go to right side of bindings *)
type cexpr = 
  | CPrim1 of prim1 * immexpr
  | CPrim2 of prim2 * immexpr * immexpr
  | CIf of immexpr * aexpr * aexpr
  | CImm of immexpr

type aexpr = 
  | ALet of string * cexpr
  | ACexpr of cexpr
```
```ocaml
let anf e = 
  let helpI (e : expr) (imm * (string * cexpr) list) =
  match e with
  | Prim1(op, e) -> let (ans, ctxt) = helpI e (* because ans must be immediate *)
                    let temp = ...
                    (temp, ctxt @ [(temp, CPrint1(..))])

  | _ -> ...
  and helpC (e : expr) (cexpr * (string * cexpr) list) = 
  ...
```
Example,
3 + 4
helpI returns a let binding.
but helpC returns 3 + 4

Adding functions to ANF
```ocaml
type aprogram = 
| AProg of defn list * aexpr
```

## Tail call
def fact(n):
  if n < 1 : 1
  else n * fact(n-1)

fact(2) call stack
```
   <- ESP (reserve space for local variables)



EBP
return address
2
```

call fact(1).
```
EBP
return address
1


1
false
EBP
ret addr
2
```

after call fact(1), restore EBP

```

2
1
1
false
EBP
ret addr
2
```
We can rewrite the program:
```
def fact_tail(n, acc):
    if n < 1 acc
    else fact()
```
call fact_tail(2):
```
2
1
```
then 
```
   <- ESP (reserve space for local variables)


EBP
ret addr
2
1
```

```
   <- ESP (reserve space for local variables)
1
2
false
EBP
ret addr
2
1
```
In self-recursion, the stack frame has the same structure.

An edge case:
```
def min(x, y)
  if x < y x
  else min(y, x)
```
call min(12, 10)

The stack is:

```
false
EBP
ret address
12
10 (* recursive call would turn 10 to 12 and lose the 10 value *)
```

tail-recursion of same arities
get tail-recursion of difference arities: call functions with greater arities.

## alpha-renaming
for cases like (let x = 1 in x) + (let x = 2 in x)

Use env (string to string) to keep track of renaming.
```ocaml
let rec renaming e env = 
match e with
| ...
| Id(name, tag) ->
| Let(binds, body, tag) ->  

```

## type rules

----------------
n : Int

----------------
true : Bool

----------------
false: Bool


e1: Bool e2: Bool
----------------
e1 and e2: Bool

e1: Int e2: Int
----------------
e1 + e2: Int

e1: Int e2: Int
----------------
e1 < e2: Bool


c: Bool t, f : tau
----------------
if c t f : tau

e : tau
----------------
isBool(e) : Bool

e : tau
----------------
print(e) : tau

e1 e2 : tau 
----------------
e1 == e2 : Bool

We have to introduce Γ as type environment.

Γ⊢ e: tau1     Γx: tau1⊢ b : tau2 
--------------------------------
Γ⊢ let x = e in b : tau2





To check the expression (if true then 1 else 2) + 3 : Int:

--------------------------------
⊢ (if true then 1 else 2) + 3: Int


⊢(if true then 1 else 2) : Int   ⊢3 : Int
--------------------------------
⊢ (if true then 1 else 2) : Int


⊢true:Bool ⊢1:Int ⊢2 Int
-------------------------        -------
⊢ (if true then 1 else 2) : Int   ⊢3 : Int
--------------------------------
⊢ (if true then 1 else 2) : Int


---------  -----  -----
⊢true:Bool ⊢1:Int ⊢2 Int
-------------------------        -------
⊢(if true then 1 else 2) : Int   ⊢3 : Int
--------------------------------
⊢ (if true then 1 else 2) : Int



Hindly-Milner type inference
let f g h x = h(g(h(x)))

```
f = lambda.g lambda.h lambda.x h(g(h(x)))
f : alpha
alpha = beta->gamma
g : beta
gamma = delta->epsilon
h : delta
epsilon = miu -> eta
x : miu

Because h is applied to x
delta = miu->theta
beta = ...
```

Then we can get the type of f:

forall theta, X, f : (theta->X)->(X->theta)->X->theta









