open Printf

(* Abstract syntax of (a small subset of) x86 assembly instructions *)
let word_size = 4
;;

type reg =
  | EAX
  | ECX
  | EDX
  | ESP
  | EBP
  | ESI
  | CL

type size =
  | DWORD_PTR
  | WORD_PTR
  | BYTE_PTR

type directive = 
  | DB
  | DW
  | DD

type arg =
  | Const of int
  | HexConst of int
  | Reg of reg
  | RegOffset of int * reg (* int is # words of offset *)
  | RegOffsetReg of reg * reg * int * int
  | Sized of size * arg
  | Label of string
  | LabelContents of string

type instruction =
  | IMov of arg * arg

  | IAdd of arg * arg
  | ISub of arg * arg
  | IMul of arg * arg

  | IShl of arg * arg
  | IShr of arg * arg
  | ISar of arg * arg

  | IAnd of arg * arg
  | IOr of arg * arg
  | IXor of arg * arg

  | ILabel of string
  | IPush of arg
  | IPop of arg
  | ICall of arg
  | IRet

  | ICmp of arg * arg
  | ITest of arg * arg
  | IJo of arg
  | IJno of arg
  | IJe of arg
  | IJne of arg
  | IJl of arg
  | IJle of arg
  | IJg of arg
  | IJge of arg
  | IJmp of arg
  | IJz of arg
  | IJnz of arg

  | IVar of string * directive * int

  | ILineComment of string
  | IInstrComment of instruction * string


let r_to_asm (r : reg) : string =
  match r with
  | EAX -> "eax"
  | ESP -> "esp"
  | EBP -> "ebp"
  | ESI -> "esi"
  | ECX -> "ecx"
  | EDX -> "edx"
  | CL -> "cl"

let rec arg_to_asm (a : arg) : string =
  match a with
  | Const(n) -> sprintf "%d" n
  | HexConst(n) -> sprintf "0x%lx" (Int32.of_int n)
  | Reg(r) -> r_to_asm r
  | RegOffset(n, r) ->
     if n >= 0 then
       sprintf "[%s+%d]" (r_to_asm r) n
     else
       sprintf "[%s-%d]" (r_to_asm r) (-1 * n)
  | RegOffsetReg(r1, r2, mul, off) ->
     sprintf "[%s + %s * %d + %d]"
             (r_to_asm r1) (r_to_asm r2) mul off
  | Sized(size, a) ->
     sprintf "%s %s"
             (match size with | DWORD_PTR -> "DWORD" | WORD_PTR -> "WORD" | BYTE_PTR -> "BYTE")
             (arg_to_asm a)
  | Label s -> s
  | LabelContents s -> sprintf "[%s]" s
;;

let rec i_to_asm (i : instruction) : string =
  match i with
  | IMov(dest, value) ->
     sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd(dest, to_add) ->
     sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | ISub(dest, to_sub) ->
     sprintf "  sub %s, %s" (arg_to_asm dest) (arg_to_asm to_sub)
  | IMul(dest, to_mul) ->
     sprintf "  imul %s, %s" (arg_to_asm dest) (arg_to_asm to_mul)
  | ICmp(left, right) ->
     sprintf "  cmp %s, %s" (arg_to_asm left) (arg_to_asm right)
  | ILabel(name) ->
     name ^ ":"
  | IJo(dest) ->
     sprintf "  jo near %s" (arg_to_asm dest)
  | IJno(dest) ->
     sprintf "  jno near %s" (arg_to_asm dest)
  | IJe(dest) ->
     sprintf "  je near %s" (arg_to_asm dest)
  | IJne(dest) ->
     sprintf "  jne near %s" (arg_to_asm dest)
  | IJl(dest) ->
     sprintf "  jl near %s" (arg_to_asm dest)
  | IJle(dest) ->
     sprintf "  jle near %s" (arg_to_asm dest)
  | IJg(dest) ->
     sprintf "  jg near %s" (arg_to_asm dest)
  | IJge(dest) ->
     sprintf "  jge near %s" (arg_to_asm dest)
  | IJmp(dest) ->
     sprintf "  jmp near %s" (arg_to_asm dest)
  | IJz(dest) ->
     sprintf "  jz near %s" (arg_to_asm dest)
  | IJnz(dest) ->
     sprintf "  jnz near %s" (arg_to_asm dest)
  | IAnd(dest, value) ->
     sprintf "  and %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IOr(dest, value) ->
     sprintf "  or %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IXor(dest, value) ->
     sprintf "  xor %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShl(dest, value) ->
     sprintf "  shl %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShr(dest, value) ->
     sprintf "  shr %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | ISar(dest, value) ->
     sprintf "  sar %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IPush(value) ->
     sprintf "  push %s" (arg_to_asm value)
  | IPop(dest) ->
     sprintf "  pop %s" (arg_to_asm dest)
  | ICall(label) ->
     sprintf "  call %s" (arg_to_asm label)
  | IRet ->
     "  ret"
  | ITest(arg, comp) ->
     sprintf "  test %s, %s" (arg_to_asm arg) (arg_to_asm comp)
  | IVar(name, directive, value) ->
     let size = match directive with DB -> "DB" | DW -> "DW" | DD -> "DD" in
     sprintf "%s    %s %d" name size value
  | ILineComment(str) ->
     sprintf "  ;; %s" str
  | IInstrComment(instr, str) ->
     sprintf "%s ; %s" (i_to_asm instr) str

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is
