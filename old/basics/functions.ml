(* Fill in the functions you need to write here *)

let rec fibonacci (n : int) : int = 
	if n == 0 then 0
	else if n == 1 then 1
	else fibonacci(n-1) + fibonacci(n-2)
(*
 * fibonacci 3
 * fibonacci 2 + fibonacci 1
 * fibonacci 1 + fibonacci 0 + 1
 * 1 + 0 + 1
 * 2
 * *)


(* Binary Tree *)
type btnode = 
	| Leaf
	| Node of string * btnode * btnode

let rec inorder_str (btn : btnode) : string = 
	match btn with
		| Leaf -> ""
		| Node(s, left, right) -> (inorder_str left) ^ s ^ (inorder_str right)

let rec size (btn : btnode) : int =
	match btn with
		| Leaf -> 0
		| Node(s, left, right) -> (size left) + 1 + (size right)

let rec height (btn : btnode) : int =
	match btn with
		| Leaf -> 0
		| Node(s, left, right) -> max (height left) (height right) + 1

(* list *)
let increment_all (l : int list) : int list = 
	List.map (fun x -> x + 1) l

let long_strings (l : string list) (n : int) : string list = 
	List.filter (fun x -> String.length x > n) l

let every_other (l : 'a list) : 'a list = 
	let (a, b) = List.fold_left (fun (a,b) x -> if b mod 2 = 0 then (a@[x], b+1) else (a,b+1)) ([],0) l in
		a

let sum (l : int list) : int = 
	List.fold_left (fun acc x -> acc + x) 0 l

let sum_all (l : int list list) : int list = 
	List.map sum l

