open OUnit2
open Functions

(* This file contains some example tests.  Feel free to delete and reorganize
the unnecessary parts of this file; it is provided to match up with the given
writeup initially. *)

let check_fun _ = (* a function of one argument containing a successful test *)
  assert_equal (2 + 2) 4;;

let check_fun2 _ = (* a failing test *)
  assert_equal (2 + 2) 5;;

(* a helper for testing integers *)
let t_int name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:string_of_int);;

(* a helper for testing strings *)
let t_string name value expected = name>::
	(fun _ -> assert_equal expected value ~printer:(fun x -> x))

(* a helper for testing lists *)
let t_list name value expected = name>::
	(fun _ -> assert_equal expected value)

(* Feel free to add any new testing functions you may need *)

let my_first_test = "my_first_test">::check_fun;;
let my_second_test = "my_second_test">::check_fun2;;
let my_third_test = t_int "my_third_test" (2 + 2) 7;;
let my_fourth_test = t_int "my_fourth_test" (2 + 2) 4;;

let my_string_test = t_string "my_string_test" (String.uppercase_ascii "ocaml") "OCAML"

let fibonacci_zero = t_int "fibonacci_zero_test" (fibonacci 0) 0;;
let fibonacci_one = t_int "fibonacci_one_test" (fibonacci 1) 1;;
let fibonacci_12 = t_int "fibonacci_12_test" (fibonacci 12) 144;;

let max_4_3 = t_int "max_4_3_test" (max 4 3) 4;;
let max_4_4 = t_int "max_4_3_test" (max 4 4) 4;;

(* binary tree *)
let tree0 = Leaf
let tree1 = Node("a", Leaf, Leaf)
let tree2 = Node("b", tree1, Leaf)
let tree3 = Node("c", tree2, Node("d", Leaf, Leaf))
(* evaluation of inorder_str on tree3
 * inorder_str tree3
 * inorder_str tree2 + "c" + inorder_str Node("d", Leaf, Leaf)
 * inorder_str Node("b", tree1, Leaf) + "c" + inorder_str Node("d", Leaf, Leaf)
 * inorder_str tree1 + "b" + inorder Leaf + "c" + inorder_str Leaf + "d" + inorder_str Leaf
 * "a" + "b" + "c" + "d"
 * "abcd" 
 * *)
let tree4 = Node("e", tree0, tree3)

let tree_0 = t_string "binary_tree_0" (inorder_str tree0) "";;
let tree_1 = t_string "binary_tree_1" (inorder_str tree1) "a";;
let tree_2 = t_string "binary_tree_2" (inorder_str tree2) "ab";;
let tree_3 = t_string "binary_tree_3" (inorder_str tree3) "abcd";;
let tree_4 = t_string "binary_tree_4" (inorder_str tree4) "eabcd";;

let tree_0_size = t_int "binary_tree_0_size" (size tree0) 0;;
let tree_1_size = t_int "binary_tree_1_size" (size tree1) 1;;

let tree_0_height = t_int "binary_tree_0_height" (height tree0) 0;;
let tree_1_height = t_int "binary_tree_1_height" (height tree1) 1;;

(* list *)
let list_0 = [];;
let list_1 = [1;2;3;4];;

let list_0_inc = t_list "" (increment_all []) [];;
let list_1_inc = t_list "" (increment_all list_1) [2;3;4;5];;

let strlist_0 = [];;
let strlist_1 = ["a";"ab";"abc";"abcd"];;

let strlist_0_0 = t_list "" (long_strings strlist_0 0) [];;
let strlist_1_1 = t_list "" (long_strings strlist_1 1) ["ab";"abc";"abcd"];;
let strlist_1_2 = t_list "" (long_strings strlist_1 2) ["abc";"abcd"];;

let list_list_0 = [[];[2;3;4];[1];[5;6]];;
let sum_all_0 = t_list "" (sum_all list_list_0) [0;9;1;11];;

let every_other_0 = t_list "every_other_0" (every_other []) [];;
let every_other_1 = t_list "every_other_1" (every_other [1;2;3]) [1;3];;
let every_other_2 = t_list "every_other_2" (every_other [1;2;3;4;5;6]) [1;3;5];;

let suite = "suite">:::[
my_first_test;
  (* my_second_test; *)
  (* my_third_test; *)
  (* my_fourth_test; *)
  my_string_test;
  fibonacci_zero;
  fibonacci_one;
  fibonacci_12;
  max_4_3;
  max_4_4;
  tree_0;
  tree_1;
  tree_2;
  tree_3;
  tree_4;
  tree_0_size;
  tree_1_size;
  tree_0_height;
  tree_1_height;
  list_0_inc;
  list_1_inc;
  strlist_0_0;
  strlist_1_1;
  strlist_1_2;
  sum_all_0;
  every_other_0;
  every_other_1;
  every_other_2;
  (* add more tests here *)
  ];;

run_test_tt_main suite
