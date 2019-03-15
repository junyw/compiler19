open Exprs
open Errors
open Printf
open Pretty
open Phases

let show_debug_print = ref false
let debug_printf fmt =
  if !show_debug_print
  then printf fmt
  else ifprintf stdout fmt
;;