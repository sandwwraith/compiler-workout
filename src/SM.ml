open GT

open Syntax
open Stmt
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval cfg prog = List.fold_left eval1 cfg prog
  and eval1 cfg cmd = let (stack, (state, input, output)) = cfg in match cmd with 
    | BINOP op -> (
      match stack with 
        | op1::op2::tail -> let result = Expr.eval Expr.empty (Binop (op, (Const op2), (Const op1))) in 
          (result::tail, (state, input, output))
        | _ -> failwith "Not enough operands on stack"
    )
    | CONST i -> (i::stack, (state, input, output))
    | READ -> (
      match input with
      | x::tail -> (x::stack, (state, input, output))
      | _ -> failwith "Not enough input to consume"   
    )
    | WRITE -> (
      match stack with
        | h::tail -> (tail, (state, input, output@[h]))
        | _ -> failwith "Not enough operands on stack"
    ) 
    | LD name -> let var = state name in (var::stack, (state, input, output))
    | ST name -> (
      match stack with
        | h::tail -> (tail, (Expr.update name h state, input, output))
        | _ -> failwith "Not enough operands on stack"
    )

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile stmt = match stmt with
  | Read name -> [READ; ST name]
  | Write expr -> (compile_expr expr)@[WRITE]
  | Assign (x, expr) -> (compile_expr expr)@[ST x]
  | Seq (t1, t2) -> (compile t1)@(compile t2)
  and compile_expr expr = match expr with 
    | Expr.Const n -> [CONST n]
    | Expr.Var x -> [LD x]
    | Expr.Binop (op, arg1, arg2) -> (compile_expr arg1)@(compile_expr arg2)@[BINOP op]
