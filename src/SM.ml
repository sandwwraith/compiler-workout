open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env cfg prog = List.fold_left eval1 cfg prog
  and eval1 cfg cmd = let (stack, (state, input, output)) = cfg in match cmd with
    | BINOP op -> (
      match stack with
        | op1::op2::tail -> let result = Expr.makeBinOp op op2 op1 in
          (result::tail, (state, input, output))
        | _ -> failwith "Not enough operands on stack"
    )
    | CONST i -> (i::stack, (state, input, output))
    | READ -> (
      match input with
      | head::tail -> (head::stack, (state, tail, output))
      | _ -> failwith "Not enough input to consume"
    )
    | WRITE -> (
      match stack with
        | head::tail -> (tail, (state, input, output@[head]))
        | _ -> failwith "Not enough operands on stack"
    )
    | LD name -> let var = state name in (var::stack, (state, input, output))
    | ST name -> (
      match stack with
        | head::tail -> (tail, (Expr.update name head state, input, output))
        | _ -> failwith "Not enough operands on stack"
    )

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

open Expr
open Stmt

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

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