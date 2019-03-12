open GT
open Language

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
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)
let rec eval cfg prog = List.fold_left eval1 cfg prog
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
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
