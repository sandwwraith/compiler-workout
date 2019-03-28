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

let rec eval env cfg prog = let (stack, (state, input, output)) = cfg in  match prog with
  | [] -> cfg
  | cmd :: rest -> 
    let cont c = eval env c rest in
    let jmp c l = eval env c (env#labeled l) in
    match cmd with
      | BINOP op -> cont (
        match stack with
          | op1::op2::tail -> let result = Expr.makeBinOp op op2 op1 in
            (result::tail, (state, input, output))
          | _ -> failwith "Not enough operands on stack BINOP"
      )
      | CONST i -> cont (i::stack, (state, input, output))
      | READ -> cont (
        match input with
        | head::tail -> (head::stack, (state, tail, output))
        | _ -> failwith "Not enough input to consume"
      )
      | WRITE -> cont (
        match stack with
          | head::tail -> (tail, (state, input, output@[head]))
          | _ -> failwith "Not enough operands on stack WRITE"
      )
      | LD name -> let var = state name in cont (var::stack, (state, input, output))
      | ST name -> cont (
        match stack with
          | head::tail -> (tail, (Expr.update name head state, input, output))
          | _ -> failwith "Not enough operands on stack ST"
      )
    | LABEL l -> cont cfg
    | JMP l -> jmp cfg l
    | CJMP (cond, l) -> (
      match stack with
        | head :: tail -> (
          let newcfg = (tail, (state, input, output)) in
          match cond with
            | "z"  -> if (head == 0) then jmp newcfg l else cont newcfg
            | "nz" -> if (head != 0) then jmp newcfg l else cont newcfg
            | _ -> failwith "Incorrect operand for CJMP"
        )
        | _ -> failwith "Not enough operands on stack CJMP"
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

let label_generator = object (this)
  val mutable cnt = 0
  method gen =
    cnt <- cnt + 1;
    "l" ^ (string_of_int cnt)
  
  method gen2 = 
    let one = this#gen in
    let two = this#gen in
    one, two

end 

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile stmt = 
let rec compile_expr expr = match expr with
    | Expr.Const n -> [CONST n]
    | Expr.Var x -> [LD x]
    | Expr.Binop (op, arg1, arg2) -> (compile_expr arg1)@(compile_expr arg2)@[BINOP op]
in
let rec opt_if expr outer_label = match expr with
  | Seq (s1, s2) -> (compile s1)@(opt_if s2 outer_label)
  | If (cond, zen, elze) -> 
    let l_else = label_generator#gen in
    compile_expr cond
    @ [CJMP ("z", l_else)]
    @ opt_if zen outer_label
    @ [JMP outer_label]
    @ [LABEL (l_else)]
    @ compile elze
  | _ -> compile expr
in
match stmt with
  | Read name -> [READ; ST name]
  | Write expr -> (compile_expr expr)@[WRITE]
  | Assign (x, expr) -> (compile_expr expr)@[ST x]
  | Seq (t1, t2) -> (compile t1)@(compile t2)
  | Skip -> []
  | If (cond, zen, elze) -> let l_out = label_generator#gen in (opt_if stmt l_out)@[LABEL l_out]
  | While (cond, action) -> let l_check, l_loop = label_generator#gen2 in 
    [JMP l_check]
    @ [LABEL l_loop]
    @ (compile action)
    @ [LABEL l_check]
    @ (compile_expr cond)
    @ [CJMP ("nz", l_loop)]
  | Repeat (action, cond) -> let l_check, l_loop = label_generator#gen2 in
    [LABEL l_loop]
    @ (compile action)
    @ [LABEL l_check]
    @ (compile_expr cond)
    @ [CJMP ("z", l_loop)]