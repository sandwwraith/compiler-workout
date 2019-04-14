open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env ((controls, stack, ((state, input, output) as world)) as cfg) prog = match prog with
  | [] -> cfg
  | cmd :: rest -> 
    let cont c = eval env c rest in
    let jmp c l = eval env c (env#labeled l) in
    match cmd with
    | BINOP op -> cont (
      match stack with
        | op1::op2::tail -> let result = Expr.makeBinOp op (Value.to_int op2) (Value.to_int op1) in
          (controls, (Value.of_int result)::tail, world)
        | _ -> failwith "Not enough operands on stack BINOP"
    )
    | CONST i -> cont (controls, (Value.of_int i)::stack, world)
    | STRING s -> cont (controls, (Value.of_string s)::stack, world)
    | LD name -> let var = State.eval state name in cont (controls, var::stack, world)
    | ST name -> cont (
      match stack with
        | head::tail -> (controls, tail, (State.update name head state, input, output))
        | _ -> failwith "Not enough operands on stack ST"
    )
    | STA (name, size) -> cont (
      let (value::idxs), stack = split (size + 1) stack in 
      (controls, stack, (Stmt.update state name value idxs, input, output))
    )
    | LABEL l -> cont cfg
    | JMP l -> jmp cfg l
    | CJMP (cond, l) -> (
      match stack with
        | head :: tail -> (
          let newcfg = (controls, tail, world) in
          match cond with
            | "z"  -> if (not (Value.to_bool head)) then jmp newcfg l else cont newcfg
            | "nz" -> if (Value.to_bool head)       then jmp newcfg l else cont newcfg
            | _ -> failwith "Incorrect operand for CJMP"
        )
        | _ -> failwith "Not enough operands on stack CJMP"
    )
    | CALL (f, arg_cnt, is_func) ->  if env#is_label f 
      then eval env ((rest, state)::controls, stack, world) (env#labeled f)
      else eval env (env#builtin cfg f arg_cnt (not is_func)) rest 
    | BEGIN (_, params, locals) -> 
      let state' = State.enter state (params @ locals) in
      let restore_seq = List.map (fun p -> ST p) params in
      let cfg' = eval env (controls, stack, (state', input, output)) restore_seq in
      eval env cfg' rest
    | (RET _ | END) -> (match controls with
      | (ret, ret_state)::controls_rest -> 
        let state' = State.leave state ret_state in
        eval env (controls_rest, stack, (state', input, output)) ret
      | _ -> cfg
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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machinelet compile (defs, p) = failwith "Not implemented"
*)
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
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile (defs, main) = 
let rec compile_expr expr =
let compile_call name args = (List.flatten @@ List.map compile_expr (List.rev args)) @ [CALL (name, List.length args, true)] in
match expr with
    | Expr.Const n -> [CONST n]
    | Expr.Var x -> [LD x]
    | Expr.Array args -> compile_call "$array" (List.rev args)
    | Expr.String s -> [STRING s]
    | Expr.Elem (a, i) -> compile_call "$elem" [i;a]
    | Expr.Length a -> compile_call "$length" [a]
    | Expr.Binop (op, arg1, arg2) -> (compile_expr arg1)@(compile_expr arg2)@[BINOP op]
    | Expr.Call (f, args) -> compile_call f args
in
let rec opt_if expr outer_label = match expr with
  | Seq (s1, s2) -> (compile_stmt s1)@(opt_if s2 outer_label)
  | If (cond, zen, elze) -> 
    let l_else = label_generator#gen in
    compile_expr cond
    @ [CJMP ("z", l_else)]
    @ opt_if zen outer_label
    @ [JMP outer_label]
    @ [LABEL (l_else)]
    @ compile_stmt elze
  | _ -> compile_stmt expr
and compile_stmt stmt = match stmt with
  | Assign (x, idxs, expr) -> (match idxs with
    | [] -> (compile_expr expr)@[ST x]
    | _ -> (List.flatten @@ List.map compile_expr (List.rev idxs))@(compile_expr expr)@[STA (x, List.length idxs)]
  )
  | Seq (t1, t2) -> (compile_stmt t1)@(compile_stmt t2)
  | Skip -> []
  | If (cond, zen, elze) -> let l_out = label_generator#gen in (opt_if stmt l_out)@[LABEL l_out]
  | While (cond, action) -> let l_check, l_loop = label_generator#gen2 in 
    [JMP l_check]
    @ [LABEL l_loop]
    @ (compile_stmt action)
    @ [LABEL l_check]
    @ (compile_expr cond)
    @ [CJMP ("nz", l_loop)]
  | Repeat (action, cond) -> let l_check, l_loop = label_generator#gen2 in
    [LABEL l_loop]
    @ (compile_stmt action)
    @ [LABEL l_check]
    @ (compile_expr cond)
    @ [CJMP ("z", l_loop)]
  | Call (f, args) -> (List.flatten @@ List.map compile_expr (List.rev args)) @ [CALL (f, List.length args, false)]
  | Return r -> (match r with
    | Some e -> (compile_expr e) @ [RET true]
    | _ -> [RET false]
    )
and compile_def (name, (params, locals, body)) = 
  let body = compile_stmt body in
  [LABEL name; BEGIN (name, params, locals)] @ body @ [END]
in
let defs = List.flatten @@ List.map compile_def defs in
let main = compile_stmt main in
main @ [END] @ defs
