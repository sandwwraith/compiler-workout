open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
(* drop values from stack and jmp  *) | ZJMPDROP of string * int
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
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
    | STRING s -> cont (controls, (Value.of_string (Bytes.of_string s))::stack, world)
    | SEXP (tag, cnt) -> 
      let values, rest = split cnt stack in
      let value = (Value.sexp tag (List.rev values)) in
      cont (controls, value::rest, world)
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
    | DROP -> cont (controls, (List.tl stack), world)
    | DUP -> cont (controls, (List.hd stack)::stack, world)
    | SWAP -> let x::y::stack' = stack in cont (controls, y::x::stack', world)
    | TAG t -> 
      let head::stack' = stack in 
      let res = match head with
        | Value.Sexp (t', _) when t = t' -> 1
        | _ -> 0
      in 
      cont (controls, (Value.of_int res)::stack', world)
    | LABEL l -> cont cfg
    | JMP l -> jmp cfg l
    | ZJMPDROP (l, cnt) -> 
      let head::stack' = stack in
      if (not (Value.to_bool head))
        then let (_, stack') = split cnt stack' in jmp (controls, stack', world) l
        else cont (controls, stack', world)
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
      else eval env (env#builtin cfg f arg_cnt (is_func)) rest 
    | ENTER (args) -> 
      let values, stack' = split (List.length args) stack in
      let state' = State.push state (List.fold_left (fun s (x, v) -> State.bind x v s) State.undefined (List.combine args values)) args in
      cont (controls, stack', (state', input, output))
    | LEAVE -> cont (controls, stack, (State.drop state, input, output))
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
  (*print_prg p;*)
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
           (*Printf.printf "Builtin:\n";*)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

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

let rec compile (defs, main) = 
let rec compile_expr expr =
let compile_call name args = (List.flatten @@ List.map compile_expr (List.rev args)) @ [CALL (name, List.length args, false)] in
match expr with
    | Expr.Const n -> [CONST n]
    | Expr.Var x -> [LD x]
    | Expr.Array args -> compile_call ".array" (List.rev args)
    | Expr.String s -> [STRING s]
    | Expr.Elem (a, i) -> compile_call ".elem" [i;a]
    | Expr.Length a -> compile_call ".length" [a]
    | Expr.Binop (op, arg1, arg2) -> (compile_expr arg1)@(compile_expr arg2)@[BINOP op]
    | Expr.Call (f, args) -> compile_call f args
    | Expr.Sexp (name, exprs) -> 
      let compiled_exprs = List.flatten @@ List.map compile_expr exprs in
      compiled_exprs @ [SEXP (name, List.length exprs)]
    | _ -> failwith "Not implemented"
in
let rec make_bindings pattern =
  let rec inner p = match p with
    | Pattern.Wildcard -> []
    | Pattern.Ident var -> [[]]
    | Pattern.Sexp (_, exprs) -> 
      let next i x = List.map (fun arr -> i::arr) (inner x) in List.flatten (List.mapi next exprs)
  in
  let elem i = [CONST i; CALL (".elem", 2, false)] in
  let make_bind p = [DUP] @ (List.flatten (List.map elem p)) @ [SWAP] in
  List.flatten (List.map make_bind (List.rev (inner pattern)))
and compile_pattern pattern end_label depth = 
  match pattern with
    | Pattern.Wildcard -> [DROP], false
    | Pattern.Ident _ -> [DROP], false
    | Pattern.Sexp (name, exprs) ->
      let compile_subpattern i pattern = 
        let inner_prg = match pattern with
        | Pattern.Sexp (_, ps) -> 
          if List.length ps > 0 
            then [DUP] @ fst (compile_pattern pattern end_label (depth + 1)) @ [DROP]
            else fst (compile_pattern pattern end_label depth)
        | _ -> fst (compile_pattern pattern end_label depth) 
        in  
        [DUP; CONST i; CALL (".elem", 2, false)] @ inner_prg in 
      let prg = List.flatten (List.mapi compile_subpattern exprs) in
      [TAG name] @ [ZJMPDROP (end_label, depth)] @ prg, true 
and compile_branch pattern stmt next_label end_label =
  let pattern_code, p_used = compile_pattern pattern next_label 0 in
  let body, s_used = compile_stmt (Stmt.Seq (stmt, Stmt.Leave)) end_label in
  pattern_code @ make_bindings pattern @ [DROP; ENTER (List.rev (Stmt.Pattern.vars pattern))] @ body, p_used, s_used
and compile_stmt stmt end_label = match stmt with
  | Assign (x, idxs, expr) -> (match idxs with
    | [] -> (compile_expr expr)@[ST x]
    | _ -> (List.flatten @@ List.map compile_expr (List.rev idxs))@(compile_expr expr)@[STA (x, List.length idxs)]
  ), false
  | Seq (t1, t2) -> 
    let l_out = label_generator#gen in 
    let p1, used1 = compile_stmt t1 l_out in 
    let p2, used2 = compile_stmt t2 end_label in
    p1 @ (if used1 then [LABEL l_out] else []) @ p2, used2
  | Skip -> [], false
  | If (cond, zen, elze) -> 
    let l_else = label_generator#gen in
    let p_if, u_if     = compile_stmt  zen end_label in
    let p_else, u_else = compile_stmt elze end_label in
    compile_expr cond
    @ [CJMP ("z", l_else)]
    @ p_if
    @ [JMP end_label]
    @ [LABEL (l_else)]
    @ p_else
    @ [JMP end_label], true
  | Case (cond, [case0, stmt0]) -> 
    let branch_code, p_used, s_used = compile_branch case0 stmt0 end_label end_label in 
    compile_expr cond @ [DUP] @ branch_code, p_used || s_used 
  | Case (cond, branches) -> 
    let n = List.length branches - 1 in
      let op (prev_label, i, prg) (pattern, body) =
        let has_next = (i != n) in
        let next_label = if has_next then label_generator#gen else end_label in
        let label_code = match prev_label with Some x -> [LABEL x; DUP] | None -> [] in
        let branch_code, _, _ = compile_branch pattern body next_label end_label in
        let code = label_code @ branch_code @ (if has_next then [JMP end_label] else []) in
        Some next_label, i + 1, code :: prg in
      let _, _, res = List.fold_left op (None, 0, []) branches in
    compile_expr cond @ [DUP] @ List.flatten @@ List.rev res, true
  | While (cond, action) -> 
    let l_check, l_loop = label_generator#gen2 in 
    let code, _ = (compile_stmt action l_check) in
    [JMP l_check]
    @ [LABEL l_loop]
    @ code
    @ [LABEL l_check]
    @ (compile_expr cond)
    @ [CJMP ("nz", l_loop)], false
  | Repeat (action, cond) -> 
    let l_check, l_loop = label_generator#gen2 in
    let code, _ = (compile_stmt action l_check) in
    [LABEL l_loop]
    @ code
    @ [LABEL l_check]
    @ (compile_expr cond)
    @ [CJMP ("z", l_loop)], false
  | Call (f, args) -> (List.flatten @@ List.map compile_expr (List.rev args)) @ [CALL (f, List.length args, true)], false
  | Return r -> (match r with
    | Some e -> (compile_expr e) @ [RET true]
    | _ -> [RET false]
    ), false
  | Leave -> [LEAVE], false
and compile_body body = 
  let end_lbl = label_generator#gen in
  let body, used = compile_stmt body end_lbl in
  body @ if (used) then [LABEL end_lbl] else []
and compile_def (name, (params, locals, body)) =
  let body = compile_body body in
  [LABEL name; BEGIN (name, params, locals)] @ body @ [END]
in
let defs = List.flatten @@ List.map compile_def defs in
let main = compile_body main in
main @ [END] @ defs
