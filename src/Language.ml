(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)

    let bool2int x = if x then 1 else 0
    let int2bool = (!=) 0

    let makeBinOp name =
    let intify f = fun a b -> bool2int (f a b) in
    match name with
      | "+" -> (+)
      | "-" -> (-)
      | "*" -> ( * )
      | "/" -> ( / )
      | "%" -> ( mod )
      | ">" -> intify ( > )
      | ">=" -> intify ( >= )
      | "<" -> intify ( < )
      | "<=" -> intify ( <= )
      | "==" -> intify ( == )
      | "!=" -> intify ( != )
      | "&&" -> fun a b -> bool2int ((int2bool a) && (int2bool b))
      | "!!" -> fun a b -> bool2int ((int2bool a) || (int2bool b))
      | _ -> failwith ("Unknown operator " ^ name)

                                                           
    let rec eval env ((st, i, o, r) as conf) expr = match expr with
      | Binop (op, x, y) ->
        let (st1, i1, o1, Some r1) = eval env conf x in
        let (st2, i2, o2, Some r2) = eval env (st1, i1, o1, None) y in
        (st2, i2, o2, Some (makeBinOp op r1 r2))
      | Var x -> (st, i, o, Some (State.eval st x))
      | Const x -> (st, i, o, Some x)
      | Call (f, args) ->
        let eval_args = (fun (st, i, o, values) arg ->
          let (st', i', o', Some value) = eval env (st, i, o, None) arg in
          (st', i', o', values @ [value])) in
        let st', i', o', values = List.fold_left eval_args (st, i, o, []) args in
        env#definition env f values (st', i', o', None)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
     parse: 
      !(Ostap.Util.expr 
              (fun x -> x)
              (Array.map (fun (a, s) -> a, 
                              List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                            )
                [|
                  `Lefta, ["!!"];
                  `Lefta, ["&&"];
                  `Nona , ["<="; "<"; ">="; ">"; "=="; "!="];
                  `Lefta, ["+"; "-"];
                  `Lefta, ["*"; "/"; "%"];
                |] 
              )
              primary
          );

      primary: n:DECIMAL {Const n} 
             | f:IDENT "(" args:!(Util.list0 parse) ")" {Call (f, args)}
             | x:IDENT {Var x} 
             | -"(" parse -")" 
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((state, input, output, ret) as config) k stmt =
    let kont k s = match k with
      | Skip -> s
      | _ -> Seq (s, k)
    in
    match stmt with
      | Read name -> (
        match input with
          | [] -> failwith "Can't read from empty input"
          | x::tail -> eval env (State.update name x state, tail, output, None) Skip k
      )
      | Write e -> let (s, i, o, Some res) = Expr.eval env config e in 
        eval env (s, i, o@[res], None) Skip k
      | Assign (name, e) -> let (s, i, o, Some res) = Expr.eval env config e in 
        eval env (State.update name res s, i, o, None) Skip k (* Maybe Some val here? *)
      | Seq (one, two) -> eval env config (kont k two) one
      | Skip -> (match k with
          | Skip -> config
          | _    -> eval env config Skip k
        )
      | If (cond, zen, elze) -> let (s, i, o, Some res) = Expr.eval env config cond in
        if (res != 0) then eval env (s, i, o, None) k zen else eval env (s, i, o, None) k elze
      | While (cond, action) -> let (s, i, o, Some res) = Expr.eval env config cond in
        if (res == 0) then eval env (s,i,o,None) Skip k else eval env (s,i,o,None) (kont k stmt) action
      | Repeat (action, cond) -> 
        eval env config (kont k (While (Expr.Binop ("==", cond, Expr.Const 0), action))) action
      | Call (f, args) -> 
        eval env (Expr.eval env config (Expr.Call (f, args))) Skip k
      | Return res -> (match res with
        | Some v -> Expr.eval env config v
        | _        -> (state, input, output, None)
      )
         
    (* Statement parser *)
    ostap (
      statement:
        "read" "(" x:IDENT ")"           {Read x}
        | "write" "(" e:!(Expr.parse) ")" {Write e}
        | x:IDENT ":=" e:!(Expr.parse)    {Assign (x, e)}
        | "skip" {Skip}
        | "if" e:!(Expr.parse) "then" s1:parse s2:elif {If (e, s1, s2)}
        | "while" e:!(Expr.parse) "do" s:parse "od" {While (e, s)}
        | "repeat" s:parse "until" e:!(Expr.parse) {Repeat (s, e)}
        | "for" i:parse "," e:!(Expr.parse) "," inc:parse "do" s:parse "od" {Seq (i, While (e, Seq(s, inc)))}
        | f:IDENT "(" args:(!(Expr.parse))* ")" {Call (f, args)}
        | "return" expr:!(Expr.parse)? {Return expr}
        ;

      elif:
        "fi" { Skip }
        | "else" s:parse "fi" { s }
        | "elif" e:!(Expr.parse) "then" s1:parse s2:elif { If (e, s1, s2) }
        ;

      parse: <s::ss> : !(Util.listBy)[ostap (";")][statement] { List.fold_left (fun s ss -> Seq(s, ss)) s ss }
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    let list_of option = match option with
      | Some list -> list
      | _ -> []

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      ident_list: i:IDENT "," rest:ident_list {i::rest} | i:IDENT {[i]};                                      
      parse: "fun" name:IDENT "(" params:ident_list? ")" locals:(-"local" ident_list)? "{" body:!(Stmt.parse) "}" 
        {name, (list_of params, list_of locals, body)}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
