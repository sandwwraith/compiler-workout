(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Ostap.Combinators

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
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

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
        `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
        `Lefta, ["+" ; "-"];
        `Lefta, ["*" ; "/"; "%"];
                  |] 
          )
          primary);
          
          primary:
            n:DECIMAL {Const n}
          | x:IDENT   {Var x}
          | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env config statement =
    let (state, input, output) = config in
    match statement with
      | Read name -> (
        match input with
          | [] -> failwith "Can't read from empty input"
          | x::tail -> (State.update name x state, tail, output)
      )
      | Write e -> (state, input, output@[(Expr.eval state e)])
      | Assign (name, e) -> (State.update name (Expr.eval state e) state, input, output)
      | Seq (one, two) -> eval env (eval env config one) two
      | Skip -> (state, input, output)
      | If (cond, zen, elze) -> let res = (Expr.eval state cond) in 
        if (res != 0) then eval env config zen  else eval env config elze
      | While (cond, action) -> let res = (Expr.eval state cond) in 
        if (res == 0) then config else eval env (eval env config action) (statement)
      | Repeat (action, cond) -> 
        let first = eval env config action in 
        let (conf', _, _) = first in 
        if (Expr.eval conf' cond  != 0) then first else eval env first statement
      | Call (f, args) -> 
        let params, locals, body = env#definition f in
        let args = List.map (Expr.eval state) args in
        let f_scope = State.push_scope state (params @ locals) in
        let f_state = List.fold_left2 (fun s x v -> State.update x v s) f_scope params args in
        let (new_state, in', out') = eval env (f_state, input, output) body in
        (State.drop_scope new_state state, in', out')
                                
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
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
