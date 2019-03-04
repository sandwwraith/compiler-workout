(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Ostap.Combinators

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

    (* State: a partial map from variables to integer values. *)
    type state = string -> int

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

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

    (* Expression evaluator
          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let rec eval state expr = match expr with
      | Const c -> c
      | Var name -> state name
      | Binop (op, arg1, arg2) -> makeBinOp op (eval state arg1) (eval state arg2)
    ;;

    (* let ostap x = x
    let _ = Array.map (fun (assoc, ops) -> (assoc, List.map (fun op -> (ostap - $(op), fun a b -> Binop (op, a, b))) ops))
          [|                                               (* --- an array of binary operator specifiers, ordered by the priority in increasing order              *)
            `Lefta , ["+"]; (*     --- each specifier describes the associativity at given priority (one of `Lefta, `Righta, `Nona) *)
            `Righta, ["*"]; (*     --- and the list of pairs:                                                                       *)
          |] *)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    ostap (
      expr:
      !(Ostap.Util.expr
          (fun x -> x)
          (Array.map (fun (assoc, ops) -> assoc, List.map (fun op -> ostap (- $(op)), fun a b -> Binop (op, a, b)) ops) [|
            `Lefta, ["!!"];
            `Lefta, ["&&"];
            `Nona , ["<="; "<"; ">="; ">"; "=="; "!="];
            `Lefta, ["+"; "-"];
            `Lefta, ["*"; "/"; "%"];
          |])
          primary
        );

      primary:
        c:DECIMAL {Const c}
        | x:IDENT {Var x}
        | -"(" expr -")"
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

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval config statement =
    let (state, input, output) = config in
    match statement with
      | Read name -> (
        match input with
          | [] -> failwith "Can't read from empty input"
          | x::tail -> (Expr.update name x state, tail, output)
      )
      | Write e -> (state, input, output@[(Expr.eval state e)])
      | Assign (name, e) -> (Expr.update name (Expr.eval state e) state, input, output)
      | Seq (one, two) -> eval (eval config one) two


    (* Statement parser *)
    ostap (
      statement:
        "read" "(" x:IDENT ")"           {Read x}
        | "write" "(" e:!(Expr.expr) ")" {Write e}
        | x:IDENT ":=" e:!(Expr.expr)    {Assign (x, e)}
        ;

      parse: <s::ss> : !(Util.listBy)[ostap (";")][statement] { List.fold_left (fun s ss -> Seq(s, ss)) s ss }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
