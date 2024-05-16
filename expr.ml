(*
                          CS 51 Final Project
                         MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions
*)
open Printf

type unop = Negate

type binop = Plus | Minus | Times | Equals | LessThan | Concat

type varid = string

type expr =
  | Var of varid (* variables *)
  | Num of int (* integers *)
  | Bool of bool (* booleans *)
  | String of string (* strings *)
  | Unop of unop * expr (* unary operators *)
  | Binop of binop * expr * expr (* binary operators *)
  | Conditional of expr * expr * expr (* if then else *)
  | Fun of varid * expr (* function definitions *)
  | Let of varid * expr * expr (* local naming *)
  | Letrec of varid * expr * expr (* recursive local naming *)
  | Raise (* exceptions *)
  | Unassigned (* (temporarily) unassigned *)
  | App of expr * expr
(* function applications *)

(*......................................................................
  Manipulation of variable names (varids) and sets of them
*)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
  type t = varid

  let compare = String.compare
end)

type varidset = SS.t

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool = SS.equal

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset = SS.of_list

(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var v -> SS.singleton v
  | Num _ | Bool _ | Raise | Unassigned | String _ -> SS.empty
  | Unop (_u, e) -> free_vars e
  | Binop (_, e1, e2) | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | Conditional (e1, e2, e3) ->
      SS.union (SS.union (free_vars e1) (free_vars e2)) (free_vars e3)
  | Fun (v, e) -> SS.remove v (free_vars e)
  | Let (v, e1, e2) -> SS.union (SS.remove v (free_vars e2)) (free_vars e1)
  | Letrec (v, e1, e2) ->
      SS.union (SS.remove v (free_vars e2)) (SS.remove v (free_vars e1))

(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no other variable names
   use the prefix "var". (Otherwise, they might accidentally be the
   same as a generated variable name.) *)
let new_varname =
  let ctr : int ref = ref ~-1 in
  fun () : varid ->
    ctr := succ !ctr;
    sprintf "var%i" !ctr

(*......................................................................
  Substitution

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
*)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  match exp with
  | Var v -> if v = var_name then repl else exp
  | Num _ | Bool _ | Raise | Unassigned | String _ -> exp
  | Unop (u, e) -> Unop (u, subst var_name repl e)
  | Binop (b, e1, e2) ->
      Binop (b, subst var_name repl e1, subst var_name repl e2)
  | Conditional (e1, e2, e3) ->
      Conditional
        (subst var_name repl e1, subst var_name repl e2, subst var_name repl e3)
  | Fun (v, e) ->
      if v = var_name then exp
      else if SS.mem v (free_vars repl) then
        let z = new_varname () in
        Fun (z, subst var_name repl (subst v (Var z) e))
      else Fun (v, subst var_name repl e)
  | Let (v, e1, e2) ->
      if v = var_name then Let (v, subst var_name repl e1, e2)
      else if SS.mem v (free_vars repl) then
        let z = new_varname () in
        Let (z, subst var_name repl e1, subst var_name repl (subst v (Var z) e2))
      else Let (v, subst var_name repl e1, subst var_name repl e2)
  | Letrec (v, e1, e2) ->
      if v = var_name then Letrec (v, subst var_name repl e1, e2)
      else if SS.mem v (free_vars repl) then
        let z = new_varname () in
        Letrec
          ( z,
            subst var_name repl (subst v (Var z) e1),
            subst var_name repl (subst v (Var z) e2) )
      else Letrec (v, subst var_name repl e1, subst var_name repl e2)
  | App (e1, e2) -> App (subst var_name repl e1, subst var_name repl e2)

(*......................................................................
  String representations of expressions
*)

(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var v -> v
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | String s -> "\"" ^ s ^ "\""
  | Unop (u, e) -> ( match u with Negate -> "~-" ^ exp_to_concrete_string e)
  | Binop (b, e1, e2) -> (
      let s1, s2 = (exp_to_concrete_string e1, exp_to_concrete_string e2) in
      match b with
      | Plus -> s1 ^ " + " ^ s2
      | Minus -> s1 ^ " - " ^ s2
      | Times -> s1 ^ " * " ^ s2
      | Equals -> s1 ^ " = " ^ s2
      | LessThan -> s1 ^ " < " ^ s2
      | Concat -> s1 ^ " ^ " ^ s2)
  | Conditional (e1, e2, e3) ->
      sprintf "if %s then %s else %s"
        (exp_to_concrete_string e1)
        (exp_to_concrete_string e2)
        (exp_to_concrete_string e3)
  | Fun (v, e) -> sprintf "fun %s -> %s" v (exp_to_concrete_string e)
  | Let (v, e1, e2) ->
      sprintf "let %s = %s in %s" v
        (exp_to_concrete_string e1)
        (exp_to_concrete_string e2)
  | Letrec (v, e1, e2) ->
      sprintf "let rec %s = %s in %s" v
        (exp_to_concrete_string e1)
        (exp_to_concrete_string e2)
  | Raise -> "exception"
  | Unassigned -> "unassigned"
  | App (e1, e2) ->
      sprintf "%s %s" (exp_to_concrete_string e1) (exp_to_concrete_string e2)

(* string_of_binop b -- Return a string representation of the binop for use in
   exp_to_abstract_string *)
let string_of_binop (b : binop) : string =
  match b with
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Times -> "Times"
  | Equals -> "Equals"
  | LessThan -> "LessThan"
  | Concat -> "Concat"

(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var v -> sprintf "Var(%s)" v
  | Num n -> sprintf "Num(%i)" n
  | Bool b -> sprintf "Bool(%B)" b
  | String s -> sprintf "String(%s)" s
  | Unop (u, e) -> (
      match u with
      | Negate -> sprintf "Unop(Negate, %s)" (exp_to_abstract_string e))
  | Binop (b, e1, e2) ->
      sprintf "Binop(%s, %s, %s)" (string_of_binop b)
        (exp_to_abstract_string e1)
        (exp_to_abstract_string e2)
  | Conditional (e1, e2, e3) ->
      sprintf "Conditional(%s, %s, %s)"
        (exp_to_abstract_string e1)
        (exp_to_abstract_string e2)
        (exp_to_abstract_string e3)
  | Fun (v, e) -> sprintf "Fun(%s, %s)" v (exp_to_abstract_string e)
  | Let (v, e1, e2) ->
      sprintf "Let(%s, %s, %s)" v
        (exp_to_abstract_string e1)
        (exp_to_abstract_string e2)
  | Letrec (v, e1, e2) ->
      sprintf "Letrec(%s, %s, %s)" v
        (exp_to_abstract_string e1)
        (exp_to_abstract_string e2)
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (e1, e2) ->
      sprintf "App(%s, %s)"
        (exp_to_abstract_string e1)
        (exp_to_abstract_string e2)
