(* Unit tests for functions in expression.ml and evaluation.ml *)

open CS51Utils
open Absbook
open Expr
open Evaluation

let exp_to_abstract_string_tests () =
  unit_test
    (exp_to_abstract_string (Var "x") = "Var(x)")
    "exp_to_abstract_string Var";
  unit_test
    (exp_to_abstract_string (Num 4) = "Num(4)")
    "exp_to_abstract_string Num";
  unit_test
    (exp_to_abstract_string (Bool false) = "Bool(false)")
    "exp_to_abstract_string Bool";
  unit_test 
    (exp_to_abstract_string (String "test") = "String(test)")
    "exp_to_abstract_string String";
  unit_test
    (exp_to_abstract_string (Unop (Negate, Num 4)) = "Unop(Negate, Num(4))")
    "exp_to_abstract_string Unop";
  unit_test
    (exp_to_abstract_string (Binop (Plus, Num 2, Num 4))
    = "Binop(Plus, Num(2), Num(4))")
    "exp_to_abstract_string Binop Plus";
  unit_test
    (exp_to_abstract_string (Binop (Concat, String "h", String "ello"))
    = "Binop(Concat, String(h), String(ello))")
    "exp_to_abstract_string Binop Concat";
  unit_test
    (exp_to_abstract_string (Conditional (Bool true, Num 2, Num 4))
    = "Conditional(Bool(true), Num(2), Num(4))")
    "exp_to_abstract_string Conditional";
  unit_test
    (exp_to_abstract_string (Fun ("x", Var "x")) = "Fun(x, Var(x))")
    "exp_to_abstract_string Fun";
  unit_test
    (exp_to_abstract_string (Let ("f", Fun ("x", Var "x"), Var "f"))
    = "Let(f, Fun(x, Var(x)), Var(f))")
    "exp_to_abstract_string Let";
  unit_test
    (exp_to_abstract_string (Letrec ("x", Num 4, Num 2))
    = "Letrec(x, Num(4), Num(2))")
    "exp_to_abstract_string Letrec";
  unit_test
    (exp_to_abstract_string (App (Num 4, Num 6)) = "App(Num(4), Num(6))")
    "exp_to_abstract_string App";
  unit_test
    (exp_to_abstract_string
       (Let ("f", Fun ("x", Var "x"), App (App (Var "f", Var "f"), Num 3)))
    = "Let(f, Fun(x, Var(x)), App(App(Var(f), Var(f)), Num(3)))")
    "exp_to_abstract_string Let and App";
  unit_test
    (exp_to_abstract_string Raise = "Raise")
    "exp_to_abstract_string Raise";
  unit_test
    (exp_to_abstract_string Unassigned = "Unassigned")
    "exp_to_abstract_string Unassigned"

let free_vars_tests () =
  (* FV (x) = {x} *)
  unit_test
    (same_vars (free_vars (Var "x")) (vars_of_list [ "x" ]))
    "free_vars var";
  (* FV (4) = {} *)
  unit_test (same_vars (free_vars (Num 4)) (vars_of_list [])) "free_vars num";
  (* FV (true) = {} *)
  unit_test
    (same_vars (free_vars (Bool true)) (vars_of_list []))
    "free_vars bool";
  (* FV ("test") = {} *)
  unit_test
    (same_vars (free_vars (String "test")) (vars_of_list []))
    "free_vars string";
  (* FV (Raise) = {} *)
  unit_test
    (same_vars (free_vars Raise) (vars_of_list []))
    "free_vars exception";
  (* FV (Unassigned) = {} *)
  unit_test
    (same_vars (free_vars Unassigned) (vars_of_list []))
    "free_vars unassigned";
  (* FV (~-x) = {x} *)
  unit_test
    (same_vars (free_vars (Unop (Negate, Var "x"))) (vars_of_list [ "x" ]))
    "free_vars unop";
  (* FV (x * y) = {x, y} *)
  unit_test
    (same_vars
       (free_vars (Binop (Times, Var "x", Var "y")))
       (vars_of_list [ "x"; "y" ]))
    "free_vars binop";
  (* FV (if x = 4 then y else z) = {x, y, z} *)
  unit_test
    (same_vars
       (free_vars
          (Conditional (Binop (Equals, Var "x", Num 4), Var "y", Var "z")))
       (vars_of_list [ "x"; "y"; "z" ]))
    "free_vars conditional";
  (* FV (fun y -> f (x + y)) = {f, x} *)
  unit_test
    (same_vars
       (free_vars (Fun ("y", App (Var "f", Binop (Plus, Var "x", Var "y")))))
       (vars_of_list [ "f"; "x" ]))
    "free_vars function 1";
  (* FV (fun x -> x + y) = {y} *)
  unit_test
    (same_vars
       (free_vars (Fun ("x", Binop (Plus, Var "x", Var "y"))))
       (vars_of_list [ "y" ]))
    "free_vars function 2";
  (* FV (let x = fun y -> x in x) = {x} *)
  unit_test
    (same_vars
       (free_vars (Let ("x", Fun ("y", Var "x"), Var "x")))
       (vars_of_list [ "x" ]))
    "free_vars let 1";
  (* FV (let x = 3 in x + y) = {y} *)
  unit_test
    (same_vars
       (free_vars (Let ("x", Num 3, Binop (Plus, Var "x", Var "y"))))
       (vars_of_list [ "y" ]))
    "free_vars let 2";
  (* FV (let rec x = fun y -> x in x) = {} *)
  unit_test
    (same_vars
       (free_vars (Letrec ("x", Fun ("y", Var "x"), Var "x")))
       (vars_of_list []))
    "free_vars let rec";
  (* FV (let x = y in let y = x in f x y) = {f, y} *)
  unit_test
    (same_vars
       (free_vars
          (Let
             ( "x",
               Var "y",
               Let ("y", Var "x", App (App (Var "f", Var "x"), Var "y")) )))
       (vars_of_list [ "f"; "y" ]))
    "free_vars let nested 1";
  (* FV (let z = 40 in let y = z + x in y) = {x} *)
  unit_test
    (same_vars
       (free_vars
          (Let ("z", Num 40, Let ("y", Binop (Plus, Var "z", Var "x"), Var "y"))))
       (vars_of_list [ "x" ]))
    "free_vars let nested 2"

let subst_tests () =
  (* x[x->4] = 4 *)
  unit_test (subst "x" (Num 4) (Var "x") = Num 4) "subst var";
  (* y[x->4] = y *)
  unit_test (subst "x" (Num 4) (Var "y") = Var "y") "subst var x =/ y";
  (* 6[x->4] = 6 *)
  unit_test (subst "x" (Num 4) (Num 6) = Num 6) "subst num";
  (* true[x->4] = true *)
  unit_test (subst "x" (Num 4) (Bool true) = Bool true) "subst bool";
  (* "test"[x->4] = "test" *)
  unit_test (subst "x" (Num 4) (String "test") = String "test") "subst string";
  (* Raise[x->6] = Raise *)
  unit_test (subst "x" (Num 4) Raise = Raise) "subst Raise";
  (* Unassigned[x->6] = Unassigned *)
  unit_test (subst "x" (Num 4) Unassigned = Unassigned) "subst Unassigned";
  (* ~-x[x->4] = ~-4 *)
  unit_test
    (subst "x" (Num 4) (Unop (Negate, Var "x")) = Unop (Negate, Num 4))
    "subst unop";
  (* (x * y)[x->4] = 4 * y *)
  unit_test
    (subst "x" (Num 4) (Binop (Times, Var "x", Var "y"))
    = Binop (Times, Num 4, Var "y"))
    "subst binop 1";
  (* (x + y)[x->4][y->6] = 4 + 6 *)
  unit_test
    (subst "x" (Num 4) (subst "y" (Num 6) (Binop (Plus, Var "x", Var "y")))
    = Binop (Plus, Num 4, Num 6))
    "subst binop 2";
  (* (x ^ y)[x->"h"][y->"ello"] = "h" ^ "ello" *)
  unit_test
    (subst "x" (String "h") (subst "y" (String "ello") (Binop (Concat, Var "x", Var "y")))
    = Binop (Concat, String "h", String "ello"))
    "subst binop 3";
  (* (if y = x then z)[x->4][z->6] = if y = 4 then 6 *)
  unit_test
    (subst "x" (Num 4)
       (subst "z" (Num 6) (Conditional (Var "y", Var "x", Var "z")))
    = Conditional (Var "y", Num 4, Num 6))
    "subst conditional";
  (* (fun x -> x + x)[x->3] = fun x -> x + x *)
  unit_test
    (subst "x" (Num 3) (Fun ("x", Binop (Plus, Var "x", Var "x")))
    = Fun ("x", Binop (Plus, Var "x", Var "x")))
    "subst fun 1";
  (* (fun x -> y + x)[x->3] = fun x -> y + x *)
  unit_test
    (subst "x" (Num 3) (Fun ("x", Binop (Plus, Var "y", Var "x")))
    = Fun ("x", Binop (Plus, Var "y", Var "x")))
    "subst fun 2";
  (* (fun y -> y + x)[x->3] = fun y -> y + 3 *)
  unit_test
    (subst "x" (Num 3) (Fun ("y", Binop (Plus, Var "y", Var "x")))
    = Fun ("y", Binop (Plus, Var "y", Num 3)))
    "subst fun 3";
  (* (fun y -> y + x)[x->y+4] = fun z -> z + y + 4 *)
  unit_test
    (subst "x"
       (Binop (Plus, Var "y", Num 4))
       (Fun ("y", Binop (Plus, Var "y", Var "x")))
    = Fun ("var0", Binop (Plus, Var "var0", Binop (Plus, Var "y", Num 4))))
    "subst fun 4";
  (* (let x = y * y in x + x)[x->3] = let x = y * y in x + x *)
  unit_test
    (subst "x" (Num 3)
       (Let
          ("x", Binop (Times, Var "y", Var "y"), Binop (Plus, Var "x", Var "x")))
    = Let ("x", Binop (Times, Var "y", Var "y"), Binop (Plus, Var "x", Var "x"))
    )
    "subst let 1";
  (* (let y = x * x in y + x)[x->3] = let y = 3 * 3 in y + 3 *)
  unit_test
    (subst "x" (Num 3)
       (Let
          ("y", Binop (Times, Var "x", Var "x"), Binop (Plus, Var "y", Var "x")))
    = Let ("y", Binop (Times, Num 3, Num 3), Binop (Plus, Var "y", Num 3)))
    "subst let 2";
  (* (let y = x * x in y + x)[x->y+4] = let z = (y+4)*(y+4) in z+y+4 *)
  unit_test
    (subst "x"
       (Binop (Plus, Var "y", Num 4))
       (Let
          ("y", Binop (Times, Var "x", Var "x"), Binop (Plus, Var "y", Var "x")))
    = Let
        ( "var1",
          Binop
            (Times, Binop (Plus, Var "y", Num 4), Binop (Plus, Var "y", Num 4)),
          Binop (Plus, Var "var1", Binop (Plus, Var "y", Num 4)) ))
    "subst let 3";
  (* (let x = 5 in f y)[y -> x + 1] = let z = 5 in f (x + 1) *)
  unit_test
    (subst "y"
       (Binop (Plus, Var "x", Num 1))
       (Let ("x", Num 5, App (Var "f", Var "y")))
    = Let ("var2", Num 5, App (Var "f", Binop (Plus, Var "x", Num 1))))
    "subst let 4"

(* evaluations that both the lexical and dynamic semantics should agree on: *)
let eval_tests ?(closures : bool = false) (eval : expr -> Env.env -> Env.value)
    =
  let env = Env.empty () in
  unit_test
    (try
       let _ = eval (Var "x") env in
       false
     with
    | EvalError _ -> true
    | _ -> false)
    "eval variable";
  unit_test
    (try
       let _ = eval Raise env in
       false
     with
    | EvalException -> true
    | _ -> false)
    "eval exception";
  unit_test (eval (Num 4) env = Env.Val (Num 4)) "eval num";
  unit_test (eval (Bool true) env = Env.Val (Bool true)) "eval bool";
  unit_test (eval (String "test") env = Env.Val (String "test")) "eval string";
  let exp_fun = Fun ("x", Var "x") in
  if closures then
    unit_test (eval exp_fun env = Env.Closure (exp_fun, env)) "eval fun closure"
  else unit_test (eval exp_fun env = Env.Val exp_fun) "eval fun";
  unit_test (eval Unassigned env = Env.Val Unassigned) "eval unassigned";
  unit_test (eval (Unop (Negate, Num 4)) env = Env.Val (Num ~-4)) "eval unop";
  unit_test
    (try
       let _ = eval (Unop (Negate, Bool true)) env in
       false
     with
    | EvalError _ -> true
    | _ -> false)
    "eval unop error";
  unit_test
    (eval (Binop (Times, Num 4, Num 5)) env = Env.Val (Num 20))
    "eval binop nums";
  unit_test
    (eval (Binop (Equals, Bool true, Bool false)) env = Env.Val (Bool false))
    "eval binop bools";
  unit_test
    (eval (Binop (Concat, String "h", String "ello")) env = Env.Val (String "hello"))
    "eval binop strings 1";
  unit_test
    (eval (Binop (Equals, String "h", String "h")) env = Env.Val (Bool true))
    "eval binop strings 2";
  unit_test
    (try
       let _ = eval (Binop (Plus, Bool true, Bool false)) env in
       false
     with
    | EvalError _ -> true
    | _ -> false)
    "eval binop error 1";
  unit_test
    (try
       let _ = eval (Binop (Concat, Num 4, Num 8)) env in
       false
     with
    | EvalError _ -> true
    | _ -> false)
    "eval binop error 2";
  unit_test
    (eval (App (Fun ("x", Binop (Plus, Var "x", Num 1)), Num 3)) env
    = Env.Val (Num 4))
    "eval app";
  unit_test
    (try
       let _ = eval (App (Num 3, Num 4)) env in
       false
     with
    | EvalError _ -> true
    | _ -> false)
    "eval app error";
  unit_test
    (eval (Conditional (Bool true, Num 4, Num 6)) env = Env.Val (Num 4))
    "eval conditional";
  (* let x = 3 * 4 in x + 1 = 13 *)
  unit_test
    (eval
       (Let ("x", Binop (Times, Num 3, Num 4), Binop (Plus, Var "x", Num 1)))
       env
    = Env.Val (Num 13))
    "eval let 1";
  (* let f = fun x -> x in f f 3 = 3 *)
  unit_test
    (eval
       (Let ("f", Fun ("x", Var "x"), App (Var "f", App (Var "f", Num 3))))
       env
    = Env.Val (Num 3))
    "eval let 2";
  (* let intofbool = fun b -> if b then 1 else 0 in intofbool true = 1 *)
  unit_test
    (eval
       (Let
          ( "intofbool",
            Fun ("b", Conditional (Var "b", Num 1, Num 0)),
            App (Var "intofbool", Bool true) ))
       env
    = Env.Val (Num 1))
    "eval let 3";
  (* let f = fun s -> s ^ s in f "hey "  = "hey hey " *)
  unit_test
    (eval
       (Let
          ( "f",
            Fun ("s", Binop(Concat, Var "s", Var "s")),
           App (Var "f", String "hey ")) )
       env
    = Env.Val (String "hey hey "))
    "eval let 4";
  (* let rec f = fun x -> if x = 0 then 1 else x * f (x-1) in f 4
     = 24 *)
  unit_test
    (eval
       (Letrec
          ( "f",
            Fun
              ( "x",
                Conditional
                  ( Binop (Equals, Var "x", Num 0),
                    Num 1,
                    Binop
                      ( Times,
                        Var "x",
                        App (Var "f", Binop (Minus, Var "x", Num 1)) ) ) ),
            App (Var "f", Num 4) ))
       env
    = Env.Val (Num 24))
    "eval letrec factorial";
  (* let rec f = fun x -> if x = 0 then 0 else x + f (x-1) in f 100
     = 5050 *)
  unit_test
    (eval
       (Letrec
          ( "f",
            Fun
              ( "x",
                Conditional
                  ( Binop (Equals, Var "x", Num 0),
                    Num 0,
                    Binop
                      ( Plus,
                        Var "x",
                        App (Var "f", Binop (Minus, Var "x", Num 1)) ) ) ),
            App (Var "f", Num 100) ))
       env
    = Env.Val (Num 5050))
    "eval letrec sum of first 100 nats"

(* separate tests for evaluations that differ depending on whether
   lexical or dynamic semantics rules are used *)

(* let x = 1 in let f = fun y -> x + y in let x = 2 in f 3 *)
let let_exp_1 =
  Let
    ( "x",
      Num 1,
      Let
        ( "f",
          Fun ("y", Binop (Plus, Var "x", Var "y")),
          Let ("x", Num 2, App (Var "f", Num 3)) ) )

(* let x = 1 in let y = x + x in let x = 5 in let f = let x = 3 in
   fun y -> x + y in f 10 *)
let let_exp_2 =
  Let
    ( "x",
      Num 1,
      Let
        ( "y",
          Binop (Plus, Var "x", Var "x"),
          Let
            ( "x",
              Num 5,
              Let
                ( "f",
                  Let ("x", Num 3, Fun ("y", Binop (Plus, Var "x", Var "y"))),
                  App (Var "f", Num 10) ) ) ) )

(* let x = 2 in let f = fun y -> x * y in let x = 1 in f 21 *)
let let_exp_3 =
  Let
    ( "x",
      Num 2,
      Let
        ( "f",
          Fun ("y", Binop (Times, Var "x", Var "y")),
          Let ("x", Num 1, App (Var "f", Num 21)) ) )

(* fun x -> fun y -> x + y) 1 2 *)
let curried_exp_1 =
  App (App (Fun ("x", Fun ("y", Binop (Plus, Var "x", Var "y"))), Num 1), Num 2)

(* let x = 10 in let f = fun y -> fun z -> z * (x + y) in let y = 12 in f 11 2 *)
let curried_exp_2 =
  Let
    ( "x",
      Num 10,
      Let
        ( "f",
          Fun
            ( "y",
              Fun ("z", Binop (Times, Var "z", Binop (Plus, Var "x", Var "y")))
            ),
          Let ("y", Num 12, App (App (Var "f", Num 11), Num 2)) ) )

(* let x = 10 in let f = fun y -> fun z -> z * (x + y) in f 11 2 *)
let curried_exp_3 =
  Let
    ( "x",
      Num 10,
      Let
        ( "f",
          Fun
            ( "y",
              Fun ("z", Binop (Times, Var "z", Binop (Plus, Var "x", Var "y")))
            ),
          App (App (Var "f", Num 11), Num 2) ) )

let eval_lexical_tests (eval : expr -> Env.env -> Env.value) =
  let env = Env.empty () in
  (* let_exp_1 = 4 *)
  unit_test (eval let_exp_1 env = Env.Val (Num 4)) "eval_lexical let 1";
  (* let_exp_2 = 13 *)
  unit_test (eval let_exp_2 env = Env.Val (Num 13)) "eval_lexical let 2";
  (* let_exp_3 = 42 *)
  unit_test (eval let_exp_3 env = Env.Val (Num 42)) "eval_lexical let 3";
  (* curried_exp_1 = 3 *)
  unit_test (eval curried_exp_1 env = Env.Val (Num 3)) "eval_lexical curried 1";
  (* curried_exp_2 = 42 *)
  unit_test (eval curried_exp_2 env = Env.Val (Num 42)) "eval_lexical curried 2";
  (* curried_exp_3 = 42 *)
  unit_test (eval curried_exp_3 env = Env.Val (Num 42)) "eval_lexical curried 3"

let eval_dynamic_tests () =
  let env = Env.empty () in
  (* let_exp_1 = 5 *)
  unit_test (eval_d let_exp_1 env = Env.Val (Num 5)) "eval_dynamic let 1";
  (* let_exp_2 = 15 *)
  unit_test (eval_d let_exp_2 env = Env.Val (Num 15)) "eval_dynamic let 2";
  (* let_exp_3 = 21 *)
  unit_test (eval_d let_exp_3 env = Env.Val (Num 21)) "eval_dynamic let 3";
  (* curried_exp_1 -> evaluation error *)
  unit_test
    (try
       let _ = eval_d curried_exp_1 env in
       false
     with EvalError _ -> true)
    "eval_dynamic curried 1";
  (* curried_exp_2 = 44 *)
  unit_test
    (eval_d curried_exp_2 env = Env.Val (Num 44))
    "eval_dynamic curried 2";
  (* curried_exp_3 -> evaluation error *)
  unit_test
    (try
       let _ = eval_d curried_exp_3 env in
       false
     with EvalError _ -> true)
    "eval_dynamic curried 3"

let env_tests () =
  let empty = Env.empty () in
  let v1 = ref (Env.Val (Num 4)) in
  let e1 = Env.extend empty "x" v1 in
  unit_test (Env.lookup e1 "x" = Env.Val (Num 4)) "env lookup";
  unit_test (Env.value_to_string !v1 = "4") "env value_to_string";
  unit_test (Env.env_to_string e1 = "{x -> 4}") "env env_to_string";
  let exp = Fun ("x", Binop (Plus, Var "x", Num 1)) in
  let v2 = ref (Env.close exp e1) in
  let e2 = Env.extend e1 "y" v2 in
  unit_test (Env.lookup e2 "y" = Env.Closure (exp, e1)) "env lookup closure";
  unit_test
    (Env.value_to_string !v2 = "[{x -> 4} |- fun x -> x + 1]")
    "env value_to_string closure";
  unit_test
    (Env.value_to_string ~printenvp:false !v2 = "fun x -> x + 1")
    "env value_to_string closure 2";
  let e3 = Env.extend e2 "z" (ref (Env.Val (Num 8))) in
  unit_test
    (Env.env_to_string e3
   = "{z -> 8}{y -> [{x -> 4} |- fun x -> x + 1]}{x -> 4}")
    "env env_to_string 2";
  let e4 = Env.extend e3 "x" (ref (Env.Val (Num 12))) in
  unit_test
    (Env.env_to_string e4
   = "{x -> 12}{z -> 8}{y -> [{x -> 4} |- fun x -> x + 1]}")
    "env env_to_string 3";
  unit_test (Env.lookup e4 "z" = Env.Val (Num 8)) "env lookup 2";
  unit_test
    (try
       let _ = Env.lookup e4 "f" in
       false
     with EvalError _ -> true)
    "env lookup error"

let eval_s_tests () = eval_tests eval_s

let eval_d_tests () = eval_tests eval_d

let eval_l_tests () = eval_tests ~closures:true eval_l

let eval_s_lexical_tests () = eval_lexical_tests eval_s

let eval_l_lexical_tests () = eval_lexical_tests eval_l

let tests () =
  exp_to_abstract_string_tests ();
  free_vars_tests ();
  subst_tests ();
  Printf.printf "\nTests for eval_s:\n";
  eval_s_tests ();
  eval_s_lexical_tests ();
  Printf.printf "end of eval_s tests\n\n";
  env_tests ();
  Printf.printf "\nTests for eval_d:\n";
  eval_d_tests ();
  eval_dynamic_tests ();
  Printf.printf "end of eval_d tests\n\n";
  Printf.printf "Tests for eval_l:\n";
  eval_l_tests ();
  eval_l_lexical_tests ();
  Printf.printf "end of eval_l tests\n"

let _ = tests ()
