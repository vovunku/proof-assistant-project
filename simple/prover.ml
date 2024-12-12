open Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)

let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

let () = Printexc.record_backtrace true
(* 
(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | Ty of tvar
  | Impl of ty * ty
  | Conj of ty * ty
  | Truth
  | Disj of ty * ty
  | Falsity
  | Nat

(** Terms. *)
type tm =
  | Var of var
  | Lam of var * ty * tm
  | App of tm * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Triv
  | Inl of tm * ty
  | Inr of ty * tm
  | Case of tm * var * tm * var * tm
  | Absurd of tm * ty
  | Zero
  | Succ of tm
  | Rec of tm * tm * var * var * tm  *)

(** String representation of types. *)
let rec string_of_ty = function
  | Ty tvar -> tvar
  | Impl (ty1, ty2) ->
      "(" ^ string_of_ty ty1 ^ " => " ^ string_of_ty ty2 ^ ")"
  | Conj (ty1, ty2) ->
      "(" ^ string_of_ty ty1 ^ " /\\ " ^ string_of_ty ty2 ^ ")"
  | Truth -> "⊤"
  | Disj (ty1, ty2) ->
      "(" ^ string_of_ty ty1 ^ " \\/ " ^ string_of_ty ty2 ^ ")"
  | Falsity -> "⊥"
  | Nat -> "Nat"

(** String representation of terms. *)
let rec string_of_tm = function
  | Var var -> var
  | Lam (var, ty, tm) ->
      "(fun (" ^ var ^ " : " ^ string_of_ty ty ^ ") -> " ^ string_of_tm tm ^ ")"
  | App (tm1, tm2) ->
      "(" ^ string_of_tm tm1 ^ " " ^ string_of_tm tm2 ^ ")"
  | Pair (tm1, tm2) ->
      "(" ^ string_of_tm tm1 ^ ", " ^ string_of_tm tm2 ^ ")"
  | Fst tm -> "fst " ^ string_of_tm tm
  | Snd tm -> "snd " ^ string_of_tm tm
  | Triv -> "()"
  | Inl (tm, _) -> "left " ^ string_of_tm tm
  | Inr (_, tm) -> "right " ^ string_of_tm tm
  | Case (tm, x1, tm1, x2, tm2) ->
      "case " ^ string_of_tm tm ^ " of " ^ x1 ^ " => " ^ string_of_tm tm1 ^ " | " ^ x2 ^ " => " ^ string_of_tm tm2
  | Absurd (tm, ty) -> "absurd " ^ string_of_tm tm ^ " : " ^ string_of_ty ty
  | Zero -> "Zero"
  | Succ tm -> "Succ " ^ string_of_tm tm
  | Rec (tm1, tm2, x1, x2, tm3) ->
      "Rec (" ^ string_of_tm tm1 ^ ", " ^ string_of_tm tm2 ^ ", " ^ x1 ^ ", " ^ x2 ^ ", " ^ string_of_tm tm3 ^ ")"
  

let tya = Ty "A"
let tyb = Ty "B"
let tyc = Ty "C"
let tyab = Impl (tya, tyb)
let tyac = Impl (tya, tyc)
let tyabac = Impl (tyab, tyac)

let () = Printf.printf "tyabac = %s\n" (string_of_ty tyabac)

let tm1 = Lam ("x", tya, App (Var "f", Var "x"))
let tm2 = Lam ("f", tyab, tm1)

let () =
  Printf.printf "tm1 = %s\n" (string_of_tm tm1);
  Printf.printf "tm2 = %s\n" (string_of_tm tm2)

(** Type environment. *)
type context = (var * ty) list

exception Type_error

let rec infer_type (ctx : context) (tm : tm) : ty =
  match tm with
  | Var var ->
      (try List.assoc var ctx with Not_found -> raise Type_error)
  | Lam (var, ty, tm) ->
      let ctx' = (var, ty) :: ctx in
      let ty' = infer_type ctx' tm in
      Impl (ty, ty')
  | App (tm1, tm2) ->
      let ty1 = infer_type ctx tm1 in
      (match ty1 with
      | Impl (ty11, ty12) -> 
          check_type ctx tm2 ty11;
          ty12
      | _ -> raise Type_error)
  | Pair (tm1, tm2) ->
      let ty1 = infer_type ctx tm1 in
      let ty2 = infer_type ctx tm2 in
      Conj (ty1, ty2)
  | Fst tm ->
      (match infer_type ctx tm with
      | Conj (ty1, _) -> ty1
      | _ -> raise Type_error)
  | Snd tm ->
      (match infer_type ctx tm with
      | Conj (_, ty2) -> ty2
      | _ -> raise Type_error)
  | Triv -> Truth
  | Inl (tm, ty) ->
      Disj (infer_type ctx tm, ty)
  | Inr (ty, tm) ->
      Disj (ty, infer_type ctx tm)
  | Case (tm, x1, tm1, x2, tm2) ->
      (match infer_type ctx tm with
      | Disj (ty1, ty2) ->
          let ty1' = infer_type ((x1, ty1) :: ctx) tm1 in
          let ty2' = infer_type ((x2, ty2) :: ctx) tm2 in
          if ty1' = ty2' then ty1' else raise Type_error
      | _ -> raise Type_error)
  (* | Case (tm1, tm2, tm3) ->
      (match infer_type ctx tm2 with
        | Impl (ty1, ty3) ->
          (match infer_type ctx tm3 with
            | Impl (ty2, ty4) when ty3 = ty4 -> 
              check_type ctx tm1 (Disj (ty1, ty2));
              ty3
            | _ -> raise Type_error
          )
        | _ -> raise Type_error
      ) *)
  | Absurd (tm, ty) ->
      check_type ctx tm Falsity;
      ty
  | Zero -> Nat
  | Succ tm ->
      check_type ctx tm Nat;
      Nat
  | Rec (n, z, x, y, s) ->
      check_type ctx n Nat;
      let zty = infer_type ctx z in
      let ctx' = (x, Nat) :: (y, zty) :: ctx in
      check_type ctx' s zty;
      zty
      

and check_type (ctx : context) (tm : tm) (ty : ty) : unit =
  let ty' = infer_type ctx tm in
  if ty <> ty' then raise Type_error


(** Type inference. *)
(* let rec infer_type (ctx : context) (tm : tm) : ty =
  match tm with
  | Var var ->
      (try List.assoc var ctx with Not_found -> raise Type_error)
  | Lam (var, ty, tm) ->
      let ctx' = (var, ty) :: ctx in
      let ty' = infer_type ctx' tm in
      Impl (ty, ty')
  | App (tm1, tm2) ->
      let ty1 = infer_type ctx tm1 in
      let ty2 = infer_type ctx tm2 in
      (match ty1 with
      | Impl (ty11, ty12) when ty11 = ty2 -> ty12
      | _ -> raise Type_error) *)

let tm = 
  Lam ("f", Impl (tya, tyb),
    Lam ("g", Impl (tyb, tyc),
      Lam ("x", tya,
        App (Var "g", App (Var "f", Var "x"))
      )
    )
  )

let () =
  let ty = infer_type [] tm in
  Printf.printf "tm = %s\n" (string_of_tm tm);
  Printf.printf "type = %s\n" (string_of_ty ty)

let test_infer_type () =
  let test_cases = [
    (Lam ("f", tya, Var "x"), "Lam (\"f\", tya, Var \"x\")");
    (Lam ("f", tya, Lam ("x", tyb, App (Var "f", Var "x"))), "Lam (\"f\", tya, Lam (\"x\", tyb, App (Var \"f\", Var \"x\")))");
    (Lam ("f", Impl (tya, tyb), Lam ("x", tyb, App (Var "f", Var "x"))), "Lam (\"f\", Impl (tya, tyb), Lam (\"x\", tyb, App (Var \"f\", Var \"x\")))")
  ] in
  List.iter (fun (tm, desc) ->
    try
      let _ = infer_type [] tm in
      Printf.printf "Test failed: %s did not raise Type_error\n" desc
    with
    | Type_error -> Printf.printf "Test passed: %s raised Type_error\n" desc
    | exn -> Printf.printf "Test failed: %s raised unexpected exception %s\n" desc (Printexc.to_string exn)
  ) test_cases

let () = test_infer_type ()

(* let check_type cx trm typ = 
  let ty = infer_type cx trm in
  if ty <> typ then raise Type_error

let () =
  let tm = Lam ("x", tya, Var "x") in
  let ctx = [] in
  let test tm typ expected msg =
    try
      check_type ctx tm typ;
      Printf.printf "Test %s: %s\n" (if expected then "passed" else "failed") msg
    with
    | Type_error -> Printf.printf "Test %s: %s\n" (if expected then "failed" else "passed") msg
  in
  test tm (Impl (tya, tya)) true "(fun (x : A) -> x) has type A -> A";
  test tm (Impl (tyb, tyb)) false "(fun (x : A) -> x) has type B -> B";
  test (Var "x") tya false "x has type A" *)

let and_comm = 
  Lam ("p", Conj (tya, tyb),
    Pair (Snd (Var "p"), Fst (Var "p"))
  )

let () =
  Printf.printf "and_comm = %s\n" (string_of_tm and_comm);
  Printf.printf "type = %s\n" (string_of_ty (infer_type [] and_comm))

let top_impl_a_impl_a = 
  Lam ("f", Impl (Truth, tya),
    App (Var "f", Triv)
  )

let () =
  Printf.printf "top_impl_a_impl_a = %s\n" (string_of_tm top_impl_a_impl_a);
  Printf.printf "type = %s\n" (string_of_ty (infer_type [] top_impl_a_impl_a))

let or_comm = 
  Lam ("p", Disj (tya, tyb),
    Case (Var "p", "x", Inr (tyb, Var "x"), "y", Inl (Var "y", tya))
  )

let () =
  Printf.printf "or_comm = %s\n" (string_of_tm or_comm);
  Printf.printf "type = %s\n" (string_of_ty (infer_type [] or_comm))

let a_and_not_a_impl_b = 
  Lam ("p", Conj (tya, Impl (tya, Falsity)),
    Absurd (App (Snd (Var "p"), Fst (Var "p")), tyb)
  )

let () =
  Printf.printf "a_and_not_a_impl_b = %s\n" (string_of_tm a_and_not_a_impl_b);
  Printf.printf "type = %s\n" (string_of_ty (infer_type [] a_and_not_a_impl_b))

let () =
  let l = [
    "A => B";
    "A ⇒ B";
    "A /\\ B";
    "A ∧ B";
    "T";
    "A \\/ B";
    "A ∨ B";
    "_";
    "not A";
    "¬ A";
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))
    ) l

let () =
  let l = [
    "t u v";
    "fun (x : A) -> t";
    "λ (x : A) → t";
    "(t , u)";
    "fst(t)";
    "snd(t)";
    "()";
    "case t of x -> u | y -> v";
    "left(t,B)";
    "right(A,t)";
    "absurd(t,A)"
  ]
  in
  List.iter
    (fun s ->
        Printf.printf
          "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))
    ) l
  
let string_of_ctx (ctx : context) : string =
  let string_of_binding (var, ty) = var ^ " : " ^ string_of_ty ty in
  String.concat " , " (List.map string_of_binding ctx)

let () =
  let ctx = [("x", tyab); ("y", Conj (tya, tyb)); ("z", Truth)] in
  Printf.printf "context = %s\n" (string_of_ctx ctx)

(** Type for sequents. *)
type sequent = context * ty

(** String representation of sequents. *)
let string_of_seq (ctx, ty) =
  string_of_ctx ctx ^ " ⊢ " ^ string_of_ty ty

(* 2.3 An interactive prover *)
let proof_log = ref None

let start_logging filename =
  let oc = open_out filename in
  proof_log := Some oc

let log_command cmd =
  match !proof_log with
  | Some oc -> output_string oc (cmd ^ "\n"); flush oc
  | None -> ()

let stop_logging () =
  match !proof_log with
  | Some oc -> close_out oc; proof_log := None
  | None -> ()

let rec prove env a =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    log_command cmd;
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" ->
     (
       match a with
       | Impl (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x,a)::env) b in
            Lam (x, a, t)
       | Conj (x, y) ->
          Pair (prove env x, prove env y)
       | Truth -> Triv
      | Nat -> 
         (match arg with
         | "zero" -> Zero
         | "succ" -> let t = prove env Nat in Succ t
         | _ -> error "Please provide either 'zero' or 'succ' for Nat introduction.")
       | _ ->
          error "Don't know how to introduce this."
     )
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else t
  | "elim" ->
      (
        match List.assoc_opt arg env with
        | Some (Impl (x, y)) when y = a -> App (Var arg, prove env x)
        | Some (Disj (x, y)) -> 
            let z = arg in (* need ids *)
            let u = prove ((z, x) :: env) a in
            let v = prove ((z, y) :: env) a in
            Case (Var arg, z, u, z, v)
        | Some (Falsity) -> Absurd (Var arg, a)
        | Some Nat ->
            let z = prove env a in
            let x = "x" in
            let y = "y" in
            let s = prove ((x, Nat) :: (y, a) :: env) a in
            Rec (Var arg, z, x, y, s)
        | _ -> error "Cannot eliminate."
      )
  | "cut" ->
      (
        let cutTy = ty_of_string arg in
        let totalProof = prove env (Impl (cutTy, a)) in
        let cutProof = prove env (cutTy) in
        App (totalProof , cutProof)
      )
  | "left" ->
      (
        match a with
        | Disj (x, y) -> Inl (prove env x, y)
        | _ -> error "Cannot left."
      )
  | "right" ->
      (
        match a with
        | Disj (x, y) -> Inr (x, prove env y)
        | _ -> error "Cannot right."
      )
  | "fst" -> 
      (
        match List.assoc_opt arg env with
        | Some (Conj (x, _)) when x = a -> Fst (Var arg)
        | _ -> error "Cannot fst."
      )
  | "snd" -> 
      (
        match List.assoc_opt arg env with
        | Some (Conj (_, y)) when y = a -> Snd (Var arg)
        | _ -> error "Cannot snd."
      )
  | cmd -> error ("Unknown command: " ^ cmd)
         
let () =
  print_endline "Please enter the formula to prove:";
  start_logging "tmp.proof";
  let a = input_line stdin in
  log_command a;
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_endline (infer_type [] t |> string_of_ty);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  stop_logging ();
  print_endline "ok."

