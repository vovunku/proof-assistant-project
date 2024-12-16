open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

(* Fill me in! *)
let rec to_string = function
  | Type -> "Type"
  | Var v -> v
  | App (e1, e2) -> "(" ^ to_string e1 ^ " " ^ to_string e2 ^ ")"
  | Abs (v, e1, e2) -> "(λ" ^ v ^ ":" ^ to_string e1 ^ ". " ^ to_string e2 ^ ")"
  | Pi (v, e1, e2) -> "(Π" ^ v ^ ":" ^ to_string e1 ^ ". " ^ to_string e2 ^ ")"
  | Nat -> "Nat"
  | Z -> "Z"
  | S e -> "(S " ^ to_string e ^ ")"
  | Ind (p, z, s,  n) -> "(Ind " ^ to_string p ^ " " ^ to_string z ^ " " ^ to_string s ^ " " ^ to_string n ^ ")"
  | Eq (e1, e2) -> "(Eq " ^ to_string e1 ^ " " ^ to_string e2 ^ ")"
  | Refl e -> "(Refl " ^ to_string e ^ ")"
  | J (p, r, x, y, e) -> "(J " ^ to_string p ^ " " ^ to_string r ^ " " ^ to_string x ^ " " ^ to_string y ^ " " ^ to_string e ^ ")"

let counter = ref 0

let fresh_var () =
  incr counter;
  "x" ^ string_of_int !counter

let rec subst x t u = match u with
  | Type -> Type
  | Var v -> if v = x then t else Var v
  | App (e1, e2) -> App (subst x t e1, subst x t e2)
  | Abs (v, tv, e) ->
    let v' = fresh_var () in
    let e' = subst v (Var v') e in
    Abs (v', subst x t tv, subst x t e')
  | Pi (v, e1, e2) ->
    let v' = fresh_var () in
    let e2' = subst v (Var v') e2 in
    Pi (v', subst x t e1, subst x t e2')
  | Nat -> Nat
  | Z -> Z
  | S e -> S (subst x t e)
  | Ind (e1, e2, e3, e4) -> Ind (subst x t e1, subst x t e2, subst x t e3, subst x t e4)
  | Eq (e1, e2) -> Eq (subst x t e1, subst x t e2)
  | Refl e -> Refl (subst x t e)
  | J (e1, e2, e3, e4, e5) -> J (subst x t e1, subst x t e2, subst x t e3, subst x t e4, subst x t e5)

type context = (var * (expr * expr option)) list
 
let string_of_context ctx =
  let string_of_binding (v, (ty, value)) =
    match value with
    | None -> v ^ " : " ^ to_string ty
    | Some ev -> v ^ " : " ^ to_string ty ^ " = " ^ to_string ev
  in
  String.concat "\n" (List.map string_of_binding ctx)

let rec normalize ctx = function
  | Type -> Type
  | Var v -> (
      match List.assoc_opt v ctx with
      | Some (_, Some value) -> normalize ctx value
      | _ -> Var v)
  | App (e1, e2) ->
      let e1' = normalize ctx e1 in
      let e2' = normalize ctx e2 in
      (match e1' with
      | Abs (v, _, body) -> normalize ctx (subst v e2' body)
      | _ -> App (e1', e2'))
  | Abs (v, t, e) ->
      let t' = normalize ctx t in
      let e' = normalize ((v, (t', None)) :: ctx) e in
      Abs (v, t', e')
  | Pi (v, e1, e2) ->
      let e1' = normalize ctx e1 in
      let e2' = normalize ((v, (e1', None)) :: ctx) e2 in
      Pi (v, e1', e2')
  | Nat -> Nat
  | Z -> Z
  | S e -> S (normalize ctx e)
  | Ind (p, z, s, n) ->
    let p' = normalize ctx p in
    let z' = normalize ctx z in
    let s' = normalize ctx s in
    let n' = normalize ctx n in
    (match n' with
      | Z -> z'
      | S m -> normalize ctx (App (App (s', S m), Ind (p', z', s', m)))
      | _ -> Ind (p', z', s', n'))
  | Eq (e1, e2) -> Eq (normalize ctx e1, normalize ctx e2)
  | Refl e -> Refl (normalize ctx e)
  | J (p, r, x, y, e) ->
    let p' = normalize ctx p in
    let r' = normalize ctx r in
    let x' = normalize ctx x in
    let y' = normalize ctx y in
    let e' = normalize ctx e in
    match e' with
    | Refl z when x' = y' && z = x' -> normalize ctx (App (r', x'))
    | _ -> J (p', r', x', y', e')

let rec alpha e1 e2 =
  match e1, e2 with
  | Type, Type -> true
  | Var v1, Var v2 -> v1 = v2
  | App (e1_1, e1_2), App (e2_1, e2_2) -> alpha e1_1 e2_1 && alpha e1_2 e2_2
  | Abs (v1, t1, e1), Abs (v2, t2, e2) ->
      let v' = fresh_var () in
      alpha t1 t2 && alpha (subst v1 (Var v') e1) (subst v2 (Var v') e2)
  | Pi (v1, e1_1, e1_2), Pi (v2, e2_1, e2_2) ->
      let v' = fresh_var () in
      alpha e1_1 e2_1 && alpha (subst v1 (Var v') e1_2) (subst v2 (Var v') e2_2)
  | Nat, Nat -> true
  | Z, Z -> true
  | S e1, S e2 -> alpha e1 e2
  | Ind (e1_1, e1_2, e1_3, e1_4), Ind (e2_1, e2_2, e2_3, e2_4) ->
      alpha e1_1 e2_1 && alpha e1_2 e2_2 && alpha e1_3 e2_3 && alpha e1_4 e2_4
  | Eq (e1_1, e1_2), Eq (e2_1, e2_2) -> alpha e1_1 e2_1 && alpha e1_2 e2_2
  | Refl e1, Refl e2 -> alpha e1 e2
  | J (e1_1, e1_2, e1_3, e1_4, e1_5), J (e2_1, e2_2, e2_3, e2_4, e2_5) ->
      alpha e1_1 e2_1 && alpha e1_2 e2_2 && alpha e1_3 e2_3 && alpha e1_4 e2_4 && alpha e1_5 e2_5
  | _ -> false

let conv ctx e1 e2 =
  alpha (normalize ctx e1) (normalize ctx e2)

exception Type_error of string

let rec infer ctx e = match e with
  | Type -> Type
  | Var v -> (
      match List.assoc_opt v ctx with
      | Some (ty, _) -> ty
      | None -> raise (Type_error ("Unbound variable: " ^ v)))
  | App (e1, e2) -> (
      match infer ctx e1 with
      | Pi (v, ty1, ty2) ->
          let ty1' = infer ctx e2 in
          if conv ctx ty1 ty1' then subst v e2 ty2
          else raise (Type_error "Function argument type mismatch")
      | _ -> raise (Type_error "Application of a non-function"))
  | Abs (v, ty, e) ->
      let ty' = infer ((v, (ty, None)) :: ctx) e in
      Pi (v, ty, ty')
  | Pi (v, ty1, ty2) ->
      let ty1' = infer ctx ty1 in
      let ty2' = infer ((v, (ty1, None)) :: ctx) ty2 in
      if conv ctx ty1' Type && conv ctx ty2' Type then Type
      else raise (Type_error "Invalid Pi type")
  | Nat -> Type
  | Z -> Nat
  | S e ->
      if conv ctx (infer ctx e) Nat then Nat
      else raise (Type_error "Invalid successor argument")
  | Ind (p, z, s, n) ->
      let pty = infer ctx p in
      let zty = infer ctx z in
      let sty = infer ctx s in
      let nty = infer ctx n in
      if conv ctx pty (Pi ("n", Nat, Type)) &&
          conv ctx zty (App (p, Z)) &&
          conv ctx sty (Pi ("n", Nat, Pi ("n'", App (p, Var "n"), App (p, S (Var "n"))))) &&
          conv ctx nty Nat then
        App (p, n)
      else raise (Type_error "Invalid Ind arguments")
  | Eq (e1, e2) ->
      let ty1 = infer ctx e1 in
      let ty2 = infer ctx e2 in
      if conv ctx ty1 ty2 then Type
      else raise (Type_error "Equality type mismatch")
  | Refl e ->
      let _ = infer ctx e in
      Eq (e, e)
  | J (p, r, x, y, e) ->
      let pty = infer ctx p in
      let rty = infer ctx r in
      let xty = infer ctx x in
      let yty = infer ctx y in
      let ety = infer ctx e in
      if conv ctx xty yty &&
          conv ctx pty (Pi ("x", xty, Pi ("y", xty, Pi ("eq", Eq (Var "x", Var "y"), Type)))) &&
          conv ctx rty (Pi ("x", xty, App (App (App (p, Var "x"), Var "x"), Refl (Var "x")))) &&
          conv ctx ety (Eq (x, y)) then
        App (App (App (p, x), y), e)
      else raise (Type_error "Invalid J arguments")

let check ctx e ty =
  let ty' = infer ctx e in
  if conv ctx ty ty' then ()
  else raise (Type_error "Type mismatch")

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s, ""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
        let x, sa = split ':' arg in
        let a = of_string sa in
        check !env a Type;
        env := (x,(a,None)) :: !env;
        print_endline (x^" assumed of type "^to_string a)
      | "define" ->
        let x, st = split '=' arg in
        let t = of_string st in
        let a = infer !env t in
        env := (x,(a,Some t)) :: !env;
        print_endline (x^" defined to "^to_string t^" of type "^to_string a)
      | "context" ->
        print_endline (string_of_context !env)
      | "type" ->
        let t = of_string arg in
        let a = infer !env t in
        print_endline (to_string t^" is of type "^to_string a)
      | "check" ->
        let t, a = split '=' arg in
        let t = of_string t in
        let a = of_string a in
        check !env t a;
        print_endline "Ok."
      | "eval" ->
        let t = of_string arg in
        let _ = infer !env t in
        print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: "^cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: "^err^".")
    | Type_error err -> print_endline ("Typing error :"^err^".")
    | Parsing.Parse_error -> print_endline ("Parsing error.")
  done;
  print_endline "Bye."