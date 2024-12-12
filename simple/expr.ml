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
  | Rec of tm * tm * var * var * tm 
