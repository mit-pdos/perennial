From Coq Require Import String.
From stdpp Require Import gmap binders strings base.
From Coq Require Import Logic.Classical_Prop.

Inductive typeid :=
| Z_id | nat_id | string_id
.
Definition typeid_interp (i:typeid) : Type :=
  match i with
  | Z_id => Z
  | nat_id => nat
  | string_id => string
  end
.
Definition val : Type := { i : typeid & typeid_interp i }.

Class ToVal T := {
    to_val (x:T) : val
  }
.
Instance natToVal : ToVal nat :=
  {
    to_val n := existT nat_id n
  }.
Instance stringToVal : ToVal string :=
  {
    to_val x := existT string_id x
  }.

Definition loc := Z.

(* Heap stores these untyped vals *)
Definition heap := gmap loc val.

Inductive expr :=
(* Values *)
| Val (v : val)
| Comp (f : val → option val)

(* Base lambda calculus *)
| Var (x : string)
| Rec (f x : binder) (e : expr)
| App (e1 e2 : expr)
.

Instance lem_all (x y : typeid) : Decision (x = y).
Proof. unfold Decision. decide equality. Qed.

Definition x : expr :=
  Comp (λ (x : val),
          match x with
          | existT tid y =>
              if decide (tid = string_id) then Some x
              else Some (to_val "bad")
          end
       )
.

Eval cbv in x.
