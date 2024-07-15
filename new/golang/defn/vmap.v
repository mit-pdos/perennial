From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import list.

(* This defines a "value map" for use in other GooseLang libraries. It does not
   provide a semantics for Go maps; for that, see map.v *)

Module vmap.
Section goose_lang.
Context {ext:ffi_syntax}.
Local Coercion Var' (s:string) : expr := Var s.

Fixpoint ind_n (f : Type → Type) (n : nat) : Type :=
  match n with
  | O => False
  | S n => f (ind_n f n)
  end.

Definition ind (f : Type → Type) : Type :=
  { n : nat & ind_n f n }.


Lemma val_exists :
  ∃ (T : Type) (Int : nat → T) (Heqdec : EqDecision T) (Hcount : Countable T) (Map : gmap T T → T)
    (val_rect : ∀ (P : T → Prop),
       (∀ (n : nat), P (Int n)) →
       (∀ (m : gmap T T) (Helems : map_Forall (λ k v, P k ∧ P v) m), P (Map m)) →
       (∀ v, P v)), True
.
Proof.
  exists (ind (λ T, (nat + T)%type)).
Abort.

Inductive val2 (valρ : Type) `{Countable valρ} : Type :=
| NatV (n : nat)
| MapV (g : valρ → option valρ)
.

Instance EqDecision_val2 (valρ : Type) {Hdec : EqDecision valρ} {Hcount : Countable valρ} :
  EqDecision (val2 valρ).
Proof. Admitted.

Instance Countable_val2 (valρ : Type) {Hdec : EqDecision valρ} {Hcount : Countable valρ} :
  Countable (val2 valρ).
Proof. Admitted.

Instance EqDecision_False : EqDecision False.
Proof. by intros ?. Qed.
Instance Countable_False : Countable False.
Proof. refine (Build_Countable _ _ (False_rect positive) (λ _, None) _). by intros. Qed.

Fixpoint val3 (n : nat) : { V : Type & { H : EqDecision V & Countable V} } :=
  match n with
  | O => existT (((λ x, x) : Prop → Type) False) (existT EqDecision_False Countable_False)
  | S n =>
      match (val3 n) with
      | existT V (existT Heqdec Hcount) => existT (@val2 V Heqdec Hcount)
                                            (existT (@EqDecision_val2 V Heqdec Hcount) (@Countable_val2 _ _ _))
      end
  end.


Instance EqDecision_sigT A P (HT : EqDecision A) (HP : ∀ a, EqDecision (P a)) :
  EqDecision {x : A & P x}.
Proof.
  unfold EqDecision.
  intros. destruct x, y.
  destruct (decide (x = x0)).
  {
    subst.
    enough (Decision (p = p0)).
    { destruct H; subst.
      * by left.
      * right. intros H. by apply Eqdep.EqdepTheory.inj_pair2 in H. }
    solve_decision.
  }
  right. intros H. by apply eq_sigT_fst in H.
Qed.

Instance Countable_sigT A P (HTeq : EqDecision A) (HT : Countable A)
  (HPeq : ∀ a, EqDecision (P a)) (HP : ∀ a, Countable (P a)) :
  Countable { x : A & P x }.
Proof.
  (* use prod_countable's encode and decode. *)
  set sigT_encode:=(λ s : {x : A & P x},
                 match s with
                 | existT x y => encode (encode x, encode y)
                 end
              ).
  set sigT_decode:=((λ (e : positive),
                      match (decode e) : option (positive * positive) with
                      | None => None
                      | Some (a, b) =>
                          match decode a with
                          | Some a =>
                              match decode b with
                              | Some b => Some (existT a b)
                              | _ => None
                              end
                          | _ => None
                          end
                      end)
              : _ → option {x : A & P x}).
  refine (Build_Countable _ _ sigT_encode sigT_decode _). intros.
  destruct x. unfold sigT_decode. simpl.
  by repeat rewrite decode_encode.
Qed.

Lemma val_exists :
  ∃ (T : Type) (Int : nat → T) (Heqdec : EqDecision T) (Hcount : Countable T) (Map : gmap T T → T)
    (val_rect : ∀ (P : T → Prop),
       (∀ (n : nat), P (Int n)) →
       (∀ (m : gmap T T) (Helems : map_Forall (λ k v, P k ∧ P v) m), P (Map m)) →
       (∀ v, P v)), True
.
Proof.
  exists {n : nat & projT1 (val3 n)}.
  eexists (λ n, (existT 1%nat (NatV _ n))).
  eexists _. Unshelve.
  2:{ (* EqDecision *)
    apply EqDecision_sigT; first apply _.
    intros [|a] x y.
    { simpl in *. done. }
    { simpl in *. destruct (val3 a), s. solve_decision. }
  }
  eexists _. Unshelve.
  2:{
    apply Countable_sigT; first apply _.
    intros [|a].
    { simpl. refine (Build_Countable _ _ (False_rect positive) (λ _, None) _). by intros. }
    simpl.
    destruct (val3 a), s. simpl.
    apply _.
  }
  eexists _. Unshelve.
  2:{ intros. (* find the maximum step index over the gmap, then convert everything to that level. *)
      admit. }
  eexists _. Unshelve.
  2:{ intros. (* induction principle*)
      destruct v.
      induction x.
      { simpl in *. by exfalso. }
      clear IHx.
      simpl in *.
      destruct (val3 x).
Qed

Definition Insert : val := λ: "k" "v" "m", [(Pair "k" "v") ; "m"].

Definition Get : val :=
  rec: "get" "k" "m" :=
    list.Match "m"
      (λ: <>, InjLV #()) (* [] *)
      (λ: "kv" "m",     (* kv::m *)
         let: ("k2", "v") := "kv" in
         if: "k" = "k2" then
           InjR "v"
         else
           "get" "k" "m")
.

Definition Delete : val :=
  rec: "delete" "k" "m" :=
    list.Match "m"
    (λ: <>, [])
    (λ: "kv" "m",
       let: ("k2", "v") := "kv" in
       let: "m" := "delete" "k" "m" in
       if: "k" = "k2" then "m"
       else list.Cons (Pair "k2" "v") "m"
    )
.

Definition Match : val :=
  λ: "m" "handleEmpty" "handleInsert",
    list.Match "m" "handleEmpty"
      (λ: "kv" "m",
         let: ("k", "v") := "kv" in
         "handleInsert" (Delete "m" "k") "k" "v"
      )
.

Definition val_def (m : gmap val val) :=
  list.val (map_fold (λ k v kvs, (PairV k v) :: kvs) ([] : list val) m).
Program Definition val := unseal (_:seal (@val_def)). Obligation 1. by eexists. Qed.
Definition val_unseal : val = _ := seal_eq _.
End goose_lang.
End vmap.

Notation "{[]}" := (vmap.val ∅) : expr_scope.
Notation "{[  k  :=  v  ]}" :=
  (App (App (App (Val vmap.Insert) k) v) (Val (vmap.val ∅))) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11 ; k12 := v12  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11 ; k12 := v12 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11 ; k12 := v12 ; k13 := v13  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11 ; k12 := v12 ; k13 := v13 ]}) : expr_scope.
