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

Require Import Coq.Logic.JMeq.
Arguments JMeq _ _ _ _ : clear implicits.
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
      simpl in *.
      (*
      enough (∃ y p', JMeq y p' _ p ∧
                      P (existT (S x) p')).
      assert (JMeq _ p _ p).
      { done. }
      simpl in H1.
      set y := (val3 x) in H1.
      destruct y.
      Set Printing All.
      destruct (val3 x). in p *.
      simpl in p.
      fold y in p.
      inversion y in p.
      inversion y.
      set y := projT1 (val3 (S x)).
      inversion y.
      change (projT1 (val3 (S x)))
      simpl in *.
      set z := ((λ x, x) : projT1 (let (V, s) := val3 x in
                                   let (Heqdec, Hcount) := s in
                                   existT (val2 V) (existT (EqDecision_val2 V) (Countable_val2 V))) →
                            projT1 (val3 (S x))
               ).
      change (p) with (z p).
      set w:=(projT1 (val3 (S x))).
      fold w in z.
      destruct (val3 x).
      set y:=(val3 x).
      fold y in p.
      destruct y.
      destruct (val3 x).
      unfold val3 in p.
      assert (∃ t, t = val3 x) as [t Heq] by eauto.
      destruct t.
      assert (∃ p', p' = p) as [p' Hpeq] by eauto.
      rewrite Heq in p'.
      refine (match t with
              | existT V s => _
              end
             ).
      destruct (val3 x) eqn:X. *)
Admitted.

Inductive val4 :=
| NatV4 : nat → val4
| MapV4 : gmap positive positive → val4
.

Instance EqDecision_val4 : EqDecision val4.
Proof. solve_decision. Qed.

Local Ltac count t_rec :=
  let rec go num f :=
      (let t := type of f in
       let t := eval cbv beta in t in
           lazymatch t with
           | nat -> _ => go constr:(S num) constr:(f num)
           | _ => f
           end) in
  go constr:(0%nat) constr:(t_rec (fun _ => nat)).

Local Ltac match_n num :=
  lazymatch num with
  | 0%nat => uconstr:(fun (n:nat) => _)
  | _ => let num' := (eval cbv in (Nat.pred num)) in
        let match_n' := match_n num' in
        uconstr:(fun (n:nat) => match n with
                       | O => _
                       | S n' => match_n' n'
                       end)
  end.

Ltac solve_countable rec num :=
  let inj := count rec in
  let dec := match_n num in
  unshelve (refine (inj_countable' inj dec _); intros []; reflexivity);
  constructor.

Instance Countable_val4 : Countable val4.
Proof.
  refine (inj_countable'
            (λ (v:val4), match v with
                         | NatV4 n => inl n
                         | MapV4 m => inr m
                         end)
            (λ e, match e with
                  | inl n => NatV4 n
                  | inr m => MapV4 m
                  end)
            _).
  by intros [].
Qed.

Definition val5 := val4.

Definition MapV5 (m : gmap val5 val5) : val5 :=
  MapV4 (map_fold (λ k v m, <[encode k := encode v]> m) ∅ m).

Definition NatV5 (n : nat) : val5 := NatV4 n.

Definition val5_ind :
  ∀ (P : val5 → Prop),
  (∀ n : nat, P (NatV5 n)) →
  (∀ g : gmap val5 val5, P (MapV5 g)) →
  ∀ v, P v.
Proof.
  intros.
  induction v.
  { done. }
  (* XXX: stuck here because g is an arbitrary [gmap positive positive], whereas
     H0 only works for maps found by encoding a [gmap val5 val5]*)
Abort.


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
