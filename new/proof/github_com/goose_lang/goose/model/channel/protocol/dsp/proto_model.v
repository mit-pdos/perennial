(*
   This file is part of Actris (https://gitlab.mpi-sws.org/iris/actris).

   Copyright (c) Actris developers and contributors.
   Distributed under the terms of the BSD 3-Clause License; see
   https://gitlab.mpi-sws.org/iris/actris/-/blob/master/LICENSE
   for the full license text.
*)

(** This file defines the model of dependent separation protocols as the
solution of a recursive domain equation, along with various primitive
operations, such as append and map.

Important: This file should not be used directly, but rather the wrappers in
[proto] should be used.

Dependent Separation Protocols are modeled as the solution of the following
recursive domain equation:

[proto = 1 + (action * (V → ▶ proto → PROP))]

Here, the left-hand side of the sum is used for the terminated process, while
the right-hand side is used for the communication constructors. The type
[action] is an inductively defined datatype with two constructors [Send] and
[Recv]. Compared to having an additional sum in [proto], this makes it
possible to factorize the code in a better way.

The remainder [V → ▶ proto → PROP] is a predicate that ranges over the
communicated value [V] and the tail protocol [proto]. Note that to solve this
recursive domain equation using Iris's COFE solver, the recursive occurrence
of [proto] appear under the later [▶].

On top of the type [proto], we define the constructors:

- [proto_end], which constructs the left-side of the sum.
- [proto_msg], which takes an action and a predicate and constructs the
  right-hand side of the sum accordingly.

The defined functions on the type [proto] are:

- [proto_map], which can be used to map the actions and the propositions of
  a given protocol.
- [proto_app], which appends two protocols [p1] and [p2], by substituting
  all terminations [END] in [p1] with [p2]. *)
From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import proofmode.
From New.proof.github_com.goose_lang.goose.model.channel Require Import cofe_solver_2.

Set Default Proof Using "Type".

Module Export action.
  Inductive action := Send | Recv.
  Global Instance action_inhabited : Inhabited action := populate Send.
  Definition action_dual (a : action) : action :=
    match a with Send => Recv | Recv => Send end.
  Global Instance action_dual_involutive : Involutive (=) action_dual.
  Proof. by intros []. Qed.
  Canonical Structure actionO := leibnizO action.
End action.

Definition proto_auxO (V : Type) (PROP : ofe) (A : ofe) : ofe :=
  optionO (prodO actionO (V -d> laterO A -n> PROP)).
Definition proto_auxOF (V : Type) (PROP : ofe) : oFunctor :=
  optionOF (actionO * (V -d> ▶ ∙ -n> PROP)).

Definition pre_proto_result (V : Type) := result_2 (proto_auxOF V).
Definition pre_proto (V : Type) (PROPn PROP : ofe) `{!Cofe PROPn, !Cofe PROP} : ofe :=
  solution_2_car (pre_proto_result V) PROPn _ PROP _.
Global Instance pre_proto_cofe {V} `{!Cofe PROPn, !Cofe PROP} :
  Cofe (pre_proto V PROPn PROP).
Proof. apply _. Qed.

Definition proto (V : Type) (PROPn PROP : ofe) `{!Cofe PROPn, !Cofe PROP} : ofe :=
  proto_auxO V PROP (pre_proto V PROP PROPn).
Global Instance proto_cofe {V} `{!Cofe PROPn, !Cofe PROP} :
  Cofe (proto V PROPn PROP).
Proof. apply _. Qed.

Lemma proto_iso {V} `{!Cofe PROPn, !Cofe PROP} :
  ofe_iso (proto V PROPn PROP) (pre_proto V PROPn PROP).
Proof. apply pre_proto_result. Qed.

Definition proto_fold {V} `{!Cofe PROPn, !Cofe PROP} :
  pre_proto V PROPn PROP -n> proto V PROPn PROP := ofe_iso_2 proto_iso.
Definition proto_unfold {V} `{!Cofe PROPn, !Cofe PROP} :
  proto V PROPn PROP -n> pre_proto V PROPn PROP := ofe_iso_1 proto_iso.
Lemma proto_fold_unfold {V} `{!Cofe PROPn, !Cofe PROP} (p : proto V PROPn PROP) :
  proto_fold (proto_unfold p) ≡ p.
Proof. apply (ofe_iso_21 proto_iso). Qed.
Lemma proto_unfold_fold {V} `{!Cofe PROPn, !Cofe PROP} (p : pre_proto V PROPn PROP) :
  proto_unfold (proto_fold p) ≡ p.
Proof. apply (ofe_iso_12 proto_iso). Qed.

Definition proto_end {V} `{!Cofe PROPn, !Cofe PROP} : proto V PROPn PROP :=
  None.
Definition proto_message {V} `{!Cofe PROPn, !Cofe PROP} (a : action)
    (m : V → laterO (proto V PROP PROPn) -n> PROP) : proto V PROPn PROP :=
  Some (a, λ v, m v ◎ laterO_map proto_fold).

Global Instance proto_message_ne {V} `{!Cofe PROPn, !Cofe PROP} a n :
  Proper (pointwise_relation V (dist n) ==> dist n)
         (proto_message (PROPn:=PROPn) (PROP:=PROP) a).
Proof.
  intros c1 c2 Hc. rewrite /proto_message.
  (repeat constructor)=> //= v. by f_equiv.
Qed.
Global Instance proto_message_proper {V} `{!Cofe PROPn, !Cofe PROP} a :
  Proper (pointwise_relation V (≡) ==> (≡))
         (proto_message (PROPn:=PROPn) (PROP:=PROP) a).
Proof.
  intros c1 c2 Hc. rewrite /proto_message.
  (repeat constructor)=> //= v. by f_equiv.
Qed.

Lemma proto_case {V} `{!Cofe PROPn, !Cofe PROP} (p : proto V PROPn PROP) :
  p ≡ proto_end ∨ ∃ a m, p ≡ proto_message a m.
Proof.
  destruct p as [[a m]|]; [|by left].
  right. exists a, (λ v, m v ◎ laterO_map proto_unfold).
  rewrite /proto_message. do 2 f_equiv. intros v p; simpl. f_equiv.
  rewrite -later_map_compose -{1}(later_map_id p).
  apply later_map_ext=> p' /=. by rewrite proto_unfold_fold.
Qed.
Global Instance proto_inhabited {V} `{!Cofe PROPn, !Cofe PROP} :
  Inhabited (proto V PROPn PROP) := populate proto_end.

Lemma proto_message_equivI `{!BiInternalEq SPROP} {V} `{!Cofe PROPn, !Cofe PROP} a1 a2 m1 m2 :
  proto_message (V:=V) (PROPn:=PROPn) (PROP:=PROP) a1 m1 ≡ proto_message a2 m2
  ⊣⊢@{SPROP} ⌜ a1 = a2 ⌝ ∧ (∀ v p', m1 v p' ≡ m2 v p').
Proof.
  rewrite /proto_message option_equivI prod_equivI /=.
  rewrite discrete_eq discrete_fun_equivI. f_equiv; [done|]. f_equiv=> x.
  rewrite ofe_morO_equivI /=. iSplit; iIntros "H %p //".
  assert (p ≡ later_map proto_fold (later_map proto_unfold p)) as ->; last done.
  rewrite -later_map_compose -{1}(later_map_id p).
  apply later_map_ext=> p' /=. by rewrite proto_fold_unfold.
Qed.
Lemma proto_message_end_equivI `{!BiInternalEq SPROP} {V} `{!Cofe PROPn, !Cofe PROP} a m :
  proto_message (V:=V) (PROPn:=PROPn) (PROP:=PROP) a m ≡ proto_end ⊢@{SPROP} False.
Proof. by rewrite option_equivI. Qed.
Lemma proto_end_message_equivI `{!BiInternalEq SPROP} {V} `{!Cofe PROPn, !Cofe PROP} a m :
  proto_end ≡ proto_message (V:=V) (PROPn:=PROPn) (PROP:=PROP) a m ⊢@{SPROP} False.
Proof. by rewrite internal_eq_sym proto_message_end_equivI. Qed.

Definition proto_elim {V} `{!Cofe PROPn, !Cofe PROP} {A}
    (x : A) (f : action → (V → laterO (proto V PROP PROPn) -n> PROP) → A)
    (p : proto V PROPn PROP) : A :=
  match p with
  | None => x
  | Some (a, m) => f a (λ v, m v ◎ laterO_map proto_unfold)
  end.
Global Arguments proto_elim : simpl never.

Lemma proto_elim_ne {V} `{!Cofe PROPn, !Cofe PROP} {A : ofe}
    (x : A) (f1 f2 : action → (V → laterO (proto V PROP PROPn) -n> PROP) → A) p1 p2 n :
  (∀ a m1 m2, (∀ v, m1 v ≡{n}≡ m2 v) → f1 a m1 ≡{n}≡ f2 a m2) →
  p1 ≡{n}≡ p2 →
  proto_elim x f1 p1 ≡{n}≡ proto_elim x f2 p2.
Proof.
  intros Hf [[a1 m1] [a2 m2] [[=->] ?]|]; rewrite /proto_elim //=.
  apply Hf=> v. by f_equiv.
Qed.

Lemma proto_elim_end {V} `{!Cofe PROPn, !Cofe PROP} {A : ofe}
    (x : A) (f : action → (V → laterO (proto V PROP PROPn) -n> PROP) → A) :
  proto_elim x f proto_end ≡ x.
Proof. done. Qed.
Lemma proto_elim_message {V} `{!Cofe PROPn, !Cofe PROP} {A : ofe}
    (x : A) (f : action → (V → laterO (proto V PROP PROPn) -n> PROP) → A) a m :
  (∀ a, Proper (pointwise_relation _ (≡) ==> (≡)) (f a)) →
  proto_elim x f (proto_message a m) ≡ f a m.
Proof.
  intros. rewrite /proto_elim /proto_message /=. f_equiv=> v p /=. f_equiv.
  rewrite -later_map_compose -{2}(later_map_id p).
  apply later_map_ext=> p' /=. by rewrite proto_fold_unfold.
Qed.

(** Functor *)
Program Definition proto_map_aux {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (g : PROP -n> PROP') (rec : proto V PROP' PROPn' -n> proto V PROP PROPn) :
    proto V PROPn PROP -n> proto V PROPn' PROP' := λne p,
  proto_elim proto_end (λ a m, proto_message a (λ v, g ◎ m v ◎ laterO_map rec)) p.
Next Obligation.
  intros V PROPn ? PROPn' ? PROP ? PROP' ? g rec n p1 p2 Hp.
  apply proto_elim_ne=> // a m1 m2 Hm. by repeat f_equiv.
Qed.

Global Instance proto_map_aux_contractive {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'} (g : PROP -n> PROP') :
  Contractive (proto_map_aux (V:=V) (PROPn:=PROPn) (PROPn':=PROPn') g).
Proof.
  intros n rec1 rec2 Hrec p. simpl. apply proto_elim_ne=> // a m1 m2 Hm.
  f_equiv=> v p' /=. do 2 f_equiv; [done|].
  apply Next_contractive; by dist_later_intro as n' Hn'.
Qed.

Definition proto_map_aux_2 {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP')
    (rec : proto V PROPn PROP -n> proto V PROPn' PROP') :
    proto V PROPn PROP -n> proto V PROPn' PROP' :=
  proto_map_aux g (proto_map_aux gn rec).
Global Instance proto_map_aux_2_contractive {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
  Contractive (proto_map_aux_2 (V:=V) gn g).
Proof.
  intros n rec1 rec2 Hrec. rewrite /proto_map_aux_2.
  f_equiv. by apply proto_map_aux_contractive.
Qed.
Definition proto_map {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
    proto V PROPn PROP -n> proto V PROPn' PROP' :=
  fixpoint (proto_map_aux_2 gn g).

Lemma proto_map_unfold {V}
    `{Hcn:!Cofe PROPn, Hcn':!Cofe PROPn', Hc:!Cofe PROP, Hc':!Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') p :
  proto_map (V:=V) gn g p ≡ proto_map_aux g (proto_map g gn) p.
Proof.
  apply equiv_dist=> n. revert PROPn Hcn PROPn' Hcn' PROP Hc PROP' Hc' gn g p.
  induction (lt_wf n) as [n _ IH]=>
    PROPn Hcn PROPn' Hcn' PROP Hc PROP' Hc' gn g p.
  etrans; [apply equiv_dist, (fixpoint_unfold (proto_map_aux_2 gn g))|].
  apply proto_map_aux_contractive; constructor=> n' ?. symmetry. by apply: IH.
Qed.
Lemma proto_map_end {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
  proto_map (V:=V) gn g proto_end ≡ proto_end.
Proof. by rewrite proto_map_unfold /proto_map_aux. Qed.
Lemma proto_map_message {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') a m :
  proto_map (V:=V) gn g (proto_message a m)
  ≡ proto_message a (λ v, g ◎ m v ◎ laterO_map (proto_map g gn)).
Proof.
  rewrite proto_map_unfold /proto_map_aux /=.
  rewrite ->proto_elim_message; [done|].
  intros a' m1 m2 Hm. f_equiv; solve_proper.
Qed.

Lemma proto_map_ne {V}
    `{Hcn:!Cofe PROPn, Hcn':!Cofe PROPn', Hc:!Cofe PROP, Hc':!Cofe PROP'}
    (gn1 gn2 : PROPn' -n> PROPn) (g1 g2 : PROP -n> PROP') p n :
  gn1 ≡{n}≡ gn2 → g1 ≡{n}≡ g2 →
  proto_map (V:=V) gn1 g1 p ≡{n}≡ proto_map (V:=V) gn2 g2 p.
Proof.
  revert PROPn Hcn PROPn' Hcn' PROP Hc PROP' Hc' gn1 gn2 g1 g2 p.
  induction (lt_wf n) as [n _ IH]=>
    PROPn ? PROPn' ? PROP ? PROP' ? gn1 gn2 g1 g2 p Hgn Hg /=.
  destruct (proto_case p) as [->|(a & m & ->)]; [by rewrite !proto_map_end|].
  rewrite !proto_map_message /=.
  apply proto_message_ne=> // v p' /=. f_equiv; [done|]. f_equiv.
  apply Next_contractive; dist_later_intro as n' Hn'; eauto using dist_lt.
Qed.
Lemma proto_map_ext {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn1 gn2 : PROPn' -n> PROPn) (g1 g2 : PROP -n> PROP') p :
  gn1 ≡ gn2 → g1 ≡ g2 → proto_map (V:=V) gn1 g1 p ≡ proto_map (V:=V) gn2 g2 p.
Proof.
  intros Hgn Hg. apply equiv_dist=> n.
  apply proto_map_ne=> // ?; by apply equiv_dist.
Qed.
Lemma proto_map_id {V} `{Hcn:!Cofe PROPn, Hc:!Cofe PROP} (p : proto V PROPn PROP) :
  proto_map cid cid p ≡ p.
Proof.
  apply equiv_dist=> n. revert PROPn Hcn PROP Hc p.
  induction (lt_wf n) as [n _ IH]=> PROPn ? PROP ? p /=.
  destruct (proto_case p) as [->|(a & m & ->)]; [by rewrite !proto_map_end|].
  rewrite !proto_map_message /=. apply proto_message_ne=> // v p' /=. f_equiv.
  apply Next_contractive; dist_later_intro as n' Hn'; auto.
Qed.
Lemma proto_map_compose {V}
   `{Hcn:!Cofe PROPn, Hcn':!Cofe PROPn', Hcn'':!Cofe PROPn'',
     Hc:!Cofe PROP, Hc':!Cofe PROP', Hc'':!Cofe PROP''}
    (gn1 : PROPn'' -n> PROPn') (gn2 : PROPn' -n> PROPn)
    (g1 : PROP -n> PROP') (g2 : PROP' -n> PROP'') (p : proto V PROPn PROP) :
  proto_map (gn2 ◎ gn1) (g2 ◎ g1) p ≡ proto_map gn1 g2 (proto_map gn2 g1 p).
Proof.
  apply equiv_dist=> n. revert PROPn Hcn PROPn' Hcn' PROPn'' Hcn''
    PROP Hc PROP' Hc' PROP'' Hc'' gn1 gn2 g1 g2 p.
  induction (lt_wf n) as [n _ IH]=> PROPn ? PROPn' ? PROPn'' ?
    PROP ? PROP' ? PROP'' ? gn1 gn2 g1 g2 p /=.
  destruct (proto_case p) as [->|(a & c & ->)]; [by rewrite !proto_map_end|].
  rewrite !proto_map_message /=. apply proto_message_ne=> // v p' /=.
  do 3 f_equiv. apply Next_contractive; dist_later_intro as n' Hn'; simpl; auto.
Qed.

Program Definition protoOF (V : Type) (Fn F : oFunctor)
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car Fn A B)}
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F A B)} : oFunctor := {|
  oFunctor_car A _ B _ := proto V (oFunctor_car Fn B A) (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    proto_map (oFunctor_map Fn (fg.2, fg.1)) (oFunctor_map F fg)
|}.
Next Obligation.
  intros V Fn F ?? A1 ? A2 ? B1 ? B2 ? n f g [??] p; simpl in *.
  apply proto_map_ne=> // y; by apply oFunctor_map_ne.
Qed.
Next Obligation.
  intros V Fn F ?? A ? B ? p; simpl in *. rewrite /= -{2}(proto_map_id p).
  apply proto_map_ext=> //= y; by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros V Fn F ?? A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' p; simpl in *.
  rewrite -proto_map_compose.
  apply proto_map_ext=> //= y; by rewrite ofe.oFunctor_map_compose.
Qed.

Global Instance protoOF_contractive (V : Type) (Fn F : oFunctor)
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car Fn A B)}
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F A B)} :
  oFunctorContractive Fn → oFunctorContractive F → 
  oFunctorContractive (protoOF V Fn F).
Proof.
  intros HFn HF A1 ? A2 ? B1 ? B2 ? n f g Hfg p; simpl in *.
  apply proto_map_ne=> y //=.
  + apply HFn. dist_later_intro as n' Hn'. f_equiv; apply Hfg.
  + apply HF. by dist_later_intro as n' Hn'.
Qed.