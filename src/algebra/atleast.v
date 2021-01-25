From stdpp Require Import nat_cancel.
From iris.proofmode Require Import base tactics modality_instances classes.
From iris.bi Require Export derived_laws derived_connectives.
From iris.algebra Require Import monoid cmra.
From iris.base_logic Require Import upred bi own.
From Perennial.algebra Require Export laterN.
Import interface.bi.
Import derived_laws.bi.
Import derived_laws_later.bi.

Set Default Proof Using "Type".

Definition bi_atleast {PROP : bi} (k : nat) (P : PROP) : PROP := (▷^k False ∨ P)%I.
Arguments bi_atleast {_} _ _%I : simpl never.
Notation "◇_ n P" := (bi_atleast n P) (at level 20, n at level 9, P at level 20,
   format "◇_ n  P").
Instance: Params (@bi_atleast) 2 := {}.
Typeclasses Opaque bi_atleast.

Class AbsolutelyTimeless {PROP : bi} (P : PROP) := abs_timeless : ∀ k, ▷^k P ⊢ ◇_k P.
Arguments AbsolutelyTimeless {_} _%I : simpl never.
Arguments abs_timeless {_} _%I {_}.
Hint Mode AbsolutelyTimeless + ! : typeclass_instances.
Instance: Params (@AbsolutelyTimeless) 1 := {}.

Section PROP_laws.
Context {PROP : bi}.
Context {H: BiLöb PROP}.
Implicit Types φ : Prop.
Implicit Types P Q R : PROP.
Implicit Types Ps : list PROP.
Implicit Types A : Type.

Local Hint Resolve or_elim or_intro_l' or_intro_r' True_intro False_elim : core.
Local Hint Resolve and_elim_l' and_elim_r' and_intro forall_intro : core.

(* Force implicit argument PROP *)
Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).

Global Instance atleast_ne k : NonExpansive (@bi_atleast PROP k).
Proof. solve_proper. Qed.
Global Instance atleast_proper k : Proper ((⊣⊢) ==> (⊣⊢)) (@bi_atleast PROP k).
Proof. solve_proper. Qed.
Global Instance atleast_mono' k : Proper ((⊢) ==> (⊢)) (@bi_atleast PROP k).
Proof. solve_proper. Qed.
Global Instance atleast_flip_mono' k :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_atleast PROP k).
Proof. solve_proper. Qed.

Section laws.
Context (k: nat).
Lemma atleast_intro P : P ⊢ ◇_k P.
Proof. rewrite /bi_atleast; auto. Qed.
Lemma atleast_mono P Q : (P ⊢ Q) → ◇_k P ⊢ ◇_k Q.
Proof. by intros ->. Qed.
Lemma atleast_le k1 k2 P : k1 ≤ k2 → ◇_k1 P ⊢ ◇_k2 P.
Proof.
  rewrite /bi_atleast. iIntros (?) "[Hf|HP]".
  - iLeft. iApply laterN_le; eauto.
  - iRight. eauto.
Qed.
Lemma atleast_idemp P : ◇_k ◇_k P ⊣⊢ ◇_k P.
Proof.
  apply (anti_symm _); rewrite /bi_atleast; auto.
Qed.

Lemma except_0_atleast P : ◇ P ⊣⊢ ◇_1 P.
Proof. rewrite /bi_atleast/bi_except_0//=. Qed.

Lemma atleast_True : ◇_k True ⊣⊢ True.
Proof using H. rewrite /bi_atleast. apply (anti_symm _); auto. Qed.
Lemma atleast_emp `{!BiAffine PROP} : ◇_k emp ⊣⊢ emp.
Proof using H. by rewrite -True_emp atleast_True. Qed.
Lemma atleast_or P Q : ◇_k (P ∨ Q) ⊣⊢ ◇_k P ∨ ◇_k Q.
Proof.
  rewrite /bi_atleast. apply (anti_symm _); auto.
Qed.
Lemma atleast_and P Q : ◇_k (P ∧ Q) ⊣⊢ ◇_k P ∧ ◇_k Q.
Proof. by rewrite /bi_atleast or_and_l. Qed.
Lemma atleast_sep P Q : ◇_k (P ∗ Q) ⊣⊢ ◇_k P ∗ ◇_k Q.
Proof.
  rewrite /bi_atleast. apply (anti_symm _).
  - apply or_elim; last by auto using sep_mono.
    by rewrite -!or_intro_l -persistently_pure -laterN_sep -persistently_sep_dup.
  - rewrite sep_or_r !sep_or_l {1}(later_intro P) {1}(later_intro Q).
    rewrite -!laterN_sep !left_absorb.
    iIntros "[[?|(?&?)]|[(?&?)|?]]"; eauto.
Qed.
Lemma atleast_exist_2 {A} (Φ : A → PROP) : (∃ a, ◇_k Φ a) ⊢ ◇_k ∃ a, Φ a.
Proof. apply exist_elim=> a. by rewrite (exist_intro a). Qed.
Lemma atleast_exist `{Inhabited A} (Φ : A → PROP) :
  ◇_k (∃ a, Φ a) ⊣⊢ (∃ a, ◇_k Φ a).
Proof.
  apply (anti_symm _); [|by apply atleast_exist_2]. apply or_elim.
  - rewrite -(exist_intro inhabitant). by apply or_intro_l.
  - apply exist_mono=> a. apply atleast_intro.
Qed.
Lemma atleast_laterN_le P j (Hle: j ≤ k) : ◇_k ▷^j P ⊢ ▷^k P.
Proof. by rewrite /bi_atleast (laterN_le j k) // -laterN_or False_or. Qed.
Lemma atleast_laterN P : ◇_k ▷^k P ⊢ ▷^k P.
Proof. by apply atleast_laterN_le. Qed.
Lemma atleast_later P (Hle: 1 <= k): ◇_k ▷ P ⊢ ▷^k P.
Proof. rewrite (atleast_laterN_le _ 1) //=. Qed.
(*
Lemma atleast_laterN n P (Hle: 1 ≤ k) : ◇_k ▷^n P ⊢ ▷^n ◇_k P.
Proof. destruct n as [|n]; rewrite //= ?atleast_later //=. -atleast_intro. Qed.
*)
Lemma atleast_into_later P : ◇_k P ⊢ ▷^k P.
Proof. by rewrite -atleast_laterN -laterN_intro. Qed.
Lemma atleast_persistently P : ◇_k <pers> P ⊣⊢ <pers> ◇_k P.
Proof.
  by rewrite /bi_atleast persistently_or -laterN_persistently persistently_pure.
Qed.
Lemma atleast_affinely_2 P : <affine> ◇_k P ⊢ ◇_k <affine> P.
Proof. rewrite /bi_affinely atleast_and. auto using atleast_intro. Qed.
Lemma atleast_intuitionistically_2 P : □ ◇_k P ⊢ ◇_k □ P.
Proof. by rewrite /bi_intuitionistically -atleast_persistently atleast_affinely_2. Qed.
Lemma atleast_intuitionistically_if_2 p P : □?p ◇_k P ⊢ ◇_k □?p P.
Proof. destruct p; simpl; auto using atleast_intuitionistically_2. Qed.
Lemma atleast_absorbingly P : ◇_k <absorb> P ⊣⊢ <absorb> ◇_k P.
Proof using H. by rewrite /bi_absorbingly atleast_sep atleast_True. Qed.

Lemma atleast_frame_l P Q : P ∗ ◇_k Q ⊢ ◇_k (P ∗ Q).
Proof. by rewrite {1}(atleast_intro P) atleast_sep. Qed.
Lemma atleast_frame_r P Q : ◇_k P ∗ Q ⊢ ◇_k (P ∗ Q).
Proof. by rewrite {1}(atleast_intro Q) atleast_sep. Qed.

Lemma later_affinely_1 `{!AbsolutelyTimeless (PROP:=PROP) emp} P : ▷^k <affine> P ⊢ ◇_k <affine> ▷^k P.
Proof.
  rewrite /bi_affinely laterN_and (abs_timeless emp%I) atleast_and.
  by apply and_mono, atleast_intro.
Qed.

Global Instance atleast_persistent P : Persistent P → Persistent (◇_k P).
Proof. rewrite /bi_atleast; apply _. Qed.
Global Instance atleast_absorbing P : Absorbing P → Absorbing (◇_k P).
Proof. rewrite /bi_atleast; apply _. Qed.
(* AbsolutelyTimeless instances *)
Global Instance AbsolutelyTimeless_proper : Proper ((≡) ==> iff) (@AbsolutelyTimeless PROP).
Proof.
  rewrite /AbsolutelyTimeless.
  intros ?? Heq. split; intros ? k0.
  * rewrite -Heq; eauto.
  * rewrite Heq; eauto.
Qed.

Lemma atleast_bupd `{!BiBUpd PROP} P : ◇_k (|==> P) ⊢ (|==> ◇_k P).
Proof.
  rewrite /bi_atleast. apply or_elim; eauto using bupd_mono, or_intro_r.
Qed.

End laws.

Global Instance and_abs_timeless P Q : AbsolutelyTimeless P → AbsolutelyTimeless Q → AbsolutelyTimeless (P ∧ Q).
Proof. intros ???; rewrite /AbsolutelyTimeless atleast_and laterN_and; auto. Qed.
Global Instance or_abs_timeless P Q : AbsolutelyTimeless P → AbsolutelyTimeless Q → AbsolutelyTimeless (P ∨ Q).
Proof. intros ???; rewrite /AbsolutelyTimeless atleast_or laterN_or; auto. Qed.

Global Instance sep_abs_timeless P Q: AbsolutelyTimeless P → AbsolutelyTimeless Q → AbsolutelyTimeless (P ∗ Q).
Proof.
  intros ???; rewrite /AbsolutelyTimeless atleast_sep laterN_sep; auto using sep_mono.
Qed.

Global Instance persistently_abs_timeless P : AbsolutelyTimeless P → AbsolutelyTimeless (<pers> P).
Proof.
  intros ??. rewrite /AbsolutelyTimeless /bi_atleast laterN_persistently.
  by rewrite (abs_timeless P) persistently_or {1}persistently_elim.
Qed.

Global Instance affinely_abs_timeless P :
  AbsolutelyTimeless (PROP:=PROP) emp → AbsolutelyTimeless P → AbsolutelyTimeless (<affine> P).
Proof. rewrite /bi_affinely; apply _. Qed.
(*
Global Instance absorbingly_abs_timeless P : AbsolutelyTimeless P → AbsolutelyTimeless (<absorb> P).
Proof. rewrite /bi_absorbingly; apply _. Qed.
*)

Global Instance intuitionistically_abs_timeless P :
  AbsolutelyTimeless (PROP:=PROP) emp → AbsolutelyTimeless P → AbsolutelyTimeless (□ P).
Proof. rewrite /bi_intuitionistically; apply _. Qed.

Global Instance from_option_abs_timeless {A} P (Ψ : A → PROP) (mx : option A) :
  (∀ x, AbsolutelyTimeless (Ψ x)) → AbsolutelyTimeless P → AbsolutelyTimeless (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.
End PROP_laws.

Section uPred_laws.
Context {M: ucmra}.
Implicit Types φ : Prop.
Implicit Types P Q R : (uPred M).
Implicit Types Ps : list (uPred M).
Implicit Types A : Type.



Local Hint Resolve or_elim or_intro_l' or_intro_r' True_intro False_elim : core.
Local Hint Resolve and_elim_l' and_elim_r' and_intro forall_intro : core.

(* TODO: Is there a syntactic proof of this for all BI?
   The generalization of the syntactic proof for except_0 did not seem to work out. *)
Lemma atleast_forall {A} k (Φ : A → uPred M) : ◇_k (∀ a, Φ a) ⊣⊢ ∀ a, ◇_k Φ a.
Proof.
  apply (anti_symm _).
  { apply forall_intro=> a. by rewrite (forall_elim a). }
  split => n x Hval Hall.
  destruct (decide (n < k)).
  - rewrite /bi_atleast/bi_or//=. uPred.unseal. left. apply laterN_small; eauto.
  - move: Hall. rewrite /bi_atleast/bi_or//=. uPred.unseal. right.
    intros a. specialize (Hall a) as [Hleft|Hright].
    * exfalso. eapply (laterN_big n k x); eauto.
      { lia. }
      { uPred.unseal; eauto. }
    * eauto.
Qed.

Global Instance pure_abs_timeless φ : AbsolutelyTimeless (PROP:=uPredI M) ⌜φ⌝.
Proof.
  intros k'. rewrite /bi_atleast pure_alt laterN_exist_false.
  apply or_mono; first auto.
  apply exist_elim. intros. eauto.
Qed.
Global Instance emp_abs_timeless `{BiAffine PROP} : AbsolutelyTimeless (PROP:=uPredI M) emp.
Proof. rewrite -True_emp. apply _. Qed.
Global Instance forall_abs_timeless {A} (Ψ : A → uPred M) :
  (∀ x, AbsolutelyTimeless (Ψ x)) → AbsolutelyTimeless (∀ x, Ψ x).
Proof.
  rewrite /AbsolutelyTimeless=> HQ k. rewrite atleast_forall laterN_forall.
  apply forall_mono; auto.
Qed.
Global Instance exist_abs_timeless {A} (Ψ : A → uPred M) :
  (∀ x, AbsolutelyTimeless (Ψ x)) → AbsolutelyTimeless (∃ x, Ψ x).
Proof.
  rewrite /AbsolutelyTimeless=> ??. rewrite laterN_exist_false. apply or_elim.
  - rewrite /bi_atleast; auto.
  - apply exist_elim=> x. rewrite -(exist_intro x); auto.
Qed.

Global Instance eq_abs_timeless {A : ofe} (a b : A) :
  Discrete a → AbsolutelyTimeless (PROP:=uPredI M) (a ≡ b).
Proof. intros. rewrite /Discrete !discrete_eq => k. apply (abs_timeless _). Qed.

(* These next two instances hold for Timeless, but they appear to not be true for AbsolutelyTimeless.

   However, a quick test suggests that the corresponding Timeless versions are un-used in Perennial,
   so losing them for AbsolutelyTimeless is not a problem. *)

(*
Global Instance impl_abs_timeless `{!BiLöb PROP} P Q : AbsolutelyTimeless Q → AbsolutelyTimeless (P → Q).
Proof.
  rewrite /AbsolutelyTimeless=> HQ k.
  split => n x Hval HPQ.
  destruct (decide (n < k)).
  - rewrite /bi_atleast//=. uPred.unseal. left. apply laterN_small; eauto.
  - move: HQ HPQ. rewrite /bi_atleast//=. uPred.unseal. right.
    intros n' x' Hincl Hle Hval' HP.
    assert (HPQ_later: (uPred_impl_def P Q) (n - k) x).
    assert (HP_later: P (n' - k) x).
Abort.
*)

(*
Global Instance wand_abs_timeless `{!BiLöb PROP} P Q : AbsolutelyTimeless Q → AbsolutelyTimeless (P -∗ Q).
Proof.
Abort.
*)

Import base_logic.bi.uPred.
Global Instance valid_abs_timeless {A : cmra} `{!CmraDiscrete A} (a : A) :
  AbsolutelyTimeless (✓ a : uPred M)%I.
Proof. rewrite /AbsolutelyTimeless => k. rewrite !discrete_valid. apply (abs_timeless _). Qed.


Global Instance ownM_abs_timeless (a : M) : Discrete a → AbsolutelyTimeless (uPred_ownM a).
Proof.
  intros ? k. rewrite laterN_ownM.
  apply exist_elim=> b.
  rewrite (abs_timeless (a≡b)) (atleast_intro k (uPred_ownM b)) -atleast_and.
  apply atleast_mono. rewrite internal_eq_sym.
  apply (internal_eq_rewrite' b a (uPred_ownM) _);
    auto using and_elim_l, and_elim_r.
Qed.
End uPred_laws.

Class IntoAtLeast {PROP : bi} k (P Q : PROP) := into_atleast : P ⊢ ◇_k Q.
Arguments IntoAtLeast {_} _ _%I _%I : simpl never.
Arguments into_atleast {_} _ _%I _%I {_}.
Hint Mode IntoAtLeast + - ! - : typeclass_instances.
Hint Mode IntoAtLeast + - - ! : typeclass_instances.

Class IsAtLeast {PROP : bi} k (Q : PROP) := is_atleast : ◇_k Q ⊢ Q.
Arguments IsAtLeast {_} _ _%I : simpl never.
Arguments is_atleast {_} _ _%I {_}.
Hint Mode IsAtLeast + + ! : typeclass_instances.

Class MakeAtLeast {PROP : bi} k (P Q : PROP) :=
  make_atleast : ◇_k P ⊣⊢ Q.
Arguments MakeAtLeast {_} _ _%I _%I.
Hint Mode MakeAtLeast + - - - : typeclass_instances.
Class KnownMakeAtLeast {PROP : bi} k (P Q : PROP) :=
  known_make_except_0 :> MakeAtLeast k P Q.
Arguments KnownMakeAtLeast {_} _ _%I _%I.
Hint Mode KnownMakeAtLeast + + ! - : typeclass_instances.

Section class_instances_atleast.
Context {M: ucmra}.
Context (k: nat).
Implicit Types P Q R : uPred M.

Global Instance from_assumption_atleast p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (◇_k Q)%I.
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply atleast_intro. Qed.

Global Instance from_pure_atleast a P φ : FromPure a P φ → FromPure a (◇_k P) φ.
Proof. rewrite /FromPure=> ->. apply atleast_intro. Qed.

Global Instance from_and_atleast P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (◇_k P) (◇_k Q1) (◇_k Q2).
Proof. rewrite /FromAnd=><-. by rewrite atleast_and. Qed.

Global Instance from_sep_atleast P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (◇_k P) (◇_k Q1) (◇_k Q2).
Proof. rewrite /FromSep=><-. by rewrite atleast_sep. Qed.

Global Instance into_and_atleast p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (◇_k P) (◇_k Q1) (◇_k Q2).
Proof.
  rewrite /IntoAnd=> HP. apply intuitionistically_if_intro'.
  by rewrite atleast_intuitionistically_if_2 HP
             intuitionistically_if_elim atleast_and.
Qed.

Global Instance into_sep_atleast P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (◇_k P) (◇_k Q1) (◇_k Q2).
Proof. rewrite /IntoSep=> ->. by rewrite atleast_sep. Qed.

Global Instance from_or_atleast P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (◇_k P) (◇_k Q1) (◇_k Q2).
Proof. rewrite /FromOr=><-. by rewrite atleast_or. Qed.

Global Instance into_or_atleast P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (◇_k P) (◇_k Q1) (◇_k Q2).
Proof. rewrite /IntoOr=>->. by rewrite atleast_or. Qed.

Global Instance from_exist_atleast {A} P (Φ : A → uPred M) :
  FromExist P Φ → FromExist (◇_k P) (λ a, ◇_k (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite atleast_exist_2. Qed.

Global Instance into_exist_atleast {A} P (Φ : A → uPred M) i :
  IntoExist P Φ i → Inhabited A → IntoExist (◇_k P) (λ a, ◇_k (Φ a))%I i.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP atleast_exist. Qed.

Global Instance into_forall_atleast {A} P (Φ : A → uPred M) :
  IntoForall P Φ → IntoForall (◇_k P) (λ a, ◇_k (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP atleast_forall. Qed.

Global Instance from_forall_atleast {A} P (Φ : A → uPred M) i :
  FromForall P Φ i → FromForall (◇_k P)%I (λ a, ◇_k (Φ a))%I i.
Proof. rewrite /FromForall=> <-. by rewrite atleast_forall. Qed.

Global Instance from_modal_atleast P : FromModal modality_id (◇_k P) (◇_k P) P.
Proof. by rewrite /FromModal /= -atleast_intro. Qed.

(** IsAtLeast *)
Global Instance is_atleast_atleast P : IsAtLeast k (◇_k P).
Proof. by rewrite /IsAtLeast atleast_idemp. Qed.
Global Instance is_atleast_later P : IsAtLeast k (▷^k P).
Proof. by rewrite /IsAtLeast atleast_laterN. Qed.

(** IntoAtLeast *)
Global Instance into_atleast_atleast P : IntoAtLeast k (◇_k P) P.
Proof. by rewrite /IntoAtLeast. Qed.
Global Instance into_atleast_later P : AbsolutelyTimeless P → IntoAtLeast k (▷^k P) P.
Proof. by rewrite /IntoAtLeast. Qed.

(* Special instances of above for k=1 and k=2. This could be done more generically, but it seems like
   we will only use k=1 and k=2 in practice anyway, so for now we just add directly the instances needed. *)
Global Instance into_atleast_later1 P : AbsolutelyTimeless P → IntoAtLeast 1 (▷ P) P.
Proof. rewrite /IntoAtLeast. by replace (▷ P)%I with (▷^1 P)%I by auto. Qed.
Global Instance into_atleast_later2 P : AbsolutelyTimeless P → IntoAtLeast 2 (▷▷ P) P.
Proof. rewrite /IntoAtLeast. by replace (▷▷ P)%I with (▷^2 P)%I by auto. Qed.
Global Instance into_atleast_later2' P : AbsolutelyTimeless P → IntoAtLeast 2 (▷ P) P.
Proof. rewrite /IntoAtLeast => ?. transitivity (▷▷ P)%I; first eauto. by apply into_atleast_later2. Qed.

(* XXX should this be added?
Global Instance into_atleast_later P : Timeless P → IntoAtLeast 1 (▷ P) P.
Proof. by rewrite /IntoAtLeast. Qed.
Global Instance into_atleast_later_if p P : Timeless P → IntoAtLeast (▷?p P) P.
Proof. rewrite /IntoAtLeast. destruct p; auto using atleast_intro. Qed.
*)

Global Instance into_atleast_affinely P Q :
  IntoAtLeast k P Q → IntoAtLeast k (<affine> P) (<affine> Q).
Proof. rewrite /IntoAtLeast=> ->. by rewrite atleast_affinely_2. Qed.
Global Instance into_atleast_intuitionistically P Q :
  IntoAtLeast k P Q → IntoAtLeast k (□ P) (□ Q).
Proof. rewrite /IntoAtLeast=> ->. by rewrite atleast_intuitionistically_2. Qed.
Global Instance into_atleast_absorbingly P Q :
  IntoAtLeast k P Q → IntoAtLeast k (<absorb> P) (<absorb> Q).
Proof. rewrite /IntoAtLeast=> ->. by rewrite atleast_absorbingly. Qed.
Global Instance into_atleast_persistently P Q :
  IntoAtLeast k P Q → IntoAtLeast k (<pers> P) (<pers> Q).
Proof. rewrite /IntoAtLeast=> ->. by rewrite atleast_persistently. Qed.

Global Instance elim_modal_abstimeless p P Q P' :
  IntoAtLeast k P P' → IsAtLeast k Q → ElimModal True p p P P' Q Q.
Proof.
  intros. rewrite /ElimModal (atleast_intro k (_ -∗ _)%I) (into_atleast k P).
  by rewrite atleast_intuitionistically_if_2 -atleast_sep wand_elim_r.
Qed.

Global Instance add_modal_atleast P Q : AddModal (◇_k P) P (◇_k Q) | 1.
Proof.
  intros. rewrite /AddModal (atleast_intro k (_ -∗ _)%I).
  by rewrite -atleast_sep wand_elim_r atleast_idemp.
Qed.
Global Instance add_modal_atleast_later P Q : AddModal (◇_k P) P (▷^k Q) | 1.
Proof.
  intros. rewrite /AddModal (atleast_intro k (_ -∗ _)%I).
  by rewrite -atleast_sep wand_elim_r atleast_laterN.
Qed.

Global Instance make_atleast_True : @KnownMakeAtLeast (uPredI M) k True True.
Proof. by rewrite /KnownMakeAtLeast /MakeAtLeast atleast_True. Qed.
Global Instance make_atleast_default P : MakeAtLeast k P (◇_k P) | 100.
Proof. by rewrite /MakeAtLeast. Qed.

Global Instance frame_atleast p R P Q Q' :
  Frame p R P Q → MakeAtLeast k Q Q' → Frame p R (◇_k P) Q'.
Proof.
  rewrite /Frame /MakeAtLeast=><- <-.
  by rewrite atleast_sep -(atleast_intro k (□?p R)%I).
Qed.

Global Instance is_atleast_bupd P : IsAtLeast k P → IsAtLeast k (|==> P).
Proof.
  rewrite /IsAtLeast=> HP.
  by rewrite -{2}HP -(atleast_idemp k P) -atleast_bupd -(atleast_intro k P).
Qed.

End class_instances_atleast.

Section iprop_instances.

  Global Instance own_abs_timeless {A: cmra} `{inG Σ A} γ (a: A):
    Discrete a →
    AbsolutelyTimeless (own γ a).
  Proof.
    intros ?. rewrite own.own_eq /own.own_def.
    apply ownM_abs_timeless, iRes_singleton_discrete. done.
  Qed.

End iprop_instances.
