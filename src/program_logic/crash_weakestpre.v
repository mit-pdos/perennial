From iris.algebra Require Import auth agree excl csum.
From Perennial.base_logic Require Import ae_invariants.
From iris.bi Require Export weakestpre.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Export invariants fupd_level fancy_updates2.
From Perennial.program_logic Require Import step_fupd_extra ae_invariants_mutable.
From Perennial.algebra Require Export own_discrete.
From Perennial.base_logic.lib Require Export ncfupd.
From Perennial.program_logic Require Export language cfupd.
From Perennial.program_logic Require ectx_language.
From iris.prelude Require Import options.
Import uPred.

(** [irisGS] captures the parameters that remain the same throughout the
entire execution of the crashing or distributed system. It is a single fixed
global parameter, instantiated once all the way at the top in adequacy. *)
Class irisGS (Λ : language) (Σ : gFunctors) := IrisGS {
  #[global] iris_invGS :: invGS Σ;

  (** The global state interpretation is a whole-system invariant that should
  hold in between each step of reduction. Here [global_state Λ] is the global
  state, the [nat] is the number of steps already performed by the system, and
  [list Λobservation] are the remaining observations.
  The fracR and the coPset are relevant for crash borrows; also see later_res
  and private_invariants *)
  global_state_interp : global_state Λ → nat → fracR → coPset → list (observation Λ) → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : val Λ → iProp Σ;

  (** Number of additional logical steps (i.e., later modality in the
  definition of WP) per physical step, depending on the physical steps
  counter. In addition to these steps, the definition of WP adds one
  extra later per physical step to make sure that there is at least
  one later for each physical step. *)
  num_laters_per_step : nat → nat;

  (** Further inflate how many laters we generate per step. *)
  step_count_next : nat → nat;

  (** When performing pure steps, the state interpretation needs to be
  adapted for the change in the [ns] parameter.

  Note that we use an empty-mask fancy update here. We could also use
  a basic update or a bare magic wand, the expressiveness of the
  framework would be the same. If we removed the modality here, then
  the client would have to include the modality it needs as part of
  the definition of [global_state_interp]. Since adding the modality as part
  of the definition [global_state_interp_mono] does not significantly
  complicate the formalization in Iris, we prefer simplifying the
  client. *)
  global_state_interp_mono g ns q D κs:
    global_state_interp g ns q D κs ={∅}=∗ global_state_interp g (S ns) q D κs;

  step_count_next_incr n : n ≤ step_count_next n
}.
Global Opaque iris_invGS.

Global Arguments global_state_interp : simpl never.
Global Arguments step_count_next : simpl never.


(* [generationGS] captures the parameters that can change on each crash,
   and between machines in the distributed setting. *)
Class generationGS (Λ : language) (Σ : gFunctors) := GenerationGS {
  #[global] iris_crashGS :: crashGS Σ;

  (** The state interpretation is a per-machine invariant that should hold in
  between each step of reduction. Here [state Λ] is the per-machine state, and
  the [nat] is the number of forked-off threads (not the total number of threads,
  which is one higher because there is always a main thread). *)
  state_interp : state Λ → nat → iProp Σ;
}.

Global Arguments state_interp : simpl never.

Global Arguments iris_crashGS {Λ Σ G} : rename.
Global Arguments state_interp {Λ Σ G} : rename.

(* Define a weakestpre with an explicit crash invariant (i.e. there is a postcondition and a crash condition *)
Definition wpc_pre `{!irisGS Λ Σ, !generationGS Λ Σ} (s : stuckness) (mj: fracR)
    (wpc : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ := λ E1 e1 Φ Φc,
  ((match to_val e1 with
    | Some v =>
      ∀ q g1 ns D κs,
        global_state_interp g1 ns mj D κs -∗ NC q -∗ ||={E1|⊤∖D, E1|⊤∖D}=> Φ v ∗
          global_state_interp g1 ns mj D κs ∗
          NC q
   | None => ∀ q σ1 g1 ns D κ κs nt,
       state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ NC q -∗
       £ (S $ num_laters_per_step ns) -∗ ||={E1|⊤∖D,∅|∅}=>
         ||▷=>^(S $ num_laters_per_step ns)
        (⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
        ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ ||={∅|∅,E1|⊤∖D}=>
          (state_interp σ2 (length efs + nt) ∗
          global_state_interp g2 (step_count_next ns) mj D κs ∗
          wpc (match to_val e2 with | Some _ => E1 | _ => ⊤ end) e2 Φ Φc ∗
          ([∗ list] i ↦ ef ∈ efs, wpc ⊤ ef fork_post True) ∗
          NC q))
   end ∧
  (* Todo introduce notation for this split up cfupd *)
    ((∀ g1 ns D κs, global_state_interp g1 ns mj D κs -∗ C -∗
     £ (num_laters_per_step ns) -∗
     ||={E1|⊤∖D,∅|∅}=> ||▷=>^(num_laters_per_step ns) ||={∅|∅,E1|⊤∖D}=> global_state_interp g1 ns mj D κs ∗ Φc))))%I.

Local Instance wpc_pre_contractive `{!irisGS Λ Σ, !generationGS Λ Σ} s mj : Contractive (wpc_pre s mj).
Proof.
  rewrite /wpc_pre=> n wp wp' Hwp E1 e1 Φ Φc.
  do 23 (f_contractive || f_equiv).
  induction num_laters_per_step as [|k' IH]; simpl.
  - repeat (f_contractive || f_equiv); apply Hwp.
  - simpl in IH. rewrite -IH. eauto.
Qed.

Definition wpc0 `{!irisGS Λ Σ, !generationGS Λ Σ} (s : stuckness) mj :
  coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ → iProp Σ := fixpoint (wpc_pre s mj).

Definition wpc_def `{!irisGS Λ Σ, !generationGS Λ Σ} (s : stuckness) :
  coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ → iProp Σ :=
  λ E1 e1 Φ Φc, (∀ mj, wpc0 s mj E1 e1 Φ Φc)%I.
Definition wpc_aux `{!irisGS Λ Σ, !generationGS Λ Σ} : seal (@wpc_def Λ Σ _ _). by eexists. Qed.

Definition wpc `{!irisGS Λ Σ, !generationGS Λ Σ} := wpc_aux.(unseal).
Arguments wpc {Λ Σ _ _} _ E _%E _%I _%I.
#[global]
Instance: Params (@wpc) 7 := {}.
Definition wpc_eq `{!irisGS Λ Σ, !generationGS Λ Σ} : wpc = @wpc_def Λ Σ _ _ := wpc_aux.(seal_eq).

(** Notations for partial crash weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WPC' e @ s ; E1 {{ Φ } } {{ Φc } }" := (wpc s E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e @ E1 {{ Φ } } {{ Φc } }" := (wpc NotStuck E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e {{ Φ } } {{ Φc } }" := (wpc NotStuck ⊤ e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.

(** Notations with binder.  *)
Notation "'WPC' e @ s ; E1 {{ v , Q } } {{ R } }" := (wpc s E1 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[hv' 'WPC'  e  '/' @  '[' s ;  E1  ']' '/' {{  '[' v ,  '/' Q  ']' } }  '/' {{  '[' R  ']' } } ']'") : bi_scope.
Notation "'WPC' e @ E1 {{ v , Q } } {{ R } }" := (wpc NotStuck E1 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[hv' 'WPC'  e  '/' @  '[' E1  ']' '/' {{  '[' v ,  '/' Q  ']' } }  '/' {{  '[' R  ']' } } ']'") : bi_scope.

(* Texan triples *)
Notation "'{{{' P } } } e @ s ; E1 {{{ x .. y , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc,
      P -∗ (Qc -∗ Φc) ∧ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPC e @ s; E1 {{ Φ }} {{ Φc }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  E1  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } }  '/' {{{  '[' Qc  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E1 {{{ x .. y , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc,
      P -∗ (Qc -∗ Φc) ∧ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPC e @ E1 {{ Φ }} {{ Φc }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' E1  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } }  '/' {{{  '[' Qc  ']' } } } ']'") : bi_scope.

(*
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  ? {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' ? {{{  x  ..  y ,   RET  pat ;  Q  } } } ']'") : bi_scope.
*)

Notation "'{{{' P } } } e @ s ; E1 {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (Q -∗ Φ pat%V) -∗ WPC e @ s; E1 {{ Φ }} {{ Φc }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  E1  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } }  '/' {{{  '[' Qc  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E1 {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (Q -∗ Φ pat%V) -∗ WPC e @ E1 {{ Φ }} {{ Φc }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' E1  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } }  '/' {{{  '[' Qc  ']' } } } ']'") : bi_scope.
(*
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
*)

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e @ s ; E1 {{{ x .. y , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPC e @ s; E1 {{ Φ }} {{ Φc }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E1 {{{ x .. y , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPC e @ E1 {{ Φ }} {{ Φc }}) : stdpp_scope.
(*
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }}) : stdpp_scope.
*)
Notation "'{{{' P } } } e @ s ; E1 {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (Q -∗ Φ pat%V) -∗ WPC e @ s; E1 {{ Φ }} {{ Φc }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E1 {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (Q -∗ Φ pat%V) -∗ WPC e @ E1 {{ Φ }} {{ Φc }}) : stdpp_scope.
(*
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }}) : stdpp_scope.
*)

(** Defining WP in terms of WPC (needs to be here since WP is used in this file)
*)
Definition wp_def `{!irisGS Λ Σ, !generationGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) stuckness :=
  λ s E e Φ, (WPC e @ s ; E {{ Φ }} {{ True }})%I.
Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _}.
(* We cannot make this an instance since [simple apply] unification is too weak. *)
Global Hint Extern 0 (Wp _ _ _ _) => apply wp' : typeclass_instances.
Lemma wp_eq `{!irisGS Λ Σ, !generationGS Λ Σ} : wp = @wp_def Λ Σ _ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

(** We do not really need crashGS, but it is the laziest way
    to get an inG fracR. *)
(*Lemma fupd_level_later_to_disc `{!invGS Σ, !crashGS Σ} k E P:
  ▷ P -∗ |k={E}=> <disc> ▷ P.
Proof.
  iMod (own_alloc (Cinl 1%Qp)) as (γ) "H".
  { rewrite //=. }
  iIntros "HP".
  iPoseProof (ae_inv_alloc' O None E (P ∨ own γ (Cinl 1%Qp)) with "[HP]") as "Hinv".
  { by iLeft. }
  rewrite uPred_fupd_level_eq.
  iMod (fupd_split_level_le with "Hinv") as "#Hinv"; first naive_solver lia.
  iModIntro. rewrite own_discrete_fupd_eq /own_discrete_fupd_def. iModIntro.
  rewrite uPred_fupd_level_eq.
  iMod (ae_inv_acc_bupd _ _ _ _ (▷ P) with "Hinv [H]").
  { iDestruct 1 as "[HP|>Hfalse]"; do 2 iModIntro; last first.
    { by iDestruct (own_valid_2 with "H Hfalse") as %?. }
    iFrame "H". eauto.
  }
  iModIntro; eauto.
Qed.
Lemma fupd_later_to_disc `{!invGS Σ, !crashGS Σ} E P:
  ▷ P -∗ |={E}=> <disc> ▷ P.
Proof.
  iIntros "H". iApply (fupd_level_fupd _ _ _ O). by iApply fupd_level_later_to_disc.
Qed.*)

Section wpc.
Context `{!irisGS Λ Σ, !generationGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpc0_unfold s mj E1 e Φ Φc :
  wpc0 s mj E1 e Φ Φc ⊣⊢ wpc_pre s mj (wpc0 s mj) E1 e Φ Φc.
Proof. apply (fixpoint_unfold (wpc_pre s mj)). Qed.

Lemma wpc_unfold s E1 e Φ Φc :
  WPC e @ s; E1 {{ Φ }} {{ Φc }} ⊣⊢ ∀ mj, wpc_pre s mj (wpc0 s mj) E1 e Φ Φc.
Proof. rewrite wpc_eq. rewrite /wpc_def. f_equiv => mj. apply wpc0_unfold. Qed.

Global Instance wpc0_ne s mj E1 e n :
  Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) (wpc0 s mj E1 e).
Proof.
  revert E1 e. induction (lt_wf n) as [n _ IH]=> E1 e Φ Ψ HΦ Φc Ψc HΦc.
  rewrite !wpc0_unfold /wpc_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  rewrite /cfupd.
  do 14 (apply step_fupd2N_ne || f_contractive || f_equiv); auto; last first.
  { repeat f_equiv. eauto. }
  2: { repeat f_equiv. }
  do 9 (apply step_fupd2N_ne || f_contractive || f_equiv).
  induction num_laters_per_step as [|k' IHk]; simpl; last first.
  { simpl in IHk. by rewrite IHk. }
  f_equiv. f_contractive.
  do 12 f_equiv.
  cbn [sidx_lt natSI] in *. (* TODO: can zify do this automatically? *)
  rewrite IH; [done|try lia| |].
  - intros v. eapply dist_le; eauto. lia.
  - eapply dist_le; eauto. lia.
Qed.

Global Instance wpc_ne s E1 e n :
  Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) (wpc s E1 e).
Proof. intros ??????. rewrite !wpc_unfold. f_equiv => mj. rewrite -?wpc0_unfold. by apply wpc0_ne. Qed.

Global Instance wpc_proper s E1 e :
  Proper (pointwise_relation _ (≡) ==> (≡) ==> (≡)) (wpc s E1 e).
Proof.
  intros Φ Φ' ? Φc Φc' ?.
  apply equiv_dist=>n. apply wpc_ne; auto.
  by intros v; apply equiv_dist.
Qed.

Lemma wpc0_wpc s E1 e Φ Φc mj:
  WPC e @ s; E1 {{ Φ }} {{ Φc }} -∗
  wpc0 s mj E1 e Φ Φc.
Proof. rewrite wpc0_unfold wpc_unfold. iIntros "H". iApply "H". Qed.

Lemma wpc0_strong_mono_fupd2 s1 s2 mj E1 E2 e Φ Ψ Φc Ψc :
  s1 ⊑ s2 → E1 ⊆ E2 →
  wpc0 s1 mj E1 e Φ Φc -∗
  (∀ v, Φ v -∗ ||={E2|∅,E2|∅}=> Ψ v) ∧ (Φc -∗ ||={E2|∅, E2|∅}=> Ψc) -∗
  wpc0 s2 mj E2 e Ψ Ψc.
Proof.
  iIntros (? HE) "H HΦ".
  iLöb as "IH" forall (e E1 E2 HE Φ Ψ Φc Ψc).
  rewrite !wpc0_unfold /wpc_pre.
  iSplit.
  - destruct (to_val e) as [v|] eqn:?.
    {
      iDestruct "HΦ" as "(HΦ&_)". iDestruct "H" as "(H&_)".
      iMod (fupd_mask_subseteq E1) as "Hclo"; first by auto.
      iIntros.
      iMod ("H" with "[$] [$]") as "(?&?&?)". iMod "Hclo" as "_".
      iSpecialize ("HΦ" with "[$]").
      iMod (fupd2_mask_subseteq E2 ∅) as "Hclo"; first done; try set_solver.
      iMod "HΦ". iMod "Hclo". iFrame. eauto.
    }
    iIntros (q σ1 g1 ns D κ κs n) "Hσ Hg HNC Hlc".
    iMod (fupd2_mask_subseteq E1 (⊤ ∖ _)) as "Hclo"; first done.
    { reflexivity. }
    iDestruct "H" as "(H&_)".
    iMod ("H" with "[$] [$] [$] [$]") as "H".
    iModIntro. simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    iApply (step_fupd2N_wand with "H"). iIntros "[% H]".
    iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 g2 efs Hstep).
    iSpecialize ("H" with "[//]"). simpl. iMod "H".
    iDestruct "H" as "(Hσ & Hg & H & Hefs & HNC)". iMod "Hclo" as "_". iModIntro.
    iFrame.
    iSplitR "Hefs".
    ** iApply ("IH" with "[] H [HΦ]"); first (destruct (to_val e2); auto).
       iSplit.
       *** iDestruct "HΦ" as "(HΦ&_)". iIntros (v) "H".
           iMod (fupd2_mask_subseteq E2 ∅) as "Hclo"; first (destruct (to_val e2); set_solver).
           { done. }
           iMod ("HΦ" with "[$]"). iMod "Hclo". eauto.
       *** iDestruct "HΦ" as "(_&HΦ)". iIntros "H".
           iMod (fupd2_mask_subseteq E2 ∅) as "Hclo"; first (destruct (to_val e2); set_solver).
           { done. }
           iMod ("HΦ" with "[$]"). iMod "Hclo". eauto.
    ** iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
       iIntros "H". eauto. iApply ("IH" with "[] H"); auto.
  - iDestruct "H" as "(_&H)". iDestruct "HΦ" as "(_&HΦ)".
    iIntros (????) "Hg HC Hlc".
    iSpecialize ("H" with "[$] [$] [$]").
    iMod (fupd2_mask_subseteq E1 (⊤ ∖ _)) as "Hclo"; first done.
    { reflexivity. }
    iApply (step_fupd2N_wand with "H").
    iIntros "H". iMod "H" as "($&H)". iMod "Hclo" as "_".
    iMod (fupd2_mask_subseteq E2 ∅) as "Hclo"; try set_solver+.
    iMod ("HΦ" with "H"). iMod "Hclo". eauto.
Qed.

Lemma wpc0_strong_mono s1 s2 mj E1 E2 e Φ Ψ Φc Ψc :
  s1 ⊑ s2 → E1 ⊆ E2 →
  wpc0 s1 mj E1 e Φ Φc -∗
  (∀ v, Φ v -∗ |NC={E2}=> Ψ v) ∧ (Φc -∗ |C={E2}=> Ψc) -∗
  wpc0 s2 mj E2 e Ψ Ψc.
Proof.
  iIntros (? HE) "H HΦ".
  iLöb as "IH" forall (e E1 E2 HE Φ Ψ Φc Ψc).
  rewrite !wpc0_unfold /wpc_pre.
  iSplit.
  - destruct (to_val e) as [v|] eqn:?.
    {
      iDestruct "HΦ" as "(HΦ&_)". iDestruct "H" as "(H&_)".
      iMod (fupd_mask_subseteq E1) as "Hclo"; first by auto.
      iIntros.
      iMod ("H" with "[$] [$]") as "(?&?&?)". iMod "Hclo" as "_".
      rewrite ncfupd_eq /ncfupd_def.
      iMod ("HΦ" with "[$] [$]"). iFrame. eauto.
    }
    iIntros (q σ1 g1 ns D κ κs n) "Hσ Hg HNC Hlc".
    iMod (fupd2_mask_subseteq E1 (⊤ ∖ _)) as "Hclo"; first done.
    { reflexivity. }
    iDestruct "H" as "(H&_)".
    iMod ("H" with "[$] [$] [$] [$]") as "H".
    iModIntro. simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    iApply (step_fupd2N_wand with "H"). iIntros "[% H]".
    iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 g2 efs Hstep).
    iSpecialize ("H" with "[//]"). simpl. iMod "H".
    iDestruct "H" as "(Hσ & Hg & H & Hefs & HNC)". iMod "Hclo" as "_". iModIntro.
    iFrame.
    iSplitR "Hefs".
    ** iApply ("IH" with "[] H [HΦ]"); first (destruct (to_val e2); auto).
       iSplit.
       *** iDestruct "HΦ" as "(HΦ&_)". iIntros (v) "H".
           iMod (ncfupd_mask_subseteq E2) as "Hclo"; first (destruct (to_val e2); set_solver).
           iMod ("HΦ" with "[$]"). iMod "Hclo". eauto.
       *** iDestruct "HΦ" as "(_&HΦ)". iIntros "H".
           iApply (cfupd_weaken_mask); last (by iApply "HΦ"); auto.
           destruct (to_val e2); set_solver.
    ** iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
       iIntros "H". eauto. iApply ("IH" with "[] H"); auto.
  - iDestruct "H" as "(_&H)". iDestruct "HΦ" as "(_&HΦ)".
    iIntros (????) "Hg #HC Hlc".
    iSpecialize ("H" with "[$] [$] [$]").
    iMod (fupd2_mask_subseteq E1 (⊤ ∖ _)) as "Hclo"; first done.
    { reflexivity. }
    iApply (step_fupd2N_wand with "H").
    iIntros "H". iMod "H" as "($&H)". iMod "Hclo" as "_".
    iSpecialize ("HΦ" with "H [$]"). eauto.
    iApply (fupd_fupd2). eauto.
Qed.

Lemma wpc0_step_strong_mono s1 s2 mj E1 E2 e Φ Ψ Φc Ψc :
  to_val e = None →
  s1 ⊑ s2 → E1 ⊆ E2 →
  wpc0 s1 mj E1 e Φ Φc -∗
  ▷ (∀ v, Φ v -∗ |NC={E2}=> Ψ v) ∧ (Φc -∗ |C={E2}=> Ψc) -∗
  wpc0 s2 mj E2 e Ψ Ψc.
Proof.
  iIntros (Hval ? HE) "H HΦ".
  iLöb as "IH" forall (e Hval E1 E2 HE Φ Ψ Φc Ψc).
  rewrite !wpc0_unfold /wpc_pre.
  iSplit.
  - rewrite Hval.
    iIntros (q σ1 g1 ns D κ κs n) "Hσ Hg HNC Hlc".
    iMod (fupd2_mask_subseteq E1 (⊤ ∖ _)) as "Hclo"; first done.
    { reflexivity. }
    iDestruct "H" as "(H&_)".
    iMod ("H" with "[$] [$] [$] [$]") as "H".
    iModIntro. simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    iApply (step_fupd2N_wand with "H").
    iIntros "[% H]".
    iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 g2 efs Hstep).
    iMod ("H" with "[//]") as "(Hσ & Hg & H & Hefs & HNC)". iMod "Hclo" as "_". iModIntro.
    iFrame.
    iSplitR "Hefs".
    ** iApply (wpc0_strong_mono with "H [HΦ]"); eauto;  first (destruct (to_val e2); auto).
       iSplit.
       *** iDestruct "HΦ" as "(HΦ&_)". iIntros (v) "H".
           iMod (ncfupd_mask_subseteq E2) as "Hclo"; first (destruct (to_val e2); set_solver).
           iMod ("HΦ" with "[$]"). iMod "Hclo". eauto.
       *** iDestruct "HΦ" as "(_&HΦ)". iIntros "H".
           iApply (cfupd_weaken_mask); last (by iApply "HΦ"); auto.
           destruct (to_val e2); set_solver.
    ** iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
       iIntros "H".  iApply (wpc0_strong_mono with "H []"); eauto.
  - iDestruct "H" as "(_&H)". iDestruct "HΦ" as "(_&HΦ)".
    iIntros.
    iSpecialize ("H" with "[$] [$] [$]").
    iMod (fupd2_mask_subseteq E1 (⊤ ∖ _)) as "Hclo"; first done.
    { reflexivity. }
    iApply (step_fupd2N_wand with "H").
    iIntros "H". iMod "H" as "($&H)". iMod "Hclo" as "_".
    iSpecialize ("HΦ" with "H [$]"). eauto.
    iApply fupd_fupd2. eauto.
Qed.

Lemma wp_wpc s E1 e Φ:
  WP e @ s; E1 {{ Φ }} ⊢ WPC e @ s; E1 {{ Φ }} {{ True }}.
Proof. rewrite wp_eq /wp_def wpc_eq. iIntros "H" (?). done. Qed.

Lemma wpc_wp s E1 e Φ Φc:
  WPC e @ s; E1 {{ Φ }} {{ Φc }} ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite wp_eq /wp_def wpc_eq. iIntros "H" (?).
  iApply (wpc0_strong_mono with "H"); auto.
Qed.

Lemma wpc_strong_mono_fupd2 s1 s2 E1 E2 e Φ Ψ Φc Ψc :
  s1 ⊑ s2 → E1 ⊆ E2 →
  wpc s1 E1 e Φ Φc -∗
  (∀ v, Φ v -∗ ||={E2|∅,E2|∅}=> Ψ v) ∧ (Φc -∗ ||={E2|∅, E2|∅}=> Ψc) -∗
  wpc s2 E2 e Ψ Ψc.
Proof.
  iIntros (? HE) "H HΦ". rewrite wpc_eq. iIntros (mj). iSpecialize ("H" $! mj).
  iApply (wpc0_strong_mono_fupd2 _ _ mj with "[$] [$]"); eauto.
Qed.

Lemma wpc_strong_mono s1 s2 E1 E2 e Φ Ψ Φc Ψc :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WPC e @ s1; E1 {{ Φ }} {{ Φc }} -∗
  (∀ v, Φ v -∗ |NC={E2}=> Ψ v) ∧ (Φc -∗ |C={E2}=> Ψc) -∗
  WPC e @ s2; E2 {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (? HE) "H HΦ". rewrite wpc_eq. iIntros (mj). iSpecialize ("H" $! mj).
  iApply (wpc0_strong_mono _ _ mj with "[$] [$]"); eauto.
Qed.

Lemma wpc_step_strong_mono s1 s2 E1 E2 e Φ Ψ Φc Ψc :
  to_val e = None →
  s1 ⊑ s2 → E1 ⊆ E2 →
  WPC e @ s1; E1 {{ Φ }} {{ Φc }} -∗
  ▷ (∀ v, Φ v -∗ |NC={E2}=> Ψ v) ∧ (Φc -∗ |C={E2}=> Ψc) -∗
  WPC e @ s2; E2 {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (?? HE) "H HΦ". rewrite wpc_eq. iIntros (mj). iSpecialize ("H" $! mj).
  iApply (wpc0_step_strong_mono _ _ mj with "[$] [$]"); eauto.
Qed.

Lemma wpc_strong_mono' s1 s2 E1 E2 e Φ Ψ Φc Ψc :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WPC e @ s1; E1 {{ Φ }} {{ Φc }} -∗
  (∀ v, Φ v ={E2}=∗ Ψ v) ∧ (Φc ={E2}=∗ Ψc) -∗
  WPC e @ s2; E2 {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (??) "? H".
  iApply (wpc_strong_mono with "[$] [-]"); auto.
  iSplit.
  - iDestruct "H" as "(H&_)". iIntros. by iMod ("H" with "[$]").
  - iDestruct "H" as "(_&H)".
    iIntros "HΦc HC". by iApply "H".
Qed.

Lemma wpc_subscript_mono s1 s2 E1 E2 e Φ Φc :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WPC e @ s1; E1 {{ Φ }} {{ Φc }} -∗
  WPC e @ s2; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (??) "H".
  iApply (wpc_strong_mono with "[$] [-]"); auto.
Qed.

Theorem wpc_crash_mono stk E1 e Φ Φc Φc' :
  (Φc' -∗ Φc) -∗
  WPC e @ stk; E1 {{ Φ }} {{ Φc' }} -∗
  WPC e @ stk; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "Hweaken Hwpc".
  iApply (wpc_strong_mono' with "Hwpc"); eauto.
  iSplit; eauto.
  iIntros "Hc'".
  by iApply "Hweaken".
Qed.

Lemma cfupd_fupd E1 Φc:
  (|C={E1}=> Φc) -∗
  (C -∗ |={E1}=> Φc).
Proof.
  iIntros "HΦ C".
  iSpecialize ("HΦ" with "[$]").
  eauto.
Qed.

Lemma wpc_step_strong_mono' s1 s2 E1 E2 e Φ Ψ Φc Ψc :
  to_val e = None →
  s1 ⊑ s2 → E1 ⊆ E2 →
  WPC e @ s1; E1 {{ Φ }} {{ Φc }} -∗
  ▷ (∀ v, Φ v ={E2}=∗ Ψ v) ∧ (Φc -∗ |={E2}=> Ψc) -∗
  WPC e @ s2; E2 {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (???) "? H".
  iApply (wpc_step_strong_mono with "[$] [-]"); auto.
  iSplit.
  - iDestruct "H" as "(H&_)". iNext. iIntros. by iMod ("H" with "[$]").
  - iDestruct "H" as "(_&H)".
    iIntros "HΦc HC". by iApply "H".
Qed.

Lemma wpc_strong_crash_frame' s1 s2 E1 E1' E2 e Φ Φc Ψc :
  s1 ⊑ s2 → E1 ⊆ E2 → E1' ⊆ E2 →
  WPC e @ s1; E1 {{ Φ }} {{ Φc }} -∗
  (|C={E1'}=> Ψc) -∗
  WPC e @ s2; E2 {{ λ v, Φ v ∗ (|C={E1'}=> Ψc)}} {{ Φc ∗ Ψc }}.
Proof.
  iIntros (? HE HE') "H HΦ".  rewrite wpc_eq. iIntros (mj). iSpecialize ("H" $! mj).
  iLöb as "IH" forall (e E1 E1' E2 HE HE' Φ Φc Ψc).
  rewrite !wpc0_unfold /wpc_pre.
  iSplit.
  - destruct (to_val e) as [v|] eqn:?; eauto.
    {
      iDestruct "H" as "(H&_)".
      iMod (fupd_mask_subseteq E1) as "Hclo"; first by auto.
      iIntros. iMod ("H" with "[$] [$]"). iMod "Hclo" as "_".
      iModIntro; eauto. do 2 iFrame.
    }
    iIntros (q σ1 g1 ns D κ κs n) "Hσ Hg HNC Hlc".
    iMod (fupd2_mask_subseteq E1) as "Hclo"; [ done | reflexivity |].
    iDestruct "H" as "(H&_)".
    iMod ("H" with "[$] [$] [$] [$]") as "H".
    iModIntro. simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    iApply (step_fupd2N_wand with "H").
    iIntros "[% H]".
    iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 g2 efs Hstep).
    iMod ("H" with "[//]") as "(Hσ & Hg & H & Hefs & HNC)". iMod "Hclo" as "_". iModIntro.
    iFrame.
    iSplitR "Hefs".
    ** iApply ("IH" with "[] [] H [HΦ]"); auto.
       { destruct (to_val e2); auto. }
       { destruct (to_val e2); auto. }
    ** iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
       iIntros "H". eauto. iApply (wpc0_strong_mono with "H"); eauto.
  - iDestruct "H" as "(_&H)". iIntros.
    iSpecialize ("H" with "[$] [$] [$]").
    rewrite /cfupd.
    iSpecialize ("HΦ" with "[$]").
    iMod (fupd2_mask_subseteq E1) as "Hclo"; [ done | reflexivity |].
    iApply (step_fupd2N_wand with "H").
    iIntros "H". iMod "H". iMod "Hclo".
    iApply (fupd2_mask_mono E1'); auto.
    iApply fupd_fupd2.
    iMod "HΦ". iFrame. eauto.
Qed.

Lemma wpc_strong_crash_frame s1 s2 E1 E2 e Φ Φc Ψc :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WPC e @ s1; E1 {{ Φ }} {{ Φc }} -∗
  (|C={E2}=> Ψc) -∗
  WPC e @ s2; E2 {{ Φ }} {{ Φc ∗ Ψc }}.
Proof.
  iIntros (? HE) "H HΦ".
  iPoseProof (wpc_strong_crash_frame' with "[$] [$]") as "H"; eauto.
  iApply (wpc_strong_mono' with "H"); auto.
  iSplit; eauto.
  by iIntros (?) "($&_)".
Qed.

Lemma wpc_frame_l' s E1 e Φ Φc R R' :
  (R ∧ R') ∗ WPC e @ s; E1 {{ Φ }} {{ Φc }}
  ⊢ WPC e @ s; E1 {{ v, R ∗ Φ v }} {{ R' ∗ Φc }}.
Proof.
  iIntros "[HR H]". iApply (wpc_strong_mono' with "H"); auto.
  iSplit; iIntros; iFrame.
  - by iDestruct "HR" as "($&_)".
  - iDestruct "HR" as "(_&H)". iModIntro. eauto.
Qed.

Lemma wpc_frame_l s E1 e Φ Φc R :
  R ∗ WPC e @ s; E1 {{ Φ }} {{ Φc }}
  ⊢ WPC e @ s; E1 {{ v, R ∗ Φ v }} {{ R ∗ Φc }}.
Proof.
  iIntros "[? H]". iApply (wpc_strong_mono' with "H"); auto.
  iSplit; iIntros; iFrame.
  - by iApply (own_disc_fupd_elim).
  - iModIntro. eauto.
Qed.

Theorem wpc_frame (s : stuckness) (E1 : coPset)
        (e: expr Λ) (Φ Φ': val Λ -> iProp Σ) (Φc Φc': iProp Σ) (R : iPropI Σ) :
    R -∗
    WPC e @ s; E1 {{ v, Φ v }} {{Φc}} -∗
    (R ∗ Φc -∗ Φc') -∗
    (∀ v, R ∗ Φ v -∗ Φ' v) -∗
    WPC e @ s; E1 {{ v, Φ' v }} {{Φc'}}.
Proof.
  iIntros "F Hwpc HΦc' HΦ'".
  iDestruct (wpc_frame_l with "[F $Hwpc]") as "Hwpc".
  { iExact "F". }
  iApply (wpc_strong_mono' with "Hwpc"); eauto.
  iSplit.
  - iIntros (v) "HΦ".
    iApply ("HΦ'" with "HΦ").
  - iIntros "HΦc".
    iApply fupd_mask_intro_discard; [ set_solver+ | ].
    iApply ("HΦc'" with "HΦc").
Qed.

(*
Lemma wpc_fupd_crash_shift s k E1 E2 E2' e Φ Φc :
  E2 ## E2' →
  WPC e @ s; k; E1 ; E2 {{ Φ }} {{ |k={E2', ∅}=> Φc }} ⊢ WPC e @ s; (E2 ∪ E2') {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "H".
  iApply (wpc_strong_mono' s s k k E1 E1 _ with "H []"); auto.
  - set_solver+.
  - iSplit; auto. iIntros "!> H".
    replace ((E2 ∪ E2') ∖ E2) with E2'; first done.
    set_solver.
Qed.

Lemma wpc_fupd_crash_shift' s k E1 E2 e Φ Φc :
  WPC e @ s; k; E1 ; E2 {{ Φ }} {{ |k={∅}=> Φc }} ⊢ WPC e @ s; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H".
  iApply (wpc_strong_mono' s s k k E1 E1 _ with "H []"); auto.
  - iSplit; auto. rewrite difference_diag_L //=. iIntros "!> ". eauto.
Qed.

Lemma wpc_fupd_crash_shift_empty s k E1 e Φ Φc :
  WPC e @ s; k; E1 ; ∅ {{ Φ }} {{ |k={E1}=> Φc }} ⊢ WPC e @ s; ∅ {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H".
  iApply (wpc_strong_mono_empty_crash' s s k k E1 E1 _ with "H []"); auto.
  iSplit; auto. iIntros "!> H".
  iMod "H". eauto.
Qed.
*)

(*
Lemma wpc_inv (N: namespace) s k E e Φ Φc :
  inv N Φc ∗ WPC e @ s; k; E {{ Φ }} {{ True }} ⊢ WPC e @ s; ↑N {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros "(#Hinv&H)".
  iApply (wpc_strong_mono' s s k k E E _ with "H"); try set_solver+.
  iSplit; auto.
  iIntros "!>". iInv N as "H" "Hclo"; first by set_solver+.
  replace (↑N ∖ (∅: coPset) ∖ ↑N) with (∅: coPset) by set_solver.
  iIntros. iModIntro. eauto.
Qed.

Lemma wpc_inv' (N: namespace) s k E1 E2 E2' e Φ P Φc Φc' :
  E2 ⊆ E2' →
  ↑N ⊆ E2' ∖ E2 →
  inv N P ∗ WPC e @ s; E2 {{ Φ }} {{ Φc }} ∗ □ (P -∗ Φc -∗ Φc') ⊢
  WPC e @ s; E2' {{ Φ }} {{ Φc' }}.
Proof.
  iIntros (??) "(#Hinv&H&#Hwand)".
  iApply (wpc_strong_mono' s s k k E1 E1 _ with "H"); try set_solver.
  iSplit; auto.
  iIntros "!> HΦc".
  iMod (fupd_level_mask_subseteq (↑N)); auto.
  iInv N as "H" "Hclo".
  replace (↑N ∖ ↑N) with (∅: coPset) by set_solver.
  iModIntro. iNext. iApply ("Hwand" with "[$] [$]").
Qed.

(* TODO: move before defining wpcs  *)
Lemma inv_cfupd (N: namespace) E1 k P :
  ↑N ⊆ E1 →
  inv N P -∗
  cfupd k E1 (↑N) (P).
Proof.
  iIntros (?) "#Hinv".
  rewrite /cfupd.
  iIntros "_".
  iModIntro.
  iInv N as "H" "Hclo".
  replace (↑N ∖ ↑N) with (∅: coPset) by set_solver.
  by iFrame.
Qed.

Lemma wp_wpc_inv (N: namespace) s k E e Φ Φc :
  inv N Φc ∗ WP e @ s; E {{ Φ }} ⊢ WPC e @ s; ↑N {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros "(#Hinv&H)". iDestruct (wp_wpc with "H") as "H"; eauto. iApply wpc_inv; eauto.
Qed.
*)

Lemma wpc_value s E1 Φ Φc v :
  (|NC={E1}=> Φ v) ∧ (|C={E1}=> Φc) ⊢ WPC of_val v @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre to_of_val. iIntros "H".
  iIntros (mj).
  iSplit.
  - iDestruct "H" as "(H&_)". rewrite ncfupd_eq /ncfupd_def.
    iIntros (q g ns D κs) "Hg HNC". iMod ("H" with "HNC"). by iFrame.
  - iDestruct "H" as "(_&H)". iIntros.
    iMod ("H" with "[$]").
    iApply (step_fupd2N_inner_later); eauto. iModIntro; iFrame.
Qed.

Lemma wpc_value' s E1 Φ Φc v :
 Φ v ∧ Φc ⊢ WPC of_val v @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". iApply wpc_value.
  iSplit.
  - iModIntro. iDestruct "H" as "($&_)".
  - iDestruct "H" as "(_&H)". by iModIntro.
Qed.

Lemma wpc0_value_inv' s mj E1 q Φ Φc v g κs ns D :
  wpc0 s mj E1 (of_val v) Φ Φc -∗
  global_state_interp g ns mj D κs -∗
  NC q -∗
  ||={E1|⊤∖D, E1|⊤∖D}=> Φ v ∗ global_state_interp g ns mj D κs ∗ NC q.
Proof.
  rewrite wpc0_unfold /wpc_pre to_of_val.
  iIntros "H". iDestruct "H" as "(H&_)"; auto.
Qed.

Lemma wpc_value_inv' s E1 q g Φ Φc v mj D κs ns :
  WPC of_val v @ s; E1 {{ Φ }} {{ Φc }} -∗
  global_state_interp g ns mj D κs -∗
  NC q -∗
  ||={E1|⊤∖D, E1|⊤∖D}=> Φ v ∗ global_state_interp g ns mj D κs ∗ NC q.
Proof.
  rewrite wpc_eq. iIntros "H ?". iSpecialize ("H" $! mj).
  iPoseProof (wpc0_value_inv' with "[$] [$]") as "H". eauto.
Qed.

Lemma wpc0_value_inv_option s mj D E1 q Φ Φc e g κs ns :
  wpc0 s mj E1 e Φ Φc -∗
  global_state_interp g ns mj D κs -∗
  NC q -∗
  ||={E1|⊤∖D, E1|⊤∖D}=> from_option Φ True (to_val e) ∗ global_state_interp g ns mj D κs ∗ NC q.
Proof.
  iIntros. destruct (to_val e) as [v|] eqn:He; last by iFrame.
  apply of_to_val in He as <-. by iMod (wpc0_value_inv' with "[$] [$] [$]") as "($&$)".
Qed.

Lemma wpc_value_inv_option s mj D E1 q Φ Φc e g κs ns :
  WPC e @ s; E1 {{ Φ }} {{ Φc }} -∗
  global_state_interp g ns mj D κs -∗
  NC q -∗
  ||={E1|⊤∖D, E1|⊤∖D}=> from_option Φ True (to_val e) ∗ global_state_interp g ns mj D κs ∗ NC q.
Proof.
  iIntros. destruct (to_val e) as [v|] eqn:He; last by iFrame.
  apply of_to_val in He as <-. by iMod (wpc_value_inv' with "[$] [$] [$]") as "($&$)".
Qed.

Lemma wpc_C s E1 e Φ Φc :
 C ∗ Φc ⊢ WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "(#HC&HΦc)".
  rewrite wpc_unfold /wpc_pre /cfupd.
  iIntros (?).
  iSplit.
  - destruct (to_val e).
    * iIntros (?????) "Hg HNC". iDestruct (NC_C with "[$] [$]") as "[]".
    * iIntros (????????) "_ _ HNC". iDestruct (NC_C with "[$] [$]") as "[]".
  - iIntros. iApply step_fupd2N_inner_later; auto. iIntros " !>". iFrame.
Qed.

Lemma fupd_wpc s E1 e Φ Φc:
  (|={E1}=> WPC e @ s; E1 {{ Φ }} {{ Φc }}) ⊢ WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre. iIntros "H".
  iIntros (mj). iSplit.
  - destruct (to_val e).
    * iIntros. iMod "H" as "H". iSpecialize ("H" $! mj). iDestruct "H" as "(H&_)".
      iApply ("H" with "[$] [$]").
    * iIntros. iMod "H" as "H". iSpecialize ("H" $! mj). iDestruct "H" as "(H&_)".
      iApply ("H" with "[$] [$] [$] [$]").
  - iIntros. iMod "H" as "H". iSpecialize ("H" $! mj). iDestruct "H" as "(_&H)".
    iApply ("H" with "[$] [$] [$]").
Qed.

Lemma wpc_fupd2 s E1 e Φ Φc:
  ( WPC e @ s; E1 {{ v, ||={E1|∅, E1|∅}=> Φ v }} {{ Φc }}) ⊢ WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". iApply (wpc_strong_mono_fupd2 with "H"); auto.
Qed.

Lemma wpc_fupd s E1 e Φ Φc:
  ( WPC e @ s; E1 {{ v, |={E1}=> Φ v }} {{ Φc }}) ⊢ WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". iApply (wpc_strong_mono' with "H"); rewrite ?difference_diag_L; auto.
Qed.

Lemma wpc_ncfupd s E1 e Φ Φc:
  ( WPC e @ s; E1 {{ v, |NC={E1}=> Φ v }} {{ Φc }}) ⊢ WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". iApply (wpc_strong_mono with "H"); rewrite ?difference_diag_L; auto.
Qed.

Lemma wpc_cfupd s E1 e Φ Φc:
  ( WPC e @ s; E1 {{ v, Φ v }} {{ |C={E1}=> Φc }}) ⊢ WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". iApply (wpc_strong_mono with "H"); rewrite ?difference_diag_L; auto.
Qed.

Lemma wpc0_crash s mj E1 e Φ Φc:
  wpc0 s mj E1 e Φ Φc -∗
  ((∀ g1 ns D κs, global_state_interp g1 ns mj D κs -∗ C -∗ £ (num_laters_per_step ns) -∗
    ||={E1|⊤∖D,∅|∅}=> ||▷=>^(num_laters_per_step ns) ||={∅|∅,E1|⊤∖D}=> global_state_interp g1 ns mj D κs ∗ Φc))%I.
Proof. rewrite wpc0_unfold /wpc_pre. iIntros "(_&$)". Qed.

Lemma wpc_crash s E1 e Φ Φc:
  WPC e @ s; E1 {{ Φ }} {{ Φc }} -∗
  ((∀ g1 ns mj D κs, global_state_interp g1 ns mj D κs -∗ C -∗ £ (num_laters_per_step ns) -∗
    ||={E1|⊤∖D,∅|∅}=> ||▷=>^(num_laters_per_step ns) ||={∅|∅,E1|⊤∖D}=> global_state_interp g1 ns mj D κs ∗ Φc))%I.
Proof.
  rewrite wpc_unfold /wpc_pre.
  iIntros "H". iIntros (?? mj). iDestruct ("H" $! mj) as "(_&Hc)". eauto.
Qed.

Lemma ncfupd_wpc s E1 e Φ Φc :
  (cfupd E1 Φc) ∧ (|NC={E1}=> WPC e @ s; E1 {{ Φ }} {{ Φc }}) ⊢
  WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  rewrite ncfupd_eq /ncfupd_def.
  iIntros "H". iEval (rewrite wpc_unfold /wpc_pre).
  iIntros (mj).
  destruct (to_val e) as [v|] eqn:He.
  { iSplit.
    - iDestruct "H" as "(_&H)". iIntros (q g ns D κs) "Hg HNC".
      iMod ("H" with "[$]") as "(H&HNC)".
      rewrite wpc_unfold /wpc_pre.
      iDestruct ("H" $! mj) as "(H&_)". rewrite He. by iMod ("H" with "[$] [$]").
    - iDestruct "H" as "(H&_)"; eauto.
      iIntros. iSpecialize ("H" with "[$]"). iMod "H".
      iApply step_fupd2N_inner_later; eauto. iModIntro; iFrame.
  }
  iSplit.
  { iDestruct "H" as "(_&H)". iIntros (q ???????) "Hσ Hg HNC Hlc".
    iSpecialize ("H" $! q).
    rewrite wpc_unfold /wpc_pre.
    iMod ("H" with "[$]") as "(H&HNC)".
    iDestruct ("H" $! mj) as "(H&_)".
    rewrite He.
    by iMod ("H" with "[$] [$] [$] [$]") as "$".
  }
  iDestruct "H" as "(H&_)".
  iIntros. iSpecialize ("H" with "[$]"). iMod "H".
  iApply step_fupd2N_inner_later; eauto. iModIntro; iFrame.
Qed.

(* XXX: the Atomic hypothesis could be weakened to
   Atomic (stuckness_to_atomicity s) but it seems to require
   moving the ⌜ reducible e1 σ1 ⌝ in the definition of wpc_pre to be
   before the conjunction that occurs closest there. *)
Lemma wpc_atomic_crash_modality s E1 e Φ Φc `{!Atomic StronglyAtomic e} :
  (cfupd E1 (Φc)) ∧ (WP e @ s; E1 {{ v, |={E1}=> (|={E1}=>Φ v) ∧ cfupd E1 (Φc) }}) ⊢
  WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". iEval (rewrite !wpc_unfold /wpc_pre).
  rewrite wp_eq /wp_def. rewrite wpc_unfold /wpc_pre.
  iIntros (mj).
  destruct (to_val e) as [v|] eqn:He.
  { iSplit.
    - iDestruct "H" as "(_&H)". iIntros (?????) "Hg HNC".
      iSpecialize ("H" $! mj).
      iDestruct "H" as "[H _]".
      iMod ("H" with "[$] [$]") as "(H&$)".
      iMod "H". iDestruct "H" as "(H&_)".
      iMod "H". eauto.
    - iDestruct "H" as "(H&_)"; eauto.
      iIntros. iMod ("H" with "[$]").
      iApply step_fupd2N_inner_later; eauto. iModIntro; iFrame.
  }
  iSplit.
  {
    iIntros (q σ1 g1 ns D κ κs n) "Hσ Hg HNC Hlc".
    iDestruct "H" as "(_&H)".
    iSpecialize ("H" $! mj).
    iDestruct "H" as "[H _]".
    iMod ("H" with "[$] [$] [$] [$]") as "H".
    iModIntro.
    iApply (step_fupd2N_wand with "H").
    iIntros "[$ H]".
    iIntros (e2 σ2 g2 efs Hstep).
    iMod ("H" with "[//]") as "(Hσ&Hg&H&Hefs&HNC)".
    iFrame "Hσ".
    rewrite wpc0_unfold /wpc_pre.
    destruct (to_val e2) as [v2|] eqn:He2.
    - iDestruct "H" as "[H _]".
      iMod ("H" with "[$] [$]") as "(H&$&HNC)".
      iSplitL "H".
       { rewrite wpc0_unfold /wpc_pre.
         rewrite He2. iMod "H". iModIntro. iSplit.
         * iIntros. iDestruct "H" as "(H&_)". iMod "H". by iFrame.
         * iIntros. iDestruct "H" as "(_&H)".
           iIntros. iMod ("H" with "[$]").
           iApply step_fupd2N_inner_later; eauto. iModIntro; iFrame.
       }
       iFrame. done.
    - edestruct (atomic _ _ _ _ _ _ _ Hstep); congruence.
  }
  iDestruct "H" as "(H&_)"; eauto.
  iIntros. iMod ("H" with "[$]").
  iApply step_fupd2N_inner_later; eauto. iModIntro; iFrame.
Qed.

Lemma fupd_mask_cfupd E1 P:
  (|={E1}=> P) -∗ cfupd E1 P.
Proof. iIntros "H HC". iMod "H". iModIntro. auto. Qed.

Lemma intro_cfupd E1 P:
  P -∗ cfupd E1 P.
Proof. iIntros "HP". iModIntro. eauto. Qed.

Lemma wpc_step_fupd s E1 E2 e P P' Φ Φc :
  to_val e = None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P ∧ (|C={E2}=> P'))
    ∧ (|C={E2}=> P') -∗
  WPC e @ s; E2 {{ v, P ={E1}=∗ Φ v }} {{ P' -∗ Φc }} -∗
  WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  rewrite !wpc_unfold /wpc_pre. iIntros (-> ?) "HR H". iIntros (mj).
  iSpecialize ("H" $! mj).
  iSplit; last first.
  - iDestruct "H" as "(_&H)".
    iDestruct "HR" as "(_&HR)".
    iIntros.
    iSpecialize ("H" with "[$] [$] [$]").
    iDestruct (cfupd_fupd with "HR") as "HR".
    iSpecialize ("HR" with "[$]").
    iApply step_fupd2N_inner_fupd.
    iApply (step_fupd2N_inner_wand with "H"); auto.
    iIntros "($&H)".
    iMod (fupd_mask_mono with "HR") as "HR"; auto.
    iApply "H"; eauto.
  - iDestruct "H" as "(H&_)".
    iIntros (q σ1 g1 ns D κ κs n) "Hσ Hg HNC Hlc".
    iDestruct "HR" as "(HR&_)". iMod "HR".
    iMod ("H" with "[$] [$] [$] [$]") as "H".
    iModIntro. simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    iApply (step_fupd2N_wand with "H").
    iIntros "[$ H]".
    iIntros (e2 σ2 g2 efs Hstep).
    iMod ("H" with "[//]") as "(Hσ & Hg & H & Hefs & HNC)".
    iMod "HR". iModIntro. iFrame "Hσ Hefs". iFrame.
    iApply (wpc0_strong_mono s s mj _ with "H"); auto.
    { destruct (to_val e2); set_solver. }
    iSplit.
    * iIntros (?) "H". iDestruct "HR" as "(HR&_)".
      iApply (ncfupd_mask_mono); last by by iMod ("H" with "[$]"). auto.
      { destruct (to_val e2); set_solver. }
    * iDestruct "HR" as "(_&HR)". iIntros "H".
      iMod (cfupd_weaken_mask with "HR").
      { destruct (to_val e2); set_solver. }
      iModIntro. by iApply "H".
Qed.

(* written to match the premise of wpc_bind *)
(*
Lemma wpc_atomic_from_bind K `{!LanguageCtx K} s E1 E2 e Φ Φc `{!Atomic StronglyAtomic e} :
  <disc> Φc ∧ WP e @ s; E1 {{ v, WPC K (of_val v) @ s; E1; E2 {{ Φ }} {{ Φc }} }} ⊢
  WPC e @ s; E1 ; E2 {{ v, WPC K (of_val v) @ s; E1; E2 {{ Φ }} {{ Φc }} }} {{ Φc }}.
Proof.
  iIntros "Hwp".
  iApply wpc_atomic_crash_modality.
  iSplit.
  - iDestruct "Hwp" as "[H _]". iModIntro. iApply fupd_mask_open_cfupd.
    iApply fupd_atleast_mask_weaken; eauto; set_solver.
  - iDestruct "Hwp" as "[_ Hwp]". iIntros "$".
    iApply (wp_mono with "Hwp").
    iIntros (?) "H". (* iSplit; first done. *)
    iSplit; auto.
    iApply wpc_crash_elim; eauto.
Qed.
*)

Lemma wpc0_bind K `{!LanguageCtx K} s E1 mj e Φ Φc :
  wpc0 s mj E1 e (λ v, wpc0 s mj (match to_val e, to_val (K (of_val v)) with
                                                  | Some _, _ | _, Some _ => E1
                                                  | _, _ => ⊤
                                                  end) (K (of_val v)) Φ Φc) Φc
  ⊢ wpc0 s mj E1 (K e) Φ Φc.
Proof.
  iIntros "H".
  iLöb as "IH" forall (E1 e Φ). rewrite wpc0_unfold /wpc_pre.
  destruct (to_val e) as [v|] eqn:He.
  { setoid_rewrite wpc0_unfold. rewrite /wpc_pre //.
    apply of_to_val in He as Heq0.
    rewrite -Heq0.
    destruct (to_val (K (of_val v))) as [|] eqn:Heq1.
    - iSplit.
      * iDestruct "H" as "(H&_)". iIntros.
        iMod ("H" with "[$] [$]") as "(H&Hg&HNC)".
        rewrite /wpc_def.
        iDestruct "H" as "(H&_)".
        iMod ("H" with "[$] [$]"); eauto.
      * iDestruct "H" as "(_&$)".
    - iSplit.
      * iDestruct "H" as "(H&_)". iIntros.
        iDestruct ("H" with "[$] [$]") as ">(H&Hg&NC)".
        rewrite /wpc_def.
        iDestruct "H" as "(H&_)".
        iMod ("H" with "[$] [$] [$] [$]") as "$".
        eauto.
      * iDestruct "H" as "(_&$)".
  }
  rewrite wpc0_unfold /wpc_pre.
  destruct (to_val (K e)) eqn:Hval.
  { eapply fill_not_val in He; congruence. }
  iSplit; last by (iDestruct "H" as "(_&$)").
  iDestruct "H" as "(H&_)".
  iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC Hlc".
  iMod ("H" with "[$] [$] [$] [$]") as "H".
  iModIntro. simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
  iApply (step_fupd2N_wand with "H").
  iIntros "[% H]".
  iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iIntros (e2 σ2 g2 efs Hstep).
  destruct (fill_step_inv e σ1 g1 κ e2 σ2 g2 efs) as (e2'&->&?); auto.
  iSpecialize ("H" $! e2' σ2 g2 efs with "[//]").
  simpl. iMod "H". iModIntro.
  iDestruct "H" as "(Hσ&Hg&H&Hefs&$)".
  iFrame "Hσ Hg Hefs".
  destruct (to_val e2') eqn:Hval'; eauto.
  - destruct (to_val (K e2')) eqn:Hval''.
    { iApply ("IH" with "[H]").
      iApply (wpc0_strong_mono with "H"); auto.
      iSplit; last by (iIntros "? !>"; eauto).
      iIntros (v') "H".
      iModIntro.
      rewrite Hval'.
      assert (is_Some (to_val (K (of_val v')))) as (?&->).
      { eapply fill_val_inv. apply of_to_val in Hval'. rewrite -Hval' // in Hval''. eauto. }
      eauto.
    }
    { iApply ("IH" with "[H]").
      iApply (wpc0_strong_mono with "H"); auto.
      iSplit; last by (iIntros "? !>"; eauto).
      iIntros (v') "H".
      iModIntro.
      rewrite Hval'.
      iApply (wpc0_strong_mono with "H"); auto.
    }
  - rewrite fill_not_val //.
    iApply ("IH" with "[H]").
    iApply (wpc0_strong_mono with "H"); auto.
    iSplit; last by (iIntros "? !>"; eauto).
    iIntros (v') "H".
    iModIntro.
    rewrite Hval'.
    iApply (wpc0_strong_mono with "H"); auto.
    destruct (to_val (K (of_val v'))); set_solver.
Qed.

Lemma wpc_bind' K `{!LanguageCtx K} s E1 e Φ Φc :
  WPC e @ s; E1 {{ v, WPC K (of_val v) @ s; (match to_val e, to_val (K (of_val v)) with
                                                  | Some _, _ | _, Some _ => E1
                                                  | _, _ => ⊤
                                                  end) {{ Φ }} {{ Φc }} }} {{ Φc }}
                     ⊢ WPC K e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". rewrite ?wpc_eq. iIntros (mj). iSpecialize ("H" $! mj).
  iApply wpc0_bind. iApply (wpc0_strong_mono with "H"); auto.
Qed.

Lemma wpc_bind K `{!LanguageCtx K} s E1 e Φ Φc :
  WPC e @ s; E1 {{ v, WPC K (of_val v) @ s; E1 {{ Φ }} {{ Φc }} }} {{ Φc }}
                     ⊢ WPC K e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H".
  iApply wpc_bind'.
  iApply (wpc_strong_mono' with "H"); auto.
  iSplit; auto.
  iIntros. iModIntro.
  iApply (wpc_strong_mono' with "[$]"); auto.
  { destruct (to_val _); auto.
    destruct (to_val _); auto. }
Qed.

(*
Lemma wpc_bind_inv K `{!LanguageCtx K} s E1 E2 e Φ Φc :
  WPC K e @ s; E1; E2 {{ Φ }} {{ Φc }}
  ⊢ WPC e @ s; E1 ; E2 {{ v, WPC K (of_val v) @ s; E1; E2 {{ Φ }} {{ Φc }} }} {{Φc }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E1 E2 e Φ Φc). rewrite !wpc_unfold /wpc_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He. rewrite <-He. setoid_rewrite wpc_unfold. rewrite /wpc_pre.
    iIntros (mj).
    iSpecialize ("H" $! O). iMod "H". iModIntro. iSplit.
    - iIntros. iModIntro. iFrame. iIntros (mj').
      iModIntro. iSplit.
      * iDestruct "H" as "($&_)".
      * iDestruct "H" as "(_&H)".
Qed.
*)

Lemma wpc_lift_step_fupd s E Φ Φc e1 :
  to_val e1 = None →
  ((∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ |={E,∅}=> ▷
   ((⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
    ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ |={∅,E}=>
      (state_interp σ2 (length efs + nt) ∗
       global_state_interp g2 (step_count_next ns) mj D κs ∗
       WPC e2 @ s; E {{ Φ }} {{ Φc }} ∗
       [∗ list] ef ∈ efs, WPC ef @ s; ⊤ {{ fork_post }} {{ True }}))))
  ∧ |C={E}=> Φc)%I
 ⊢ WPC e1 @ s; E {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre /cfupd=>->. iIntros "H".
  iIntros (mj).
  iSplit; last first.
  { iDestruct "H" as "(_&H)".
    iIntros. iMod ("H" with "[$]").
    iApply step_fupd2N_inner_later; eauto. iModIntro; iFrame.
  }
  iDestruct "H" as "(H&_)". iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC Hlc".
  iMod ("H" with "Hσ Hg") as "H".
  iMod (fupd2_mask_subseteq (∅ : coPset) (∅ : coPset)) as "Hclo"; [done | set_solver+ |].
  iModIntro. simpl. iModIntro. iNext. iModIntro.
  iDestruct "H" as "(%&H)".
  iApply step_fupd2N_later; auto. iModIntro. iFrame "∗ %".
  iIntros. iMod "Hclo". iMod ("H" with "[//]") as "H". iModIntro.
  iDestruct "H" as "($&$&Hwpc&Hlist)".
  iSplitL "Hwpc".
  - iApply wpc0_wpc. iApply (wpc_strong_mono with "[$]"); eauto.
    destruct (to_val _); set_solver.
  - iFrame. iApply (big_sepL_mono with "Hlist"). intros.
      by iApply wpc0_wpc.
Qed.

Lemma wpc_lift_step s E1 Φ Φc e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ |={E1,∅}=> ▷
    (⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
     ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ |={∅,E1}=>
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WPC e2 @ s; E1 {{ Φ }} {{ Φc }} ∗
      [∗ list] ef ∈ efs, WPC ef @ s; ⊤ {{ fork_post }} {{ True }}))
  ∧ Φc
  ⊢ WPC e1 @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "H". iApply wpc_lift_step_fupd; [done|].
  iSplit; last first.
  { iDestruct "H" as "(_&H)". by do 1 iModIntro. }
  iIntros (????????) "Hσ Hg".
  iMod ("H" with "Hσ Hg") as "[$ H]".
  iIntros "!> !> * %". by iApply "H".
Qed.


Lemma global_state_interp_le ns ns' g mj D κs E:
  ns ≤ ns' →
  global_state_interp g ns mj D κs ={E}=∗ global_state_interp g ns' mj D κs.
Proof.
  iIntros (Hle) "Hg".
  iInduction Hle as [|ns'] "IH".
  { eauto. }
  iMod ("IH" with "[$]") as "Hg".
  iMod (fupd_mask_subseteq ∅) as "H"; first set_solver+.
  iMod (global_state_interp_mono with "Hg"). iMod "H". eauto.
Qed.

Lemma wpc_lift_pure_step_no_fork `{!Inhabited (state Λ)} `{!Inhabited (global_state Λ)} s E1 E1' Φ Φc e1 :
  (∀ σ1 g1, if s is NotStuck then reducible e1 σ1 g1 else to_val e1 = None) →
  (∀ κ σ1 g1 e2 σ2 g2 efs, prim_step e1 σ1 g1 κ e2 σ2 g2 efs → κ = [] ∧ σ2 = σ1 ∧ g2 = g1 ∧ efs = []) →
  (|={E1,E1'}=> ▷ |={E1', E1}=>
          ∀ κ e2 efs σ g, ⌜prim_step e1 σ g κ e2 σ g efs⌝ → WPC e2 @ s; E1 {{ Φ }} {{ Φc }}) ∧ Φc
  ⊢ WPC e1 @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wpc_lift_step.
  { specialize (Hsafe inhabitant inhabitant). destruct s; eauto using reducible_not_val. }
  iSplit; last by (iDestruct "H" as "(_&$)").
  iDestruct "H" as "(H&_)".
  iIntros (σ1 g1 ns mj D κ κs n) "Hσ Hg". iMod "H".
  iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver. iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 g2 efs ?).
  destruct (Hstep κ σ1 g1 e2 σ2 g2 efs) as (-> & <- & <- & ->); auto.
  iMod (global_state_interp_le _ (step_count_next ns) with "Hg") as "$".
  { apply step_count_next_incr. }
  iFrame "Hσ".
  iMod "Hclose" as "_". iMod "H". iModIntro.
  iDestruct ("H" with "[//]") as "H". simpl. iFrame.
Qed.

Lemma wpc_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} `{!Inhabited (global_state Λ)}
      {s E1 E1' Φ Φc} e1 e2 :
  (∀ σ1 g1, if s is NotStuck then reducible e1 σ1 g1 else to_val e1 = None) →
  (∀ σ1 g1 κ e2' σ2 g2 efs', prim_step e1 σ1 g1 κ e2' σ2 g2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ g2 = g1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E1,E1'}=> ▷ |={E1', E1}=>
                    WPC e2 @ s; E1 {{ Φ }} {{ Φc }}) ∧ Φc
  ⊢ WPC e1 @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wpc_lift_pure_step_no_fork s E1 E1'); try done.
  { naive_solver. }
  iSplit; last by (iDestruct "H" as "(_&$)").
  iDestruct "H" as "(H&_)".
  iMod "H". iModIntro. iNext. iMod "H". iModIntro.
  iIntros (κ e' efs' σ g). iIntros ((_&?&?&->&?)%Hpuredet); auto.
Qed.

(* Note: compared to wp_pure_step_fupd, we have n = 1 *)
Lemma wpc_pure_step_fupd `{!Inhabited (state Λ), !Inhabited (global_state Λ)} s E1 e1 e2 φ Φ Φc :
  PureExec φ 1 e1 e2 →
  φ →
  (|={E1,∅}=> ▷ |={∅,E1}=> WPC e2 @ s; E1 {{ Φ }} {{ Φc }}) ∧ Φc
  ⊢ WPC e1 @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  inversion Hexec as [|? e1' e2' e3' [Hsafe ?] Hrest]. subst.
  inversion Hrest; subst.
  iApply wpc_lift_pure_det_step_no_fork; last eauto.
  - intros σ g. specialize (Hsafe σ g). destruct s;
    eauto using reducible_not_val, reducible_no_obs_reducible.
  - done.
Qed.

Lemma wpc_pure_step_later `{!Inhabited (state Λ), !Inhabited (global_state Λ)} s E1 e1 e2 φ Φ Φc :
  PureExec φ 1 e1 e2 →
  φ →
  ▷ WPC e2 @ s; E1 {{ Φ }} {{ Φc }} ∧ Φc
  ⊢ WPC e1 @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  intros Hexec ?. rewrite -wpc_pure_step_fupd //. clear Hexec.
  apply and_mono; auto. iIntros "H".
  rewrite //= -step_fupd_intro //. set_solver.
Qed.

(*
Lemma wp_atomic s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 κ κs n) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iIntros (e2 σ2 efs Hstep).
  iMod ("H" with "[//]") as "H". iIntros "!>!>".
  iMod "H" as "(Hσ & H & Hefs)". destruct s.
  - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" $! _ [] with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ Hstep).
  - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
    iMod (wp_value_inv' with "H") as ">H".
    iModIntro. iFrame "Hσ Hefs". by iApply wp_value'.
Qed.

Lemma wp_step_fupd s E1 E2 e P Φ :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 κ κs n) "Hσ". iMod "HR". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!>" (e2 σ2 efs Hstep). iMod ("H" $! e2 σ2 efs with "[% //]") as "H".
  iIntros "!>!>". iMod "H" as "(Hσ & H & Hefs)".
  iMod "HR". iModIntro. iFrame "Hσ Hefs".
  iApply (wp_strong_mono s s E2 with "H"); [done..|].
  iIntros (v) "H". by iApply "H".
Qed.

Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ :
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite fill_not_val //.
  iIntros (σ1 κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]". iModIntro; iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! (K e2) σ2 efs with "[]") as "H"; [by eauto using fill_step|].
  iIntros "!>!>". iMod "H" as "(Hσ & H & Hefs)".
  iModIntro. iFrame "Hσ Hefs". by iApply "IH".
Qed.
*)

(** * Derived rules *)
Lemma wpc_mono s E1 e Φ Ψ Φc Ψc :
  (∀ v, Φ v ⊢ Ψ v) → (Φc ⊢ Ψc) → WPC e @ s; E1 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; E1 {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (HΦ HΦc) "H"; iApply (wpc_strong_mono' with "H"); auto.
  iSplit.
  - iIntros (v) "?". by iApply HΦ.
  - iIntros "? !>". by iApply HΦc.
Qed.

Lemma wpc_mono' s E1 e Φ Ψ Φc Ψc :
  (∀ v, Φ v -∗ Ψ v) -∗ (Φc -∗ Ψc) -∗ WPC e @ s; E1 {{ Φ }} {{ Φc }} -∗
  WPC e @ s; E1  {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros "H1 H2 H3"; iApply (wpc_strong_mono' with "H3"); auto.
  iSplit.
  - iIntros (v) "?". by iApply "H1".
  - iIntros "? !>". by iApply "H2".
Qed.

Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. intros Hpost. rewrite wp_eq. apply wpc_mono; done. Qed.

Lemma wpc_atomic s E1 e Φ Φc `{!Atomic StronglyAtomic e} :
  (|={E1}=> Φc) ∧ WP e @ s; E1 {{ v, (|={E1}=> Φ v) ∧ |={E1}=> Φc }} ⊢
  WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". iApply (wpc_atomic_crash_modality); iApply (and_mono with "H").
  { iIntros "H HC". eauto. }
  iIntros "H".
  iApply (wp_mono with "H"). iIntros (?).
  iIntros "H". iModIntro.
  iApply (and_mono with "H"); auto.
  { iIntros "H HC". eauto. }
Qed.

(* note that this also reverses the postcondition and crash condition, so we
prove the crash condition first *)
Lemma wpc_atomic_no_mask s E1 e Φ Φc `{!Atomic StronglyAtomic e} :
  Φc ∧ WP e @ s; E1 {{ v, (|={E1}=> Φc) ∧ (|={E1}=> Φ v) }} ⊢
  WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "Hc_wp".
  iApply wpc_atomic.
  iSplit.
  - iDestruct "Hc_wp" as "(?&_)". iApply fupd_mask_intro_discard; [ set_solver+ | ].
    eauto.
  - iDestruct "Hc_wp" as "[_ Hwp]".
    iApply (wp_mono with "Hwp").
    iIntros (x) "HΦ".
    iSplit.
    + iDestruct "HΦ" as "[_  >HΦc]". eauto.
    + iDestruct "HΦ" as "[HΦ _]".
      iMod "HΦ" as "HΦ".
      iApply fupd_mask_intro_discard; [ set_solver+ | ]; iFrame.
Qed.

Lemma wp_wpc_frame' s E1 e Φ Φc R :
  (Φc ∧ R) ∗
  WP e @ s; E1 {{ λ v, R -∗ Φ v }} ⊢
  WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "(HΦc&Hwp)".
  iApply (wpc_strong_mono' s s E1 E1 _ (λ v, R ∗ (R -∗ Φ v))%I _ (Φc ∗ True)%I
         with "[-]"); auto.
  { iApply wpc_frame_l'.
    rewrite comm; iFrame.
    iApply wp_wpc; eauto. }
  iSplit.
  - iIntros (?). rewrite wand_elim_r. iIntros; eauto.
  - iIntros "(H&?)". iApply (fupd_mask_intro_discard); eauto.
Qed.

Lemma wp_wpc_step_frame' s E1 e Φ Φc R :
  to_val e = None →
  (Φc ∧ ▷ R) ∗
  WP e @ s; E1 {{ λ v, R -∗ Φ v }} ⊢
  WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "(HΦc&Hwp)".
  iApply (wpc_step_fupd _ _ _ _ R (Φc) with "[HΦc]"); first done.
  { reflexivity. }
  { iSplit.
    * iModIntro. iNext. iModIntro. iSplit.
      ** iDestruct "HΦc" as "(_&$)".
      ** iDestruct "HΦc" as "(H&_)". do 1 iModIntro. eauto.
    * iDestruct "HΦc" as "(H&_)". do 1 iModIntro. eauto.
  }
  iApply (wpc_strong_mono' s s E1 E1 _ (λ v, (R -∗ Φ v))%I _ (True)%I
         with "[-]"); auto.
  { iApply wp_wpc. iApply "Hwp". }
  iSplit.
  - iIntros (?) "H !> HR !>". by iApply "H".
  - iIntros "_ !> $".
Qed.

Lemma wp_wpc_frame s E1 e Φ Φc :
  Φc ∗ WP e @ s; E1 {{ λ v, Φc -∗ Φ v }} ⊢
  WPC e @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "(HΦc&Hwp)".
  iApply wpc_fupd.
  iApply (wp_wpc_frame' _ _ _ _ _ Φc).
  iSplitL "HΦc".
  { iSplit; eauto. }
  iApply (wp_mono with "Hwp").
  iIntros (?) "H Hdisc". by iApply "H".
Qed.

Lemma wpc_crash_frame_wand s E2 e Φ Φc Ψc :
  WPC e @ s; E2 {{ Φ }} {{ Ψc -∗ Φc }} -∗
  (|C={E2}=> Ψc) -∗
  WPC e @ s; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros.
  iAssert (WPC e @ s; E2  {{ Φ }} {{ (Ψc -∗ Φc) ∗ Ψc }})%I with "[-]" as "Hwp"; last first.
  { iApply (wpc_mono with "Hwp"); auto. rewrite wand_elim_l //. }
  by iApply (wpc_strong_crash_frame with "[$]").
Qed.

Lemma wpc_crash_frame_wand' s E1 E2 e Φ Φc Ψc :
  E1 ⊆ E2 →
  WPC e @ s; E2 {{ λ v, (|C={E1}=> Ψc) -∗ Φ v }} {{ Ψc -∗ Φc }} -∗
  (|C={E1}=> Ψc) -∗
  WPC e @ s; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros.
  iAssert (WPC e @ s; E2  {{ λ v, ((|C={E1}=> Ψc) -∗ Φ v) ∗ (|C={E1}=> Ψc) }}
                             {{ (Ψc -∗ Φc) ∗ Ψc }})%I with "[-]" as "Hwp"; last first.
  { iApply (wpc_mono with "Hwp"); auto.
    - iIntros (?). simpl. rewrite wand_elim_l //.
     - by rewrite wand_elim_l.
  }
  iApply (wpc_strong_crash_frame' with "[$]"); auto.
Qed.

(* This is mainly for compatibility reasons *)
Lemma wpc_crash_frame_wand_bdisc s E1 E2 e Φ Φc Ψc :
  E1 ⊆ E2 →
  WPC e @ s; E2 {{ λ v, <bdisc> (|C={E1}=> Ψc) -∗ Φ v }} {{ Ψc -∗ Φc }} -∗
  <bdisc> (|C={E1}=> Ψc) -∗
  WPC e @ s; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "H Hbdisc".
  iApply (wpc_strong_mono with "H"); auto.
  iSplit.
  { iIntros (?) "H !>". iApply "H". eauto. }
  iIntros "H".
  iDestruct (own_discrete_elim with "Hbdisc") as "Hbdisc".
  iIntros "HC". iSpecialize ("Hbdisc" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclo"; eauto.
  iMod "Hbdisc". iMod "Hclo". iModIntro. iApply "H"; eauto.
Qed.

Definition bi_sch_cfupd_protector E :=
  (wsat.bi_sch_or (wsat.bi_sch_wand (wsat.bi_sch_var_fixed O) (bi_sch_fupd_mj E E None (wsat.bi_sch_var_fixed 1)))
                  (wsat.bi_sch_var_fixed 2))%I.

(*
Lemma cfupd_to_disc k1 k2 E2 P:
  S k1 ≤ k2 →
  (|C={E2}_k1=> ▷ P) -∗ (|k2={E2}=> <disc> |C={E2}_(S k1)=> ▷ P) .
Proof.
  iMod (own_alloc (Cinl 1%Qp)) as (γ) "H".
  { rewrite //=. }
  iIntros (Hle) "HP".
  iPoseProof (ae_inv_mut_alloc (S k1) None E2 (bi_sch_cfupd_protector E2)
                                        [C; P; own γ (Cinl 1%Qp)]%I [] with "[HP]") as "Hinv".
  { rewrite wsat.bi_schema_interp_unfold.
    rewrite /bi_sch_cfupd_protector.
    rewrite wsat.bi_schema_interp_unfold.
    erewrite bi_sch_fupd_interp_mj; last first.
    { reflexivity. }
    rewrite ?wsat.bi_schema_interp_unfold ?list_lookup_fmap //=.
    iLeft. iIntros ">HC".
    iSpecialize ("HP" with "[$]").
    iMod (fupd_level_split_level with "HP") as "H"; first lia.
    eauto.
  }
  rewrite uPred_fupd_level_eq.
  iMod (fupd_split_level_le with "Hinv") as "(#Hinv&_)"; first naive_solver lia.
  iModIntro. rewrite own_discrete_fupd_eq /own_discrete_fupd_def. iModIntro.
  rewrite uPred_fupd_level_eq.
  iPoseProof (ae_inv_mut_acc _ _ E2 _ _ (|C={E2}_k1=> ▷ P) with "Hinv [H]") as "H".
  { iIntros (?).
    rewrite wsat.bi_schema_interp_unfold.
    rewrite /bi_sch_cfupd_protector.
    rewrite wsat.bi_schema_interp_unfold.
    erewrite bi_sch_fupd_interp_mj; last first.
    { reflexivity. }
    rewrite ?wsat.bi_schema_interp_unfold ?list_lookup_fmap //=.
    iDestruct 1 as "[HP|>Hfalse]".
    { iModIntro. iFrame "H".
      rewrite /cfupd. iIntros "HC".
      iSpecialize ("HP" with "[$]").
      rewrite uPred_fupd_level_eq /uPred_fupd_level_def.
      eauto.
    }
    { by iDestruct (own_valid_2 with "H Hfalse") as %?. }
  }
  iModIntro.
  iIntros "HC".
  rewrite /cfupd ?uPred_fupd_level_eq /uPred_fupd_level_def.
  iMod "H". iSpecialize ("H" with "[$]").
  iApply (fupd_split_level_le with "H"); eauto.
Qed.
*)


(*
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. by apply wp_value'. Qed.
Lemma wp_value_fupd' s E Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
Lemma wp_value_fupd s E Φ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
Proof. intros. rewrite -wp_fupd -wp_value //. Qed.
Lemma wp_value_inv s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ={E}=∗ Φ v.
Proof. intros <-. by apply wp_value_inv'. Qed.

Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma wp_frame_step_l s E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1,E2}▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  to_val e = None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  to_val e = None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
*)

(** Access the state interpretation resources temporarily. This only gives the
    global resources because the very next step might be a crash. *)
Lemma wpc_acc_global_state_interp s E e Φ Φc :
  TCEq (to_val e) None →
  (∀ g ns mj D κs, global_state_interp g ns mj D κs ={E}=∗
    (global_state_interp g ns mj D κs ∗
     WPC e @ s; E {{ Φ }} {{ Φc }})) -∗
  WPC e @ s; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (HnotVal) "H".
  setoid_rewrite wpc_unfold. rewrite /wpc_pre.
  rewrite HnotVal.
  iIntros (mj).
  iSplit.
  {
    iIntros (????????).
    iIntros "? Hg ? ?".
    iMod ("H" with "Hg") as "H".
    iDestruct "H" as "[Hg H]".
    iSpecialize ("H" $! mj).
    iDestruct "H" as "[H _]".
    iApply ("H" with "[$] [$] [$] [$]").
  }
  {
    iIntros (????) "Hg ? ?".
    iMod ("H" with "Hg") as "H".
    iDestruct "H" as "[Hg H]".
    iSpecialize ("H" $! mj).
    iDestruct "H" as "[_ H]".
    iApply ("H" with "[$] [$] [$]").
  }
Qed.

End wpc.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS Λ Σ, !generationGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wpc s E1 e R Φ Ψ Φc Ψc :
    (∀ v, Frame false R (Φ v) (Ψ v)) →
     Frame false R Φc Ψc →
    Frame false R (WPC e @ s; E1 {{ Φ }} {{ Φc }}) (WPC e @ s; E1 {{ Ψ }} {{ Ψc }}).
  Proof.
    rewrite /Frame=> HR HRc.
    iIntros "(HR&Hwpc)".
    iAssert (R ∧ R)%I with "[HR]" as "HR"; first by auto.
    iPoseProof (wpc_frame_l' with "[$Hwpc HR]") as "Hwpc".
    { iSplit.
      * iApply "HR".
      * iDestruct "HR" as "(_&HHR)". iApply "HHR".
    }
    iApply (wpc_mono with "Hwpc"); last done.
    { iIntros (?) "(HR&HΨ)". iApply HR.
      iFrame. iDestruct "HR" as "($&_)".
    }
  Qed.


  Global Instance frame_wpc' p s E1 e R Φ Ψ Φc Ψc :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
     Frame p R Φc Ψc →
    Frame p R (WPC e @ s; E1 {{ Φ }} {{ Φc }}) (WPC e @ s; E1 {{ Ψ }} {{ Ψc }}).
  Proof.
    rewrite /Frame=> HR HRc.
    iIntros "(HR&Hwpc)".
    iAssert (□?p R ∧ □?p R)%I with "[HR]" as "HR".
    { iSplit; first by auto. destruct p => //=. }
    iPoseProof (wpc_frame_l' with "[$Hwpc HR]") as "Hwpc".
    { iSplit.
      * iApply "HR".
      * iDestruct "HR" as "(_&HHR)". iApply "HHR".
    }
    iApply (wpc_mono with "Hwpc"); last done.
    { iIntros (?) "(HR&HΨ)". iApply HR.
      iFrame. iDestruct "HR" as "($&_)".
    }
  Qed.

  Global Instance is_except_0_wpc s E1 e Φ Φc : IsExcept0 (WPC e @ s; E1 {{ Φ }} {{ Φc }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wpc -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wpc p s E1 e P Φ Φc:
    ElimModal True p false (|==> P) P (WPC e @ s; E1 {{ Φ }} {{ Φc }}) (WPC e @ s; E1 {{ Φ }} {{ Φc }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_wpc.
  Qed.

  Global Instance elim_modal_fupd_wpc p s E1 e P Φ Φc :
    ElimModal True p false (|={E1}=> P) P (WPC e @ s; E1 {{ Φ }} {{ Φc }})
              (WPC e @ s; E1 {{ Φ }} {{ Φc }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wpc.
  Qed.

  Global Instance elim_modal_fupd_level_wpc k p s E1 e P Φ Φc :
    ElimModal True p false (|k={E1}=> P) P (WPC e @ s; E1 {{ Φ }} {{ Φc }})
              (WPC e @ s; E1 {{ Φ }} {{ Φc }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim fupd_level_fupd fupd_frame_r wand_elim_r fupd_wpc.
  Qed.

  Global Instance elim_modal_cfupd_wpc p s E1 e P Φ Φc :
    ElimModal True p false (cfupd E1 P) True
              (WPC e @ s; E1 {{ Φ }} {{ Φc }})
              (WPC e @ s; E1 {{ Φ }} {{ P -∗ Φc }}).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim.
    iIntros (?) "[Hc Hwpc]".
    iSpecialize ("Hwpc" with "[//]").
    iApply (wpc_crash_frame_wand with "Hwpc [Hc]").
    iMod "Hc" as "$".
    iModIntro; done.
  Qed.

  Global Instance elim_modal_cfupd0_sub_wpc p s E1 E2 e P Φ Φc :
    ElimModal (E1 ⊆ E2) p false (cfupd E1 (P)) True
              (WPC e @ s; E2 {{ Φ }} {{ Φc }})
              (WPC e @ s; E2 {{ Φ }} {{ P -∗ Φc }}).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim.
    iIntros (?) "[Hc Hwpc]".
    iSpecialize ("Hwpc" with "[//]").
    iApply (wpc_crash_frame_wand with "Hwpc [Hc]").
    iApply (cfupd_weaken_mask _ E1); [ by auto | ].
    iMod "Hc" as "$".
    iModIntro; done.
  Qed.

  Example test_wpc_frame s E1 e Φ Φc Ψc :
    WPC e @ s; E1 {{ Φ }} {{ Φc }} -∗
    (|C={E1}=> Ψc) -∗
    WPC e @ s; E1 {{ Φ }} {{ Φc ∗ Ψc }}.
  Proof.
    iIntros "Hwpc Hc".
    iMod "Hc" as "_".
    iApply (wpc_mono' with "[] [] Hwpc"); auto.
    iIntros "$ $".
  Qed.

  (*
  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp {X} E1 E2 α β γ e s Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
  *)
End proofmode_classes.

Section wpc_ectx_lifting.
Import ectx_language.
Context {Λ : ectxLanguage} `{!irisGS Λ Σ, !generationGS Λ Σ} {Hinh : Inhabited (state Λ)}.
Hint Resolve base_prim_reducible base_reducible_prim_step : core.
Local Definition reducible_not_val_inhabitant_state e := reducible_not_val e inhabitant.
Hint Resolve reducible_not_val_inhabitant_state : core.
Hint Resolve base_stuck_stuck : core.

Lemma wpc_lift_base_step_fupd s E Φ Φc e1 :
  to_val e1 = None →
  ((∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ |={E,∅}=> ▷
    (⌜base_reducible e1 σ1 g1⌝ ∗
    ∀ e2 σ2 g2 efs, ⌜base_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ |={∅,E}=>
      (state_interp σ2 (length efs + nt) ∗
       global_state_interp g2 (step_count_next ns) mj D κs ∗
       WPC e2 @ s; E {{ Φ }} {{ Φc }} ∗
       [∗ list] ef ∈ efs, WPC ef @ s; ⊤ {{ fork_post }} {{ True }})))
  ∧ |C={E}=> Φc)%I
 ⊢ WPC e1 @ s; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "H". iApply wpc_lift_step_fupd=>//. iSplit.
  - iDestruct "H" as "(H&_)". iIntros (σ1 g1 ns mj D κ κs nt) "Hσ Hg".
    iMod ("H" with "Hσ Hg") as "[>% H]"; iModIntro.
    iSplit; first by destruct s; eauto. iIntros (e2 σ2 g2 efs ?).
    iApply "H"; eauto.
  - iDestruct "H" as "(_&$)".
Qed.

Lemma wpc_lift_base_step s E1 Φ Φc e1 :
  to_val e1 = None →
  ((∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ |={E1,∅}=> ▷
    (⌜base_reducible e1 σ1 g1⌝ ∗
     ∀ e2 σ2 g2 efs, ⌜base_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ |={∅,E1}=>
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WPC e2 @ s; E1 {{ Φ }} {{ Φc }} ∗
      [∗ list] ef ∈ efs, WPC ef @ s; ⊤ {{ fork_post }} {{ True }}))
  ∧ |C={E1}=> Φc)%I
  ⊢ WPC e1 @ s; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "H". iApply wpc_lift_base_step_fupd; [done|]. iSplit.
  - iDestruct "H" as "(H&_)". iIntros (????????) "??".
    iMod ("H" with "[$] [$]") as "[$ H]". iIntros "!> !>" (e2 σ2 g2 efs ?). by iApply "H".
  - iDestruct "H" as "(_&$)".
Qed.

End wpc_ectx_lifting.
