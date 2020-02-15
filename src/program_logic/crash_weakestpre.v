From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import crash_token step_fupd_extra.
Set Default Proof Using "Type".
Import uPred.

(* Define a weakestpre with an explicit crash invariant (i.e. there is a postcondition and a crash condition *)

Definition wpc_pre `{!irisG Λ Σ} `{crashG Σ} (s : stuckness) (k: nat)
    (wpc : coPset -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ) :
    coPset -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ := λ E1 E2 e1 Φ Φc,
  (match to_val e1 with
   | Some v => NC ={E1}=∗ Φ v ∗ NC
   | None => ∀ σ1 κ κs n,
      state_interp σ1 (κ ++ κs) n -∗ NC ={E1,∅}=∗ (|={∅, ∅}▷=>^(S k)
        ((|={∅}=> ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
        ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ |={∅,∅}_(S k)=> |={∅,∅,E1}▷=> |={E1, E1}_(S k)=>
          (state_interp σ2 κs (length efs + n) ∗
          wpc E1 E2 e2 Φ Φc ∗
          ([∗ list] i ↦ ef ∈ efs, wpc ⊤ ∅ ef fork_post True) ∗
          NC))))
   end ∧
   (C -∗ |={E1,E1}_(S k)=> |={E2, ∅}=> |={∅, ∅}▷=>^(S k) |={∅, ∅}=> Φc))%I.


Local Instance wpc_pre_contractive `{!irisG Λ Σ} `{crashG Σ} s k : Contractive (wpc_pre s k).
Proof.
  rewrite /wpc_pre=> n wp wp' Hwp E1 E2 e1 Φ Φc.
  repeat (apply step_fupdN_ne || f_contractive || f_equiv); apply Hwp.
Qed.

Definition wpc_def `{!irisG Λ Σ} `{crashG Σ} (s : stuckness) (k: nat) :
  coPset → coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ → iProp Σ := fixpoint (wpc_pre s k).
Definition wpc_aux `{!irisG Λ Σ} `{crashG Σ} : seal (@wpc_def Λ Σ _ _). by eexists. Qed.


(* Notation: copied from iris bi/weakestpre.v *)
Class Wpc (Λ : language) (PROP A B : Type) :=
  wpc : A → B → coPset → coPset → expr Λ → (val Λ → PROP) → PROP → PROP.
Arguments wpc {_ _ _ _ _} _ _ _ _ _%E _%I _%I.
Instance: Params (@wpc) 11 := {}.

Instance wpc' `{!irisG Λ Σ} `{crashG Σ} : Wpc Λ (iProp Σ) stuckness nat := wpc_aux.(unseal).
Definition wpc_eq `{!irisG Λ Σ} `{crashG Σ} : wpc = @wpc_def Λ Σ _ _ := wpc_aux.(seal_eq).

(** Notations for partial crash weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WPC' e @ s ; k ; E1 ; E2 {{ Φ } } {{ Φc } }" := (wpc s k%nat E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e @ k ; E1 ; E2 {{ Φ } } {{ Φc } }" := (wpc NotStuck k%nat E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
(*
Notation "'WPC' e @ E1 ; E2 ? {{ Φ } } {{ Φc } }" := (wpc MaybeStuck E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
*)
Notation "'WPC' e @ k {{ Φ } } {{ Φc } }" := (wpc NotStuck k%nat ⊤ ∅ e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
(*
Notation "'WPC' e ? {{ Φ } } {{ Φc } }" := (wpc MaybeStuck ⊤ ∅ e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
*)

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'WPC' e @ s ; k ; E1 ; E2 {{ v , Q } } {{ R } }" := (wpc s k%nat E1 E2 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[' 'WPC'  e  '/' '[          ' @  s ;  k ;  E1 ;  E2  {{  v ,  Q  } }  {{ R } } ']' ']'") : bi_scope.
Notation "'WPC' e @ k ; E1 ; E2 {{ v , Q } } {{ R } }" := (wpc NotStuck k%nat E1 E2 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[' 'WPC'  e  '/' '[       ' @  k ;  E1 ; E2  {{  v ,  Q  } } {{ R } } ']' ']'") : bi_scope.

(* Texan triples *)
Notation "'{{{' P } } } e @ s ; k ; E1 ; E2 {{{ x .. y , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc,
      P -∗ (Qc -∗ Φc) ∧ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  s ; k ;  E1 ; E2 '/' {{{  x  ..  y ,  RET  pat ;  Q  } } } '/' {{{ Qc } } } ']'") : bi_scope.
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

Notation "'{{{' P } } } e @ s ; k ; E1 ; E2 {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (Q -∗ Φ pat%V) -∗ WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  s ; k ;  E1 ; E2 '/' {{{  RET  pat ;  Q  } } } '/' {{{ Qc } } } ']'") : bi_scope.
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
Notation "'{{{' P } } } e @ s ; k ; E1 ; E2 {{{ x .. y , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }}) : stdpp_scope.
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
Notation "'{{{' P } } } e @ s ; k ; E1 ; E2 {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (Q -∗ Φ pat%V) -∗ WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }}) : stdpp_scope.
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

Section wpc.
Context `{!irisG Λ Σ} `{crashG Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpc_unfold s k E1 E2 e Φ Φc :
  WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }} ⊣⊢ wpc_pre s k (wpc (PROP:=iProp Σ) s k) E1 E2 e Φ Φc.
Proof. rewrite wpc_eq. apply (fixpoint_unfold (wpc_pre s k)). Qed.

Global Instance wpc_ne s k E1 E2 e n :
  Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) (wpc (PROP:=iProp Σ) s k E1 E2 e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ Φc Ψc HΦc.
  rewrite !wpc_unfold /wpc_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 4 (apply step_fupdN_ne || f_contractive || f_equiv); auto.
  { f_equiv. f_equiv. }
  2: { f_equiv. f_equiv. apply step_fupdN_ne. f_equiv. eauto. }
  do 30 (apply step_fupdN_ne || f_contractive || f_equiv).
  eapply IH; eauto.
  - intros v. eapply dist_le; eauto.
  - eapply dist_le; eauto.
Qed.

Global Instance wpc_proper s k E1 E2 e :
  Proper (pointwise_relation _ (≡) ==> (≡) ==> (≡)) (wpc (PROP:=iProp Σ) s k E1 E2 e).
Proof.
  intros Φ Φ' ? Φc Φc' ?.
  apply equiv_dist=>n. apply wpc_ne; auto.
  by intros v; apply equiv_dist.
Qed.

Lemma wp_wpc s E1 E2 e Φ k:
  WP e @ s ; E1 {{ Φ }} ⊢ WPC e @ s ; k ; E1 ; E2 {{ Φ }} {{ True }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E1 E2 e Φ).
  rewrite wp_unfold wpc_unfold /wp_pre /wpc_pre.
  iSplit; last first.
  - iIntros "HC".
    iApply step_fupdN_inner_later; auto.
    do 2 iNext.
    iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
    iApply step_fupdN_inner_later; auto.
  - destruct (to_val e) as [v|]=>//.
    { iIntros; iFrame. }
    iIntros (σ1 κ κs n) "Hσ".
    iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
    iIntros "HNC".
    iModIntro.
    iApply step_fupdN_later; auto.
    iNext. iNext.
    iMod "Hclo" as "_".
    iMod ("H" with "Hσ") as "[% H]". iIntros "!>".
    iSplitR.
    { destruct s; last done. eauto using reducible_no_obs_reducible. }
    iIntros (e2 σ2 efs) "Hstep". iMod ("H" with "Hstep") as "H".
    iApply step_fupdN_inner_later; first by reflexivity.
    do 2 iNext. iModIntro. iNext. iMod ("H") as "(Hσ & H & Hfork)". iFrame. iModIntro.
    iApply step_fupdN_inner_later; first by set_solver+. do 2 iNext.
    iFrame. iSplitL "H".
    { by iApply "IH". }
    iApply (@big_sepL_impl with "Hfork").
    iIntros "!#" (? ef _) "H". by iApply "IH".
Qed.

Lemma wpc_wp s E1 E2 e Φ Φc k:
  WPC e @ s ; k; E1; E2 {{ Φ }} {{ Φc }} ⊢ NC -∗ WP e @ s ; E1 {{ Φ }}.
Proof.
  iIntros "H HNC". (iLöb as "IH" forall (E1 E2 e Φ)).
  rewrite wp_unfold wpc_unfold /wp_pre /wpc_pre.
  destruct (to_val e) as [v|]=>//.
  - iDestruct "H" as "[H _]".
    iDestruct ("H" with "HNC") as ">[$ _]".
    auto.
  - iIntros (σ κ κs n) "Hinterp".
    iDestruct "H" as "[H _]".
    iMod ("H" with "Hinterp [$]") as "H".
    (* oops, H is under (S k) laters so probably isn't usable *)
Abort.

Lemma wpc_strong_mono s1 s2 k1 k2 E1 E2 E1' E2' e Φ Ψ Φc Ψc :
  s1 ⊑ s2 → k1 ≤ k2 → E1 ⊆ E2 → E1' ⊆ E2' →
  WPC e @ s1; k1; E1 ; E1' {{ Φ }} {{ Φc }} -∗
  (∀ v, Φ v ={E2}=∗ Ψ v) ∧ (Φc -∗ |={E2' ∖ E1', ∅}_(k2 - k1)=> Ψc) -∗
  WPC e @ s2; k2; E2 ; E2' {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (?? HE HE') "H HΦ".
  iLöb as "IH" forall (e E1 E2 E1' E2' HE HE' Φ Ψ Φc Ψc).
  rewrite !wpc_unfold /wpc_pre.
  iSplit.
  - destruct (to_val e) as [v|] eqn:?.
    {
      iDestruct "HΦ" as "(HΦ&_)". iDestruct "H" as "(H&_)".
      iMod (fupd_intro_mask' _ E1) as "Hclo"; first by auto.
      iIntros.
      iMod ("H" with "[$]") as "(?&?)". iMod "Hclo" as "_".
      iMod ("HΦ" with "[$]"). iFrame. eauto.
    }
    iIntros (σ1 κ κs n) "Hσ HNC".
    iMod (fupd_intro_mask' E2 E1) as "Hclo"; first done.
    iDestruct "H" as "(H&_)".
    iMod ("H" with "[$] [$]") as "H".
    iModIntro.
    iApply (step_fupdN_le (S k1)); eauto.
    { lia. }
    iApply (step_fupdN_wand with "H"). iIntros "H".
    iDestruct "H" as "H". iMod "H" as "(%&H)".
    iModIntro.
    iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
    iMod ("H" with "[//]") as "H".
    iApply (step_fupdN_le (S k1)); eauto.
    { lia. }
    iApply (step_fupdN_wand with "H"). iModIntro. iIntros "H".
    iIntros "!>".
    iMod "H". iMod "H". iIntros "!>". iNext. iMod "H". iMod "Hclo" as "_". iModIntro.
    iApply (step_fupdN_le (S k1)); eauto.
    { lia. }
    iApply (step_fupdN_inner_wand with "H"); auto.
    iIntros "(Hσ & H & Hefs & HNC)". iFrame.
    iSplitR "Hefs".
    ** iApply ("IH" with "[] [] H [HΦ]"); auto.
    ** iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
       iIntros "H". eauto. iApply ("IH" with "[] [] H"); auto.
       { iSplit; first auto. iIntros. iApply step_fupdN_inner_later; auto; try set_solver+. }
  - iDestruct "H" as "(_&H)". iIntros "HC".
    iSpecialize ("H" with "[$]").
    iApply (step_fupdN_inner_wand with "H"); auto.
    { lia. }
    iIntros "H".
    iPoseProof (fupd_mask_frame_r _ _ (E2' ∖ E1') with "H") as "H"; first by set_solver+.
    rewrite -union_difference_L; auto.
    iMod "H". rewrite left_id_L.
    replace (S k2) with (S k1 + (k2 - k1)) by lia.
    iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver.
    rewrite Nat_iter_add. iEval (rewrite step_fupdN_S_fupd). iModIntro.
    iApply (step_fupdN_wand with "H"). iIntros "H".
    iMod "H".
    iDestruct "HΦ" as "(_&HΦ)".
    iMod "Hclo".
    iEval (rewrite -step_fupdN_inner_fupd).
    iMod ("HΦ" with "[$]") as "HΦ".
    iApply (step_fupdN_wand with "HΦ"). iModIntro; eauto.
Qed.

Lemma wpc_strong_mono' s1 s2 k1 k2 E1 E2 E1' E2' e Φ Ψ Φc Ψc :
  s1 ⊑ s2 → k1 ≤ k2 → E1 ⊆ E2 → E1' ⊆ E2' →
  WPC e @ s1; k1; E1 ; E1' {{ Φ }} {{ Φc }} -∗
  (∀ v, Φ v ={E2}=∗ Ψ v) ∧ (Φc ={E2' ∖ E1', ∅}=∗ Ψc) -∗
  WPC e @ s2; k2; E2 ; E2' {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (????) "? H".
  iApply (wpc_strong_mono with "[$] [-]"); auto.
  iSplit.
  - iDestruct "H" as "(H&_)". eauto.
  - iIntros. iDestruct "H" as "(_&H)".
    iMod ("H" with "[$]").
    iApply step_fupdN_inner_later; auto.
Qed.

Theorem wpc_crash_mono k stk E1 E2 e Φ Φc Φc' :
  (Φc' -∗ Φc) -∗
  WPC e @ stk; k; E1; E2 {{ Φ }} {{ Φc' }} -∗
  WPC e @ stk; k; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "Hweaken Hwpc".
  iApply (wpc_strong_mono' with "Hwpc"); eauto.
  iSplit; eauto.
  rewrite difference_diag_L.
  iIntros "Hc'".
  by iApply "Hweaken".
Qed.

Lemma wpc_strong_crash_frame s1 s2 k1 k2 E1 E2 e Φ Φc Ψc :
  s1 ⊑ s2 → k1 ≤ k2 → E1 ⊆ E2 →
  WPC e @ s1; k1; E1 ; ∅ {{ Φ }} {{ Φc }} -∗
  (C -∗ |={E2, E2}_(k2 - k1)=> Ψc) -∗
  WPC e @ s2; k2; E2 ; ∅ {{ Φ }} {{ Φc ∗ Ψc }}.
Proof.
  iIntros (?? HE) "H HΦ".
  iLöb as "IH" forall (e E1 E2 HE Φ Φc Ψc).
  rewrite !wpc_unfold /wpc_pre.
  iSplit.
  - destruct (to_val e) as [v|] eqn:?; eauto.
    {
      iDestruct "H" as "(H&_)".
      iMod (fupd_intro_mask' _ E1) as "Hclo"; first by auto.
      iIntros. iMod ("H" with "[$]"). iMod "Hclo" as "_".
      iModIntro; eauto.
    }
    iIntros (σ1 κ κs n) "Hσ HNC".
    iMod (fupd_intro_mask' E2 E1) as "Hclo"; first done.
    iDestruct "H" as "(H&_)".
    iMod ("H" with "[$] [$]") as "H".
    iModIntro.
    iApply (step_fupdN_le (S k1)); eauto.
    { lia. }
    iApply (step_fupdN_wand with "H"). iIntros "H".
    iDestruct "H" as "H". iMod "H" as "(%&H)".
    iModIntro.
    iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
    iMod ("H" with "[//]") as "H".
    iApply (step_fupdN_le (S k1)); eauto.
    { lia. }
    iApply (step_fupdN_wand with "H"). iModIntro. iIntros "H".
    iIntros "!>".
    iMod "H". iMod "H". iIntros "!>". iNext. iMod "H". iMod "Hclo" as "_". iModIntro.
    iApply (step_fupdN_le (S k1)); eauto.
    { lia. }
    iApply (step_fupdN_inner_wand with "H"); auto.
    iIntros "(Hσ & H & Hefs & HNC)". iFrame.
    iSplitR "Hefs".
    ** iApply ("IH" with "[] H [HΦ]"); auto.
    ** iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
       iIntros "H". eauto. iApply (wpc_strong_mono with "H"); eauto.
       iSplit; eauto. iIntros. iApply step_fupdN_inner_later; auto; try set_solver+.
  - iDestruct "H" as "(_&H)". iIntros "#HC".
    iSpecialize ("H" with "[$]").
    iSpecialize ("HΦ" with "[$]").
    replace (S k2) with (S k1 + (k2 - k1)) by lia.
    rewrite Nat_iter_add.
    iMod (fupd_intro_mask' _ E1) as "Hclo"; first by set_solver.
    iMod "H". iModIntro.
    iEval (rewrite step_fupdN_S_fupd).
    iApply (step_fupdN_wand with "H"). iIntros "H".
    iMod "H".
    iMod "Hclo".
    iApply (step_fupdN_inner_wand with "HΦ"); auto. iIntros "HΦ".
    iApply (step_fupdN_inner_wand with "H"); eauto; try lia.
    iIntros; by iFrame.
Qed.


Lemma wpc_frame_l s k E1 E2 e Φ Φc R :
  R ∗ WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; k; E1 ; E2 {{ v, R ∗ Φ v }} {{ R ∗ Φc }}.
Proof. iIntros "[? H]". iApply (wpc_strong_mono' with "H"); rewrite ?difference_diag_L; auto with iFrame. Qed.

Theorem wpc_frame (s : stuckness) (k : nat) (E1 E2 : coPset)
        (e: expr Λ) (Φ Φ': val Λ -> iProp Σ) (Φc Φc': iProp Σ) (R : iPropI Σ) :
    R -∗
    WPC e @ s; k; E1; E2 {{ v, Φ v }} {{Φc}} -∗
    (R ∗ Φc -∗ Φc') -∗
    (∀ v, R ∗ Φ v -∗ Φ' v) -∗
    WPC e @ s; k; E1; E2 {{ v, Φ' v }} {{Φc'}}.
Proof.
  iIntros "F Hwpc HΦc' HΦ'".
  iDestruct (wpc_frame_l with "[F $Hwpc]") as "Hwpc".
  { iExact "F". }
  iApply (wpc_strong_mono' with "Hwpc"); eauto.
  iSplit.
  - iIntros (v) "HΦ".
    iApply ("HΦ'" with "HΦ").
  - iIntros "HΦc".
    iApply fupd_mask_weaken; [ set_solver+ | ].
    iApply ("HΦc'" with "HΦc").
Qed.

Lemma wpc_fupd_crash_shift s k E1 E2 E2' e Φ Φc :
  E2 ## E2' →
  WPC e @ s; k ; E1 ; E2 {{ Φ }} {{ |={E2', ∅}=> Φc }} ⊢ WPC e @ s; k; E1 ; (E2 ∪ E2') {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "H".
  iApply (wpc_strong_mono' s s k k E1 E1 _ with "H []"); auto.
  - set_solver+.
  - iSplit; auto. iIntros "H".
    replace ((E2 ∪ E2') ∖ E2) with E2'; first done.
    set_solver.
Qed.

Lemma wpc_inv (N: namespace) s k E e Φ Φc :
  inv N Φc ∗ WPC e @ s ; k ; E; ∅ {{ Φ }} {{ True }} ⊢ WPC e @ s ; k ; E ; ↑N {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros "(#Hinv&H)".
  iApply (wpc_strong_mono' s s k k E E _ with "H"); try set_solver+.
  iSplit; auto.
  iIntros. iInv N as "H" "Hclo"; first by set_solver+.
  replace (↑N ∖ (∅: coPset) ∖ ↑N) with (∅: coPset) by set_solver.
  iModIntro; eauto.
Qed.

Lemma wp_wpc_inv (N: namespace) s E e Φ Φc :
  inv N Φc ∗ WP e @ s ; E {{ Φ }} ⊢ WPC e @ s ; 0 ; E ; ↑N {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros "(#Hinv&H)". iDestruct (wp_wpc with "H") as "H"; eauto. iApply wpc_inv; eauto.
Qed.

Lemma wpc_value s k E1 E2 Φ Φc v :
  (|={E1}=> Φ v) ∧ (|={E1}=> |={E2, ∅}=> Φc) ⊢ WPC of_val v @ s; k; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre to_of_val. iApply and_mono; auto.
  { iIntros.  iFrame. }
  iIntros "H". iIntros "HC".
  iMod "H". iApply step_fupdN_inner_later; auto.
  do 2 iNext.
  iMod "H".
  iMod (fupd_intro_mask' _ ∅) as "Hc"; first by set_solver+.
  iApply step_fupdN_inner_later; auto.
Qed.

Lemma wpc_value' s k E1 E2 Φ Φc v :
 Φ v ∧ Φc ⊢ WPC of_val v @ s; k; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". iApply wpc_value.
  iSplit.
  - iModIntro. iDestruct "H" as "($&_)".
  - iDestruct "H" as "(_&H)". iModIntro.
    iApply fupd_mask_weaken; first by set_solver+. iFrame.
Qed.

Lemma wpc_value_inv' s k E1 E2 Φ Φc v :
  WPC of_val v @ s; k; E1; E2 {{ Φ }} {{ Φc }} -∗ NC ={E1}=∗ Φ v ∗ NC.
Proof. rewrite wpc_unfold /wpc_pre to_of_val. iIntros "(?&_)"; auto. Qed.

Lemma wpc_value_inv_option s k E1 E2 Φ Φc e :
  WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }} -∗ NC ={E1}=∗ from_option Φ True (to_val e) ∗ NC.
Proof.
  iIntros. destruct (to_val e) as [v|] eqn:He; last by iFrame.
  apply of_to_val in He as <-. by iMod (wpc_value_inv' with "[$] [$]") as "($&$)".
Qed.

Lemma fupd_wpc s k E1 E2 e Φ Φc:
  (|={E1}=> WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}) ⊢ WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre. iIntros "H". iSplit.
  - destruct (to_val e) as [v|] eqn:?.
    {
      iMod (fupd_mask_mono with "H") as "($&_)"; first by set_solver+.
    }
    iIntros (σ1 κ κs n) "Hσ1".
    iMod (fupd_mask_mono with "H") as "(H&_)"; first by set_solver+.
    by iApply "H".
  - iMod (fupd_mask_mono with "H") as "(_&$)"; first by set_solver+.
Qed.

Lemma wpc_fupd s k E1 E2 e Φ Φc:
  ( WPC e @ s; k; E1 ; E2 {{ v, |={E1}=> Φ v }} {{ Φc }}) ⊢ WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof. iIntros "H". iApply (wpc_strong_mono' with "H"); rewrite ?difference_diag_L; auto. Qed.

Lemma wpc_crash s E1 E2 e k Φ Φc:
  WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }} -∗
  C -∗ |={E1, E1}_(S k)=> |={E2, ∅}_(S k)=> Φc.
Proof.
  iIntros "H".
  rewrite wpc_unfold /wpc_pre.
  iDestruct "H" as "(_&$)".
Qed.

(* XXX: the Atomic hypothesis could be weakened to
   Atomic (stuckness_to_atomicity s) but it seems to require
   moving the ⌜ reducible e1 σ1 ⌝ in the definition of wpc_pre to be
   before the conjunction that occurs closest there. *)
Lemma wpc_atomic s k E1 E2 e Φ Φc `{!Atomic StronglyAtomic e} :
  (|={E2, ∅}=> Φc) ∧ WP e @ s; E1 {{ v, (|={E1}=> Φ v) ∧ |={E2, ∅}=> Φc }} ⊢
  WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". rewrite !wpc_unfold !wp_unfold /wpc_pre /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { iSplit.
    - iDestruct "H" as "(_&H)". iIntros "HNC". iFrame.
      iMod (fupd_mask_mono with "H") as "($&_)"; first by set_solver+.
    - iDestruct "H" as "(H&_)".
      iIntros "HC". iApply step_fupdN_inner_later; auto. do 2 iNext.
      iMod "H".
      iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
      iModIntro. iApply step_fupdN_later; eauto.
  }
  iSplit.
  {
    iIntros (σ1 κ κs n) "Hσ HNC".
    iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
    iModIntro. iApply step_fupdN_later; first auto.
    iNext. iNext.
    iMod "Hclo".
    iDestruct "H" as "(_&H)".
    iSpecialize ("H" $! σ1 with "Hσ").
    iMod "H" as "[$ H]".
    iModIntro. iIntros (e2 σ2 efs Hstep).
    iModIntro. iApply step_fupdN_later; first auto.
    do 3 iModIntro.
    iMod ("H" with "[//]") as "H". iIntros "!>!>".
    iMod "H" as "(Hσ & H & Hefs)".
    iModIntro.
    iApply step_fupdN_inner_later; first by set_solver+.
    do 2 iNext.
    * rewrite wpc_unfold wp_unfold /wpc_pre /wp_pre.
      destruct (to_val e2) as [v2|] eqn:He2.
      ** iFrame "Hσ". iSplitL "H".
         { iSplit.
           * iIntros. iMod "H" as "(?&_)". iFrame.
           * iIntros. iMod "H" as "(_&H)". iApply step_fupdN_inner_later; auto.
             do 2 iNext.
             iMod (fupd_intro_mask' _ ∅) as "Hclo'"; first by set_solver+.
             iModIntro. iApply step_fupdN_later; eauto.
             do 2 iNext. iMod "Hclo'". eauto.
         }
         iFrame.
         iApply big_sepL_mono; last eauto. iIntros. by iApply wp_wpc.
      ** edestruct (atomic _ _ _ _ _ Hstep); congruence.
  }
  iDestruct "H" as "(H&_)".
  iIntros "HC".
  iApply step_fupdN_inner_later; auto. do 2 iNext.
  iMod "H".
  iMod (fupd_intro_mask' _ ∅) as "Hclo'"; first by set_solver+.
  iModIntro. iApply step_fupdN_later; auto.
Qed.

(* note that this also reverses the postcondition and crash condition, so we
prove the crash condition first *)
Lemma wpc_atomic_no_mask s k E1 E2 e Φ Φc `{!Atomic StronglyAtomic e} :
  Φc ∧ WP e @ s; E1 {{ v, (|={E2}=> Φc) ∧ (|={E1}=> Φ v) }} ⊢
  WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "Hc_wp".
  iApply wpc_atomic.
  iSplit.
  - iApply fupd_mask_weaken; [ set_solver+ | ].
    iDestruct "Hc_wp" as "[$ _]".
  - iDestruct "Hc_wp" as "[_ Hwp]".
    iApply wp_mono; iFrame.
    iIntros (x) "HΦ".
    iSplit.
    + iDestruct "HΦ" as "[_ >HΦc]".
      iApply fupd_mask_weaken; [ set_solver+ | ]; iFrame.
    + iDestruct "HΦ" as "[>HΦ _]".
      iApply fupd_mask_weaken; [ set_solver+ | ]; iFrame.
Qed.

(* written to match the premise of wpc_bind *)
Lemma wpc_atomic_from_bind K `{!LanguageCtx K} s k E1 E2 e Φ Φc `{!Atomic StronglyAtomic e} :
  Φc ∧ WP e @ s; E1 {{ v, (|={E1}=> WPC K (of_val v) @ s; k; E1; E2 {{ Φ }} {{ Φc }}) }} ⊢
  WPC e @ s; k; E1 ; E2 {{ v, WPC K (of_val v) @ s; k; E1; E2 {{ Φ }} {{ Φc }} }} {{ Φc }}.
Proof.
  iIntros "Hwp".
  iApply wpc_atomic_no_mask.
  iSplit.
  - iDestruct "Hwp" as "[$ _]".
  - iDestruct "Hwp" as "[_ Hwp]".
Admitted.

Lemma wpc_bind K `{!LanguageCtx K} s k E1 E2 e Φ Φc :
  WPC e @ s; k; E1 ; E2 {{ v, WPC K (of_val v) @ s; k; E1; E2 {{ Φ }} {{ Φc }} }} {{ Φc }}
                     ⊢ WPC K e @ s; k; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E1 E2 e Φ). rewrite wpc_unfold /wpc_pre.
  destruct (to_val e) as [v|] eqn:He.
  { rewrite !wpc_unfold /wpc_pre //.
    apply of_to_val in He as <-.
    destruct (to_val (K (of_val v))).
    - iSplit.
      * iDestruct "H" as "(H&_)". iIntros.
        iMod ("H" with "[$]") as "((H&_)&HNC)". iMod ("H" with "[$]"). eauto.
      * iDestruct "H" as "(_&$)".
    - iSplit.
      * iDestruct "H" as "(H&_)". iIntros.
        iMod ("H" with "[$]") as "((H&_)&?)".
        iMod ("H" with "[$] [$]") as "$". eauto.
      * iDestruct "H" as "(_&$)".
  }
  rewrite wpc_unfold /wpc_pre fill_not_val //.
  iSplit; last by (iDestruct "H" as "(_&$)").
  iDestruct "H" as "(H&_)".
  iIntros (σ1 κ κs n) "Hσ HNC". iMod ("H" with "[$] [$]") as "H".
  iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H".
  iMod "H" as "[% H]". iModIntro; iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iSpecialize ("H" $! e2' σ2 efs with "[//]").
  iApply (step_fupdN_inner_wand with "H"); try auto.
  iIntros "H".
  iMod "H". iModIntro. iNext. iMod "H". iModIntro.
  iMod "H". iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros "H". iMod "H" as "(Hσ&H&Hefs)".
  iFrame "Hσ Hefs". by iApply "IH".
Qed.

Lemma wpc_bind_inv K `{!LanguageCtx K} s k E1 E2 e Φ Φc :
  WPC K e @ s; k; E1; E2 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; k; E1 ; E2 {{ v, WPC K (of_val v) @ s; k; E1; E2 {{ Φ }} {{ Φc }} }} {{Φc }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E1 E2 e Φ Φc). rewrite !wpc_unfold /wpc_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He. rewrite <-He. rewrite !wpc_unfold /wpc_pre. iSplit.
    - iIntros. iModIntro. iFrame.
    - iDestruct "H" as "(_&$)".
  }
  rewrite fill_not_val //.
  iSplit.
  - iDestruct "H" as "(H&_)".
    iIntros (σ1 κ κs n) "Hσ HNC". iMod ("H" with "[$] [$]") as "H". iModIntro.
    iApply (step_fupdN_wand with "H"). iIntros "H".
    iMod "H". iModIntro. iDestruct "H" as "[% H]".
    iSplit.
    { destruct s; eauto using reducible_fill. }
    iIntros (e2 σ2 efs Hstep).
    iMod ("H" $! (K e2) σ2 efs with "[]") as "H"; [by eauto using fill_step|].
    iModIntro. iApply (step_fupdN_wand with "H"). iIntros "H".
    iMod "H". iModIntro.
    iMod "H". do 2 iModIntro.
    iMod "H". iModIntro.
    iApply (step_fupdN_inner_wand with "H"); auto.
    iIntros "(Hσ & H & Hefs)".
    iFrame "Hσ Hefs". by iApply "IH".
  -iDestruct "H" as "(_&H)". eauto.
Qed.

Lemma wpc_lift_step_fupd s k E E' Φ Φc e1 :
  to_val e1 = None →
  ((∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E,∅}=∗
    (⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,∅,E}▷=∗
      (state_interp σ2 κs (length efs + n) ∗
       WPC e2 @ s; k; E; E' {{ Φ }} {{ Φc }} ∗
       [∗ list] ef ∈ efs, WPC ef @ s; k; ⊤; ∅ {{ fork_post }} {{ True }})))
  ∧ |={E}=> ▷ |={E', ∅}=> Φc)%I
 ⊢ WPC e1 @ s; k; E; E' {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre=>->. iIntros "H".
  iSplit; last first.
  { iIntros. iDestruct "H" as "(_&H)".
    iMod "H".
    iApply step_fupdN_inner_later; auto; do 2 iNext.
    iMod "H".
    iModIntro. iApply step_fupdN_later; auto.
  }
  iDestruct "H" as "(H&_)". iIntros (σ1 κ κs n) "Hσ HNC".
  iMod ("H" with "Hσ") as "H". iModIntro.
  iApply step_fupdN_later; first auto. do 2 iNext.
  iModIntro; iDestruct "H" as "($&H)".
  iIntros.
  iApply step_fupdN_later; first auto.
  iMod ("H" with "[//]") as "H". iModIntro.
  do 5 iModIntro.
  iMod "H". iApply step_fupdN_inner_later; first auto.
  iModIntro. do 2 iNext. iFrame. eauto.
Qed.

Lemma wpc_lift_step s k E1 E2 Φ Φc e1 :
  to_val e1 = None →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E1,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E1}=∗
      state_interp σ2 κs (length efs + n) ∗
      WPC e2 @ s; k; E1; E2 {{ Φ }} {{ Φc }} ∗
      [∗ list] ef ∈ efs, WPC ef @ s; k; ⊤; ∅ {{ fork_post }} {{ True }})
  ∧ ▷ Φc
  ⊢ WPC e1 @ s; k; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "H". iApply wpc_lift_step_fupd; [done|].
  iSplit; last first.
  { iDestruct "H" as "(_&H)". iModIntro. iApply fupd_mask_weaken; auto. set_solver+. }
  iIntros (????) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]".
  iIntros "!> * % !> !>". by iApply "H".
Qed.

Lemma wpc_lift_pure_step_no_fork `{!Inhabited (state Λ)} s k E1 E1' E2 Φ Φc e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={E1,E1'}▷=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → WPC e2 @ s; k; E1; E2 {{ Φ }} {{ Φc }}) ∧ ▷ Φc
  ⊢ WPC e1 @ s; k; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wpc_lift_step.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iSplit; last by (iDestruct "H" as "(_&$)").
  iDestruct "H" as "(H&_)".
  iIntros (σ1 κ κs n) "Hσ". iMod "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first by set_solver. iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 efs ?).
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iMod "Hclose" as "_". iMod "H". iModIntro.
  iDestruct ("H" with "[//]") as "H". simpl. iFrame.
Qed.

Lemma wpc_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s k E1 E1' E2 Φ Φc} e1 e2 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E1,E1'}▷=> WPC e2 @ s; k; E1; E2 {{ Φ }} {{ Φc }}) ∧ ▷ Φc
  ⊢ WPC e1 @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wpc_lift_pure_step_no_fork s k E1 E1' E2); try done.
  { naive_solver. }
  iSplit; last by (iDestruct "H" as "(_&$)").
  iDestruct "H" as "(H&_)".
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.

(* Note: compared to wp_pure_step_fupd, we have n = 1 *)
Lemma wpc_pure_step_fupd `{!Inhabited (state Λ)} s k E1 E2 e1 e2 φ Φ Φc :
  PureExec φ 1 e1 e2 →
  φ →
  (|={E1,E1}▷=>^1 WPC e2 @ s; k; E1; E2 {{ Φ }} {{ Φc }}) ∧ ▷ Φc
  ⊢ WPC e1 @ s; k; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  inversion Hexec as [|? e1' e2' e3' [Hsafe ?] Hrest]. subst.
  inversion Hrest; subst.
  iApply wpc_lift_pure_det_step_no_fork; last eauto.
  - intros σ. specialize (Hsafe σ). destruct s;
    eauto using reducible_not_val, reducible_no_obs_reducible.
  - done.
Qed.

Lemma wpc_pure_step_later `{!Inhabited (state Λ)} s k E1 E2 e1 e2 φ Φ Φc :
  PureExec φ 1 e1 e2 →
  φ →
  ▷^1 WPC e2 @ s; k; E1 ; E2 {{ Φ }} {{ Φc }} ∧ ▷^1 Φc
  ⊢ WPC e1 @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  intros Hexec ?. rewrite -wpc_pure_step_fupd //. clear Hexec.
  rewrite //= -step_fupd_intro //.
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
Lemma wpc_mono s k E1 E2 e Φ Ψ Φc Ψc :
  (∀ v, Φ v ⊢ Ψ v) → (Φc ⊢ Ψc) → WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; k; E1; E2 {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (HΦ HΦc) "H"; iApply (wpc_strong_mono' with "H"); auto.
  iSplit.
  - iIntros (v) "?". by iApply HΦ.
  - iIntros "?". iMod (fupd_intro_mask' _ ∅); first by set_solver+. by iApply HΦc.
Qed.

Lemma wpc_mono' s k E1 E2 e Φ Ψ Φc Ψc :
  (∀ v, Φ v -∗ Ψ v) -∗ (Φc -∗ Ψc) -∗ WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }} -∗
  WPC e @ s; k; E1; E2 {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros "H1 H2 H3"; iApply (wpc_strong_mono' with "H3"); auto.
  iSplit.
  - iIntros (v) "?". by iApply "H1".
  - iIntros "?". iMod (fupd_intro_mask' _ ∅); first by set_solver+. by iApply "H2".
Qed.

Lemma wp_wpc_frame' s E1 E2 e Φ Φc Φc' k:
  Φc' ∗
  □ (Φc' -∗ Φc) ∗
  WP e @ s ; E1 {{ λ v, Φc' -∗ Φ v }} ⊢ WPC e @ s ; k ; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "(HΦc&#HΦc_imp&Hwp)".
  iApply (wpc_strong_mono' s s k k E1 E1 E2 E2 _ (λ v, Φc' ∗ (Φc' -∗ Φ v))%I _ (Φc' ∗ True)%I
         with "[-]"); auto.
  { iApply wpc_frame_l; iFrame.
    iApply wp_wpc; eauto. }
  iSplit.
  - iIntros (?). rewrite wand_elim_r. iIntros; eauto.
  - iIntros "(H&?)". iApply (fupd_mask_weaken); eauto. set_solver+.
    iApply "HΦc_imp". eauto.
Qed.

Lemma wp_wpc_frame s E1 E2 e Φ Φc k:
  Φc ∗ WP e @ s ; E1 {{ λ v, Φc -∗ Φ v }} ⊢ WPC e @ s ; k ; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "(HΦc&Hwp)".
  iApply wp_wpc_frame'.
  iFrame. eauto.
Qed.

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
Lemma wp_frame_wand_l s E e Q Φ :
  Q ∗ WP e @ s; E {{ v, Q -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
*)

End wpc.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisG Λ Σ, !crashG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wpc p s k E1 E2 e R Φ Ψ Φc Ψc :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
     Frame p R Φc Ψc →
    Frame p R (WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }}) (WPC e @ s; k; E1; E2 {{ Ψ }} {{ Ψc }}).
  Proof. rewrite /Frame=> HR HRc. rewrite wpc_frame_l. apply wpc_mono; [ apply HR | apply HRc ]. Qed.

  Global Instance is_except_0_wpc s k E1 E2 e Φ Φc : IsExcept0 (WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wpc -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wpc p s k E1 E2 e P Φ Φc:
    ElimModal True p false (|==> P) P (WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }}) (WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_wpc.
  Qed.

  Global Instance elim_modal_fupd_wpc p s k E1 E2 e P Φ Φc :
    ElimModal True p false (|={E1}=> P) P (WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }})
              (WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wpc.
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
