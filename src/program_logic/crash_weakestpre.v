From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant.
Set Default Proof Using "Type".
Import uPred.

(* Define a weakestpre with an explicit crash invariant (i.e. there is a postcondition and a crash condition *)

Definition wpc_pre `{!irisG Λ Σ} (s : stuckness) (k: nat)
    (wpc : coPset -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ) :
    coPset -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ := λ E1 E2 e1 Φ Φc,
  (match to_val e1 with
   | Some v => |={E1}=> Φ v
   | None => ∀ σ1 κ κs n,
      state_interp σ1 (κ ++ κs) n ={E1,∅}=∗ (|={∅, ∅}▷=>^(S k)
        ((⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
        ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,∅,E1}▷=∗ |={E1, ∅}=> |={∅, ∅}▷=>^(S k) |={∅, E1}=>
          (state_interp σ2 κs (length efs + n) ∗
          wpc E1 E2 e2 Φ Φc ∗
          [∗ list] i ↦ ef ∈ efs, wpc ⊤ ∅ ef fork_post True))
           ∧ |={∅}=> Φc ∗ |={∅, E2}=> state_interp σ1 (κ ++ κs) n))
   end ∧
   match to_val e1 with
   | Some v => |={E1, E2}=> Φc
   | None => |={E1, ∅}=> |={∅, ∅}▷=>^(S k) |={∅, ∅}=> Φc ∗ |={∅, E2}=> emp
   end)%I.

Local Instance wpc_pre_contractive `{!irisG Λ Σ} s k : Contractive (wpc_pre s k).
Proof.
Admitted.
(*
  rewrite /wpc_pre=> n wp wp' Hwp E1 E2 e1 Φ Φc.
  do 10 (f_contractive || f_equiv).
  do 2 (f_contractive || f_equiv).
  induction (S k).
  - rewrite //=.
    repeat (f_contractive || f_equiv); apply Hwp.
  - simpl. rewrite IHn0. eauto.
Qed.
*)

Definition wpc_def `{!irisG Λ Σ} (s : stuckness) (k: nat) :
  coPset → coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ → iProp Σ := fixpoint (wpc_pre s k).
Definition wpc_aux `{!irisG Λ Σ} : seal (@wpc_def Λ Σ _). by eexists. Qed.


(* Notation: copied from iris bi/weakestpre.v *)
Class Wpc (Λ : language) (PROP A B : Type) :=
  wpc : A → B → coPset → coPset → expr Λ → (val Λ → PROP) → PROP → PROP.
Arguments wpc {_ _ _ _ _} _ _ _ _ _%E _%I _%I.
Instance: Params (@wpc) 11 := {}.

Instance wpc' `{!irisG Λ Σ} : Wpc Λ (iProp Σ) stuckness nat := wpc_aux.(unseal).
Definition wpc_eq `{!irisG Λ Σ} : wpc = @wpc_def Λ Σ _ := wpc_aux.(seal_eq).

(** Notations for partial crash weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WPC' e @ s ; k ; E1 ; E2 {{ Φ } } {{ Φc } }" := (wpc s k E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e @ k ; E1 ; E2 {{ Φ } } {{ Φc } }" := (wpc NotStuck k E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
(*
Notation "'WPC' e @ E1 ; E2 ? {{ Φ } } {{ Φc } }" := (wpc MaybeStuck E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
*)
Notation "'WPC' e @ k {{ Φ } } {{ Φc } }" := (wpc NotStuck k ⊤ ∅ e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
(*
Notation "'WPC' e ? {{ Φ } } {{ Φc } }" := (wpc MaybeStuck ⊤ ∅ e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
*)

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'WPC' e @ s ; k ; E1 ; E2 {{ v , Q } } {{ R } }" := (wpc s k E1 E2 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[' 'WPC'  e  '/' '[          ' @  s ;  k ;  E1 ;  E2  {{  v ,  Q  } }  {{ R } } ']' ']'") : bi_scope.
Notation "'WPC' e @ k ; E1 ; E2 {{ v , Q } } {{ R } }" := (wpc NotStuck k E1 E2 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[' 'WPC'  e  '/' '[       ' @  k ;  E1 ; E2  {{  v ,  Q  } } {{ R } } ']' ']'") : bi_scope.
Notation "'WPC' e @ E1 ; E2 ? {{ v , Q } } {{ R } }" := (wpc MaybeStuck E1 E2 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[' 'WPC'  e  '/' '[        ' @  E1 ; E2  ? {{  v ,  Q  } } {{ R } } ']' ']'") : bi_scope.

Section wpc.
Context `{!irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpc_unfold s k E1 E2 e Φ Φc :
  WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }} ⊣⊢ wpc_pre s k (wpc (PROP:=iProp Σ) s k) E1 E2 e Φ Φc.
Proof. rewrite wpc_eq. apply (fixpoint_unfold (wpc_pre s k)). Qed.

(* XXX : there should be a proper instance for Nat. iter *)
Global Instance wpc_ne s k E1 E2 e n :
  Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) (wpc (PROP:=iProp Σ) s k E1 E2 e).
Proof.
Admitted.
(*
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ Φc Ψc HΦc.
  rewrite !wpc_unfold /wpc_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  (*
  (f_contractive || f_equiv); last first.
  (f_contractive || f_equiv); last first.
  { repeat (f_contractive || f_equiv). auto. }
   *)
  (f_contractive || f_equiv); last first.
  { repeat (f_contractive || f_equiv). auto. }
  do 11 (f_contractive || f_equiv); auto.
  - remember (S k) as k' eqn:Heq.
    clear Heq.
    induction k'.
    {
    do 11 (f_contractive || f_equiv); auto.
    apply IH; first lia.
    * intros v. eapply dist_le; eauto with lia.
    * eapply dist_le; eauto with lia.
    }
    simpl. do 3 f_equiv; eauto.
Qed.
*)

Global Instance wpc_proper s k E1 E2 e :
  Proper (pointwise_relation _ (≡) ==> (≡) ==> (≡)) (wpc (PROP:=iProp Σ) s k E1 E2 e).
Proof.
  intros Φ Φ' ? Φc Φc' ?.
  apply equiv_dist=>n. apply wpc_ne; auto.
  by intros v; apply equiv_dist.
Qed.

(*
Lemma wp_wpc s E1 E2 e Φ :
  E2 ⊆ E1 →
  WP e @ s ; E1 {{ Φ }} ⊢ WPC e @ s ; O ; E1 ; E2 {{ Φ }} {{ True }}.
Proof.
  iIntros (Hsub) "H". iLöb as "IH" forall (E1 E2 e Φ Hsub).
  rewrite wp_unfold wpc_unfold /wp_pre /wpc_pre. destruct (to_val e) as [v|]=>//.
  - iMod "H". iModIntro.
    iSplit; auto. iIntros. iFrame. iMod (fupd_intro_mask' _ E2); auto.
    iApply fupd_intro_mask; auto; set_solver+.
  - iIntros (σ1 κ κs n) "Hσ".
    iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
    iModIntro. iSplit.
    * iMod "Hclo". iMod ("H" with "Hσ") as "[% H]". iIntros "!> !> !>".
      iSplitR.
      { destruct s; last done. eauto using reducible_no_obs_reducible. }
      iIntros (e2 σ2 efs) "Hstep". iMod ("H" with "Hstep") as "H".
      iModIntro. iNext. iMod ("H") as "(Hσ & H & Hfork)". iFrame. iModIntro.
      iSplitL "H".
      { by iApply "IH". }
      iApply (@big_sepL_impl with "Hfork").
      iIntros "!#" (k ef _) "H". by iApply "IH".
    *  iFrame. iIntros. iFrame. iModIntro. iMod "Hclo". iApply (fupd_mask_weaken _ E2); auto.
Qed.
*)

Lemma step_fupdN_le {PROP : sbi} {H : BiFUpd PROP} {E1 E2 : coPset} (n1 n2 : nat) (P: PROP):
  E2 ⊆ E1 →
  n1 ≤ n2 → (|={E1,E2}▷=>^n1 P) -∗ |={E1,E2}▷=>^n2 P.
Proof.
  intros ?. induction 1 => //=.
  iIntros. iApply step_fupd_intro; auto. iNext. by iApply IHle.
Qed.

Lemma wpc_strong_mono s1 s2 k1 k2 E1 E2 E1' E2' e Φ Ψ Φc Ψc :
  s1 ⊑ s2 → k1 ≤ k2 → E1 ⊆ E2 → E2' ⊆ E1' → E2' ⊆ E2 →
  WPC e @ s1; k1; E1 ; E1' {{ Φ }} {{ Φc }} -∗
  (∀ v, Φ v ={E2}=∗ Ψ v) ∧ (Φc ={E1', E2'}=∗ Ψc) -∗
  WPC e @ s2; k2; E2 ; E2' {{ Ψ }} {{ Ψc }}.
Proof.
  Admitted.
(*
  iIntros (?? HE HE' HE2) "H HΦ". iLöb as "IH" forall (e E1 E2 E1' E2' HE HE' HE2 Φ Ψ Φc Ψc).
  rewrite !wpc_unfold /wpc_pre.
  destruct (to_val e) as [v|] eqn:?.
  {
    iMod (fupd_intro_mask' _ E1) as "Hclo"; first by auto.
    iMod "H" as "H". iMod "Hclo" as "_". 
    iModIntro. iSplit.
    * iDestruct "HΦ" as "(HΦ&_)". iDestruct "H" as "(H&_)".
      iMod (fupd_intro_mask' _ E1) as "Hclo"; first by auto.
      iMod "H". iMod "Hclo" as "_". 
      iMod ("HΦ" with "[$]"). eauto.
    * iIntros. iDestruct "H" as "(_&H)".
      iMod (fupd_intro_mask' _ E1) as "Hclo"; first by auto.
      iMod ("H" with "[$]") as "(?&$&Hclo')".
      iMod "Hclo'". iDestruct "HΦ" as "(_&HΦ)".
      iMod ("HΦ" with "[$]"). iFrame.
      iApply fupd_intro_mask; auto; set_solver+.
  }
  iIntros (σ1 κ κs n) "Hσ". iMod (fupd_intro_mask' E2 E1) as "Hclo"; first done.
  iMod ("H" with "[$]") as "H".
  iModIntro. iSplit.
  - iDestruct "H" as "(H&_)".
    iApply (step_fupdN_le (S k1)); eauto.
    { lia. }
    iApply (step_fupdN_wand with "H"); iIntros "(%&H)".
    iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!> !>".
    iMod "H" as "(Hσ & H & Hefs)".
    iMod "Hclo" as "_". iModIntro. iFrame "Hσ". iSplitR "Hefs".
    * iApply ("IH" with "[] [] [] H [HΦ]"); auto.
    * iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
      iIntros "H". eauto. iApply ("IH" with "[] [] [] H"); auto.
  - iDestruct "H" as "(_&H)". 
    iMod "H" as "(HΦc&$&Hclo')".
    iDestruct "HΦ" as "(_&HΦ)".
    iMod "Hclo'" as "_". iMod ("HΦ"  with "[$]") as "$".
    iApply fupd_intro_mask; auto; set_solver+.
Qed.
*)

Lemma wpc_frame_l s k E1 E2 e Φ Φc R :
  E2 ⊆ E1 →
  R ∗ WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; k; E1 ; E2 {{ v, R ∗ Φ v }} {{ R ∗ Φc }}.
Proof. iIntros (?) "[? H]". iApply (wpc_strong_mono with "H"); auto with iFrame. Qed.

Lemma wpc_fupd_open s k E1 E2 E2' e Φ Φc :
  E2 ⊆ E1 →
  E2 ⊆ E2' →
  WPC e @ s; k ; E1 ; E2' {{ Φ }} {{ |={E2', E2}=> Φc }} ⊢ WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof. iIntros (??) "H". iApply (wpc_strong_mono s s k k E1 E1 E2' with "H []"); auto. Qed.

(** XXX: this could be strengthened by being more careful about the masks **)
Lemma wpc_inv (N: namespace) s k E e Φ Φc :
  ↑N ⊆ E →
  inv N Φc ∗ WPC e @ s ; k ; E; ↑N {{ Φ }} {{ True }} ⊢ WPC e @ s ; k ; E ; ∅ {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros (?) "(#Hinv&H)".
  iApply (wpc_strong_mono s s k k E E (↑N) with "H"); try set_solver+.
  iSplit; auto.
  iIntros. iInv N as "Hfoo" "Hclo".
  iApply fupd_mask_weaken; first by set_solver+. done.
Qed.

(*
Lemma wp_wpc_inv (N: namespace) s E e Φ Φc :
  ↑N ⊆ E →
  inv N Φc ∗ WP e @ s ; E {{ Φ }} ⊢ WPC e @ s ; 0 ; E ; ∅ {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros (?) "(#Hinv&H)". iDestruct (wp_wpc with "H") as "H"; eauto. iApply wpc_inv; eauto.
Qed.
*)

(*
Lemma wpc_value s E1 E2 Φ Φc v : (|={E1}=> Φ v) ∧ (|={⊤, E2}=> Φc) ⊢ WPC of_val v @ s; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre to_of_val. iApply and_mono; auto.
  iIntros "H". iIntros. iMod "H". by iFrame.
Qed.

Lemma wpc_value' s E1 E2 Φ Φc v : Φ v ∧ Φc ⊢ WPC of_val v @ s; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre to_of_val. iApply and_mono; auto.
  iIntros. iApply fupd_mask_weaken; first by auto. iFrame.
Qed.

Lemma wpc_value_inv' s E1 E2 Φ Φc v : WPC of_val v @ s; E1; E2 {{ Φ }} {{ Φc }} ={E1}=∗ Φ v.
Proof. rewrite wpc_unfold /wpc_pre to_of_val. iIntros "(?&_)"; auto. Qed.
*)

Lemma fupd_wpc s k E1 E2 e Φ Φc:
  (|={E1}=> WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}) ⊢ WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre. iIntros "H". iSplit.
  - destruct (to_val e) as [v|] eqn:?.
    { by iMod "H" as "(?&_)". }
    iIntros (σ1 κ κs n) "Hσ1". iMod "H". iDestruct "H" as "(H&_)". by iApply "H".
  - destruct (to_val e) as [v|] eqn:?.
    { by iMod "H" as "(_&H)". }
    iMod "H". iDestruct "H" as "(_&H)". by iApply "H".
Qed.

Lemma wpc_fupd s k E1 E2 e Φ Φc:
  E2 ⊆ E1 →
  ( WPC e @ s; k; E1 ; E2 {{ v, |={E1}=> Φ v }} {{ Φc }}) ⊢ WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof. iIntros (?) "H". iApply (wpc_strong_mono with "H"); auto. Qed.

Axiom Tok: iProp Σ.
Axiom Tok_Tok : Tok ∗ Tok -∗ False.
Instance timeless_Tok: Timeless (Tok).
Admitted.

Context `{!stagedG Σ}.

Definition detached_staged k E1 E2 P : iProp Σ :=
  (|={E1, ∅}=> |={∅, ∅}▷=>^k |={∅, E2}=> P)%I.

Definition detached_ci k E1 E2 N (P: iProp Σ) : iProp Σ :=
  P ∨ (∃ γ, Tok ∗ staged_inv N γ (detached_staged k E1 E2 P))%I.

Lemma step_fupdN_later E1 E2 k P:
  E2 ⊆ E1 →
  ▷^k P -∗ |={E1,E2}▷=>^k P.
Proof.
  iIntros (Hle).
  iInduction k as [| k] "IH".
  - eauto.
  - iIntros. rewrite Nat_iter_S. iMod (fupd_intro_mask' _ E2) as "Hclo".
    { set_solver. }
    iModIntro. iModIntro. iMod "Hclo". by iApply "IH".
Qed.

Lemma step_fupdN_inner_later E1 E2 k P:
  E2 ⊆ E1 →
  ▷^k P -∗ |={E1,∅}=> |={∅,∅}▷=>^k |={∅,E2}=> P.
Proof.
  iIntros (Hle).
  iInduction k as [| k] "IH".
  - rewrite //=. iIntros "HP".
    iMod (fupd_intro_mask' _ E2); eauto.
    iApply fupd_intro_mask; eauto; set_solver.
  - iIntros. iMod (fupd_intro_mask' _ ∅) as "Hclo".
    { set_solver. }
    rewrite Nat_iter_S.
    iModIntro. iModIntro. iNext. iMod "Hclo". by iApply "IH".
Qed.

Lemma step_fupdN_inner_plus E1 E2 k1 k2 P:
  (|={E1,∅}=> |={∅,∅}▷=>^k1 |={∅, E1}=> |={E1,∅}=> |={∅,∅}▷=>^k2 |={∅,E2}=> P)
  ⊢ (|={E1,∅}=> |={∅,∅}▷=>^(k1 + k2) |={∅,E2}=> P)%I.
Proof.
  rewrite Nat_iter_add.
  iIntros "H". iMod "H". iModIntro.
  iApply (step_fupdN_mono with "H"). iIntros "H".
  destruct k2.
  * simpl. do 3 iMod "H". eauto.
  * rewrite Nat_iter_S. iMod "H". iMod "H". eauto.
Qed.

Lemma wpc_crash s E1 E2 e k Φ Φc:
  WPC e @ s; k; E1 ; E2 {{ Φ }} {{ Φc }} -∗
  |={E1, ∅}=> |={∅, ∅}▷=>^(S k) |={∅, ∅}=> Φc ∗ |={∅, E2}=> emp.
Proof.
  iIntros "H".
  rewrite wpc_unfold /wpc_pre.
  iDestruct "H" as "(_&H)".
  destruct (to_val e) as [v|].
  - iMod "H". iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
    iModIntro. iApply step_fupdN_inner_later; auto. iModIntro. do 2 iNext.
    iFrame.
  - eauto.
Qed.

Lemma wpc_staged_invariant_aux s k E1 E2 E1' E2' e Φ Φc P Q1 R1 Q2 R2 N1 N2 γ :
  ↑N1 ⊆ E1 →
  ↑N2 ⊆ E1 →
  (E2' ⊆ E1') →
  (E1 ⊆ E1') →
  (E2' ⊆ E2) →
  N1 ## N2 →
  inv N1 (detached_ci (2 * S (S (S k))) E1' E2' N2 P) ∗
  □ (Q1 -∗ R1) ∗
  □ (Q2 -∗ R2) ∗
  staged_inv N2 γ (detached_staged (2 * (S (S (S k)))) E1' E2' P) ∗
  staged_value N2 γ (|={E1 ∖ ↑N1 ∖ ↑N2, ∅}=> |={∅, ∅}▷=>^(S k)
                     |={∅, E1 ∖ ↑N1 ∖ ↑N2}=>
                     Q1 ∗ WPC e @ k; E1 ∖ ↑N1 ∖ ↑N2;E2 {{ v, (Φ v ∧ |={E1,E2}=> Φc) ∗ P }}{{Φc ∗ P}} ∗ Q2) ⊢
  |={E1, ∅}=> |={∅, ∅}▷=>^(S (S (S k))) |={∅, E1}=> R1 ∗ WPC e @ s; S (S k); E1; E2 {{ v, Φ v }} {{Φc}} ∗ R2.
Proof.
  iIntros (????? Hdisj) "(#Hinv&#HQR1&#HQR2&#Hsi&Hwp)".
  iLöb as "IH" forall (Q1 Q2 R1 R2 e) "HQR1 HQR2".
  destruct (to_val e) as [v|] eqn:Hval.
  {
    rewrite Nat_iter_S.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
    iModIntro. rewrite Nat_iter_S. iModIntro. iNext. iModIntro.
    rewrite Nat_iter_S.
    iModIntro. iNext.
    iMod "Hclo" as "_".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo"; first by set_solver+.
    iMod "H". iModIntro.
    rewrite Nat_iter_S. iMod "H".  iModIntro. iNext. iMod "H". iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iMod "H".
    rewrite wpc_unfold /wpc_pre.
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(HQ1&(H&_)&HQ2)".
    iMod "H" as "(HΦ&HP)".
    iMod "Hclo".
    iMod ("Hclo'" with "[HP]").
    { iSplitL. iApply "HP". iAlways.
      iIntros. rewrite /detached_staged.
      iApply step_fupdN_inner_later; first auto.
      iNext. eauto.
    }
    iModIntro.
    iSplitL "HQ1".
    { by iApply "HQR1". }
    iSplitR "HQ2"; last first.
    { by iApply "HQR2". }
    iSplit.
    - by iDestruct "HΦ" as "($&_)".
    - by iDestruct "HΦ" as "(_&$)".
  }
  rewrite (Nat_iter_S ((S (S k)))).
  iMod (staged_inv_open with "[$]") as "(H&Hclo')".
  { set_solver. }
  iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
  rewrite (Nat_iter_S (S k)).
  iModIntro. iModIntro. iNext. iModIntro.
  iModIntro. iNext.
  iMod "Hclo" as "_".
  iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo"; first by set_solver+.
  iMod "H". iModIntro.
  iApply (step_fupdN_wand with "H").
  iIntros "H".
  iMod "H".
  iMod "Hclo" as "_".
  iDestruct "H" as "(HQ1&H&HQ2)".
  iSpecialize ("Hclo'" $! _ with "[H]").
  { iSplitL "H". iApply "H".
    iAlways.
    iIntros "H".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(_&HP)".
    rewrite /detached_staged.
    iMod (fupd_intro_mask') as "Hclo"; [| iMod "HP"].
    { set_solver. }
    iModIntro.
    iApply (step_fupdN_le (S k)).
    { reflexivity. }
    { lia. }
    iApply (step_fupdN_wand with "HP").
    iIntros "HP". iMod "HP". iDestruct "HP" as "((_&HP)&Hclo')".
    iMod "Hclo'".
    iApply fupd_mask_weaken; auto.
  }
  iMod "Hclo'".
  iModIntro.
  iSplitL "HQ1".
  { iApply "HQR1". eauto. }
  iSplitR "HQ2"; last first.
  { iApply "HQR2". eauto. }
  rewrite wpc_unfold /wpc_pre. rewrite Hval.
  iSplit.
  - iIntros.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    iModIntro. rewrite Nat_iter_S. rewrite Nat_iter_S.
    iModIntro. iNext. iModIntro. iModIntro. iNext.
    iMod "Hclo''" as "_".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(H&_)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo''".
    { set_solver. }
    iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iSplit; last first.
    { iDestruct "H" as "(_&H)".
      iMod "H" as "(($&?)&$)". eauto.
    }
    iDestruct "H" as "(H&_)".
    iDestruct "H" as "(%&H)".
    iSplitL "".
    { destruct s; eauto. }
    iIntros.
    iMod ("H" with "[//]") as "H".
    iModIntro. iNext. iMod "H" as "H".

    iMod "Hclo''" as "_".
    iSpecialize ("Hclo'" $! _ with "[H]").
    { iSplitL "H". iApply "H".
      iAlways. iIntros "H".
      rewrite /detached_staged.
      replace (2 * S (S (S k))) with (S (S (S k)) + S (S (S k))) by lia.
      iApply step_fupdN_inner_plus.
      iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo''".
      { set_solver. }
      iMod "H".
      iModIntro.
      iApply (step_fupdN_le (S k)); first reflexivity.
      { lia. }
      iApply (step_fupdN_wand with "H"). iIntros "H".
      iMod "H". iMod "Hclo''" as "_".
      iDestruct "H" as "(_&H&_)".
      iPoseProof (wpc_crash with "H") as "H".
      iModIntro.
      iMod (fupd_intro_mask') as "Hclo"; [| iMod "H"].
      { set_solver. }
      iModIntro.
      iApply (step_fupdN_le (S k)).
      { reflexivity. }
      { lia. }
      iApply (step_fupdN_wand with "H").
      iIntros "HP". iMod "HP". iDestruct "HP" as "((_&HP)&Hclo')".
      iMod "Hclo'".
      iApply fupd_mask_weaken; auto.
    }
    iMod "Hclo'". iModIntro.
    iApply ("IH" with "Hclo' [] []").
    { iAlways. iIntros "H". eauto. }
    { iAlways. iIntros "H". iApply (big_sepL_mono with "H").
      iIntros. iApply (wpc_strong_mono with "[$]"); eauto.
    }
  - iIntros.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    iModIntro. rewrite Nat_iter_S. rewrite Nat_iter_S.
    iModIntro. iNext. iModIntro. iModIntro. iNext.
    iMod "Hclo''" as "_".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(_&H)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo''".
    { set_solver. }
    iMod ("H") as "H".
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iMod "H" as "(($&HP)&$)".
    eauto.
Qed.

Lemma detached_ci_tok k E1 E2 N P:
  ▷ detached_ci k E1 E2 N P -∗
  Tok -∗
  ▷ (P ∗ Tok).
Proof.
  iIntros "HCI HTok".
  iNext.
  rewrite /detached_ci.
  iDestruct "HCI" as "[$|H]".
  - iFrame.
  - iDestruct "H" as (?) "(H&?)".
    iDestruct (Tok_Tok with "[$]") as "[]".
Qed.

Lemma wpc_staged_invariant s k E1 E2 E1' E2' e Φ Φc P N1 N2 :
  ↑N1 ⊆ E1 →
  ↑N2 ⊆ E1 →
  (E2' ⊆ E1') →
  (E1 ⊆ E1') →
  (E2' ⊆ E2) →
  N1 ## N2 →
  inv N1 (detached_ci (2 * S (S (S k))) E1' E2' N2 P) ∗
  Tok ∗
  (▷ (P) -∗ WPC e @ NotStuck; k; (E1 ∖ ↑N1 ∖ ↑N2); E2
                {{ λ v, (Φ v ∧ |={E1,E2}=> Φc) ∗ P}} {{ Φc ∗ P }}) ⊢
  WPC e @ s; (S (S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (????? Hdisj) "(#Hinv&Htok&Hwp)".
  rewrite !wpc_unfold /wpc_pre.
  iSplit; last first.
  {
    destruct (to_val e).
    - iInv "Hinv" as "H" "Hclo".
      iDestruct (detached_ci_tok with "[$] [$]") as "(H&Htok)".
      iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo'".
      { set_solver+. }
      iDestruct ("Hwp" with "[$]") as "(_&H)".
      iIntros. iMod "H" as "($&?)"; eauto.
    - iInv "Hinv" as "H" "Hclo".
      iDestruct (detached_ci_tok with "[$] [$]") as "(H&Htok)".
      iDestruct ("Hwp" with "[$]") as "(_&H)".
      iIntros. 
      iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo'".
      { set_solver. }
      iMod "H". iModIntro.
      iApply (step_fupdN_le (S k)); first by set_solver+.
      { lia. }
      iApply (step_fupdN_wand with "H").
      iIntros "H". iMod "H" as "(($&?)&$)".
      eauto.
  }
  destruct (to_val e).
  - iInv "Hinv" as "H" "Hclo".
    iDestruct (detached_ci_tok with "[$] [$]") as "(H&Htok)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo'".
    { set_solver+. }
    iDestruct ("Hwp" with "[$]") as "(H&_)".
    iMod "H" as "(($&_)&HP)".
    iMod "Hclo'".
    iMod ("Hclo" with "[-]"); last eauto.
    iLeft. iFrame.
  - iIntros (????) "Hstate".
    iInv "Hinv" as "H" "Hclo".
    iDestruct (detached_ci_tok with "[$] [$]") as "(H&Htok)".
    iDestruct ("Hwp" with "[$]") as "(Hwp&_)".
    replace (↑ N2 : coPset) with (∅ ∪ ↑N2 : coPset) at 1 by set_solver.
    replace (E1 ∖ ↑N1) with (((E1 ∖ ↑N1) ∖ ↑N2) ∪ ↑N2) at 2; last first.
    { assert ((↑N1: coPset) ## (↑N2: coPset)). set_solver.
      clear Hdisj.
      assert (↑N2 ⊆ E1 ∖ ↑N1) by set_solver.
      rewrite difference_union_L. set_solver.
    }
    iSpecialize ("Hwp" with "[$]").
    iMod (fupd_mask_frame_r with "Hwp") as "Hwp".
    { set_solver. }
    rewrite left_id_L.
    iMod (fupd_intro_mask' (↑N2) ∅) as "Hclo'".
    { set_solver. }
    iModIntro. do 2 iEval (rewrite Nat_iter_S_r).
    iApply (step_fupdN_wand with "Hwp").
    iIntros "Hwp".
    iMod (staged_inv_alloc N2 _
             (|={E1', ∅}=> |={∅, ∅}▷=>^(2 * S (S (S k))) |={∅, E2'}=>P)%I _ with "[Hwp]")
      as (γ) "(#Hsi&Hval)".
    { iSplitL "Hwp". iApply "Hwp".
       iAlways. iIntros "(_&Hwp)".
       iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
       iMod "Hwp".
       iModIntro.
       iApply step_fupdN_later; eauto.
       iNext. iDestruct "Hwp" as "((?&HP)&Hclo')".
       iMod "Hclo" as "_". iApply fupd_mask_weaken; eauto.
    }
    iMod "Hclo'" as "_".
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    rewrite difference_diag_L.
    iModIntro. iNext. iModIntro. iModIntro. iNext.
    iModIntro.
    iSplit.
    *
    iDestruct "H" as "(H&_)".
    iDestruct "H" as "(%&H)".
    iSplitL "".
    { destruct s; eauto. }
    iIntros.
    iMod ("H" with "[//]") as "H".
    iModIntro. iNext. iMod "H" as "H".
    iSpecialize ("Hclo'" $! _ with "[H]").
    { iSplitL "H". iApply "H".
      iAlways.
      iIntros "H".

      replace (2 * S (S (S k))) with (S (S (S k)) + S (S (S k))) by lia.
      iApply step_fupdN_inner_plus.
      iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo''".
      { set_solver. }
      iMod "H".
      iModIntro.
      iApply (step_fupdN_le (S k)); first reflexivity.
      { lia. }
      iApply (step_fupdN_wand with "H"). iIntros "H".
      iMod "H". iMod "Hclo''" as "_".
      iDestruct "H" as "(_&H&_)".
      iPoseProof (wpc_crash with "H") as "H".
      iModIntro.
      iMod (fupd_intro_mask') as "Hclo"; [| iMod "H"].
      { set_solver. }
      iModIntro.
      iApply (step_fupdN_le (S k)).
      { reflexivity. }
      { lia. }
      iApply (step_fupdN_wand with "H").
      iIntros "HP". iMod "HP". iDestruct "HP" as "((_&HP)&Hclo')".
      iMod "Hclo'".
      iApply fupd_mask_weaken; auto.
    }
    iAssert (|={E1 ∖ ↑N1 ∖ ↑N2,E1 ∖ ↑N1}=> staged_value N2 γ _)%I with "[Hclo']" as "H".
    {
    iApply fupd_mask_frame.
    2: { iMod "Hclo'". iModIntro.
         rewrite difference_empty_L.
         iApply (fupd_mask_same).
         rewrite (comm_L (∪)).
      assert (↑N2 ⊆ E1 ∖ ↑N1) by set_solver.
      rewrite difference_union_L. set_solver.
      iModIntro. eauto.
    }
    { set_solver. }
    }
    iMod "H".
    iMod ("Hclo" with "[Htok]") as "_".
    { iNext. iRight. iExists _. iFrame. iFrame "Hsi". }
    iModIntro.
    iApply (wpc_staged_invariant_aux s k E1 E2 E1' E2'
                  _ Φ Φc P
                  (state_interp σ2 a1 (strings.length efs + a2)) _
                  ([∗ list] ef ∈ efs, WPC ef @ k; ⊤;∅ {{ v, fork_post v }}{{True}})%I  _ N1 N2 with "[H]"); try assumption.
    { iIntros. iFrame "Hinv". iFrame "H".
      iFrame "Hsi". iSplit.
      - eauto.
      - iAlways. iIntros "H". iApply (big_sepL_mono with "H").
        iIntros. iApply (wpc_strong_mono with "[$]"); eauto.
    }
    * iDestruct "H" as "(_&H)".
      iMod "H" as "(($&_)&$)". eauto.
Qed.

Lemma wpc_atomic s E1 E2 e Φ Φc `{!Atomic (stuckness_to_atomicity s) e} :
  Φc ∧ WP e @ s; E1 {{ v, (|={E1}=> Φ v) ∧ |={⊤, E2}=> Φc }} ⊢ WPC e @ s; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". rewrite !wpc_unfold !wp_unfold /wpc_pre /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { iSplit.
    - iDestruct "H" as "(_&H)".
      by iMod "H" as "($&_)".
    - iDestruct "H" as "(H&_)".
      iIntros. iFrame. iApply fupd_mask_weaken; eauto.
  }
  iSplit.
  {
    iDestruct "H" as "(_&H)".
    iIntros (σ1 κ κs n) "Hσ". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
    iModIntro. iIntros (e2 σ2 efs Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!>!>".
    iMod "H" as "(Hσ & H & Hefs)". destruct s.
    - rewrite !wpc_unfold !wp_unfold /wpc_pre /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
      + iDestruct "H" as "> H". iFrame.
        iModIntro. iSplitL "H".
        { iSplit.
          * by iDestruct "H" as "($&_)".
          * iDestruct "H" as "(_&H)". iIntros. iMod "H". iFrame. by iApply fupd_mask_weaken. }
        { iApply big_sepL_mono; last eauto. iIntros.
          by iApply wp_wpc.
        }
      + iMod ("H" $! _ [] with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ? & ?).
        by edestruct (atomic _ _ _ _ _ Hstep).
    - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
      iMod (wp_value_inv' with "H") as "H".
      iModIntro. iFrame.
      iSplitL "H".
      { by iApply wpc_value. }
      { iApply big_sepL_mono; last eauto. iIntros.
          by iApply wp_wpc.
      }
  }
  { iIntros. iDestruct "H" as "(H&_)". iFrame. iApply fupd_mask_weaken; eauto. }
Qed.

Lemma wpc_bind K `{!LanguageCtx K} s E1 E2 e Φ Φc :
  WPC e @ s; E1 ; E2 {{ v, WPC K (of_val v) @ s; E1; E2 {{ Φ }} {{ Φc }} }} {{ Φc }}
                     ⊢ WPC K e @ s; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E1 E2 e Φ). rewrite wpc_unfold /wpc_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply fupd_wpc. iDestruct "H" as "($&_)". }
  rewrite wpc_unfold /wpc_pre fill_not_val //.
  iSplit; last by (iDestruct "H" as "(_&$)").
  iDestruct "H" as "(H&_)".
  iIntros (σ1 κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]". iModIntro; iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//]") as "H". iIntros "!>!>".
  iMod "H" as "(Hσ & H & Hefs)".
  iModIntro. iFrame "Hσ Hefs". by iApply "IH".
Qed.

Lemma wpc_bind_inv K `{!LanguageCtx K} s E1 E2 e Φ Φc :
  WPC K e @ s; E1; E2 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; E1 ; E2 {{ v, WPC K (of_val v) @ s; E1; E2 {{ Φ }} {{ Φc }} }} {{Φc }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E1 E2 e Φ Φc). rewrite !wpc_unfold /wpc_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. rewrite !wpc_unfold /wpc_pre. iSplit.
    - iModIntro. eauto.
    - iDestruct "H" as "(_&$)".
  }
  rewrite fill_not_val //.
  iSplit.
  - iDestruct "H" as "(H&_)".
    iIntros (σ1 κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]". iModIntro; iSplit.
    { destruct s; eauto using reducible_fill. }
    iIntros (e2 σ2 efs Hstep).
    iMod ("H" $! (K e2) σ2 efs with "[]") as "H"; [by eauto using fill_step|].
    iIntros "!>!>". iMod "H" as "(Hσ & H & Hefs)".
    iModIntro. iFrame "Hσ Hefs". by iApply "IH".
  - iIntros. iDestruct "H" as "(_&H)".
    by iMod ("H" with "[$]").
Qed.

Lemma wpc_lift_step_fupd s E E' Φ Φc e1 :
  to_val e1 = None →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,∅,E}▷=∗
      state_interp σ2 κs (length efs + n) ∗
      WPC e2 @ s; E; E' {{ Φ }} {{ Φc }} ∗
      [∗ list] ef ∈ efs, WPC ef @ s; ⊤; ∅ {{ fork_post }} {{ True }})
  ∧ Φc
  ⊢ WPC e1 @ s; E; E' {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre=>->. iIntros "H".
  iSplit; last first.
  { iIntros. iDestruct "H" as "(_&$)". iFrame. iApply fupd_mask_weaken; eauto. }
  iDestruct "H" as "(H&_)". iIntros (σ1 κ κs n) "Hσ".
  iMod ("H" with "Hσ") as "(%&H)". iModIntro. iSplit. by destruct s.
  iIntros (????). iApply "H". eauto.
Qed.

Lemma wpc_lift_step s E1 E2 Φ Φc e1 :
  to_val e1 = None →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E1,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E1}=∗
      state_interp σ2 κs (length efs + n) ∗
      WPC e2 @ s; E1; E2 {{ Φ }} {{ Φc }} ∗
      [∗ list] ef ∈ efs, WPC ef @ s; ⊤; ∅ {{ fork_post }} {{ True }})
  ∧ Φc
  ⊢ WPC e1 @ s; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "H". iApply wpc_lift_step_fupd; [done|].
  iSplit; last by (iDestruct "H" as "(_&$)").
  iIntros (????) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % !> !>". by iApply "H".
Qed.

Lemma wpc_lift_pure_step_no_fork `{!Inhabited (state Λ)} s E1 E1' E2 Φ Φc e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={E1,E1'}▷=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → WPC e2 @ s; E1; E2 {{ Φ }} {{ Φc }}) ∧ Φc
  ⊢ WPC e1 @ s; E1; E2 {{ Φ }} {{ Φc }}.
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

Lemma wpc_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E1 E1' E2 Φ Φc} e1 e2 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E1,E1'}▷=> WPC e2 @ s; E1; E2 {{ Φ }} {{ Φc }}) ∧ Φc
  ⊢ WPC e1 @ s; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wpc_lift_pure_step_no_fork s E1 E1' E2); try done.
  { naive_solver. }
  iSplit; last by (iDestruct "H" as "(_&$)").
  iDestruct "H" as "(H&_)".
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.

(* Note: compared to wp_pure_step_fupd, we have n = 1 *)
Lemma wpc_pure_step_fupd `{!Inhabited (state Λ)} s E1 E1' E2 e1 e2 φ Φ Φc :
  PureExec φ 1 e1 e2 →
  φ →
  (|={E1,E1'}▷=>^1 WPC e2 @ s; E1; E2 {{ Φ }} {{ Φc }}) ∧ Φc
  ⊢ WPC e1 @ s; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  inversion Hexec as [|? e1' e2' e3' [Hsafe ?] Hrest]. subst.
  inversion Hrest; subst.
  iApply wpc_lift_pure_det_step_no_fork; last eauto.
  - intros σ. specialize (Hsafe σ). destruct s;
    eauto using reducible_not_val, reducible_no_obs_reducible.
  - done.
Qed.

Lemma wpc_pure_step_later `{!Inhabited (state Λ)} s E1 E2 e1 e2 φ Φ Φc :
  PureExec φ 1 e1 e2 →
  φ →
  ▷^1 WPC e2 @ s; E1 ; E2 {{ Φ }} {{ Φc }} ∧ Φc
  ⊢ WPC e1 @ s; E1 ; E2 {{ Φ }} {{ Φc }}.
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
Lemma wpc_mono s E1 E2 e Φ Ψ Φc Ψc :
  (∀ v, Φ v ⊢ Ψ v) → (Φc ⊢ Ψc) → WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; E1; E2 {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (HΦ HΦc) "H"; iApply (wpc_strong_mono with "H"); auto.
  iSplit.
  - iIntros (v) "?". by iApply HΦ.
  - iIntros "?". by iApply HΦc.
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
  Context `{!irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wpc p s E1 E2 e R Φ Ψ Φc Ψc :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
     Frame p R Φc Ψc →
    Frame p R (WPC e @ s; E1; E2 {{ Φ }} {{ Φc }}) (WPC e @ s; E1; E2 {{ Ψ }} {{ Ψc }}).
  Proof. rewrite /Frame=> HR HRc. rewrite wpc_frame_l. apply wpc_mono; [ apply HR | apply HRc ]. Qed.

  Global Instance is_except_0_wpc s E1 E2 e Φ Φc : IsExcept0 (WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wpc -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wpc p s E1 E2 e P Φ Φc:
    ElimModal True p false (|==> P) P (WPC e @ s; E1; E2 {{ Φ }} {{ Φc }}) (WPC e @ s; E1; E2 {{ Φ }} {{ Φc }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_wpc.
  Qed.

  Global Instance elim_modal_fupd_wpc p s E1 E2 e P Φ Φc :
    ElimModal True p false (|={E1}=> P) P (WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }})
              (WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }}).
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
