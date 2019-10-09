From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
Set Default Proof Using "Type".
Import uPred.

(* Define a weakestpre with an explicit crash invariant (i.e. there is a postcondition and a crash condition *)

Definition wpc_pre `{!irisG Λ Σ} (s : stuckness)
    (wpc : coPset -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ) :
    coPset -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ := λ E1 E2 e1 Φ Φc,
  (match to_val e1 with
   | Some v => |={E1}=> Φ v
   | None => ∀ σ1 κ κs n,
      state_interp σ1 (κ ++ κs) n ={E1,∅}=∗
        ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
        ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,∅,E1}▷=∗
          state_interp σ2 κs (length efs + n) ∗
          wpc E1 E2 e2 Φ Φc ∗
          [∗ list] i ↦ ef ∈ efs, wpc ⊤ ⊤ ef fork_post True
   end ∧
   ∀ σ κs n, state_interp σ κs n ={⊤, E2}=∗ Φc ∗ state_interp σ κs n)%I.

Local Instance wpc_pre_contractive `{!irisG Λ Σ} s : Contractive (wpc_pre s).
Proof.
  rewrite /wpc_pre=> n wp wp' Hwp E1 E2 e1 Φ Φc.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wpc_def `{!irisG Λ Σ} (s : stuckness) :
  coPset → coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ → iProp Σ := fixpoint (wpc_pre s).
Definition wpc_aux `{!irisG Λ Σ} : seal (@wpc_def Λ Σ _). by eexists. Qed.


(* Notation: copied from iris bi/weakestpre.v *)
Class Wpc (Λ : language) (PROP A : Type) :=
  wpc : A → coPset → coPset → expr Λ → (val Λ → PROP) → PROP → PROP.
Arguments wpc {_ _ _ _} _ _ _ _%E _%I _%I.
Instance: Params (@wp) 9 := {}.

Instance wpc' `{!irisG Λ Σ} : Wpc Λ (iProp Σ) stuckness := wpc_aux.(unseal).
Definition wpc_eq `{!irisG Λ Σ} : wpc = @wpc_def Λ Σ _ := wpc_aux.(seal_eq).

(** Notations for partial crash weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WPC' e @ s ; E1 ; E2 {{ Φ } } {{ Φc } }" := (wpc s E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e @ E1 ; E2 {{ Φ } } {{ Φc } }" := (wpc NotStuck E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e @ E1 ; E2 ? {{ Φ } } {{ Φc } }" := (wpc MaybeStuck E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e {{ Φ } } {{ Φc } }" := (wpc NotStuck ⊤ ∅ e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e ? {{ Φ } } {{ Φc } }" := (wpc MaybeStuck ⊤ ∅ e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'WPC' e @ s ; E1 ; E2 {{ v , Q } } {{ R } }" := (wpc s E1 E2 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[' 'WPC'  e  '/' '[          ' @  s ;  E1 ;  E2  {{  v ,  Q  } }  {{ R } } ']' ']'") : bi_scope.
(*
Notation "'WP' e @ E {{ v , Q } }" := (wp NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[       ' @  E  {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e @ E ? {{ v , Q } }" := (wp MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[        ' @  E  ? {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e {{ v , Q } }" := (wp NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[   ' {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' e ? {{ v , Q } }" := (wp MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' '[    ' ? {{  v ,  Q  } } ']' ']'") : bi_scope.
*)

Section wpc.
Context `{!irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpc_unfold s E1 E2 e Φ Φc :
  WPC e @ s; E1; E2 {{ Φ }} {{ Φc }} ⊣⊢ wpc_pre s (wpc (PROP:=iProp Σ)  s) E1 E2 e Φ Φc.
Proof. rewrite wpc_eq. apply (fixpoint_unfold (wpc_pre s)). Qed.

Global Instance wpc_ne s E1 E2 e n :
  Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) (wpc (PROP:=iProp Σ) s E1 E2 e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ Φc Ψc HΦc.
  rewrite !wpc_unfold /wpc_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  (f_contractive || f_equiv); last first.
  { repeat (f_contractive || f_equiv). auto. }
  do 24 (f_contractive || f_equiv). apply IH; first lia.
  - intros v. eapply dist_le; eauto with lia.
  - eapply dist_le; eauto with lia.
Qed.

Global Instance wpc_proper s E1 E2 e :
  Proper (pointwise_relation _ (≡) ==> (≡) ==> (≡)) (wpc (PROP:=iProp Σ) s E1 E2 e).
Proof.
  intros Φ Φ' ? Φc Φc' ?.
  apply equiv_dist=>n. apply wpc_ne; auto.
  by intros v; apply equiv_dist.
Qed.

Lemma wp_wpc s E1 E2 e Φ :
  WP e @ s ; E1 {{ Φ }} ⊢ WPC e @ s ; E1 ; E2 {{ Φ }} {{ True }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E1 E2 e Φ).
  rewrite wp_unfold wpc_unfold /wp_pre /wpc_pre. destruct (to_val e) as [v|]=>//.
  - iSplit; auto. iIntros. iFrame. iApply (fupd_mask_weaken _ E2); auto.
  - iSplit.
    * iIntros (σ1 κ κs n) "Hσ". iMod ("H" with "Hσ") as "[% H]". iIntros "!>". iSplitR.
      { destruct s; last done. eauto using reducible_no_obs_reducible. }
      iIntros (e2 σ2 efs) "Hstep". iMod ("H" with "Hstep") as "H".
      iModIntro. iNext. iMod ("H") as "(Hσ & H & Hfork)". iFrame. iModIntro.
      iSplitL "H".
      { by iApply "IH". }
      iApply (@big_sepL_impl with "Hfork").
      iIntros "!#" (k ef _) "H". by iApply "IH".
    * iIntros. iFrame. iApply (fupd_mask_weaken _ E2); auto.
Qed.

Lemma wpc_strong_mono s1 s2 E1 E2 E1' E2' e Φ Ψ Φc Ψc :
  s1 ⊑ s2 → E1 ⊆ E2 → E2' ⊆ E1' →
  WPC e @ s1; E1 ; E1' {{ Φ }} {{ Φc }} -∗
  (∀ v, Φ v ={E2}=∗ Ψ v) ∧ (Φc ={E1', E2'}=∗ Ψc) -∗
  WPC e @ s2; E2 ; E2' {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (? HE HE') "H HΦ". iLöb as "IH" forall (e E1 E2 E1' E2' HE HE' Φ Ψ Φc Ψc).
  rewrite !wpc_unfold /wpc_pre.
  destruct (to_val e) as [v|] eqn:?.
  { iSplit.
    - iDestruct "HΦ" as "(HΦ&_)".
      iApply ("HΦ" with "[> -]"). iDestruct "H" as "(H&_)". by iApply (fupd_mask_mono E1 _).
    - iIntros. iDestruct "HΦ" as "(_&HΦ)". iDestruct "H" as "(_&H)".
      iMod ("H" with "[$]") as "(?&$)".
      by iMod ("HΦ" with "[$]").
  }
  iSplit.
  - iIntros (σ1 κ κs n) "Hσ". iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
    iDestruct "H" as "(H&_)".
    iMod ("H" with "[$]") as "[% H]".
    iModIntro. iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!> !>".
    iMod "H" as "(Hσ & H & Hefs)".
    iMod "Hclose" as "_". iModIntro. iFrame "Hσ". iSplitR "Hefs".
    * iApply ("IH" with "[] [] H [HΦ]"); auto.
    * iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
      iIntros "H". eauto. iApply ("IH" with "[] [] H"); auto.
  - iIntros. iDestruct "HΦ" as "(_&HΦ)". iDestruct "H" as "(_&H)".
    iMod ("H" with "[$]") as "(?&$)".
    by iMod ("HΦ" with "[$]").
Qed.

Lemma wpc_frame_l s E1 E2 e Φ Φc R :
  R ∗ WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; E1 ; E2 {{ v, R ∗ Φ v }} {{ R ∗ Φc }}.
Proof. iIntros "[? H]". iApply (wpc_strong_mono with "H"); auto with iFrame. Qed.

Lemma wpc_fupd_open s E1 E2 E2' e Φ Φc :
  E2 ⊆ E2' →
  WPC e @ s; E1 ; E2' {{ Φ }} {{ |={E2', E2}=> Φc }} ⊢ WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof. iIntros (?) "H". iApply (wpc_strong_mono s s E1 E1 E2' with "H []"); auto. Qed.

(** XXX: this could be strengthened by being more careful about the masks **)
Lemma wpc_inv (N: namespace) s E e Φ Φc :
  inv N Φc ∗ WPC e @ s ; E; ↑N {{ Φ }} {{ True }} ⊢ WPC e @ s ; E ; ∅ {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros "(#Hinv&H)".
  iApply (wpc_strong_mono s s E E (↑N) with "H"); try set_solver+.
  iSplit; auto.
  iIntros. iInv N as "Hfoo" "Hclo".
  iApply fupd_mask_weaken; first by set_solver+. done.
Qed.

Lemma wp_wpc_inv (N: namespace) s E e Φ Φc :
  inv N Φc ∗ WP e @ s ; E {{ Φ }} ⊢ WPC e @ s ; E ; ∅ {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros "(#Hinv&H)". iDestruct (wp_wpc with "H") as "H". iApply wpc_inv; by iFrame.
Qed.

Lemma wpc_value' s E1 E2 Φ Φc v : Φ v ∧ Φc ⊢ WPC of_val v @ s; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre to_of_val. iApply and_mono; auto.
  iIntros. iApply fupd_mask_weaken; first by auto. iFrame.
Qed.

Lemma wpc_value_inv' s E1 E2 Φ Φc v : WPC of_val v @ s; E1; E2 {{ Φ }} {{ Φc }} ={E1}=∗ Φ v.
Proof. rewrite wpc_unfold /wpc_pre to_of_val. iIntros "(?&_)"; auto. Qed.

Lemma fupd_wpc s E1 E2 e Φ Φc:
  (|={E1}=> WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }}) ⊢ WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre. iIntros "H". iSplit.
  - destruct (to_val e) as [v|] eqn:?.
    { by iMod "H" as "(?&_)". }
    iIntros (σ1 κ κs n) "Hσ1". iMod "H". by iApply "H".
  - iIntros. iApply (fupd_trans ⊤ ⊤).
    iApply fupd_mask_mono; last (iMod "H" as "(_&H)"); first by set_solver+.
    iModIntro. by iApply "H".
Qed.

(*
Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.

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

Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val //.
  iIntros (σ1 κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]". iModIntro; iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//]") as "H". iIntros "!>!>".
  iMod "H" as "(Hσ & H & Hefs)".
  iModIntro. iFrame "Hσ Hefs". by iApply "IH".
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

(** * Derived rules *)
Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
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

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
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

(*
(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

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
End proofmode_classes.
*)
