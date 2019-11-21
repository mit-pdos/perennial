From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
Set Default Proof Using "Type".
Import uPred.

(* Define a weakestpre with an explicit crash invariant (i.e. there is a postcondition and a crash condition *)

Axiom NC : forall Σ, nat -> iProp Σ.
Axiom C : forall Σ, iProp Σ.
Arguments NC {_}.
Arguments C {_}.

Definition wpc_pre `{!irisG Λ Σ} (s : stuckness)
    (wpc : nat -d> coPset -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ) :
    nat -d> coPset -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ := λ ntok E1 E2 e1 Φ Φc,
  ((|={E1}=> ∃ k, NC k -∗ match to_val e1 with
   | Some v => |={E1}=> Φ v
   | None => ∀ σ1 κ κs n,
      state_interp σ1 (κ ++ κs) n ={E1,∅}=∗
        ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
        ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,∅,E1}▷=∗
          state_interp σ2 κs (length efs + n) ∗
          wpc (ntok + k) E1 E2 e2 Φ Φc ∗
          ([∗ list] i ↦ ef ∈ efs, wpc 0 ⊤ ∅ ef fork_post True)
   end) ∧
   ∀ σ κs n, state_interp σ κs n ={E1, E2}=∗ NC ntok ∗ |={E2, E1}=> (C ={E1, E2}=∗  Φc ∗ state_interp σ κs n ∗ C))%I.

Axiom NC_C: forall Σ k, @NC Σ (S k) ∗ @C Σ -∗ False.
Axiom NC_S: forall Σ k, @NC Σ (S k) -∗ @NC Σ k ∗ @NC Σ 1.

Local Instance wpc_pre_contractive `{!irisG Λ Σ} s : Contractive (wpc_pre s).
Proof.
  rewrite /wpc_pre=> n wp wp' Hwp ntok E1 E2 e1 Φ Φc.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wpc_def `{!irisG Λ Σ} (s : stuckness) :
  nat → coPset → coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ → iProp Σ := fixpoint (wpc_pre s).
Definition wpc_aux `{!irisG Λ Σ} : seal (@wpc_def Λ Σ _). by eexists. Qed.


(* Notation: copied from iris bi/weakestpre.v *)
Class Wpc (Λ : language) (PROP A : Type) :=
  wpc : A → nat → coPset → coPset → expr Λ → (val Λ → PROP) → PROP → PROP.
Arguments wpc {_ _ _ _} _ _ _ _ _%E _%I _%I.
Instance: Params (@wp) 10 := {}.

Instance wpc' `{!irisG Λ Σ} : Wpc Λ (iProp Σ) stuckness := wpc_aux.(unseal).
Definition wpc_eq `{!irisG Λ Σ} : wpc = @wpc_def Λ Σ _ := wpc_aux.(seal_eq).

(** Notations for partial crash weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WPC' e @ n ; s ; E1 ; E2 {{ Φ } } {{ Φc } }" := (wpc s n E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e @ n ; E1 ; E2 {{ Φ } } {{ Φc } }" := (wpc NotStuck n E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
(*
Notation "'WPC' e @ E1 ; E2 ? {{ Φ } } {{ Φc } }" := (wpc MaybeStuck E1 E2 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e {{ Φ } } {{ Φc } }" := (wpc NotStuck ⊤ ∅ e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e ? {{ Φ } } {{ Φc } }" := (wpc MaybeStuck ⊤ ∅ e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
*)

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'WPC' e @ n ; s ; E1 ; E2 {{ v , Q } } {{ R } }" := (wpc n s E1 E2 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[' 'WPC'  e  '/' '[          ' @  n ; s ;  E1 ;  E2  {{  v ,  Q  } }  {{ R } } ']' ']'") : bi_scope.
(*
Notation "'WPC' e @ E1 ; E2 {{ v , Q } } {{ R } }" := (wpc NotStuck E1 E2 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[' 'WPC'  e  '/' '[       ' @  E1 ; E2  {{  v ,  Q  } } {{ R } } ']' ']'") : bi_scope.
Notation "'WPC' e @ E1 ; E2 ? {{ v , Q } } {{ R } }" := (wpc MaybeStuck E1 E2 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[' 'WPC'  e  '/' '[        ' @  E1 ; E2  ? {{  v ,  Q  } } {{ R } } ']' ']'") : bi_scope.
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

Lemma wpc_unfold (n: nat) s E1 E2 e Φ Φc :
  WPC e @ n; s; E1; E2 {{ Φ }} {{ Φc }} ⊣⊢ wpc_pre s (wpc (PROP:=iProp Σ)  s) n E1 E2 e Φ Φc.
Proof. rewrite wpc_eq. apply (fixpoint_unfold (wpc_pre s)). Qed.

Global Instance wpc_ne s E1 E2 e n ntok :
  Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) (wpc (PROP:=iProp Σ) s ntok E1 E2 e).
Proof.
  revert ntok e. induction (lt_wf n) as [n _ IH]=> ntok e Φ Ψ HΦ Φc Ψc HΦc.
  rewrite !wpc_unfold /wpc_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  (f_contractive || f_equiv); last first.
  { repeat (f_contractive || f_equiv). auto. }
  do 28 (f_contractive || f_equiv). apply IH; first lia.
  - intros v. eapply dist_le; eauto with lia.
  - eapply dist_le; eauto with lia.
Qed.

Global Instance wpc_proper s E1 E2 e ntok :
  Proper (pointwise_relation _ (≡) ==> (≡) ==> (≡)) (wpc (PROP:=iProp Σ) s ntok E1 E2 e).
Proof.
  intros Φ Φ' ? Φc Φc' ?.
  apply equiv_dist=>n. apply wpc_ne; auto.
  by intros v; apply equiv_dist.
Qed.

Axiom NCO : (@NC Σ O : iProp Σ) ≡ True%I.

Lemma wp_wpc s E1 E2 e Φ :
  E2 ⊆ E1 →
  WP e @ s ; E1 {{ Φ }} ⊢ WPC e @ 0 ; s ; E1 ; E2 {{ Φ }} {{ True }}.
Proof.
  iIntros (Hsub) "H". iLöb as "IH" forall (E1 E2 Hsub e Φ).
  rewrite wp_unfold wpc_unfold /wp_pre /wpc_pre. destruct (to_val e) as [v|]=>//.
  - iIntros; iSplit; first by (iExists O; auto). iIntros. iFrame. 
    iMod "H".
    iMod (fupd_intro_mask' _ E2) as "H'"; first by auto.
    iModIntro. rewrite NCO left_id. iMod "H'". iModIntro. iIntros.
    iApply (fupd_mask_weaken _ E2); auto.
  - iSplit.
    * iExists O.
      iIntros "!> NC". iIntros (σ1 κ κs n) "Hσ".
      iMod ("H" with "Hσ") as "[% H]". iIntros "!>". iSplitR.
      { destruct s; last done. eauto using reducible_no_obs_reducible. }
      iIntros (e2 σ2 efs) "Hstep". iMod ("H" with "Hstep") as "H".
      iModIntro. iNext. iMod ("H") as "(Hσ & H & Hfork)". iFrame. iModIntro.
      rewrite right_id.
      iSplitL "H".
      { by iApply "IH". }
      iApply (@big_sepL_impl with "Hfork").
      iIntros "!#" (k ef _) "H". by iApply "IH".
    * iIntros. iFrame.
      rewrite NCO left_id. iApply fupd_intro_mask; first by auto.
      iApply (fupd_mask_weaken _ E2); auto.
Qed.

Lemma wpc_strong_mono s1 s2 E1 E2 E1' E2' e Φ Ψ Φc Ψc ntok :
  s1 ⊑ s2 → E1 ⊆ E2 → E2' ⊆ E1' → E2' ⊆ E2 →
  WPC e @ ntok; s1; E1 ; E1' {{ Φ }} {{ Φc }} -∗
  (∀ v, Φ v ={E2}=∗ Ψ v) ∧ (Φc ∗ C ={E1', E2'}=∗ Ψc ∗ C) -∗
  WPC e @ ntok; s2; E2 ; E2' {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (? HE HE' HE2) "H HΦ". iLöb as "IH" forall (e E1 E2 E1' E2' HE HE' HE2 Φ Ψ Φc Ψc ntok).
  rewrite !wpc_unfold /wpc_pre.
  iSplit.
  - iDestruct "H" as "(H&_)".
    iMod (fupd_intro_mask' _ E1) as "Hclo"; first by auto.
    iMod "H" as (k) "H". iMod "Hclo" as "_". iExists k. iModIntro.
    iIntros "HNC".
    destruct (to_val e) as [v|] eqn:?.
    * iDestruct "HΦ" as "(HΦ&_)".
      iApply ("HΦ" with "[> -]"). iSpecialize ("H" with "[$]").
      by iApply (fupd_mask_mono E1 _).
    * iIntros (σ1 κ κs n) "Hσ".
      iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
      iMod ("H" with "[$] [$]") as "[% H]".
      iModIntro. iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
      iMod ("H" with "[//]") as "H". iIntros "!> !>".
      iMod "H" as "(Hσ & H & Hefs)".
      iMod "Hclose" as "_". iModIntro. iFrame "Hσ". iFrame. iSplitR "Hefs".
      ** iApply ("IH" with "[] [] [] H [HΦ]"); auto.
      ** iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k' ef _).
         iIntros "H". eauto. iApply ("IH" with "[] [] [] H"); auto.
  - iIntros. iDestruct "HΦ" as "(_&HΦ)". iDestruct "H" as "(_&H)".
    iSpecialize ("H" with "[$]").
    iMod (fupd_intro_mask' E2 E1) as "Hclo"; first auto.
    iMod "H" as "($&H)".
    iMod "H". iMod "Hclo" as "_".
    iApply fupd_intro_mask; first auto.
    iIntros "HC".
    iMod (fupd_intro_mask' E2 E1); first auto.
    iMod ("H" with "[$]") as "(?&$&HC)".
    iMod ("HΦ" with "[$]") as "$". eauto.
Qed.

(*
Lemma wpc_frame_l s E1 E2 e Φ Φc R :
  R ∗ WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; E1 ; E2 {{ v, R ∗ Φ v }} {{ R ∗ Φc }}.
Proof. iIntros "[? H]". iApply (wpc_strong_mono with "H"); auto with iFrame. Qed.
*)

Lemma wpc_fupd_open ntok s E1 E2 E2' e Φ Φc :
  E2 ⊆ E2' → E2 ⊆ E1 →
  WPC e @ ntok; s; E1 ; E2' {{ Φ }} {{ |={E2', E2}=> Φc }} ⊢ WPC e @ ntok; s; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (??) "H".
  iApply (wpc_strong_mono s s E1 E1 E2' with "H []"); auto.
  iSplit.
  - eauto.
  - iIntros "(?&$)". eauto.
Qed.

(** XXX: this could be strengthened by being more careful about the masks **)
Lemma wpc_inv (N: namespace) ntok s E e Φ Φc :
  inv N Φc ∗ WPC e @ ntok; s ; E; ↑N {{ Φ }} {{ True }} ⊢ WPC e @ ntok; s ; E ; ∅ {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros "(#Hinv&H)".
  iApply (wpc_strong_mono s s E E (↑N) with "H"); try set_solver+.
  iSplit; auto.
  iIntros "(?&?)". iInv N as "Hfoo" "Hclo".
  iApply fupd_mask_weaken; first by set_solver+. iFrame.
Qed.

Axiom Tok: iProp Σ.
Axiom Tok_Tok : Tok ∗ Tok -∗ False.
Instance timeless_C: Timeless (@C Σ).
Admitted.
Instance timeless_NC k: Timeless (@NC Σ k).
Admitted.
Instance timeless_Tok: Timeless (Tok).
Admitted.

(*
Lemma wpc_crash_inv' (N: namespace) ntok s E e Φ Φc :
  (↑N ⊆ E) →
  inv N ((NC 1 ∗ (Φc ∨ Tok)) ∨ (Φc ∗ (NC 1 ∨ Tok))) ∗
  Φc ∗
  (▷ Tok -∗ WPC e @ ntok; s ; E; ↑N {{ Φ }} {{ True }}) ⊢
  WPC e @ ntok; s ; E; ↑N {{ λ v, Φ v ∗ Φc }} {{ Φc }}.
Proof.
  iIntros (HN) "(#Hinv&HΦc&H)".
  iApply (wpc_strong_mono s s E E (↑N) with "H"); try set_solver.
  iSplit.
  - iIntros. by iFrame.
  - iIntros "(?&HC)". by iFrame.
Qed.
*)

Lemma wpc_crash_inv (N: namespace) ntok s E e Φ Φc :
  inv N ((NC 1 ∗ (Φc ∨ Tok)) ∨ (Φc ∗ (NC 1 ∨ Tok))) ∗
  WPC e @ ntok; s ; E; ↑N {{ Φ }} {{ True }} ⊢
  WPC e @ ntok; s ; E ; ∅ {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros "(#Hinv&H)".
  iApply (wpc_strong_mono s s E E (↑N) with "H"); try set_solver+.
  iSplit; auto.
  iIntros "(_&HC)". iInv N as "Hi" "Hclo".
  iAssert (|={↑N ∖ ↑N,∅}=> ▷ (Φc ∗ C))%I with "[-]" as "H"; last first.
  { iMod "H" as "(?&>C)". iFrame. eauto. }
  iApply fupd_mask_weaken; first by set_solver+.
  iNext. iDestruct "Hi" as "[(Hnc&?)|($&?)]".
  {  iExFalso. iApply (NC_C with "[$]"). }
  eauto.
Qed.

(*
Lemma wpc_crash_inv_alloc (N: namespace) ntok s E e Φ Φc :
  ↑N ⊆ E →
  Φc ∗ Tok ∗
  (inv N ((NC 1 ∗ (Φc ∨ Tok)) ∨ (Φc ∗ (NC 1 ∨ Tok))) -∗ Tok -∗
  WPC e @ ntok; s ; E; ↑N {{ Φ }} {{ True }}) ⊢
  WPC e @ ntok; s ; E ; ∅ {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros (?) "(HΦ&Htok&Hw)".
  rewrite !wpc_unfold /wpc_pre.
  iSplit; last first.

  iApply (wpc_strong_mono s s E E (↑N) with "H"); try set_solver+.
  iSplit; auto.
  iIntros "(_&HC)". iInv N as "Hi" "Hclo".
  iAssert (|={↑N ∖ ↑N,∅}=> ▷ (Φc ∗ C))%I with "[-]" as "H"; last first.
  { iMod "H" as "(?&>C)". iFrame. eauto. }
  iApply fupd_mask_weaken; first by set_solver+.
  iNext. iDestruct "Hi" as "[(Hnc&?)|($&?)]".
  {  iExFalso. iApply (NC_C with "[$]"). }
  eauto.
Qed.
*)

Lemma wpc_crash_inv_rev (N: namespace) ntok s E e Φ Φc :
 ↑N ⊆ E →
  inv N ((NC 1 ∗ (Φc ∨ Tok)) ∨ (Φc ∗ (NC 1 ∨ Tok))) ∗
  Tok ∗
  (▷ Φc -∗ WPC e @ ntok; s ; E; ↑N {{ λ v, Φ v ∗ Φc }} {{ Φc }}) ⊢
  WPC e @ ntok; s ; E ; ↑N {{ Φ }} {{ True }}.
Proof.
  iIntros (?) "(#Hinv&Htok&Hwand)".
  rewrite !wpc_unfold /wpc_pre.
  iSplit; last first.
  - iIntros. iInv "Hinv" as "H" "Hclo".
    iDestruct "H" as "[H|H]".
    * iDestruct "H" as "(>HNC&[HΦ|>Htok'])"; last first.
      { iExFalso. iApply (Tok_Tok with "[$]"). }
      iDestruct ("Hwand" with "[$]") as "(_&Hcrash)".
      iMod ("Hclo" with "[HNC Htok]").
      { iNext. iLeft. iFrame. }
      iMod ("Hcrash" with "[$]") as "(HNC&H)".
      iModIntro. iFrame. iMod "H" as "H".
      iIntros "!> HC". iMod ("H" with "[$]") as "(?&$&$)". by iModIntro.
    * iDestruct "H" as "(HΦ&[>HNC|>Htok'])"; last first.
      { iExFalso. iApply (Tok_Tok with "[$]"). }
      iDestruct ("Hwand" with "[$]") as "(_&Hcrash)".
      iSpecialize ("Hcrash" with "[$]").
      iMod ("Hclo" with "[HNC Htok]").
      {  iLeft. iFrame. }
      iMod ("Hcrash") as "(HNC&H)".
      iModIntro. iFrame. iMod "H". iIntros "!> HC".
      iMod ("H" with "[$]") as "(?&$&$)".
      eauto.
  - iIntros. iInv "Hinv" as "H" "Hclo".
    iDestruct "H" as "[H|H]".
    * iDestruct "H" as "(>HNC&[HΦ|>Htok'])"; last first.
      { iExFalso. iApply (Tok_Tok with "[$]"). }
      iDestruct ("Hwand" with "[$]") as "(Hwp&_)".
      iMod ("Hclo" with "[HNC Htok]").
      { iNext. iLeft. iFrame. }
      iMod ("Hwp") as (k) "Hwp". iModIntro. iExists k. iIntros "HNC".
      iSpecialize ("Hwp" with "[$]").
      destruct (to_val e) as [|].
      { by iMod "Hwp" as "($&_)". }
      iIntros (????) "H".
      iMod ("Hwp" with "H") as "($&H)".
      iModIntro. iIntros.
      iMod ("H" with "[//]") as "H". iModIntro.
      iNext. iMod "H" as "(Hσ & H & Hfork)". iModIntro.
      iFrame.
      iApply (wpc_strong_mono with "H"); eauto.
      iSplit.
      ** iIntros (?) "(?&?)"; by iFrame.
      ** iIntros "(?&?)"; by iFrame.
    * iDestruct "H" as "(HΦ&[>HNC|>Htok'])"; last first.
      { iExFalso. iApply (Tok_Tok with "[$]"). }
      iDestruct ("Hwand" with "[$]") as "(Hwp&_)".
      iMod ("Hclo" with "[HNC Htok]").
      { iNext. iLeft. iFrame. }
      iMod ("Hwp") as (k) "Hwp". iModIntro. iExists k. iIntros "HNC".
      iSpecialize ("Hwp" with "[$]").
      destruct (to_val e) as [|].
      { by iMod "Hwp" as "($&_)". }
      iIntros (????) "H".
      iMod ("Hwp" with "H") as "($&H)".
      iModIntro. iIntros.
      iMod ("H" with "[//]") as "H". iModIntro.
      iNext. iMod "H" as "(Hσ & H & Hfork)". iModIntro.
      iFrame.
      iApply (wpc_strong_mono with "H"); eauto.
      iSplit.
      ** iIntros (?) "(?&?)"; by iFrame.
      ** iIntros "(?&?)"; by iFrame.
Qed.


(*
Lemma wp_wpc_inv (N: namespace) s E e Φ Φc :
  inv N Φc ∗ WP e @ s ; E {{ Φ }} ⊢ WPC e @ s ; E ; ∅ {{ Φ }} {{ ▷ Φc }}.
Proof.
  iIntros "(#Hinv&H)". iDestruct (wp_wpc with "H") as "H". iApply wpc_inv; by iFrame.
Qed.
*)

Lemma wpc_value s E1 E2 Φ Φc v :
  E1 ⊆ E2 →
  (|={E1}=> Φ v) ∧ (|={E1, E2}=> Φc) ⊢ WPC of_val v @ O; s; E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  rewrite wpc_unfold /wpc_pre to_of_val. iIntros (?). iApply and_mono; auto.
  - iIntros "H". iIntros. iMod "H". iModIntro. iExists O. iIntros; by iFrame.
  - iIntros "H". iIntros. rewrite NCO. iMod "H". iModIntro. iSplitL ""; first by eauto. iMod (fupd_intro_mask' _ E1) as "Hclo"; auto. iModIntro.
    iIntros. iMod "Hclo". iFrame. eauto.
Qed.

(*
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

Lemma wpc_fupd s E1 E2 e Φ Φc:
  ( WPC e @ s; E1 ; E2 {{ v, |={E1}=> Φ v }} {{ Φc }}) ⊢ WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }}.
Proof. iIntros "H". iApply (wpc_strong_mono with "H"); auto. Qed.

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
*)

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
(*
Lemma wpc_mono s E1 E2 e Φ Ψ Φc Ψc :
  (∀ v, Φ v ⊢ Ψ v) → (Φc ⊢ Ψc) → WPC e @ s; E1 ; E2 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; E1; E2 {{ Ψ }} {{ Ψc }}.
Proof.
  iIntros (HΦ HΦc) "H"; iApply (wpc_strong_mono with "H"); auto.
  iSplit.
  - iIntros (v) "?". by iApply HΦ.
  - iIntros "?". by iApply HΦc.
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
*)
