From iris.proofmode Require Import reduction monpred.
From Perennial.Helpers Require Import ipm NamedProps.

From Perennial.goose_lang Require Import lifting.

Section goose_lang.
Context `{ffi_semantics: ext_semantics}.
Context `{!ffi_interp ffi}.

(*
Definition post_crash `{hG: !heapG Σ} (P: forall {hG': heapG Σ}, iProp Σ) : iProp Σ :=
  (∀ σ σ' hG', ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ (heapG_ffiG (hG := hG')) σ' -∗
                             @P hG').
*)

Definition post_crash {Σ} (P: heapG Σ → iProp Σ) `{hG: !heapG Σ}  : iProp Σ :=
  (∀ σ σ' hG', ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ (heapG_ffiG (hG := hG')) σ' -∗
                             (P hG')).

(*
Definition post_crash `{hG: !heapG Σ} (P: forall {hG': heapG Σ}, iProp Σ) : iProp Σ :=
  (∀ σ σ' new, ffi_crash_rel Σ hG σ (ffi_update Σ hG new) σ' -∗
                             @P (ffi_update Σ hG new)).
*)

Class IntoCrash {Σ} `{!heapG Σ} (P: iProp Σ) (Q: heapG Σ → iProp Σ) :=
  into_crash : P -∗ post_crash (Σ := Σ) (λ hG', Q hG').

Section post_crash_prop.
Context `{hG: !heapG Σ}.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.

Existing Instances ffi_crash_rel_pers.

Lemma post_crash_intro Q:
  (⊢ Q) →
  (⊢ post_crash (λ _, Q)).
Proof. iIntros (Hmono). iIntros (???) "#Hrel". iApply Hmono. Qed.

Lemma post_crash_mono P Q:
  (∀ hG, P hG -∗ Q hG) →
  post_crash P -∗ post_crash Q.
Proof.
  iIntros (Hmono) "HP". iIntros (???) "#Hrel".
  iApply Hmono. iApply "HP"; eauto.
Qed.

Lemma post_crash_pers P Q:
  (P -∗ post_crash Q) →
  □ P -∗ post_crash (λ hG, □ Q hG).
Proof.
  iIntros (Hmono) "#HP". iIntros (???) "#Hrel".
  iModIntro. iApply Hmono; eauto.
Qed.

Lemma post_crash_sep P Q:
  post_crash P ∗ post_crash Q -∗ post_crash (λ hG, P hG ∗ Q hG).
Proof.
  iIntros "(HP&HQ)". iIntros (???) "#Hrel".
  iDestruct ("HP" with "[$]") as "$".
  iDestruct ("HQ" with "[$]") as "$".
Qed.

Lemma post_crash_or P Q:
  post_crash P ∨ post_crash Q -∗ post_crash (λ hG, P hG ∨ Q hG).
Proof.
  iIntros "[HP|HQ]"; iIntros (???) "#Hrel".
  - iLeft. by iApply "HP".
  - iRight. by iApply "HQ".
Qed.

Lemma post_crash_and P Q:
  post_crash P ∧ post_crash Q -∗ post_crash (λ hG, P hG ∧ Q hG).
Proof.
  iIntros "HPQ"; iIntros (???) "#Hrel".
  iSplit.
  - iDestruct "HPQ" as "(HP&_)". by iApply "HP".
  - iDestruct "HPQ" as "(_&HQ)". by iApply "HQ".
Qed.

Lemma post_crash_pure (P: Prop) :
  P → ⊢ post_crash (λ _, ⌜ P ⌝).
Proof.
  iIntros (????); eauto.
Qed.

Lemma post_crash_nodep (P: iProp Σ) :
  P -∗ post_crash (λ _, P).
Proof. iIntros "HP". iIntros (???); eauto. Qed.

Lemma post_crash_exists {A} P Q:
  (∀ (x: A), P hG x -∗ post_crash (λ hG, Q hG x)) -∗
  (∃ x, P hG x) -∗ post_crash (λ hG, ∃ x, Q hG x).
Proof.
  iIntros "Hall HP". iIntros (???) "#Hrel".
  iDestruct "HP" as (x) "HP".
  iExists x. iApply ("Hall" with "[$] [$]").
Qed.

Lemma post_crash_forall {A} P Q:
  (∀ (x: A), P hG x -∗ post_crash (λ hG, Q hG x)) -∗
  (∀ x, P hG x) -∗ post_crash (λ hG, ∀ x, Q hG x).
Proof.
  iIntros "Hall HP". iIntros (???) "#Hrel".
  iIntros (?). iApply ("Hall" with "[HP] [$]"). iApply "HP".
Qed.

Lemma post_crash_exists_intro {A} P (x: A):
  (∀ (x: A), P hG x -∗ post_crash (λ hG, P hG x)) -∗
  P hG x -∗ post_crash (λ hG, ∃ x, P hG x).
Proof.
  iIntros "Hall HP". iIntros (???) "#Hrel".
  iExists x. iApply ("Hall" with "[$] [$]").
Qed.

Global Instance from_exist_post_crash {A} (Φ: heapG Σ → iProp Σ) (Ψ: heapG Σ → A → iProp Σ)
  {Himpl: ∀ hG, FromExist (Φ hG) (λ x, Ψ hG x)} :
  FromExist (post_crash (λ hG, Φ hG)) (λ x, post_crash (λ hG, Ψ hG x)).
Proof.
  hnf; iIntros "H".
  iDestruct "H" as (x) "H".
  rewrite /post_crash.
  iIntros (σ σ' hG') "Hrel".
  iSpecialize ("H" with "Hrel").
  iExists x; iFrame.
Qed.

Lemma post_crash_named P name:
  named name (post_crash (λ hG, P hG)) -∗
  post_crash (λ hG, named name (P hG)).
Proof. rewrite //=. Qed.

End post_crash_prop.

Section IntoCrash.

  Context `{hG: !heapG Σ}.
  Global Instance sep_into_crash P P' Q Q':
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (P ∗ Q)%I (λ hG, P' hG ∗ Q' hG)%I.
  Proof.
    iIntros (H1 H2). rewrite /IntoCrash.
    rewrite (@into_crash _ _ P).
    rewrite (@into_crash _ _ Q).
    rewrite post_crash_sep //.
  Qed.

  Global Instance or_into_crash P P' Q Q':
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (P ∨ Q)%I (λ hG, P' hG ∨ Q' hG)%I.
  Proof.
    iIntros (H1 H2). rewrite /IntoCrash.
    rewrite (@into_crash _ _ P).
    rewrite (@into_crash _ _ Q).
    rewrite post_crash_or //.
  Qed.

  Global Instance and_into_crash P P' Q Q':
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (P ∧ Q)%I (λ hG, P' hG ∧ Q' hG)%I.
  Proof.
    iIntros (H1 H2). rewrite /IntoCrash.
    rewrite (@into_crash _ _ P).
    rewrite (@into_crash _ _ Q).
    rewrite post_crash_and //.
  Qed.

  (* XXX: probably should rephrase in terms of IntoPure *)
  Global Instance pure_into_crash (P: Prop) :
    IntoCrash (⌜ P ⌝%I) (λ _, ⌜ P ⌝%I).
  Proof. rewrite /IntoCrash. iIntros "%". by iApply post_crash_pure. Qed.

  Global Instance exist_into_crash {A} Φ Ψ:
    (∀ x : A, IntoCrash (Φ x) (λ hG, Ψ hG x)) →
    IntoCrash (∃ x, Φ x)%I (λ hG, (∃ x, Ψ hG x)%I).
  Proof.
    rewrite /IntoCrash.
    iIntros (?) "H". iDestruct "H" as (?) "HΦ". iPoseProof (H with "[$]") as "HΦ".
    iApply (post_crash_mono with "HΦ"). eauto.
  Qed.

  Global Instance forall_into_crash {A} Φ Ψ:
    (∀ x : A, IntoCrash (Φ x) (λ hG, Ψ hG x)) →
    IntoCrash (∀ x, Φ x)%I (λ hG, (∀ x, Ψ hG x)%I).
  Proof.
    rewrite /IntoCrash.
    iIntros (?) "H". iApply post_crash_forall; last eauto. iIntros (?). iApply H.
  Qed.

  (*
  Global Instance post_crash_into_crash P:
    IntoCrash (post_crash P) P.
  Proof. rewrite /IntoCrash. by iApply post_crash_mono. Qed.
   *)

  Lemma into_crash_proper P P' Q Q':
    IntoCrash P Q →
    (P ⊣⊢ P') →
    (∀ hG, Q hG ⊣⊢ Q' hG) →
    IntoCrash P' Q'.
  Proof.
    rewrite /IntoCrash.
    iIntros (HD Hwand1 Hwand2) "HP".
    iApply post_crash_mono; last first.
    { iApply HD. iApply Hwand1. eauto. }
    intros. simpl. by rewrite Hwand2.
  Qed.

  Global Instance big_sepL_into_crash:
    ∀ (A : Type) Φ (Ψ : heapG Σ → nat → A → iProp Σ) (l : list A),
    (∀ (k : nat) (x : A), IntoCrash (Φ k x) (λ hG, Ψ hG k x)) →
    IntoCrash ([∗ list] k↦x ∈ l, Φ k x)%I (λ hG, [∗ list] k↦x ∈ l, Ψ hG k x)%I.
  Proof.
    intros.
    cut (∀ n, IntoCrash ([∗ list] k↦x ∈ l, Φ (n + k)%nat x)%I
                        (λ hG, [∗ list] k↦x ∈ l, Ψ hG (n + k)%nat x)%I).
    { intros Hres. specialize (Hres O). eauto. }
    induction l => n.
    - rewrite //=. apply _.
    - rewrite //=. apply sep_into_crash; eauto.
      eapply into_crash_proper; first eapply (IHl (S n)).
      * intros. setoid_rewrite Nat.add_succ_r. setoid_rewrite <-Nat.add_succ_l. eauto.
      * intros. setoid_rewrite Nat.add_succ_r. setoid_rewrite <-Nat.add_succ_l. eauto.
  Qed.

  Global Instance big_sepM_into_crash `{Countable K} :
    ∀ (A : Type) Φ (Ψ : heapG Σ → K → A → iProp Σ) (m : gmap K A),
    (∀ (k : K) (x : A), IntoCrash (Φ k x) (λ hG, Ψ hG k x)) →
    IntoCrash ([∗ map] k↦x ∈ m, Φ k x)%I (λ hG, [∗ map] k↦x ∈ m, Ψ hG k x)%I.
  Proof.
    intros. induction m using map_ind.
    - eapply (into_crash_proper True%I _ (λ _, True%I)).
      { apply _. }
      * rewrite big_sepM_empty; eauto.
      * intros. rewrite big_sepM_empty; eauto.
    - eapply (into_crash_proper (Φ i x ∗ [∗ map] k↦x0 ∈ m, Φ k x0) _
                                (λ _, (Ψ _ i x ∗ [∗ map] k↦x0 ∈ m, Ψ _ k x0)%I)).
      { apply _. }
      * rewrite big_sepM_insert //=.
      * intros. rewrite big_sepM_insert //=.
  Qed.

  Global Instance big_sepS_into_crash `{Countable K} :
    ∀ Φ (Ψ : heapG Σ → K → iProp Σ) (m : gset K),
    (∀ (k : K), IntoCrash (Φ k) (λ hG, Ψ hG k)) →
    IntoCrash ([∗ set] k ∈ m, Φ k)%I (λ hG, [∗ set] k ∈ m, Ψ hG k)%I.
  Proof.
    intros. induction m as [|i m ? IH] using set_ind_L => //=.
    - eapply (into_crash_proper True%I _ (λ _, True%I)).
      { apply _. }
      * rewrite big_sepS_empty; eauto.
      * intros. rewrite big_sepS_empty; eauto.
    - eapply (into_crash_proper (Φ i ∗ [∗ set] k ∈ m, Φ k) _
                                (λ _, (Ψ _ i ∗ [∗ set] k ∈ m, Ψ _ k)%I)).
      { apply _. }
      * rewrite big_sepS_insert //=.
      * intros. rewrite big_sepS_insert //=.
  Qed.

  Lemma into_crash_post_crash_frame_l P P' `{!IntoCrash P P'} Q:
    P -∗ post_crash Q -∗ post_crash (λ hG', P' hG' ∗ Q hG').
  Proof. iIntros "HP HQ". rewrite (@into_crash _ _ P). iApply post_crash_sep. iFrame. Qed.

  Lemma into_crash_post_crash_frame_r P P' `{!IntoCrash P P'} Q:
    post_crash Q -∗ P  -∗ post_crash (λ hG', Q hG' ∗ P' hG').
  Proof. iIntros "HP HQ". rewrite (@into_crash _ _ P). iApply post_crash_sep. iFrame. Qed.

End IntoCrash.
End goose_lang.

Lemma modus_ponens {Σ} (P Q: iProp Σ)  : P -∗ (P -∗ Q) -∗ Q.
Proof. iIntros "HP Hwand". by iApply "Hwand". Qed.

Ltac crash_env Γ :=
  match Γ with
    | environments.Enil => idtac
    | environments.Esnoc ?Γ' ?id (post_crash _) => crash_env Γ'
    | environments.Esnoc ?Γ' ?id ?A => first [ iEval (rewrite (@into_crash _ _ _ _ _ A) )in id || iClear id ] ; crash_env Γ'
  end.

Ltac crash_ctx :=
  match goal with
  | [ |- environments.envs_entails ?Γ _] =>
    let spatial := pm_eval (environments.env_spatial Γ) in
    let intuit := pm_eval (environments.env_intuitionistic Γ) in
    crash_env spatial; crash_env intuit
  end.

Ltac iCrash :=
  crash_ctx;
  iApply (modus_ponens with "[-]"); [ iNamedAccu | ];
  rewrite ?post_crash_named ?post_crash_sep; iApply post_crash_mono;
  intros; simpl;
  let H := iFresh in iIntros H; iNamed H.

Section goose_lang.
Context `{ffi_semantics: ext_semantics}.
Context `{!ffi_interp ffi}.
Context {Σ: gFunctors}.
Section modality_alt.
  Context `{hG: !heapG Σ}.
  Context `{Hi1: !IntoCrash P P'}.
  Context `{Hi2: !IntoCrash Q Q'}.
  Lemma test R :
    P -∗ Q -∗ R -∗ post_crash (λ hG', P' hG' ∗ Q' hG').
  Proof.
    iIntros "HP HQ HR". iCrash. iFrame.
  Qed.

End modality_alt.

End goose_lang.
