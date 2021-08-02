From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode.
From Perennial.goose_lang.lib Require Export typed_mem loop.impl.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Theorem wp_forBreak_cond (I: bool -> iProp Σ) stk E (cond body: val) :
  {{{ I true }}}
    if: cond #() then body #() else #false @ stk; E
  {{{ r, RET #r; I r }}} -∗
  {{{ I true }}}
    (for: cond; (λ: <>, Skip)%V :=
       body) @ stk; E
  {{{ RET #(); I false }}}.
Proof.
  iIntros "#Hbody".
  iIntros (Φ) "!> I HΦ".
  rewrite /For.
  wp_lam.
  wp_let.
  wp_let.
  wp_pure (Rec _ _ _).
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  iLöb as "IH".
  wp_pures.
  iDestruct ("Hbody" with "I") as "Hbody1".
  wp_apply "Hbody1".
  iIntros (r) "Hr".
  destruct r.
  - iDestruct ("IH" with "Hr HΦ") as "IH1".
    wp_let.
    wp_if.
    wp_lam.
    wp_lam.
    wp_pure (Rec _ _ _).
    wp_lam.
    iApply "IH1".
  - wp_pures.
    iApply "HΦ".
    iApply "Hr".
Qed.

Theorem wp_forBreak (I: bool -> iProp Σ) stk E (body: val) :
  {{{ I true }}}
    body #() @ stk; E
  {{{ r, RET #r; I r }}} -∗
  {{{ I true }}}
    (for: (λ: <>, #true)%V ; (λ: <>, Skip)%V :=
       body) @ stk; E
  {{{ RET #(); I false }}}.
Proof.
  iIntros "#Hbody".
  iIntros (Φ) "!> I HΦ".
  wp_apply (wp_forBreak_cond I with "[] I HΦ").
  iIntros "!>" (Φ') "I HΦ".
  wp_pures.
  wp_apply ("Hbody" with "[$]").
  iFrame.
Qed.


Theorem wp_forBreak_cond' (P: iProp Σ) stk E (cond body: val) (Φ : val → iProp Σ) :
  P -∗
  □ (P -∗
      WP if: cond #() then body #() else #false @ stk; E
      {{ v, ⌜v = #true⌝ ∗ P ∨ ⌜v = #false⌝ ∗ Φ #() }}) -∗
  WP (for: cond; (λ: <>, Skip)%V := body) @ stk; E {{ Φ }}.
Proof.
  iIntros "HP #Hloop".
  iApply (wp_forBreak_cond (λ b, ⌜b = true⌝ ∗ P ∨ ⌜b = false⌝ ∗ Φ #()) with "[] [-]")%I.
  - iIntros "!#" (Φ') "Hinv HΦ'".
    iDestruct "Hinv" as "[[_ HP]|[% _]]"; last done.
    iSpecialize ("Hloop" with "HP").
    iApply (wp_wand with "[HΦ' Hloop]").
    { iApply wp_frame_step_l'. iFrame. }
    iIntros (v) "[HP [[-> Hpost]|[-> Hpost]]]".
    + iApply "HP". iLeft. eauto.
    + iApply "HP". iRight. eauto.
  - iLeft. eauto.
  - iNext. iIntros "[[% _]|[_ HΦ]]"; first done.
    eauto.
Qed.

Theorem wp_forBreak' (P: iProp Σ) stk E (body: val) (Φ : val → iProp Σ) :
  P -∗
  □ (P -∗
      WP body #() @ stk; E
      {{ v, ⌜v = #true⌝ ∗ P ∨ ⌜v = #false⌝ ∗ Φ #() }}) -∗
  WP (for: (λ: <>, #true)%V; (λ: <>, Skip)%V := body) @ stk; E {{ Φ }}.
Proof.
  iIntros "HP #Hloop". iApply (wp_forBreak_cond' with "HP").
  iIntros "!# HP". wp_pures. iApply "Hloop". done.
Qed.

Local Opaque load_ty store_ty.

Theorem wp_forUpto (I: u64 -> iProp Σ) stk E (start max:u64) (l:loc) (body: val) :
  int.Z start <= int.Z max ->
  (∀ (i:u64),
      {{{ I i ∗ l ↦[uint64T] #i ∗ ⌜int.Z i < int.Z max⌝ }}}
        body #() @ stk; E
      {{{ RET #true; I (word.add i (U64 1)) ∗ l ↦[uint64T] #i }}}) -∗
  {{{ I start ∗ l ↦[uint64T] #start }}}
    (for: (λ:<>, #max > ![uint64T] #l)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l + #1)%V :=
       body) @ stk; E
  {{{ RET #(); I max ∗ l ↦[uint64T] #max }}}.
Proof.
  iIntros (Hstart_max) "#Hbody".
  iIntros (Φ) "!> (H0 & Hl) HΦ".
  rewrite /For /Continue.
  wp_lam.
  wp_let.
  wp_let.
  wp_pure (Rec _ _ _).
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  remember start as x.
  assert (int.Z start <= int.Z x <= int.Z max) as Hbounds by (subst; word).
  clear Heqx Hstart_max.
  iDestruct "H0" as "HIx".
  iLöb as "IH" forall (x Hbounds).
  wp_pures.
  wp_load.
  wp_pures.
  wp_bind (If _ _ _).
  wp_if_destruct.
  - wp_apply ("Hbody" with "[$HIx $Hl]").
    { iPureIntro; lia. }
    iIntros "[HIx Hl]".
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    iApply ("IH" with "[] HIx Hl").
    { iPureIntro; word. }
    iFrame.
  - wp_pures.
    assert (int.Z x = int.Z max) by word.
    apply word.unsigned_inj in H; subst.
    iApply ("HΦ" with "[$]").
Qed.

Local Hint Extern 2 (envs_entails _ (∃ i, ?I i ∗ ⌜_⌝)%I) =>
iExists _; iFrame; iPureIntro; word : core.

Theorem wpc_forBreak_cond' (I: bool -> iProp Σ) Ic Φ Φc stk k E1 (cond body: val) :
  (∀ b, I b -∗ Ic) -∗
  (Ic -∗ Φc) ∧ ▷ (I false -∗ Φ #()) -∗
  □ (I true -∗
     WPC if: cond #() then body #() else #false @ stk; k; E1
     {{ v, ∃ b : bool, ⌜ v = #b ⌝ ∧ I b }}
     {{ Ic }}) -∗
  I true -∗
  WPC (for: cond; (λ: <>, (λ: <>, #())%V #())%V := body) @ stk; k; E1
  {{ Φ }}
  {{ Φc }}.
Proof.
  iIntros "HIc HΦ #Hbody I".
  rewrite /For.
  iCache with "HIc I HΦ".
  { iLeft in "HΦ". iDestruct ("HIc" with "[$]") as "HI". by iApply "HΦ". }
  wpc_pures.
  wpc_pures.
  { iLeft in "HΦ". iDestruct ("HIc" with "[$]") as "HI". by iApply "HΦ". }
  iLöb as "IH".
  wpc_bind_seq.
  iDestruct ("Hbody" with "I") as "Hbody1".
  iApply (wpc_strong_mono with "Hbody1"); try auto.
  iSplit; last first.
  { iLeft in "HΦ". iIntros "H". iModIntro.
    by iApply "HΦ". }
  iIntros (v) "H".
  iModIntro.
  iDestruct "H" as (b Heq) "I".
  iCache with "HIc I HΦ".
  { iLeft in "HΦ". iDestruct ("HIc" with "[$]") as "HI". by iApply "HΦ". }
  wpc_pures. wpc_pures.
  subst.
  destruct b.
  - wpc_pures.
    iApply ("IH" with "[$] [$] [$]").
  - wpc_pures.
    { iRight in "HΦ". by iApply "HΦ". }
Qed.

Theorem wpc_forBreak_cond (I: bool -> iProp Σ) Ic stk k E1 (cond body: val) :
  (∀ b, I b -∗ Ic) →
  {{{ I true }}}
    if: cond #() then body #() else #false @ stk; k; E1
  {{{ r, RET #r; I r }}}
  {{{ Ic }}} -∗
  {{{ I true }}}
    (for: cond; (λ: <>, (λ: <>, #())%V #())%V :=
       body) @ stk; k; E1
  {{{ RET #(); I false }}}
  {{{ Ic }}}.
Proof.
  iIntros (Hcrash) "#Hbody".
  iIntros (Φ Φc) "!> I HΦ".
  iApply (wpc_forBreak_cond' I Ic with "[] [$] [] [$]").
  { iIntros. by iApply Hcrash. }
  iModIntro. iIntros "HI".
  iApply ("Hbody" with "[$]").
  iSplit; eauto.
Qed.

Theorem wpc_forBreak_cond_2 (P: iProp Σ) stk k E (cond body: goose_lang.val) (Φ : goose_lang.val → iProp Σ) (Φc: iProp Σ) :
  P -∗
  (P -∗ Φc) -∗
  □ (P -∗
      WPC if: cond #() then body #() else #false @ stk; k; E
      {{ v, ⌜v = #true⌝ ∗ P ∨ ⌜v = #false⌝ ∗ (Φ #() ∧ Φc) }} {{ Φc }} ) -∗
  WPC (for: cond; (λ: <>, Skip)%V := body) @ stk; k ; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros "HP HΦc #Hbody".
  rewrite /For.
  iCache with "HP HΦc".
  { by iApply "HΦc". }
  wpc_pures.
  iLöb as "IH".
  wpc_bind_seq.
  iDestruct ("Hbody" with "HP") as "Hbody1".
  iApply (wpc_strong_mono with "Hbody1"); try auto.
  iSplit; last first.
  { iIntros. by iModIntro. }
  iIntros (v) "H".
  iModIntro.
  iDestruct "H" as "[[% H]|[% H]]"; subst.
  - iCache with "HΦc H".
    { iSpecialize ("HΦc" with "H"). done. }
    wpc_pures.
    wpc_pures.
    iApply ("IH" with "[$] [$]").
  - iCache with "H".
    { by iRight in "H". }
    wpc_pures.
    wpc_pures.
    by iLeft in "H".
Qed.

Theorem wpc_forUpto (I I': u64 -> iProp Σ) stk k E1 (start max:u64) (l:loc) (body: val) :
  int.Z start <= int.Z max ->
  (∀ (i:u64), ⌜int.Z start ≤ int.Z i ≤ int.Z max⌝ -∗ I i -∗ I' i) →
  (∀ (i:u64),
      {{{ I i ∗ l ↦[uint64T] #i ∗ ⌜int.Z i < int.Z max⌝ }}}
        body #() @ stk; k; E1
      {{{ RET #true; I (word.add i (U64 1)) ∗ l ↦[uint64T] #i }}}
      {{{ I' i ∨ I' (word.add i (U64 1)) }}}) -∗
  {{{ I start ∗ l ↦[uint64T] #start }}}
    (for: (λ:<>, #max > ![uint64T] #l)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l + #1)%V :=
       body) @ stk; k; E1
  {{{ RET #(); I max ∗ l ↦[uint64T] #max }}}
  {{{ ∃ (i:u64), I' i ∗ ⌜int.Z start <= int.Z i <= int.Z max⌝ }}}.
Proof.
  iIntros (Hstart_max Himpl) "#Hbody".
  iIntros (Φ Φc) "!> (H0 & Hl) HΦ".
  rewrite /For /Continue.
  wpc_rec Hcrash.
  {
    iDestruct (Himpl with "[%] H0") as "H0".
    { lia. }
    crash_case.
    iExists _; iFrame.
    auto.
  }
  clear Hcrash.
  wpc_pure1 Hcrash; auto.
  {
    iDestruct (Himpl with "[%] H0") as "H0".
    { lia. }
    crash_case.
    iExists _; iFrame.
    auto.
  }
  wpc_pure1 _; auto.
  wpc_pure1 _; auto.
  wpc_pure1 _; auto.
  wpc_pure (Rec _ _ _) Hcrash.
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  remember start as x.
  assert (int.Z start <= int.Z x <= int.Z max) as Hbounds by (subst; word).
  clear Heqx Hstart_max.
  iDestruct "H0" as "HIx".
  clear Hcrash.
  (iLöb as "IH" forall (x Himpl Hbounds)).
  iCache with "HΦ HIx".
  {
    iDestruct (Himpl with "[] [$]") as "?"; eauto.
    { iPureIntro; lia. }
    crash_case.
    iExists _; iFrame.
    iPureIntro. lia.
  }
  wpc_pures.
  wpc_pures.
  wpc_bind (load_ty _ _).
  wpc_frame.
  wp_load.
  iIntros "!> H". iNamed "H".
  wpc_pures.
  wpc_bind (If _ _ _).
  wpc_if_destruct; wpc_pures; auto; try (by (iDestruct (Himpl with "[$]") as "?"; eauto)).
  - wpc_apply ("Hbody" with "[$HIx $Hl]").
    { iPureIntro; lia. }
    iSplit.
    { iDestruct "HΦ" as "(HΦ&_)".  iIntros "[IH1 | IH2]"; iApply "HΦ"; auto. }
    iIntros "!> [HIx Hl]".
    iCache with "HΦ HIx".
    {
      iDestruct (Himpl with "[] [$]") as "?"; eauto.
      {iPureIntro; word. }
      crash_case.
      eauto.
    }
    wpc_pures.
    wpc_frame_seq.
    wp_load.
    wp_store.
    iModIntro. iNamed 1.
    wpc_pure1 Hcrash.
    { iFromCache. }
    wpc_pure1 Hcrash.
    iApply ("IH" with "[%] [] HIx Hl").
    { iIntros (i Hbound) "HIx".
      iDestruct (Himpl with "[%] HIx") as "$".
      revert Hbound; word. }
    { iPureIntro; word. }
    iSplit.
    + iLeft in "HΦ".
      iIntros "HIx".
      iApply "HΦ".
      iDestruct "HIx" as (x') "[HI %]".
      iExists _; iFrame.
      iPureIntro; revert H; word.
    + iRight in "HΦ".
      iFrame.
  - assert (int.Z x = int.Z max) by word.
    apply word.unsigned_inj in H; subst.
    iApply ("HΦ" with "[$]").
Qed.

End goose_lang.

(** Tactics for convenient loop reasoning *)
Ltac wp_forBreak_cond :=
  wp_bind (For _ _ _); iApply (wp_forBreak_cond' with "[-]");
  [ by iNamedAccu
  | iIntros "!# __CTX"; iNamed "__CTX" ].
Ltac wp_forBreak :=
  wp_bind (For _ _ _); iApply (wp_forBreak' with "[-]");
  [ by iNamedAccu
  | iIntros "!# __CTX"; iNamed "__CTX" ].
