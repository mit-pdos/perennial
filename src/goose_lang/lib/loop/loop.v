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
  wp_rec.
  wp_pures.
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
    wp_pures.
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

Theorem wp_for_breakCond (I breakCond: iProp Σ) (body: val) :
  {{{ I }}}
    body #()
  {{{ r, RET #r; I ∗ (⌜r = false⌝ -∗ breakCond) }}} -∗
  {{{ I }}}
    (for: (λ: <>, #true)%V ; (λ: <>, Skip)%V :=
       body)
  {{{ RET #(); I ∗ breakCond }}}.
Proof.
  iIntros "#Hbody".
  iIntros "!>" (Φ) "IH HΦ".
  wp_apply (wp_forBreak
              (λ continue, if continue then I else (I ∗ breakCond)%I)
           with "[] [$IH]").
  - clear Φ.
    iIntros "!>" (Φ) "IH HΦ".
    wp_apply ("Hbody" with "IH").
    iIntros (r) "[HI Hbreak]".
    iApply "HΦ".
    destruct r; iFrame "HI".
    iApply "Hbreak"; auto.
  - iApply "HΦ".
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
  uint.Z start <= uint.Z max ->
  (∀ (i:u64),
      {{{ I i ∗ l ↦[uint64T] #i ∗ ⌜uint.Z i < uint.Z max⌝ }}}
        body #() @ stk; E
      {{{ RET #true; I (word.add i (W64 1)) ∗ l ↦[uint64T] #i }}}) -∗
  {{{ I start ∗ l ↦[uint64T] #start }}}
    (for: (λ:<>, #max > ![uint64T] #l)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l + #1)%V :=
       body) @ stk; E
  {{{ RET #(); I max ∗ l ↦[uint64T] #max }}}.
Proof.
  iIntros (Hstart_max) "#Hbody".
  iIntros (Φ) "!> (H0 & Hl) HΦ".
  rewrite /For /Continue.
  wp_rec.
  wp_pures.
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  remember start as x.
  assert (uint.Z start <= uint.Z x <= uint.Z max) as Hbounds by (subst; word).
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
    wp_store. wp_pures.
    iApply ("IH" with "[] HIx Hl").
    { word. }
    iFrame.
  - wp_pures.
    assert (uint.Z x = uint.Z max) by word.
    apply word.unsigned_inj in H; subst.
    iApply ("HΦ" with "[$]").
Qed.

Theorem wp_forUpto' (I: u64 → iProp Σ) stk E (start max:u64) (l:loc) (body: val) :
  ∀ Φ,
  l ↦[uint64T] #start ∗ ⌜uint.Z start ≤ uint.Z max⌝ ∗ I start -∗
  □(∀ (i: w64) Φ', I i ∗ l ↦[uint64T] #i ∗ ⌜uint.Z i < uint.Z max⌝ -∗
      ▷ (I (word.add i (W64 1)) ∗ l ↦[uint64T] #i -∗ Φ' #true) -∗
      WP body #() @ stk; E {{ Φ' }}) -∗
  ▷ (I max ∗ l ↦[uint64T] #max -∗ Φ #())%V -∗
  WP (for: (λ:<>, #max > ![uint64T] #l)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l + #1)%V :=
      body)%V @ stk; E {{ Φ }}.
Proof.
  iIntros (Φ) "(l & %Hstart & Istart) #IH HΦ".
  wp_apply (wp_forUpto I with "[] [$l $Istart] [$HΦ]").
  - auto.
  - clear Φ.
    iIntros (i Φ) "!> Hpre HΦ".
    iApply ("IH" with "[$Hpre] [$HΦ]").
Qed.

Lemma wp_forDec (I: u64 -> iProp Σ) stk E (start:u64) (l:loc) (body: val) :
  (∀ (i:u64),
      {{{ I i ∗ l ↦[uint64T] #i ∗ ⌜uint.Z 0 < uint.Z i <= uint.Z start⌝ }}}
        body #() @ stk; E
      {{{ RET #true; I (word.sub i (W64 1)) ∗ l ↦[uint64T] #i }}}) -∗
  {{{ I start ∗ l ↦[uint64T] #start }}}
    (for: (λ:<>, ![uint64T] #l > #0)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l - #1)%V :=
       body) @ stk; E
  {{{ RET #(); I (W64 0) ∗ l ↦[uint64T] #0 }}}.
Proof.
  iIntros "#Hbody".
  iIntros (Φ) "!> (HI & Hl) HΦ".
  rewrite /For /Continue.
  wp_rec.
  wp_pures.
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  assert (∃ x, start = x) as [? Heqx] by naive_solver.
  iEval (rewrite Heqx) in "HI Hl".
  assert (uint.Z 0 <= uint.Z x <= uint.Z start) as Hbounds by (subst; word).
  clear Heqx.
  iLöb as "IH" forall (x Hbounds).
  wp_load.
  wp_bind (If _ _ _).
  wp_if_destruct.
  - wp_apply ("Hbody" with "[$HI $Hl]").
    { iPureIntro; lia. }
    iIntros "[HI Hl]".
    wp_load. wp_store.
    wp_pures. iApply ("IH" with "[] HI Hl"); [word|].
    iFrame.
  - assert (uint.Z x = uint.Z 0) by word.
    apply word.unsigned_inj in H; subst.
    wp_pures. iApply ("HΦ" with "[$]").
Qed.

Local Hint Extern 2 (envs_entails _ (∃ i, ?I i ∗ ⌜_⌝)%I) =>
iExists _; iFrame; word : core.

Theorem wpc_forBreak_cond' (I: bool -> iProp Σ) Ic Φ Φc stk E1 (cond body: val) :
  (∀ b, I b -∗ Ic) -∗
  (Ic -∗ Φc) ∧ ▷ (I false -∗ Φ #()) -∗
  □ (I true -∗
     WPC if: cond #() then body #() else #false @ stk; E1
     {{ v, ∃ b : bool, ⌜ v = #b ⌝ ∧ I b }}
     {{ Ic }}) -∗
  I true -∗
  WPC (for: cond; (λ: <>, (λ: <>, #())%V #())%V := body) @ stk; E1
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

Theorem wpc_forBreak_cond (I: bool -> iProp Σ) Ic stk E1 (cond body: val) :
  (∀ b, I b -∗ Ic) →
  {{{ I true }}}
    if: cond #() then body #() else #false @ stk; E1
  {{{ r, RET #r; I r }}}
  {{{ Ic }}} -∗
  {{{ I true }}}
    (for: cond; (λ: <>, (λ: <>, #())%V #())%V :=
       body) @ stk; E1
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

Theorem wpc_forBreak_cond_2 (P: iProp Σ) stk E (cond body: goose_lang.val) (Φ : goose_lang.val → iProp Σ) (Φc: iProp Σ) :
  P -∗
  (P -∗ Φc) -∗
  □ (P -∗
      WPC if: cond #() then body #() else #false @ stk; E
      {{ v, ⌜v = #true⌝ ∗ P ∨ ⌜v = #false⌝ ∗ (Φ #() ∧ Φc) }} {{ Φc }} ) -∗
  WPC (for: cond; (λ: <>, Skip)%V := body) @ stk; E {{ Φ }} {{ Φc }}.
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

Theorem wpc_forUpto (I I': u64 -> iProp Σ) stk E1 (start max:u64) (l:loc) (body: val) :
  uint.Z start <= uint.Z max ->
  (∀ (i:u64), ⌜uint.Z start ≤ uint.Z i ≤ uint.Z max⌝ -∗ I i -∗ I' i) →
  (∀ (i:u64),
      {{{ I i ∗ l ↦[uint64T] #i ∗ ⌜uint.Z i < uint.Z max⌝ }}}
        body #() @ stk; E1
      {{{ RET #true; I (word.add i (W64 1)) ∗ l ↦[uint64T] #i }}}
      {{{ I' i ∨ I' (word.add i (W64 1)) }}}) -∗
  {{{ I start ∗ l ↦[uint64T] #start }}}
    (for: (λ:<>, #max > ![uint64T] #l)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l + #1)%V :=
       body) @ stk; E1
  {{{ RET #(); I max ∗ l ↦[uint64T] #max }}}
  {{{ ∃ (i:u64), I' i ∗ ⌜uint.Z start <= uint.Z i <= uint.Z max⌝ }}}.
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
  assert (uint.Z start <= uint.Z x <= uint.Z max) as Hbounds by (subst; word).
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
      {word. }
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
    { word. }
    iSplit.
    + iLeft in "HΦ".
      iIntros "HIx".
      iApply "HΦ".
      iDestruct "HIx" as (x') "[HI %]".
      iExists _; iFrame.
      iPureIntro; revert H; word.
    + iRight in "HΦ".
      iFrame.
  - assert (uint.Z x = uint.Z max) by word.
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
