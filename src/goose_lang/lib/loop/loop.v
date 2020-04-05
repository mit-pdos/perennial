From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode.
From Perennial.goose_lang.lib Require Export typed_mem loop.impl.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} `{!crashG Σ}.
Context {ext_ty: ext_types ext}.

Theorem wp_forBreak (I X: iProp Σ) stk E (body: val) :
  {{{ I }}}
    body #() @ stk; E
  {{{ r, RET #r; I ∗ ⌜r=true⌝ ∨ X ∗ ⌜r=false⌝ }}} -∗
  {{{ I }}}
    (for: (λ: <>, #true)%V ; (λ: <>, (λ: <>, #())%V #())%V :=
       body) @ stk; E
  {{{ RET #(); X }}}.
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
  wp_bind (body _).
  iApply "Hbody1".
  iNext.
  iIntros (r) "Hr".
  iDestruct "Hr" as "[[I %] | [X %]]"; subst.
  - iDestruct ("IH" with "I HΦ") as "IH1".
    wp_let.
    wp_if.
    wp_lam.
    wp_lam.
    wp_pure (Rec _ _ _).
    wp_lam.
    iApply "IH1".
  - wp_pures.
    iApply "HΦ".
    iApply "X".
Qed.

Theorem wp_forBreak' (I: bool -> iProp Σ) stk E (body: val) :
  {{{ I true }}}
    body #() @ stk; E
  {{{ r, RET #r; I r }}} -∗
  {{{ I true }}}
    (for: (λ: <>, #true)%V ; (λ: <>, (λ: <>, #())%V #())%V :=
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

Local Opaque load_ty store_ty.

Theorem wp_forUpto (I: u64 -> iProp Σ) stk E (start max:u64) (l:loc) (body: val) :
  int.val start <= int.val max ->
  (∀ (i:u64),
      {{{ I i ∗ l ↦[uint64T] #i ∗ ⌜int.val i < int.val max⌝ }}}
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
  assert (int.val start <= int.val x <= int.val max) as Hbounds by (subst; word).
  clear Heqx Hstart_max.
  iDestruct "H0" as "HIx".
  iLöb as "IH" forall (x Hbounds).
  wp_pures.
  wp_load.
  wp_pures.
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
  - assert (int.val x = int.val max) by word.
    apply word.unsigned_inj in H; subst.
    iApply ("HΦ" with "[$]").
Qed.

Theorem wpc_forUpto (I: u64 -> iProp Σ) stk k E1 E2 (start max:u64) (l:loc) (body: val) :
  int.val start <= int.val max ->
  (∀ (i:u64),
      {{{ I i ∗ l ↦[uint64T] #i ∗ ⌜int.val i < int.val max⌝ }}}
        body #() @ stk; k; E1; E2
      {{{ RET #true; I (word.add i (U64 1)) ∗ l ↦[uint64T] #i }}}
      {{{ I i ∨ I (word.add i (U64 1)) }}}) -∗
  {{{ I start ∗ l ↦[uint64T] #start }}}
    (for: (λ:<>, #max > ![uint64T] #l)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l + #1)%V :=
       body) @ stk; k; E1; E2
  {{{ RET #(); I max ∗ l ↦[uint64T] #max }}}
  {{{ ∃ (i:u64), I i ∗ ⌜int.val start <= int.val i <= int.val max⌝ }}}.
Proof.
  iIntros (Hstart_max) "#Hbody".
  iIntros (Φ Φc) "!> (H0 & Hl) HΦ".
  rewrite /For /Continue.
  wpc_rec Hcrash.
  { crash_case.
    iExists _; iFrame.
    iPureIntro; word. }
  wpc_let Hcrash.
  wpc_let Hcrash.
  wpc_pure (Rec _ _ _) Hcrash.
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  remember start as x.
  assert (int.val start <= int.val x <= int.val max) as Hbounds by (subst; word).
  clear Heqx Hstart_max.
  iDestruct "H0" as "HIx".
  clear Hcrash.
  iLöb as "IH" forall (x Hbounds).
  wpc_pures.
  { iExists _; iFrame.
    iPureIntro; word. }
  wpc_bind (load_ty _ _).
  wpc_frame "HIx HΦ".
  { iIntros "(HIx&HΦ)".
    crash_case.
    iExists _; iFrame.
    iPureIntro; word. }
  wp_load.
  iIntros "(HIx&HΦ)".
  wpc_pures.
  { iExists _; iFrame.
    iPureIntro; word. }
  wpc_if_destruct.
  - wpc_pures.
    { iExists _; iFrame.
      iPureIntro; word. }
    wpc_apply ("Hbody" with "[$HIx $Hl]").
    { iPureIntro; lia. }
    iSplit.
    { iIntros "[IH1 | IH2]"; crash_case.
      - iExists _; iFrame; iPureIntro; word.
      - iExists _; iFrame; iPureIntro; word. }
    iIntros "!> [HIx Hl]".
    wpc_pures.
    { iExists _; iFrame.
      iPureIntro; word. }
    wpc_bind (store_ty _ _).
    wpc_frame "HIx HΦ".
    { iIntros "(HIx&HΦ)".
      crash_case.
      iExists _; iFrame.
      iPureIntro; word. }
    wp_load.
    wp_store.
    iIntros "(HIx&HΦ)".
    wpc_pure _ Hcrash.
    { crash_case.
      iExists _; iFrame.
      iPureIntro; word. }
    wpc_pure _ Hcrash.
    iApply ("IH" with "[] HIx Hl").
    { iPureIntro; word. }
    iSplit.
    + iIntros "HIx".
      iDestruct "HIx" as (x') "[HI %]".
      crash_case.
      iExists _; iFrame.
      iPureIntro; revert H; word.
    + iRight in "HΦ".
      iFrame.
  - assert (int.val x = int.val max) by word.
    apply word.unsigned_inj in H; subst.
    wpc_pures.
    { iExists _; iFrame; iPureIntro; word. }
    iApply ("HΦ" with "[$]").
Qed.

End goose_lang.
