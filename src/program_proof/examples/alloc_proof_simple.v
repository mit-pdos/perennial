From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import Map.

From Perennial.program_logic Require Export weakestpre post_expr.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.goose_lang Require Import proofmode wpc_proofmode notation crash_borrow.
From Perennial.base_logic Require Import lib.ghost_map.

From Goose.github_com.mit_pdos.perennial_examples Require Import alloc.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof.examples Require Import alloc_addrset.

Section goose.
Context `{!heapGS Σ}.

Let allocN := nroot.@"allocator".

Implicit Types (a: u64) (m: gmap u64 ()) (free: gset u64).
Implicit Types (P: gset u64 → iProp Σ).
Implicit Types (l:loc).

Definition allocator_linv P (mref: loc) free : iProp Σ :=
  "Hfreemap" ∷ is_addrset mref (free) ∗
  "HP" ∷ P free
.

Definition is_allocator (l: loc) P : iProp Σ :=
  ∃ (lref mref: loc),
    "#Hsplit" ∷ □ (∀ σ1 σ2, ⌜ σ1 ## σ2 ⌝ → P (σ1 ∪ σ2) -∗ post_expr ∅ (P σ1 ∗ P σ2)) ∗
    "#Hjoin" ∷ □ (∀ σ1 σ2, P σ1 -∗ P σ2 -∗ post_expr ∅ (P (σ1 ∪ σ2))) ∗
    "#m" ∷ readonly (l ↦[Allocator :: "m"] #lref) ∗
    "#free" ∷ readonly (l ↦[Allocator :: "free"] #mref) ∗
    "#His_lock" ∷ is_lock allocN #lref (∃ σ, "Hlockinv" ∷ allocator_linv P mref σ)
.

Global Instance is_allocator_Persistent l P :
  Persistent (is_allocator l P).
Proof. apply _. Qed.

Theorem wp_newAllocator mref (start sz: u64) used P E :
  uint.Z start + uint.Z sz < 2^64 →
  {{{
       □ (∀ σ1 σ2, ⌜ σ1 ## σ2 ⌝ → P (σ1 ∪ σ2) -∗ post_expr ∅ (P σ1 ∗ P σ2)) ∗
       □ (∀ σ1 σ2, P σ1 -∗ P σ2 -∗ post_expr ∅ (P (σ1 ∪ σ2))) ∗
       is_addrset mref used ∗
      let σ0 := (rangeSet (uint.Z start) (uint.Z sz)) ∖ used in
       ▷ P σ0 }}}
    New #start #sz #mref @ E
  {{{ l, RET #l; is_allocator l P }}}.
Proof.
  iIntros (Hoverflow Φ) "(#Hsplit&#Hjoin&Hused&HP) HΦ".
  wp_rec. wp_pures.
  wp_apply wp_freeRange; first by auto.
  iIntros (mref') "Hfree".
  wp_pures.
  wp_apply (wp_mapRemove with "[$Hfree $Hused]"); iIntros "(Hfree & Hused)".
  wp_apply wp_new_free_lock.
  iIntros (lk) "Hlock".
  rewrite -wp_fupd.
  wp_apply wp_allocStruct; auto.
  iIntros (l) "Hallocator".
  iDestruct (struct_fields_split with "Hallocator") as "(m&free&_)".
  iMod (readonly_alloc_1 with "m") as "#m".
  iMod (readonly_alloc_1 with "free") as "#free".
  iMod (alloc_lock allocN E _
                   (∃ σ, "Hlockinv" ∷ allocator_linv P mref' σ)%I
          with "[$Hlock] [-HΦ]") as "#Hlock".
  { iExists _; iFrame. }
  iModIntro.
  iApply ("HΦ" $! _).
  iExists _, _; iFrame "#".
Qed.

Lemma map_empty_difference `{Countable K} {V} (m: gmap K V) :
  ∅ ∖ m = ∅.
Proof.
  apply map_eq; intros.
  rewrite lookup_difference_None; eauto.
Qed.

Lemma set_empty_difference `{Countable K} (m: gset K) :
  ∅ ∖ m = ∅.
Proof.
  clear.
  set_solver.
Qed.

Theorem wp_Reserve l P :
  {{{ is_allocator l P }}}
    Allocator__Reserve #l
  {{{ a (ok: bool), RET (#a, #ok);
      if ok then P {[a]} else True%I }}}.
Proof.
  clear.
  iIntros (Φ) "Hinv HΦ"; iNamed "Hinv".
  wp_rec. wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "His_lock").
  iIntros "(His_locked & Hinner)"; iNamed "Hinner".
  iNamed "Hlockinv".
  wp_loadField.
  wp_apply (wp_findKey with "Hfreemap").
  iIntros (k ok) "[%Hk Hfreemap]".
  wp_pures.
  wp_loadField.
  iDestruct "Hfreemap" as (m') "[Hfreemap %Hdom]".
  wp_apply (wp_MapDelete with "Hfreemap"); iIntros "Hfreemap".
  wp_pures.
  wp_bind (struct.loadF _ _ _).
  destruct ok.
  - assert (σ = (σ ∖ {[k]}) ∪ {[k]}) as ->.
    { rewrite difference_union_L. set_solver. }
    iDestruct ("Hsplit" with "[] HP") as "Hpost".
    { iPureIntro. set_solver. }
    iApply (wpc_wp NotStuck _ _ _ True).
    iApply (post_expr_elim with "Hpost"); first set_solver+; auto.
    iApply wp_wpc.
    wp_loadField.
    iIntros "(HP&Hk)".
    wp_apply (release_spec with "[-HΦ Hk $His_lock $His_locked]").
    { iNext. iExists _; iFrame. rewrite /map_del dom_delete_L. iPureIntro; congruence. }
    wp_pures.
    iApply "HΦ"; by iFrame.
  - wp_loadField.
    wp_apply (release_spec with "[-HΦ $His_lock $His_locked]").
    { iNext. iExists _; iFrame. rewrite /map_del dom_delete_L. subst.
      iPureIntro. rewrite Hdom. set_solver. }
    wp_pures.
    iApply "HΦ"; by iFrame.
Qed.

Lemma gset_difference_difference `{Countable K} (A B C: gset K) :
  C ⊆ A →
  A ∖ (B ∖ C) = A ∖ B ∪ C.
Proof using.
  clear.
  intros.
  apply set_eq; intros k.
  rewrite !elem_of_difference.
  intuition.
  - destruct (decide (k ∈ C)); set_solver.
  - set_solver.
  - set_solver.
Qed.

Theorem wp_Free P l (a: u64) :
  {{{ is_allocator l P ∗ P {[a]} }}}
    Allocator__Free #l #a
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(Halloc&Ha) HΦ"; iNamed "Halloc".
  wp_rec. wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "His_lock").
  iIntros "(Hlocked&Hinv)"; iNamed "Hinv".
  iNamed "Hlockinv".
  wp_loadField.
  iDestruct "Hfreemap" as (m) "[Hfreemap %Hdom]".
  wp_apply (wp_MapInsert _ _ () with "Hfreemap"); first by auto.
  iIntros "Hfreemap".
  iAssert (is_addrset mref (σ ∪ {[a]})) with "[Hfreemap]" as "Hfreemap".
  { iExists _; iFrame.
    iPureIntro.
    rewrite /map_insert dom_insert_L.
    set_solver. }
  wp_pures.
  wp_bind (struct.loadF _ _ _).
  iDestruct ("Hjoin" with "HP [$]") as "Hpost".
  iApply (wpc_wp NotStuck _ _ _ True).
  iApply (post_expr_elim with "Hpost"); first set_solver+; auto.
  iApply wp_wpc.
  wp_loadField.
  iIntros "HP".
  wp_apply (release_spec with "[$His_lock $Hlocked Hfreemap HP]").
  { iExists _; iFrame "HP". eauto. }
  wp_pures.
  iApply ("HΦ" with "[$]").
Qed.

End goose.

Opaque crash_borrow.

Section crash.
Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

Implicit Types (a: u64) (m: gmap u64 ()) (free: gset u64).
Implicit Types (P: gset u64 → iProp Σ).
Implicit Types (l:loc).

Definition valid_allocPred (P Pc: gset u64 → iProp Σ) : iProp Σ :=
  (* Splitting/joining of P *)
  □ (∀ σ1 σ2, ⌜ σ1 ## σ2 ⌝ → P (σ1 ∪ σ2) -∗ (P σ1 ∗ P σ2)) ∗
  □ (∀ σ1 σ2, P σ1 -∗ P σ2 -∗ ⌜ σ1 ## σ2 ⌝ ∧ (P (σ1 ∪ σ2))) ∗
  (* Splitting/joining of Pc *)
  □ (∀ σ1 σ2, ⌜ σ1 ## σ2 ⌝ → Pc (σ1 ∪ σ2) -∗ (Pc σ1 ∗ Pc σ2)) ∗
  □ (∀ σ1 σ2, Pc σ1 -∗ Pc σ2 -∗ (Pc (σ1 ∪ σ2))) ∗
  (* P must imply Pc *)
  □ (∀ σ, P σ -∗ Pc σ).

Definition is_crash_allocator l P Pc :=
  is_allocator l (λ σ, crash_borrow (P σ) (Pc σ)).

Theorem wpc_newAllocator Φ Φc (mref : loc) (start sz: u64) used P Pc K `{!LanguageCtx K} :
  uint.Z start + uint.Z sz < 2^64 →
  let σ := (rangeSet (uint.Z start) (uint.Z sz)) ∖ used in
  valid_allocPred P Pc ⊢@{_}
  P σ -∗
  is_addrset mref used -∗
  Φc ∧ (∀ l, is_crash_allocator l P Pc -∗
     WPC (K (of_val #l)) @ ⊤ {{ Φ }} {{ Φc }}) -∗
  WPC (K (New #start #sz #mref)) @ ⊤ {{ Φ }} {{ Φc ∗ Pc σ }}.
Proof.
  iIntros (Hbound ?) "#Hvalid HP Haddr HK".
  iApply (wpc_crash_borrow_init_ctx' _ _ _ _ (P _) (Pc _) with "[HP]"); auto.
  { iDestruct "Hvalid" as "(?&?&?&?&Himp)". by iApply "Himp". }
  iSplit.
  { iLeft in "HK". eauto. }
  iIntros "Hcb".
  iCache with "HK".
  { by iLeft in "HK". }
  wpc_frame.
  wp_apply (wp_newAllocator _ _ _ used (λ σ, crash_borrow (P σ) (Pc σ)) with "[$Hcb $Haddr]").
  { auto. }
  { iDestruct "Hvalid" as "(Hsplit1&Hjoin1&Hsplit2&Hjoin2&Himp)". iSplit.
    - iModIntro. iIntros (?? Hdisj) "H".
      iApply (crash_borrow_split_post with "H").
      { iApply "Hsplit1". eauto. }
      { iApply "Himp". }
      { iApply "Himp". }
      { iNext. iIntros "(H1&?)". iApply ("Hjoin2" with "H1 [$]"). }
    - iModIntro. iIntros (??) "H1 H2".
      iApply (crash_borrow_combine_post' with "H1 H2").
      {
        iNext. iIntros "(HP1&HP2)". iDestruct ("Hjoin1" with "HP1 [$]") as "(%Hdisj&HP)".
        iModIntro. iFrame.
        iSplit.
        * iIntros. iApply "Hsplit2"; auto.
        * iApply "Himp".
      }
  }
  iIntros (l) "Halloc HK".
  iApply "HK".
  iFrame.
Qed.

Theorem wp_crash_Reserve l P Pc :
  {{{ is_crash_allocator l P Pc }}}
    Allocator__Reserve #l
  {{{ a (ok: bool), RET (#a, #ok);
      if ok then crash_borrow (P {[a]}) (Pc {[a]}) else True%I }}}.
Proof.
  iIntros (Φ) "#Hc HΦ". wp_apply (wp_Reserve).
  { eauto. }
  iIntros (a ok) "H". iApply "HΦ".
  eauto.
Qed.

Theorem wp_crash_Free P Pc l (a: u64) :
  {{{ is_crash_allocator l P Pc ∗ crash_borrow (P {[a]}) (Pc {[a]}) }}}
    Allocator__Free #l #a
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hc&Hborrow) HΦ". wp_apply (wp_Free with "[Hborrow]").
  { iFrame "Hc". eauto. }
  by iApply "HΦ".
Qed.

End crash.
