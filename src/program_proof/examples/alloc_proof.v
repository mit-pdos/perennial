From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import Map.

From Perennial.goose_lang Require Import crash_modality.
From Perennial.algebra Require Import deletable_heap.

From Goose.github_com.mit_pdos.perennial_examples Require Import alloc.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.examples Require Import alloc_addrset.

Class allocG Σ :=
  { alloc_used_preG :> gen_heapPreG u64 () Σ; }.

(* state representation types (defined here since modules can't be in sections) *)
Module alloc.
  Record t :=
    mk { domain: gset u64;
         used: gset u64;
       }.
  Global Instance _eta : Settable _ := settable! mk <domain; used>.
  Global Instance _witness : Inhabited t := populate!.

  Definition wf σ := σ.(used) ⊆ σ.(domain).
  Definition free σ := σ.(domain) ∖ σ.(used).
End alloc.

Section goose.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!allocG Σ}.

Let allocN := nroot.@"allocator".

Record alloc_names :=
  { alloc_lock_name: gname;
    alloc_used_name: gen_heapG u64 unit Σ;
  }.

Instance alloc_names_eta : Settable _ := settable! Build_alloc_names <alloc_lock_name; alloc_used_name>.

Implicit Types (a: u64) (m: gmap u64 ()) (free: gset u64).

Context (P: alloc.t → iProp Σ).
Context (Ψ: u64 → iProp Σ).
Implicit Types (l:loc) (γ:alloc_names) (σ: alloc.t).

Definition allocator_durable σ : iProp Σ :=
  "%Hwf'" ∷ ⌜alloc.wf σ⌝ ∗
  "Hblocks" ∷ [∗ set] k ∈ alloc.free σ, Ψ k.

Definition allocator_linv γ (mref: loc) σ : iProp Σ :=
  "%Hwf" ∷ ⌜alloc.wf σ⌝ ∗
  "Hfreemap" ∷ is_addrset mref (alloc.free σ) ∗
  "Hdurable" ∷ allocator_durable σ ∗
  "Hallocated" ∷ gen_heap_ctx (hG:=γ.(alloc_used_name))
                   (gset_to_gmap () (alloc.used σ))
.

Definition is_allocator (l: loc) γ : iProp Σ :=
  ∃ (lref mref: loc),
    "#m" ∷ readonly (l ↦[Allocator.S :: "m"] #lref) ∗
    "#free" ∷ readonly (l ↦[Allocator.S :: "free"] #mref) ∗
    "#His_lock" ∷ is_lock allocN γ.(alloc_lock_name) #lref
                          (∃ σ, "Hlockinv" ∷ allocator_linv γ mref σ ∗ "HP" ∷ P σ)
.

Definition alloc_used γ a : iProp Σ :=
  mapsto (hG:=γ.(alloc_used_name)) a 1 ().

Context {Hitemcrash: ∀ x, IntoCrash (Ψ x) (λ _, Ψ x)}.
Instance allocator_post_crash γ mref σ :
  IntoCrash (allocator_linv γ mref σ) (λ _, allocator_durable σ).
Proof.
  hnf; iNamed 1.
  by iFrame.
Qed.

Global Instance is_allocator_Persistent l γ :
  Persistent (is_allocator l γ).
Proof. apply _. Qed.

(* TODO: prove something useful for initializing from zero blocks *)

Theorem wp_newAllocator mref (start sz: u64) used :
  int.val start + int.val sz < 2^64 →
  {{{ is_addrset mref used ∗
      let σ0 := {| alloc.domain := rangeSet (int.val start) (int.val sz);
                   alloc.used := used |} in
      ⌜alloc.wf σ0⌝ ∗ allocator_durable σ0 ∗ ▷ P σ0 }}}
    New #start #sz #mref
  {{{ l γ, RET #l; is_allocator l γ }}}.
Proof using allocG0.
  iIntros (Hoverflow Φ) "(Hused&%Hwf&Hblocks&HP) HΦ".
  wp_call.
  wp_apply wp_freeRange; first by auto.
  iIntros (mref') "Hfree".
  wp_pures.
  wp_apply (wp_mapRemove with "[$Hfree $Hused]"); iIntros "(Hfree & Hused)".
  wp_apply wp_new_free_lock.
  iIntros (γ1 lk) "Hlock".
  rewrite -wp_fupd.
  wp_apply wp_allocStruct; auto.
  iIntros (l) "Hallocator".
  iDestruct (struct_fields_split with "Hallocator") as "(m&free&_)".
  iMod (readonly_alloc_1 with "m") as "#m".
  iMod (readonly_alloc_1 with "free") as "#free".
  iMod (gen_heap_init (gset_to_gmap () used)) as (γ2) "Husedctx".
  set (γ:={| alloc_lock_name := γ1; alloc_used_name := γ2 |}).
  iMod (alloc_lock allocN ⊤ _ _
                   (∃ σ, "Hlockinv" ∷ allocator_linv γ mref' σ ∗ "HP" ∷ P σ)%I
          with "[$Hlock] [-HΦ]") as "#Hlock".
  { iExists _; iFrame.
    rewrite /alloc.free /=.
    iFrame "% ∗". }
  iModIntro.
  iApply ("HΦ" $! _ γ).
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

Theorem alloc_free_use σ new :
  alloc.free (set alloc.used (union new) σ) =
  alloc.free σ ∖ new.
Proof.
  clear.
  rewrite /alloc.free /=.
  set_solver.
Qed.

Theorem wp_Reserve (Q: option u64 → iProp Σ) l γ :
  {{{ is_allocator l γ ∗
     (∀ σ σ' ma,
          ⌜match ma with
           | Some a => a ∈ alloc.free σ ∧ σ' = set alloc.used ({[a]} ∪.) σ
           | None => σ' = σ
           end⌝ -∗
           ⌜alloc.wf σ⌝ -∗
          ▷ P σ ={⊤}=∗ ▷ P σ' ∗ Q ma)
  }}}
    Allocator__Reserve #l
  {{{ a (ok: bool), RET (#a, #ok);
      if ok then Q (Some a) ∗ Ψ a ∗ alloc_used γ a
      else Q None }}}.
Proof.
  clear.
  iIntros (Φ) "(Hinv&Hfupd) HΦ"; iNamed "Hinv".
  wp_call.
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
  iAssert (is_addrset mref (alloc.free σ ∖ {[k]})) with "[Hfreemap]" as "Hfreemap".
  { iExists _; iFrame.
    iPureIntro.
    rewrite /map_del.
    rewrite dom_delete_L.
    set_solver. }
  iMod ("Hfupd" $! _ (if ok then _ else _) (if ok then Some k else None) with "[] [%//] HP") as "[HP HQ]".
  { destruct ok; simpl; auto. }
  wp_loadField.
  destruct ok.

  - (* extract block *)
    iNamed "Hdurable".
    iDestruct (big_sepS_delete with "Hblocks") as "[Hbk Hblocks]"; eauto.

    iMod (gen_heap_alloc _ k () with "Hallocated") as "[Hallocated His_used]".
    { apply lookup_gset_to_gmap_None.
      rewrite /alloc.free in Hk; set_solver. }

    wp_apply (release_spec with "[-HΦ HQ Hbk His_used $His_lock $His_locked]").
    { iExists _; iFrame.
      assert (alloc.wf (set alloc.used ({[k]} ∪.) σ)) as Hwf''.
      { rewrite /alloc.wf in Hwf |- *; set_solver. }
      iFrame "%".
      iSplitL "Hfreemap".
      - rewrite alloc_free_use; iFrame.
      - iSplitL "Hblocks".
        { rewrite alloc_free_use; iFrame. }
        simpl.
        rewrite -gset_to_gmap_union_singleton //. }
    wp_pures.
    iApply "HΦ"; iFrame.
  - wp_apply (release_spec with "[-HΦ HQ $His_lock $His_locked]").
    { iExists _; iFrame "∗ %". iNext.
      iExactEq "Hfreemap"; rewrite /named.
      f_equal.
      set_solver. }
    wp_pures.
    iApply "HΦ"; iFrame.
Qed.

Lemma gset_difference_difference `{Countable K} (A B C: gset K) :
  C ⊆ A →
  A ∖ (B ∖ C) = A ∖ B ∪ C.
Proof using.
  clear.
  intros.
  apply gset_eq; intros k.
  rewrite !elem_of_difference.
  intuition.
  - destruct (decide (k ∈ C)); set_solver.
  - set_solver.
  - set_solver.
Qed.

Theorem alloc_free_free σ new :
  new ⊆ σ.(alloc.domain) →
  alloc.free (set alloc.used (λ used, used ∖ new) σ) =
  alloc.free σ ∪ new.
Proof.
  intros Hsub.
  rewrite /alloc.free /=.
  rewrite gset_difference_difference //.
Qed.

Lemma alloc_used_valid γ a used :
  gen_heap_ctx (hG:=γ.(alloc_used_name)) (gset_to_gmap () used) -∗
  alloc_used γ a -∗
  ⌜a ∈ used⌝.
Proof.
  rewrite /alloc_used.
  iIntros "Hctx Hused".
  iDestruct (gen_heap_valid with "Hctx Hused") as %Hlookup.
  iPureIntro.
  apply lookup_gset_to_gmap_Some in Hlookup as [? _]; auto.
Qed.

Theorem wp_Free (Q: iProp Σ) l γ (a: u64) :
  {{{ is_allocator l γ ∗ Ψ a ∗ alloc_used γ a ∗
     (∀ σ σ',
          ⌜σ' = set alloc.used (λ used, used ∖ {[a]}) σ⌝ -∗
          ⌜alloc.wf σ⌝ -∗
          ▷ P σ ={⊤}=∗ ▷ P σ' ∗ Q)
  }}}
    Allocator__Free #l #a
  {{{ RET #(); Q }}}.
Proof.
  clear Hitemcrash.
  iIntros (Φ) "(Halloc&Hb&Hused&Hfupd) HΦ"; iNamed "Halloc".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "His_lock").
  iIntros "(Hlocked&Hinv)"; iNamed "Hinv".
  iNamed "Hlockinv".
  wp_loadField.
  iDestruct "Hfreemap" as (m) "[Hfreemap %Hdom]".
  wp_apply (wp_MapInsert _ _ _ _ () with "Hfreemap"); first by auto.
  iIntros "Hfreemap".
  iAssert (is_addrset mref (alloc.free σ ∪ {[a]})) with "[Hfreemap]" as "Hfreemap".
  { iExists _; iFrame.
    iPureIntro.
    rewrite /map_insert dom_insert_L.
    set_solver. }
  wp_loadField.
  iMod ("Hfupd" $! σ with "[] [%//] HP") as "[HP HQ]".
  { iPureIntro.
    eauto. }
  iDestruct (alloc_used_valid with "Hallocated Hused") as %Hused.
  assert (a ∉ alloc.free σ) by set_solver.
  assert (a ∈ σ.(alloc.domain)) by set_solver.
  assert (alloc.wf (set alloc.used (λ used : gset u64, used ∖ {[a]}) σ)) as Hwf''.
  { set_solver. }
  iMod (gen_heap_delete with "[$Hallocated $Hused]") as "Hallocated".
  wp_apply (release_spec with "[$His_lock $Hlocked Hb Hdurable Hfreemap Hallocated HP]").
  { iNamed "Hdurable".
    iExists _; iFrame "HP".
    iFrame "%".
    rewrite alloc_free_free; last first.
    { apply elem_of_subseteq_singleton; auto. }
    iFrame "Hfreemap".
    rewrite big_sepS_union; last first.
    { apply disjoint_singleton_r; auto. }
    rewrite big_opS_singleton.
    iFrame "Hb Hblocks". iNext.
    iExactEq "Hallocated".
    rewrite /named.
    f_equal.
    simpl.
    rewrite -gset_to_gmap_difference_singleton //.
  }
  iApply ("HΦ" with "[$]").
Qed.

End goose.
