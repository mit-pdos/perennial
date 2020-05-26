From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import Map.

From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import alloc.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.examples Require Import alloc_addrset.

(* state representation types (defined here since modules can't be in sections) *)
Module alloc.
  Record t :=
    mk { domain: gset u64;
         used: gset u64;
       }.
  Global Instance _eta : Settable _ := settable! mk <domain; used>.
  Global Instance _witness : Inhabited t := populate!.

  Definition free σ := σ.(domain) ∖ σ.(used).
End alloc.

Section goose.
Context `{!heapG Σ}.
Context `{!lockG Σ}.

Let allocN := nroot.@"allocator".

Implicit Types (m: gmap u64 ()) (free: gset u64).

Context (P: alloc.t → iProp Σ).
Context (Ψ: u64 → iProp Σ).
Implicit Types (l:loc) (γ:gname) (σ: alloc.t).

Definition allocator_linv (mref: loc) σ : iProp Σ :=
  "Hfreemap" ∷ is_addrset mref (alloc.free σ) ∗
  "Hblocks" ∷ [∗ set] k ∈ alloc.free σ, Ψ k
.

Definition allocator_durable σ : iProp Σ :=
  ([∗ set] k ∈ alloc.free σ, Ψ k)%I.

Definition is_allocator (l: loc) (γ: gname) : iProp Σ :=
  ∃ (lref mref: loc),
    "#m" ∷ readonly (l ↦[Allocator.S :: "m"] #lref) ∗
    "#free" ∷ readonly (l ↦[Allocator.S :: "free"] #mref) ∗
    "#His_lock" ∷ is_lock allocN γ #lref (∃ σ, "Hlockinv" ∷ allocator_linv mref σ ∗ "HP" ∷ P σ)
.

Context {Hitemcrash: ∀ x, IntoCrash (Ψ x) (λ _, Ψ x)}.
Instance allocator_post_crash mref σ :
  IntoCrash (allocator_linv mref σ) (λ _, allocator_durable σ).
Proof.
  hnf; iIntros "H"; iNamed "H".
  by iFrame.
Qed.

Global Instance is_allocator_Persistent l γ :
  Persistent (is_allocator l γ).
Proof. apply _. Qed.

Theorem allocator_durable_from_map m σ :
  alloc.free σ = dom (gset _) m →
  ([∗ map] a↦_ ∈ m, Ψ a) -∗
  allocator_durable σ.
Proof.
  iIntros (Hdom) "Hblocks".
  rewrite /allocator_durable.
  rewrite Hdom.
  iApply (big_sepM_dom with "Hblocks").
Qed.

Theorem wp_newAllocator mref (start sz: u64) used :
  int.val start + int.val sz < 2^64 →
  {{{ is_addrset mref used ∗
      let σ0 := {| alloc.domain := rangeSet (int.val start) (int.val sz);
                   alloc.used := used |} in
      allocator_durable σ0 ∗ P σ0 }}}
    New #start #sz #mref
  {{{ l γ, RET #l; is_allocator l γ }}}.
Proof.
  iIntros (Hoverflow Φ) "(Hused&Hblocks&HP) HΦ".
  wp_call.
  wp_apply wp_freeRange; first by auto.
  iIntros (mref') "Hfree".
  wp_pures.
  wp_apply (wp_mapRemove with "[$Hfree $Hused]"); iIntros "(Hfree & Hused)".
  wp_apply wp_new_free_lock.
  iIntros (γ lk) "Hlock".
  rewrite -wp_fupd.
  wp_apply wp_allocStruct; auto.
  iIntros (l) "Hallocator".
  iDestruct (struct_fields_split with "Hallocator") as "(m&free&_)".
  iMod (readonly_alloc_1 with "m") as "#m".
  iMod (readonly_alloc_1 with "free") as "#free".
  iMod (alloc_lock allocN ⊤ _ _
                   (∃ σ, "Hlockinv" ∷ allocator_linv mref' σ ∗ "HP" ∷ P σ)%I
          with "[$Hlock] [-HΦ]") as "#Hlock".
  { iExists _; iFrame.
    rewrite /alloc.free /=.
    iFrame. }
  iModIntro.
  iApply "HΦ".
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
  alloc.free (set alloc.used (λ used, used ∪ new) σ) =
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
           | Some a => a ∈ alloc.free σ ∧ σ' = set alloc.used (λ used, used ∪ {[a]}) σ
           | None => σ' = σ
           end⌝ -∗
          P σ ={⊤}=∗ P σ' ∗ Q ma)
  }}}
    Allocator__Reserve #l
  {{{ a (ok: bool), RET (#a, #ok);
      if ok then Q (Some a) ∗ Ψ a
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
  iMod ("Hfupd" $! _ (if ok then _ else _) (if ok then Some k else None) with "[] HP") as "[HP HQ]".
  { destruct ok; simpl; auto. }
  wp_loadField.

  (* extract block, if ok *)
  iAssert (([∗ set] k0 ∈ if ok then alloc.free σ ∖ {[k]} else alloc.free σ, Ψ k0) ∗
          if ok then Ψ k else emp)%I
          with "[Hblocks]" as "[Hblocks Hbk]".
  { destruct ok.
    - iDestruct (big_sepS_delete with "Hblocks") as "[$ $]".
      auto.
    - iFrame. }

  wp_apply (release_spec with "[-HΦ HQ Hbk $His_lock $His_locked]").
  { iExists _; iFrame.
    iSplitL "Hfreemap".
    - destruct ok; simpl.
      + rewrite alloc_free_use; iFrame.
      + rewrite Hk.
        iExactEq "Hfreemap".
        rewrite /named.
        f_equal.
        set_solver.
    - destruct ok; iFrame.
      rewrite alloc_free_use; iFrame. }

  wp_pures.
  iApply "HΦ".
  destruct ok; iFrame.
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

Theorem wp_Free (Q: iProp Σ) l γ (a: u64) :
  {{{ is_allocator l γ ∗ Ψ a ∗
     (∀ σ σ',
          ⌜σ' = set alloc.used (λ used, used ∖ {[a]}) σ⌝ -∗
          P σ ={⊤}=∗ P σ' ∗ Q)
  }}}
    Allocator__Free #l #a
  {{{ RET #(); Q }}}.
Proof.
  iIntros (Φ) "(Halloc&Hb&Hfupd) HΦ"; iNamed "Halloc".
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
  iMod ("Hfupd" $! σ with "[] HP") as "[HP HQ]".
  { iPureIntro.
    eauto. }
  wp_apply (release_spec with "[$His_lock $Hlocked Hb Hblocks Hfreemap HP]").
  { iExists _; iFrame.
    rewrite /allocator_linv.
    assert (a ∈ σ.(alloc.domain)) by admit.
    assert (a ∉ alloc.free σ) by admit.
    rewrite alloc_free_free; last first.
    { apply elem_of_subseteq_singleton; auto. }
    iFrame "Hfreemap".
    rewrite big_sepS_union; last first.
    { apply disjoint_singleton_r; auto. }
    rewrite big_opS_singleton.
    iFrame. }
  iApply ("HΦ" with "[$]").
Admitted.

End goose.
