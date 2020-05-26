From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import Map.

From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import alloc.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import typed_slice into_val.
From Perennial.program_proof.examples Require Import range_set.

Instance unit_IntoVal : IntoVal ().
Proof.
  refine {| to_val := λ _, #();
            IntoVal_def := ();
         |}.
  intros [] [] _; auto.
Defined.

Instance unit_IntoValForType : IntoValForType unit_IntoVal (struct.t unit.S).
Proof.
  constructor; auto.
Qed.

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

Lemma rangeSet_append_one:
  ∀ start sz : u64,
    int.val start + int.val sz < 2 ^ 64
    → ∀ i : u64,
      int.val i < int.val (word.add start sz)
      → int.val start ≤ int.val i
      → {[i]} ∪ rangeSet (int.val start) (int.val i - int.val start) =
        rangeSet (int.val start) (int.val i - int.val start + 1).
Proof.
  intros start sz Hbound i Hibound Hilower_bound.
  replace (int.val (word.add start sz)) with (int.val start + int.val sz) in Hibound by word.
  apply gset_eq; intros.
  rewrite elem_of_union.
  rewrite elem_of_singleton.
  rewrite !rangeSet_lookup; try word.
  destruct (decide (x = i)); subst.
  - split; intros; eauto.
    word.
  - intuition; try word.
    right.
    assert (int.val x ≠ int.val i) by (apply not_inj; auto).
    word.
Qed.

Definition is_addrset (m_ref: loc) (addrs: gset u64): iProp Σ :=
  ∃ m, is_map m_ref m ∗ ⌜dom (gset _) m = addrs⌝.

Theorem wp_freeRange (start sz: u64) :
  int.val start + int.val sz < 2^64 ->
  {{{ True }}}
    freeRange #start #sz
  {{{ (mref: loc), RET #mref;
      is_addrset mref (rangeSet (int.val start) (int.val sz)) }}}.
Proof.
  iIntros (Hbound Φ) "_ HΦ".
  wp_call.
  wp_apply (wp_NewMap () (t:=struct.t unit.S)).
  iIntros (mref) "Hmap".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (il) "i".
  wp_pures.
  wp_apply (wp_forUpto (λ i, "%Hilower_bound" ∷ ⌜int.val start ≤ int.val i⌝ ∗
                             "*" ∷ ∃ m, "Hmap" ∷ is_map mref m ∗
                                        "%Hmapdom" ∷ ⌜dom (gset _) m = rangeSet (int.val start) (int.val i - int.val start)⌝)%I
            with "[] [Hmap $i]").
  - word.

  - clear Φ.
    iIntros (i).
    iIntros "!>" (Φ) "(HI & i & %Hibound) HΦ"; iNamed "HI".
    wp_pures.
    wp_load.
    wp_apply (wp_MapInsert _ _ _ _ () with "Hmap"); auto.
    iIntros "Hm".
    wp_pures.
    iApply "HΦ".
    iFrame.
    iSplitR.
    { iPureIntro; word. }
    rewrite /named.
    iExists _; iFrame.
    iPureIntro.
    rewrite /map_insert dom_insert_L.
    rewrite Hmapdom.
    replace (int.val (word.add i 1) - int.val start) with ((int.val i - int.val start) + 1) by word.
    eapply rangeSet_append_one; eauto.

  - iSplitR; auto.
    rewrite -> rangeSet_diag by word.
    iExists _; iFrame.
    rewrite dom_empty_L; auto.
  - iIntros "(HI&Hil)"; iNamed "HI".
    wp_pures.
    iApply "HΦ"; iFrame.
    iExists _; iFrame.
    iPureIntro; auto.
    rewrite Hmapdom.
    repeat (f_equal; try word).
Qed.

Lemma big_sepM_lookup_unit (PROP:bi) `{Countable K}
  `{BiAffine PROP} (m: gmap K ()) :
  ⊢@{PROP} [∗ map] k↦_ ∈ m, ⌜m !! k = Some tt⌝.
Proof.
  iDestruct (big_sepM_lookup_holds m) as "Hmap".
  iApply (big_sepM_mono with "Hmap"); simpl; intros.
  destruct x; auto.
Qed.

(* this is superceded by wp_findKey, but that theorem relies in an unproven map
iteration theorem *)
Theorem wp_findKey' mref m :
  {{{ is_map mref m }}}
    findKey #mref
  {{{ (k: u64) (ok: bool), RET (#k, #ok);
      ⌜if ok then m !! k = Some tt else True⌝ ∗ (* TODO: easier if this
      promises to find a key if it exists *)
      is_map mref m
  }}}.
Proof.
  iIntros (Φ) "Hmap HΦ".
  wp_call.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (found_l) "found".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (ok_l) "ok".
  wp_pures.
  wp_apply (wp_MapIter _ _ _ _
                       (∃ (found: u64) (ok: bool),
                           "found" ∷ found_l ↦[uint64T] #found ∗
                           "ok" ∷ ok_l ↦[boolT] #ok ∗
                           "%Hfound_is" ∷ ⌜if ok then m !! found = Some tt else True⌝)
                       (λ k _, ⌜m !! k = Some tt⌝)%I
                       (λ _ _, True)%I
                       with "Hmap [found ok]").
  - iExists _, _; iFrame.
  - iApply big_sepM_lookup_unit.
  - iIntros (k v) "!>".
    clear Φ.
    iIntros (Φ) "[HI %Helem] HΦ"; iNamed "HI".
    wp_pures.
    wp_load.
    wp_pures.
    wp_if_destruct.
    + wp_store. wp_store.
      iApply "HΦ".
      iSplitL; auto.
      iExists _, _; iFrame.
      auto.
    + iApply "HΦ".
      iSplitL; auto.
      iExists _, _; iFrame.
      apply negb_false_iff in Heqb; subst.
      auto.
  - iIntros "(His_map&HI&_HQ)"; iNamed "HI".
    wp_pures.
    wp_load. wp_load.
    wp_pures.
    iApply "HΦ"; iFrame.
    auto.
Qed.

Theorem wp_findKey mref free :
  {{{ is_addrset mref free }}}
    findKey #mref
  {{{ (k: u64) (ok: bool), RET (#k, #ok);
      ⌜if ok then k ∈ free else free = ∅⌝ ∗
      is_addrset mref free
  }}}.
Proof.
  iIntros (Φ) "Hmap HΦ".
  wp_call.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (found_l) "found".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (ok_l) "ok".
  wp_pures.
  iDestruct "Hmap" as (m) "[Hmap %Hmapdom]".
  wp_apply (wp_MapIter_fold _ _ (λ mdone, ∃ (found: u64) (ok: bool),
                           "found" ∷ found_l ↦[uint64T] #found ∗
                           "ok" ∷ ok_l ↦[boolT] #ok ∗
                           "%Hfound_is" ∷ ⌜if ok then m !! found = Some tt else mdone = ∅⌝)%I
           with "Hmap [found ok]").
  - iExists _, _; by iFrame.
  - clear Φ.
    iIntros (mdone k v) "!>".
    iIntros (Φ) "(HI&(%&%)) HΦ"; iNamed "HI".
    wp_pures.
    wp_load.
    wp_pures.
    wp_if_destruct;
      (* TODO: automate this in wp_if_destruct *)
      [ apply negb_true_iff in Heqb | apply negb_false_iff in Heqb ]; subst.
    + wp_store. wp_store.
      iApply "HΦ".
      iExists _, _; iFrame.
      destruct v; auto.
    + iApply "HΦ".
      iExists _, _; iFrame.
      auto.
  - iIntros "[Hm HI]"; iNamed "HI".
    wp_load. wp_load.
    wp_pures.
    iApply "HΦ".
    destruct ok.
    + iSplitR.
      { iPureIntro.
        rewrite -Hmapdom.
        apply elem_of_dom; eauto. }
      iExists _; iFrame "% ∗".
    + iSplitR.
      { iPureIntro.
        rewrite -Hmapdom; subst.
        rewrite dom_empty_L //. }
      iExists _; iFrame "% ∗".
Qed.

Theorem wp_mapRemove m_ref remove_ref free remove :
  {{{ is_addrset m_ref free ∗ is_addrset remove_ref remove }}}
    mapRemove #m_ref #remove_ref
  {{{ RET #(); is_addrset m_ref (free ∖ remove) ∗ is_addrset remove_ref remove }}}.
Proof.
  iIntros (Φ) "[His_free His_remove] HΦ".
  rewrite /mapRemove.
  wp_pures.
  iDestruct "His_remove" as (m) "[His_remove %Hdom]".
  wp_apply (wp_MapIter_2 _ _ _ _
                         (λ mtodo mdone, is_addrset m_ref (free ∖ dom (gset _) mdone))
              with "His_remove [His_free] [] [HΦ]").
  - rewrite dom_empty_L.
    rewrite difference_empty_L.
    iFrame.

  - clear Hdom m Φ.
    iIntros (k [] mtodo mdone) "!>".
    iIntros (Φ) "[His_free %Hin] HΦ".
    wp_call.
    iDestruct "His_free" as (m) "[His_free %Hdom]".
    wp_apply (wp_MapDelete with "His_free").
    iIntros "Hm".
    iApply "HΦ".
    iExists _; iFrame.
    iPureIntro.
    rewrite /map_del dom_delete_L.
    set_solver.
  - iIntros "[Hremove Hfree]".
    iApply "HΦ".
    rewrite Hdom.
    iFrame.
    iExists _; iFrame "% ∗".
Qed.

Theorem wp_SetAdd mref used addr_s q addrs :
  {{{ is_addrset mref used ∗ is_slice_small addr_s uint64T q addrs }}}
    SetAdd #mref (slice_val addr_s)
  {{{ RET #(); is_addrset mref (used ∪ list_to_set addrs) ∗
               is_slice_small addr_s uint64T q addrs }}}.
Proof.
  iIntros (Φ) "(Hused&Haddrs) HΦ".
  rewrite /SetAdd; wp_pures.
  wp_apply (wp_forSlicePrefix (λ done todo, is_addrset mref (used ∪ list_to_set done))
                              with "[] [Hused $Haddrs]").

  - clear Φ.
    iIntros (i a done _) "!>".
    iIntros (Φ) "Hused HΦ".
    wp_pures.
    iDestruct "Hused" as (m) "[Hused %Hdom]".
    wp_apply (wp_MapInsert _ _ _ _ () with "Hused").
    { auto. }
    iIntros "Hm".
    iApply "HΦ".
    iExists _; iFrame.
    iPureIntro.
    rewrite /map_insert dom_insert_L.
    set_solver.
  - simpl.
    iExactEq "Hused".
    f_equal.
    set_solver.
  - iIntros "[Hs Haddrs]".
    iApply "HΦ"; iFrame.
Qed.

Implicit Types (P: alloc.t → iProp Σ).
Implicit Types (l:loc) (γ:gname) (σ: alloc.t).

Definition allocator_linv (mref: loc) σ : iProp Σ :=
  "Hfreemap" ∷ is_addrset mref (alloc.free σ) ∗
  "Hblocks" ∷ [∗ set] k ∈ alloc.free σ, ∃ b, int.val k d↦ b
.

Definition allocator_durable σ : iProp Σ :=
  ([∗ set] k ∈ alloc.free σ, ∃ b, int.val k d↦ b)%I.

Definition is_allocator P (l: loc) (γ: gname) : iProp Σ :=
  ∃ (lref mref: loc),
    "#m" ∷ readonly (l ↦[Allocator.S :: "m"] #lref) ∗
    "#free" ∷ readonly (l ↦[Allocator.S :: "free"] #mref) ∗
    "#His_lock" ∷ is_lock allocN γ #lref (∃ σ, "Hlockinv" ∷ allocator_linv mref σ ∗ "HP" ∷ P σ)
.

Instance allocator_post_crash mref σ :
  IntoCrash (allocator_linv mref σ) (λ _, allocator_durable σ).
Proof.
  hnf; iIntros "H"; iNamed "H".
  by iFrame.
Qed.

Global Instance is_allocator_Persistent P l γ :
  Persistent (is_allocator P l γ).
Proof. apply _. Qed.

Theorem allocator_durable_from_map m σ :
  alloc.free σ = dom (gset _) m →
  ([∗ map] a↦_ ∈ m, ∃ b, int.val a d↦ b) -∗
  allocator_durable σ.
Proof.
  iIntros (Hdom) "Hblocks".
  rewrite /allocator_durable.
  rewrite Hdom.
  iApply (big_sepM_dom with "Hblocks").
Qed.

Theorem wp_newAllocator P mref (start sz: u64) used :
  int.val start + int.val sz < 2^64 →
  {{{ is_addrset mref used ∗
      let σ0 := {| alloc.domain := rangeSet (int.val start) (int.val sz);
                   alloc.used := used |} in
      allocator_durable σ0 ∗ P σ0 }}}
    New #start #sz #mref
  {{{ l γ, RET #l; is_allocator P l γ }}}.
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
  apply gset_eq; intros.
  rewrite elem_of_difference.
  intuition auto.
  apply not_elem_of_empty in H0; auto.
Qed.

Theorem alloc_free_use σ new :
  alloc.free (set alloc.used (λ used, used ∪ new) σ) =
  alloc.free σ ∖ new.
Proof.
  rewrite /alloc.free /=.
  set_solver.
Qed.

Theorem wp_Reserve P (Q: option u64 → iProp Σ) l γ :
  {{{ is_allocator P l γ ∗
     (∀ σ σ' ma,
          ⌜match ma with
           | Some a => a ∈ alloc.free σ ∧ σ' = set alloc.used (λ used, used ∪ {[a]}) σ
           | None => σ' = σ
           end⌝ -∗
          P σ ={⊤}=∗ P σ' ∗ Q ma)
  }}}
    Allocator__Reserve #l
  {{{ a (ok: bool), RET (#a, #ok);
      if ok then Q (Some a) ∗ (∃ b, int.val a d↦ b)
      else Q None }}}.
Proof.
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
  iAssert (([∗ set] k0 ∈ if ok then alloc.free σ ∖ {[k]} else alloc.free σ, ∃ b, int.val k0 d↦ b) ∗
          if ok then (∃ b, int.val k d↦ b) else emp)%I
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
Proof.
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

Theorem wp_Free P (Q: iProp Σ) l γ (a: u64) :
  {{{ is_allocator P l γ ∗ (∃ b, int.val a d↦ b) ∗
     (∀ σ σ',
          ⌜if decide (a ∈ σ.(alloc.domain))
           then σ' = set alloc.used (λ used, used ∖ {[a]}) σ
           else σ' = σ⌝ -∗
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
  iMod ("Hfupd" $! σ (if decide (a ∈ σ.(alloc.domain)) then _ else _)
          with "[] HP") as "[HP HQ]".
  { iPureIntro.
    destruct (decide (a ∈ σ.(alloc.domain))); eauto. }
  wp_apply (release_spec with "[$His_lock $Hlocked Hb Hblocks Hfreemap HP]").
  { iExists _; iFrame.
    rewrite /allocator_linv.
    destruct (decide (a ∈ σ.(alloc.domain))); iFrame.
    - rewrite alloc_free_free; last first.
      { apply elem_of_subseteq_singleton; auto. }
      iFrame "Hfreemap".
      iAssert (⌜a ∈ alloc.free σ⌝ -∗ ⌜False⌝)%I as "%Hnotfree".
      { iIntros (Hin).
        iDestruct (big_sepS_delete with "Hblocks") as "[Hb' _]"; eauto.
        iDeexHyp "Hb".
        iDeexHyp "Hb'".
        iDestruct (gen_heap.mapsto_mapsto_ne with "Hb Hb'") as %Hnoteq; auto. }
      rewrite big_sepS_union; last first.
      { rewrite disjoint_singleton_r; auto. }
      rewrite big_opS_singleton.
      iFrame.
    - admit. (* TODO: oops, can't mark something free if it's not in the domain
      (really need a to be in the domain) *) }
  iApply ("HΦ" with "[$]").
Admitted.

End goose.
