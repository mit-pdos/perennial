From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.tuple Require Import res tuple.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type Index struct {                                                     @*)
  (*@     mu   *sync.Mutex                                                    @*)
  (*@     tplm map[string]*tuple.Tuple                                        @*)
  (*@ }                                                                       @*)
  Definition own_index (idx : loc) γ α : iProp Σ :=
    ∃ (tplmP : loc) (tplm : gmap dbkey loc),
      let keys_unalloc := keys_all ∖ (dom tplm) in
      "HtplmP"  ∷ idx ↦[Index :: "tplm"] #tplmP ∗
      "Htplm"   ∷ own_map tplmP (DfracOwn 1) tplm ∗
      "Hphysm"  ∷ ([∗ set] key ∈ keys_unalloc, own_phys_hist_half α key [None]) ∗
      "#Hreplm" ∷ ([∗ set] key ∈ keys_all, is_repl_hist_lb γ key [None]) ∗
      "#Htpls"  ∷ ([∗ map] key ↦ tpl ∈ tplm, is_tuple tpl key γ α).

  Definition is_index (idx : loc) (γ : tulip_names) α : iProp Σ :=
    ∃ (muP : loc),
      "#HmuP" ∷ readonly (idx ↦[Index :: "mu"] #muP) ∗
      "#Hmu"  ∷ is_lock tulipNS #muP (own_index idx γ α).

  Theorem wp_Index__GetTuple (idx : loc) (key : byte_string) γ α :
    key ∈ keys_all ->
    is_index idx γ α -∗
    {{{ True }}}
      Index__GetTuple #idx #(LitString key)
    {{{ (tpl : loc), RET #tpl; is_tuple tpl key γ α }}}.
  Proof.
    iIntros (Hkey) "#Hidx".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (idx *Index) GetTuple(key string) *tuple.Tuple {                   @*)
    (*@     idx.mu.Lock()                                                       @*)
    (*@     tpl, ok := idx.tplm[key]                                            @*)
    (*@                                                                         @*)
    iNamed "Hidx".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hmu").
    iIntros "[Hlocked Hidx]".
    iNamed "Hidx".
    wp_loadField.
    wp_apply (wp_MapGet with "Htplm").
    iIntros (tplP ok) "[%Hok Htplm]".
    wp_pures.

    (*@     // Return the tuple if there already exists one.                    @*)
    (*@     if ok {                                                             @*)
    (*@         idx.mu.Unlock()                                                 @*)
    (*@         return tpl                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct ok; wp_pures.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hmu Hlocked ∗ #". }
      wp_pures.
      iApply "HΦ".
      apply map_get_true in Hok.
      by iApply (big_sepM_lookup with "Htpls").
    }
    apply map_get_false in Hok as [Hnone _].

    (*@     tplnew := tuple.MkTuple()                                           @*)
    (*@     idx.tplm[key] = tplnew                                              @*)
    (*@                                                                         @*)
    iDestruct (big_sepS_delete _ _ key with "Hphysm") as "[Hphys Hphysm]".
    { apply not_elem_of_dom in Hnone. set_solver. }
    iDestruct (big_sepS_elem_of with "Hreplm") as "#Hrepl".
    { apply Hkey. }
    wp_apply (wp_MkTuple with "Hrepl Hphys").
    iIntros (tplnewP) "#Htplnew".
    wp_loadField.
    wp_apply (wp_MapInsert with "Htplm"); first done.
    iIntros "Htplm".
    iDestruct (big_sepM_insert_2 with "[] Htpls") as "Htpls'".
    { iFrame "Htplnew". }

    (*@     idx.mu.Unlock()                                                     @*)
    (*@     return tplnew                                                       @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hmu Hlocked ∗ #".
      by rewrite dom_insert_L union_comm_L -difference_difference_l_L.
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_MkIndex γ α :
    ([∗ set] key ∈ keys_all, is_repl_hist_lb γ key [None]) -∗
    {{{ ([∗ set] key ∈ keys_all, own_phys_hist_half α key [None]) }}}
      MkIndex #()
    {{{ (idx : loc), RET #idx; is_index idx γ α }}}.
  Proof.
    iIntros "#Hreplm" (Φ) "!> Hphysm HΦ".
    wp_rec.

    (*@ func MkIndex() *Index {                                                 @*)
    (*@     idx := new(Index)                                                   @*)
    (*@     idx.mu = new(sync.Mutex)                                            @*)
    (*@     idx.tplm = make(map[string]*tuple.Tuple)                            @*)
    (*@     return idx                                                          @*)
    (*@ }                                                                       @*)
    wp_apply wp_allocStruct; first by auto.
    iIntros (idxP) "Hidx".
    iDestruct (struct_fields_split with "Hidx") as "Hidx".
    iNamed "Hidx". simpl.
    wp_apply wp_new_free_lock.
    iIntros (muP) "Hfree".
    wp_storeField.
    wp_apply wp_NewMap.
    iIntros (tplmP) "Htplm".
    wp_storeField.
    iMod (alloc_lock _ _ _ (own_index idxP γ α) with "Hfree [-HΦ mu]") as "#Hmu".
    { iFrame "∗ #".
      rewrite dom_empty_L difference_empty_L big_sepM_empty.
      by iFrame.
    }
    iMod (readonly_alloc_1 with "mu") as "#HmuP".
    iApply "HΦ".
    by iFrame "#".
  Qed.

End program.
