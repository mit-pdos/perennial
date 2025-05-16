From New.proof.github_com.mit_pdos.tulip Require Import tuple.res program_prelude.

(* systematic *)
From New.proof.github_com.mit_pdos.tulip Require Import tuple.
From New.proof Require Import sync.
From New.proof Require Import grove_prelude.
From New.generatedproof.github_com.mit_pdos.tulip Require Import index.
(* end systematic *)

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !goGlobalsGS Σ}.

  #[global] Program Instance : IsPkgInit index := ltac2:(build_pkg_init ()).

  (*@ type Index struct {                                                     @*)
  (*@     mu   *sync.Mutex                                                    @*)
  (*@     tplm map[string]*tuple.Tuple                                        @*)
  (*@ }                                                                       @*)
  Definition own_index (idx : loc) γ α : iProp Σ :=
    ∃ (tplmP : loc) (tplm : gmap dbkey loc),
      let keys_unalloc := keys_all ∖ (dom tplm) in
      "HtplmP"  ∷ idx ↦s[index.Index :: "tplm"] tplmP ∗
      "Htplm"   ∷ own_map tplmP (DfracOwn 1) tplm ∗
      "Hphysm"  ∷ ([∗ set] key ∈ keys_unalloc, own_phys_hist_half α key [None]) ∗
      "#Hreplm" ∷ ([∗ set] key ∈ keys_all, is_repl_hist_lb γ key [None]) ∗
      "#Htpls"  ∷ ([∗ map] key ↦ tpl ∈ tplm, is_tuple tpl key γ α).

  Definition is_index (idx : loc) (γ : tulip_names) α : iProp Σ :=
    ∃ (muP : loc),
      "#HmuP" ∷ idx ↦s[index.Index :: "mu"]□ muP ∗
      "#Hmu"  ∷ is_Mutex muP (own_index idx γ α).

  Theorem wp_Index__GetTuple (idx : loc) (key : byte_string) γ α :
    key ∈ keys_all ->
    is_index idx γ α -∗
    {{{ is_pkg_init index }}}
      idx @ index @ "Index'ptr" @ "GetTuple" #key
    {{{ (tpl : loc), RET #tpl; is_tuple tpl key γ α }}}.
  Proof.
    iIntros (Hkey) "#Hidx".
    wp_start as "_".
    wp_auto.
    iPersist "idx key".

    (*@ func (idx *Index) GetTuple(key string) *tuple.Tuple {                   @*)
    (*@     idx.mu.Lock()                                                       @*)
    (*@     tpl, ok := idx.tplm[key]                                            @*)
    (*@                                                                         @*)
    iNamed "Hidx".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hmu]").
    iIntros "[Hlocked Hidx]".
    iNamed "Hidx".
    wp_auto.
    wp_apply (wp_map_get with "Htplm").
    iIntros "Htplm".
    wp_auto.

    (*@     // Return the tuple if there already exists one.                    @*)
    (*@     if ok {                                                             @*)
    (*@         idx.mu.Unlock()                                                 @*)
    (*@         return tpl                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct (tplm !! key) eqn:Hget.
    { rewrite Hget. rewrite bool_decide_eq_true_2; [ | by auto ].
      wp_auto.
      wp_apply (wp_Mutex__Unlock with "[-HΦ ok tpl]").
      { by iFrame "Hmu Hlocked ∗ #". }
      iApply "HΦ".
      by iApply (big_sepM_lookup with "Htpls").
    }
    rewrite Hget. rewrite bool_decide_eq_false_2; [ | by auto ].
    wp_auto.

    (*@     tplnew := tuple.MkTuple()                                           @*)
    (*@     idx.tplm[key] = tplnew                                              @*)
    (*@                                                                         @*)
    iDestruct (big_sepS_delete _ _ key with "Hphysm") as "[Hphys Hphysm]".
    { apply not_elem_of_dom in Hget. set_solver+ Hkey Hget. }
    iDestruct (big_sepS_elem_of with "Hreplm") as "#Hrepl".
    { apply Hkey. }
    wp_apply (wp_MkTuple with "Hrepl [$Hphys]").
    iIntros (tplnewP) "#Htplnew".
    wp_auto.
    wp_apply (wp_map_insert with "Htplm").
    iIntros "Htplm".
    iDestruct (big_sepM_insert_2 with "[] Htpls") as "Htpls'".
    { iFrame "Htplnew". }

    (*@     idx.mu.Unlock()                                                     @*)
    (*@     return tplnew                                                       @*)
    (*@ }                                                                       @*)
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[-HΦ ok tplnew]").
    { iFrame "Hmu Hlocked ∗ #".
      by rewrite dom_insert_L union_comm_L -difference_difference_l_L.
    }
    by iApply "HΦ".
  Qed.

  Theorem wp_MkIndex γ α :
    ([∗ set] key ∈ keys_all, is_repl_hist_lb γ key [None]) -∗
    {{{ is_pkg_init index ∗ ([∗ set] key ∈ keys_all, own_phys_hist_half α key [None]) }}}
      index @ "MkIndex" #()
    {{{ (idx : loc), RET #idx; is_index idx γ α }}}.
  Proof.
    iIntros "#Hreplm".
    wp_start as "Hphysm".
    wp_auto.

    (*@ func MkIndex() *Index {                                                 @*)
    (*@     idx := new(Index)                                                   @*)
    (*@     idx.mu = new(sync.Mutex)                                            @*)
    (*@     idx.tplm = make(map[string]*tuple.Tuple)                            @*)
    (*@     return idx                                                          @*)
    (*@ }                                                                       @*)
    wp_alloc idxP as "Hidx".
    iApply struct_fields_split in "Hidx". iNamed "Hidx".
    with_strategy opaque [is_pkg_init] cbn.
    iRename "Hmu" into "mu".
    wp_auto.
    wp_alloc muP as "Hfree".
    wp_auto.
    wp_apply (wp_map_make (K:=byte_string) (V:=loc)); first done.
    iIntros (tplmP) "Htplm_map".
    rewrite -wp_fupd.
    wp_auto.
    iMod (init_Mutex (own_index idxP γ α) with "Hfree [-HΦ mu]") as "#Hmu".
    { iFrame "∗ #".
      rewrite dom_empty_L difference_empty_L big_sepM_empty.
      iFrame.
    }
    iPersist "mu".
    iModIntro.
    iApply "HΦ".
    by iFrame "#".
  Qed.

End program.
