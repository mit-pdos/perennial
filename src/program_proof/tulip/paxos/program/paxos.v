From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.invariance Require Import
  accept advance ascend commit extend prepare.
From Perennial.program_proof.tulip.util Require Import next_aligned.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section repr.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  (*@ type Paxos struct {                                                     @*)
  (*@     // Node ID of its peers.                                            @*)
  (*@     peers     []uint64                                                  @*)
  (*@     // Addresses of other Paxos nodes.                                  @*)
  (*@     addrpeers map[uint64]grove_ffi.Address                              @*)
  (*@     // Address of this node.                                            @*)
  (*@     me        grove_ffi.Address                                         @*)
  (*@     // Size of the cluster. @sc = @len(peers) + 1.                      @*)
  (*@     sc        uint64                                                    @*)
  (*@     // ID of this node.                                                 @*)
  (*@     nidme     uint64                                                    @*)
  (*@     // Mutex protecting fields below.                                   @*)
  (*@     mu        *sync.Mutex                                               @*)
  (*@     // Heartbeat.                                                       @*)
  (*@     hb        bool                                                      @*)
  (*@     // Term in which this Paxos node currently is. Persistent.          @*)
  (*@     termc     uint64                                                    @*)
  (*@     // Term to which the log entries @ents belong. Persistent.          @*)
  (*@     terml     uint64                                                    @*)
  (*@     // List of log entries. Persistent.                                 @*)
  (*@     log      []string                                                   @*)
  (*@     // LSN before which entries are committed (exclusively). Persistent. Note @*)
  (*@     // that persistence of @lsnc is *not* a safety requirement, but a   @*)
  (*@     // performance improvement (so that the leader's corresponding @lsnpeers @*)
  (*@     // entry can be updated more efficiently when this node crashes and @*)
  (*@     // recovers, rather than always start from 0).                      @*)
  (*@     lsnc      uint64                                                    @*)
  (*@     // Whether this node is the candidate in @termc.                    @*)
  (*@     iscand    bool                                                      @*)
  (*@     // Whether this node is the leader in @termc.                       @*)
  (*@     isleader  bool                                                      @*)
  (*@     //                                                                  @*)
  (*@     // Candidate state below.                                           @*)
  (*@     //                                                                  @*)
  (*@     // Largest term seen in the prepare phase.                          @*)
  (*@     termp     uint64                                                    @*)
  (*@     // Longest entries after @lsnp in @termc in the prepare phase.      @*)
  (*@     entsp     []string                                                  @*)
  (*@     // Termed log entries collected from peers in the prepare phase.    @*)
  (*@     // NB: Unit range would suffice.                                    @*)
  (*@     respp     map[uint64]bool                                           @*)
  (*@     //                                                                  @*)
  (*@     // Leader state below.                                              @*)
  (*@     //                                                                  @*)
  (*@     // For each follower, LSN up to which all entries match @ents (i.e., @*)
  (*@     // consistent in @terml). @lsnpeers are also used to decide which entries @*)
  (*@     // should be sent to the follower. It is initialized to be an empty map when @*)
  (*@     // a leader is first elected. Absence of an entry means that the node has @*)
  (*@     // not reported what is on its log, in which case the leader could simply @*)
  (*@     // send an APPEND-ENTRIES with LSN = @len(px.log). Note that once   @*)
  (*@     // @lsnpeers[nid] is set, it should only increase monotonically, as @*)
  (*@     // followers' log are supposed to only grow within a term. This subsumes the @*)
  (*@     // next / match indexes in Raft.                                    @*)
  (*@     lsnpeers  map[uint64]uint64                                         @*)
  (*@     //                                                                  @*)
  (*@     // Connections to peers. Used only when the node is a leader.       @*)
  (*@     //                                                                  @*)
  (*@     conns     map[uint64]grove_ffi.Connection                           @*)
  (*@ }                                                                       @*)
  Definition own_paxos_comm (paxos : loc) (peers : gset u64) : iProp Σ :=
    ∃ (peersP : Slice.t) (addrpeersP : loc) (connsP : loc),
      "HpeersP"     ∷ paxos ↦[Paxos :: "peers"] (to_val peersP) ∗
      "HaddrpeersP" ∷ paxos ↦[Paxos :: "addrpeers"] #addrpeersP ∗
      "HconnsP"     ∷ paxos ↦[Paxos :: "conns"] #connsP ∗
      "#Hpeers"     ∷ own_slice peersP uint64T DfracDiscarded (elements peers).

  Definition own_paxos_candidate_only
    (nidme termc terml termp : u64) (logc : list string)
    (entspP : Slice.t) (resppP : loc) nids γ : iProp Σ :=
    ∃ (entsp : list string) (respp : gmap u64 bool),
      "Hentsp"    ∷ own_slice entspP stringT (DfracOwn 1) entsp ∗
      "Hrespp"    ∷ own_map resppP (DfracOwn 1) respp ∗
      "#Hvotes"   ∷ votes_in γ (dom respp) (uint.nat termc) (uint.nat termp) (logc ++ entsp) ∗
      "%Hton"     ∷ ⌜is_term_of_node nidme (uint.nat termc)⌝ ∗
      "%Hdomvts"  ∷ ⌜dom respp ⊆ nids⌝ ∗
      "%Hllep"    ∷ ⌜uint.Z terml ≤ uint.Z termp⌝ ∗
      "%Hpltc"    ∷ ⌜uint.Z termp < uint.Z termc⌝.

  Definition own_paxos_candidate
    (paxos : loc) (nid termc terml : u64) (entsc : list string) (iscand : bool) nids γ : iProp Σ :=
    ∃ (termp : u64) (entspP : Slice.t) (resppP : loc),
      "HiscandP" ∷ paxos ↦[Paxos :: "iscand"] #iscand ∗
      "HtermpP"  ∷ paxos ↦[Paxos :: "termp"] #termp ∗
      "HentspP"  ∷ paxos ↦[Paxos :: "entsp"] (to_val entspP) ∗
      "HresppP"  ∷ paxos ↦[Paxos :: "respp"] #resppP ∗
      "Honlyc"   ∷ (if iscand
                    then own_paxos_candidate_only nid termc terml termp entsc entspP resppP nids γ
                    else True).

  Definition own_paxos_leader_only (termc : u64) (ents : list string) γ : iProp Σ :=
    ∃ (entsbase : list string),
      "Hps"   ∷ own_proposal γ (uint.nat termc) ents ∗
      "#Hpsb" ∷ is_base_proposal_receipt γ (uint.nat termc) entsbase ∗
      "%Hpsb" ∷ ⌜prefix entsbase ents⌝.

  Definition own_paxos_leader
    (paxos : loc) (termc : u64) (ents : list string) (isleader : bool) γ : iProp Σ :=
    ∃ (lsnpeersP : loc),
      "HisleaderP" ∷ paxos ↦[Paxos :: "isleader"] #isleader ∗
      "HlsnpeersP" ∷ paxos ↦[Paxos :: "lsnpeers"] #lsnpeersP ∗
      "Honlyl"     ∷ (if isleader then own_paxos_leader_only termc ents γ else True).

  Definition own_paxos_sc (paxos : loc) (nids : gset u64) : iProp Σ :=
    ∃ (sc : u64),
      "HscP" ∷ paxos ↦[Paxos :: "sc"] #sc ∗
      "%Hsc" ∷ ⌜size nids = uint.nat sc⌝.
  
  Definition own_paxos_common
    (paxos : loc) (nidme termc terml lsnc : u64) (log : list string)
    (nids : gset u64) γ : iProp Σ :=
    ∃ (me : u64) (hb : bool) (logP : Slice.t) (peers : gset u64),
      "HmeP"       ∷ paxos ↦[Paxos :: "me"] #me ∗
      "HnidP"      ∷ paxos ↦[Paxos :: "nidme"] #nidme ∗
      "HhbP"       ∷ paxos ↦[Paxos :: "hb"] #hb ∗
      "HtermcP"    ∷ paxos ↦[Paxos :: "termc"] #termc ∗
      "Htermc"     ∷ own_current_term_half γ nidme (uint.nat termc) ∗
      "HtermlP"    ∷ paxos ↦[Paxos :: "terml"] #terml ∗
      "Hterml"     ∷ own_ledger_term_half γ nidme (uint.nat terml) ∗
      "HlogP"      ∷ paxos ↦[Paxos :: "log"] (to_val logP) ∗
      "Hlog"       ∷ own_slice logP stringT (DfracOwn 1) log ∗
      "Hlogn"      ∷ own_node_ledger_half γ nidme log ∗
      "HlsncP"     ∷ paxos ↦[Paxos :: "lsnc"] #lsnc ∗
      "Hsafecmt"   ∷ safe_ledger_above γ nids (uint.nat terml) (take (uint.nat lsnc) log) ∗ 
      "Hcomm"      ∷ own_paxos_comm paxos peers ∗
      "Hsc"        ∷ own_paxos_sc paxos nids ∗
      "#Hpreped"   ∷ (if decide (termc = terml)
                      then True
                      else past_nodedecs_latest_before γ nidme (uint.nat termc) (uint.nat terml) log) ∗
      "%Hnids"     ∷ ⌜nids = {[nidme]} ∪ peers⌝ ∗
      "%Hnid"      ∷ ⌜0 ≤ uint.Z nidme < max_nodes⌝ ∗
      "%Htermlc"   ∷ ⌜uint.Z terml ≤ uint.Z termc⌝ ∗
      "%Hlsncub"   ∷ ⌜uint.Z lsnc ≤ length log⌝.

  (** Note on designing the lock invariant abstraction: [own_paxos_internal]
  serves as a boundary for exposing internal states required for use by internal
  methods. All [own_paxos{*}_with_{*}] should then be derived from it. Values
  that are decomposed (e.g., [terml]) into smaller pieces of representation
  predicates should be existentially quantified. *)
  Definition own_paxos_internal
    (paxos : loc) (nidme termc terml lsnc : u64) (iscand isleader : bool) nids γ : iProp Σ :=
    ∃ (log : list string),
      let logc := (take (uint.nat lsnc) log) in
      "Hpx"     ∷ own_paxos_common paxos nidme termc terml lsnc log nids γ ∗
      "Hcand"   ∷ own_paxos_candidate paxos nidme termc terml logc iscand nids γ ∗
      "Hleader" ∷ own_paxos_leader paxos termc log isleader γ.

  Definition own_paxos_with_termc_lsnc
    (paxos : loc) (nidme termc lsnc : u64) nids γ : iProp Σ :=
    ∃ (terml : u64) (iscand isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc iscand isleader nids γ.

  Definition own_paxos_nominiated_with_termc_lsnc
    (paxos : loc) (nidme termc lsnc : u64) nids γ : iProp Σ :=
    ∃ (terml : u64) (isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc true isleader nids γ.

  Definition own_paxos_with_termc
    (paxos : loc) (nidme termc : u64) nids γ : iProp Σ :=
    ∃ (terml lsnc : u64) (iscand : bool) (isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc iscand isleader nids γ.

  Definition own_paxos_with_termc_terml
    (paxos : loc) (nidme termc terml : u64) nids γ : iProp Σ :=
    ∃ (lsnc : u64) (iscand : bool) (isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc iscand isleader nids γ.

  Definition own_paxos (paxos : loc) (nidme : u64) nids γ : iProp Σ :=
    ∃ (termc terml lsnc : u64) (iscand : bool) (isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc iscand isleader nids γ.

  Definition own_paxos_nominated (paxos : loc) (nidme : u64) nids γ : iProp Σ :=
    ∃ (termc terml lsnc : u64) (isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc true isleader nids γ.

  (* TODO: finding the right states to expose after adding network. *)

  Definition is_paxos (paxos : loc) (nidme : u64) γ : iProp Σ :=
    ∃ (mu : loc) (nids : gset u64),
      "#HmuP"  ∷ readonly (paxos ↦[Paxos :: "mu"] #mu) ∗
      "#Hlock" ∷ is_lock paxosNS #mu (own_paxos paxos nidme nids γ) ∗
      "#Hinv"  ∷ know_paxos_inv γ nids.

End repr.

Section stepdown.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__stepdown px (nidme term : u64) termc nids γ :
    uint.Z termc < uint.Z term ->
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__stepdown #px #term
    {{{ RET #(); own_paxos_with_termc px nidme term nids γ }}}.
  Proof.
    iIntros (Hlt) "#Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) stepdown(term uint64) {                                @*)
    (*@     px.termc = term                                                     @*)
    (*@     px.iscand = false                                                   @*)
    (*@     px.isleader = false                                                 @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hcand". iNamed "Hleader".
    do 3 wp_storeField.

    (*@     // TODO: Write @px.termc to disk.                                   @*)
    (*@                                                                         @*)
    (*@     // Logical action: Prepare(@term).                                  @*)
    (*@ }                                                                       @*)
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_prepare (uint.nat term) with "Htermc Hterml Hlogn HinvO")
      as "(Htermc & Hterml & Hlogn & HinvO & #Hpromise)".
    { set_solver. }
    { word. }
    iMod ("HinvC" with "HinvO") as "_".
    iApply "HΦ".
    iFrame "HiscandP".
    assert (Htermlc' : uint.Z terml ≤ uint.Z term) by word.
    iFrame "∗ # %".
    iClear "Hpreped".
    by case_decide.
  Qed.

End stepdown.

Section nominate.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__nominate (px : loc) (nidme : u64) nids γ :
    know_paxos_inv γ nids -∗
    {{{ own_paxos px nidme nids γ }}}
      Paxos__nominate #px
    {{{ (term : u64) (lsn : u64), RET (#term, #lsn); own_paxos px nidme nids γ }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> Hpx HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) nominate() (uint64, uint64) {                          @*)
    (*@     // Compute the new term and proceed to that term.                   @*)
    (*@     term := util.NextAligned(px.termc, MAX_NODES, px.nid)               @*)
    (*@     px.termc = term                                                     @*)
    (*@     px.isleader = false                                                 @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hleader".
    do 2 wp_loadField.
    wp_apply wp_NextAligned.
    { word. }
    { rewrite /max_nodes in Hnid. word. }
    iIntros (term [Hgttermc Hmod]).
    do 2 wp_storeField.

    (*@     // Obtain entries after @px.lsnc.                                   @*)
    (*@     lsn := px.lsnc                                                      @*)
    (*@     ents := make([]string, uint64(len(px.log)) - lsn)                   @*)
    (*@     copy(ents, px.log[lsn :])                                           @*)
    (*@                                                                         @*)
    do 2 wp_loadField.
    wp_apply wp_slice_len.
    wp_apply wp_NewSlice.
    iIntros (entsP) "Hents".
    wp_loadField.
    iDestruct (own_slice_sz with "Hlog") as %Hsz.
    iDestruct (own_slice_small_acc with "Hlog") as "[Hlog HlogC]".
    iDestruct (own_slice_small_acc with "Hents") as "[Hents HentsC]".
    wp_apply (wp_SliceCopy_SliceSkip_src with "[$Hlog $Hents]").
    { word. }
    { rewrite length_replicate /=. word. }
    iIntros "[Hlog Hents]".
    iDestruct ("HlogC" with "Hlog") as "Hlog".
    iDestruct ("HentsC" with "Hents") as "Hents".

    (*@     // Use the candidate's log term (@px.terml) and entries (after the committed @*)
    (*@     // LSN, @ents) as the initial preparing term and entries.           @*)
    (*@     px.iscand = true                                                    @*)
    (*@     px.termp  = px.terml                                                @*)
    (*@     px.entsp  = ents                                                    @*)
    (*@     px.respp  = make(map[uint64]bool)                                   @*)
    (*@     px.respp[px.nidme] = true                                           @*)
    (*@                                                                         @*)
    iNamed "Hcand".
    wp_storeField.
    wp_loadField.
    do 2 wp_storeField.
    wp_apply (wp_NewMap u64 bool).
    iIntros (resppP') "Hrespp'".
    wp_storeField.
    do 2 wp_loadField.
    wp_apply (wp_MapInsert with "Hrespp'"); first done.
    iIntros "Hrespp'".
    wp_pures.

    (*@     // Logical action: Prepare(@term).                                  @*)
    (*@                                                                         @*)
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_prepare (uint.nat term) with "Htermc Hterml Hlogn HinvO")
      as "(Htermc & Hterml & Hlogn & HinvO & #Hpromise)".
    { set_solver. }
    { word. }
    iMod ("HinvC" with "HinvO") as "_".

    (*@     return term, lsn                                                    @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    assert (Hton' : is_term_of_node nidme (uint.nat term)).
    { rewrite /is_term_of_node /max_nodes. word. }
    assert (Htermlt' : uint.Z terml ≤ uint.Z term) by word.
    assert (Hlcne' : uint.Z terml ≠ uint.Z term) by word.
    set logc := take _ log.
    set entsp := drop _ log.
    set respp' := map_insert _ _ _.
    iAssert (votes_in γ (dom respp') (uint.nat term) (uint.nat terml) (logc ++ entsp))%I as "Hvotes".
    { iNamed "Hpromise".
      iExists {[nidme := ds]}.
      rewrite big_sepM_singleton.
      iFrame "Hpastd".
      iPureIntro.
      split.
      { rewrite map_Forall_singleton. clear -Hlends Htermlt'. word. }
      split.
      { apply latest_term_before_quorum_with_singleton.
        by rewrite -latest_term_before_nodedec_unfold -Hlends -latest_term_nodedec_unfold.
      }
      split.
      { apply length_of_longest_ledger_in_term_singleton.
        by rewrite Hacpt take_drop.
      }
      split.
      { by rewrite map_Exists_singleton Hacpt take_drop. }
      { rewrite dom_singleton_L dom_insert_L. set_solver. }
    }
    iFrame "HiscandP HisleaderP".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { iClear "Hpreped". by case_decide. }
    iPureIntro.
    split; last lia.
    rewrite dom_insert_L. set_solver.
  Qed.

End nominate.

Section cquorum.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__cquorum (px : loc) (n : u64) nids :
    {{{ own_paxos_sc px nids }}}
      Paxos__cquorum #px #n
    {{{ (ok : bool), RET #ok; own_paxos_sc px nids ∗ ⌜size nids / 2 < uint.Z n⌝ }}}.
  Proof.
    (*@ func (px *Paxos) cquorum(n uint64) bool {                               @*)
    (*@     return quorum.ClassicQuorum(px.sc) <= n                             @*)
    (*@ }                                                                       @*)
  Admitted.

End cquorum.

Section lemma.
  Context `{!paxos_ghostG Σ}.

  Lemma node_inv_past_nodedecs_impl_prefix_base_ledger γ nid ds dslb psa t v :
    dslb !! t = Some (Accept v) ->
    is_past_nodedecs_lb γ nid dslb -∗
    node_inv_ds_psa γ nid ds psa -∗
    prefix_base_ledger γ t v.
  Proof.
    iIntros (Hv) "Hdslb Hnode".
    iNamed "Hnode". iNamed "Hpsa".
    iDestruct (past_nodedecs_prefix with "Hdslb Hpastd") as %Hprefix.
    pose proof (prefix_lookup_Some _ _ _ _ Hv Hprefix) as Hdst.
    specialize (Hfixed _ _ Hdst).
    by iDestruct (big_sepM_lookup with "Hpsalbs") as "?"; first apply Hfixed.
  Qed.

  Lemma safe_ledger_past_nodedecs_impl_prefix γ nids nid dslb t1 t2 v1 v2 :
    nid ∈ nids ->
    (t1 < t2)%nat ->
    dslb !! t2 = Some (Accept v2) ->
    safe_ledger_in γ nids t1 v1 -∗
    is_past_nodedecs_lb γ nid dslb -∗
    paxos_inv γ nids -∗
    ⌜prefix v1 v2⌝.
  Proof.
    iIntros (Hnid Hlt Hv2) "Hsafev1 Hdslb Hinv".
    iNamed "Hinv".
    iDestruct (nodes_inv_extract_ds_psa with "Hnodes") as (dss bs) "[Hndp Hnodes]".
    (* Obtain [dom termlm = dom bs]. *)
    iDestruct (big_sepM2_dom with "Hnodes") as %Hdomdp.
    iDestruct (big_sepM2_dom with "Hndp") as %Hdom.
    rewrite dom_map_zip_with_L Hdomdp intersection_idemp_L Hdomtermlm in Hdom.
    symmetry in Hdom.
    iClear "Hndp".
    (* Obtain [prefix_base_ledger γ t2 v2]. *)
    iAssert (prefix_base_ledger γ t2 v2)%I as (vb) "[#Hvb %Hvblev2]".
    { assert (is_Some (dss !! nid)) as [ds Hds].
      { by rewrite -elem_of_dom Hdomdp Hdom. }
      assert (is_Some (bs !! nid)) as [psa Hpsa].
      { by rewrite -elem_of_dom Hdom. }
      iDestruct (big_sepM2_lookup with "Hnodes") as "Hnode"; [apply Hds | apply Hpsa |].
      by iApply (node_inv_past_nodedecs_impl_prefix_base_ledger with "Hdslb Hnode").
    }
    (* Obtain [valid_base_proposals], [valid_lb_ballots], and [valid_ub_ballots]. *)
    iDestruct (nodes_inv_impl_valid_base_proposals with "Hsafepsb Hnodes") as %Hvbp.
    { apply Hdom. }
    iDestruct (nodes_inv_ds_psa_impl_nodes_inv_psa with "Hnodes") as "Hnodes".
    iDestruct (nodes_inv_impl_valid_lb_ballots with "Hpsb Hnodes") as %Hvlb.
    iDestruct (nodes_inv_impl_valid_ub_ballots with "Hps Hnodes") as %Hvub.
    (* Obtain [proposed_after_chosen] from the above. *)
    pose proof (vlb_vub_vbp_impl_pac _ _ _ Hvlb Hvub Hvbp) as Hpac.
    (* Obtain [chosen_in bs p v1] *)
    iDestruct (nodes_inv_safe_ledger_in_impl_chosen_in with "Hsafev1 Hnodes") as %Hchosen.
    { apply Hdom. }
    (* Obtain [psb !! t2 = Some vb]. *)
    iDestruct (base_proposal_lookup with "Hvb Hpsb") as %Hvb.
    iPureIntro.
    specialize (Hpac _ _ _ _ Hlt Hchosen Hvb).
    by trans vb.
  Qed.

End lemma.

Section collect.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__collect
    (px : loc) (nid : u64) (term : u64)
    (nidme : u64) (entsP : Slice.t) (ents : list string)
    (termc lsnc : u64) (logpeer : list string) nids γ :
    nid ∈ nids ->
    drop (uint.nat lsnc) logpeer = ents ->
    past_nodedecs_latest_before γ nid (uint.nat termc) (uint.nat term) logpeer -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_nominiated_with_termc_lsnc px nidme termc lsnc nids γ ∗
        own_slice entsP stringT (DfracOwn 1) ents
    }}}
      Paxos__collect #px #nid #term (to_val entsP)
    {{{ RET #(); own_paxos_nominated px nidme nids γ }}}.
  Proof.
    iIntros (Hinnids Hlogpeer) "#Hpromise #Hinv".
    iIntros (Φ) "!> [Hpx Hents] HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) collect(nid uint64, term uint64, ents []string) {      @*)
    (*@     _, recved := px.respp[nid]                                          @*)
    (*@     if recved {                                                         @*)
    (*@         // Vote from [nid] has already been received.                   @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hpx". iNamed "Hcand". iNamed "Honlyc".
    wp_loadField.
    wp_apply (wp_MapGet with "Hrespp").
    iIntros (v recved) "[%Hrecved Hrespp]".
    wp_if_destruct.
    { iApply "HΦ".
      iFrame "Hpx HentspP HiscandP".
      by iFrame "∗ # %".
    }
    apply map_get_false in Hrecved as [Hrecved _].
    clear Heqb v recved.

    (*@     if term < px.termp {                                                @*)
    (*@         // Simply record the response if the peer has a smaller term.   @*)
    (*@         px.respp[nid] = true                                            @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_MapInsert with "Hrespp"); first done.
      iIntros "Hrespp".
      wp_pures.
      iApply "HΦ".
      set logc := take _ log.
      set respp' := map_insert _ _ _.
      iAssert (votes_in γ (dom respp') (uint.nat termc) (uint.nat termp) (logc ++ entsp))%I
        as "Hvotes'".
      { iNamed "Hpromise".
        iNamed "Hvotes".
        iDestruct (big_sepM_insert_2 with "Hpastd Hdss") as "Hdss'".
        iFrame "Hdss'".
        iPureIntro.
        split.
        { by apply map_Forall_insert_2. }
        split.
        { rewrite /latest_term_before_quorum_nodedec.
          rewrite (latest_term_before_quorum_with_insert_le _ _ _ _ _ (uint.nat term)).
          { done. }
          { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
          { rewrite -Hlends. apply Hlatest. }
          rewrite -latest_term_before_quorum_nodedec_unfold Hlatestq.
          clear -Heqb.
          word.
        }
        split.
        { rewrite length_of_longest_ledger_in_term_insert_None; first apply Hlongestq.
          { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
          rewrite (latest_term_before_with_None (mbind nodedec_to_ledger) (length ds)).
          { done. }
          rewrite /latest_term_nodedec /latest_term_before_nodedec in Hlatest.
          word.
        }
        split.
        { apply map_Exists_insert_2_2; last done.
          by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom.
        }
        { by rewrite 2!dom_insert_L Hdomdss. }
      }
      iFrame "Hpx HentspP HiscandP".
      iFrame "∗ # %".
      iPureIntro.
      rewrite dom_insert_L.
      set_solver.
    }
    rewrite Z.nlt_ge in Heqb.
    rename Heqb into Htermple.

    (*@     if term == px.termp && uint64(len(ents)) <= uint64(len(px.entsp)) { @*)
    (*@         // Simply record the response if the peer has the same term, but not @*)
    (*@         // more entries (i.e., longer prefix).                          @*)
    (*@         px.respp[nid] = true                                            @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_and with "[HentspP Hentsp]").
    { iNamedAccu. }
    { by wp_pures. }
    { iIntros (Heq).
      iNamed 1.
      wp_apply wp_slice_len.
      wp_loadField.
      wp_apply wp_slice_len.
      wp_pures.
      by iFrame.
    }
    iNamed 1.
    wp_if_destruct.
    { destruct Heqb as [Heq Hszle].
      inv Heq.
      iDestruct (own_slice_sz with "Hents") as %Hszents.
      iDestruct (own_slice_sz with "Hentsp") as %Hszentsp.
      wp_loadField.
      wp_apply (wp_MapInsert with "Hrespp"); first done.
      iIntros "Hrespp".
      wp_pures.
      iApply "HΦ".
      set logc := take _ log.
      set respp' := map_insert _ _ _.
      iAssert (⌜uint.Z lsnc ≤ length log⌝)%I as %Hlsncub.
      { by iNamed "Hpx". }
      iAssert (votes_in γ (dom respp') (uint.nat termc) (uint.nat termp) (logc ++ entsp))%I
        as "Hvotes'".
      { iNamed "Hpromise".
        iNamed "Hvotes".
        iDestruct (big_sepM_insert_2 with "Hpastd Hdss") as "Hdss'".
        iFrame "Hdss'".
        iPureIntro.
        split.
        { by apply map_Forall_insert_2. }
        split.
        { rewrite /latest_term_before_quorum_nodedec.
          rewrite (latest_term_before_quorum_with_insert_le _ _ _ _ _ (uint.nat termp)).
          { done. }
          { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
          { rewrite -Hlends. apply Hlatest. }
          rewrite -latest_term_before_quorum_nodedec_unfold Hlatestq.
          done.
        }
        split.
        { rewrite (length_of_longest_ledger_in_term_insert_Some_length_le _ _ _ _ logpeer).
          { apply Hlongestq. }
          { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
          { by rewrite Hacpt. }
          rewrite length_drop in Hszents.
          rewrite Hlongestq length_app length_take.
          clear -Hszents Hszentsp Hszle Hlsncub.
          word.
        }
        split.
        { apply map_Exists_insert_2_2; last done.
          by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom.
        }
        { by rewrite 2!dom_insert_L Hdomdss. }
      }
      iFrame "Hpx HiscandP".
      iFrame "∗ # %".
      iPureIntro.
      rewrite dom_insert_L.
      set_solver.
    }
    apply Classical_Prop.not_and_or in Heqb.
    rename Heqb into Hcase.
    rewrite Z.nle_gt in Hcase.
    iDestruct (own_slice_sz with "Hents") as %Hszents.
    iDestruct (own_slice_sz with "Hentsp") as %Hszentsp.

    (*@     // Update the largest term and longest log seen so far in this preparing @*)
    (*@     // phase, and record the response.                                  @*)
    (*@     px.termp = term                                                     @*)
    (*@     px.entsp = ents                                                     @*)
    (*@     px.respp[nid] = true                                                @*)
    (*@                                                                         @*)
    do 2 wp_storeField.
    wp_loadField.
    wp_apply (wp_MapInsert with "Hrespp"); first done.
    iIntros "Hrespp".
    wp_pures.
    iApply "HΦ".
    set logc := take _ log.
    set respp' := map_insert _ _ _.
    iAssert (⌜uint.Z term < uint.Z termc⌝)%I as %Htermlt.
    { iNamed "Hpromise".
      iPureIntro.
      rewrite /latest_term_nodedec /latest_term_before_nodedec Hlends in Hlatest.
      set f := mbind _ in Hlatest.
      unshelve epose proof (latest_term_before_with_lt f (uint.nat termc) ds _) as Hlt.
      { word. }
      clear -Hlt Hlatest.
      word.
    }
    (* Prove that the committed part [logc] matches on the leader and peer sides. *)
    iInv "Hinv" as "> HinvO" "HinvC".
    iAssert (⌜logpeer = logc ++ ents⌝)%I as %->.
    { (* Obtain [safe_ledger_above]. *)
      iNamed "Hpx".
      iDestruct "Hsafecmt" as (p) "[Hsafecmt %Hple]".
      iNamed "Hpromise".
      destruct (decide (p < uint.nat term)%nat) as [Hlt | Hge].
      { iDestruct (safe_ledger_past_nodedecs_impl_prefix with "Hsafecmt Hpastd HinvO") as %Hlogc.
        { apply Hinnids. }
        { apply Hlt. }
        { apply Hacpt. }
        iPureIntro.
        subst logc.
        rewrite -(take_drop (uint.nat lsnc) logpeer) -Hlogpeer.
        f_equal.
        destruct Hlogc as [logtail ->].
        rewrite take_app_le; last first.
        { rewrite length_take. clear -Hlsncub. lia. }
        by rewrite take_idemp.
      }
      assert (term = termp) as ->.
      { clear -Hple Hge Htermple Hllep. word. }
      destruct Hcase as [? | Hlenlt]; first done.
      assert (p = uint.nat termp) as ->.
      { clear -Hple Hge Htermple Hllep. lia. }
      iDestruct "Hsafecmt" as (nidx nidsq) "Hsafecmt".
      iNamed "Hsafecmt".
      iDestruct (paxos_inv_impl_nodes_inv with "HinvO") as (termlm) "[Hnodes %Hdomtermlm]".
      iDestruct (nodes_inv_extract_ds_psa with "Hnodes") as (dss bs) "[Hndp Hnodes]".
      iDestruct (big_sepM2_dom with "Hnodes") as %Hdomdp.
      iDestruct (big_sepM2_dom with "Hndp") as %Hdom.
      rewrite dom_map_zip_with_L Hdomdp intersection_idemp_L Hdomtermlm in Hdom.
      symmetry in Hdom.
      iClear "Hndp".
      iDestruct (accepted_proposal_past_nodedecs_impl_prefix with "Hvacpt Hpastd Hnodes")
        as %Horprefix.
      { rewrite Hdom. apply Hmember. }
      { rewrite Hdom. apply Hinnids. }
      { apply Hacpt. }
      iPureIntro.
      assert (Hlogc : prefix logc logpeer).
      { destruct Horprefix as [Hprefix | Hprefix]; first apply Hprefix.
        rewrite (prefix_length_eq _ _ Hprefix); first done.
        rewrite length_take.
        unshelve epose proof (drop_lt_inv logpeer (uint.nat lsnc) _) as Hgt.
        { rewrite Hlogpeer. intros ->. simpl in Hszents. clear -Hszents Hlenlt. word. }
        lia.
      }
      subst logc.
      rewrite -(take_drop (uint.nat lsnc) logpeer) -Hlogpeer.
      f_equal.
      destruct Hlogc as [logtail ->].
      rewrite take_app_le; last first.
      { rewrite length_take. clear -Hlsncub. lia. }
      by rewrite take_idemp.
    }
    iMod ("HinvC" with "HinvO") as "_".
    iAssert (votes_in γ (dom respp') (uint.nat termc) (uint.nat term) (logc ++ ents))%I
      as "Hvotes'".
    { iNamed "Hpromise".
      iNamed "Hvotes".
      iDestruct (big_sepM_insert_2 with "Hpastd Hdss") as "Hdss'".
      iFrame "Hdss'".
      iPureIntro.
      split.
      { by apply map_Forall_insert_2. }
      split.
      { apply latest_term_before_quorum_with_insert_ge.
        { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
        { by rewrite /latest_term_nodedec /latest_term_before_nodedec Hlends in Hlatest. }
        rewrite -latest_term_before_quorum_nodedec_unfold Hlatestq.
        word.
      }
      split.
      { apply length_of_longest_ledger_in_term_insert_Some_length_ge.
        { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
        { by rewrite Hacpt. }
        { destruct (decide (termp = term)) as [-> | Hne].
          { (* Case: [termp = term]. *)
            destruct Hcase as [? | Hlonger]; first done.
            rewrite Hlongestq 2!length_app.
            lia.
          }
          { (* Case: [termp < term]. *)
            assert (Hltterm : uint.Z termp < uint.Z term) by word.
            replace (length_of_longest_ledger_in_term _ _) with O; first lia.
            rewrite /length_of_longest_ledger_in_term /length_of_longest_ledger.
            replace (omap _ _) with (∅ : gmap u64 ledger).
            { by rewrite fmap_empty map_fold_empty. }
            apply map_eq.
            intros nidx.
            rewrite lookup_empty lookup_omap.
            set f := mbind nodedec_to_ledger.
            set t := uint.nat termc.
            set p := uint.nat term.
            unshelve epose proof (latest_term_before_quorum_with_None f dss t p _) as Hnone.
            { rewrite -latest_term_before_quorum_nodedec_unfold Hlatestq.
              clear -Hltterm Htermlt.
              word.
            }
            destruct (dss !! nidx) as [dsx |] eqn:Hdsx; last done.
            simpl.
            specialize (Hnone _ _ Hdsx).
            by rewrite /ledger_in_term_with Hnone.
          }
        }
      }
      split.
      { apply map_Exists_insert_2_1. by rewrite Hacpt. }
      { by rewrite 2!dom_insert_L Hdomdss. }
    }
    iFrame "Hpx HiscandP HentspP".
    iFrame "∗ # %".
    iPureIntro.
    split; last lia.
    rewrite dom_insert_L. set_solver.
  Qed.

End collect.

Section ascend.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__ascend (px : loc) (nidme : u64) nids γ :
    know_paxos_inv γ nids -∗
    {{{ own_paxos_nominated px nidme nids γ }}}
      Paxos__ascend #px
    {{{ RET #(); own_paxos px nidme nids γ }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) ascend() {                                             @*)
    (*@     // Nothing should be done before obtaining a classic quorum of responses. @*)
    (*@     if !px.cquorum(uint64(len(px.respp))) {                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hpx". iNamed "Hcand". iNamed "Honlyc".
    wp_loadField.
    wp_apply (wp_MapLen with "Hrespp").
    iIntros "[%Hsz Hrespp]".
    iNamed "Hpx".
    wp_apply (wp_Paxos__cquorum with "Hsc").
    iIntros (ok) "[Hsc %Hquorum]".
    wp_if_destruct.
    { iApply "HΦ".
      iFrame "HtermcP HtermlP HiscandP HlogP HentspP".
      by iFrame "∗ # %".
    }

    (*@     // Add the longest prefix in the largest term among some quorum (i.e., @*)
    (*@     // @px.entsp) to our log starting from @px.lsnc.                    @*)
    (*@     px.log = append(px.log[: px.lsnc], px.entsp...)                     @*)
    (*@                                                                         @*)
    do 3 wp_loadField.
    wp_apply (wp_SliceTake_full with "Hlog"); first word.
    iIntros "Hlog".
    iDestruct (own_slice_to_small with "Hentsp") as "Hentsp".
    wp_apply (wp_SliceAppendSlice with "[$Hlog $Hentsp]"); first done.
    iIntros (logP') "[Hlog Hentsp]".
    wp_storeField.

    (*@     // Update @px.terml to @px.termc here.                              @*)
    (*@     px.terml = px.termc                                                 @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_storeField.

    (*@     // Transit from the candidate to the leader.                        @*)
    (*@     px.iscand = false                                                   @*)
    (*@     px.isleader = true                                                  @*)
    (*@                                                                         @*)
    iNamed "Hleader". iNamed "Honlyl".
    do 2 wp_storeField.

    (*@     // Logical action: Ascend(@px.termc, @px.log).                      @*)
    (*@                                                                         @*)
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_ascend with "[] Htermc Hterml Hlogn HinvO")
      as "(Htermc & Hterml & Hlogn & HinvO & Hps & #Hpsb & #Hacptlb)".
    { set_solver. }
    { apply Hton. }
    { word. }
    { iFrame "Hvotes".
      iPureIntro.
      split; first apply Hdomvts.
      rewrite /cquorum_size size_dom.
      word.
    }
    iMod ("HinvC" with "HinvO") as "_".

    (*@     // TODO: Write @px.log and @px.terml to disk.                       @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    set log' := _ ++ _.
    iAssert (own_paxos_leader px termc log' true γ)%I
      with "[$HisleaderP $HlsnpeersP $Hps]" as "Hleader".
    { by iFrame "Hpsb". }
    set entsc' := take (uint.nat lsnc) log'.
    iDestruct (safe_ledger_above_mono (uint.nat terml) entsc' (uint.nat termc) with "[Hsafecmt]")
      as "Hsafecmt".
    { word. }
    { subst entsc' log'.
      rewrite take_app_le; last first.
      { rewrite length_take. lia. }
      by rewrite take_idemp.
    }
    iFrame "Hleader".
    iFrame "HtermcP HtermlP HiscandP".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { iClear "Hpreped". by case_decide. }
    iPureIntro.
    split; first done.
    split; first done.
    subst log'.
    rewrite length_app length_take.
    lia.
  Qed.

End ascend.

Section prepare.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__prepare (px : loc) (lsn : u64) (nidme termc terml : u64) nids γ :
    termc ≠ terml ->
    {{{ own_paxos_with_termc_terml px nidme termc terml nids γ }}}
      Paxos__prepare #px #lsn
    {{{ (entsP : Slice.t) (ents logpeer : list string), RET (#terml, (to_val entsP));
        own_paxos_with_termc_terml px nidme termc terml nids γ ∗
        own_slice entsP stringT (DfracOwn 1) ents ∗
        past_nodedecs_latest_before γ nidme (uint.nat termc) (uint.nat terml) logpeer ∗
        ⌜drop (uint.nat lsn) logpeer = ents⌝
    }}}.
  Proof.
    iIntros (Hne Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) prepare(lsn uint64) (uint64, []string) {               @*)
    (*@     if uint64(len(px.log)) <= lsn {                                     @*)
    (*@         return px.terml, make([]string, 0)                              @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    case_decide; first done.
    wp_loadField.
    iDestruct (own_slice_sz with "Hlog") as %Hsz.
    wp_apply wp_slice_len.
    wp_if_destruct.
    { wp_loadField.
      wp_apply wp_NewSlice.
      iIntros (entsP) "Hents".
      wp_pures.
      iApply "HΦ".
      iFrame "Hcand Hleader".
      iFrame "∗ # %".
      case_decide; first done.
      iFrame "Hpreped".
      iPureIntro.
      rewrite uint_nat_W64_0 drop_ge /=; [done | lia].
    }

    (*@     ents := make([]string, uint64(len(px.log)) - lsn)                   @*)
    (*@     copy(ents, px.log[lsn :])                                           @*)
    (*@     return px.terml, ents                                               @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_apply wp_NewSlice.
    iIntros (entsP) "Hents".
    wp_loadField.
    iDestruct (own_slice_small_acc with "Hlog") as "[Hlog HlogC]".
    iDestruct (own_slice_small_acc with "Hents") as "[Hents HentsC]".
    wp_apply (wp_SliceCopy_SliceSkip_src with "[$Hlog $Hents]").
    { word. }
    { rewrite length_replicate /=. word. }
    iIntros "[Hlog Hents]".
    iDestruct ("HlogC" with "Hlog") as "Hlog".
    iDestruct ("HentsC" with "Hents") as "Hents".
    wp_loadField.
    wp_pures.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    iFrame "∗ # %".
    case_decide; first done.
    by iFrame "Hpreped".
  Qed.

End prepare.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

End program.
