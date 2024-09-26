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

  Definition own_paxos_votes
    (termc termp : u64) (entsc entsp : list string) (respp : gmap u64 bool) γ : iProp Σ :=
    ∃ (dss : gmap u64 (list nodedec)),
      "#Hdss"      ∷ ([∗ map] nid↦ds ∈ dss, is_past_nodedecs_lb γ nid ds) ∗
      "%Hlendss"   ∷ ⌜map_Forall (λ _ ds, (length ds = uint.nat termc)%nat) dss⌝ ∗
      "%Hlatestq"  ∷ ⌜latest_term_before_quorum_nodedec dss (uint.nat termc) = (uint.nat termp)⌝ ∗
      "%Hlongestq" ∷ ⌜longest_proposal_in_term_nodedec dss (uint.nat termp) = Some (entsc ++ entsp)⌝ ∗
      "%Hrspd"     ∷ ⌜dom dss = dom respp⌝.

  Definition own_paxos_candidate_only
    (nidme termc terml termp : u64) (entsc : list string)
    (entspP : Slice.t) (resppP : loc) γ : iProp Σ :=
    ∃ (entsp : list string) (respp : gmap u64 bool),
      "Hentsp"    ∷ own_slice entspP stringT (DfracOwn 1) entsp ∗
      "Hrespp"    ∷ own_map resppP (DfracOwn 1) respp ∗
      "#Hvotes"   ∷ own_paxos_votes termc termp entsc entsp respp γ ∗
      "%Hton"     ∷ ⌜is_term_of_node nidme (uint.nat termc)⌝ ∗
      "%Hlcne"    ∷ ⌜uint.Z terml ≠ uint.Z termc⌝.

  Definition own_paxos_candidate
    (paxos : loc) (nid termc terml : u64) (entsc : list string) (iscand : bool) γ : iProp Σ :=
    ∃ (termp : u64) (entspP : Slice.t) (resppP : loc),
      "HiscandP" ∷ paxos ↦[Paxos :: "iscand"] #iscand ∗
      "HtermpP"  ∷ paxos ↦[Paxos :: "termp"] #termp ∗
      "HentspP"  ∷ paxos ↦[Paxos :: "entsp"] (to_val entspP) ∗
      "HresppP"  ∷ paxos ↦[Paxos :: "respp"] #resppP ∗
      "Honlyc"   ∷ (if iscand
                    then own_paxos_candidate_only nid termc terml termp entsc entspP resppP γ
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
    (paxos : loc) (termc lsnc : u64) (iscand isleader : bool) nids γ : iProp Σ :=
    ∃ (nidme terml : u64) (log : list string),
      let logc := (take (uint.nat lsnc) log) in
      "Hpx"     ∷ own_paxos_common paxos nidme termc terml lsnc log nids γ ∗
      "Hcand"   ∷ own_paxos_candidate paxos nidme termc terml logc iscand γ ∗
      "Hleader" ∷ own_paxos_leader paxos termc log isleader γ.

  Definition own_paxos_with_termc_lsnc
    (paxos : loc) (termc lsnc : u64) nids γ : iProp Σ :=
    ∃ (iscand : bool) (isleader : bool),
      own_paxos_internal paxos termc lsnc iscand isleader nids γ.

  Definition own_paxos_nominiated_with_termc_lsnc
    (paxos : loc) (termc lsnc : u64) nids γ : iProp Σ :=
    ∃ (isleader : bool),
      own_paxos_internal paxos termc lsnc true isleader nids γ.

  Definition own_paxos_with_termc
    (paxos : loc) (termc : u64) nids γ : iProp Σ :=
    ∃ (lsnc : u64) (iscand : bool) (isleader : bool),
      own_paxos_internal paxos termc lsnc iscand isleader nids γ.

  Definition own_paxos (paxos : loc) nids γ : iProp Σ :=
    ∃ (termc lsnc : u64) (iscand : bool) (isleader : bool),
      own_paxos_internal paxos termc lsnc iscand isleader nids γ.

  Definition own_paxos_nominated (paxos : loc) nids γ : iProp Σ :=
    ∃ (termc lsnc : u64) (isleader : bool),
      own_paxos_internal paxos termc lsnc true isleader nids γ.

  Definition is_paxos (paxos : loc) γ : iProp Σ :=
    ∃ (mu : loc) (nids : gset u64),
      "#HmuP"  ∷ readonly (paxos ↦[Paxos :: "mu"] #mu) ∗
      "#Hlock" ∷ is_lock paxosNS #mu (own_paxos paxos nids γ) ∗
      "#Hinv"  ∷ know_paxos_inv γ nids.

End repr.

Section stepdown.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__stepdown px (term : u64) termc nids γ :
    uint.Z termc < uint.Z term ->
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc px termc nids γ }}}
      Paxos__stepdown #px #term
    {{{ RET #(); own_paxos_with_termc px term nids γ }}}.
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
    by iFrame "∗ # %".
  Qed.

End stepdown.

Section nominate.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__nominate (px : loc) nids γ :
    know_paxos_inv γ nids -∗
    {{{ own_paxos px nids γ }}}
      Paxos__nominate #px
    {{{ (term : u64) (lsn : u64), RET (#term, #lsn); own_paxos px nids γ }}}.
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
    iAssert (own_paxos_votes term terml logc entsp {[nidme := true]} γ)%I as "Hvotes".
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
      { apply longest_proposal_in_term_with_singleton.
        by rewrite Hacpt take_drop.
      }
      { by rewrite 2!dom_singleton_L. }
    }
    iFrame "HiscandP HisleaderP".
    by iFrame "∗ # %".
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

Section collect.
  Context `{!paxos_ghostG Σ}.
    
  
End collect.

Section collect.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__collect
    (px : loc) (nid : u64) (term : u64)
    (entsP : Slice.t) (ents : list string)
    (termc lsnc : u64) (logpeer : list string) nids γ :
    drop (uint.nat lsnc) logpeer = ents ->
    past_nodedecs_latest_before γ nid (uint.nat termc) (uint.nat term) logpeer -∗
    {{{ own_paxos_nominiated_with_termc_lsnc px termc lsnc nids γ ∗
        own_slice entsP stringT (DfracOwn 1) ents
    }}}
      Paxos__collect #px #nid #term (to_val entsP)
    {{{ RET #(); own_paxos_nominated px nids γ }}}.
  Proof.
    iIntros (Hlogpeer) "#Hpromise".
    iIntros (Φ) "!> [Hpx Hentspeer] HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) collect(nid uint64, term uint64, ents []string) {      @*)
    (*@     if term < px.termp {                                                @*)
    (*@         // Simply record the response if the peer has a smaller term.   @*)
    (*@         px.respp[nid] = true                                            @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hpx". iNamed "Hcand". iNamed "Honlyc".
    wp_loadField.
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_MapInsert with "Hrespp"); first done.
      iIntros "Hrespp".
      wp_pures.
      iApply "HΦ".
      set logc := take _ log.
      iAssert (own_paxos_votes termc termp logc entsp (<[nid := true]> respp) γ)%I
        as "Hvotes'".
      { iNamed "Hpromise".
        iNamed "Hvotes".
        iDestruct (big_sepM_insert_2 with "Hpastd Hdss") as "Hdss'".
        iFrame "Hdss'".
        iPureIntro.
        split.
        { by apply map_Forall_insert_2. }
        split.
        { admit. }
        split.
        { admit. }
        { by rewrite 2!dom_insert_L Hrspd. }
      }
      iFrame "Hpx HentspP HiscandP".
      by iFrame "∗ # %".
    }

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
    { wp_loadField.
      wp_apply (wp_MapInsert with "Hrespp"); first done.
      iIntros "Hrespp".
      wp_pures.
      iApply "HΦ".
      iFrame "Hpx HiscandP".
      iFrame "∗ # %".
      admit.
    }

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
  Admitted.

End collect.

Section ascend.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__ascend (px : loc) nids γ :
    know_paxos_inv γ nids -∗
    {{{ own_paxos_nominated px nids γ }}}
      Paxos__ascend #px
    {{{ RET #(); own_paxos px nids γ }}}.
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
      iFrame "∗ # %".
      admit.
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
    { (* TODO: prove [safe_base_proposal]. *) admit. }
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
    iPureIntro.
    split; first done.
    split; first done.
    subst log'.
    rewrite length_app length_take.
    lia.
  Admitted.

End ascend.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

End program.
