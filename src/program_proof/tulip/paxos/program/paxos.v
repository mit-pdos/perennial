From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.invariance Require Import
  accept advance ascend commit extend prepare.
From Perennial.program_proof.tulip.util Require Import
  next_aligned.
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
  (*@     nid       uint64                                                    @*)
  (*@     // Mutex protecting fields below.                                   @*)
  (*@     mu        *sync.Mutex                                               @*)
  (*@     // Whether this node is the leader in @termc.                       @*)
  (*@     isleader  bool                                                      @*)
  (*@     // Heartbeat.                                                       @*)
  (*@     hb        bool                                                      @*)
  (*@     // Term in which this Paxos node currently is. Persistent.          @*)
  (*@     termc     uint64                                                    @*)
  (*@     // Term to which the log entries @ents belong. Persistent.          @*)
  (*@     terml     uint64                                                    @*)
  (*@     // List of log entries. Persistent.                                 @*)
  (*@     ents      []string                                                  @*)
  (*@     // LSN before which entries are committed (exclusively). Persistent. Note @*)
  (*@     // that persistence of @lsnc is *not* a safety requirement, but a   @*)
  (*@     // performance one (so that the leader's corresponding @lsnpeers entry can @*)
  (*@     // be updated more efficiently when this node crashes, rather than always @*)
  (*@     // start from 0).                                                   @*)
  (*@     lsnc      uint64                                                    @*)
  (*@     //                                                                  @*)
  (*@     // Candidate state below.                                           @*)
  (*@     //                                                                  @*)
  (*@     // Whether this node is the candidate in @termc.                    @*)
  (*@     iscand    bool                                                      @*)
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
  (*@     // send an APPEND-ENTRIES with LSN = @len(px.ents). Note that once  @*)
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

  Definition own_paxos_candidate (paxos : loc) (iscand : bool) : iProp Σ :=
    ∃ (termp : u64) (entspP : Slice.t) (entsp : list string)
      (resppP : loc) (respp : gmap u64 bool),
      "HiscandP" ∷ paxos ↦[Paxos :: "iscand"] #iscand ∗
      "HtermpP"  ∷ paxos ↦[Paxos :: "termp"] #termp ∗
      "HentspP"  ∷ paxos ↦[Paxos :: "entsp"] (to_val entspP) ∗
      "Hentsp"   ∷ (if iscand then own_slice entspP stringT (DfracOwn 1) entsp else True) ∗
      "HresppP"  ∷ paxos ↦[Paxos :: "respp"] #resppP ∗
      "Hrespp"   ∷ (if iscand then own_map resppP (DfracOwn 1) respp else True).

  Definition own_paxos_sc (paxos : loc) (nids : gset u64) : iProp Σ :=
    ∃ (sc : u64),
      "HscP" ∷ paxos ↦[Paxos :: "sc"] #sc ∗
      "%Hsc" ∷ ⌜size nids = uint.nat sc⌝.
  
  Definition own_paxos_common
    (paxos : loc) (termc : u64) (terml : u64) (nids : gset u64) γ : iProp Σ :=
    ∃ (me : u64) (nid : u64) (isleader : bool) (hb : bool)
      (entsP : Slice.t) (ents : list string)
      (lsnc : u64) (lsnpeersP : loc) (peers : gset u64),
      "HmeP"       ∷ paxos ↦[Paxos :: "me"] #me ∗
      "HnidP"      ∷ paxos ↦[Paxos :: "nid"] #nid ∗
      "HisleaderP" ∷ paxos ↦[Paxos :: "isleader"] #isleader ∗
      "HhbP"       ∷ paxos ↦[Paxos :: "hb"] #hb ∗
      "HtermcP"    ∷ paxos ↦[Paxos :: "termc"] #termc ∗
      "Htermc"     ∷ own_current_term_half γ nid (uint.nat termc) ∗
      "HtermlP"    ∷ paxos ↦[Paxos :: "terml"] #terml ∗
      "Hterml"     ∷ own_ledger_term_half γ nid (uint.nat terml) ∗
      "HentsP"     ∷ paxos ↦[Paxos :: "ents"] (to_val entsP) ∗
      "Hents"      ∷ own_slice entsP stringT (DfracOwn 1) ents ∗
      "Hlogn"      ∷ own_node_ledger_half γ nid ents ∗
      "HlsncP"     ∷ paxos ↦[Paxos :: "lsnc"] #lsnc ∗
      "HlsnpeersP" ∷ paxos ↦[Paxos :: "lsnpeers"] #lsnpeersP ∗
      "Hcomm"      ∷ own_paxos_comm paxos peers ∗
      "Hsc"        ∷ own_paxos_sc paxos nids ∗
      "%Hnids"     ∷ ⌜nids = {[nid]} ∪ peers⌝ ∗
      "%Hnid"      ∷ ⌜0 ≤ uint.Z nid < max_nodes⌝ ∗
      "%Hlsncub"   ∷ ⌜uint.Z lsnc ≤ length ents⌝.

  Definition own_paxos_with_termc_terml
    (paxos : loc) (termc : u64) (terml : u64) nids γ : iProp Σ :=
    ∃  (iscand : bool),
      "Hpx"   ∷ own_paxos_common paxos termc terml nids γ ∗
      "Hcand" ∷ own_paxos_candidate paxos iscand.

  Definition own_paxos paxos nids γ : iProp Σ :=
    ∃ (termc : u64) (terml : u64),
      own_paxos_with_termc_terml paxos termc terml nids γ.

  Definition is_paxos (paxos : loc) γ : iProp Σ :=
    ∃ (mu : loc) (nids : gset u64),
      "#HmuP"  ∷ readonly (paxos ↦[Paxos :: "mu"] #mu) ∗
      "#Hlock" ∷ is_lock paxosNS #mu (own_paxos paxos nids γ) ∗
      "#Hinv"  ∷ know_paxos_inv γ nids.

End repr.

Section stepdown.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__stepdown (px : loc) (term : u64) (termc terml : u64) nids γ :
    (uint.nat termc < uint.nat term)%nat ->
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc_terml px termc terml nids γ }}}
      Paxos__stepdown #px #term
    {{{ RET #(); own_paxos_with_termc_terml px term terml nids γ }}}.
  Proof.
    iIntros (Hlt) "#Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) stepdown(term uint64) {                                @*)
    (*@     px.termc = term                                                     @*)
    (*@     px.iscand = false                                                   @*)
    (*@     px.isleader = false                                                 @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    iNamed "Hcand".
    do 3 wp_storeField.

    (*@     // TODO: Write @px.termc to disk.                                   @*)
    (*@                                                                         @*)
    (*@     // Logical action: Prepare(@term).                                  @*)
    (*@ }                                                                       @*)
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_prepare (uint.nat term) with "Htermc Hterml Hlogn HinvO")
      as "(Htermc & Hterml & Hlogn & HinvO & #Hpromise)".
    { set_solver. }
    { apply Hlt. }
    iMod ("HinvC" with "HinvO") as "_".
    iApply "HΦ".
    iFrame "HiscandP".
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
    do 2 iNamed "Hpx".
    do 2 wp_loadField.
    wp_apply wp_NextAligned.
    { word. }
    { rewrite /max_nodes in Hnid. word. }
    iIntros (term [Hgttermc Hmod]).
    do 2 wp_storeField.

    (*@     // Obtain entries after @px.lsnc.                                   @*)
    (*@     lsn := px.lsnc                                                      @*)
    (*@     var ents = make([]string, 0, uint64(len(px.ents)) - lsn)            @*)
    (*@     copy(ents, px.ents[lsn :])                                          @*)
    (*@                                                                         @*)
    do 2 wp_loadField.
    wp_apply wp_slice_len.
    wp_apply wp_NewSlice.
    iIntros (entsP') "Hents'".
    wp_loadField.
    iDestruct (own_slice_sz with "Hents") as %Hsz.
    iDestruct (own_slice_small_acc with "Hents") as "[Hents HentsC]".
    iDestruct (own_slice_small_acc with "Hents'") as "[Hents' HentsC']".
    wp_apply (wp_SliceCopy_SliceSkip_src with "[$Hents $Hents']").
    { word. }
    { rewrite length_replicate /=. word. }
    iIntros "[Hents Hents']".
    iDestruct ("HentsC" with "Hents") as "Hents".
    iDestruct ("HentsC'" with "Hents'") as "Hents'".

    (*@     // Use the candidate's log term (@px.terml) and entries (after the committed @*)
    (*@     // LSN, @ents) as the initial preparing term and entries.           @*)
    (*@     px.iscand = true                                                    @*)
    (*@     px.termp  = px.terml                                                @*)
    (*@     px.entsp  = ents                                                    @*)
    (*@     px.respp  = make(map[uint64]bool)                                   @*)
    (*@     px.respp[px.nid] = true                                             @*)
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
    iFrame "HiscandP".
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
    (px : loc) (nidpeer : u64) (term : u64)
    (entspeerP : Slice.t) (entspeer : list string) nids γ :
    know_paxos_inv γ nids -∗
    {{{ own_paxos px nids γ ∗ own_slice entspeerP stringT (DfracOwn 1) entspeer }}}
      Paxos__collect #px #nidpeer #term (to_val entspeerP)
    {{{ RET #(); own_paxos px nids γ }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> [Hpx Hentspeer] HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) collect(nid uint64, term uint64, ents []string) {      @*)
    (*@     if !px.iscand {                                                     @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hpx".
    iNamed "Hcand".
    wp_loadField.
    wp_if_destruct.
    { iApply "HΦ".
      iFrame "Hpx".
      by iFrame "∗ # %".
    }

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
      iFrame "Hpx HentspP".
      iExists true.
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
      iFrame "Hpx".
      iExists true.
      by iFrame "∗ # %".
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

    (*@     // Nothing should be done before obtaining a classic quorum of responses. @*)
    (*@     if !px.cquorum(uint64(len(px.respp))) {                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapLen with "Hrespp").
    iIntros "[%Hsz Hrespp]".
    iNamed "Hpx".
    wp_apply (wp_Paxos__cquorum with "Hsc").
    iIntros (ok) "[Hsc %Hquorum]".
    wp_if_destruct.
    { iApply "HΦ".
      iFrame "HtermcP HtermlP".
      iExists true.
      iFrame "HentsP HentspP".
      by iFrame "∗ # %".
    }

    (*@     // Add the longest prefix in the largest term among some quorum (i.e., @*)
    (*@     // @px.entsp) to our log starting from @px.lsnc.                    @*)
    (*@     px.ents = append(px.ents[: px.lsnc], px.entsp...)                   @*)
    (*@                                                                         @*)
    do 3 wp_loadField.
    wp_apply (wp_SliceTake_full with "Hents"); first word.
    iIntros "Hents".
    iDestruct (own_slice_to_small with "Hentspeer") as "Hentspeer".
    wp_apply (wp_SliceAppendSlice with "[$Hents $Hentspeer]"); first done.
    iIntros (entsP') "[Hents Hentspeer]".
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
    do 2 wp_storeField.
    
    (*@     // Logical action: Ascend(@px.termc, px.ents).                      @*)
    (*@                                                                         @*)
    (*@     // TODO: Write @px.ents and @px.terml to disk.                      @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame "HtermcP HtermlP".
    iExists false.
    iFrame "HentsP".
    iFrame "∗ # %".
  Admitted.

End collect.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

End program.
