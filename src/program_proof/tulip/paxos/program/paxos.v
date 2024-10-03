From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.invariance Require Import
  accept advance ascend commit extend prepare.
From Perennial.program_proof.tulip.program.util Require Import next_aligned sort.
From Perennial.program_proof.tulip.program Require Import quorum.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

(* Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. *)

Section repr.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  (*@ type Paxos struct {                                                     @*)
  (*@     // ID of this node.                                                 @*)
  (*@     nidme     uint64                                                    @*)
  (*@     // Node ID of its peers.                                            @*)
  (*@     peers     []uint64                                                  @*)
  (*@     // Address of this node.                                            @*)
  (*@     addrme    grove_ffi.Address                                         @*)
  (*@     // Addresses of other Paxos nodes.                                  @*)
  (*@     addrpeers map[uint64]grove_ffi.Address                              @*)
  (*@     // Size of the cluster. @sc = @len(peers) + 1.                      @*)
  (*@     sc        uint64                                                    @*)
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
  (*@     // Connections to peers. Used only when the node is a leader or a candidate. @*)
  (*@     //                                                                  @*)
  (*@     conns     map[uint64]grove_ffi.Connection                           @*)
  (*@ }                                                                       @*)
  Definition own_paxos_comm (paxos : loc) (peers : gset u64) : iProp Σ :=
    ∃ (addrme : u64) (addrpeersP : loc) (connsP : loc),
      "HaddrmeP"    ∷ paxos ↦[Paxos :: "addrme"] #addrme ∗
      "HaddrpeersP" ∷ paxos ↦[Paxos :: "addrpeers"] #addrpeersP ∗
      "HconnsP"     ∷ paxos ↦[Paxos :: "conns"] #connsP.

  Definition own_paxos_candidate_only
    (nidme termc terml termp : u64) (logc : list string)
    (entspP : Slice.t) (resppP : loc) nids γ : iProp Σ :=
    ∃ (entsp : list string) (respp : gmap u64 bool),
      "Hentsp"   ∷ own_slice entspP stringT (DfracOwn 1) entsp ∗
      "Hrespp"   ∷ own_map resppP (DfracOwn 1) respp ∗
      "#Hvotes"  ∷ votes_in γ (dom respp) (uint.nat termc) (uint.nat termp) (logc ++ entsp) ∗
      "%Hton"    ∷ ⌜is_term_of_node nidme (uint.nat termc)⌝ ∗
      "%Hdomvts" ∷ ⌜dom respp ⊆ nids⌝ ∗
      "%Hllep"   ∷ ⌜uint.Z terml ≤ uint.Z termp⌝ ∗
      "%Hpltc"   ∷ ⌜uint.Z termp < uint.Z termc⌝.

  Definition own_paxos_candidate
    (paxos : loc) (nid termc terml : u64) (logc : list string) (iscand : bool) nids γ : iProp Σ :=
    ∃ (termp : u64) (entspP : Slice.t) (resppP : loc),
      "HiscandP" ∷ paxos ↦[Paxos :: "iscand"] #iscand ∗
      "HtermpP"  ∷ paxos ↦[Paxos :: "termp"] #termp ∗
      "HentspP"  ∷ paxos ↦[Paxos :: "entsp"] (to_val entspP) ∗
      "HresppP"  ∷ paxos ↦[Paxos :: "respp"] #resppP ∗
      "Honlyc"   ∷ (if iscand
                    then own_paxos_candidate_only nid termc terml termp logc entspP resppP nids γ
                    else True).

  Lemma terml_eq_termc_impl_not_nominiated paxos nid termc terml logc iscand nids γ :
    terml = termc ->
    own_paxos_candidate paxos nid termc terml logc iscand nids γ -∗
    ⌜iscand = false⌝.
  Proof.
    iIntros (->) "Hcand".
    iNamed "Hcand".
    destruct iscand; last done.
    iNamed "Honlyc".
    clear -Hllep Hpltc. word.
  Qed.

  Definition accepted_or_committed_until γ nids nid (a : bool) t n : iProp Σ :=
    if a
    then is_accepted_proposal_length_lb γ nid t n
    else (∃ v, safe_ledger_above γ nids t v ∗ ⌜length v = n⌝)%I.

  #[global]
  Instance accepted_or_committed_until_persistent γ nids nid a t n :
    Persistent (accepted_or_committed_until γ nids nid a t n).
  Proof. destruct a; apply _. Defined.

  Definition safe_peer_lsns γ nids t (lsns : gmap u64 u64) : iProp Σ :=
    ∃ (aocm : gmap u64 bool),
      ([∗ map] nid ↦ i; a ∈ lsns; aocm,
         accepted_or_committed_until γ nids nid a t (uint.nat i)).

  Definition own_paxos_leader_only
    (termc terml : u64) (log : list string) (lsnpeersP : loc) (peers : gset u64)
    nids γ : iProp Σ :=
    ∃ (lsnpeers : gmap u64 u64),
      "Hps"        ∷ own_proposal γ (uint.nat termc) log ∗
      "Hlsnpeers"  ∷ own_map lsnpeersP (DfracOwn 1) lsnpeers ∗
      "#Haocm"     ∷ safe_peer_lsns γ nids (uint.nat termc) lsnpeers ∗
      "%Hleqc"     ∷ ⌜terml = termc⌝ ∗
      "%Hlelog"    ∷ ⌜map_Forall (λ _ i, (uint.nat i ≤ length log)%nat) lsnpeers⌝ ∗
      "%Hinclnids" ∷ ⌜dom lsnpeers ⊆ peers⌝.

  Definition own_paxos_leader
    (paxos : loc) (termc terml : u64) (log : list string) (isleader : bool) (peers : gset u64)
    nids γ : iProp Σ :=
    ∃ (lsnpeersP : loc),
      "HisleaderP" ∷ paxos ↦[Paxos :: "isleader"] #isleader ∗
      "HlsnpeersP" ∷ paxos ↦[Paxos :: "lsnpeers"] #lsnpeersP ∗
      "Honlyl"     ∷ (if isleader
                      then own_paxos_leader_only termc terml log lsnpeersP peers nids γ
                      else True).

  Definition own_paxos_sc (paxos : loc) (nids : gset u64) : iProp Σ :=
    ∃ (sc : u64),
      "HscP"    ∷ paxos ↦[Paxos :: "sc"] #sc ∗
      (* This condition allows a nicer implementation and proof for pushing the
      committed LSN (i.e., @px.push). *)
      "%Hmulti" ∷ ⌜1 < uint.Z sc⌝ ∗
      "%Hsc"    ∷ ⌜size nids = uint.nat sc⌝.

  Definition own_paxos_nids
    (paxos : loc) (nidme : u64) (peers : gset u64) nids : iProp Σ :=
    ∃ (peersP : Slice.t),
      "HnidmeP"  ∷ paxos ↦[Paxos :: "nidme"] #nidme ∗
      "HpeersP"  ∷ paxos ↦[Paxos :: "peers"] (to_val peersP) ∗
      "Hpeers"   ∷ own_slice peersP uint64T (DfracOwn 1) (elements peers) ∗
      "%Hnids"   ∷ ⌜nids = {[nidme]} ∪ peers⌝ ∗
      "%Hnidsne" ∷ ⌜nidme ∉ peers⌝.

  Definition own_paxos_common
    (paxos : loc) (nidme termc terml lsnc : u64) (log : list string) nids γ : iProp Σ :=
    ∃ (hb : bool) (logP : Slice.t),
      "HhbP"     ∷ paxos ↦[Paxos :: "hb"] #hb ∗
      "HtermcP"  ∷ paxos ↦[Paxos :: "termc"] #termc ∗
      "Htermc"   ∷ own_current_term_half γ nidme (uint.nat termc) ∗
      "HtermlP"  ∷ paxos ↦[Paxos :: "terml"] #terml ∗
      "Hterml"   ∷ own_ledger_term_half γ nidme (uint.nat terml) ∗
      "HlogP"    ∷ paxos ↦[Paxos :: "log"] (to_val logP) ∗
      "Hlog"     ∷ own_slice logP stringT (DfracOwn 1) log ∗
      "Hlogn"    ∷ own_node_ledger_half γ nidme log ∗
      "HlsncP"   ∷ paxos ↦[Paxos :: "lsnc"] #lsnc ∗
      "Hsc"      ∷ own_paxos_sc paxos nids ∗
      "#Hgebase" ∷ prefix_base_ledger γ (uint.nat terml) log ∗
      "#Hpreped" ∷ (if decide (termc = terml)
                    then True
                    else past_nodedecs_latest_before γ nidme (uint.nat termc) (uint.nat terml) log) ∗
      "#Hacpted" ∷ is_accepted_proposal_lb γ nidme (uint.nat terml) log ∗
      "#Hcmted"  ∷ safe_ledger_above γ nids (uint.nat terml) (take (uint.nat lsnc) log) ∗
      "%Hnid"    ∷ ⌜0 ≤ uint.Z nidme < max_nodes⌝ ∗
      "%Htermlc" ∷ ⌜uint.Z terml ≤ uint.Z termc⌝ ∗
      "%Hlsncub" ∷ ⌜uint.Z lsnc ≤ length log⌝.

  (** Note on designing the lock invariant abstraction: [own_paxos_internal]
  serves as a boundary for exposing internal states required for use by internal
  methods. All [own_paxos{*}_with_{*}] should then be derived from it. Values
  that are decomposed (e.g., [terml]) into smaller pieces of representation
  predicates should be existentially quantified. *)
  Definition own_paxos_internal
    (paxos : loc) (nidme termc terml lsnc : u64) (iscand isleader : bool) nids γ : iProp Σ :=
    ∃ (log : list string) (peers : gset u64),
      let logc := (take (uint.nat lsnc) log) in
      "Hpx"     ∷ own_paxos_common paxos nidme termc terml lsnc log nids γ ∗
      "Hcand"   ∷ own_paxos_candidate paxos nidme termc terml logc iscand nids γ ∗
      "Hleader" ∷ own_paxos_leader paxos termc terml log isleader peers nids γ ∗
      "Hnids"   ∷ own_paxos_nids paxos nidme peers nids ∗
      "Hcomm"   ∷ own_paxos_comm paxos peers.

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

  Definition own_paxos_following_with_termc
    (paxos : loc) (nidme termc : u64) nids γ : iProp Σ :=
    ∃ (terml lsnc : u64),
      own_paxos_internal paxos nidme termc terml lsnc false false nids γ.

  Definition own_paxos_leading_with_termc
    (paxos : loc) (nidme termc : u64) nids γ : iProp Σ :=
    ∃ (terml lsnc : u64) (iscand : bool),
      own_paxos_internal paxos nidme termc terml lsnc iscand true nids γ.

  Definition own_paxos_with_termc_terml
    (paxos : loc) (nidme termc terml : u64) nids γ : iProp Σ :=
    ∃ (lsnc : u64) (iscand : bool) (isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc iscand isleader nids γ.

  Definition own_paxos_with_termc_terml_iscand
    (paxos : loc) (nidme termc terml : u64) (iscand : bool) nids γ : iProp Σ :=
    ∃ (lsnc : u64) (isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc iscand isleader nids γ.

  Definition own_paxos (paxos : loc) (nidme : u64) nids γ : iProp Σ :=
    ∃ (termc terml lsnc : u64) (iscand : bool) (isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc iscand isleader nids γ.

  Definition own_paxos_nominated (paxos : loc) (nidme : u64) nids γ : iProp Σ :=
    ∃ (termc terml lsnc : u64) (isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc true isleader nids γ.

  Definition own_paxos_leading (paxos : loc) (nidme : u64) nids γ : iProp Σ :=
    ∃ (termc terml lsnc : u64) (iscand : bool),
      own_paxos_internal paxos nidme termc terml lsnc iscand true nids γ.

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
    uint.Z termc ≤ uint.Z term ->
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__stepdown #px #term
    {{{ RET #(); own_paxos_following_with_termc px nidme term nids γ }}}.
  Proof.
    iIntros (Hlt) "#Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) stepdown(term uint64) {                                @*)
    (*@     px.termc = term                                                     @*)
    (*@     px.iscand = false                                                   @*)
    (*@     px.isleader = false                                                 @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hcand". iNamed "Hleader". iNamed "Hnids".
    do 3 wp_storeField.

    (*@     // TODO: Write @px.termc to disk.                                   @*)
    (*@                                                                         @*)
    (*@     // Logical action: Prepare(@term).                                  @*)
    (*@ }                                                                       @*)
    destruct (decide (termc = term)) as [-> | Hne].
    { (* Case: [termc = term]. No logical updates required. *)
      iApply "HΦ".
      iFrame "HiscandP HisleaderP".
      by iFrame "∗ # %".
    }
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_prepare (uint.nat term) with "Htermc Hterml Hlogn HinvO")
      as "(Htermc & Hterml & Hlogn & HinvO & #Hpromise)".
    { set_solver. }
    { word. }
    iMod ("HinvC" with "HinvO") as "_".
    iApply "HΦ".
    iFrame "HisleaderP HiscandP".
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
    do 2 iNamed "Hpx". iNamed "Hleader". iNamed "Hnids".
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
      iDestruct "Hcmted" as (p) "[Hcmted %Hple]".
      iNamed "Hpromise".
      destruct (decide (p < uint.nat term)%nat) as [Hlt | Hge].
      { (* Case: The safe term [p] is less than the term [term] of [logpeer] / [ents].  *)
        iDestruct (safe_ledger_past_nodedecs_impl_prefix with "Hcmted Hpastd HinvO") as %Hlogc.
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
      (* Case: The safe term equal to the entries term. *)
      assert (term = termp) as ->.
      { clear -Hple Hge Htermple Hllep. word. }
      destruct Hcase as [? | Hlenlt]; first done.
      assert (p = uint.nat termp) as ->.
      { clear -Hple Hge Htermple Hllep. lia. }
      iDestruct "Hcmted" as (nidx nidsq) "Hcmted".
      iNamed "Hcmted".
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
    (*@     px.lsnpeers = make(map[uint64]uint64)                               @*)
    (*@                                                                         @*)
    iNamed "Hleader".
    do 2 wp_storeField.
    wp_apply (wp_NewMap u64 u64).
    iIntros (lsnpeersP') "Hlsnpeers".
    wp_storeField.

    (*@     // Logical action: Ascend(@px.termc, @px.log).                      @*)
    (*@                                                                         @*)
    iNamed "Hnids".
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
    set logc := take (uint.nat lsnc) log.
    set log' := logc ++ entsp.
    set logc' := take (uint.nat lsnc) log'.
    iAssert (own_paxos_leader px termc termc log' true peers nids γ)%I
      with "[$HisleaderP $HlsnpeersP $Hlsnpeers $Hps]" as "Hleader".
    { iSplit; last done.
      iExists ∅.
      by rewrite big_sepM2_empty.
    }
    iAssert (prefix_base_ledger γ (uint.nat termc) log')%I as "#Hpfb'".
    { by iFrame "Hpsb". }
    iDestruct (safe_ledger_above_mono (uint.nat terml) (uint.nat termc) logc' with "[]")
      as "Hcmted'".
    { word. }
    { subst logc log' logc'.
      rewrite take_app_le; last first.
      { rewrite length_take. lia. }
      by rewrite take_idemp.
    }
    iClear "Hcmted".
    iFrame "Hleader".
    iFrame "HtermcP HtermlP HiscandP Hpfb'".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { iClear "Hpreped". by case_decide. }
    iPureIntro.
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

Section accept.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__accept
    (px : loc) (lsn : u64) (term : u64) (entsP : Slice.t) (ents logleader : list string)
    (nidme : u64) nids γ :
    (uint.nat lsn ≤ length logleader)%nat ->
    drop (uint.nat lsn) logleader = ents ->
    prefix_base_ledger γ (uint.nat term) logleader -∗
    prefix_growing_ledger γ (uint.nat term) logleader -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_following_with_termc px nidme term nids γ ∗
        own_slice entsP stringT (DfracOwn 1) ents
    }}}
      Paxos__accept #px #lsn #term (to_val entsP)
    {{{ (lsna : u64) (loga : list string), RET #lsna;
        own_paxos_following_with_termc px nidme term nids γ ∗
        (is_accepted_proposal_lb γ nidme (uint.nat term) loga ∨
         safe_ledger_above γ nids (uint.nat term) loga) ∗
        ⌜length loga = uint.nat lsna⌝
    }}}.
  Proof.
    iIntros (Hlsnle Hents) "#Hpfb #Hpfg #Hinv".
    iIntros (Φ) "!> [Hpx Hents] HΦ".
    wp_rec.

    (*@ func (px *Paxos) accept(lsn uint64, term uint64, ents []string) uint64 { @*)
    (*@     if term != px.terml {                                               @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    set logc := take _ log.
    wp_loadField.
    wp_if_destruct.
    { rename Heqb into Htermne.
      wp_loadField.

      (*@         // Our log term does not match the term @term of @ents. Return an error @*)
      (*@         // if @px.lsnc < @lsn, as log consistency at @term cannot be guaranteed. @*)
      (*@         if px.lsnc != lsn {                                             @*)
      (*@             return px.lsnc                                              @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { wp_loadField.
        rename Heqb into Hlsnne.
        iApply "HΦ".
        iSplit.
        { iFrame "Hcand Hleader HlogP".
          by iFrame "∗ # %".
        }
        iDestruct (safe_ledger_above_mono (uint.nat terml) (uint.nat term) logc with "Hcmted")
          as "Hcmted'".
        { clear -Htermlc. word. }
        iFrame "Hcmted'".
        iPureIntro.
        rewrite length_take.
        lia.
      }

      (*@         // Append @ents to our own log starting at @lsn.                @*)
      (*@         px.log = px.log[: lsn]                                          @*)
      (*@         px.log = append(px.log, ents...)                                @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply (wp_SliceTake_full with "Hlog"); first word.
      iIntros "Hlog".
      iDestruct (own_slice_to_small with "Hents") as "Hents".
      wp_storeField.
      wp_loadField.
      wp_apply (wp_SliceAppendSlice with "[$Hlog $Hents]"); first done.
      iIntros (logP') "[Hlog Hents]".
      wp_storeField.

      (*@         // Update the log term to @term.                                @*)
      (*@         px.terml = term                                                 @*)
      (*@                                                                         @*)
      wp_storeField.

      (*@         // TODO: Write @px.log and @px.terml to disk.                   @*)
      (*@                                                                         @*)
      (*@         // Return LSN at the end of our log after accepting @ents.      @*)
      (*@         lsna := uint64(len(px.log))                                     @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply wp_slice_len.
      wp_pures.

      (*@         // Logical action: Advance(term, log).                          @*)
      (*@                                                                         @*)
      iNamed "Hnids".
      iInv "Hinv" as "> HinvO" "HinvC".
      iMod (paxos_inv_advance with "Hpfb Hpfg Htermc Hterml Hlogn HinvO")
        as "(Htermc & Hterml & Hlogn & HinvO & #Hacpted')".
      { set_solver. }
      { clear -Htermlc Htermne. word. }
      iMod ("HinvC" with "HinvO") as "_".

      (*@         return lsna                                                     @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      iApply "HΦ".
      set log' := logc ++ _.
      set logc' := take (uint.nat lsn) log'.
      iInv "Hinv" as "> HinvO" "HinvC".
      iAssert (⌜logleader = log'⌝)%I as %Heq.
      { subst log'.
        iDestruct "Hcmted" as (p) "[Hsafep %Hple]".
        iDestruct (safe_ledger_prefix_base_ledger_impl_prefix with "Hsafep Hpfb HinvO")
          as %Hprefix.
        { clear -Htermlc Htermne Hple. word. }
        iPureIntro.
        rewrite -{1}(take_drop (uint.nat lsn) logleader).
        f_equal.
        subst logc.
        destruct Hprefix as [logtail ->].
        rewrite take_app_le; last first.
        { rewrite length_take. clear -Hlsncub. lia. }
        by rewrite take_idemp.
      }
      iMod ("HinvC" with "HinvO") as "_".
      iDestruct (safe_ledger_above_mono (uint.nat terml) (uint.nat term) logc' with "[]")
        as "Hcmted'".
      { word. }
      { subst logc'.
        rewrite take_app_le; last first.
        { rewrite length_take. lia. }
        by rewrite take_idemp.
      }
      iClear "Hcmted".
      iModIntro.
      rewrite Heq.
      iSplit.
      { iFrame "Hcand Hleader HlogP HtermlP".
        iClear "Hpreped".
        case_decide; last done.
        iFrame "∗ # %".
        iPureIntro.
        split; first done.
        rewrite -Heq.
        word.
      }
      iFrame "Hacpted'".
      iApply (own_slice_sz with "Hlog").
    }

    (*@     // We're in the same term. Now we should skip appending @ents iff there's @*)
    (*@     // gap between @ents and @px.log OR appending @ents starting at @lsn @*)
    (*@     // actually shortens the log.                                       @*)
    (*@     nents := uint64(len(px.log))                                        @*)
    (*@     if nents < lsn || lsn + uint64(len(ents)) <= nents {                @*)
    (*@         return nents                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_apply (wp_or with "[Hents]").
    { iNamedAccu. }
    { wp_pures. done. }
    { iIntros "_".
      iNamed 1.
      wp_apply wp_slice_len.
      wp_pures.
      by iFrame.
    }
    iNamed 1.
    wp_if_destruct.
    { iApply "HΦ".
      iModIntro.
      iSplit.
      { iFrame "Hcand Hleader HlogP".
        by iFrame "∗ # %".
      }
      iFrame "Hacpted".
      iApply (own_slice_sz with "Hlog").
    }
    apply Classical_Prop.not_or_and in Heqb.
    destruct Heqb as [Hnogap Hlonger].
    rewrite Z.nlt_ge in Hnogap.
    rewrite Z.nle_gt in Hlonger.
    iDestruct (own_slice_sz with "Hlog") as %Hszlog.

    (*@     // Append @ents to our own log starting at @lsn.                    @*)
    (*@     px.log = px.log[: lsn]                                              @*)
    (*@     px.log = append(px.log, ents...)                                    @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_SliceTake_full with "Hlog").
    { clear -Hnogap Hszlog. word. }
    iIntros "Hlog".
    wp_storeField.
    wp_loadField.
    iDestruct (own_slice_to_small with "Hents") as "Hents".
    wp_apply (wp_SliceAppendSlice with "[$Hlog $Hents]"); first done.
    iIntros (logP') "[Hlog Hents]".
    wp_storeField.

    (*@     // TODO: Write @px.log to disk.                                     @*)
    (*@                                                                         @*)

    (*@     lsna := uint64(len(px.log))                                         @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_pures.

    (*@     // Logical action: Accept(term, log)                                @*)
    (*@                                                                         @*)
    iDestruct (own_slice_small_sz with "Hents") as %Hszents.
    assert (length log ≤ length logleader)%nat as Hlenlog.
    { rewrite length_drop in Hszents.
      rewrite word.unsigned_add in Hlonger.
      clear -Hszlog Hszents Hnogap Hlonger.
      word.
    }
    iNamed "Hnids".
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_accept with "Hpfb Hpfg Htermc Hterml Hlogn HinvO")
      as "(Htermc & Hterml & Hlogn & HinvO & #Hacpted')".
    { set_solver. }
    { apply Hlenlog. }
    iMod ("HinvC" with "HinvO") as "_".

    (*@     return lsna                                                         @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iAssert (⌜prefix log logleader⌝)%I as %Hprefix.
    { iDestruct (accepted_proposal_lb_prefix with "Hacpted Hacpted'") as %Hprefix.
      iPureIntro.
      destruct Hprefix as [? | Hprefix]; first done.
      by rewrite (prefix_length_eq _ _ Hprefix Hlenlog).
    }
    assert (take (uint.nat lsn) log = take (uint.nat lsn) logleader) as ->.
    { rewrite (take_prefix_le _ _ (uint.nat lsn) _ Hprefix); first done.
      clear -Hnogap Hszlog. word.
    }
    rewrite take_drop.
    iModIntro.
    iSplit.
    { iFrame "Hcand Hleader HlogP HtermlP".
      case_decide; last done.
      iFrame "∗ # %".
      iSplit.
      { rewrite -(take_prefix_le _ _ (uint.nat lsnc) _ Hprefix); first done.
        clear -Hlsncub. word.
      }
      iPureIntro.
      apply prefix_length in Hprefix.
      clear -Hlsncub Hprefix.
      word.
    }
    iFrame "Hacpted'".
    by iApply (own_slice_sz with "Hlog").
  Qed.

End accept.

Section obtain.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__obtain (px : loc) (nid : u64) (nidme termc : u64) nids γ :
    {{{ own_paxos_leading_with_termc px nidme termc nids γ }}}
      Paxos__obtain #px #nid
    {{{ (lsne : u64) (entsP : Slice.t) (ents loga : list string), RET (#lsne, (to_val entsP)); 
        own_paxos_leading_with_termc px nidme termc nids γ ∗
        own_slice entsP stringT (DfracOwn 1) ents ∗
        prefix_base_ledger γ (uint.nat termc) loga ∗
        prefix_growing_ledger γ (uint.nat termc) loga ∗
        ⌜drop (uint.nat lsne) loga = ents⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) obtain(nid uint64) (uint64, []string) {                @*)
    (*@     lsne, ok := px.lsnpeers[nid]                                        @*)
    (*@                                                                         @*)
    iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl".
    wp_loadField.
    wp_apply (wp_MapGet with "Hlsnpeers").
    iIntros (lsne ok) "[%Hok Hlsnpeers]".
    wp_pures.

    (*@     if !ok {                                                            @*)
    (*@         // The follower has not reported the matched LSN, so send an    @*)
    (*@         // empty APPEND-ENTRIES request.                                @*)
    (*@         return uint64(len(px.log)), make([]string, 0)                   @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iAssert (prefix_growing_ledger γ (uint.nat termc) log)%I as "#Hpfg".
    { iDestruct (proposal_witness with "Hps") as "#Hpslb".
      by iFrame "Hpslb".
    }
    iNamed "Hpx".
    iDestruct (own_slice_sz with "Hlog") as %Hszlog.
    wp_if_destruct.
    { wp_loadField.
      wp_apply wp_slice_len.
      wp_apply wp_NewSlice.
      iIntros (entsP) "Hents".
      wp_pures.
      iApply "HΦ".
      iFrame "Hcand".
      iFrame "∗ # %".
      iPureIntro.
      by rewrite -Hszlog drop_all uint_nat_W64_0 /=.
    }
    apply map_get_true in Hok.
    apply Hlelog in Hok.

    (*@     // The follower has reported up to where the log is matched         @*)
    (*@     // (i.e., @lsne), so send everything after that.                    @*)
    (*@     ents := make([]string, uint64(len(px.log)) - lsne)                  @*)
    (*@     copy(ents, px.log[lsne :])                                          @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_apply wp_NewSlice.
    iIntros (entsP) "Hents".
    iDestruct (own_slice_sz with "Hents") as %Hszents.
    wp_loadField.
    iDestruct (own_slice_small_acc with "Hlog") as "[Hlog HlogC]".
    iDestruct (own_slice_small_acc with "Hents") as "[Hents HentsC]".
    wp_apply (wp_SliceCopy_SliceSkip_src with "[$Hlog $Hents]").
    { clear -Hok. word. }
    { rewrite length_replicate. clear -Hszents Hszlog Hok. word. }
    iIntros "[Hlog Hents]".
    iDestruct ("HlogC" with "Hlog") as "Hlog".
    iDestruct ("HentsC" with "Hents") as "Hents".
    wp_pures.

    (*@     return lsne, ents                                                   @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame "Hcand".
    by iFrame "∗ # %".
  Qed.

End obtain.

Section forward.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__forward
    (px : loc) (nid lsn : u64) (nidme termc : u64) (loga : list string) nids γ :
    nid ≠ nidme ->
    nid ∈ nids ->
    length loga = uint.nat lsn ->
    (is_accepted_proposal_lb γ nid (uint.nat termc) loga ∨
     safe_ledger_above γ nids (uint.nat termc) loga) -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_leading_with_termc px nidme termc nids γ }}}
      Paxos__forward #px #nid #lsn
    {{{ (forwarded : bool), RET #forwarded; own_paxos_leading_with_termc px nidme termc nids γ }}}.
  Proof.
    iIntros (Hnotme Hnid Hlena) "#Haoc #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) forward(nid uint64, lsn uint64) bool {                 @*)
    (*@     lsnpeer, ok := px.lsnpeers[nid]                                     @*)
    (*@                                                                         @*)
    iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl".
    subst terml.
    wp_loadField.
    wp_apply (wp_MapGet with "Hlsnpeers").
    iIntros (lsnpeer ok) "[%Hok Hlsnpeers]".
    wp_pures.

    (*@     if !ok || lsnpeer < lsn {                                           @*)
    (*@         // Advance the peer's matching LSN.                             @*)
    (*@         px.lsnpeers[nid] = lsn                                          @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    (* Not sure how to properly handle TC resolution here. *)
    unshelve wp_apply (wp_or_pure (negb ok)).
    { shelve. }
    { apply _. }
    { shelve. }
    { wp_pures. by destruct ok; case_bool_decide. }
    { iIntros (_). by  wp_pures. }
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_MapInsert with "Hlsnpeers"); first done.
      iIntros "Hlsnpeers".
      wp_pures.
      iInv "Hinv" as "> HinvO" "HinvC".
      iAssert (⌜(length loga ≤ length log)%nat⌝)%I as %Hle.
      { iDestruct "Haoc" as "[Hacpted | Hcmted]".
        { (* Case: [loga] is accepted by [nid]. *)
          iDestruct (accepted_proposal_growing_proposal_impl_prefix with "Hacpted Hps HinvO")
            as %Hprefix.
          { apply Hnid. }
          iPureIntro.
          by apply prefix_length.
        }
        (* Case: [loga] has already be committed at this or an early term. *)
        iDestruct "Hcmted" as (p) "[Hsafe %Hple]".
        destruct (decide (p = uint.nat termc)) as [-> | Hne].
        { (* Case: [loga] committed in the current term. *)
          iDestruct "Hsafe" as (nidx) "Hsafe".
          iNamed "Hsafe".
          iDestruct (accepted_proposal_growing_proposal_impl_prefix with "Hvacpt Hps HinvO")
            as %Hprefix.
          { apply Hmember. }
          iPureIntro.
          by apply prefix_length.
        }
        (* Case: [loga] committed in an early term. *)
        assert (Hlt : (p < uint.nat termc)%nat) by lia.
        iNamed "Hpx".
        iDestruct (safe_ledger_prefix_base_ledger_impl_prefix with "Hsafe Hgebase HinvO")
          as %Hprefix.
        { apply Hlt. }
        iPureIntro.
        by apply prefix_length.
      }
      iMod ("HinvC" with "HinvO") as "_".
      iNamed "Hnids".
      iApply "HΦ".
      iFrame "Hpx Hcand".
      iFrame "∗ #".
      iModIntro.
      iAssert (safe_peer_lsns γ nids (uint.nat termc) (<[nid := lsn]> lsnpeers))%I as "Haocm'".
      { iDestruct "Haoc" as "[Hacpted | Hcmted]".
        { iNamed "Haocm".
          iExists (<[nid := true]> aocm).
          iApply big_sepM2_insert_2; last done.
          iFrame "Hacpted".
          iPureIntro. lia.
        }
        { iNamed "Haocm".
          iExists (<[nid := false]> aocm).
          iApply big_sepM2_insert_2; last done.
          iFrame "Hcmted".
          iPureIntro. lia.
        }
      }
      iFrame "Haocm'".
      iPureIntro.
      split; last set_solver.
      split; first done.
      split.
      { apply map_Forall_insert_2; [lia | apply Hlelog]. }
      { rewrite dom_insert_L. set_solver. }
    }

    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame "Hpx Hcand".
    by iFrame "∗ # %".
  Qed.

End forward.

Section commit.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__commit
    (px : loc) (lsn : u64) (nidme term : u64) (logc : list string) nids γ :
    length logc = uint.nat lsn ->
    safe_ledger_above γ nids (uint.nat term) logc -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc_terml_iscand px nidme term term false nids γ }}}
      Paxos__commit #px #lsn
    {{{ RET #(); own_paxos_with_termc_terml_iscand px nidme term term false nids γ }}}.
  Proof.
    iIntros (Hlenlogc) "#Hsafe #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) commit(lsn uint64) {                                   @*)
    (*@     if lsn <= px.lsnc {                                                 @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hnids".
    wp_loadField.
    wp_if_destruct.
    { iApply "HΦ".
      iFrame "Hleader Hcand".
      by iFrame "∗ # %".
    }
    rename Heqb into Hgtlsnc.
    rewrite Z.nle_gt in Hgtlsnc.
    iDestruct (own_slice_sz with "Hlog") as %Hszlog.
    iApply fupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    iAssert (⌜prefix log logc ∨ prefix logc log⌝)%I as %Horprefix.
    { iDestruct "Hsafe" as (p) "[Hsafe %Hple]".
      destruct (decide (p = uint.nat term)) as [-> | Hne]; last first.
      { iDestruct (safe_ledger_prefix_base_ledger_impl_prefix with "Hsafe Hgebase HinvO")
          as %Hprefix.
        { clear -Hple Hne. lia. }
        iPureIntro.
        by right.
      }
      iNamed "Hsafe".
      iDestruct (paxos_inv_impl_nodes_inv_psa with "HinvO") as (bs) "[Hnodes %Hdombs]".
      iApply (nodes_inv_is_accepted_proposal_lb_impl_prefix with "Hacpted Hvacpt Hnodes").
      { set_solver. }
      { by rewrite Hdombs. }
    }
    iMod ("HinvC" with "HinvO") as "_".
    iModIntro.

    (*@     if uint64(len(px.log)) < lsn {                                      @*)
    (*@         px.lsnc = uint64(len(px.log))                                   @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_if_destruct.
    { rename Heqb into Hgtlog.
      wp_loadField.
      wp_apply wp_slice_len.
      wp_storeField.
      destruct Horprefix as [Hprefix | Hprefix]; last first.
      { apply prefix_length in Hprefix. exfalso.
        clear -Hgtlog Hprefix Hszlog Hlenlogc. word.
      }
      iApply "HΦ".
      iFrame "Hcand Hleader".
      iFrame "∗ # %".
      iModIntro.
      iSplit.
      { rewrite -Hszlog firstn_all.
        by iApply (safe_ledger_above_weaken log with "Hsafe").
      }
      iPureIntro.
      clear -Hszlog. word.
    }
    rename Heqb into Hlelog.
    rewrite Z.nlt_ge in Hlelog.

    (*@     px.lsnc = lsn                                                       @*)
    (*@                                                                         @*)
    wp_storeField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { assert (Hprefix : prefix logc log).
      { destruct Horprefix as [Hprefix | ?]; last done.
        rewrite (prefix_length_eq _ _ Hprefix); first done.
        lia.
      }
      iApply (safe_ledger_above_weaken with "Hsafe").
      by rewrite -Hlenlogc take_length_prefix.
    }
    iPureIntro.
    clear -Hlelog Hszlog. word.

    (*@     // TODO: Write @px.lsnc to disk.                                    @*)
    (*@ }                                                                       @*)
  Qed.

End commit.

Section push.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__push (px : loc) (nidme termc : u64) nids γ :
    know_paxos_inv γ nids -∗
    {{{ own_paxos_leading_with_termc px nidme termc nids γ }}}
      Paxos__push #px
    {{{ (lsnc : u64) (pushed : bool), RET (#lsnc, #pushed);
        own_paxos_leading_with_termc px nidme termc nids γ ∗
        if pushed
        then ∃ logc, safe_ledger_above γ nids (uint.nat termc) logc ∗
                     ⌜length logc = uint.nat lsnc⌝
        else True
    }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) push() (uint64, bool) {                                @*)
    (*@     if !px.cquorum(uint64(len(px.lsnpeers)) + 1) {                      @*)
    (*@         // Nothing should be done without responses from some quorum of nodes. @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl". iNamed "Hnids".
    wp_loadField.
    wp_apply (wp_MapLen with "Hlsnpeers").
    iIntros "[%Hszlsnpeers Hlsnpeers]".
    wp_apply (wp_Paxos__cquorum with "Hsc").
    iIntros (ok) "[Hsc %Hqsize]".
    (* Not using [wp_if_destruct] to prevent it eating equality about [nids]. *)
    destruct ok eqn:Hok; last first.
    { wp_pures.
      iApply "HΦ".
      iFrame "Hcand".
      by iFrame "∗ # %".
    }
    
    (*@     var lsns = make([]uint64, 0, px.sc)                                 @*)
    (*@                                                                         @*)
    iNamed "Hsc".
    wp_loadField.
    wp_apply wp_NewSliceWithCap.
    { word. }
    iIntros (lsnsinitP) "Hlsns".
    wp_apply wp_ref_to; first done.
    iIntros (lsnsPP) "HlsnsPP".

    (*@     for _, lsn := range(px.lsnpeers) {                                  @*)
    (*@         lsns = append(lsns, lsn)                                        @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    rewrite uint_nat_W64_0 /=.
    set P := (λ (m : gmap u64 u64), ∃ (lsnsP' : Slice.t) (lsns' : list u64),
                 "HlsnsP" ∷ lsnsPP ↦[slice.T uint64T] (to_val lsnsP')  ∗
          "Hlsns"   ∷ own_slice lsnsP' uint64T (DfracOwn 1) lsns' ∗
          "%Hlsns'" ∷ ⌜(map_to_list m).*2 ≡ₚ lsns'⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Hlsnpeers [$HlsnsPP $Hlsns]").
    { set_solver. }
    { (* Loop body. *)
      clear Φ.
      iIntros (m nid lsn Φ) "!> (HP & %Hnone & %Hlsn) HΦ".
      iNamed "HP".
      wp_load.
      wp_apply (wp_SliceAppend with "Hlsns").
      iIntros (lsnsP'') "Hlsns".
      wp_store.
      iApply "HΦ".
      iFrame.
      iPureIntro.
      rewrite map_to_list_insert; last apply Hnone.
      rewrite fmap_cons Hlsns' /=.
      apply Permutation_cons_append.
    }
    iIntros "[Hlsnpeers HP]".
    iNamed "HP". clear P.

    (*@     util.Sort(lsns)                                                     @*)
    (*@                                                                         @*)
    wp_load.
    wp_apply (wp_Sort with "Hlsns").
    iIntros (lsnsorts) "(Hlsns & %Hsorted & %Hperm)".
    wp_load.
    wp_apply wp_slice_len.
    wp_loadField.
    wp_load.
    iDestruct (own_slice_sz with "Hlsns") as %Hszsorted.
    rewrite Hperm -Hlsns' length_fmap length_map_to_list in Hszsorted.
    rewrite word.unsigned_add Hsc in Hqsize.
    set i := word.sub _ _.
    assert (is_Some (lsnsorts !! uint.nat i)) as [lsn Hlsn].
    { apply lookup_lt_is_Some_2.
      subst i.
      rewrite Hperm -Hlsns' length_fmap length_map_to_list.
      rewrite word.unsigned_sub_nowrap; last word.
      word.
    }
    iDestruct (own_slice_to_small with "Hlsns") as "Hlsns".
    wp_apply (wp_SliceGet with "[$Hlsns]").
    { iPureIntro. apply Hlsn. }
    iIntros "Hlsns".
    wp_pures.

    (*@     if lsn < px.lsnc {                                                  @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_if_destruct.
    { wp_pures.
      iApply "HΦ".
      iFrame "Hcand".
      by iFrame "∗ # %".
    }

    (*@     return lsn, true                                                    @*)
    (*@ }                                                                       @*)
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iSplit.
    { iFrame "Hcand".
      by iFrame "∗ # %".
    }
    iDestruct (own_slice_sz with "Hlog") as %Hszlog.
    set lsnpeersq := filter (λ x, (uint.nat lsn ≤ uint.nat x.2)%nat) lsnpeers.
    set nidpeersq := dom lsnpeersq.
    iDestruct "Haocm" as (aocm) "Haocm".
    set aocmq := filter (λ x, x.1 ∈ nidpeersq) aocm.
    destruct (decide (map_Exists (λ _ b, b = false) aocmq)) as [Hsomecmted | Hallacpted].
    { (* Case: Some peer in the quorum has already committed up to the reported LSN. *)
      destruct Hsomecmted as (nidx & b & Hfalse & ->).
      unshelve epose proof (lookup_weaken _ aocm _ _ Hfalse _) as Hnidx.
      { apply map_filter_subseteq. }
      iDestruct (big_sepM2_dom with "Haocm") as %Hdom.
      subst aocmq.
      apply map_lookup_filter_Some_1_2 in Hfalse.
      subst nidpeersq.
      rewrite elem_of_dom /= in Hfalse.
      destruct Hfalse as [lsncmted Hlsncmted].
      subst lsnpeersq.
      rewrite map_lookup_filter_Some /= in Hlsncmted.
      destruct Hlsncmted as [Hlsncmted Hlenge].
      iDestruct (big_sepM2_lookup with "Haocm") as "Hcmtedpeer".
      { apply Hlsncmted. }
      { apply Hnidx. }
      iDestruct "Hcmtedpeer" as (logx) "[Hlogx %Hlenlogx]".
      iDestruct (safe_ledger_above_weaken (take (uint.nat lsn) logx) with "Hlogx") as "Hcmted'".
      { apply prefix_take. }
      iFrame "Hcmted'".
      iPureIntro.
      rewrite length_take.
      lia.
    }
    (* Case: All peers in the quorum have accepted up to their reported LSNs. *)
    rewrite map_not_Exists in Hallacpted.
    set logc := take (uint.nat lsn) log.
    iExists logc.
    iSplit; last first.
    { iPureIntro.
      rewrite length_take.
      apply elem_of_list_lookup_2 in Hlsn.
      rewrite Hperm -Hlsns' in Hlsn.
      apply elem_of_list_lookup_1 in Hlsn as [j Hlsn].
      rewrite list_lookup_fmap in Hlsn.
      destruct (map_to_list lsnpeers !! j) as [[nidy lsny] |] eqn:Hy; last done.
      inv Hlsn.
      apply elem_of_list_lookup_2, elem_of_map_to_list in Hy.
      specialize (Hlelog _ _ Hy). simpl in Hlelog.
      clear -Hlelog. word.
    }
    iExists (uint.nat termc).
    iSplit; last done.
    set nidsq := ({[nidme]} ∪ nidpeersq).
    iExists nidme, nidsq.
    iDestruct (accepted_proposal_lb_weaken logc with "Hacpted") as "Hacpted'".
    { apply prefix_take. }
    subst terml.
    iFrame "Hacpted'".
    iSplit.
    { rewrite big_sepM2_alt.
      iDestruct "Haocm" as "[%Hdom Haocm]".
      iDestruct (big_sepM_dom_subseteq_difference _ _ nidpeersq with "Haocm") as
        (m) "([%Hdomm %Hm] & Haocm' & _)".
      { rewrite dom_map_zip_with -Hdom intersection_idemp_L.
        apply subseteq_dom, map_filter_subseteq.
      }
      iApply (big_sepS_insert_2 with "[] []").
      { by iFrame "Hacpted'". }
      rewrite big_sepS_big_sepM.
      iApply (big_sepM_impl_dom_eq with "Haocm'"); first done.
      iIntros (nid [x a] lsnp Hxa Hlsnp) "!> Hacpt".
      assert (Ha : aocmq !! nid = Some a).
      { rewrite map_lookup_filter_Some.
        split.
        { pose proof (lookup_weaken _ _ _ _ Hxa Hm) as Hlookup.
          rewrite map_lookup_zip_Some in Hlookup.
          by destruct Hlookup as [_ ?].
        }
        by rewrite elem_of_dom.
      }
      specialize (Hallacpted _ _ Ha).
      rewrite not_false_iff_true in Hallacpted.
      subst a. simpl.
      rewrite map_lookup_filter_Some /= in Hlsnp.
      destruct Hlsnp as [Hlsnp Hgelsn].
      rewrite map_subseteq_spec in Hm.
      specialize (Hm _ _ Hxa).
      rewrite map_lookup_zip_Some /= in Hm.
      destruct Hm as [Hx _].
      rewrite Hlsnp in Hx.
      inv Hx.
      iApply (accepted_proposal_length_lb_weaken with "Hacpt").
      rewrite length_take.
      clear -Hgelsn. lia.
    }
    iPureIntro.
    split; last set_solver.
    split.
    { apply union_least; first set_solver.
      trans (dom lsnpeers); [apply dom_filter_subseteq | set_solver].
    }
    rewrite /cquorum_size.
    rewrite size_union; last first.
    { clear -Hnids Hnidsne Hinclnids.
      assert (nidpeersq ⊆ peers).
      { subst nidpeersq lsnpeersq.
        trans (dom lsnpeers); [apply dom_filter_subseteq | apply Hinclnids].
      }
      set_solver.
    }
    rewrite size_singleton.
    set lsndrops := drop (uint.nat i) lsnsorts.
    assert (Hlensorts : size nids / 2 ≤ length lsndrops).
    { rewrite length_drop.
      rewrite Hperm -Hlsns' length_fmap length_map_to_list.
      rewrite word.unsigned_sub_nowrap; last word.
      word.
    }
    rewrite -Hlsns' in Hperm.
    (* Key to this proof: Obtain from [lsnsorts] an inversion [nlsorts] with
    node IDs, allowing proof of the following [submseteq] relation. We might be
    able to simplify the proof by eliminating the detour using [filter] to
    define the node IDs quorum, but define it directly using the [nlsorts]. *)
    apply Permutation_map_inv in Hperm as (nlsorts & Hnlsorts & Hperm).
    set nldrops := drop (uint.nat i) nlsorts.
    assert (Hincl : nldrops ⊆+ map_to_list lsnpeersq).
    { apply NoDup_submseteq.
      { subst nldrops.
        apply (NoDup_suffix _ nlsorts); first apply suffix_drop.
        rewrite -Hperm.
        apply NoDup_map_to_list.
      }
      intros nlx Hnlx.
      assert (Hinsorts : nlx ∈ nlsorts).
      { apply (subseteq_drop (uint.nat i) nlsorts _ Hnlx). }
      rewrite -Hperm in Hinsorts.
      destruct nlx as [nidx lsnx].
      rewrite elem_of_map_to_list in Hinsorts.
      rewrite elem_of_map_to_list.
      rewrite map_lookup_filter_Some /=.
      split; first apply Hinsorts.
      apply elem_of_list_lookup in Hnlx as [j Hnlx].
      subst nldrops.
      rewrite lookup_drop /= in Hnlx.
      assert (lsnsorts !! (uint.nat i + j)%nat = Some lsnx) as Hlsnx.
      { by rewrite Hnlsorts list_lookup_fmap Hnlx /=. }
      unshelve epose proof (Hsorted _ _ _ _ _ Hlsn Hlsnx) as Hle; first lia.
      word.
    }
    assert (Hsizele : length lsndrops ≤ length (map_to_list lsnpeersq).*2).
    { apply submseteq_length in Hincl.
      revert Hincl.
      rewrite 2!length_drop Hnlsorts 2!length_fmap.
      word.
    }
    subst nidpeersq.
    rewrite length_fmap length_map_to_list in Hsizele.
    rewrite size_dom.
    clear -Hsizele Hlensorts.
    word.
  Qed.

End push.

Section leading.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__leading (px : loc) nidme nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__leading #px
    {{{ (isleader : bool), RET #isleader;
        if isleader
        then own_paxos_leading px nidme nids γ
        else own_paxos px nidme nids γ
    }}}.
  Proof.
    (*@ func (px *Paxos) leading() bool {                                       @*)
    (*@     return px.isleader                                                  @*)
    (*@ }                                                                       @*)
    iIntros (Φ) "Hpx HΦ".
    iNamed "Hpx". iNamed "Hleader".
    wp_rec.
    wp_loadField.
    iApply "HΦ".
    destruct isleader; iFrame "Hpx Hcand Hnids Hcomm"; iFrame.
  Qed.

End leading.

Section submit.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Submit (px : loc) (c : string) nidme γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
    <<< ∀∀ cpool, own_cpool_half γ cpool >>>
      Paxos__Submit #px #(LitString c) @ ↑paxosNS
    <<< own_cpool_half γ ({[c]} ∪ cpool) >>>
    (* TODO: return a receipt for checking committedness from the client. *)
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term); True }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> _ HAU".
    wp_rec.

    (*@ func (px *Paxos) Submit(v string) (uint64, uint64) {                    @*)
    (*@     px.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    iNamed "Hinv".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hpx]".

    (*@     if !px.leading() {                                                  @*)
    (*@         px.mu.Unlock()                                                  @*)
    (*@         return 0, 0                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__leading with "Hpx").
    iIntros (isleader) "Hpx".
    destruct isleader; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx]").
      wp_pures.
      iInv "Hinv" as "> HinvO" "HinvC".
      iMod "HAU" as (cpoolcli) "[Hcpoolcli HAU]".
      iNamed "HinvO".
      iDestruct (cpool_agree with "Hcpool Hcpoolcli") as %->.
      iMod (cpool_update ({[c]} ∪ cpool) with "Hcpool Hcpoolcli") as "[Hcpool Hcpoolcli]".
      { set_solver. }
      iMod ("HAU" with "Hcpoolcli") as "HΦ".
      iMod ("HinvC" with "[-HΦ]") as "_".
      { iFrame "∗ # %". }
      by iApply "HΦ".
    }

    (*@     lsn := uint64(len(px.log))                                          @*)
    (*@     px.log = append(px.log, v)                                          @*)
    (*@     term := px.termc                                                    @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_apply wp_slice_len.
    wp_loadField.
    wp_apply (wp_SliceAppend with "Hlog").
    iIntros (logP') "Hlog".
    wp_storeField.
    wp_loadField.

    (*@     // Logical action: Extend(@px.termc, @px.log).                      @*)
    (*@                                                                         @*)
    iApply ncfupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod "HAU" as (cpoolcli) "[Hcpoolcli HAU]".
    iAssert (|==> own_cpool_half γ ({[c]} ∪ cpoolcli) ∗ paxos_inv γ nids)%I
      with "[Hcpoolcli HinvO]" as "HcpoolU".
    { iNamed "HinvO".
      iDestruct (cpool_agree with "Hcpool Hcpoolcli") as %->.
      iMod (cpool_update ({[c]} ∪ cpool) with "Hcpool Hcpoolcli") as "[Hcpool Hcpoolcli]".
      { set_solver. }
      by iFrame "∗ # %".
    }
    iMod "HcpoolU" as "[Hcpoolcli HinvO]".
    iDestruct (cpool_witness c with "Hcpoolcli") as "#Hc".
    { set_solver. }
    iNamed "Hleader". iNamed "Honlyl".
    subst terml.
    iNamed "Hnids".
    iMod (paxos_inv_extend [c] with "[] Hps Htermc Hterml Hlogn HinvO")
      as "(Hps & Htermc & Hterml & Hlogn & HinvO & #Hacpted')".
    { set_solver. }
    { by iApply big_sepL_singleton. }
    iMod ("HAU" with "Hcpoolcli") as "HΦ".
    iMod ("HinvC" with "HinvO") as "_".
    iModIntro.

    (*@     // Potential batch optimization: Even though we update @px.log here, but it @*)
    (*@     // should be OK to not immediately write them to disk, but wait until those @*)
    (*@     // entries are sent in @LeaderSession. To prove the optimization, we'll need @*)
    (*@     // to decouple the "batched entries" from the actual entries @px.log, and @*)
    (*@     // relate only @px.log to the invariant.                            @*)
    (*@                                                                         @*)
    (*@     px.mu.Unlock()                                                      @*)
    (*@     return lsn, term                                                    @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked".
      iDestruct (terml_eq_termc_impl_not_nominiated with "Hcand") as %->; first done.
      set log' := log ++ [c].
      iAssert (own_paxos_leader px termc termc log' true peers nids γ)%I
        with "[$HisleaderP $HlsnpeersP $Hlsnpeers $Hps $Haocm]" as "Hleader".
      { iPureIntro.
        split; first done.
        split; last done.
        apply (map_Forall_impl _ _ _ Hlelog).
        intros _ lsn Hlsn.
        rewrite length_app /=.
        clear -Hlsn. lia.
      }
      iNamed "Hcand".
      iFrame "Hcomm Hleader HiscandP HlogP".
      iFrame "∗ # %".
      iSplit.
      { iDestruct "Hgebase" as (vlb) "[Hvlb %Hprefix]".
        iFrame "Hvlb".
        iPureIntro.
        trans log; [apply Hprefix | by apply prefix_app_r].
      }
      iSplit.
      { by case_decide. }
      iSplit.
      { rewrite take_app_le; first done.
        clear -Hlsncub. lia.
      }
      iPureIntro.
      rewrite length_app /=.
      clear -Hlsncub. lia.
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

End submit.

Section lookup.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Lookup (px : loc) (lsn : u64) nidme γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
    <<< ∀∀ log, own_log_half γ log >>>
      Paxos__Lookup #px #lsn @ ↑paxosNS
    <<< ∃∃ log', own_log_half γ log' >>>
    {{{ (v : string) (ok : bool), RET (#(LitString v), #ok);
        ⌜if ok then log' !! (uint.nat lsn) = Some v else True⌝
    }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> _ HAU".
    wp_rec.

    (*@ func (px *Paxos) Lookup(lsn uint64) (string, bool) {                    @*)
    (*@     px.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    iNamed "Hinv".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hpx]".

    (*@     if px.lsnc <= lsn {                                                 @*)
    (*@         px.mu.Unlock()                                                  @*)
    (*@         return "", false                                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HAU]").
      { iFrame "Hlock Hlocked".
        iFrame "∗ # %".
      }
      wp_pures.
      (* Simply take and give back the same log. *)
      iMod (ncfupd_mask_subseteq (⊤ ∖ ↑paxosNS)) as "Hclose"; first solve_ndisj.
      iMod "HAU" as (logcli) "[Hlogcli HAU]".
      iMod ("HAU" with "Hlogcli") as "HΦ".
      iMod "Hclose" as "_".
      by iApply "HΦ".
    }
    rename Heqb into Hlt.
    rewrite Z.nle_gt in Hlt.

    (*@     v := px.log[lsn]                                                    @*)
    (*@                                                                         @*)
    wp_loadField.
    iDestruct (own_slice_small_acc with "Hlog") as "[Hlog HlogC]".
    assert (is_Some (log !! uint.nat lsn)) as [c Hc].
    { apply lookup_lt_is_Some_2. clear -Hlt Hlsncub. word. }
    wp_apply (wp_SliceGet with "[$Hlog]").
    { iPureIntro. apply Hc. }
    iIntros "Hlog".
    iDestruct ("HlogC" with "Hlog") as "Hlog".
    wp_pures.

    (*@     // Logical action: Commit(@px.log) if @px.log is longer than the global log. @*)
    (*@                                                                         @*)
    iApply ncfupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod "HAU" as (logcli) "[Hlogcli HAU]".
    set logc := take _ log.
    iNamed "Hnids".
    iMod (paxos_inv_commit logc with "[] Hlogcli Hlogn HinvO") as "(Hlogcli & Hlogn & HinvO)".
    { set_solver. }
    { apply prefix_take. }
    { iDestruct "Hcmted" as (t) "[Hsafe _]".
      iFrame "Hsafe".
    }
    iDestruct "Hlogcli" as (logcli') "[Hlogcli %Hprefix]".
    iMod ("HAU" with "Hlogcli") as "HΦ".
    iMod ("HinvC" with "HinvO") as "_".
    iModIntro.

    (*@     px.mu.Unlock()                                                      @*)
    (*@     return v, true                                                      @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked".
      iFrame "Hcand Hleader Hcomm".
      iFrame "∗ # %".
    }
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    rewrite -(prefix_lookup_lt logc log) in Hc; last first.
    { apply prefix_take. }
    { rewrite length_take. clear -Hlsncub Hlt. word. }
    eapply prefix_lookup_Some; [apply Hc | apply Hprefix].
  Qed.

End lookup.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

End program.
