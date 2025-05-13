From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_logic Require Export own_crash_inv.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

(* TODO: rename this file to paxos_repr.v *)

Section repr.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  (*@ type Paxos struct {                                                     @*)
  (*@     // ID of this node.                                                 @*)
  (*@     nidme     uint64                                                    @*)
  (*@     // Node ID of its peers.                                            @*)
  (*@     peers     []uint64                                                  @*)
  (*@     // Addresses of other Paxos nodes.                                  @*)
  (*@     addrm     map[uint64]grove_ffi.Address                              @*)
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
  (*@     log       []string                                                  @*)
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
  Definition is_paxos_addrm (paxos : loc) (addrm : gmap u64 chan) : iProp Σ :=
    ∃ (addrmP : loc),
      "#HaddrmP"   ∷ readonly (paxos ↦[Paxos :: "addrm"] #addrmP) ∗
      "#Haddrm"    ∷ own_map addrmP DfracDiscarded addrm.

  Definition is_paxos_nids
    (paxos : loc) (nidme : u64) (nids : gset u64) : iProp Σ :=
    ∃ (peersP : Slice.t) (peers : list u64),
      "HnidmeP" ∷ readonly (paxos ↦[Paxos :: "nidme"] #nidme) ∗
      "HpeersP" ∷ readonly (paxos ↦[Paxos :: "peers"] (to_val peersP)) ∗
      "Hpeers"  ∷ readonly (own_slice_small peersP uint64T (DfracOwn 1) peers) ∗
      "%Hpeers" ∷ ⌜list_to_set peers = nids ∖ {[nidme]}⌝.

  Definition own_paxos_comm (paxos : loc) (addrm : gmap u64 chan) γ : iProp Σ :=
    ∃ (connsP : loc) (conns : gmap u64 (chan * chan)),
      let connsV := fmap (λ x, connection_socket x.1 x.2) conns in
      "HconnsP" ∷ paxos ↦[Paxos :: "conns"] #connsP ∗
      "Hconns"  ∷ map.own_map connsP (DfracOwn 1) (connsV, #()) ∗
      "#Htrmls" ∷ ([∗ map] x ∈ conns, is_terminal γ x.1) ∗
      "%Haddrpeers" ∷ ⌜map_Forall (λ nid x, addrm !! nid = Some x.2) conns⌝.

  Definition own_paxos_candidate_only
    (nidme termc terml termp : u64) (logc : list byte_string)
    (entspP : Slice.t) (resppP : loc) nids γ : iProp Σ :=
    ∃ (entsp : list byte_string) (respp : gmap u64 bool),
      "Hentsp"   ∷ own_slice entspP stringT (DfracOwn 1) entsp ∗
      "Hrespp"   ∷ own_map resppP (DfracOwn 1) respp ∗
      "#Hvotes"  ∷ votes_in γ (dom respp) (uint.nat termc) (uint.nat termp) (logc ++ entsp) ∗
      "#Hlsnprc" ∷ is_prepare_lsn γ (uint.nat termc) (length logc) ∗
      "%Hton"    ∷ ⌜is_term_of_node nidme (uint.nat termc)⌝ ∗
      "%Hdomvts" ∷ ⌜dom respp ⊆ nids⌝ ∗
      "%Hllep"   ∷ ⌜uint.Z terml ≤ uint.Z termp⌝ ∗
      "%Hpltc"   ∷ ⌜uint.Z termp < uint.Z termc⌝.

  Definition own_paxos_candidate
    (paxos : loc) (nid termc terml : u64) (logc : list byte_string) (iscand : bool) nids γ : iProp Σ :=
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
    (termc terml : u64) (log : list byte_string) (lsnpeersP : loc) (peers : gset u64)
    nids γ : iProp Σ :=
    ∃ (lsnpeers : gmap u64 u64),
      "Hps"        ∷ own_proposal γ (uint.nat termc) log ∗
      "Hlsnpeers"  ∷ own_map lsnpeersP (DfracOwn 1) lsnpeers ∗
      "#Haocm"     ∷ safe_peer_lsns γ nids (uint.nat termc) lsnpeers ∗
      "%Hleqc"     ∷ ⌜terml = termc⌝ ∗
      "%Hlelog"    ∷ ⌜map_Forall (λ _ i, (uint.nat i ≤ length log)%nat) lsnpeers⌝ ∗
      "%Hinclnids" ∷ ⌜dom lsnpeers ⊆ peers⌝.

  Definition own_paxos_leader
    (paxos : loc) (nidme termc terml : u64) (log : list byte_string) (isleader : bool)
    nids γ : iProp Σ :=
    ∃ (lsnpeersP : loc),
      "HisleaderP" ∷ paxos ↦[Paxos :: "isleader"] #isleader ∗
      "HlsnpeersP" ∷ paxos ↦[Paxos :: "lsnpeers"] #lsnpeersP ∗
      "Honlyl"     ∷ (if isleader
                      then own_paxos_leader_only termc terml log lsnpeersP (nids ∖ {[nidme]}) nids γ
                      else True).

  Definition own_paxos_sc (paxos : loc) (nids : gset u64) : iProp Σ :=
    ∃ (sc : u64),
      "HscP"    ∷ paxos ↦[Paxos :: "sc"] #sc ∗
      (* This condition allows a nicer implementation and proof for pushing the
      committed LSN (i.e., @px.push). *)
      "%Hmulti" ∷ ⌜1 < uint.Z sc⌝ ∗
      "%Hsc"    ∷ ⌜size nids = uint.nat sc⌝.

  Definition own_paxos_common
    (paxos : loc) (nidme termc terml lsnc : u64) (log : list byte_string) nids γ : iProp Σ :=
    ∃ (hb : bool) (logP : Slice.t),
      let dst := PaxosDurable termc terml log lsnc in
      "HhbP"     ∷ paxos ↦[Paxos :: "hb"] #hb ∗
      "HtermcP"  ∷ paxos ↦[Paxos :: "termc"] #termc ∗
      "HtermlP"  ∷ paxos ↦[Paxos :: "terml"] #terml ∗
      "HlogP"    ∷ paxos ↦[Paxos :: "log"] (to_val logP) ∗
      "Hlog"     ∷ own_slice logP stringT (DfracOwn 1) log ∗
      "HlsncP"   ∷ paxos ↦[Paxos :: "lsnc"] #lsnc ∗
      "Hdurable" ∷ own_crash_ex pxcrashNS (own_paxos_durable γ nidme) dst ∗
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
    ∃ (log : list byte_string),
      let logc := (take (uint.nat lsnc) log) in
      "Hpx"     ∷ own_paxos_common paxos nidme termc terml lsnc log nids γ ∗
      "Hcand"   ∷ own_paxos_candidate paxos nidme termc terml logc iscand nids γ ∗
      "Hleader" ∷ own_paxos_leader paxos nidme termc terml log isleader nids γ.

  Definition own_paxos_with_termc_lsnc
    (paxos : loc) (nidme termc lsnc : u64) nids γ : iProp Σ :=
    ∃ (terml : u64) (iscand isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc iscand isleader nids γ.

  Definition own_paxos_nominated_with_termc
    (paxos : loc) (nidme termc : u64) nids γ : iProp Σ :=
    ∃ (terml : u64) (lsnc : u64) (isleader : bool),
      own_paxos_internal paxos nidme termc terml lsnc true isleader nids γ.

  Definition own_paxos_nominated_with_termc_lsnc
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

  Lemma own_paxos_expose_termc paxos nidme nids γ :
    own_paxos paxos nidme nids γ -∗
    ∃ termc, own_paxos_with_termc paxos nidme termc nids γ.
  Proof. iIntros "Hpx". iFrame. Qed.

  Lemma own_paxos_hide_termc paxos nidme termc nids γ :
    own_paxos_with_termc paxos nidme termc nids γ -∗
    own_paxos paxos nidme nids γ.
  Proof. iIntros "Hpx". iFrame. Qed.

  Definition is_paxos_fname (paxos : loc) (nidme : u64) γ : iProp Σ :=
    ∃ (fname : byte_string),
      "#HfnameP"  ∷ readonly (paxos ↦[Paxos :: "fname"] #(LitString fname)) ∗
      "#Hfnameme" ∷ is_node_wal_fname γ nidme fname.

  Definition is_paxos_with_addrm
    (paxos : loc) (nidme : u64) (addrm : gmap u64 chan) γ : iProp Σ :=
    ∃ (muP : loc) (cvP : loc),
      let nids := dom addrm in
      "#HmuP"     ∷ readonly (paxos ↦[Paxos :: "mu"] #muP) ∗
      "#Hlock"    ∷ is_lock paxosNS #muP (own_paxos paxos nidme nids γ ∗
                                          own_paxos_comm paxos addrm γ) ∗
      "#HcvP"     ∷ readonly (paxos ↦[Paxos :: "cv"] #cvP) ∗
      "#Hcv"      ∷ is_cond cvP #muP ∗
      "#Hfname"   ∷ is_paxos_fname paxos nidme γ ∗
      "#Haddrm"   ∷ is_paxos_addrm paxos addrm ∗
      "#Hnids"    ∷ is_paxos_nids paxos nidme nids ∗
      "#Hinv"     ∷ know_paxos_inv γ nids ∗
      "#Hinvfile" ∷ know_paxos_file_inv γ nids ∗
      "#Hinvnet"  ∷ know_paxos_network_inv γ addrm ∗
      "%Hnidme"   ∷ ⌜nidme ∈ nids⌝.

  Definition is_paxos (paxos : loc) (nidme : u64) γ : iProp Σ :=
    ∃ (addrm : gmap u64 chan),
      is_paxos_with_addrm paxos nidme addrm γ.

End repr.
