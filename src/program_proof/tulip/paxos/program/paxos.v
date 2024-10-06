From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.invariance Require Import
  accept advance ascend commit extend prepare.
From Perennial.program_proof.tulip.program.util Require Import next_aligned sort.
From Perennial.program_proof.tulip.program Require Import quorum.
From Goose.github_com.mit_pdos.tulip Require Import paxos message.

(* Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. *)

(* TODO: move them to separate file once stable *)

Inductive pxreq :=
| RequestVoteReq (term : u64) (lsnlc : u64)
| AppendEntriesReq (term : u64) (lsnlc : u64) (lsne : u64) (ents : list string).

#[global]
Instance pxreq_eq_decision :
  EqDecision pxreq.
Proof. solve_decision. Qed.

#[global]
Instance pxreq_countable :
  Countable pxreq.
Admitted.

Definition encode_pxreq (req : pxreq) : list u8.
Admitted.

Definition pxreq_to_val (req : pxreq) (entsP : Slice.t) : val :=
  match req with
  | RequestVoteReq term lsnlc =>
      struct.mk_f PaxosRequest [
          ("Kind", #(U64 0)); ("Term", #term); ("CommittedLSN", #lsnlc)
        ]
  | AppendEntriesReq term lsnlc lsne ents =>
      struct.mk_f PaxosRequest [
          ("Kind", #(U64 1)); ("Term", #term); ("CommittedLSN", #lsnlc);
          ("EntriesLSN", #lsne); ("Entries", to_val entsP)
        ]
  end.

Inductive pxresp :=
| RequestVoteResp (nid term terme : u64) (ents : list string)
| AppendEntriesResp (nid term lsneq : u64).

#[global]
Instance pxresp_eq_decision :
  EqDecision pxresp.
Proof. solve_decision. Qed.

#[global]
Instance pxresp_countable :
  Countable pxresp.
Admitted.

Definition encode_pxresp (resp : pxresp) : list u8.
Admitted.

Definition pxresp_to_val (resp : pxresp) (entsP : Slice.t) : val :=
  match resp with
  | RequestVoteResp nid term terme ents =>
      struct.mk_f PaxosResponse [
          ("Kind", #(U64 0)); ("NodeID", #nid); ("Term", #term);
          ("TermEntries", #terme); ("Entries", to_val entsP)
        ]
  | AppendEntriesResp nid term lsneq =>
      struct.mk_f PaxosResponse [
          ("Kind", #(U64 1)); ("NodeID", #nid); ("Term", #term);
          ("MatchedLSN", #lsneq)
        ]
  end.

Section res_network.
  Context `{!paxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : paxos_names).

  Definition own_terminals γ (ts : gset chan) : iProp Σ.
  Admitted.

  Definition is_terminal γ (t : chan) : iProp Σ.
  Admitted.

  #[global]
  Instance is_terminal_persistent γ t :
    Persistent (is_terminal γ t).
  Admitted.

  Lemma terminal_update {γ ts} t :
    own_terminals γ ts ==∗
    own_terminals γ ({[t]} ∪ ts) ∗ is_terminal γ t.
  Admitted.

  Lemma terminal_lookup γ ts t :
    is_terminal γ t -∗
    own_terminals γ ts -∗
    ⌜t ∈ ts⌝.
  Admitted.

End res_network.

Section inv_network.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Definition paxosnetNS := nroot .@ "paxosnet".

  Definition safe_request_vote_req γ (term lsnlc : u64) : iProp Σ :=
    is_prepare_lsn γ (uint.nat term) (uint.nat lsnlc).

  Definition safe_append_entries_req
    γ nids (term lsnlc lsne : u64) (ents : list string) : iProp Σ :=
    ∃ (logleader logcmt : list string),
      "#Hpfb"       ∷ prefix_base_ledger γ (uint.nat term) logleader ∗
      "#Hpfg"       ∷ prefix_growing_ledger γ (uint.nat term) logleader ∗
      "#Hlogcmt"    ∷ safe_ledger_above γ nids (uint.nat term) logcmt ∗
      "%Hlogleader" ∷ ⌜(uint.nat lsne ≤ length logleader)%nat⌝ ∗
      "%Hents"      ∷ ⌜drop (uint.nat lsne) logleader = ents⌝ ∗
      "%Hlogcmt"    ∷ ⌜length logcmt = uint.nat lsnlc⌝.

  Definition safe_pxreq γ nids req : iProp Σ :=
    match req with
    | RequestVoteReq term lsnlc => safe_request_vote_req γ term lsnlc
    | AppendEntriesReq term lsnlc lsne ents =>
        safe_append_entries_req γ nids term lsnlc lsne ents
    end.

  #[global]
  Instance safe_pxreq_persistent γ nids req :
    Persistent (safe_pxreq γ nids req).
  Proof. destruct req; apply _. Defined.

  Definition safe_request_vote_resp
    γ (nids : gset u64) (nid term terme : u64) (ents : list string) : iProp Σ :=
    ∃ (logpeer : list string) (lsne : u64),
      "#Hpromise" ∷ past_nodedecs_latest_before γ nid (uint.nat term) (uint.nat terme) logpeer ∗
      "#Hlsne"    ∷ is_prepare_lsn γ (uint.nat term) (uint.nat lsne) ∗
      "%Hents"    ∷ ⌜drop (uint.nat lsne) logpeer = ents⌝ ∗
      "%Hinnids"  ∷ ⌜nid ∈ nids⌝.

  Definition safe_append_entries_resp
    γ (nids : gset u64) (nid term lsneq : u64) : iProp Σ :=
    ∃ (logacpt : list string),
      "#Haoc"     ∷ (is_accepted_proposal_lb γ nid (uint.nat term) logacpt ∨
                     safe_ledger_above γ nids (uint.nat term) logacpt) ∗
      "%Hlogacpt" ∷ ⌜length logacpt = uint.nat lsneq⌝ ∗
      "%Hinnids"  ∷ ⌜nid ∈ nids⌝.

  Definition safe_pxresp γ nids resp : iProp Σ :=
    match resp with
    | RequestVoteResp nid term terme ents =>
        safe_request_vote_resp γ nids nid term terme ents
    | AppendEntriesResp nid term lsneq =>
        safe_append_entries_resp γ nids nid term lsneq
    end.

  #[global]
  Instance safe_pxresp_persistent γ nids resp :
    Persistent (safe_pxresp γ nids resp).
  Proof. destruct resp; apply _. Defined.

  Definition listen_inv
    (addr : chan) (ms : gset message) nids γ : iProp Σ :=
    ∃ (reqs : gset pxreq),
      "Hms"      ∷ addr c↦ ms ∗
      (* senders are always reachable *)
      "#Hsender" ∷ ([∗ set] trml ∈ set_map msg_sender ms, is_terminal γ trml) ∗
      "#Hreqs"   ∷ ([∗ set] req ∈ reqs, safe_pxreq γ nids req) ∗
      "%Henc"    ∷ ⌜(set_map msg_data ms : gset (list u8)) ⊆ set_map encode_pxreq reqs⌝.

  Definition connect_inv (trml : chan) (ms : gset message) nids γ : iProp Σ :=
    ∃ (resps : gset pxresp),
      "Hms"     ∷ trml c↦ ms ∗
      "#Hresps" ∷ ([∗ set] resp ∈ resps, safe_pxresp γ nids resp) ∗
      "%Henc"   ∷ ⌜(set_map msg_data ms : gset (list u8)) ⊆ set_map encode_pxresp resps⌝.

  Definition paxos_network_inv
    (γ : paxos_names) (nids : gset u64) (addrm : gmap u64 chan) : iProp Σ :=
    ∃ (listens : gmap chan (gset message)) (connects : gmap chan (gset message)),
      "Hlistens"   ∷ ([∗ map] a ↦ ms ∈ listens, listen_inv a ms nids γ) ∗
      "Hconnects"  ∷ ([∗ map] t ↦ ms ∈ connects, connect_inv t ms nids γ) ∗
      "Hterminals" ∷ own_terminals γ (dom connects) ∗
      "%Himgaddrm" ∷ ⌜map_img addrm = dom listens⌝.

  #[global]
  Instance paxos_network_inv_timeless γ nids addrm :
    Timeless (paxos_network_inv γ nids addrm).
  Admitted.

  Definition know_paxos_network_inv γ nids addrm : iProp Σ :=
    inv paxosnetNS (paxos_network_inv γ nids addrm).

End inv_network.
(* TODO: move them *)

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
  Definition is_paxos_addrm (paxos : loc) (addrm : gmap u64 chan) nids : iProp Σ :=
    ∃ (addrmP : loc),
      "#HaddrmP"   ∷ readonly (paxos ↦[Paxos :: "addrm"] #addrmP) ∗
      "#Haddrm"    ∷ own_map addrmP DfracDiscarded addrm ∗
      "%Hdomaddrm" ∷ ⌜dom addrm = nids⌝.

  Definition is_paxos_nids
    (paxos : loc) (nidme : u64) (nids : gset u64) : iProp Σ :=
    ∃ (peersP : Slice.t),
      let peers := nids ∖ {[nidme]} in
      "HnidmeP" ∷ readonly (paxos ↦[Paxos :: "nidme"] #nidme) ∗
      "HpeersP" ∷ readonly (paxos ↦[Paxos :: "peers"] (to_val peersP)) ∗
      "Hpeers"  ∷ readonly (own_slice_small peersP uint64T (DfracOwn 1) (elements peers)).

  Definition own_paxos_comm (paxos : loc) (addrm : gmap u64 chan) γ : iProp Σ :=
    ∃ (connsP : loc) (conns : gmap u64 (chan * chan)),
      let connsV := fmap (λ x, connection_socket x.1 x.2) conns in
      "HconnsP" ∷ paxos ↦[Paxos :: "conns"] #connsP ∗
      "Hconns"  ∷ map.own_map connsP (DfracOwn 1) (connsV, #()) ∗
      "#Htrmls" ∷ ([∗ map] x ∈ conns, is_terminal γ x.1) ∗
      "%Haddrpeers" ∷ ⌜map_Forall (λ nid x, addrm !! nid = Some x.2) conns⌝.

  Definition own_paxos_candidate_only
    (nidme termc terml termp : u64) (logc : list string)
    (entspP : Slice.t) (resppP : loc) nids γ : iProp Σ :=
    ∃ (entsp : list string) (respp : gmap u64 bool),
      "Hentsp"   ∷ own_slice entspP stringT (DfracOwn 1) entsp ∗
      "Hrespp"   ∷ own_map resppP (DfracOwn 1) respp ∗
      "#Hvotes"  ∷ votes_in γ (dom respp) (uint.nat termc) (uint.nat termp) (logc ++ entsp) ∗
      "#Hlsnprc" ∷ is_prepare_lsn γ (uint.nat termc) (length logc) ∗
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
    (paxos : loc) (nidme termc terml : u64) (log : list string) (isleader : bool)
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
    ∃ (log : list string),
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

  (* TODO: finding the right states to expose after adding network. *)

  Definition is_paxos_with_addrm_nids
    (paxos : loc) (nidme : u64) (addrm : gmap u64 chan) (nids : gset u64) γ : iProp Σ :=
    ∃ (mu : loc),
      "#HmuP"    ∷ readonly (paxos ↦[Paxos :: "mu"] #mu) ∗
      "#Hlock"   ∷ is_lock paxosNS #mu (own_paxos paxos nidme nids γ) ∗
      "#Hlockcm" ∷ is_lock paxosNS #mu (own_paxos_comm paxos addrm γ) ∗
      "#Haddrm"  ∷ is_paxos_addrm paxos addrm nids ∗
      "#Hnids"   ∷ is_paxos_nids paxos nidme nids ∗
      "#Hinv"    ∷ know_paxos_inv γ nids ∗
      "#Hinvnet" ∷ know_paxos_network_inv γ nids addrm ∗
      "%Hnidme"  ∷ ⌜nidme ∈ nids⌝.

  Definition is_paxos_with_addrm
    (paxos : loc) (nidme : u64) (addrm : gmap u64 chan) γ : iProp Σ :=
    ∃ (nids : gset u64),
      is_paxos_with_addrm_nids paxos nidme addrm nids γ.

  Definition is_paxos (paxos : loc) (nidme : u64) γ : iProp Σ :=
    ∃ (addrm : gmap u64 chan) (nids : gset u64),
      is_paxos_with_addrm_nids paxos nidme addrm nids γ.

End repr.

Section stepdown.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__stepdown px (nidme term : u64) termc nids γ :
    nidme ∈ nids ->
    uint.Z termc ≤ uint.Z term < 2 ^ 64 ->
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__stepdown #px #term
    {{{ RET #(); own_paxos_following_with_termc px nidme term nids γ }}}.
  Proof.
    iIntros (Hnidme Hlt) "#Hinv".
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
    destruct (decide (termc = term)) as [-> | Hne].
    { (* Case: [termc = term]. No logical updates required. *)
      iApply "HΦ".
      iFrame "HiscandP HisleaderP".
      by iFrame "∗ # %".
    }
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_prepare (uint.nat term) with "Htermc Hterml Hlogn HinvO")
      as "(Htermc & Hterml & Hlogn & HinvO & Hlsnp & #Hpromise)".
    { apply Hnidme. }
    { word. }
    iMod ("HinvC" with "HinvO") as "_".
    iApply "HΦ".
    iFrame "HisleaderP HiscandP".
    assert (Htermlc' : uint.Z terml ≤ uint.Z term) by word.
    iFrame "∗ # %".
    iClear "Hpreped Hlsnp".
    by case_decide.
  Qed.

End stepdown.

Section nominate.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__nominate (px : loc) (nidme : u64) nids γ :
    nidme ∈ nids ->
    is_paxos_nids px nidme nids -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos px nidme nids γ }}}
      Paxos__nominate #px
    {{{ (term : u64) (lsn : u64), RET (#term, #lsn);
        own_paxos px nidme nids γ ∗ is_prepare_lsn γ (uint.nat term) (uint.nat lsn)
    }}}.
  Proof.
    iIntros (Hnidme) "#Hnids #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
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
      as "(Htermc & Hterml & Hlogn & HinvO & Hlsnp & #Hpromise)".
    { apply Hnidme. }
    {  word. }
    destruct (decide (is_term_of_node nidme (uint.nat term))) as [Hton | Hnton]; last first.
    { exfalso. rewrite /is_term_of_node /max_nodes in Hnton. clear -Hmod Hnton. word. }
    set logc := take _ log.
    (* Set the prepare LSN to [length logc]. *)
    iMod (prepare_lsn_update (length logc) with "Hlsnp") as "#Hlsnprc".
    iMod ("HinvC" with "HinvO") as "_".

    (*@     return term, lsn                                                    @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    assert (Hton' : is_term_of_node nidme (uint.nat term)).
    { rewrite /is_term_of_node /max_nodes. word. }
    assert (Htermlt' : uint.Z terml ≤ uint.Z term) by word.
    assert (Hlcne' : uint.Z terml ≠ uint.Z term) by word.
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
    iModIntro.
    iSplit; last first.
    { rewrite length_take_le; last first.
      { clear -Hlsncub. lia. }
      iFrame "Hlsnprc".
    }
    iFrame "HiscandP HisleaderP".
    iFrame "∗ # %".
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
    {{{ own_paxos_nominated_with_termc_lsnc px nidme termc lsnc nids γ ∗
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
    nidme ∈ nids ->
    know_paxos_inv γ nids -∗
    {{{ own_paxos_nominated px nidme nids γ }}}
      Paxos__ascend #px
    {{{ RET #(); own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Hnidme) "#Hinv".
    iIntros (Φ) "!> Hpx HΦ".
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
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_ascend with "[] Htermc Hterml Hlogn HinvO")
      as "(Htermc & Hterml & Hlogn & HinvO & Hps & #Hpsb & #Hacptlb)".
    { apply Hnidme. }
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
    iAssert (own_paxos_leader px nidme termc termc log' true nids γ)%I
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
    nidme ∈ nids ->
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
    iIntros (Hnidme Hlsnle Hents) "#Hpfb #Hpfg #Hinv".
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
      iInv "Hinv" as "> HinvO" "HinvC".
      iMod (paxos_inv_advance with "Hpfb Hpfg Htermc Hterml Hlogn HinvO")
        as "(Htermc & Hterml & Hlogn & HinvO & #Hacpted')".
      { apply Hnidme. }
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
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_accept with "Hpfb Hpfg Htermc Hterml Hlogn HinvO")
      as "(Htermc & Hterml & Hlogn & HinvO & #Hacpted')".
    { apply Hnidme. }
    { apply Hlenlog. }
    iMod ("HinvC" with "HinvO") as "_".

    (*@     return lsna                                                         @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! _ logleader).
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
      set logc' := take (uint.nat lsnc) logleader.
      iAssert (safe_ledger_above γ nids (uint.nat terml) logc')%I as "Hcmted'".
      { subst logc.
        rewrite (take_prefix_le _ _ (uint.nat lsnc) _ Hprefix); first done.
        clear -Hlsncub. word.
      }
      iFrame "Hcmted'".
      iFrame "∗ # %".
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
        ⌜(uint.nat lsne ≤ length loga)%nat⌝ ∗
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
    nidme ∈ nids ->
    length logc = uint.nat lsn ->
    safe_ledger_above γ nids (uint.nat term) logc -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc_terml_iscand px nidme term term false nids γ }}}
      Paxos__commit #px #lsn
    {{{ RET #(); own_paxos_with_termc_terml_iscand px nidme term term false nids γ }}}.
  Proof.
    iIntros (Hnidme Hlenlogc) "#Hsafe #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) commit(lsn uint64) {                                   @*)
    (*@     if lsn <= px.lsnc {                                                 @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
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
      { rewrite Hdombs. apply Hnidme. }
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
      set logc' := take (uint.nat logP.(Slice.sz)) log.
      iDestruct (safe_ledger_above_weaken logc' with "Hsafe") as "Hsafe'".
      { subst logc'. rewrite -Hszlog firstn_all. apply Hprefix. }
      iFrame "Hsafe'".
      iFrame "∗ # %".
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
    assert (Hprefix : prefix logc log).
    { destruct Horprefix as [Hprefix | ?]; last done.
      rewrite (prefix_length_eq _ _ Hprefix); first done.
      lia.
    }
    set logc' := take (uint.nat lsn) log.
    iDestruct (safe_ledger_above_weaken logc' with "Hsafe") as "Hsafe'".
    { subst logc'. by rewrite -Hlenlogc take_length_prefix. }
    iFrame "Hsafe'".
    iFrame "∗ # %".
    iPureIntro.
    clear -Hlelog Hszlog. word.

    (*@     // TODO: Write @px.lsnc to disk.                                    @*)
    (*@ }                                                                       @*)
  Qed.

End commit.

Section learn.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__learn
    (px : loc) (lsn term : u64) (nidme : u64) (logc : list string) nids γ :
    nidme ∈ nids ->
    length logc = uint.nat lsn ->
    safe_ledger_above γ nids (uint.nat term) logc -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_following_with_termc px nidme term nids γ }}}
      Paxos__learn #px #lsn #term
    {{{ RET #(); own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Hnidme Hlenlogc) "#Hsafe #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) learn(lsn uint64, term uint64) {                       @*)
    (*@     // Skip if the log term @px.terml does not match @lsn.              @*)
    (*@     if term != px.terml {                                               @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_if_destruct.
    { iApply "HΦ".
      iFrame "Hcand Hleader".
      by iFrame "∗ # %".
    }

    (*@     px.commit(lsn)                                                      @*)
    (*@ }                                                                       @*)
    wp_apply (wp_Paxos__commit with "Hsafe Hinv [-HΦ]").
    { apply Hnidme. }
    { apply Hlenlogc. }
    { iFrame "Hcand Hleader".
      iFrame "∗ # %".
    }
    iIntros "Hpx".
    wp_pures.
    iApply "HΦ".
    iNamed "Hpx".
    by iFrame.
  Qed.

End learn.

Section push.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__push (px : loc) (nidme termc : u64) nids γ :
    nidme ∈ nids ->
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
    iIntros (Hnidme) "#Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) push() (uint64, bool) {                                @*)
    (*@     if !px.cquorum(uint64(len(px.lsnpeers)) + 1) {                      @*)
    (*@         // Nothing should be done without responses from some quorum of nodes. @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl".
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
    split; last apply Hnidme.
    split.
    { apply union_least; first set_solver.
      trans (dom lsnpeers); [apply dom_filter_subseteq | set_solver].
    }
    rewrite /cquorum_size.
    rewrite size_union; last first.
    { rewrite disjoint_singleton_l.
      assert (Hsubseteq : nidpeersq ⊆ nids ∖ {[nidme]}).
      { subst nidpeersq lsnpeersq.
        trans (dom lsnpeers); [apply dom_filter_subseteq | apply Hinclnids].
      }
      clear -Hsubseteq.
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
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) leading() bool {                                       @*)
    (*@     return px.isleader                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Hpx". iNamed "Hleader".
    wp_loadField.
    iApply "HΦ".
    destruct isleader; iFrame "Hpx Hcand"; iFrame.
  Qed.

  Theorem wp_Paxos__leading__with_termc (px : loc) nidme termc nids γ :
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__leading #px
    {{{ (isleader : bool), RET #isleader;
        if isleader
        then own_paxos_leading_with_termc px nidme termc nids γ
        else own_paxos px nidme nids γ
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) leading() bool {                                       @*)
    (*@     return px.isleader                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Hpx". iNamed "Hleader".
    wp_loadField.
    iApply "HΦ".
    destruct isleader; iFrame "Hpx Hcand"; iFrame.
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
      iAssert (own_paxos_leader px nidme termc termc log' true nids γ)%I
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
      iFrame "Hleader".
      set logc' := take (uint.nat lsnc) log'.
      iAssert (safe_ledger_above γ nids (uint.nat termc) logc')%I as "Hcmted'".
      { subst logc'.
        rewrite (take_prefix_le _ log' (uint.nat lsnc) _); last first.
        { by apply prefix_app_r. }
        { clear -Hlsncub. word. }
        done.
      }
      iFrame "Hcmted'".
      iFrame "∗ # %".
      iSplit.
      { iDestruct "Hgebase" as (vlb) "[Hvlb %Hprefix]".
        iFrame "Hvlb".
        iPureIntro.
        trans log; [apply Hprefix | by apply prefix_app_r].
      }
      iSplit.
      { by case_decide. }
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
      iFrame "Hcand Hleader".
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

Section lttermc.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__lttermc (px : loc) (term : u64) nidme nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__lttermc #px #term
    {{{ (outdated : bool), RET #outdated;
        if outdated
        then own_paxos px nidme nids γ
        else (∃ termc, own_paxos_with_termc px nidme termc nids γ ∧
                       ⌜uint.Z termc ≤ uint.Z term⌝)
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) lttermc(term uint64) bool {                            @*)
    (*@     return term < px.termc                                              @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_pures.
    iApply "HΦ".
    case_bool_decide.
    - iFrame "Hcand Hleader".
      by iFrame "∗ # %".
    - iFrame "Hcand Hleader".
      iFrame "∗ # %".
      iPureIntro. word.
  Qed.

End lttermc.

Section gttermc.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__gttermc (px : loc) (term : u64) nidme termc nids γ :
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__gttermc #px #term
    {{{ (invalid : bool), RET #invalid;
        own_paxos_with_termc px nidme termc nids γ ∗
        ⌜if invalid then True else uint.Z term ≤ uint.Z termc⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) gttermc(term uint64) bool {                            @*)
    (*@     return px.termc < term                                              @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_pures.
    iApply "HΦ".
    case_bool_decide as Horder.
    - iFrame "Hcand Hleader".
      by iFrame "∗ # %".
    - iFrame "Hcand Hleader".
      iFrame "∗ # %".
      iPureIntro.
      clear -Horder. word.
  Qed.

End gttermc.

Section gettermc.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__gettermc__following (px : loc) nidme termc nids γ :
    {{{ own_paxos_following_with_termc px nidme termc nids γ }}}
      Paxos__gettermc #px
    {{{ RET #termc; own_paxos_following_with_termc px nidme termc nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) gettermc() uint64 {                                    @*)
    (*@     return px.termc                                                     @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    iFrame "∗ # %".
  Qed.

  Theorem wp_Paxos__gettermc__leading (px : loc) nidme termc nids γ :
    {{{ own_paxos_leading_with_termc px nidme termc nids γ }}}
      Paxos__gettermc #px
    {{{ RET #termc; own_paxos_leading_with_termc px nidme termc nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) gettermc() uint64 {                                    @*)
    (*@     return px.termc                                                     @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    iFrame "∗ # %".
  Qed.

End gettermc.

Section latest.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__latest (px : loc) nidme termc nids γ :
    {{{ own_paxos_following_with_termc px nidme termc nids γ }}}
      Paxos__latest #px
    {{{ (latest : bool), RET #latest;
        if latest
        then own_paxos_following_with_termc px nidme termc nids γ
        else ∃ terml, own_paxos_with_termc_terml px nidme termc terml nids γ ∧
                      ⌜termc ≠ terml⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) latest() bool {                                        @*)
    (*@     return px.termc == px.terml                                         @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    do 2 wp_loadField.
    wp_pures.
    iApply "HΦ".
    case_bool_decide.
    - iFrame "Hcand Hleader".
      by iFrame "∗ # %".
    - iFrame "Hcand Hleader".
      iFrame "∗ # %".
      iPureIntro.
      by intros ->.
  Qed.

End latest.

Section nominated.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__nominated (px : loc) nidme termc nids γ :
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__nominated #px
    {{{ (iscand : bool), RET #iscand; 
        if iscand
        then own_paxos_nominated_with_termc px nidme termc nids γ
        else own_paxos_with_termc px nidme termc nids γ
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) nominated() bool {                                     @*)
    (*@     return px.iscand                                                    @*)
    (*@ }                                                                       @*)
    iNamed "Hpx". iNamed "Hcand".
    wp_loadField.
    iApply "HΦ".
    destruct iscand; iFrame.
  Qed.

End nominated.

Section getlsnc.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__getlsnc (px : loc) (nidme termc : u64) nids γ :
    {{{ own_paxos_leading_with_termc px nidme termc nids γ }}}
      Paxos__getlsnc #px
    {{{ (lsnc : u64) (logc : list string), RET #lsnc; 
        own_paxos_leading_with_termc px nidme termc nids γ ∗
        safe_ledger_above γ nids (uint.nat termc) logc ∗
        ⌜length logc = uint.nat lsnc⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) getlsnc() uint64 {                                     @*)
    (*@     return px.lsnc                                                      @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl". subst terml.
    wp_loadField.
    set logc := take _ log.
    iApply ("HΦ" $! _ logc).
    iFrame "Hcand HisleaderP".
    iFrame "∗ # %".
    iPureIntro.
    split; first done.
    rewrite length_take.
    clear -Hlsncub. lia.
  Qed.

End getlsnc.

Section heartbeat.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__heartbeat__following_with_termc (px : loc) nidme termc nids γ :
    {{{ own_paxos_following_with_termc px nidme termc nids γ }}}
      Paxos__heartbeat #px
    {{{ RET #(); own_paxos_following_with_termc px nidme termc nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) heartbeat() {                                          @*)
    (*@     px.hb = true                                                        @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_storeField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Paxos__heartbeat (px : loc) nidme nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__heartbeat #px
    {{{ RET #(); own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) heartbeat() {                                          @*)
    (*@     px.hb = true                                                        @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_storeField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    by iFrame "∗ # %".
  Qed.

End heartbeat.

Section heartbeated.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__heartbeated (px : loc) nidme nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__heartbeated #px
    {{{ (hb : bool), RET #hb; own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) heartbeated() bool {                                   @*)
    (*@     return px.hb                                                        @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    by iFrame "∗ # %".
  Qed.

End heartbeated.

Section paxos.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodePaxosRequestVoteRequest (term : u64) (lsnc : u64) :
    {{{ True }}}
      EncodePaxosRequestVoteRequest #term #lsnc
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_pxreq (RequestVoteReq term lsnc)⌝
    }}}.
  Proof.
    (*@ func EncodePaxosRequestVoteRequest(term uint64, lsnc uint64) []byte {  @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_EncodePaxosAppendEntriesRequest
    (term lsnc lsne : u64) (entsP : Slice.t) (ents : list string) :
    {{{ own_slice entsP stringT (DfracOwn 1) ents }}}
      EncodePaxosAppendEntriesRequest #term #lsnc #lsne (to_val entsP)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_pxreq (AppendEntriesReq term lsnc lsne ents)⌝
    }}}.
  Proof.
    (*@ func EncodePaxosAppendEntriesRequest(term uint64, lsnc, lsne uint64, ents []string) []byte { @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_EncodePaxosRequestVoteResponse
    (nid term terma : u64) (entsP : Slice.t) (ents : list string) :
    {{{ own_slice entsP stringT (DfracOwn 1) ents }}}
      EncodePaxosRequestVoteResponse #nid #term #terma (to_val entsP)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_pxresp (RequestVoteResp nid term terma ents)⌝
    }}}.
  Proof.
    (*@ func EncodePaxosRequestVoteResponse(term, terma uint64, ents []string) []byte { @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_EncodePaxosAppendEntriesResponse (nid : u64) (term : u64) (lsn : u64) :
    {{{ True }}}
      EncodePaxosAppendEntriesResponse #nid #term #lsn
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_pxresp (AppendEntriesResp nid term lsn)⌝
    }}}.
  Proof.
    (*@ func EncodePaxosAppendEntriesResponse(nid, term uint64, lsn uint64) []byte { @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_DecodePaxosRequest (dataP : Slice.t) (data : list u8) (req : pxreq) :
    data = encode_pxreq req ->
    {{{ own_slice dataP byteT (DfracOwn 1) data }}}
      DecodePaxosRequest (to_val dataP)
    {{{ (entsP : Slice.t), RET (pxreq_to_val req entsP);
        match req with
        | RequestVoteReq _ _ => True
        | AppendEntriesReq _ _ _ ents => own_slice entsP stringT (DfracOwn 1) ents
        end
    }}}.
  Proof.
    (*@ func DecodePaxosRequest(data []byte) PaxosRequest {                     @*)
    (*@     return PaxosRequest{}                                               @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_DecodePaxosResponse (dataP : Slice.t) (data : list u8) (resp : pxresp) :
    data = encode_pxresp resp ->
    {{{ True }}}
      DecodePaxosResponse (to_val dataP)
    {{{ (entsP : Slice.t), RET (pxresp_to_val resp entsP);
        match resp with
        | RequestVoteResp nid term terme ents => own_slice entsP stringT (DfracOwn 1) ents
        | AppendEntriesResp _ _ _ => True
        end
    }}}.
  Proof.
    (*@ func DecodePaxosResponse(data []byte) PaxosResponse {                   @*)
    (*@     return PaxosResponse{}                                              @*)
    (*@ }                                                                       @*)
  Admitted.

End paxos.

Section request_session.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__RequestSession (px : loc) (addrme trml : chan) nidme addrm γ :
    addrm !! nidme = Some addrme ->
    is_paxos_with_addrm px nidme addrm γ -∗
    {{{ True }}}
      Paxos__RequestSession #px (connection_socket addrme trml)
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Haddrme) "#Hinv".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) RequestSession(conn grove_ffi.Connection) {            @*)
    (*@     for {                                                               @*)
    (*@         ret := grove_ffi.Receive(conn)                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.
    wp_apply wp_Receive.
    iNamed "Hinv". iNamed "Hnids".
    iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvnetO".
    assert (is_Some (listens !! addrme)) as [msl Hmsl].
    { rewrite -elem_of_dom -Himgaddrm elem_of_map_img. by eauto. }
    iDestruct (big_sepM_lookup_acc with "Hlistens") as "[Hlst HlistensC]"; first apply Hmsl.
    iNamed "Hlst".
    iFrame "Hms".
    iIntros (err retdata) "[Hms Herr]".
    iDestruct ("HlistensC" with "[$Hms]") as "Hlistens"; first iFrame "# %".
    iMod "Hmask" as "_".
    iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_"; first done.
    iIntros "!>" (retdataP) "Hretdata".

    (*@         if ret.Err {                                                    @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_pures.
    destruct err; wp_pures.
    { by iApply "HΦ". }
    iDestruct "Herr" as "%Hmsg".
    assert (∃ req, retdata = encode_pxreq req ∧ req ∈ reqs) as (req & Hreq & Hinreqs).
    { specialize (Henc retdata).
      apply (elem_of_map_2 msg_data (D := gset (list u8))) in Hmsg.
      specialize (Henc Hmsg).
      by rewrite elem_of_map in Henc.
    }

    (*@         req  := message.DecodePaxosRequest(ret.Data)                    @*)
    (*@         kind := req.Kind                                                @*)
    (*@                                                                         @*)
    wp_apply (wp_DecodePaxosRequest with "Hretdata").
    { apply Hreq. }
    iIntros (entsaP) "Hentsa".
    destruct req as [term lsnc |]; wp_pures.
    { (* Case: RequestVote. *)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.

      (*@         px.mu.Lock()                                                    @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hpx]".
      wp_apply (wp_Paxos__lttermc with "Hpx").
      iIntros (outdated) "Hpx".

      (*@         if px.lttermc(req.Term) {                                       @*)
      (*@             // Skip the oudated message.                                @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             // We can additionally send an UPDATE-TERM message, but not sure if @*)
      (*@             // that's necessary, since eventually the new leader would reach out @*)
      (*@             // to every node.                                           @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      destruct outdated; wp_pures.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx]").
        wp_pures.
        by iApply "HΦ".
      }

      (*@         // Potentially proceed to a new term on receiving a higher-term message. @*)
      (*@         px.stepdown(req.Term)                                           @*)
      (*@                                                                         @*)
      iDestruct "Hpx" as (termc) "[Hpx %Hgetermc]".
      wp_apply (wp_Paxos__stepdown with "Hinv Hpx").
      { apply Hnidme. }
      { clear -Hgetermc. word. }
      iIntros "Hpx".

      (*@         px.heartbeat()                                                  @*)
      (*@                                                                         @*)
      wp_pures.
      wp_apply (wp_Paxos__heartbeat__following_with_termc with "Hpx").
      iIntros "Hpx".

      (*@         termc := px.gettermc()                                          @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__gettermc__following with "Hpx").
      iIntros "Hpx".
      wp_pures.

      (*@         if kind == message.MSG_PAXOS_REQUEST_VOTE {                     @*)
      (*@             if px.latest() {                                            @*)
      (*@                 // The log has already matched up the current term, meaning the @*)
      (*@                 // leader has already successfully been elected. Simply ignore @*)
      (*@                 // this request.                                        @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__latest with "Hpx").
      iIntros (latest) "Hpx".
      destruct latest; wp_pures.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }
      iDestruct "Hpx" as (terml) "[Hpx %Hcnel]".

      (*@             terml, ents := px.prepare(req.CommittedLSN)                 @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             data := message.EncodePaxosRequestVoteResponse(px.nidme, termc, terml, ents) @*)
      (*@             // Request [REQUEST-VOTE, @termc, @lsnc] and                @*)
      (*@             // Response [REQUEST-VOTE, @termc, @terml, @ents] means:    @*)
      (*@             // (1) This node will not accept any proposal with term below @termc. @*)
      (*@             // (2) The largest-term entries after LSN @lsnc this node has @*)
      (*@             // accepted before @termc is (@terml, @ents).               @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__prepare with "Hpx").
      { apply Hcnel. }
      iIntros (entsP ents logpeer) "(Hpx & Hents & #Hpastd & %Hents)".
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
      { iNamed "Hpx". iFrame. }
      wp_loadField.
      wp_apply (wp_EncodePaxosRequestVoteResponse with "Hents").
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      iNamed "Hinv".
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' nids γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := RequestVoteResp _ _ _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: AppendEntries. *)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.

      (*@         px.mu.Lock()                                                    @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hpx]".
      wp_apply (wp_Paxos__lttermc with "Hpx").
      iIntros (outdated) "Hpx".

      (*@         if px.lttermc(req.Term) {                                       @*)
      (*@             // Skip the oudated message.                                @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             // We can additionally send an UPDATE-TERM message, but not sure if @*)
      (*@             // that's necessary, since eventually the new leader would reach out @*)
      (*@             // to every node.                                           @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      destruct outdated; wp_pures.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx]").
        wp_pures.
        by iApply "HΦ".
      }

      (*@         // Potentially proceed to a new term on receiving a higher-term message. @*)
      (*@         px.stepdown(req.Term)                                           @*)
      (*@                                                                         @*)
      iDestruct "Hpx" as (termc) "[Hpx %Hgetermc]".
      wp_apply (wp_Paxos__stepdown with "Hinv Hpx").
      { apply Hnidme. }
      { clear -Hgetermc. word. }
      iIntros "Hpx".

      (*@         px.heartbeat()                                                  @*)
      (*@                                                                         @*)
      wp_pures.
      wp_apply (wp_Paxos__heartbeat__following_with_termc with "Hpx").
      iIntros "Hpx".

      (*@         termc := px.gettermc()                                          @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__gettermc__following with "Hpx").
      iIntros "Hpx".
      wp_pures.

      (*@         } else if kind == message.MSG_PAXOS_APPEND_ENTRIES {            @*)
      (*@             lsn := px.accept(req.LSNEntries, req.Term, req.Entries)     @*)
      (*@             px.learn(req.LeaderCommit, req.Term)                        @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             data := message.EncodePaxosAppendEntriesResponse(px.nidme, termc, lsn) @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@         }                                                               @*)
      (*@     }                                                                   @*)
      (*@ }                                                                       @*)
      iNamed "Hsafe".
      wp_apply (wp_Paxos__accept with "Hpfb Hpfg Hinv [$Hpx $Hentsa]").
      { apply Hnidme. }
      { apply Hlogleader. }
      { apply Hents. }
      iIntros (lsna loga) "(Hpx & #Haoc & %Hlenloga)".
      wp_pures.
      wp_apply (wp_Paxos__learn with "Hlogcmt Hinv Hpx").
      { apply Hnidme. }
      { apply Hlogcmt. }
      iIntros "Hpx".
      wp_loadField.

      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
      { iNamed "Hpx". iFrame. }
      wp_loadField.
      wp_apply (wp_EncodePaxosAppendEntriesResponse).
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      iNamed "Hinv".
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' nids γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := AppendEntriesResp _ _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
  Qed.

End request_session.

Section serve.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Serve (px : loc) nidme γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
      Paxos__Serve #px
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) Serve() {                                              @*)
    (*@     addrme := px.addrm[px.nidme]                                        @*)
    (*@     ls := grove_ffi.Listen(addrme)                                      @*)
    (*@     for {                                                               @*)
    (*@         conn := grove_ffi.Accept(ls)                                    @*)
    (*@         go func() {                                                     @*)
    (*@             px.RequestSession(conn)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hinv". iNamed "Haddrm". iNamed "Hnids".
    do 2 wp_loadField.
    wp_apply (wp_MapGet with "Haddrm").
    iIntros (addrme ok) "[%Hok _]".
    destruct ok; last first.
    { apply map_get_false in Hok as [Hok _].
      rewrite -not_elem_of_dom in Hok.
      set_solver.
    }
    apply map_get_true in Hok.
    wp_apply wp_Listen.
    wp_pures.
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.
    wp_apply wp_Accept.
    iIntros (chanpeer) "_".
    wp_pures.
    wp_apply (wp_fork).
    { (* Fork. *)
      wp_apply wp_Paxos__RequestSession.
      { apply Hok. }
      { iFrame "# %". }
      done.
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

End serve.

Section get_connection.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__GetConnection
    (px : loc) (nid : u64) (nidme : u64) (addrm : gmap u64 chan) (addrpeer : chan) γ :
    addrm !! nid = Some addrpeer ->
    is_paxos_with_addrm px nidme addrm γ -∗
    {{{ True }}}
      Paxos__GetConnection #px #nid
    {{{ (trml : chan) (ok : bool), RET (if ok 
                                     then (connection_socket trml addrpeer, #true)
                                     else (#(), #false));
        if ok then is_terminal γ trml else True
    }}}.
  Proof.
    iIntros (Haddrpeer) "#Hpx".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) GetConnection(nid uint64) (grove_ffi.Connection, bool) { @*)
    (*@     px.mu.Lock()                                                        @*)
    (*@     conn, ok := px.conns[nid]                                           @*)
    (*@     px.mu.Unlock()                                                      @*)
    (*@     return conn, ok                                                     @*)
    (*@ }                                                                       @*)
    iNamed "Hpx".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlockcm").
    iIntros "[Hlocked Hcomm]".
    iNamed "Hcomm".
    wp_loadField.
    wp_apply (map.wp_MapGet with "Hconns").
    iIntros (connV ok) "[%Hok Hconns]".
    wp_pures.
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlockcm Hlocked". iFrame "∗ # %". }
    wp_pures.
    destruct ok; last first.
    { apply map.map_get_false in Hok as [_ ->].
      (* [U64 0] is a placeholder *)
      by iApply ("HΦ" $! (U64 0) false).
    }
    apply map.map_get_true in Hok.
    rewrite lookup_fmap_Some in Hok.
    destruct Hok as ([trml addrpeer'] & <- & Hconns).
    iDestruct (big_sepM_lookup with "Htrmls") as "Htrml"; first apply Hconns.
    apply Haddrpeers in Hconns.
    rewrite Haddrpeer in Hconns.
    symmetry in Hconns. inv Hconns.
    by iApply ("HΦ" $! _ true).
  Qed.

End get_connection.

Section connect.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Connect
    (px : loc) (nid : u64) (nidme : u64) (addrm : gmap u64 chan) (addrpeer : chan) γ :
    addrm !! nid = Some addrpeer ->
    is_paxos_with_addrm px nidme addrm γ -∗
    {{{ True }}}
      Paxos__Connect #px #nid
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros (Haddrpeer) "#Hpx".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) Connect(nid uint64) bool {                             @*)
    (*@     addr := px.addrm[nid]                                               @*)
    (*@     ret := grove_ffi.Connect(addr)                                      @*)
    (*@     if !ret.Err {                                                       @*)
    (*@         px.mu.Lock()                                                    @*)
    (*@         px.conns[nid] = ret.Connection                                  @*)
    (*@         px.mu.Unlock()                                                  @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    iNamed "Hpx". iNamed "Haddrm".
    wp_loadField.
    wp_apply (wp_MapGet with "Haddrm").
    iIntros (addrpeer' ok) "[%Hok _]".
    destruct ok; last first.
    { apply map_get_false in Hok as [Hok _].
      by rewrite Haddrpeer in Hok.
    }
    apply map_get_true in Hok.
    rewrite Haddrpeer in Hok.
    symmetry in Hok. inv Hok.
    wp_pures.
    wp_apply wp_Connect.
    iIntros (err trml) "Htrml".
    wp_pures.
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlockcm").
      iIntros "[Hlocked Hcomm]".
      iNamed "Hcomm".
      wp_loadField.
      wp_apply (map.wp_MapInsert with "Hconns").
      iIntros "Hconns".
      wp_loadField.
      (* Seal [trml c↦ ∅] in the network invariant and obtain [is_terminal γ trml]. *)
      iApply ncfupd_wp.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iNamed "HinvnetO".
      iMod (terminal_update trml with "Hterminals") as "[Hterminals #Htrmlrcpt]".
      iMod ("HinvnetC" with "[$Hlistens Hconnects Hterminals Htrml]") as "_".
      { iModIntro.
        iExists (<[trml := ∅]> connects).
        rewrite dom_insert_L.
        iFrame "Hterminals %".
        iApply (big_sepM_insert_2 with "[Htrml] Hconnects").
        iExists ∅.
        iFrame.
        iSplit; first by rewrite big_sepS_empty.
        iPureIntro.
        by rewrite 2!set_map_empty.
      }
      iModIntro.
      wp_apply (wp_Mutex__Unlock with "[$Hlockcm $Hlocked $HconnsP Hconns]").
      { iModIntro.
        iExists (<[nid := (trml, addrpeer)]> conns).
        rewrite fmap_insert.
        iFrame "Hconns".
        iSplit.
        { by iApply big_sepM_insert_2. }
        iPureIntro.
        by apply map_Forall_insert_2.
      }
      wp_pures.
      by iApply "HΦ".
    }
    by iApply "HΦ".
  Qed.

End connect.

Section send.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Send
    (px : loc) (nid : u64) (dataP : Slice.t) (data : list u8) (nidme : u64)
    (addrm : gmap u64 chan) (addrpeer : chan) γ :
    addrm !! nid = Some addrpeer ->
    is_paxos_with_addrm px nidme addrm γ -∗
    {{{ own_slice dataP byteT (DfracOwn 1) data }}}
    <<< ∀∀ ms, addrpeer c↦ ms >>>
      Paxos__Send #px #nid (to_val dataP) @ ∅
    <<< ∃∃ (ok : bool),
            if ok 
            then ∃ trml, addrpeer c↦ ({[Message trml data]} ∪ ms) ∗ is_terminal γ trml
            else addrpeer c↦ ms
    >>>
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Haddrpeer) "#Hpx".
    iIntros (Φ) "!> Hdata HAU".
    wp_rec.

    (*@ func (px *Paxos) Send(nid uint64, data []byte) {                        @*)
    (*@     conn, ok := px.GetConnection(nid)                                   @*)
    (*@     if !ok {                                                            @*)
    (*@         px.Connect(nid)                                                 @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__GetConnection with "Hpx").
    { apply Haddrpeer. }
    iIntros (trml ok) "#Htrmlrcpt".
    wp_pures.
    destruct ok; wp_pures; last first.
    { wp_apply (wp_Paxos__Connect with "Hpx").
      { apply Haddrpeer. }
      iIntros (ok) "Hok".
      wp_pures.
      (* Open the AU without updating. *)
      iMod (ncfupd_mask_subseteq (⊤ ∖ ∅)) as "Hclose"; first solve_ndisj.
      iMod "HAU" as (ms) "[Hms HAU]".
      iMod ("HAU" $! false with "Hms") as "HΦ".
      iMod "Hclose" as "_".
      by iApply "HΦ".
    }

    (*@     err := grove_ffi.Send(conn, data)                                   @*)
    (*@     if err {                                                            @*)
    (*@         px.Connect(nid)                                                 @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iDestruct (own_slice_to_small with "Hdata") as "Hdata".
    wp_apply (wp_Send with "Hdata").
    iMod "HAU" as (ms) "[Hms HAU]".
    iFrame "Hms".
    iIntros "!>" (sent) "Hms".
    iMod ("HAU" $! sent with "[Hms]") as "HΦ".
    { rewrite union_comm_L. by destruct sent; first iFrame. }
    iModIntro.
    iIntros (err) "[%Herr Hdata]".
    wp_pures.
    wp_if_destruct.
    { wp_apply (wp_Paxos__Connect with "Hpx").
      { apply Haddrpeer. }
      iIntros (ok) "_".
      wp_pures.
      by iApply "HΦ".
    }
    by iApply "HΦ".
  Qed.

End send.

Section receive.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Receive
    (px : loc) (nid : u64) (nidme : u64)
    (addrpeer : chan) (addrm : gmap u64 chan) nids γ :
    addrm !! nid = Some addrpeer ->
    is_paxos_with_addrm_nids px nidme addrm nids γ -∗
    {{{ True }}}
      Paxos__Receive #px #nid
    {{{ (dataP : Slice.t) (ok : bool), RET (to_val dataP, #ok);
        if ok
        then ∃ (data : list u8) (resp : pxresp),
            own_slice dataP byteT (DfracOwn 1) data ∗
            safe_pxresp γ nids resp ∗
            ⌜data = encode_pxresp resp⌝
        else True
    }}}.
  Proof.
    iIntros (Haddrpeer) "#Hpx".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) Receive(nid uint64) ([]byte, bool) {                   @*)
    (*@     conn, ok := px.GetConnection(nid)                                   @*)
    (*@     if !ok {                                                            @*)
    (*@         px.Connect(nid)                                                 @*)
    (*@         return nil, false                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__GetConnection with "[Hpx]").
    { apply Haddrpeer. }
    { iFrame "#". }
    iIntros (trml ok) "#Htrmlrcpt".
    wp_pures.
    destruct ok; wp_pures; last first.
    { wp_apply (wp_Paxos__Connect with "[Hpx]").
      { apply Haddrpeer. }
      { iFrame "#". }
      iIntros (ok) "Hok".
      wp_pures.
      by iApply ("HΦ" $! Slice.nil false).
    }

    (*@     ret := grove_ffi.Receive(conn)                                      @*)
    (*@     if ret.Err {                                                        @*)
    (*@         px.Connect(nid)                                                 @*)
    (*@         return nil, false                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_Receive.
    iNamed "Hpx".
    iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
    iApply ncfupd_mask_intro; first solve_ndisj.
    iIntros "Hmask".
    iNamed "HinvnetO".
    iDestruct (terminal_lookup with "Htrmlrcpt Hterminals") as %Htrml.
    apply elem_of_dom in Htrml as [ms Hms].
    iDestruct (big_sepM_lookup_acc with "Hconnects") as "[Htrml HconnectsC]".
    { apply Hms. }
    iNamed "Htrml".
    iFrame "Hms".
    iIntros (err data) "[Hms Hmsg]".
    iDestruct ("HconnectsC" with "[$Hms]") as "Hconnects"; first iFrame "# %".
    iMod "Hmask" as "_".
    iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_"; first done.
    iIntros "!>" (dataP) "Hdata".
    wp_pures.
    destruct err; wp_pures.
    { wp_apply (wp_Paxos__Connect with "[]").
      { apply Haddrpeer. }
      { by iFrame "#". }
      iIntros (ok) "Hok".
      wp_pures.
      by iApply ("HΦ" $! Slice.nil false).
    }

    (*@     return ret.Data, true                                               @*)
    (*@ }                                                                       @*)
    iDestruct "Hmsg" as %Hmsg.
    assert (∃ resp, data = encode_pxresp resp ∧ resp ∈ resps) as (resp & Hresp & Hinresps).
    { specialize (Henc data).
      apply (elem_of_map_2 msg_data (D := gset (list u8))) in Hmsg.
      specialize (Henc Hmsg).
      by rewrite elem_of_map in Henc.
    }
    iDestruct (big_sepS_elem_of with "Hresps") as "Hresp"; first apply Hinresps.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End receive.

Section leader_session.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__LeaderSession (px : loc) (nidme : u64) γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
      Paxos__LeaderSession #px
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hpx" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) LeaderSession() {                                      @*)
    (*@     for {                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.

    (*@         primitive.Sleep(params.NS_BATCH_INTERVAL)                       @*)
    (*@                                                                         @*)
    wp_apply wp_Sleep.

    (*@         px.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    iNamed "Hpx".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hpx]".    

    (*@         if !px.leading() {                                              @*)
    (*@             px.mu.Unlock()                                              @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__leading with "Hpx").
    iIntros (isleader) "Hpx".
    destruct isleader; wp_pures; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx]").
      wp_pures.
      by iApply "HΦ".
    }

    (*@         // TODO: Write @px.log to disk before sending out APPEND-ENTRIES. @*)
    (*@                                                                         @*)
    (*@         for _, nidloop := range(px.peers) {                             @*)
    (*@                                                                         @*)
    set P := (λ (_ : u64), own_paxos_leading px nidme nids γ)%I.
    iNamed "Hnids".
    wp_loadField.
    iMod (readonly_load with "Hpeers") as (q) "HpeersR".
    wp_apply (wp_forSlice P with "[] [$HpeersR $Hpx]").
    { (* Loop body. *)
      clear Φ.
      iIntros (i nid Φ) "!> (Hpx & %Hbound & %Hnid) HΦ".

      (*@             nid := nidloop                                              @*)
      (*@             lsne, ents := px.obtain(nid)                                @*)
      (*@             termc := px.gettermc()                                      @*)
      (*@             lsnc  := px.getlsnc()                                       @*)
      (*@                                                                         @*)
      wp_pures.
      subst P. simpl.
      iAssert (∃ termc, own_paxos_leading_with_termc px nidme termc nids γ)%I
        with "Hpx" as (termc) "Hpx".
      wp_apply (wp_Paxos__obtain with "Hpx").
      iIntros (lsne entsP ents loga) "(Hpx & Hents & #Hpfb & #Hpfg & %Hlenloga & %Hents)".
      wp_pures.
      wp_apply (wp_Paxos__gettermc__leading with "Hpx").
      iIntros "Hpx".
      wp_apply (wp_Paxos__getlsnc with "Hpx").
      iIntros (lsnc logc) "(Hpx & #Hlogc & %Hlenlogc)".
      wp_pures.

      (*@             go func() {                                                 @*)
      (*@                 data := message.EncodePaxosAppendEntriesRequest(termc, lsnc, lsne, ents) @*)
      (*@                 px.Send(nid, data)                                      @*)
      (*@             }()                                                         @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_apply (wp_fork with "[Hents]").
      { iModIntro.
        clear Φ.
        wp_apply (wp_EncodePaxosAppendEntriesRequest with "Hents").
        iIntros (dataP data) "[Hdata %Hdataenc]".
        iNamed "Haddrm".
        assert (is_Some (addrm !! nid)) as [addrpeer Haddrpeer].
        { rewrite -elem_of_dom Hdomaddrm.
          apply elem_of_list_lookup_2 in Hnid.
          set_solver.
        }
        wp_apply (wp_Paxos__Send with "[] Hdata"); first apply Haddrpeer.
        { iFrame "# %". }
        iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iNamed "HinvnetO".
        assert (is_Some (listens !! addrpeer)) as [ms Hms].
        { rewrite -elem_of_dom -Himgaddrm elem_of_map_img. by eauto. }
        iDestruct (big_sepM_delete with "Hlistens") as "[Hlst Hlistens]"; first apply Hms.
        iNamed "Hlst".
        iFrame "Hms".
        iIntros (sent) "Hms".
        destruct sent; last first.
        { iDestruct (big_sepM_insert_2 _ _ addrpeer ms with "[Hms] Hlistens") as "Hlistens".
          { iFrame "∗ # %". }
          rewrite insert_delete; last apply Hms.
          iMod "Hmask" as "_".
          iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_".
          { done. }
          done.
        }
        iDestruct "Hms" as (trml) "[Hms #Htrml]".
        set ms' := _ ∪ ms.
        iDestruct (big_sepM_insert_2 _ _ addrpeer ms' with "[Hms] Hlistens") as "Hlistens".
        { iFrame "Hms".
          set req := AppendEntriesReq _ _ _ _ in Hdataenc.
          iExists ({[req]} ∪ reqs).
          iSplit.
          { rewrite set_map_union_L set_map_singleton_L.
            by iApply big_sepS_insert_2.
          }
          iSplit.
          { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
          iPureIntro.
          rewrite 2!set_map_union_L 2!set_map_singleton_L /= -Hdataenc.
          set_solver.
        }
        rewrite insert_delete_insert.
        iMod "Hmask" as "_".
        iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_".
        { iPureIntro.
          rewrite dom_insert_L Himgaddrm.
          apply (elem_of_map_img_2 (SA := gset chan)) in Haddrpeer.
          set_solver.
        }
        done.
      }
      iApply "HΦ".
      iFrame.
    }

    (*@         px.mu.Unlock()                                                  @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iIntros "[Hpx _]".
    wp_loadField.
    subst P.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
    { iNamed "Hpx". iFrame. }
    wp_pures.
    by iApply "HΦ".
  Qed.

End leader_session.

Section election_session.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__ElectionSession (px : loc) (nidme : u64) γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
      Paxos__ElectionSession #px
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hpx" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) ElectionSession() {                                    @*)
    (*@     for {                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.

    (*@         delta := primitive.RandomUint64() % params.NS_ELECTION_TIMEOUT_DELTA @*)
    (*@         primitive.Sleep(params.NS_ELECTION_TIMEOUT_BASE + delta)        @*)
    (*@                                                                         @*)
    wp_apply wp_RandomUint64.
    iIntros (dt) "_".
    wp_apply wp_Sleep.

    (*@         px.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    iNamed "Hpx".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hpx]".
    wp_pures.

    (*@         if px.leading() {                                               @*)
    (*@             px.mu.Unlock()                                              @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__leading with "Hpx").
    iIntros (isleader) "Hpx".
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
      { iNamed "Hpx". iFrame. }
      wp_pures.
      by iApply "HΦ".
    }

    (*@         if px.heartbeated() {                                           @*)
    (*@             px.mu.Unlock()                                              @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__heartbeated with "Hpx").
    iIntros (hb) "Hpx".
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
      { iNamed "Hpx". iFrame. }
      wp_pures.
      by iApply "HΦ".
    }

    (*@         px.heartbeat()                                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__heartbeat with "Hpx").
    iIntros "Hpx".

    (*@         termc, lsnc := px.nominate()                                    @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__nominate with "Hnids Hinv Hpx").
    { apply Hnidme. }
    iIntros (termc lsnc) "[Hpx #Hlsnprc]".

    (*@         px.mu.Unlock()                                                  @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx]").

    (*@         for _, nidloop := range(px.peers) {                             @*)
    (*@             nid := nidloop                                              @*)
    (*@             go func() {                                                 @*)
    (*@                 data := message.EncodePaxosRequestVoteRequest(termc, lsnc) @*)
    (*@                 px.Send(nid, data)                                      @*)
    (*@             }()                                                         @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hnids".
    wp_loadField.
    iMod (readonly_load with "Hpeers") as (q) "HpeersR".
    wp_apply (wp_forSlice (λ _, True)%I with "[] [$HpeersR]").
    { (* Loop body. *)
      clear Φ.
      iIntros (i nid Φ) "!> (Hpx & %Hbound & %Hnid) HΦ".
      wp_pures.
      wp_apply wp_fork.
      { wp_apply wp_EncodePaxosRequestVoteRequest.
        iIntros (dataP data) "[Hdata %Hdataenc]".
        iNamed "Haddrm".
        assert (is_Some (addrm !! nid)) as [addrpeer Haddrpeer].
        { rewrite -elem_of_dom Hdomaddrm.
          apply elem_of_list_lookup_2 in Hnid.
          set_solver.
        }
        wp_apply (wp_Paxos__Send with "[] Hdata"); first apply Haddrpeer.
        { iFrame "# %". }
        iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iNamed "HinvnetO".
        assert (is_Some (listens !! addrpeer)) as [ms Hms].
        { rewrite -elem_of_dom -Himgaddrm elem_of_map_img. by eauto. }
        iDestruct (big_sepM_delete with "Hlistens") as "[Hlst Hlistens]"; first apply Hms.
        iNamed "Hlst".
        iFrame "Hms".
        iIntros (sent) "Hms".
        destruct sent; last first.
        { iDestruct (big_sepM_insert_2 _ _ addrpeer ms with "[Hms] Hlistens") as "Hlistens".
          { iFrame "∗ # %". }
          rewrite insert_delete; last apply Hms.
          iMod "Hmask" as "_".
          iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_".
          { done. }
          done.
        }
        iDestruct "Hms" as (trml) "[Hms #Htrml]".
        set ms' := _ ∪ ms.
        iDestruct (big_sepM_insert_2 _ _ addrpeer ms' with "[Hms] Hlistens") as "Hlistens".
        { iFrame "Hms".
          set req := RequestVoteReq _ _ in Hdataenc.
          iExists ({[req]} ∪ reqs).
          iSplit.
          { rewrite set_map_union_L set_map_singleton_L.
            by iApply big_sepS_insert_2.
          }
          iSplit.
          { iApply big_sepS_insert_2; last done.
            iFrame "Hlsnprc".
          }
          iPureIntro.
          rewrite 2!set_map_union_L 2!set_map_singleton_L /= -Hdataenc.
          set_solver.
        }
        rewrite insert_delete_insert.
        iMod "Hmask" as "_".
        iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_".
        { iPureIntro.
          rewrite dom_insert_L Himgaddrm.
          apply (elem_of_map_img_2 (SA := gset chan)) in Haddrpeer.
          set_solver.
        }
        done.
      }
      by iApply "HΦ".
    }
    iIntros "_".
    wp_pures.
    by iApply "HΦ".
  Qed.

End election_session.

Section response_sesion.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__ResponseSession
    (px : loc) (nid : u64) (nidme : u64)
    (addrpeer : chan) (addrm : gmap u64 chan) nids γ :
    addrm !! nid = Some addrpeer ->
    is_paxos_with_addrm_nids px nidme addrm nids γ -∗
    {{{ True }}}
      Paxos__ResponseSession #px #nid
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Haddrpeer) "#Hpx".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) ResponseSession(nid uint64) {                          @*)
    (*@     for {                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.

    (*@         data, ok := px.Receive(nid)                                     @*)
    (*@         if !ok {                                                        @*)
    (*@             // Try to re-establish a connection on failure.             @*)
    (*@             primitive.Sleep(params.NS_RECONNECT)                        @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Receive with "Hpx").
    { apply Haddrpeer. }
    iIntros (dataP ok) "Hdata".
    wp_pures.
    destruct ok; wp_pures; last first.
    { wp_apply wp_Sleep.
      wp_pures.
      by iApply "HΦ".
    }
    iDestruct "Hdata" as (data resp) "(Hdata & #Hresp & %Hdataenc)".

    (*@         resp := message.DecodePaxosResponse(data)                       @*)
    (*@         kind := resp.Kind                                               @*)
    (*@                                                                         @*)
    wp_apply wp_DecodePaxosResponse.
    { apply Hdataenc. }
    iIntros (entsP) "Hents".
    destruct resp as [nid' term terme ents | nid' term lsneq]; wp_pures.
    { (* Case: RequestVote. *)
      
      (*@         px.mu.Lock()                                                    @*)
      (*@                                                                         @*)
      iNamed "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hpx]".

      (*@         if px.lttermc(resp.Term) {                                      @*)
      (*@             // Skip the outdated message.                               @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_pures.
      wp_apply (wp_Paxos__lttermc with "Hpx").
      iIntros (outdated) "Hpx".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx]").
        wp_pures.
        by iApply "HΦ".
      }

      (*@         // In the current design, the response would never contain a term higher @*)
      (*@         // than that in a request, and that means this check is actually not @*)
      (*@         // used. However, it is kept for two reasons: First, if adding an @*)
      (*@         // UPDATE-TERM becomes necessary (for performance or liveness reason), @*)
      (*@         // then this check would then be useful. Second, in the proof, with this @*)
      (*@         // check and the one above we obtain @px.termc = @resp.Term, which is @*)
      (*@         // very useful. If we ever want to eliminate this check in the future, @*)
      (*@         // we will have to find a way to encode ``responses terms never go higher @*)
      (*@         // than request terms'' in the proof.                           @*)
      (*@         if px.gttermc(resp.Term) {                                      @*)
      (*@             // Proceed to a new term on receiving a higher-term message. @*)
      (*@             px.stepdown(resp.Term)                                      @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_pures.
      iDestruct "Hpx" as (termc) "[Hpx %Hgttermc]".
      wp_apply (wp_Paxos__gttermc with "Hpx").
      iIntros (invalid) "[Hpx %Hlttermc]".
      wp_if_destruct.
      { wp_pures.
        wp_apply (wp_Paxos__stepdown with "Hinv Hpx").
        { apply Hnidme. }
        { clear -Hgttermc. word. }
        iIntros "Hpx".
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }
      assert (termc = term) as ->.
      { clear -Hgttermc Hlttermc. word. }
      wp_pures.

      (*@         if kind == message.MSG_PAXOS_REQUEST_VOTE {                     @*)
      (*@             if !px.nominated() {                                        @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__nominated with "Hpx").
      iIntros (iscand) "Hpx".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx]").
        wp_pures.
        by iApply "HΦ".
      }
      iAssert (∃ lsnc, own_paxos_nominated_with_termc_lsnc px nidme term lsnc nids γ)%I
        with "[Hpx]" as (lsnc) "Hpx".
      { iNamed "Hpx". iFrame. }

      (*@             // Ideally, we should not need to include the node ID in the @*)
      (*@             // response, since the entire session is used exclusively by @nid @*)
      (*@             // (i.e., in reality @resp.NodeID should always be the same as @*)
      (*@             // @nid). In the proof, we could maintain a persistent mapping from @*)
      (*@             // channels to node IDs. However, it seems like the current network @*)
      (*@             // semantics does not guarantee *freshness* of creating a channel @*)
      (*@             // through @Connect, and hence such invariant cannot be established. @*)
      (*@             px.collect(resp.NodeID, resp.TermEntries, resp.Entries)     @*)
      (*@             px.ascend()                                                 @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@                                                                         @*)
      iNamed "Hresp".
      iAssert (⌜lsne = lsnc⌝)%I as %->.
      { iNamed "Hpx". iNamed "Hcand". iNamed "Honlyc". iNamed "Hpx".
        iDestruct (prepare_lsn_eq with "Hlsne Hlsnprc") as %Heq.
        rewrite length_take_le in Heq; last first.
        { clear -Hlsncub. lia. }
        clear -Heq.
        iPureIntro.
        clear -Heq.
        word.
      }
      wp_pures.
      wp_apply (wp_Paxos__collect with "Hpromise Hinv [$Hpx $Hents]").
      { apply Hinnids. }
      { apply Hents. }
      iIntros "Hpx".
      wp_apply (wp_Paxos__ascend with "Hinv Hpx").
      { apply Hnidme. }
      iIntros "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx]").
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: AppendEntries. *)

      (*@         px.mu.Lock()                                                    @*)
      (*@                                                                         @*)
      iNamed "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hpx]".

      (*@         if px.lttermc(resp.Term) {                                      @*)
      (*@             // Skip the outdated message.                               @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_pures.
      wp_apply (wp_Paxos__lttermc with "Hpx").
      iIntros (outdated) "Hpx".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx]").
        wp_pures.
        by iApply "HΦ".
      }

      (*@         // In the current design, the response would never contain a term higher @*)
      (*@         // than that in a request, and that means this check is actually not @*)
      (*@         // used. However, it is kept for two reasons: First, if adding an @*)
      (*@         // UPDATE-TERM becomes necessary (for performance or liveness reason), @*)
      (*@         // then this check would then be useful. Second, in the proof, with this @*)
      (*@         // check and the one above we obtain @px.termc = @resp.Term, which is @*)
      (*@         // very useful. If we ever want to eliminate this check in the future, @*)
      (*@         // we will have to find a way to encode ``responses terms never go higher @*)
      (*@         // than request terms'' in the proof.                           @*)
      (*@         if px.gttermc(resp.Term) {                                      @*)
      (*@             // Proceed to a new term on receiving a higher-term message. @*)
      (*@             px.stepdown(resp.Term)                                      @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_pures.
      iDestruct "Hpx" as (termc) "[Hpx %Hgttermc]".
      wp_apply (wp_Paxos__gttermc with "Hpx").
      iIntros (invalid) "[Hpx %Hlttermc]".
      wp_if_destruct.
      { wp_pures.
        wp_apply (wp_Paxos__stepdown with "Hinv Hpx").
        { apply Hnidme. }
        { clear -Hgttermc. word. }
        iIntros "Hpx".
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }
      assert (termc = term) as ->.
      { clear -Hgttermc Hlttermc. word. }
      wp_pures.

      (*@         } else if kind == message.MSG_PAXOS_APPEND_ENTRIES {            @*)
      (*@             if !px.leading() {                                          @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__leading__with_termc with "Hpx").
      iIntros (isleader) "Hpx".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx]").
        wp_pures.
        by iApply "HΦ".
      }
      wp_pures.

      (*@             // Same as the reason above, the check below is performed merely for @*)
      (*@             // the sake of proof.                                       @*)
      (*@             if resp.NodeID == px.nidme {                                @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      iNamed "Hnids".
      wp_loadField.
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }
      rename Heqb into Hnotme.
      wp_pures.

      (*@             forwarded := px.forward(resp.NodeID, resp.MatchedLSN)       @*)
      (*@             if !forwarded {                                             @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      iNamed "Hresp".
      wp_apply (wp_Paxos__forward with "Haoc Hinv Hpx").
      { apply Hnotme. }
      { apply Hinnids. }
      { apply Hlogacpt. }
      iIntros (forwarded) "Hpx".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }

      (*@             lsnc, pushed := px.push()                                   @*)
      (*@             if !pushed {                                                @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__push with "Hinv Hpx").
      { apply Hnidme. }
      iIntros (lsnc pushed) "[Hpx #Hpushed]".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }
      iDestruct "Hpushed" as (logc) "[Hcmted %Hlenlogc]".

      (*@             px.commit(lsnc)                                             @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@         }                                                               @*)
      (*@     }                                                                   @*)
      (*@ }                                                                       @*)
      wp_apply (wp_Paxos__commit with "Hcmted Hinv [Hpx]").
      { apply Hnidme. }
      { apply Hlenlogc. }
      { iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl".
        iDestruct (terml_eq_termc_impl_not_nominiated with "Hcand") as %->.
        { apply Hleqc. }
        subst terml.
        iFrame "Hcand Hpx HisleaderP".
        by iFrame "∗ # %".
      }
      iIntros "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx]").
      { iNamed "Hpx". iFrame. }
      wp_pures.
      by iApply "HΦ".
    }
  Qed.

End response_sesion.

Section mk_paxos.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_MkPaxos :
    {{{ True }}}
      MkPaxos #()
    {{{ (px : loc), RET #px; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func MkPaxos() *Paxos {                                                 @*)
    (*@     conns := make(map[uint64]grove_ffi.Connection)                      @*)
    (*@     px := &Paxos{                                                       @*)
    (*@         conns : conns,                                                  @*)
    (*@     }                                                                   @*)
    (*@     return px                                                           @*)
    (*@ }                                                                       @*)
    wp_apply (map.wp_NewMap).
    iIntros (conns) "Hconns".
    rewrite {1}/zero_val /=.
    wp_pures.
    wp_apply (wp_allocStruct).
    { by auto 20. }
    iIntros (px) "Hpx".
    wp_pures.
    iApply "HΦ".
  Admitted.

End mk_paxos.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

End program.
