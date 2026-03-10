From iris.algebra.lib Require Import mono_nat.
Require Import New.proof.go_etcd_io.raft.v3_proof.protocol.
Require Export New.proof.proof_prelude.
Require Export New.golang.theory.

(* Q: what's the invariant for MsgHeartbeat and MsgHeartbeatResp?
   Must ensure after getting MsgHeartbeatResp, the follower was still in the
   leader's term at some point *after* the MsgHeartbeat was created.

   Potentially provable spec: associated to each pair (heartbeat ctx, nodeId),
   there can be a (persistent) atomic update that gets temporary access to
   ownership of the nodeId's latest term being equal to the leader's term.

   This, combined with some assumed raft invariants, will imply that the
   committed log (onto which the ReadState AU was placed) contains that node's
   log.  Importantly, the ONLY node that should commit entries should be the
   leader.  Otherwise, something might be committed and made visible to clients,
   without the leader knowing it. Part of the reason to commit a noop entry is
   so that the leader actually knows about something committed in its term, so
   the above argument works.

   Q: what's the invariant for readOnly? Must imply that receiving heartbeats
   for the last entry implies the earlier entries are OK too.
   A: There is no invariant implying the earlier entries are OK because the code
   is buggy: https://github.com/etcd-io/etcd/issues/20418#issuecomment-3974901065
   The problem is that network retries mean that old ReadIndex requests might
   get queued *after* new ReadIndex requests. The new ReadIndex request might
   have started after the current node was not the latest leader, but the old
   ReadIndex might have valid heartbeat responses. Thus, when `raft.readOnly`
   validates the entire queue up to a valid entry, it might validate a stale
   read index for a recent request.

   Related raft issue (with test case linked):
   https://github.com/etcd-io/raft/issues/392

   TODO: prove fixed version of raft libary
   TODO: prove weaker spec for existing raft library, to justify backportable
   fix to etcd. In particular, if `ReadIndex` is only called once (i.e. if each
   `MsgReadIndex` comes with an exclusive ghost token), then should be able to
   create a monolist of RequestCtxes in the proof, such that if any RequestCtx
   is validated, then all the RequestCtxes before are also valid (i.e. were
   up-to-date when created).

   Can probably avoid prophecy variables by having spec for creating a
   RequestCtx guarantee: "valid(index, request_ctx) ∨ node is no longer leader".
   "valid(index, request_ctx)" means that `request_ctx`'s persistent AU is
   registered for (re)execution at some index `j` and `j ≤ index`.
 *)

Record raft_names :=
  {
    commited_gn : gname;
    prop_gn : gname;
    term_gn : gname;
    config_gn : gname;
    reads_gn : gname;
    read_req_gn : gname;
    heartbeat_gn : gname;
  }.

Section global_proof.

Implicit Types (γ : raft_names) (log : list (list w8)) (node_id term index : w64)
               (read_req_ctx ctx : go_string).

Context `{!invGS Σ} `{!allG Σ}.
Context (N : namespace).

(** Ghost state for raft protocol *)
Definition own_commit_auth γ log := mono_list_auth_own γ.(commited_gn) (1/2) log.
Definition own_commit γ log := mono_list_auth_own γ.(commited_gn) (1/2) log.
Definition is_commit γ log := mono_list_lb_own γ.(commited_gn) log.

Definition own_term γ node_id term := own γ.(term_gn) {[ node_id := ●MN (sint.nat term) ]}.
Definition is_term_lb γ node_id term := own γ.(term_gn) {[ node_id := ◯MN (sint.nat term) ]}.

Definition own_unused_heartbeat_ctx γ term ctx : iProp Σ :=
  ∃ (per_term_gn ctx_gn : gname),
    term ↪[γ.(heartbeat_gn)]□ per_term_gn ∗
    ctx ↪[per_term_gn]□ ctx_gn ∗
    dghost_var ctx_gn (DfracOwn 1) (∅ : gset w64).
Definition is_heartbeat_ctx γ term ctx (srvs : gset w64) : iProp Σ :=
  ∃ (per_term_gn ctx_gn : gname),
    term ↪[γ.(heartbeat_gn)]□ per_term_gn ∗
    ctx ↪[per_term_gn]□ ctx_gn ∗
    dghost_var ctx_gn DfracDiscarded srvs.

(* Given ownership of unused (term, Context) pair, one can decide its staleness quorum. *)

(** Propositions defined in terms of the primitive ghost state. *)

(* This proof assumes there's only one configuration (for now). *)
Context (cfg : gset w64).

Axiom own_committed_in_term : ∀ γ (term : w64) (log : list $ list w8), iProp Σ.
Axiom is_committed_in_term : ∀ γ (term : w64) (log : list $ list w8), iProp Σ.
Axiom is_committed_in_term_pers : ∀ γ term log, Persistent (is_committed_in_term γ term log).
Global Existing Instance is_committed_in_term_pers.

Definition is_stale_term γ term : iProp Σ :=
  ∃ quorum,
    "%Hquorum" ∷ ⌜ quorum ⊆ cfg ∧ size cfg < 2 * size quorum ⌝ ∗
    "#Hterm_lbs" ∷
      □(∀ node_id (Hin_quorum : node_id ∈ quorum),
         ∃ term', is_term_lb γ node_id term' ∗ ⌜ sint.nat term < sint.nat term' ⌝).

Axiom committed_in_term_agree : ∀ γ term log1 log2,
  own_committed_in_term γ term log1 -∗
  is_committed_in_term γ term log2 -∗
  ⌜ prefix log2 log1 ⌝.

(* When own and is have different terms, the own term is stale. *)
Axiom committed_in_term_stale : ∀ γ term1 term2 log1 log2,
  term1 ≠ term2 →
  own_committed_in_term γ term1 log1 -∗
  is_committed_in_term γ term2 log2 -∗
  is_stale_term γ term1.

(* TODO: set this up to confirm backwards compatibility (i.e. if some raft
   servers run the new code and some run the old code, system is still safe;
   only the leader needs to run the new code in order for the system to tolerate
   duplicate ReadIndex requests). *)

(** Ownership of the reads queue: an authoritative monotone list of
    (start_index, saved_pred_gname) pairs. The gnames are hidden internally;
    the caller sees only [readsΦ : list (w64 * (list (list w8) → iProp Σ))]. *)
Definition own_reads γ (readsΦ : list (w64 * (list (list w8) → iProp Σ))) : iProp Σ :=
  ∃ l : list (w64 * gname),
    ⌜l.*1 = readsΦ.*1⌝ ∗
    mono_list_auth_own γ.(reads_gn) 1 l ∗
    ∀ i si Φ gn,
      ⌜readsΦ !! i = Some (si, Φ)⌝ →
      ⌜l !! i = Some (si, gn)⌝ →
      saved_pred_own gn DfracDiscarded Φ.

(** Persistent witness that (start_index, Φ) is tracked in the reads queue. *)
Definition is_in_reads γ (si : w64) (Φ : list (list w8) → iProp Σ) : iProp Σ :=
  ∃ i gn,
    mono_list_idx_own γ.(reads_gn) i (si, gn) ∗
    saved_pred_own gn DfracDiscarded Φ.

Global Instance is_in_reads_persistent γ si Φ :
  Persistent (is_in_reads γ si Φ) := _.

(** Insert a new read entry at the end of the list, obtaining a persistent witness. *)
Lemma reads_insert γ readsΦ si Φ :
  own_reads γ readsΦ ==∗
  own_reads γ (readsΦ ++ [(si, Φ)]) ∗ is_in_reads γ si Φ.
Proof.
  iIntros "(%l & %Hfst & Hauth & #Hfor)".
  iMod (saved_pred_alloc Φ DfracDiscarded) as (gn) "#Hgn". { done. }
  iMod (mono_list_auth_own_update_app [(si, gn)] with "Hauth") as "[Hauth #Hlb]".
  have Hlen : length l = length readsΦ.
  { rewrite -(length_fmap fst l) -(length_fmap fst readsΦ) Hfst //. }
  iModIntro. iSplit.
  - iExists (l ++ [(si, gn)]). iSplit.
    { iPureIntro. rewrite !fmap_app /= Hfst //. }
    iFrame "Hauth".
    iIntros (i si' Φ' gn' Hreads Hl').
    destruct (decide (i < length readsΦ)%nat) as [Hi|Hi%not_lt].
    + rewrite lookup_app_l in Hreads; last done.
      rewrite lookup_app_l in Hl'; last lia.
      iApply ("Hfor" $! i si' Φ' gn' Hreads Hl').
    + rewrite lookup_app_r in Hreads; last done.
      rewrite lookup_app_r in Hl'; last lia.
      destruct (i - length readsΦ)%nat eqn:Hdiff.
      * have Hdiff' : (i - length l = 0)%nat by lia.
        rewrite Hdiff' /= in Hl'. injection Hl' as [= _ <-].
        simpl in *. simplify_eq.
        iExact "Hgn".
      * discriminate.
  - iExists (length l), gn. iSplit; last done.
    iApply (mono_list_idx_own_get with "Hlb").
    rewrite lookup_app_r // Nat.sub_diag //.
Qed.

(** Agreement: the witness corresponds to an entry in [readsΦ] with
    a propositionally equal predicate (up to ▷). *)
Lemma reads_agree γ readsΦ si Φ (x : list (list w8)) :
  own_reads γ readsΦ -∗
  is_in_reads γ si Φ -∗
  ∃ i Ψ,
    ⌜readsΦ !! i = Some (si, Ψ)⌝ ∗
    ▷ (Φ x ≡ Ψ x).
Proof.
  iIntros "(%l & %Hfst & Hauth & #Hfor)". iDestruct 1 as (i gn) "[#Hidx #Hgn]".
  iDestruct (mono_list_auth_idx_lookup with "Hauth Hidx") as %Hl.
  (* [Hl : l !! i = Some (si, gn)]; derive readsΦ !! i from Hfst *)
  have Hsi : readsΦ.*1 !! i = Some si.
  { rewrite -Hfst list_lookup_fmap Hl //. }
  (* list_lookup_fmap_inv does not exist *)
  apply list_lookup_fmap_Some_1 in Hsi as ([si' Φ'] & [= <-] & HreadsΦ).
  iDestruct ("Hfor" $! i si Φ' gn HreadsΦ Hl) as "#HΨ".
  iExists i, Φ'. iFrame "%".
  iApply (saved_pred_agree with "Hgn HΨ").
Qed.

Definition Ncommit := N.@"commit".
Definition is_raft_commit_inv γ : iProp Σ := (*  *)
  inv Ncommit (∃ term log (readsΦ : list (w64 * (list $ list w8 → iProp Σ))), (*  *)
        "commit" ∷ own_commit_auth γ log ∗
        "#Hcommit" ∷ is_committed_in_term γ term log ∗
        "reads" ∷ own_reads γ readsΦ ∗

        (* Permission to linearize reads on all future logs.
           For any Φ stored in the reads queue, firing its AU against the
           current committed log produces Φ applied to that log. *)
        "#Hread_aus" ∷ □(∀ Φ (Hin : Φ ∈ readsΦ.*2) log,
                           own_commit_auth γ log ={⊤∖↑N}=∗
                           own_commit_auth γ log ∗ Φ log) ∗
        (* Witnesses that reads were linearized on every index starting at their
           respective starting index. *)
        "#Hread_wits" ∷ □(∀ start_index Φ (Hindex : (start_index, Φ) ∈ readsΦ)
                            index (Hindex : sint.nat start_index ≤ sint.nat index ≤ length log),
                            Φ (take (sint.nat index) log))
    ).

(* A read index witness: given any committed log at least as long as [index],
   opening the invariant at mask ⊤ lets us fire the stored AU to get [Φ log].
   Needs £ 2: one credit to open the invariant (strip ▷), one to strip the ▷
   from saved_pred_agree. *)
Definition is_read_index γ index Φ : iProp Σ :=
  ∀ log (Hin : sint.nat index ≤ length log),
  £ 2 -∗ is_commit γ log ={⊤}=∗ Φ log.

(** Try to add a read with continuation `Φ` to be executed forever starting at
   the committed index from term `term`. *)
Lemma try_read γ term log Φ :
  "Hlc" ∷ £ 1 ∗
  "#Hinv" ∷ is_raft_commit_inv γ ∗
  "Hcom" ∷ own_committed_in_term γ term log ∗
  "#Hau" ∷ □(|={⊤∖↑N,∅}=> ∃ log, own_commit γ log ∗ (own_commit γ log ={∅,⊤∖↑N}=∗ □ Φ log))
  ={⊤}=∗
  own_committed_in_term γ term log ∗ (is_read_index γ (W64 (length log)) Φ ∨ is_stale_term γ term).
Proof.
  iNamed 1.
  iInv "Hinv" as "Hi". iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iDestruct "Hi" as (inv_term inv_log inv_readsΦ)
    "(Hcommit_auth & #Hcommit_term & Hreads & #Hread_aus & #Hread_wits)".
  destruct (decide (term = inv_term)) as [<- | Hneq].
  - (* Same term: the committed log in the invariant matches our term. *)
    iDestruct (committed_in_term_agree with "Hcom Hcommit_term") as %Hle.
    (* Insert (W64 (length inv_log), Φ) into the reads queue. *)
    iMod (reads_insert _ _ (W64 (length inv_log)) Φ with "Hreads") as "[Hreads #Hin_reads]".
    (* Re-establish Hread_aus for the extended list. *)
    iAssert (□(∀ Φ0 (Hin : Φ0 ∈ (inv_readsΦ ++ [(W64 (length inv_log), Φ)]).*2) log0,
                 own_commit_auth γ log0 ={⊤∖↑N}=∗ own_commit_auth γ log0 ∗ Φ0 log0))%I
      as "#Hread_aus_new".
    { iIntros "!>" (Φ0 Hin log0) "Hca".
      rewrite fmap_app /= in Hin.
      apply elem_of_app in Hin as [Hin|Hin].
      - iApply ("Hread_aus" $! Φ0 Hin log0 with "Hca").
      - apply list_elem_of_singleton in Hin as ->.
        iMod "Hau" as (log_au) "[Hcommit Hclose]".
        iDestruct (mono_list_auth_own_agree with "Hca Hcommit") as %[_ <-].
        iMod ("Hclose" with "Hcommit") as "#HΦ".
        iModIntro. iFrame "∗#%". }
    (* Close the invariant with the extended reads list. *)
    iSplitR "Hcom".
    {
      iMod fupd_mask_subseteq as "Hmask"; last iMod "Hau" as "H"; first solve_ndisj.
      iDestruct "H" as (?) "(Hcom & Hclose)".
      iDestruct (mono_list_auth_own_agree with "Hcom Hcommit_auth") as %Heq.
      iMod ("Hclose" with "Hcom") as "#HΦ". iMod "Hmask". iModIntro.
      iExists term, inv_log, (inv_readsΦ ++ [(W64 (length inv_log), Φ)]).
      iFrame "∗#".
      destruct Heq as [_ <-].
      iNext. iIntros "!>" (start_index Φ0 Hindex index Hindex2).
      apply elem_of_app in Hindex as [Hindex|Hindex].
      - iApply ("Hread_wits" $! start_index Φ0 Hindex index Hindex2).
      - apply list_elem_of_singleton in Hindex as [= -> <-].
        rewrite take_ge; first iExact "HΦ".
        admit. (* FIXME: overflow of log0 *)
    }
    (* TODO: proceed with the proof. Use `is_in_reads` to prove
       `is_read_index`. Make a separate lemma for this for clarity. If you get
       stuck, or don't know how to make the proof work, then interview me about
       the challenges. *)
    admit.
  - (* Different term: term is stale. *)
    iDestruct (committed_in_term_stale with "Hcom Hcommit_term") as "#Hstale".
    { done. }
    iSplitR "Hcom".
    { iExists inv_term, inv_log, inv_readsΦ. iFrame "∗#". done. }
    iModIntro. iFrame "Hcom". iRight. iExact "Hstale".
Admitted.

Definition is_heartbeat_ctx_stale γ term ctx stale_ids : iProp Σ :=
  is_heartbeat_ctx γ term ctx stale_ids ∗
  □(∀ id, ⌜ id ∈ stale_ids ⌝ → ∃ term', is_term_lb γ id term' ∗ ⌜ sint.nat term < sint.nat term' ⌝).

Definition is_HeartbeatRequest γ (term : w64) (ctx : list w8) : iProp Σ :=
  ∃ stale_ids, is_heartbeat_ctx_stale γ term ctx stale_ids.

(** [is_HeartbeatResp] confirms that [from] was not stale back when [ctx] was
  first used in [term]. *)
Definition is_HeartbeatResp γ (from : w64) (term : w64) (ctx : list w8) : iProp Σ :=
  ∃ srvs, is_heartbeat_ctx γ term ctx srvs ∗ ⌜ from ∉ srvs ⌝.

Lemma start_heartbeat stale_ids γ term ctx :
  □(∀ id, ⌜ id ∈ stale_ids ⌝ → ∃ term', is_term_lb γ id term' ∗ ⌜ sint.nat term < sint.nat term' ⌝) -∗
  own_unused_heartbeat_ctx γ term ctx ==∗
  is_heartbeat_ctx_stale γ term ctx stale_ids.
Proof.
  iIntros "#Hstale Hunused".
  iDestruct "Hunused" as (per_term_gn ctx_gn) "(#Hterm & #Hctx & Hvar)".
  iMod (dghost_var_update stale_ids with "Hvar") as "Hvar".
  iMod (dghost_var_persist with "Hvar") as "#Hvar".
  iModIntro.
  iSplit.
  - iExists per_term_gn, ctx_gn. iFrame "#".
  - iFrame "#".
Qed.

(*
Lemma start_req_ctx Φ req_ctx index γ :
  own_read_req_ctx γ req_ctx ∗
  □(|={⊤∖↑N,∅}=> ∃ log, own_commit γ log ∗ (own_commit γ log ={∅,⊤∖↑N}=∗ Φ log))
  ={⊤}=∗
  is_read_req_ctx γ req_ctx Φ.
Proof.
Admitted.

Definition is_MsgReadIndex γ read_req_ctx : iProp Σ :=
  ∃ Φ, is_read_req_ctx γ read_req_ctx Φ.

Definition is_MsgReadIndexResp γ read_req_ctx index : iProp Σ :=
  ∃ Φ, is_read_req_ctx γ read_req_ctx Φ ∗
       is_read_index γ index Φ. *)

End global_proof.

Section wps.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.

Axiom own_raft : ∀ (γ : raft_names) (rf : raft.raft.t), iProp Σ.

(* FIXME: own_ProgressTracker precondition *)
Lemma wp_ProgressTracker__IsSingleton (p : loc) :
  {{{ True }}}
    p @! (go.PointerType tracker.ProgressTracker) @! "IsSingleton" #()
  {{{ RET #false; True }}}.
Proof.
Admitted.

Lemma wp_raft__committedEntryInCurrentTerm r rf γ :
  {{{ r ↦ rf ∗ own_raft γ rf }}}
    r @! (go.PointerType raft.raft) @! "committedEntryInCurrentTerm" (# ())
  {{{ (c : bool), RET #c; r ↦ rf ∗ own_raft γ rf ∗
                 if c then ∃ l, is_committed_in_term γ rf.(raft.raft.Term') l else True
  }}}.
Proof.
Admitted.

Definition MsgReadIndex := W32 15.
Lemma wp_raft__sendMsgReadIndexresponse γ r rf m :
  {{{ "Hr" ∷ r ↦ rf ∗
      "Hrf" ∷ own_raft γ rf ∗
      "%HmType" ∷ ⌜ m.(raftpb.Message.Type') = MsgReadIndex ⌝ ∗
      "#Hcom_in_term" ∷ True
  }}}
    @! raft.sendMsgReadIndexResponse #r #m
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
Admitted. (* TODO *)

Lemma wp_raft__stepLeader_MsgReadIndex γ r (rf : raft.raft.t) (m : raftpb.Message.t) :
  {{{ "Hr" ∷ r ↦ rf ∗
      "Hrf" ∷ own_raft γ rf ∗
      "%HmType" ∷ ⌜ m.(raftpb.Message.Type') = MsgReadIndex ⌝ }}}
    @! raft.stepLeader #r #m
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto. rewrite HmType.
  wp_auto.
  wp_apply wp_ProgressTracker__IsSingleton.
  wp_apply (wp_raft__committedEntryInCurrentTerm with "[$]").
  iIntros "%committedInTerm (Hr & Hrf & Hcom)".
  wp_if_destruct.
  - admit.
Admitted.

End wps.
