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
    term_gn : gname;
    config_gn : gname;
    reads_gn : gname;
    read_req_gn : gname;
    heartbeat_gn : gname;
  }.

Section proof.
Context (cfg : gset w64).

Section global_proof.

Implicit Types (γ : raft_names) (log : list (list w8)) (node_id term index : w64)
               (read_req_ctx ctx : go_string).

Context `{!invGS Σ} `{!allG Σ}.
Definition N := nroot.

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

Axiom own_committed_in_term : ∀ γ (term : w64) (log : list $ list w8), iProp Σ.
Axiom is_committed_in_term : ∀ γ (term : w64) (log : list $ list w8), iProp Σ.
Axiom is_committed_in_term_pers : ∀ γ term log, Persistent (is_committed_in_term γ term log).
Global Existing Instance is_committed_in_term_pers.

Definition is_quorum (quorum : gset w64) : Prop :=
  quorum ⊆ cfg ∧ size cfg < 2 * size quorum.

Definition is_stale_term γ term : iProp Σ :=
  ∃ quorum,
    "%Hquorum" ∷ ⌜ is_quorum quorum ⌝ ∗
    "#Hterm_lbs" ∷
      □(∀ id, ⌜ id ∈ quorum ⌝ → ∃ term', is_term_lb γ id term' ∗ ⌜ sint.nat term < sint.nat term' ⌝).

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
  □ (∀ log (Hin : sint.nat index ≤ length log) (Hno_overflow : length log < 2^63),
       £ 2 -∗ is_commit γ log ={⊤}=∗ Φ log).

Lemma is_in_reads_to_valid γ i j Φ :
  "#Hinv" ∷ is_raft_commit_inv γ ∗
  "#Hr" ∷ is_in_reads γ j Φ ∗
  "%Hj" ∷ ⌜ sint.nat j ≤ sint.nat i ⌝ -∗
  is_read_index γ i Φ.
Proof.
  iNamed 1. rewrite /is_read_index.
  iIntros "!# %log_wit %Hlog_wit %Hoverflow [Hlc Hlc2] #Hlog_wit". rewrite /is_read_index.
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi".
  iDestruct (mono_list_auth_lb_valid with "commit Hlog_wit") as %[_ Hle].
  iDestruct (reads_agree with "[$] [$]") as (? Ψ) "(%Hr_lookup & #HΦ)".
  iDestruct ("Hread_wits" $! j Ψ with "[%]") as "Hwit".
  { by eapply list_elem_of_lookup_2. }
  iSpecialize ("Hwit" $! (W64 (length log_wit)) with "[%]").
  { apply prefix_length in Hle. word. }
  replace (sint.nat (W64 (length log_wit))) with (length log_wit) by word.
  rewrite -prefix_to_take //.
  iMod (lc_fupd_elim_later with "[$] HΦ") as "#HΦ'".
  iMod ("Hclose" with "[-]").
  { iFrame "∗#%". }
  iModIntro. instantiate (1:=log_wit).
  iRewrite "HΦ'". done.
Qed.

(** Try to add a read with continuation `Φ` to be executed forever starting at
   the committed index from term `term`. *)
Lemma try_read γ term log Φ :
  "Hlc" ∷ £ 1 ∗
  "%Hno_overflow" ∷ ⌜ length log < 2^63 ⌝ ∗
  "#Hinv" ∷ is_raft_commit_inv γ ∗
  "Hcom" ∷ own_committed_in_term γ term log ∗
  "#Hau" ∷ □(|={⊤∖↑N,∅}=> ∃ log, own_commit γ log ∗ (own_commit γ log ={∅,⊤∖↑N}=∗ □ Φ log))
  ={⊤}=∗
  ∃ (stale_ids : gset w64),
    □(∀ id, ⌜ id ∈ stale_ids ⌝ → ∃ term', is_term_lb γ id term' ∗ ⌜ sint.nat term < sint.nat term' ⌝) ∗
    own_committed_in_term γ term log ∗
    (is_read_index γ (W64 (length log)) Φ ∨ ⌜ is_quorum stale_ids ⌝).
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
        apply prefix_length in Hle. word.
    }
    iModIntro. iModIntro. iFrame.
    iExists ∅.
    iSplitR.
    { iIntros "!#". iIntros. done. }
    iLeft.
    iDestruct (is_in_reads_to_valid with "[]") as "$".
    iFrame "#". iPureIntro. apply prefix_length in Hle. word.
  - (* Different term: term is stale. *)
    iDestruct (committed_in_term_stale with "Hcom Hcommit_term") as "#Hstale".
    { done. }
    iSplitR "Hcom".
    { iExists inv_term, inv_log, inv_readsΦ. iFrame "∗#". done. }
    iModIntro. iFrame "Hcom". iNamed "Hstale".
    iFrame "#". iRight. done.
Qed.

Definition is_heartbeat_ctx_stale γ term ctx stale_ids : iProp Σ :=
  is_heartbeat_ctx γ term ctx stale_ids ∗
  □(∀ id, ⌜ id ∈ stale_ids ⌝ → ∃ term', is_term_lb γ id term' ∗ ⌜ sint.nat term < sint.nat term' ⌝).

Definition is_HeartbeatRequest γ (term : w64) (ctx : list w8) : iProp Σ :=
  ∃ stale_ids, is_heartbeat_ctx_stale γ term ctx stale_ids.

(** [is_HeartbeatResp] confirms that [from] was not stale back when [ctx] was
  first used in [term]. *)
Definition is_HeartbeatResp γ (from : w64) (term : w64) (ctx : list w8) : iProp Σ :=
  ∃ srvs, is_heartbeat_ctx γ term ctx srvs ∗ ⌜ from ∉ srvs ⌝.

(** [is_heartbeat_ack] witnesses that [from] acknowledged heartbeat context
    [ctx] in [term], confirming [from] was not stale at that point.
    Similar to [is_HeartbeatResp] but used as a precondition for [recvAck]. *)
Definition is_heartbeat_ack γ (from : w64) (term : w64) (ctx : go_string) : iProp Σ :=
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

Definition own_read_req_ctx γ read_req_ctx : iProp Σ :=
  ∃ γreq,
    "#Hγreq" ∷ read_req_ctx ↪[γ.(read_req_gn)]□ γreq ∗
    "Hreq" ∷ saved_pred_own γreq (DfracOwn 1) (λ (_ : list (list w8)), True).

Definition is_read_req_ctx γ read_req_ctx (Φ : list (list w8) → iProp Σ) : iProp Σ :=
  ∃ γreq,
    "#Hγreq" ∷ read_req_ctx ↪[γ.(read_req_gn)]□ γreq ∗
    "#Hreq" ∷ saved_pred_own γreq DfracDiscarded Φ ∗
    "#Hau" ∷ □(|={⊤∖↑N,∅}=> ∃ log, own_commit γ log ∗ (own_commit γ log ={∅,⊤∖↑N}=∗ □ Φ log)).

Lemma start_req_ctx Φ req_ctx index γ :
  own_read_req_ctx γ req_ctx ∗
  □(|={⊤∖↑N,∅}=> ∃ log, own_commit γ log ∗ (own_commit γ log ={∅,⊤∖↑N}=∗ □ Φ log))
  ={⊤}=∗
  is_read_req_ctx γ req_ctx Φ.
Proof.
  iIntros "[Hown #Hau]".
  iNamed "Hown".
  iMod (saved_pred_update with "Hreq") as "Hreq".
  iMod (saved_pred_persist with "Hreq") as "#?".
  by iFrame "#".
Qed.

Definition is_MsgReadIndex γ read_req_ctx : iProp Σ :=
  ∃ Φ, is_read_req_ctx γ read_req_ctx Φ.

Definition is_MsgReadIndexResp γ read_req_ctx index : iProp Σ :=
  ∃ Φ, is_read_req_ctx γ read_req_ctx Φ ∗
       is_read_index γ index Φ.

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
Admitted. (* Trusted *)

Lemma wp_raft__committedEntryInCurrentTerm r rf γ :
  {{{ r ↦ rf ∗ own_raft γ rf }}}
    r @! (go.PointerType raft.raft) @! "committedEntryInCurrentTerm" (# ())
  {{{ (c : bool), RET #c; r ↦ rf ∗ own_raft γ rf ∗
                 if c then ∃ l, is_committed_in_term γ rf.(raft.raft.Term') l else True
  }}}.
Proof.
Admitted. (* Trusted *)

Definition is_readIndexRequest γ (r : loc) read_req_ctx index : iProp Σ :=
  ∃ read_req,
    "#r" ∷ r ↦□ read_req ∗
    "#ctx" ∷ read_req.(raft.readIndexRequest.req').(raftpb.Message.Context') ↦*□ read_req_ctx ∗
    "%Hindex" ∷ ⌜ read_req.(raft.readIndexRequest.index') = index ⌝ ∗
    "#His_read" ∷ (∃ Φ, is_read_req_ctx γ read_req_ctx Φ).

Definition own_heartbeat_auth γ (term : w64) (highest_index : w64) : iProp Σ :=
  ∃ per_term_gn (used : gmap go_string gname),
    term ↪[γ.(heartbeat_gn)]□ per_term_gn ∗
    ghost_map_auth per_term_gn 1 used ∗
    ⌜ ∀ k, k ∈ dom used → 0 ≤ sint.Z (le_to_u64 k) ≤ sint.Z highest_index ⌝.

Definition own_readOnly γ (r : loc) (term : w64) : iProp Σ :=
  ∃ (ro : raft.readOnly.t) (acks : gmap w64 w64) (unconfirmedReads : list loc),
    "r" ∷ r ↦ ro ∗
    "Hacks" ∷ ro.(raft.readOnly.acks') ↦$ acks ∗
    "#Hacks_wits" ∷ □(∀ voterId ackedIdx,
                          ⌜ acks !! voterId = Some ackedIdx ⌝ →
                          is_heartbeat_ack γ voterId term (u64_le ackedIdx)) ∗
    "%Hoption" ∷ ⌜ ro.(raft.readOnly.option') = W64 0 ⌝ ∗ (* equals ReadOnlySafe *)
    "unconfirmedReads" ∷ ro.(raft.readOnly.unconfirmedReads') ↦* unconfirmedReads ∗
    "unconfirmedReads_cap" ∷ own_slice_cap loc ro.(raft.readOnly.unconfirmedReads') (DfracOwn 1) ∗
    "#HunconfirmedReads" ∷ □(
        ∀ i r, ⌜ unconfirmedReads !! i = Some r ⌝ →
               (∃ read_req_ctx stale_ids index,
                   let hb_ctx :=
                     (u64_le (word.add ro.(raft.readOnly.confirmedReads') (W64 $ Z.of_nat (S i)))) in
                   "#readIndexRequest" ∷ is_readIndexRequest γ r read_req_ctx index ∗
                   "#Hhb" ∷ is_heartbeat_ctx_stale γ term hb_ctx stale_ids ∗
                   "#Hstale_or_safe" ∷
                     (⌜ is_quorum stale_ids ⌝ ∨ (∃ Φ, is_read_req_ctx γ read_req_ctx Φ ∗
                                                      is_read_index γ index Φ))
               )
      ) ∗
    "Hhb●" ∷ own_heartbeat_auth γ term
      (word.add ro.(raft.readOnly.confirmedReads') (W64 $ length unconfirmedReads)).

Lemma own_heartbeat_auth_new stale_ids γ term highest_index :
  0 ≤ sint.Z highest_index < (2^63-1) →
  own_heartbeat_auth γ term highest_index ==∗
  own_heartbeat_auth γ term (word.add highest_index (W64 1)) ∗
  is_heartbeat_ctx γ term (u64_le (word.add highest_index (W64 1))) stale_ids.
Proof.
  intros. iIntros "(% & % & #? & Hauth & %Hused)".
  iMod (dghost_var_alloc stale_ids) as (per_hb_ctx_gn) "H".
  iPersist "H".
  iMod (ghost_map_insert_persist (u64_le (word.add highest_index (W64 1))) per_hb_ctx_gn with
       "[$]") as "[? ?]".
  {
    specialize (Hused (u64_le (word.add highest_index (W64 1)))).
    destruct lookup eqn:Hlookup; try done.
    apply elem_of_dom_2 in Hlookup.
    specialize (Hused ltac:(done)).
    rewrite u64_le_to_word in Hused.
    word.
  }
  iFrame "∗#%". iPureIntro.
  intros k. rewrite dom_insert. rewrite elem_of_union.
  intros [Helem|].
  2:{ specialize (Hused k ltac:(done)). word. }
  rewrite elem_of_singleton in Helem. subst.
  rewrite u64_le_to_word. word.
Qed.

Lemma wp_readOnly_addRequest γ r term (commitIndex : w64) req read_req_ctx log dq Ψ :
  {{{ is_pkg_init raft ∗
      "#Hinv" ∷ is_raft_commit_inv γ ∗
      "Hown" ∷ own_readOnly γ r term ∗
      "Hcom" ∷ own_committed_in_term γ term log ∗
      "%HcommitIndex" ∷ ⌜ sint.nat commitIndex = length log ⌝ ∗
      "Hctx" ∷ req.(raftpb.Message.Context') ↦*{dq} read_req_ctx ∗
      "#Hread_ctx" ∷ is_read_req_ctx γ read_req_ctx Ψ
  }}}
    r @! (go.PointerType raft.readOnly) @! "addRequest" #commitIndex #req
  {{{ RET #(); own_readOnly γ r term }}}.
Proof.
  wp_start as "@". wp_auto. iNamed "Hown".
  wp_auto.
  wp_alloc req_ptr as "req".
  wp_auto.
  wp_apply wp_slice_literal.
  { iIntros. wp_auto. iFrame. }
  iIntros "% sl".
  replace (sint.nat (W64 0)) with (O) by done.
  rewrite /go.array_literal_size /= /Z.max /= /Z.add /=.
  wp_auto.
  wp_apply (wp_slice_append with "[$unconfirmedReads_cap $unconfirmedReads $sl]").
  iIntros "% (? & ? & ?)". iApply wp_fupd. wp_auto_lc 1.
  iApply "HΦ". iFrame "r". iFrame. simpl.
  iSplitR; first done.
  iFrame "#".
  iSelect (£ 1)%I (fun H => iRename H into "Hlc").
  iMod (try_read with "[Hcom Hlc]") as (?) "(#Hstale & Hcom & #Hmaybe_read)".
  { iNamed "Hread_ctx". iFrame "∗#". word. }
  iMod (own_heartbeat_auth_new stale_ids with "Hhb●") as "[Hhb● #Hhb]".
  { admit. } (* TODO: overflow of incrementing value. *)
  rewrite length_app.
  iPersist "req".
  iPersist "Hctx".
  iSplitR "Hhb●".
  {
    iFrame.
    iIntros "!# !# * %Hlookup".
    rewrite lookup_app in Hlookup.
    destruct (unconfirmedReads !! i) eqn:Hlookup_old.
    { simplify_eq. iApply "HunconfirmedReads". done. }
    rewrite list_lookup_singleton_Some in Hlookup.
    destruct Hlookup as [Hi ?]. subst.
    iFrame "req Hctx". iFrame "#". simpl.
    iExists _; iSplitR; first done.
    iSplit.
    - iExactEq "Hhb". f_equal. f_equal.
      apply lookup_ge_None_1 in Hlookup_old.
      word.
    - iDestruct "Hmaybe_read" as "[Hread|%]".
      2:{ by iLeft. }
      iRight.
      rewrite /is_read_index.
      replace (sint.nat (W64 (length log))) with (sint.nat commitIndex) by word.
      iFrame "#".
  }
  {
    rewrite /=. iModIntro. rewrite /named.
    iExactEq "Hhb●". f_equal. word.
  }
Admitted. (* NOTE: admit for overflow of incrementing value. *)

Lemma wp_readOnly_recvAck γ r term (from : w64) (ctx_sl : slice.t) (v : w64) :
  {{{ is_pkg_init raft ∗
      "Hown" ∷ own_readOnly γ r term ∗
      "Hctx" ∷ ctx_sl ↦* (u64_le v) ∗
      "#Hack" ∷ is_heartbeat_ack γ from term (u64_le v)
  }}}
    r @! (go.PointerType raft.readOnly) @! "recvAck" #from #ctx_sl
  {{{ RET #(); own_readOnly γ r term }}}.
Proof.
  wp_start as "@". iNamed "Hown".
  wp_auto.
  wp_if_destruct.
  { admit. } (* TODO handle empty byte slices *)
  wp_apply (wp_map_lookup1 with "Hacks") as "Hacks".
  wp_method_call. wp_auto.
  iAssert (global_addr binary.LittleEndian ↦□ binary.littleEndian.mk)%I with "[]" as "#H".
  { admit. } (* TODO add spec for the global variable assuming only is_pkg_init for binary. *)
  wp_auto.
  wp_apply (wp_littleEndian_Uint64 with "[Hctx]") as "Hctx".
  2:{ erewrite app_nil_r. iFrame. }
  { rewrite u64_le_length. done. }
  rewrite u64_le_to_word.
  wp_apply wp_max2_uint64.
  wp_apply (wp_map_insert with "Hacks") as "Hacks".
  iApply "HΦ".
  iExists _, _, _. iFrame "∗#%".
  iIntros "!# * %Hlookup".
  rewrite lookup_insert in Hlookup.
  destruct decide in Hlookup; subst.
  - simplify_eq. destruct lookup eqn:Hlookup.
    + simpl. destruct decide.
      * iApply "Hacks_wits". done.
      * iFrame "#".
    + simpl. rewrite -> decide_False; last word.
      iFrame "#".
  - iApply "Hacks_wits". done.
Admitted.

Lemma wp_readOnly_AckedIndex γ r term (voterId : w64) :
  {{{ is_pkg_init raft ∗
      "Hown" ∷ own_readOnly γ r term
  }}}
    r @! (go.PointerType raft.readOnly) @! "AckedIndex" #voterId
  {{{ (returnedIndex : w64) (found : bool), RET (#returnedIndex, #found);
      own_readOnly γ r term ∗
      if found then is_heartbeat_ack γ voterId term (u64_le returnedIndex) else True
  }}}.
Proof.
  wp_start as "@". iNamed "Hown". wp_auto.
  wp_apply (wp_map_lookup2 with "Hacks") as "Hacks".
  wp_end. iSplitL.
  { iFrame "∗#%". }
  destruct lookup eqn:Hlookup; simpl.
  - iApply "Hacks_wits". done.
  - done.
Qed.

(* TODO: ghost lemma showing that a quorum of heartbeat responses for a single
   hb_ctx means the stale set cannot be a quorum. *)

(* TODO: write axiom for CommittedIndex; given any "AckedIndexer" (which has a
   pure gmap w64 w64 associated with it), the returned `c` is s.t. there
   exists a quorum with acks at least `c` in the gmap. *)

(* TODO: maintain that the stale sets for already-sent HBs are smaller than the
   new stale set created. I.e. a nested sequence of set inclusions for all the
   unconfirmedReads. *)

Lemma wp_readOnly_maybeAdvance γ r term (c : quorum.JointConfig.t) m0 (voters : gmap w64 ()) :
  {{{ is_pkg_init raft ∗
      "Hown" ∷ own_readOnly γ r term ∗
      (* The config c is simple (not joint): first component is voters, second is empty. *)
      "%Hc" ∷ ⌜ array.arr c = [m0; map.nil] ⌝ ∗
      "Hm0" ∷ m0 ↦$ voters ∗
      "%Hvoters_cfg" ∷ ⌜ dom voters = cfg ⌝
  }}}
    r @! (go.PointerType raft.readOnly) @! "maybeAdvance" #c
  {{{ (rs : slice.t) (reads : list loc), RET #rs;
      own_readOnly γ r term ∗
      m0 ↦$ voters ∗
      rs ↦* reads ∗
      (* Every returned read request has a valid read index witness. *)
      □(∀ i rp, ⌜ reads !! i = Some rp ⌝ →
                ∃ read_req_ctx index Φ,
                  is_readIndexRequest γ rp read_req_ctx index ∗
                  is_read_req_ctx γ read_req_ctx Φ ∗
                  is_read_index γ index Φ)
  }}}.
Proof.
  wp_start as "@". iNamed "Hown". wp_auto.
Qed.

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
  iNamed "Hrf".
Admitted.

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

End proof.
