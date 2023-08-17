From Perennial.program_proof.rsm Require Import spaxos_prelude.
  
(* TODO: move this out to spaxos_repr.v once stable. *)
Section repr.
Context `{!heapGS Σ, !spaxos_ghostG Σ}.

(*@ type Paxos struct {                                                     @*)
(*@     // Mutex protecting all but @peers.                                 @*)
(*@     mu      *sync.Mutex                                                 @*)
(*@     // Term this paxos instance is currently in.                        @*)
(*@     termc   uint64                                                      @*)
(*@     // Term in which the currently accepted proposal is made.           @*)
(*@     termp   uint64                                                      @*)
(*@     // Content of the currently accepted proposal.                      @*)
(*@     decree  string                                                      @*)
(*@     // Have we learned the consensus?                                   @*)
(*@     learned bool                                                        @*)
(*@     // Other paxos instances. Eventually should be just addresses.      @*)
(*@     peers   []*Paxos                                                    @*)
(*@ }                                                                       @*)
Definition own_paxos (paxos : loc) (nid : nat) γ : iProp Σ :=
  ∃ (termc : u64) (termp : u64) (decree : string) (learned : bool)
    (blt : ballot),
    (*@ Res: termc uint64                                                       @*)
    "Htermc" ∷ paxos ↦[Paxos :: "termc"] #termc ∗
    (*@ Res: termp uint64                                                       @*)
    "Htermp" ∷ paxos ↦[Paxos :: "termp"] #termp ∗
    (*@ Res: decree string                                                      @*)
    "Hdecree" ∷ paxos ↦[Paxos :: "decree"] #(LitString decree) ∗
    (*@ Res: learned bool                                                       @*)
    "Hlearned" ∷ paxos ↦[Paxos :: "learned"] #learned ∗
    (*@ Res: ballot ghost                                                       @*)
    "Hballot" ∷ own_ballot γ nid blt ∗
    (*@ Res: termc uint64 / ballot ghost                                        @*)
    "%HballotLen" ∷ ⌜length blt = int.nat termc⌝ ∗
    (*@ Res: termp uint64 / ballot ghost                                        @*)
    "%HlastAcpt" ∷ True.

Definition is_paxos (paxos : loc) (nid : nat) γ : iProp Σ :=
  ∃ (mu : loc) (peers : loc),
    (*@ Res: mu *sync.Mutex                                                     @*)
    "#Hmu"   ∷ readonly (paxos ↦[Paxos :: "mu"] #mu) ∗
    "#Hlock" ∷ is_lock spaxosN #mu (own_paxos paxos nid γ) ∗
    (*@ Res: peers []*Paxos                                                     @*)
    "#Hpeers" ∷ readonly (paxos ↦[Paxos :: "peers"] #peers).

End repr.
(* TODO: move this out to spaxos_repr.v once stable. *)

(* TODO: move them out to their own files once stable. *)
Section temp.
Context `{!heapGS Σ, !spaxos_ghostG Σ}.

Definition is_proposed_decree γ v : iProp Σ :=
  ∃ n, is_proposal γ n v.

Theorem wp_Paxos__Outcome (px : loc) nid γ :
  is_paxos px nid γ -∗
  {{{ True }}}
    Paxos__Outcome #px
  {{{ (v : string) (ok : bool), RET (#(LitString v), #ok);
      (* [is_chosen] encodes safety, [is_proposed_decree] encodes non-triviality. *)
      if ok then is_chosen γ v ∗ is_proposed_decree γ v else True
  }}}.
Proof.
  (*@ func (px *Paxos) Outcome() (string, bool) {                             @*)
  (*@     px.mu.Lock()                                                        @*)
  (*@                                                                         @*)
  (*@     if px.isLearned() {                                                 @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return px.getDecree(), true                                     @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  (*@     px.mu.Unlock()                                                      @*)
  (*@     return "", false                                                    @*)
  (*@ }                                                                       @*)
Admitted.

Theorem wp_Paxos__proceedToNewTerm (px : loc) nid γ :
  {{{ own_paxos px nid γ }}}
    Paxos__proceedToNewTerm #px
  {{{ (term : u64), RET #term; own_paxos px nid γ }}}.
Proof.
  (*@ func (px *Paxos) proceedToNewTerm() uint64 {                            @*)
  (*@     // TODO                                                             @*)
  (*@     return 0                                                            @*)
  (*@ }                                                                       @*)
Admitted.

Definition major_prepares (term : u64) (decree : string) : iProp Σ.
Admitted.

Theorem wp_Paxos__prepareAll (px : loc) (term : u64) nid γ :
  {{{ own_paxos px nid γ }}}
    Paxos__prepareAll #px #term
  {{{ (term : u64) (decree : string) (ok : bool), RET (#term, #(LitString decree), #ok);
      own_paxos px nid γ ∗
      if ok then major_prepares term decree else True
  }}}.
Proof.
  (*@ func (px *Paxos) prepareAll(term uint64) (uint64, string, bool) {       @*)
  (*@     var termLargest uint64                                              @*)
  (*@     var decreeLargest string                                            @*)
  (*@     var nPrepared uint64                                                @*)
  (*@     for _, peer := range(px.peers) {                                    @*)
  (*@         // Send each node a prepare message.                            @*)
  (*@         termPeer, decreePeer, ok := peer.prepare(term)                  @*)
  (*@         if ok {                                                         @*)
  (*@             nPrepared++                                                 @*)
  (*@             if termPeer > termLargest {                                 @*)
  (*@                 // Update the largest-term proposal we've seen.         @*)
  (*@                 termLargest = termPeer                                  @*)
  (*@                 decreeLargest = decreePeer                              @*)
  (*@             }                                                           @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  (*@     // Did not reach a majority.                                        @*)
  (*@     if !px.major(nPrepared) {                                           @*)
  (*@         return 0, "", false                                             @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  (*@     return termLargest, decreeLargest, true                             @*)
  (*@ }                                                                       @*)
Admitted.


End temp.
(* TODO: move them out to their own files once stable. *)

Section prog.
Context `{!heapGS Σ, !spaxos_ghostG Σ}.

Theorem wp_Paxos__Propose (px : loc) (v : string) nid γ :
  is_paxos px nid γ -∗
  {{{ True }}}
    Paxos__Propose #px #(LitString v)
  {{{ (ok : bool), RET #ok; if ok then is_proposed_decree γ v else True }}}.
Proof.
  iIntros "#Hpaxos !>" (Φ) "_ HΦ".
  iNamed "Hpaxos".
  wp_call.

  (*@ func (px *Paxos) Propose(v string) bool {                               @*)
  (*@     px.mu.Lock()                                                        @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HpaxosOwn]".
  wp_pures.
  
  (*@     // Proceed to a new term exclusively owned by this paxos node.      @*)
  (*@     // NB: Raft does not exclusively own a term until the first phase goes thru. @*)
  (*@     term := px.proceedToNewTerm()                                       @*)
  (*@                                                                         @*)
  wp_apply (wp_Paxos__proceedToNewTerm with "HpaxosOwn").
  iIntros (term) "HpaxosOwn".
  wp_pures.
  (* TODO: We need invariant to know [term] is free when we make our proposal after phase 1. *)
  
  (*@     // Phase 1.                                                         @*)
  (*@     // Goals of this phase is to get a quorum of nodes:                 @*)
  (*@     // (1) promise not to accept any proposal with term below @term, and @*)
  (*@     // (2) find out the largest proposal (below @term) accepted by the quorum. @*)
  (*@     termLargest, decreeLargest, prepared := px.prepareAll(term)         @*)
  (*@                                                                         @*)
  wp_apply (wp_Paxos__prepareAll with "HpaxosOwn").
  iIntros (termLargest decreeLargest prepared) "[HpaxosOwn Hprepares]".
  (* TODO: [major_prepares] along with global inv should allow us to deduce [valid_proposal]. *)
  wp_pures.
  
  (*@     if !prepared {                                                      @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         // Case ``not proposed''.                                       @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct.
  { admit. }
  
  (*@     // If @termLargest is not set (meaning no node in the quorum has accepted @*)
  (*@     // any proposal yet), we can propose our value @v.                  @*)
  (*@     var decree string                                                   @*)
  (*@     var helping bool                                                    @*)
  (*@                                                                         @*)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (decree) "Hdecree".
  wp_pures.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (helping) "Hhelping".
  wp_pures.

  (*@     if termLargest == 0 {                                               @*)
  (*@         // We're the ``initiating'' thread.                             @*)
  (*@         decree = v                                                      @*)
  (*@         helping = false                                                 @*)
  (*@     } else {                                                            @*)
  (*@         // We're the ``helping'' thread.                                @*)
  (*@         decree = decreeLargest                                          @*)
  (*@         helping = true                                                  @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_apply (wp_If_join_evar with "[Hdecree Hhelping]").
  { iIntros (b Eqb).
    case_bool_decide.
    { wp_if_true. admit. }
    { wp_if_false. admit. }
  }
  iIntros "H".
  wp_pures.

  (*@     // Phase 2.                                                         @*)
  (*@     // Goal of this phase is to get a quorum of nodes accepting our proposal. @*)
  (*@     accepted := px.acceptAll(term, decree)                              @*)
  (*@                                                                         @*)
  
  (*@     if !accepted {                                                      @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         // Case ``not proposed'' or case ``proposed'', depending on @helping. @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  
  (*@     // If @accepted is true, we know @decree is chosen either the first time, @*)
  (*@     // or has already been chosen earlier. If it's the first time, we simply @*)
  (*@     // perform a ghost update on consensus; if it's been chosen earlier, we @*)
  (*@     // apply the top-level consistency theorem to deduce the decree chosen here @*)
  (*@     // (i.e., @decree) is equal to the one chosen eariler.              @*)
  (*@                                                                         @*)
  
  (*@     // Phase 3.                                                         @*)
  (*@     // Goal of this phase is to broadcast the consensus to other nodes. @*)
  (*@     px.learnAll(term, decree)                                           @*)
  (*@                                                                         @*)
  
  (*@     px.mu.Unlock()                                                      @*)
  (*@                                                                         @*)
  
  (*@     // Return false since we're merely helping early proposal go through, rather @*)
  (*@     // than proposing our own value @v.                                 @*)
  (*@     if helping {                                                        @*)
  (*@         // Case ``not proposed''.                                       @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  
  (*@     // Case ``chosen''.                                                 @*)
  (*@     return true                                                         @*)
  (*@                                                                         @*)
  
  (*@     // Wait until consensus is reached.                                 @*)
  (*@     // NB: Deferred consensus don't need this.                          @*)
  (*@     // for !px.isLearned() { }                                          @*)
  (*@ }                                                                       @*)
Admitted.

End prog.
