From Perennial.program_proof.rsm Require Import spaxos_prelude.

(* TODO: move this out to spaxos_iris_inv.v once stable. *)
Section inv.
Context `{!heapGS Σ, !spaxos_ghostG Σ}.

Definition spaxosN := nroot .@ "spaxos".

Definition spaxos_inv γ : iProp Σ :=
  ∃ c bs ps,
    "Hc"    ∷ own_consensus γ c ∗
    "Hbs"   ∷ own_ballots γ bs ∗
    "Hps"   ∷ own_proposals γ ps ∗
    "%Hvc"  ∷ ⌜valid_consensus c bs ps⌝ ∗
    "%Hvbs" ∷ ⌜valid_ballots bs ps⌝ ∗
    "%Hvps" ∷ ⌜valid_proposals bs ps⌝.

#[global]
Instance spaxos_inv_timeless γ :
  Timeless (spaxos_inv γ).
Admitted.

Definition know_sapxos_inv γ : iProp Σ :=
  inv spaxosN (spaxos_inv γ).

End inv.

#[global]
Hint Extern 1 (environments.envs_entails _ (spaxos_inv _)) => unfold spaxos_inv : core.
(* TODO: move this out to spaxos_iris_inv.v once stable. *)

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
    "#Hpeers" ∷ readonly (paxos ↦[Paxos :: "peers"] #peers) ∗
    (*@ Res: ginv                                                               @*)
    "#Hinv" ∷ know_sapxos_inv γ.

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
      if ok then is_chosen_consensus γ v ∗ is_proposed_decree γ v else True
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

Definition quorum_prepares (γ : spaxos_names) (term : u64) (decree : string) : iProp Σ.
Admitted.

#[global]
Instance quorum_prepares_persistent γ term decree :
  Persistent (quorum_prepares γ term decree).
Admitted.

Theorem wp_Paxos__prepareAll (px : loc) (term : u64) nid γ :
  {{{ own_paxos px nid γ }}}
    Paxos__prepareAll #px #term
  {{{ (term : u64) (decree : string) (ok : bool), RET (#term, #(LitString decree), #ok);
      own_paxos px nid γ ∗
      if ok then quorum_prepares γ term decree else True
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

Definition quorum_accepts (γ : spaxos_names) (term : u64) : iProp Σ.
Admitted.

#[global]
Instance quorum_accepts_persistent γ term :
  Persistent (quorum_accepts γ term).
Admitted.

Theorem wp_Paxos__acceptAll (px : loc) (term : u64) (decree : string) nid γ :
  is_proposal γ (int.nat term) decree -∗
  {{{ own_paxos px nid γ }}}
    Paxos__acceptAll #px #term #(LitString decree)
  {{{ (ok : bool), RET #ok; own_paxos px nid γ ∗ if ok then quorum_accepts γ term else True }}}.
Proof.
  (*@ func (px *Paxos) acceptAll(term uint64, decree string) bool {           @*)
  (*@     var nAccepted uint64 = 0                                            @*)
  (*@     for _, peer := range(px.peers) {                                    @*)
  (*@         ok := peer.accept(term, decree)                                 @*)
  (*@         if ok {                                                         @*)
  (*@             nAccepted++                                                 @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  (*@     return px.major(nAccepted)                                          @*)
  (*@ }                                                                       @*)
Admitted.

Theorem wp_Paxos__learnAll (px : loc) (term : u64) (decree : string) nid γ :
  is_chosen_consensus γ decree -∗
  {{{ own_paxos px nid γ }}}
    Paxos__learnAll #px #term #(LitString decree)
  {{{ RET #(); own_paxos px nid γ }}}.
Proof.
  (*@ func (px *Paxos) learnAll(term uint64, decree string) {                 @*)
  (*@     for _, peer := range(px.peers) {                                    @*)
  (*@         peer.learn(term, decree)                                        @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)
Admitted.


Lemma ite_apply (A B : Type) (b : bool) (f : A -> B) x y :
  (if b then f x else f y) = f (if b then x else y).
Proof. destruct b; done. Qed.

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
  (* TODO: [quorum_prepares] along with global inv should allow us to deduce [valid_proposal]. *)
  wp_pures.
  
  (*@     if !prepared {                                                      @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[$Hlock $Hlocked $HpaxosOwn]").
    wp_pures.
    by iApply "HΦ".
  }
  iDestruct "Hprepares" as "#Hprepares".
  
  (*@     // If @termLargest is not set (meaning no node in the quorum has accepted @*)
  (*@     // any proposal yet), we can propose our value @v.                  @*)
  (*@     var decree string                                                   @*)
  (*@     var helping bool                                                    @*)
  (*@                                                                         @*)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (decreeRef) "Hdecree".
  wp_pures.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (helpingRef) "Hhelping".
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
    - wp_if_true.
      do 2 wp_store.
      iModIntro.
      iSplit; first done.
      replace (LitString v) with
        (if b then (LitString v) else (LitString decreeLargest)) by by rewrite Eqb.
      replace #false with #(if b then false else true) by by rewrite Eqb.
      iNamedAccu.
    - wp_if_false.
      do 2 wp_store.
      iModIntro.
      iSplit; first done.
      rewrite Eqb.
      by iFrame.
  }
  iIntros "Hdh".
  iNamed "Hdh".
  wp_pures.

  (* Push [LitString] and [LitBool] our for [Hdecree] and [Hhelping], respectively. *)
  do 2 rewrite ite_apply.

  (*@     // Now that we have decided what to propose (i.e., @decree), we can perform @*)
  (*@     // a ghost update on [proposals]. To do so in an invariant-preserving way, @*)
  (*@     // we need to know two things:                                      @*)
  (*@     // 1. @term has not been proposed, and                              @*)
  (*@     // 2. the proposal we're making, (@term, @decree), is a valid one.  @*)
  (*@     // See [vp_inv_propose] for detail.                                 @*)
  (*@                                                                         @*)
  iApply fupd_wp.
  iInv "Hinv" as ">HinvO" "HinvC".
  iNamed "HinvO".
  assert (Hfresh : ps !! (int.nat term) = None).
  { (* TODO: prove this using inv about [termc] and [proposals]. *) admit. }
  set decree := (if (bool_decide _) then v else _).
  assert (Hvalid : valid_proposal bs ps (int.nat term) decree).
  { (* TODO: prove this using [quorum_prepares]. *) admit. }
  iMod (proposals_insert _ _ decree with "Hps") as "[Hps #Hp]"; first apply Hfresh.
  assert (Hnz : (int.nat term) ≠ O).
  { admit. }
  pose proof (vp_inv_propose Hfresh Hnz Hvalid Hvps) as Hvps'.
  pose proof (vb_inv_propose (int.nat term) decree Hvbs) as Hvbs'.
  pose proof (vc_inv_propose (int.nat term) decree Hvc) as Hvc'.
  iMod ("HinvC" with "[Hc Hbs Hps]") as "_"; first by eauto 10 with iFrame.
  iModIntro.

  (*@     // Phase 2.                                                         @*)
  (*@     // Goal of this phase is to get a quorum of nodes accepting our proposal. @*)
  (*@     accepted := px.acceptAll(term, decree)                              @*)
  (*@                                                                         @*)
  wp_load.
  wp_apply (wp_Paxos__acceptAll with "Hp HpaxosOwn").
  iIntros (accepted) "[HpaxosOwn Haccepts]".
  wp_pures.
  
  (*@     if !accepted {                                                      @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return !helping                                                 @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[$Hlock $Hlocked $HpaxosOwn]").
    wp_pures.
    wp_load.
    unfold is_proposed_decree.
    case_bool_decide; wp_pures; iApply "HΦ"; [by eauto | done].
  }
  iDestruct "Haccepts" as "#Haccepts".
  
  (*@     // If @accepted is true, we know @decree is chosen either the first time, @*)
  (*@     // or has already been chosen earlier. If it's the first time, we simply @*)
  (*@     // perform a ghost update on consensus; if it's been chosen earlier, we @*)
  (*@     // apply the top-level consistency theorem to deduce the decree chosen here @*)
  (*@     // (i.e., @decree) is equal to the one chosen eariler.              @*)
  (*@                                                                         @*)
  iApply fupd_wp.
  iInv "Hinv" as ">HinvO" "HinvC".
  clear c bs ps Hvc Hvc' Hvbs Hvbs' Hvps Hvps' Hfresh Hvalid.
  iNamed "HinvO".
  assert (Hchosen : chosen bs ps decree).
  { (* TODO: prove this using [Haccepts]. *) admit. }
  iAssert (|==> own_consensus γ (Chosen decree))%I with "[Hc]" as "Hc".
  { destruct c as [decree' |] eqn:Ec.
    - (* Case [Chosen decree']. *)
      unfold valid_consensus in Hvc.
      pose proof (vb_vp_impl_consistency Hvbs Hvps) as Hconsistency.
      rewrite (Hconsistency _ _ Hvc Hchosen).
      by iFrame.
    - (* Case [Free]. *)
      iMod (consensus_update decree with "Hc") as "Hc".
      by iFrame.
  }
  iMod "Hc".
  iDestruct (consensus_witness with "Hc") as "#Hconsensus".
  iMod ("HinvC" with "[Hc Hbs Hps]") as "_"; first by eauto 10 with iFrame.
  iModIntro.

  (*@     // Phase 3.                                                         @*)
  (*@     // Goal of this phase is to broadcast the consensus to other nodes. @*)
  (*@     px.learnAll(term, decree)                                           @*)
  (*@                                                                         @*)
  wp_load.
  wp_apply (wp_Paxos__learnAll with "Hconsensus HpaxosOwn").
  iIntros "HpaxosOwn".
  wp_pures.
  
  (*@     px.mu.Unlock()                                                      @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (release_spec with "[$Hlock $Hlocked $HpaxosOwn]").
  wp_pures.

  (*@     // If @helping is true, return false since we're merely helping an early @*)
  (*@     // proposal go through, rather than proposing our own value @v.     @*)
  (*@     return !helping                                                     @*)
  (*@                                                                         @*)
  wp_load.
  unfold is_proposed_decree.
  case_bool_decide; wp_pures; iApply "HΦ"; [by eauto | done].
  
  (*@     // Wait until consensus is reached.                                 @*)
  (*@     // NB: Deferred consensus don't need this.                          @*)
  (*@     // for !px.isLearned() { }                                          @*)
  (*@ }                                                                       @*)
Admitted.

End prog.
