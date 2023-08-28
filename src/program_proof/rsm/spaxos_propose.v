From Perennial.program_proof.rsm Require Import spaxos_prelude.

(* TODO: move this out to spaxos_iris_inv.v once stable. *)
Section inv.
Context `{!heapGS Σ, !spaxos_ghostG Σ}.

Definition spaxosN := nroot .@ "spaxos".

Definition is_cluster (γ : spaxos_names) (c : gset Z) : iProp Σ.
Admitted.

#[global]
Instance is_cluster_persistent γ c :
  Persistent (is_cluster γ c).
Admitted.

Lemma cluster_eq {γ s1 s2} :
  is_cluster γ s1 -∗
  is_cluster γ s2 -∗
  ⌜s1 = s2⌝.
Admitted.

Definition num_nodes : Z := 16.

Definition is_term_of_node (x : Z) (n : nat) :=
  n `mod` num_nodes = x.

(* TODO: make this a typeclass. *)
Lemma is_term_of_node_partitioned x1 x2 n :
  x1 ≠ x2 -> is_term_of_node x1 n -> not (is_term_of_node x2 n).
Proof. unfold is_term_of_node. lia. Qed.

Definition spaxos_inv γ : iProp Σ :=
  ∃ c bs ps ts,
    "Hc"     ∷ own_consensus γ c ∗
    "Hbs"    ∷ own_ballots γ bs ∗
    "Hps"    ∷ own_proposals γ ps ∗
    "Hts"    ∷ own_terms γ ts ∗
    "#Hclst" ∷ is_cluster γ (dom bs) ∗
    "%Hvc"   ∷ ⌜valid_consensus c bs ps⌝ ∗
    "%Hvbs"  ∷ ⌜valid_ballots bs ps⌝ ∗
    "%Hvps"  ∷ ⌜valid_proposals bs ps⌝ ∗
    "%Hvts"  ∷ ⌜valid_terms is_term_of_node ps ts⌝.

#[global]
Instance spaxos_inv_timeless γ :
  Timeless (spaxos_inv γ).
Admitted.

Definition know_sapxos_inv γ : iProp Σ :=
  inv spaxosN (spaxos_inv γ).

End inv.

#[export]
Hint Extern 1 (environments.envs_entails _ (spaxos_inv _)) => unfold spaxos_inv : core.
#[export]
Hint Extern 1 (environments.envs_entails _ (is_cluster _ (dom (alter _ _ _)))) => rewrite dom_alter_L : core.
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
Definition own_paxos (paxos : loc) (nid : Z) γ : iProp Σ :=
  ∃ (termc termp : u64) (decree : string) (learned : bool) (blt : ballot),
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
    (*@ Res: termmap ghost                                                      @*)
    "Hterm" ∷ own_term γ nid (int.nat termc) ∗
    (*@ Res: termc uint64 / ballot ghost                                        @*)
    "%HballotLen" ∷ ⌜length blt = int.nat termc⌝ ∗
    (*@ Res: termp uint64 / ballot ghost                                        @*)
    "%HlastAcpt" ∷ True.

Definition is_paxos_node (paxos : loc) (nid : Z) γ : iProp Σ :=
  ∃ (mu : loc),
    (*@ Res: mu *sync.Mutex                                                     @*)
    "#Hmu"   ∷ readonly (paxos ↦[Paxos :: "mu"] #mu) ∗
    "#Hlock" ∷ is_lock spaxosN #mu (own_paxos paxos nid γ).

Definition is_paxos_comm (paxos : loc) (clst : gset Z) γ : iProp Σ :=
  ∃ (peers : Slice.t) (peersL : list loc),
    (*@ Res: peers []*Paxos                                                     @*)
    "#Hpeers"  ∷ readonly (paxos ↦[Paxos :: "peers"] (to_val peers)) ∗
    "#HpeersL" ∷ readonly (own_slice_small peers ptrT 1 peersL) ∗
    (* For now we're using list index as node id, but might need another indirection later. *)
    "#Hpaxos"  ∷ ([∗ list] i ↦ px ∈ peersL, is_paxos_node px (Z.of_nat i) γ) ∗
    (* This looks ugly; think if there's better way to define this. *)
    "%Hclsteq" ∷ ⌜clst = list_to_set (Z.of_nat <$> (seq O (length peersL)))⌝.

Definition is_paxos (paxos : loc) (nid : Z) γ : iProp Σ :=
  ∃ (clst : gset Z),
    "#Hcluster" ∷ is_cluster γ clst ∗
    "#Hnode"    ∷ is_paxos_node paxos nid γ ∗
    "#Hcomm"    ∷ is_paxos_comm paxos clst γ ∗
    "#Hinv"     ∷ know_sapxos_inv γ.

End repr.

#[export]
Hint Extern 1 (environments.envs_entails _ (own_paxos _ _ _)) => unfold own_paxos : core.
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

Definition P_Paxos__advance (px : loc) (termc : u64) nid γ: iProp Σ :=
  "Htermc" ∷ px ↦[Paxos :: "termc"] #termc ∗
  "Hterm"  ∷ own_term γ nid (int.nat termc).

Definition Q_Paxos__advance (px : loc) (termc termold : u64) nid γ: iProp Σ :=
  "Htermc"   ∷ px ↦[Paxos :: "termc"] #termc ∗
  "Hterm"    ∷ own_term γ nid (int.nat termold) ∗
  "%HtermLt" ∷ ⌜(int.nat termold < int.nat termc)%nat⌝ ∗
  "%Hnode"   ∷ ⌜is_term_of_node nid (int.nat termc)⌝.

Theorem wp_Paxos__proceedToNewTerm px termc nid γ :
  {{{ P_Paxos__advance px termc nid γ }}}
    Paxos__proceedToNewTerm #px
  {{{ (term : u64), RET #term; Q_Paxos__advance px term termc nid γ }}}.
Proof.
  (*@ func (px *Paxos) proceedToNewTerm() uint64 {                            @*)
  (*@     // TODO                                                             @*)
  (*@     return 0                                                            @*)
  (*@ }                                                                       @*)
Admitted.

Definition quorum_prepares
  (term termp : u64) (decree : string) (clst : gset Z) (γ : spaxos_names) : iProp Σ :=
  ∃ (bsqlb : gmap Z ballot),
    "#Hlbs"      ∷ ([∗ map] x ↦ l ∈ bsqlb, is_ballot_lb γ x l) ∗
    "#Hproposal" ∷ (if decide (int.nat termp = O) then True else is_proposal γ (int.nat termp) decree) ∗
    "%Hquorum"   ∷ ⌜quorum clst (dom bsqlb)⌝ ∗
    "%Hlen"      ∷ ⌜map_Forall (λ _ l, ((int.nat term) ≤ length l)%nat) bsqlb⌝ ∗
    "%Hlargest"  ∷ ⌜latest_before_quorum (int.nat term) bsqlb = int.nat termp⌝.

#[global]
Instance quorum_prepares_persistent term termp decree clst γ :
  Persistent (quorum_prepares term termp decree clst γ).
Proof. unfold quorum_prepares. case_decide; apply _. Qed.

Theorem wp_Paxos__prepareAll (px : loc) (term : u64) clst γ :
  is_paxos_comm px clst γ -∗
  {{{ True }}}
    Paxos__prepareAll #px #term
  {{{ (termp : u64) (decree : string) (ok : bool), RET (#termp, #(LitString decree), #ok);
      if ok then quorum_prepares term termp decree clst γ else True
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

Definition quorum_accepts (term : u64) (clst : gset Z) (γ : spaxos_names) : iProp Σ :=
  ∃ (bsqlb : gmap Z ballot),
    "#Hlbs"     ∷ ([∗ map] x ↦ l ∈ bsqlb, is_ballot_lb γ x l) ∗
    "%Hquorum"  ∷ ⌜quorum clst (dom bsqlb)⌝ ∗
    "%Haccin"   ∷ ⌜map_Forall (λ _ l, accepted_in l (int.nat term)) bsqlb⌝.

#[global]
Instance quorum_accepts_persistent term clst γ :
  Persistent (quorum_accepts γ term clst).
Proof. apply _. Qed.

Theorem wp_Paxos__acceptAll (px : loc) (term : u64) (decree : string) clst γ :
  is_paxos_comm px clst γ -∗
  is_proposal γ (int.nat term) decree -∗
  {{{ True }}}
    Paxos__acceptAll #px #term #(LitString decree)
  {{{ (ok : bool), RET #ok; if ok then quorum_accepts term clst γ else True }}}.
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

Theorem wp_Paxos__learnAll (px : loc) (term : u64) (decree : string) clst γ :
  is_paxos_comm px clst γ -∗
  is_chosen_consensus γ decree -∗
  {{{ True }}}
    Paxos__learnAll #px #term #(LitString decree)
  {{{ RET #(); True }}}.
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

Section fin_maps.
Context `{FinMap K M}.

Lemma map_intersection_subseteq {A : Type} (m1 m2 : M A) :
  m1 ∩ m2 ⊆ m1.
Proof using EqDecision0 H H0 H1 H2 H3 H4 H5 H6 K M.
  rewrite !map_subseteq_spec. intros i x Hm.
  rewrite lookup_intersection_Some in Hm.
  by destruct Hm as [? _].
Qed.

Lemma lookup_insert_alter {A : Type} (f : A -> A) (m : M A) (i : K) (x : A) :
  m !! i = Some x ->
  <[i := f x]> m = alter f i m.
Proof using EqDecision0 H H0 H1 H2 H3 H4 H5 H6 K M.
  intros Hmi.
  by rewrite -alter_insert insert_id.
Qed.

End fin_maps.

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
  iNamed "Hnode".
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
  iNamed "HpaxosOwn".
  wp_apply (wp_Paxos__proceedToNewTerm with "[$Htermc $Hterm]").
  iIntros (term) "Hpost".
  iNamed "Hpost".
  wp_pures.

  set blt' := extend false (int.nat term) blt.
  iAssert (|={⊤}=> own_ballot γ nid blt')%I with "[Hballot]" as "> Hballot".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (ballot_lookup with "Hballot Hbs") as %Hblt.
    iMod (ballot_update (extend false (int.nat term) blt) with "Hballot Hbs") as "[Hballot Hbs]".
    { apply extend_prefix. }
    rewrite lookup_insert_alter; last done.
    pose proof (vb_inv_prepare nid (int.nat term) Hvbs) as Hvbs'.
    pose proof (vp_inv_prepare nid (int.nat term) Hvps) as Hvps'.
    pose proof (vc_inv_prepare nid (int.nat term) Hvc) as Hvc'.
    by iMod ("HinvC" with "[Hc Hbs Hps Hts]") as "_"; first by eauto 15 with iFrame.
  }

  (*@     // Phase 1.                                                         @*)
  (*@     // Goals of this phase is to get a quorum of nodes:                 @*)
  (*@     // (1) promise not to accept any proposal with term below @term, and @*)
  (*@     // (2) find out the largest proposal (below @term) accepted by the quorum. @*)
  (*@     termLargest, decreeLargest, prepared := px.prepareAll(term)         @*)
  (*@                                                                         @*)
  wp_apply (wp_Paxos__prepareAll with "Hcomm").
  iIntros (termLargest decreeLargest prepared) "Hprepares".
  wp_pures.
  
  (*@     if !prepared {                                                      @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct.
  { wp_loadField.
    (* XXX: should not need below after relating term map to termp rather than termc. *)
    iApply fupd_wp.
    iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (term_lookup with "Hterm Hts") as %Htermc.
    assert (Hprev : gt_prev_term ts nid (int.nat term)).
    { exists (int.nat termc). split; [done | word]. }
    iMod (term_update (int.nat term) with "Hterm Hts") as "[Hterm Hts]".
    pose proof (vt_inv_advance Hprev Hvts) as Hvts'.
    iMod ("HinvC" with "[Hc Hbs Hps Hts]") as "_"; first by eauto 15 with iFrame.
    iModIntro.
    wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
    { do 5 iExists _. iFrame. iPureIntro. rewrite extend_length. lia. }
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
  iIntros (decreeRef) "HdecreeRef".
  wp_pures.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (helpingRef) "HhelpingRef".
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
  wp_apply (wp_If_join_evar with "[HdecreeRef HhelpingRef]").
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
  (* Push [LitString] and [LitBool] out for [Hdecree] and [Hhelping], respectively. *)
  do 2 rewrite ite_apply.

  (*@     // Now that we have decided what to propose (i.e., @decree), we can perform @*)
  (*@     // a ghost update on [proposals]. To do so in an invariant-preserving way, @*)
  (*@     // we need to know two things:                                      @*)
  (*@     // 1. @term has not been proposed, and                              @*)
  (*@     // 2. the proposal we're making, (@term, @decree), is a valid one.  @*)
  (*@     // See [vp_inv_propose] for detail.                                 @*)
  (*@                                                                         @*)
  assert (Hnz : (int.nat term) ≠ O) by lia.
  rename decree into decree_prev.
  set decree := (if (bool_decide _) then v else _).
  set R := (own_term γ nid (int.nat term) ∗ is_proposal γ (int.nat term) decree)%I.
  iAssert (|={⊤}=> R)%I with "[Hterm]" as "> [Hterm #Hp]".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (term_lookup with "Hterm Hts") as %Htermc.
    assert (Hprev : gt_prev_term ts nid (int.nat term)).
    { exists (int.nat termc). split; [done | word]. }
    pose proof (vt_impl_freshness Htermc HtermLt Hnode Hvts) as Hfresh.
    iAssert (⌜valid_proposal bs ps (int.nat term) decree⌝)%I as %Hvalid.
    { iNamed "Hprepares".
      iDestruct (ballots_prefix with "Hlbs Hbs") as "%Hprefix".
      iAssert (⌜if decide (int.nat termLargest = O)
               then True
               else ps !! (int.nat termLargest) = Some decreeLargest⌝)%I as "%Hatterm".
      { case_decide; [done | by iApply proposal_lookup]. }
      iDestruct (cluster_eq with "Hcluster Hclst") as "->".
      iPureIntro.
      set bsq := bs ∩ bsqlb.
      exists bsq.
      split; first by apply map_intersection_subseteq.
      split.
      { replace (dom bsq) with (dom bsqlb); first done.
        rewrite dom_intersection_L.
        destruct Hquorum as [? _].
        set_solver.
      }
      split.
      { intros x b Hxb.
        rewrite lookup_intersection_Some in Hxb.
        destruct Hxb as [Hb [blb Hblb]].
        specialize (Hprefix _ _ _ Hblb Hb).
        apply Hlen in Hblb.
        apply prefix_length in Hprefix.
        lia.
      }
      unfold equal_latest_proposal_or_free.
      rewrite (latest_before_quorum_eq _ _ bsqlb); last first.
      { unfold prefixes.
        intros x lb l Hlb Hl.
        rewrite lookup_intersection_Some in Hl.
        destruct Hl as [Hl _].
        by specialize (Hprefix _ _ _ Hlb Hl).
      }
      { done. }
      { replace (dom bsq) with (dom bsqlb); first done.
        rewrite dom_intersection_L.
        destruct Hquorum as [? _].
        set_solver.
      }
      case_decide as Hcase.
      - left. by rewrite Hcase in Hlargest.
      - right. rewrite Hlargest.
        subst decree.
        case_bool_decide as Hcontra; last done.
        clear -Hcase Hcontra.
        (* Set Printing Coercions. *)
        inversion Hcontra as [Hzero].
        rewrite Hzero in Hcase.
        unfold int.nat in Hcase.
        replace (int.Z _) with 0 in Hcase; word.
    }
    iMod (proposals_insert _ _ decree with "Hps") as "[Hps #Hp]"; first apply Hfresh.
    iMod (term_update (int.nat term) with "Hterm Hts") as "[Hterm Hts]".
    pose proof (vp_inv_propose Hfresh Hnz Hvalid Hvps) as Hvps'.
    pose proof (vb_inv_propose (int.nat term) decree Hvbs) as Hvbs'.
    pose proof (vc_inv_propose (int.nat term) decree Hvc) as Hvc'.
    pose proof (vt_inv_propose_advance decree Hprev Hnode Hvts) as Hvts'.
    iMod ("HinvC" with "[Hc Hbs Hps Hts]") as "_"; first by eauto 10 with iFrame.
    by iFrame.
  }
  clear R.

  (*@     // Phase 2.                                                         @*)
  (*@     // Goal of this phase is to get a quorum of nodes accepting our proposal. @*)
  (*@     accepted := px.acceptAll(term, decree)                              @*)
  (*@                                                                         @*)
  wp_load.
  wp_apply (wp_Paxos__acceptAll with "Hcomm Hp").
  iIntros (accepted) "Haccepts".
  wp_pures.
  
  (*@     if !accepted {                                                      @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return !helping                                                 @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[-HΦ HhelpingRef $Hlock $Hlocked]").
    { do 5 iExists _. iFrame. iPureIntro. rewrite extend_length. lia. }
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
  iAssert (|={⊤}=> is_chosen_consensus γ decree)%I as "> #Hconsensus".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iAssert (⌜chosen bs ps decree⌝)%I as %Hchosen.
    { iNamed "Haccepts".
      iDestruct (ballots_prefix with "Hlbs Hbs") as %Hprefix.
      iDestruct (proposal_lookup with "Hp Hps") as %Hatterm.
      iDestruct (cluster_eq with "Hcluster Hclst") as %->.
      iPureIntro.
      exists (int.nat term).
      split; first apply Hatterm.
      set bsq := bs ∩ bsqlb.
      exists bsq.
      split; first by apply map_intersection_subseteq.
      split.
      { replace (dom bsq) with (dom bsqlb); first done.
        rewrite dom_intersection_L.
        destruct Hquorum as [? _].
        set_solver.
      }
      intros x b Hxb.
      rewrite lookup_intersection_Some in Hxb.
      destruct Hxb as [Hb [blb Hblb]].
      specialize (Hprefix _ _ _ Hblb Hb).
      apply Haccin in Hblb.
      unfold accepted_in.
      split; last done.
      eapply prefix_lookup_Some; last apply Hprefix.
      by destruct Hblb as [? _].
    }
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
    by iMod ("HinvC" with "[Hc Hbs Hps Hts]") as "_"; first by eauto 10 with iFrame.
  }

  (*@     // Phase 3.                                                         @*)
  (*@     // Goal of this phase is to broadcast the consensus to other nodes. @*)
  (*@     px.learnAll(term, decree)                                           @*)
  (*@                                                                         @*)
  wp_load.
  wp_apply (wp_Paxos__learnAll with "Hcomm Hconsensus").
  wp_pures.
  
  (*@     px.mu.Unlock()                                                      @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ HhelpingRef $Hlock $Hlocked]").
  { do 5 iExists _. iFrame. iPureIntro. rewrite extend_length. lia. }
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
Qed.

End prog.
