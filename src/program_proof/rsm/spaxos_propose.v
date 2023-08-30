From Perennial.program_proof.rsm Require Import spaxos_prelude.
From Perennial.program_proof Require Import std_proof.

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

Definition is_proposal_nz γ n v : iProp Σ :=
  (if decide (n = O) then True else is_proposal γ n v)%I.

#[global]
Instance is_proposal_nz_persistent γ n v :
  Persistent (is_proposal_nz γ n v).
Proof. unfold is_proposal_nz. case_decide; apply _. Qed.

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
(*@     // Node ID.                                                         @*)
(*@     nid     uint64                                                      @*)
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
    "%Hnz"   ∷ ⌜int.nat termc ≠ O⌝ ∗
    (*@ Res: termp uint64                                                       @*)
    "Htermp" ∷ paxos ↦[Paxos :: "termp"] #termp ∗
    (*@ Res: decree string                                                      @*)
    "Hdecree" ∷ paxos ↦[Paxos :: "decree"] #(LitString decree) ∗
    (*@ Res: learned bool                                                       @*)
    "Hlearned" ∷ paxos ↦[Paxos :: "learned"] #learned ∗
    (*@ Res: ballot ghost                                                       @*)
    "Hballot" ∷ own_ballot γ nid blt ∗
    (*@ Res: termp uint64 / termmap ghost                                       @*)
    "Hterm" ∷ own_term γ nid (int.nat termp) ∗
    (*@ Res: termp uint64 / decree string / proposal ghost                      @*)
    "#Hproposed" ∷ is_proposal_nz γ (int.nat termp) decree ∗
    (*@ Res: termc uint64 / ballot ghost                                        @*)
    "%Hcurrent" ∷ ⌜length blt = int.nat termc⌝ ∗
    (*@ Res: termp uint64 / ballot ghost                                        @*)
    "%Hlatest" ∷ ⌜latest_term blt = (int.nat termp)⌝.

(* TODO: figure the clean way of defining node ID. *)
Definition is_paxos_node (paxos : loc) (nid : Z) (clst : gset Z) γ : iProp Σ :=
  ∃ (mu : loc) (nidu64 : u64),
    (*@ Res: mu *sync.Mutex                                                     @*)
    "#Hmu"   ∷ readonly (paxos ↦[Paxos :: "mu"] #mu) ∗
    "#Hlock" ∷ is_lock spaxosN #mu (own_paxos paxos nid γ) ∗
    (*@ Res: nid uint64                                                         @*)
    "#Hnid"  ∷ readonly (paxos ↦[Paxos :: "nid"] #nidu64) ∗
    "%HnidZ" ∷ ⌜int.Z nidu64 = nid⌝ ∗
    (*@ Res: cluster ghost                                                      @*)
    "#Hcluster" ∷ is_cluster γ clst ∗
    (*@ Res: ginv                                                               @*)
    "#Hinv"  ∷ know_sapxos_inv γ.

Definition is_paxos_comm (paxos : loc) (clst : gset Z) γ : iProp Σ :=
  ∃ (peers : Slice.t) (peersL : list loc),
    (*@ Res: peers []*Paxos                                                     @*)
    "#Hpeers"  ∷ readonly (paxos ↦[Paxos :: "peers"] (to_val peers)) ∗
    "#HpeersL" ∷ readonly (own_slice_small peers ptrT 1 peersL) ∗
    "#Hpaxos"  ∷ ([∗ list] i ↦ px ∈ peersL, is_paxos_node px (Z.of_nat i) clst γ) ∗
    "%Hclsteq" ∷ ⌜clst = list_to_set (Z.of_nat <$> (seq O (length peersL)))⌝.

Definition is_paxos (paxos : loc) (nid : Z) γ : iProp Σ :=
  ∃ (clst : gset Z),
    "#Hnode"    ∷ is_paxos_node paxos nid clst γ ∗
    "#Hcomm"    ∷ is_paxos_comm paxos clst γ.
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

Definition node_prepared (term termp : u64) (decree : string) nid γ : iProp Σ :=
  ∃ (l : ballot),
    "#Hlb"     ∷ is_ballot_lb γ nid l ∗
    "#Hdecree" ∷ is_proposal_nz γ (int.nat termp) decree ∗
    "%Hlen"    ∷ ⌜(int.nat term ≤ length l)%nat⌝ ∗
    "%Hlatest" ∷ ⌜latest_before (int.nat term) l = int.nat termp⌝.

Theorem wp_Paxos__prepare (px : loc) (term : u64) nid clst γ :
  is_paxos_node px nid clst γ -∗
  {{{ True }}}
    Paxos__prepare #px #term
  {{{ (termp : u64) (decree : string) (ok : bool), RET (#termp, #(LitString decree), #ok);
      if ok then node_prepared term termp decree nid γ else True
  }}}.
Proof.
  iIntros "#Hnode" (Φ) "!> _ HΦ".
  wp_call.

  (*@ func (px *Paxos) prepare(term uint64) (uint64, string, bool) {          @*)
  (*@     px.mu.Lock()                                                        @*)
  (*@                                                                         @*)
  iNamed "Hnode".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HpaxosOwn]".
  wp_pures.

  (*@     if term < px.termc {                                                @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return 0, "", false                                             @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  iNamed "HpaxosOwn".
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); first by eauto 15 with iFrame.
    wp_pures.
    by iApply "HΦ".
  }

  (*@     px.termc = term                                                     @*)
  (*@                                                                         @*)
  wp_storeField.

  (*@     // Ghost action:                                                    @*)
  (*@     // Extending the ballot of this node with [false] to @term to extract a @*)
  (*@     // promise that this node won't accept any proposal before @term.   @*)
  (*@                                                                         @*)
  set blt' := extend false (int.nat term) blt.
  iAssert (|={⊤}=> own_ballot γ nid blt')%I with "[Hballot]" as "> Hballot".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (ballot_lookup with "Hballot Hbs") as %Hblt.
    iMod (ballot_update blt' with "Hballot Hbs") as "[Hballot Hbs]".
    { apply extend_prefix. }
    rewrite lookup_insert_alter; last done.
    pose proof (vb_inv_prepare nid (int.nat term) Hvbs) as Hvbs'.
    pose proof (vp_inv_prepare nid (int.nat term) Hvps) as Hvps'.
    pose proof (vc_inv_prepare nid (int.nat term) Hvc) as Hvc'.
    by iMod ("HinvC" with "[Hc Hbs Hps Hts]") as "_"; first by eauto 15 with iFrame.
  }
  iDestruct (ballot_witness with "Hballot") as "#Hbltlb".

  (*@     termp  := px.termp                                                  @*)
  (*@     decree := px.decree                                                 @*)
  (*@                                                                         @*)
  do 2 wp_loadField.
  wp_pures.

  (*@     px.mu.Unlock()                                                      @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
  { do 5 iExists _. iFrame "∗ #".
    iPureIntro.
    split; first lia.
    split.
    { rewrite extend_length. lia. }
    by rewrite latest_term_extend_false.
  }
  wp_pures.

  (*@     // Informally, a positive response (@t, @d, @true) of @prepare(n) means: @*)
  (*@     // (1) This node will not accept any proposal with term below @n, and @*)
  (*@     // (2) The largest-term proposal this node has accepted before term @n is @*)
  (*@     // decree (@t, @d).                                                 @*)
  (*@     return termp, decree, true                                          @*)
  (*@ }                                                                       @*)
  iApply "HΦ".
  iExists _.
  iFrame "# %".
  iPureIntro.
  split.
  { rewrite extend_length. lia. }
  replace (int.nat term) with (length blt'); last first.
  { rewrite extend_length. lia. }
  rewrite -Hlatest.
  replace (latest_before _ _) with (latest_term blt') by done.
  apply latest_term_extend_false.
Qed.

Theorem wp_Paxos__advance (px : loc) nid clst γ :
  is_paxos_node px nid clst γ -∗
  {{{ True }}}
    Paxos__advance #px
  {{{ (term : u64) (termp : u64) (decree : string), RET (#term, #termp, #(LitString decree));
      node_prepared term termp decree nid γ ∗ ⌜is_term_of_node nid (int.nat term) ∧ int.nat term ≠ O⌝
  }}}.
Proof.
  iIntros "#Hnode" (Φ) "!> _ HΦ".
  wp_call.

  (*@ func (px *Paxos) advance() (uint64, uint64, string) {                   @*)
  (*@     px.mu.Lock()                                                        @*)
  (*@                                                                         @*)
  iNamed "Hnode".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HpaxosOwn]".
  wp_pures.

  (*@     term := std.SumAssumeNoOverflow(px.termc, MAX_NODES) / MAX_NODES * MAX_NODES + px.nid @*)
  (*@                                                                         @*)
  iNamed "HpaxosOwn".
  wp_loadField.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hoverflow).
  wp_pures.
  wp_loadField.
  wp_pures.
  set term := (word.add _ _).
  assert (Hofnode : is_term_of_node nid (int.nat term)).
  { admit. }
  assert (Hlt : (int.nat termc < int.nat term)%nat).
  { admit. }

  (*@     px.termc = term                                                     @*)
  (*@                                                                         @*)
  wp_storeField.

  (*@     // Ghost action:                                                    @*)
  (*@     // Extending the ballot of this node with [false] to @term to extract a @*)
  (*@     // promise that this node won't accept any proposal before @term.   @*)
  (*@                                                                         @*)
  set blt' := extend false (int.nat term) blt.
  iAssert (|={⊤}=> own_ballot γ nid blt')%I with "[Hballot]" as "> Hballot".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (ballot_lookup with "Hballot Hbs") as %Hblt.
    iMod (ballot_update blt' with "Hballot Hbs") as "[Hballot Hbs]".
    { apply extend_prefix. }
    rewrite lookup_insert_alter; last done.
    pose proof (vb_inv_prepare nid (int.nat term) Hvbs) as Hvbs'.
    pose proof (vp_inv_prepare nid (int.nat term) Hvps) as Hvps'.
    pose proof (vc_inv_prepare nid (int.nat term) Hvc) as Hvc'.
    by iMod ("HinvC" with "[Hc Hbs Hps Hts]") as "_"; first by eauto 15 with iFrame.
  }
  iDestruct (ballot_witness with "Hballot") as "#Hbltlb".

  (*@     termp  := px.termp                                                  @*)
  (*@     decree := px.decree                                                 @*)
  (*@                                                                         @*)
  do 2 wp_loadField.
  wp_pures.

  (*@     px.mu.Unlock()                                                      @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
  { do 5 iExists _. iFrame "∗ #".
    iPureIntro.
    split; first lia.
    split.
    { rewrite extend_length. lia. }
    by rewrite latest_term_extend_false.
  }
  wp_pures.

  (*@     return term, termp, decree                                          @*)
  (*@ }                                                                       @*)
  iApply "HΦ".
  iModIntro.
  iSplit; last first.
  { iPureIntro. split; [done | lia]. }
  iExists _.
  iFrame "# %".
  iPureIntro.
  split.
  { rewrite extend_length. lia. }
  replace (int.nat term) with (length blt'); last first.
  { rewrite extend_length. lia. }
  rewrite -Hlatest.
  replace (latest_before _ _) with (latest_term blt') by done.
  apply latest_term_extend_false.
Admitted.

Definition node_accepted (term : u64) (decree : string) nid γ : iProp Σ :=
  ∃ (l : ballot),
    "#Hlb"    ∷ is_ballot_lb γ nid l ∗
    "%Haccin" ∷ ⌜accepted_in l (int.nat term)⌝.

Theorem wp_Paxos__accept (px : loc) (term : u64) (decree : string) nid clst γ :
  is_paxos_node px nid clst γ -∗
  is_proposal γ (int.nat term) decree -∗
  {{{ True }}}
    Paxos__accept #px #term #(LitString decree)
  {{{ (ok : bool), RET #ok; if ok then node_accepted term decree nid γ else True }}}.
Proof.
  iIntros "#Hnode #Hproposal" (Φ) "!> _ HΦ".
  wp_call.

  (*@ func (px *Paxos) accept(term uint64, decree string) bool {              @*)
  (*@     px.mu.Lock()                                                        @*)
  (*@                                                                         @*)
  iNamed "Hnode".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HpaxosOwn]".
  wp_pures.

  (*@     if term < px.termc {                                                @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  iNamed "HpaxosOwn".
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); first by eauto 15 with iFrame.
    wp_pures.
    by iApply "HΦ".
  }

  (*@     px.termc = std.SumAssumeNoOverflow(term, 1)                         @*)
  (*@     px.termp = term                                                     @*)
  (*@     px.decree = decree                                                  @*)
  (*@                                                                         @*)
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hoverflow).
  do 3 wp_storeField.

  (*@     // Ghost action:                                                    @*)
  (*@     // Extending the ballot of this node with [false] to @term and append one @*)
  (*@     // [true] at index @term.                                           @*)
  (*@                                                                         @*)
  set accept := λ l, (extend false (int.nat term) l) ++ [true].
  set blt' := accept blt.
  set R := (own_ballot γ nid blt' ∗ own_term γ nid (int.nat term))%I.
  iAssert (|={⊤}=> R)%I with "[Hballot Hterm]" as "> [Hballot Hterm]".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (ballot_lookup with "Hballot Hbs") as %Hblt.
    iDestruct (proposal_lookup with "Hproposal Hps") as %Hpsl.
    iDestruct (term_lookup with "Hterm Hts") as %Htm.
    assert (Hprev : gt_prev_term ts nid (int.nat term)).
    { exists (int.nat termp). split; first done.
      assert (int.nat termp < int.nat termc)%nat.
      { rewrite -Hcurrent -Hlatest. apply latest_before_lt. lia. }
      lia.
    }
    iMod (ballot_update blt' with "Hballot Hbs") as "[Hballot Hbs]".
    { apply prefix_app_r, extend_prefix. }
    rewrite lookup_insert_alter; last done.
    iMod (term_update (int.nat term) with "Hterm Hts") as "[Hterm Hts]".
    unshelve epose proof (vb_inv_accept nid (int.nat term) _ _ Hvbs) as Hvbs'.
    { done. }
    { exists blt. split; first done. lia. }
    pose proof (vp_inv_accept nid (int.nat term) Hvps) as Hvps'.
    pose proof (vc_inv_accept nid (int.nat term) Hvc) as Hvc'.
    pose proof (vt_inv_advance Hprev Hvts) as Hvts'.
    iMod ("HinvC" with "[Hc Hbs Hps Hts]") as "_"; first by eauto 15 with iFrame.
    by iFrame.
  }
  clear R.
  iDestruct (ballot_witness with "Hballot") as "#Hbltlb".

  (*@     px.mu.Unlock()                                                      @*)
  (*@                                                                         @*)
  wp_loadField.
  iClear "Hproposed".
  iAssert (is_proposal_nz γ (int.nat term) decree)%I as "#Hproposed".
  { unfold is_proposal_nz. case_decide; done. }
  wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
  { do 5 iExists _. iFrame "∗ #".
    iPureIntro.
    replace (int.nat (word.add _ _)) with (S (int.nat term)) by word.
    split; first done.
    split.
    { rewrite last_length extend_length. lia. }
    rewrite latest_term_snoc_true extend_length.
    lia.
  }
  wp_pures.

  (*@     return true                                                         @*)
  (*@ }                                                                       @*)
  iApply "HΦ".
  iExists _.
  iFrame "#".
  iPureIntro.
  unfold accepted_in.
  split; last lia.
  rewrite lookup_app_r; last first.
  { rewrite extend_length. lia. }
  rewrite extend_length.
  by replace (_ - _)%nat with O by lia.
Qed.

Definition quorum_prepared
  (term : u64) (terml : u64) (decreel : string) (clst : gset Z) (γ : spaxos_names) : iProp Σ :=
  ∃ (bsqlb : gmap Z ballot),
    "#Hlbs"      ∷ ([∗ map] x ↦ l ∈ bsqlb, is_ballot_lb γ x l) ∗
    "#Hproposal" ∷ is_proposal_nz γ (int.nat terml) decreel ∗
    "%Hquorum"   ∷ ⌜quorum clst (dom bsqlb)⌝ ∗
    "%Hlen"      ∷ ⌜map_Forall (λ _ l, ((int.nat term) ≤ length l)%nat) bsqlb⌝ ∗
    "%Hlargest"  ∷ ⌜latest_before_quorum (int.nat term) bsqlb = int.nat terml⌝.

#[global]
Instance quorum_prepared_persistent term terml decree clst γ :
  Persistent (quorum_prepared term terml decree clst γ).
Proof. apply _. Qed.

Theorem wp_Paxos__accept__proposer
  (px : loc) (term : u64) (decree : string) (terml : u64) decreel nid clst γ :
  is_term_of_node nid (int.nat term) ->
  (if decide (int.nat terml = O) then True else decree = decreel) ->
  quorum_prepared term terml decreel clst γ -∗
  is_paxos_node px nid clst γ -∗
  {{{ True }}}
    Paxos__accept #px #term #(LitString decree)
  {{{ (ok : bool), RET #ok;
      if ok then node_accepted term decree nid γ ∗ is_proposal γ (int.nat term) decree else True
  }}}.
Proof.
  iIntros "%Hofnode %Hdecree #Hprepares #Hnode" (Φ) "!> _ HΦ".
  wp_call.

  (*@ func (px *Paxos) accept(term uint64, decree string) bool {              @*)
  (*@     px.mu.Lock()                                                        @*)
  (*@                                                                         @*)
  iNamed "Hnode".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HpaxosOwn]".
  wp_pures.

  (*@     if term < px.termc {                                                @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  iNamed "HpaxosOwn".
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); first by eauto 15 with iFrame.
    wp_pures.
    by iApply "HΦ".
  }
  iClear "Hproposed".

  (*@     px.termc = std.SumAssumeNoOverflow(term, 1)                         @*)
  (*@     px.termp = term                                                     @*)
  (*@     px.decree = decree                                                  @*)
  (*@                                                                         @*)
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hoverflow).
  do 3 wp_storeField.

  (*@     // Ghost action for proposer:                                       @*)
  (*@     // (1) updating termmap of this node to @term,                      @*)
  (*@     // (2) inserting proposal (@term, @decree) in proposals.            @*)
  (*@     //                                                                  @*)
  (*@     // Note 1:                                                          @*)
  (*@     // To update the proposals in an invariant-preserving way, we need to know @*)
  (*@     // two things:                                                      @*)
  (*@     // (1) @term has not been used, and                                 @*)
  (*@     // (2) the proposal we're making, (@term, @decree), is a valid one. @*)
  (*@     // See [vp_inv_propose] for detail.                                 @*)
  (*@     //                                                                  @*)
  (*@     // Note 2: Ideally, we want to update the ghost state one at a time if @*)
  (*@     // possible; for instance, we update the termmap and proposals here, and @*)
  (*@     // then the ballot below.                                           @*)
  (*@     // Following this discipline should significatly simplify invairance proofs. @*)
  (*@     // However, sometimes we'll have to update more than one ghost states in one @*)
  (*@     // step; for instance, we update the termmap and proposals together @*)
  (*@     // here. The reason is that we need to deduce @term is free using the @*)
  (*@     // free-term invariant, insert the proposal at @term, update the termmap @*)
  (*@     // entry to @term to re-establish the free-term invariant.          @*)
  (*@     //                                                                  @*)
  (*@     // Note 3: An alternative design would be separately proposing and then @*)
  (*@     // accepting. The downside of this design is that we would need an  @*)
  (*@     // additional physical state to distinguish between "not proposed" state @*)
  (*@     // from "proposed but not accepted" state. By merging proposing with @*)
  (*@     // accepting, we know a term has not been used by a node if that term @*)
  (*@     // belongs to the node *and* that the node has not accepted the term. Hence @*)
  (*@     // this design saves one physical state.                            @*)
  (*@                                                                         @*)
  assert (Htermcp : (int.nat termp < int.nat termc)%nat).
  { rewrite -Hcurrent -Hlatest. apply latest_before_lt. lia. }
  assert (Htermorder : (int.nat termp < int.nat term)%nat) by lia.
  set R := (own_term γ nid (int.nat term) ∗ is_proposal γ (int.nat term) decree)%I.
  iAssert (|={⊤}=> R)%I with "[Hterm]" as "> [Hterm #Hproposal]".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (term_lookup with "Hterm Hts") as %Htermc.
    assert (Hprev : gt_prev_term ts nid (int.nat term)).
    { exists (int.nat termp). split; [done | word]. }
    pose proof (vt_impl_freshness Htermc Htermorder Hofnode Hvts) as Hfresh.
    iAssert (⌜valid_proposal bs ps (int.nat term) decree⌝)%I as %Hvalid.
    { iNamed "Hprepares".
      iDestruct (ballots_prefix with "Hlbs Hbs") as %Hprefix.
      unfold is_proposal_nz.
      iAssert (⌜if decide (int.nat terml = O)
               then True
               else ps !! (int.nat terml) = Some decree⌝)%I as %Hatterm.
      { case_decide; first done. rewrite Hdecree. by iApply proposal_lookup. }
      iDestruct (cluster_eq with "Hcluster Hclst") as %->.
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
      - right. by rewrite Hlargest.
    }
    iMod (proposals_insert _ _ decree with "Hps") as "[Hps #Hp]"; first apply Hfresh.
    iMod (term_update (int.nat term) with "Hterm Hts") as "[Hterm Hts]".
    assert (Htermnz : int.nat term ≠ O) by lia.
    pose proof (vp_inv_propose Hfresh Htermnz Hvalid Hvps) as Hvps'.
    pose proof (vb_inv_propose (int.nat term) decree Hvbs) as Hvbs'.
    pose proof (vc_inv_propose (int.nat term) decree Hvc) as Hvc'.
    pose proof (vt_inv_propose_advance decree Hprev Hofnode Hvts) as Hvts'.
    iMod ("HinvC" with "[Hc Hbs Hps Hts]") as "_"; first by eauto 10 with iFrame.
    by iFrame.
  }
  clear R.

  (*@     // Ghost action:                                                    @*)
  (*@     // Extending the ballot of this node with [false] to @term and append one @*)
  (*@     // [true] at index @term.                                           @*)
  (*@                                                                         @*)
  set accept := λ l, (extend false (int.nat term) l) ++ [true].
  set blt' := accept blt.
  iAssert (|={⊤}=> own_ballot γ nid blt')%I with "[Hballot]" as "> Hballot".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (ballot_lookup with "Hballot Hbs") as %Hblt.
    iDestruct (proposal_lookup with "Hproposal Hps") as %Hpsl.
    iMod (ballot_update blt' with "Hballot Hbs") as "[Hballot Hbs]".
    { apply prefix_app_r, extend_prefix. }
    rewrite lookup_insert_alter; last done.
    unshelve epose proof (vb_inv_accept nid (int.nat term) _ _ Hvbs) as Hvbs'.
    { done. }
    { exists blt. split; first done. lia. }
    pose proof (vp_inv_accept nid (int.nat term) Hvps) as Hvps'.
    pose proof (vc_inv_accept nid (int.nat term) Hvc) as Hvc'.
    iMod ("HinvC" with "[Hc Hbs Hps Hts]") as "_"; first by eauto 15 with iFrame.
    by iFrame.
  }
  iDestruct (ballot_witness with "Hballot") as "#Hbltlb".

  (*@     px.mu.Unlock()                                                      @*)
  (*@                                                                         @*)
  wp_loadField.
  iAssert (is_proposal_nz γ (int.nat term) decree)%I as "#Hproposed".
  { unfold is_proposal_nz. destruct (decide (int.nat term = _)); done. }
  wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
  { do 5 iExists _. iFrame "∗ #".
    iPureIntro.
    replace (int.nat (word.add _ _)) with (S (int.nat term)) by word.
    split; first done.
    split.
    { rewrite last_length extend_length. lia. }
    rewrite latest_term_snoc_true extend_length.
    lia.
  }
  wp_pures.

  (*@     return true                                                         @*)
  (*@ }                                                                       @*)
  iApply "HΦ". iModIntro.
  iSplit; last done.
  iExists _.
  iFrame "#".
  iPureIntro.
  unfold accepted_in.
  split; last lia.
  rewrite lookup_app_r; last first.
  { rewrite extend_length. lia. }
  rewrite extend_length.
  by replace (_ - _)%nat with O by lia.
Qed.

Theorem wp_Paxos__prepareAll (px : loc) (term terma : u64) (decreea : string) clst nid γ :
  is_paxos_comm px clst γ -∗
  node_prepared term terma decreea nid γ -∗
  {{{ True }}}
    Paxos__prepareAll #px #term #terma #(LitString decreea)
  {{{ (termp : u64) (decree : string) (ok : bool), RET (#termp, #(LitString decree), #ok);
      if ok then quorum_prepared term termp decree clst γ else True
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

Definition quorum_accepted (term : u64) (clst : gset Z) (γ : spaxos_names) : iProp Σ :=
  ∃ (bsqlb : gmap Z ballot),
    "#Hlbs"    ∷ ([∗ map] x ↦ l ∈ bsqlb, is_ballot_lb γ x l) ∗
    "%Hquorum" ∷ ⌜quorum clst (dom bsqlb)⌝ ∗
    "%Haccin"  ∷ ⌜map_Forall (λ _ l, accepted_in l (int.nat term)) bsqlb⌝.

#[global]
Instance quorum_accepted_persistent term clst γ :
  Persistent (quorum_accepted γ term clst).
Proof. apply _. Qed.

Theorem wp_Paxos__acceptAll (px : loc) (term : u64) (decree : string) clst nid γ :
  is_paxos_comm px clst γ -∗
  node_accepted term decree nid γ -∗
  is_proposal γ (int.nat term) decree -∗
  {{{ True }}}
    Paxos__acceptAll #px #term #(LitString decree)
  {{{ (ok : bool), RET #ok; if ok then quorum_accepted term clst γ else True }}}.
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

Section prog.
Context `{!heapGS Σ, !spaxos_ghostG Σ}.

Theorem wp_Paxos__Propose (px : loc) (v : string) nid γ :
  is_paxos px nid γ -∗
  {{{ True }}}
    Paxos__Propose #px #(LitString v)
  {{{ (ok : bool), RET #ok; if ok then is_proposed_decree γ v else True }}}.
Proof.
  iIntros "#Hpaxos !>" (Φ) "_ HΦ".
  wp_call.

  (*@ func (px *Paxos) Propose(v string) bool {                               @*)
  (*@     // Proceed to a new term exclusively owned by this paxos node.      @*)
  (*@     // NB: Raft does not exclusively own a term until the first phase goes thru. @*)
  (*@     term, terma, decreea := px.advance()                                @*)
  (*@                                                                         @*)
  iNamed "Hpaxos".
  wp_apply (wp_Paxos__advance with "Hnode").
  iIntros (term terma decreea) "[#Hprep [%Hofnode %Htermnz]]".
  wp_pures.

  (*@     // Phase 1.                                                         @*)
  (*@     // Goals of this phase is to get a quorum of nodes:                 @*)
  (*@     // (1) promise not to accept any proposal with term below @term, and @*)
  (*@     // (2) find out the largest proposal (below @term) accepted by the quorum. @*)
  (*@     terml, decreel, prepared := px.prepareAll(term, terma, decreea)     @*)
  (*@                                                                         @*)
  wp_apply (wp_Paxos__prepareAll with "Hcomm Hprep").
  iIntros (terml decreel prepared) "Hprepq".
  wp_pures.
  
  (*@     if !prepared {                                                      @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct; first by iApply "HΦ".
  iDestruct "Hprepq" as "#Hprepq".

  (*@     var decree string                                                   @*)
  (*@     var helping bool                                                    @*)
  (*@                                                                         @*)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (decreeRef) "HdecreeRef".
  wp_pures.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (helpingRef) "HhelpingRef".
  wp_pures.

  (*@     // If @terml is not set (meaning no node in the quorum has accepted any @*)
  (*@     // proposal yet), we can propose our value @v.                      @*)
  (*@     if terml == 0 {                                                     @*)
  (*@         // We're the ``initiating'' thread.                             @*)
  (*@         decree = v                                                      @*)
  (*@         helping = false                                                 @*)
  (*@     } else {                                                            @*)
  (*@         // We're the ``helping'' thread.                                @*)
  (*@         decree = decreel                                                @*)
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
        (if b then (LitString v) else (LitString decreel)) by by rewrite Eqb.
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

  (*@     // We have decided what to propose (i.e., @decree).                 @*)
  (*@     proposed := px.accept(term, decree)                                 @*)
  (*@                                                                         @*)
  wp_load.
  wp_apply (wp_Paxos__accept__proposer with "Hprepq Hnode"); first done.
  { case_decide as Hneq; first done.
    case_bool_decide as Heq; last done.
    inversion Heq as [Eterml].
    rewrite Eterml in Hneq.
    by replace (int.nat (U64 0)) with O in Hneq by word.
  }
  iIntros (proposed) "Hproposed".
  wp_pures.

  (*@     if !proposed {                                                      @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct; first by iApply "HΦ".
  iDestruct "Hproposed" as "[#Hacpt #Hpsl]".

  (*@     // Phase 2.                                                         @*)
  (*@     // Goal of this phase is to get a quorum of nodes accepting our proposal. @*)
  (*@     accepted := px.acceptAll(term, decree)                              @*)
  (*@                                                                         @*)
  wp_load.
  wp_apply (wp_Paxos__acceptAll with "Hcomm Hacpt Hpsl").
  iIntros (accepted) "Hacptq".
  wp_pures.

  (*@     if !accepted {                                                      @*)
  (*@         return !helping                                                 @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct.
  { wp_load.
    unfold is_proposed_decree.
    case_bool_decide; wp_pures; iApply "HΦ"; [by eauto | done].
  }
  iDestruct "Hacptq" as "#Hacptq".

  (*@     // Ghost action: Committing the consensus.                          @*)
  (*@     //                                                                  @*)
  (*@     // Note 1:                                                          @*)
  (*@     // If @accepted is true, we know @decree is chosen either the first time, @*)
  (*@     // or has already been chosen earlier. If it's the first time, we simply @*)
  (*@     // perform a ghost update on consensus; if it's been chosen earlier, we @*)
  (*@     // apply the top-level consistency theorem to deduce the decree chosen here @*)
  (*@     // (i.e., @decree) is equal to the one chosen eariler.              @*)
  (*@                                                                         @*)
  set decree := (if (bool_decide _) then v else _).
  iAssert (|={⊤}=> is_chosen_consensus γ decree)%I as "> #Hconsensus".
  { iNamed "Hnode".
    iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iAssert (⌜chosen bs ps decree⌝)%I as %Hchosen.
    { iNamed "Hacptq".
      iDestruct (ballots_prefix with "Hlbs Hbs") as %Hprefix.
      iDestruct (proposal_lookup with "Hpsl Hps") as %Hatterm.
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

  (*@     // If @helping is true, return false since we're merely helping an early @*)
  (*@     // proposal go through, rather than proposing our own value @v.     @*)
  (*@     return !helping                                                     @*)
  (*@ }                                                                       @*)
  wp_load.
  unfold is_proposed_decree.
  case_bool_decide; wp_pures; iApply "HΦ"; [by eauto | done].
Qed.

End prog.
