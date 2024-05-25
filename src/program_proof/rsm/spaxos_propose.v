From Perennial.program_proof.rsm Require Import spaxos_prelude rsm_misc.
From Perennial.program_proof Require Import std_proof.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

(* TODO: move this out to spaxos_iris_inv.v once stable. *)
Section inv.
Context `{!heapGS Σ, !spaxos_ghostG Σ}.

Definition spaxosN := nroot .@ "spaxos".

Definition max_nodes : Z := 16.

Definition is_term_of_node (x : u64) (n : nat) :=
  n `mod` max_nodes = (uint.Z x).

(* TODO: make this a typeclass. *)
Lemma is_term_of_node_partitioned x1 x2 n :
  x1 ≠ x2 -> is_term_of_node x1 n -> not (is_term_of_node x2 n).
Proof.
  unfold is_term_of_node.
  intros Hne Hx1.
  rewrite Hx1.
  by apply word.unsigned_inj'.
Qed.

Definition consented_impl_committed (v c : consensus) :=
  if v then c = v else True.

Definition proposals_incl_candidates (vs : gset string) (ps : gmap nat string) :=
  map_img ps ⊆ vs.

Definition spaxos_inv sc γ : iProp Σ :=
  ∃ v vs c bs ps ts,
    (* External states: *)
    "Hv"      ∷ own_consensus_half γ v ∗
    "Hvs"     ∷ own_candidates_half γ vs ∗
    (* Internal states: *)
    "Hc"      ∷ own_commitment γ c ∗
    "Hbs"     ∷ own_ballots γ bs ∗
    "Hps"     ∷ own_proposals γ ps ∗
    "Hts"     ∷ own_terms γ ts ∗
    (* Constraints between external and internal states: *)
    "%Hcic"   ∷ ⌜consented_impl_committed v c⌝ ∗
    "%Hpic"   ∷ ⌜proposals_incl_candidates vs ps⌝ ∗
    (* Constraints on internal states: *)
    "%Hvc"    ∷ ⌜valid_commitment c bs ps⌝ ∗
    "%Hvbs"   ∷ ⌜valid_ballots bs ps⌝ ∗
    "%Hvps"   ∷ ⌜valid_proposals bs ps⌝ ∗
    "%Hvts"   ∷ ⌜valid_terms is_term_of_node ps ts⌝ ∗
    "%Hdombs" ∷ ⌜size (dom bs) = sc⌝.

#[global]
Instance spaxos_inv_timeless sc γ :
  Timeless (spaxos_inv sc γ).
Admitted.

Definition know_sapxos_inv sc γ : iProp Σ :=
  inv spaxosN (spaxos_inv sc γ).

Definition is_proposal_nz γ n v : iProp Σ :=
  (if decide (n = O) then True else is_proposal γ n v)%I.

#[global]
Instance is_proposal_nz_persistent γ n v :
  Persistent (is_proposal_nz γ n v).
Proof. unfold is_proposal_nz. case_decide; apply _. Qed.

Definition is_chosen_commitment_learned γ (l : bool) (v : string) : iProp Σ :=
  (if l then is_chosen_commitment γ v else True)%I.

#[global]
Instance is_commitment_learned_persistent γ l v :
  Persistent (is_chosen_commitment_learned γ l v).
Proof. unfold is_chosen_commitment_learned. destruct l; apply _. Qed.

End inv.

#[export]
Hint Extern 1 (environments.envs_entails _ (spaxos_inv _ _)) => unfold spaxos_inv : core.
#[export]
Hint Extern 1 (size (dom (alter _ _ _)) = _) => rewrite dom_alter_L : core.
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
(*@     decreep  string                                                     @*)
(*@     // Have we learned the consensus?                                   @*)
(*@     learned bool                                                        @*)
(*@     // Size of the cluster.                                             @*)
(*@     sc      uint64                                                      @*)
(*@     // Other paxos instances. Eventually should be just addresses.      @*)
(*@     peers   map[uint64]*Paxos                                           @*)
(*@ }                                                                       @*)
Definition own_paxos (paxos : loc) (nid : u64) γ : iProp Σ :=
  ∃ (termc termp : u64) (decreep : string) (learned : bool) (blt : ballot),
    "Htermc" ∷ paxos ↦[Paxos :: "termc"] #termc ∗
    "%Hnz"   ∷ ⌜uint.nat termc ≠ O⌝ ∗
    "Htermp" ∷ paxos ↦[Paxos :: "termp"] #termp ∗
    "Hdecreep" ∷ paxos ↦[Paxos :: "decreep"] #(LitString decreep) ∗
    "Hlearned" ∷ paxos ↦[Paxos :: "learned"] #learned ∗
    "Hballot" ∷ own_ballot γ nid blt ∗
    "Hterm" ∷ own_term γ nid (uint.nat termp) ∗
    "#Hproposed" ∷ is_proposal_nz γ (uint.nat termp) decreep ∗
    "#Hcommitment" ∷ is_chosen_commitment_learned γ learned decreep ∗
    "%Hcurrent" ∷ ⌜length blt = uint.nat termc⌝ ∗
    "%Hlatest" ∷ ⌜latest_term blt = (uint.nat termp)⌝ ∗
    "%Htermpnz" ∷ ⌜if learned then (uint.nat termp) ≠ O else True⌝.

(* TODO: figure the clean way of defining node ID. *)
Definition is_paxos_node (paxos : loc) (nid : u64) (sc : nat) γ : iProp Σ :=
  ∃ (mu : loc),
    "#Hmu"   ∷ readonly (paxos ↦[Paxos :: "mu"] #mu) ∗
    "#Hlock" ∷ is_lock spaxosN #mu (own_paxos paxos nid γ) ∗
    "#Hnid" ∷ readonly (paxos ↦[Paxos :: "nid"] #nid) ∗
    "%Hnid" ∷ ⌜0 ≤ uint.Z nid < max_nodes⌝ ∗
    "#Hinv" ∷ know_sapxos_inv sc γ.

(* NB: We don't really need read-only map since reconfiguration is to be supported. *)
Instance own_map_as_pointsto `{Countable K} `{!IntoVal K} `{!IntoVal V} (mref : loc) (m : gmap K V) :
  AsMapsTo (own_map mref (DfracOwn 1) m) (λ q : Qp, own_map mref (DfracOwn q) m).
Admitted.

Definition is_paxos_comm (paxos : loc) (nid : u64) sc γ : iProp Σ :=
  ∃ (peers : loc) (peersM : gmap u64 loc) (scu64 : u64),
    "#Hpeers"   ∷ readonly (paxos ↦[Paxos :: "peers"] #peers) ∗
    "#HpeersMR" ∷ readonly (own_map peers (DfracOwn 1) peersM) ∗
    "#Hpaxos"   ∷ ([∗ map] i ↦ px ∈ peersM, is_paxos_node px i sc γ) ∗
    "%Hszpeers" ∷ ⌜size peersM < max_nodes⌝ ∗
    "%Hnotin"   ∷ ⌜nid ∉ dom peersM⌝ ∗
    "#Hsc"      ∷ readonly (paxos ↦[Paxos :: "sc"] #scu64) ∗
    "%Hscu64"   ∷ ⌜uint.nat scu64 = sc⌝.

Definition is_paxos (paxos : loc) (nid : u64) sc γ : iProp Σ :=
  "#Hnode" ∷ is_paxos_node paxos nid sc γ ∗
  "#Hcomm" ∷ is_paxos_comm paxos nid sc γ.
End repr.

#[export]
Hint Extern 1 (environments.envs_entails _ (own_paxos _ _ _)) => unfold own_paxos : core.
(* TODO: move this out to spaxos_repr.v once stable. *)

(* TODO: move them out to their own files once stable. *)
Section temp.
Context `{!heapGS Σ, !spaxos_ghostG Σ}.

Definition paxos_init px γ : iProp Σ :=
  "Hvs"  ∷ own_candidates_half γ ∅ ∗
  "Hv"   ∷ own_consensus_half γ Free ∗
  "#Hpx" ∷ is_paxos px (W64 0) 3%nat γ.

Theorem wp_MkPaxos :
  {{{ True }}}
    MkPaxos #()
  {{{ (γ : spaxos_names) (px : loc), RET #px; paxos_init px γ }}}.
Proof.
  (*@ func MkPaxos() *Paxos {                                                 @*)
  (*@     var px *Paxos                                                       @*)
  (*@                                                                         @*)
  (*@     return px                                                           @*)
  (*@ }                                                                       @*)
Admitted.

Lemma Z_next_aligned (c i l : Z) :
  0 ≤ l < i ->
  (c + (l - (c `mod` i))) `mod` i = l.
Proof.
  intros Horder.
  rewrite Zplus_mod Zminus_mod Zmod_mod -Zminus_mod -Zplus_mod.
  replace (c + _) with l by lia.
  apply Zmod_small. lia.
Qed.

Theorem wp_NextAligned (current : u64) (interval : u64) (low : u64) :
  uint.Z interval < 2 ^ 63 ->
  0 ≤ uint.Z low < uint.Z interval ->
  {{{ True }}}
    NextAligned #current #interval #low
  {{{ (n : u64), RET #n;
      ⌜uint.Z current < uint.Z n ∧ uint.Z n `mod` uint.Z interval = uint.Z low⌝
  }}}.
Proof.
  iIntros (Hitv Horder Φ) "_ HΦ".
  wp_call.

  (*@ func NextAligned(current, interval, low uint64) uint64 {                @*)
  (*@     var delta uint64                                                    @*)
  (*@                                                                         @*)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (deltaRef) "HdeltaRef".
  wp_pures.

  (*@     rem := current % interval                                           @*)
  (*@     if rem < low {                                                      @*)
  (*@         delta = low - rem                                               @*)
  (*@     } else {                                                            @*)
  (*@         delta = interval + low - rem                                    @*)
  (*@     }                                                                   @*)
  (*@     return std.SumAssumeNoOverflow(current, delta)                      @*)
  (*@ }                                                                       @*)
  set rem := (word.modu _ _).
  wp_if_destruct; wp_store; wp_load; wp_apply wp_SumAssumeNoOverflow.
  - iIntros (Hoverflow). iApply "HΦ". iPureIntro.
    rewrite Hoverflow.
    split; first word.
    rewrite word.unsigned_sub_nowrap; last lia.
    rewrite word.unsigned_modu_nowrap; last lia.
    apply Z_next_aligned.
    lia.
  - iIntros (Hoverflow). iApply "HΦ". iPureIntro.
    rewrite Hoverflow.
    rewrite word.unsigned_sub_nowrap; last first.
    { rewrite word.unsigned_add_nowrap; last lia.
      rewrite word.unsigned_modu_nowrap; lia.
    }
    rewrite word.unsigned_add_nowrap; last lia.
    rewrite word.unsigned_modu_nowrap; last lia.
    rewrite word.unsigned_modu_nowrap in Heqb; last lia.
    split; first lia.
    rewrite -Z.add_sub_assoc Z.add_assoc (Z.add_comm (uint.Z current)) -Z.add_assoc.
    rewrite Zplus_mod Z_mod_same_full Z.add_0_l Zmod_mod.
    apply Z_next_aligned.
    lia.
Qed.

Definition is_proposed_decree γ v : iProp Σ :=
  ∃ n, is_proposal γ n v.

Theorem wp_Paxos__outcome (px : loc) nid sc γ :
  is_paxos_node px nid sc γ -∗
  {{{ True }}}
  <<< ∀∀ c, own_consensus_half γ c >>>
    Paxos__outcome #px @ ↑spaxosN
  <<< ∃∃ (v : string) (ok : bool), own_consensus_half γ (if ok then Chosen v else c) >>>
  {{{ RET (#(LitString v), #ok); True }}}.
Proof.
  iIntros "#Hnode" (Φ) "!> _ HAU".
  wp_call.

  (*@ func (px *Paxos) outcome() (string, bool) {                             @*)
  (*@     px.mu.Lock()                                                        @*)
  (*@     decree := px.decreep                                                @*)
  (*@     learned := px.learned                                               @*)
  (*@     px.mu.Unlock()                                                      @*)
  (*@     return decree, learned                                              @*)
  (*@ }                                                                       @*)
  iNamed "Hnode".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HpaxosOwn]".
  wp_pures.
  iNamed "HpaxosOwn".
  do 2 wp_loadField. wp_pures. wp_loadField.
  wp_apply (release_spec with "[-HAU $Hlock $Hlocked]"); first eauto 15 with iFrame.
  wp_pures.

  destruct learned eqn:Elearned; last first.
  - (* Case: Returning false. *)
    iMod (ncfupd_mask_subseteq (⊤ ∖ ↑spaxosN)) as "Hclose"; first solve_ndisj.
    iMod "HAU" as (c) "[Hv HAU]".
    iMod ("HAU" $! decreep false with "Hv") as "HΦ".
    iMod "Hclose".
    by iApply "HΦ".
  - (* Case: Returning true. *)
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod "HAU" as (v') "[Hv' HAU]".
    iNamed "HinvO".
    iDestruct (consensus_combine with "Hv Hv'") as "[Hv <-]".
    unfold is_chosen_commitment_learned.
    iDestruct (commitment_discharged with "Hc Hcommitment") as %->.
    destruct v as [v' |] eqn:Ev.
    + (* Case: Subsequent observer (i.e., consensus already set). *)
      rewrite -Hcic.
      iDestruct (consensus_split with "Hv") as "[Hv Hv']".
      iMod ("HAU" $! decreep true with "Hv'") as "HΦ".
      iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 10 with iFrame.
      by iApply "HΦ".
    + (* Case: First observer. *)
      unfold is_proposal_nz.
      case_decide; first contradiction.
      iDestruct (proposal_lookup with "Hproposed Hps") as %Hin.
      iMod (consensus_update decreep with "Hv Hvs") as "[Hv Hvs]".
      { unfold proposals_incl_candidates in Hpic.
        apply (elem_of_map_img_2 (SA:=gset string)) in Hin.
        set_solver.
      }
      iDestruct (consensus_split with "Hv") as "[Hv Hv']".
      iMod ("HAU" $! decreep true with "Hv'") as "HΦ".
      iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 10 with iFrame.
      by iApply "HΦ".
Qed.

Theorem wp_Paxos__Outcome (px : loc) nid sc γ :
  is_paxos px nid sc γ -∗
  {{{ True }}}
  <<< ∀∀ c, own_consensus_half γ c >>>
    Paxos__Outcome #px @ ↑spaxosN
  <<< ∃∃ (v : string) (ok : bool), own_consensus_half γ (if ok then Chosen v else c) >>>
  {{{ RET (#(LitString v), #ok); True }}}.
Proof.
  iIntros "#Hpaxos" (Φ) "!> _ HAU".
  wp_call.

  (*@ func (px *Paxos) Outcome() (string, bool) {                             @*)
  (*@     decree, ok := px.outcome()                                          @*)
  (*@     return decree, ok                                                   @*)
  (*@ }                                                                       @*)
  iNamed "Hpaxos".
  wp_apply (wp_Paxos__outcome with "Hnode").
  iMod "HAU" as (c) "[Hv HAU]".
  iModIntro. iExists c. iFrame.
  iIntros (v ok) "Hv".
  iMod ("HAU" $! v ok with "Hv") as "HΦ".
  iIntros "!> _".
  wp_pures.
  by iApply "HΦ".
Qed.

Definition node_prepared (term termp : u64) (decree : string) nid γ : iProp Σ :=
  ∃ (l : ballot),
    "#Hlb"     ∷ is_ballot_lb γ nid l ∗
    "#Hdecree" ∷ is_proposal_nz γ (uint.nat termp) decree ∗
    "%Hlen"    ∷ ⌜(uint.nat term ≤ length l)%nat⌝ ∗
    "%Hlatest" ∷ ⌜latest_before (uint.nat term) l = uint.nat termp⌝.

Theorem wp_Paxos__prepare (px : loc) (term : u64) nid sc γ :
  is_paxos_node px nid sc γ -∗
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
  set blt' := extend false (uint.nat term) blt.
  iAssert (|={⊤}=> own_ballot γ nid blt')%I with "[Hballot]" as "> Hballot".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (ballot_lookup with "Hballot Hbs") as %Hblt.
    iMod (ballot_update blt' with "Hballot Hbs") as "[Hballot Hbs]".
    { apply extend_prefix. }
    rewrite -lookup_alter_Some; last done.
    pose proof (vb_inv_prepare nid (uint.nat term) Hvbs) as Hvbs'.
    pose proof (vp_inv_prepare nid (uint.nat term) Hvps) as Hvps'.
    pose proof (vc_inv_prepare nid (uint.nat term) Hvc) as Hvc'.
    by iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 20 with iFrame.
  }
  iDestruct (ballot_witness with "Hballot") as "#Hbltlb".

  (*@     termp   := px.termp                                                 @*)
  (*@     decreep := px.decreep                                              @*)
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
  (*@     return termp, decreep, true                                         @*)
  (*@ }                                                                       @*)
  iApply "HΦ".
  iExists _.
  iFrame "# %".
  iPureIntro.
  split.
  { rewrite extend_length. lia. }
  replace (uint.nat term) with (length blt'); last first.
  { rewrite extend_length. lia. }
  rewrite -Hlatest.
  replace (latest_before _ _) with (latest_term blt') by done.
  apply latest_term_extend_false.
Qed.

Theorem wp_Paxos__advance (px : loc) nid sc γ :
  is_paxos_node px nid sc γ -∗
  {{{ True }}}
    Paxos__advance #px
  {{{ (term : u64) (termp : u64) (decree : string), RET (#term, #termp, #(LitString decree));
      node_prepared term termp decree nid γ ∗ ⌜is_term_of_node nid (uint.nat term) ∧ uint.nat term ≠ O⌝
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

  (*@     term := NextAligned(px.termc, MAX_NODES, px.nid)                    @*)
  (*@                                                                         @*)
  iNamed "HpaxosOwn".
  do 2 wp_loadField.
  unfold max_nodes in Hnid.
  wp_apply wp_NextAligned; [word | word |].
  iIntros (term) "[%Hlt %Hofnode]".
  wp_pures.

  (*@     px.termc = term                                                     @*)
  (*@                                                                         @*)
  wp_storeField.

  (*@     // Ghost action:                                                    @*)
  (*@     // Extending the ballot of this node with [false] to @term to extract a @*)
  (*@     // promise that this node won't accept any proposal before @term.   @*)
  (*@                                                                         @*)
  set blt' := extend false (uint.nat term) blt.
  iAssert (|={⊤}=> own_ballot γ nid blt')%I with "[Hballot]" as "> Hballot".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (ballot_lookup with "Hballot Hbs") as %Hblt.
    iMod (ballot_update blt' with "Hballot Hbs") as "[Hballot Hbs]".
    { apply extend_prefix. }
    rewrite -lookup_alter_Some; last done.
    pose proof (vb_inv_prepare nid (uint.nat term) Hvbs) as Hvbs'.
    pose proof (vp_inv_prepare nid (uint.nat term) Hvps) as Hvps'.
    pose proof (vc_inv_prepare nid (uint.nat term) Hvc) as Hvc'.
    by iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 20 with iFrame.
  }
  iDestruct (ballot_witness with "Hballot") as "#Hbltlb".

  (*@     termp   := px.termp                                                  @*)
  (*@     decreep := px.decreep                                               @*)
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

  (*@     return term, termp, decreep                                         @*)
  (*@ }                                                                       @*)
  iApply "HΦ".
  iModIntro.
  iSplit; last first.
  { iPureIntro. unfold is_term_of_node, max_nodes. split; [word | lia]. }
  iExists _.
  iFrame "# %".
  iPureIntro.
  split.
  { rewrite extend_length. lia. }
  replace (uint.nat term) with (length blt'); last first.
  { rewrite extend_length. lia. }
  rewrite -Hlatest.
  replace (latest_before _ _) with (latest_term blt') by done.
  apply latest_term_extend_false.
Qed.

Definition node_accepted (term : u64) (decree : string) nid γ : iProp Σ :=
  ∃ (l : ballot),
    "#Hlb"    ∷ is_ballot_lb γ nid l ∗
    "%Haccin" ∷ ⌜accepted_in l (uint.nat term)⌝.

Theorem wp_Paxos__accept (px : loc) (term : u64) (decree : string) nid sc γ :
  is_proposal γ (uint.nat term) decree -∗
  is_paxos_node px nid sc γ -∗
  {{{ True }}}
    Paxos__accept #px #term #(LitString decree)
  {{{ (ok : bool), RET #ok; if ok then node_accepted term decree nid γ else True }}}.
Proof.
  iIntros "#Hproposal #Hnode" (Φ) "!> _ HΦ".
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

  (*@     if px.learned {                                                     @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); first by eauto 15 with iFrame.
    wp_pures.
    by iApply "HΦ".
  }

  (*@     px.termc = std.SumAssumeNoOverflow(term, 1)                         @*)
  (*@     px.termp = term                                                     @*)
  (*@     px.decreep = decree                                                 @*)
  (*@                                                                         @*)
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hoverflow).
  do 3 wp_storeField.

  (*@     // Ghost action:                                                    @*)
  (*@     // Extending the ballot of this node with [false] to @term and append one @*)
  (*@     // [true] at index @term.                                           @*)
  (*@                                                                         @*)
  set accept := λ l, (extend false (uint.nat term) l) ++ [true].
  set blt' := accept blt.
  set R := (own_ballot γ nid blt' ∗ own_term γ nid (uint.nat term))%I.
  iAssert (|={⊤}=> R)%I with "[Hballot Hterm]" as "> [Hballot Hterm]".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (ballot_lookup with "Hballot Hbs") as %Hblt.
    iDestruct (proposal_lookup with "Hproposal Hps") as %Hpsl.
    iDestruct (term_lookup with "Hterm Hts") as %Htm.
    assert (Hprev : gt_prev_term ts nid (uint.nat term)).
    { exists (uint.nat termp). split; first done.
      assert (uint.nat termp < uint.nat termc)%nat.
      { rewrite -Hcurrent -Hlatest. apply latest_before_lt. lia. }
      lia.
    }
    iMod (ballot_update blt' with "Hballot Hbs") as "[Hballot Hbs]".
    { apply prefix_app_r, extend_prefix. }
    rewrite -lookup_alter_Some; last done.
    iMod (term_update (uint.nat term) with "Hterm Hts") as "[Hterm Hts]".
    unshelve epose proof (vb_inv_accept nid (uint.nat term) _ _ Hvbs) as Hvbs'.
    { done. }
    { exists blt. split; first done. lia. }
    pose proof (vp_inv_accept nid (uint.nat term) Hvps) as Hvps'.
    pose proof (vc_inv_accept nid (uint.nat term) Hvc) as Hvc'.
    pose proof (vt_inv_advance Hprev Hvts) as Hvts'.
    iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 20 with iFrame.
    by iFrame.
  }
  clear R.
  iDestruct (ballot_witness with "Hballot") as "#Hbltlb".

  (*@     px.mu.Unlock()                                                      @*)
  (*@                                                                         @*)
  wp_loadField.
  iClear "Hproposed".
  iAssert (is_proposal_nz γ (uint.nat term) decree)%I as "#Hproposed".
  { unfold is_proposal_nz. case_decide; done. }
  wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
  { do 5 iExists _. iFrame "∗ #".
    iPureIntro.
    replace (uint.nat (word.add _ _)) with (S (uint.nat term)) by word.
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
  rewrite /accepted_in lookup_app_r; last first.
  { rewrite extend_length. lia. }
  rewrite extend_length.
  by replace (_ - _)%nat with O by lia.
Qed.

Definition reached_quorum (sc n : nat) := sc / 2 < n.

Definition quorum_prepared
  (term : u64) (terml : u64) (decreel : string) (sc : nat) (γ : spaxos_names) : iProp Σ :=
  ∃ (bsqlb : gmap u64 ballot),
    "#Hlbs"      ∷ ([∗ map] x ↦ l ∈ bsqlb, is_ballot_lb γ x l) ∗
    "#Hproposal" ∷ is_proposal_nz γ (uint.nat terml) decreel ∗
    "%Hnprep"    ∷ ⌜reached_quorum sc (size (dom bsqlb))⌝ ∗
    "%Hlen"      ∷ ⌜map_Forall (λ _ l, ((uint.nat term) ≤ length l)%nat) bsqlb⌝ ∗
    "%Hlargest"  ∷ ⌜latest_before_quorum (uint.nat term) bsqlb = uint.nat terml⌝.

#[global]
Instance quorum_prepared_persistent term terml decree sc γ :
  Persistent (quorum_prepared term terml decree sc γ).
Proof. apply _. Qed.

Theorem wp_Paxos__accept__proposer
  {px : loc} {term : u64} {decree : string}
  (v : string) (terml : u64) decreel nid sc γ :
  is_term_of_node nid (uint.nat term) ->
  decree = (if decide (uint.nat terml = O) then v else decreel) ->
  (* (if decide (uint.nat terml = O) then True else decree = decreel) -> *)
  quorum_prepared term terml decreel sc γ -∗
  is_paxos_node px nid sc γ -∗
  {{{ True }}}
  <<< ∀∀ vs, own_candidates_half γ vs >>>
    Paxos__accept #px #term #(LitString decree) @ ↑spaxosN
  <<< own_candidates_half γ ({[v]} ∪ vs) >>>
  {{{ (ok : bool), RET #ok;
      if ok then node_accepted term decree nid γ ∗ is_proposal γ (uint.nat term) decree else True
  }}}.
Proof.
  iIntros "%Hofnode %Hdecree #Hprepares #Hnode" (Φ) "!> _ HAU".
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
    wp_apply (release_spec with "[-HAU $Hlock $Hlocked]"); first by eauto 15 with iFrame.
    wp_pures.
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod "HAU" as (vs) "[Hvs' HAU]".
    iNamed "HinvO".
    iDestruct (candidates_combine with "Hvs Hvs'") as "[Hvs ->]".
    iMod (candidates_update ({[v]} ∪ vs) with "Hvs") as "Hvs"; first set_solver.
    iDestruct (candidates_split with "Hvs") as "[Hvs Hvs']".
    iMod ("HAU" with "Hvs'") as "HΦ".
    assert (Hpic' : proposals_incl_candidates ({[v]} ∪ vs) ps).
    { unfold proposals_incl_candidates. set_solver. }
    iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 10 with iFrame.
    by iApply "HΦ".
  }

  (*@     if px.learned {                                                     @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[-HAU $Hlock $Hlocked]"); first by eauto 15 with iFrame.
    wp_pures.
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod "HAU" as (vs) "[Hvs' HAU]".
    iNamed "HinvO".
    iDestruct (candidates_combine with "Hvs Hvs'") as "[Hvs ->]".
    iMod (candidates_update ({[v]} ∪ vs) with "Hvs") as "Hvs"; first set_solver.
    iDestruct (candidates_split with "Hvs") as "[Hvs Hvs']".
    iMod ("HAU" with "Hvs'") as "HΦ".
    assert (Hpic' : proposals_incl_candidates ({[v]} ∪ vs) ps).
    { unfold proposals_incl_candidates. set_solver. }
    iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 10 with iFrame.
    by iApply "HΦ".
  }
  iClear "Hproposed".

  (*@     px.termc = std.SumAssumeNoOverflow(term, 1)                         @*)
  (*@     px.termp = term                                                     @*)
  (*@     px.decreep = decree                                                 @*)
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
  assert (Htermcp : (uint.nat termp < uint.nat termc)%nat).
  { rewrite -Hcurrent -Hlatest. apply latest_before_lt. lia. }
  assert (Htermorder : (uint.nat termp < uint.nat term)%nat) by lia.
  set P := (∀ ok : bool,
              (if ok
               then node_accepted term decree nid γ ∗ is_proposal γ (uint.nat term) decree
               else True) -∗ Φ #ok)%I.
  set R := (own_term γ nid (uint.nat term) ∗ P ∗ is_proposal γ (uint.nat term) decree)%I.
  iAssert (|NC={⊤}=> R)%I with "[Hterm HAU]" as "> (Hterm & HΦ & #Hproposal)".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (term_lookup with "Hterm Hts") as %Htermc.
    assert (Hprev : gt_prev_term ts nid (uint.nat term)).
    { exists (uint.nat termp). split; [done | word]. }
    pose proof (vt_impl_freshness Htermc Htermorder Hofnode Hvts) as Hfresh.
    iAssert (⌜valid_proposal bs ps (uint.nat term) decree⌝)%I as %Hvalid.
    { iNamed "Hprepares".
      iDestruct (ballots_prefix with "Hlbs Hbs") as "[%Hsubseteq %Hprefix]".
      unfold is_proposal_nz.
      iAssert (⌜if decide (uint.nat terml = O)
               then True
               else ps !! (uint.nat terml) = Some decree⌝)%I as %Hatterm.
      { case_decide; first done. rewrite Hdecree. by iApply proposal_lookup. }
      iPureIntro.
      set bsq := bs ∩ bsqlb.
      exists bsq.
      assert (Hdoms : dom bsq = dom bsqlb).
      { rewrite dom_intersection_L. set_solver. }
      split; first by apply map_intersection_subseteq.
      split.
      { rewrite Hdoms. unfold quorum_size. by rewrite Hdombs. }
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
      { by rewrite Hdoms. }
      case_decide as Hcase.
      - left. by rewrite Hcase in Hlargest.
      - right. by rewrite Hlargest.
    }
    iAssert (⌜uint.nat terml ≠ O -> ps !! (uint.nat terml) = Some decreel⌝)%I as %Hterml.
    { iNamed "Hprepares".
      unfold is_proposal_nz.
      destruct (decide (uint.nat terml = O)); first done.
      by iDestruct (proposal_lookup with "Hproposal Hps") as %Hgoal.
    }
    iMod (proposals_insert _ _ decree with "Hps") as "[Hps #Hp]"; first apply Hfresh.
    iMod (term_update (uint.nat term) with "Hterm Hts") as "[Hterm Hts]".
    assert (Htermnz : uint.nat term ≠ O) by lia.
    pose proof (vp_inv_propose Hfresh Htermnz Hvalid Hvps) as Hvps'.
    pose proof (vb_inv_propose (uint.nat term) decree Hvbs) as Hvbs'.
    pose proof (vc_inv_propose (uint.nat term) decree Hfresh Hvc) as Hvc'.
    pose proof (vt_inv_propose_advance decree Hprev Hofnode Hvts) as Hvts'.
    iMod "HAU" as (vs') "[Hvs' HAU]".
    iDestruct (candidates_combine with "Hvs Hvs'") as "[Hvs <-]".
    iMod (candidates_update ({[v]} ∪ vs) with "Hvs") as "Hvs"; first set_solver.
    iDestruct (candidates_split with "Hvs") as "[Hvs Hvs']".
    iMod ("HAU" with "Hvs'") as "HΦ".
    assert (Hpic' : proposals_incl_candidates ({[v]} ∪ vs) (<[uint.nat term:=decree]> ps)).
    { unfold proposals_incl_candidates.
      case_decide; subst decree.
      - (* Case: Adding [v] to [ps]. *)
        etransitivity; [apply map_img_insert_subseteq | set_solver].
      - (* Case: Adding [decreel] to [ps]. *)
        transitivity (map_img (SA:=gset string) ps); last by set_solver.
        specialize (Hterml H).
        clear -Hterml.
        etransitivity; first apply map_img_insert_subseteq.
        apply (elem_of_map_img_2 (SA:=gset string)) in Hterml.
        set_solver.
    }
    iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 10 with iFrame.
    by iFrame.
  }
  subst P. clear R.

  (*@     // Ghost action:                                                    @*)
  (*@     // Extending the ballot of this node with [false] to @term and append one @*)
  (*@     // [true] at index @term.                                           @*)
  (*@                                                                         @*)
  set accept := λ l, (extend false (uint.nat term) l) ++ [true].
  set blt' := accept blt.
  iAssert (|={⊤}=> own_ballot γ nid blt')%I with "[Hballot]" as "> Hballot".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (ballot_lookup with "Hballot Hbs") as %Hblt.
    iDestruct (proposal_lookup with "Hproposal Hps") as %Hpsl.
    iMod (ballot_update blt' with "Hballot Hbs") as "[Hballot Hbs]".
    { apply prefix_app_r, extend_prefix. }
    rewrite -lookup_alter_Some; last done.
    unshelve epose proof (vb_inv_accept nid (uint.nat term) _ _ Hvbs) as Hvbs'.
    { done. }
    { exists blt. split; first done. lia. }
    pose proof (vp_inv_accept nid (uint.nat term) Hvps) as Hvps'.
    pose proof (vc_inv_accept nid (uint.nat term) Hvc) as Hvc'.
    iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 20 with iFrame.
    by iFrame.
  }
  iDestruct (ballot_witness with "Hballot") as "#Hbltlb".

  (*@     px.mu.Unlock()                                                      @*)
  (*@                                                                         @*)
  wp_loadField.
  iAssert (is_proposal_nz γ (uint.nat term) decree)%I as "#Hproposed".
  { unfold is_proposal_nz. destruct (decide (uint.nat term = _)); done. }
  wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
  { do 5 iExists _. iFrame "∗ #".
    iPureIntro.
    replace (uint.nat (word.add _ _)) with (S (uint.nat term)) by word.
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
  rewrite /accepted_in lookup_app_r; last first.
  { rewrite extend_length. lia. }
  rewrite extend_length.
  by replace (_ - _)%nat with O by lia.
Qed.

Theorem wp_Paxos__major (px : loc) (n : u64) (sc : nat) (scu64 : u64) :
  uint.nat scu64 = sc ->
  readonly (px ↦[Paxos :: "sc"] #scu64) -∗
  {{{ True }}}
    Paxos__major #px #n
  {{{ (ok : bool), RET #ok; ⌜if ok then reached_quorum sc (uint.nat n) else True⌝ }}}.
Proof.
  iIntros "%Hscu64 #Hsc" (Φ) "!> _ HΦ".
  wp_call.

  (*@ func (px *Paxos) major(n uint64) bool {                                 @*)
  (*@     return n > px.sc / 2                                                @*)
  (*@ }                                                                       @*)
  wp_loadField. wp_pures.
  iApply "HΦ". iPureIntro.
  case_bool_decide as Hlt; last done.
  unfold reached_quorum.
  rewrite word.unsigned_divu_nowrap in Hlt; word.
Qed.

Lemma ite_apply (A B : Type) (b : bool) (f : A -> B) x y :
  (if b then f x else f y) = f (if b then x else y).
Proof. destruct b; done. Qed.

Theorem wp_Paxos__prepareAll (px : loc) (term terma : u64) (decreea : string) nid sc γ :
  node_prepared term terma decreea nid γ -∗
  is_paxos_comm px nid sc γ -∗
  {{{ True }}}
    Paxos__prepareAll #px #term #terma #(LitString decreea)
  {{{ (termp : u64) (decree : string) (ok : bool), RET (#termp, #(LitString decree), #ok);
      if ok then quorum_prepared term termp decree sc γ else True
  }}}.
Proof.
  iIntros "#Hprep #Hcomm" (Φ) "!> _ HΦ".
  wp_call.

  (*@ func (px *Paxos) prepareAll(term uint64) (uint64, string, bool) {       @*)
  (*@     var termLargest uint64                                              @*)
  (*@     var decreeLargest string                                            @*)
  (*@     var nPrepared uint64                                                @*)
  (*@                                                                         @*)
  wp_apply (wp_ref_to); first by auto.
  iIntros (termlRef) "HtermlRef".
  wp_apply (wp_ref_to); first by auto.
  iIntros (decreelRef) "HdecreelRef".
  wp_apply (wp_ref_to); first by auto.
  iIntros (nRef) "HnRef".
  wp_pures.

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
  iNamed "Hcomm".
  wp_loadField.
  iMod (readonly_load with "HpeersMR") as (q) "HpeersM".
  set P := (λ (m : gmap u64 loc),
    ∃ (terml : u64) (decreel : string) (n : u64) (bsqlb : gmap u64 ballot),
      "HtermlRef"   ∷ termlRef ↦[uint64T] #terml ∗
      "HdecreelRef" ∷ decreelRef ↦[stringT] #(str decreel) ∗
      "HnRef"  ∷ nRef ↦[uint64T] #n ∗
      "#Hlbs"  ∷ ([∗ map] x ↦ l ∈ bsqlb, is_ballot_lb γ x l) ∗
      "#Hpsl"  ∷ is_proposal_nz γ (uint.nat terml) decreel ∗
      (* [Hm], [Hdom] and [Hszpeers] in [is_paxos_comm] gives [size (dom bsqlb) ≤ max_nodes]. *)
      "%Hm"    ∷ ⌜m ⊆ peersM⌝ ∗
      (* [Hdom] gives [bsqlb !! nidpeer = None], where [nidpeer] is the nid of current iteration. *)
      "%Hdom"  ∷ ⌜dom bsqlb ⊆ {[ nid ]} ∪ dom m⌝ ∗
      "%Hlens" ∷ ⌜map_Forall (λ _ l, (uint.nat term ≤ length l)%nat) bsqlb⌝ ∗
      "%Hlq"   ∷ ⌜latest_before_quorum (uint.nat term) bsqlb = uint.nat terml⌝ ∗
      "%Hn"    ∷ ⌜size (dom bsqlb) = uint.nat n⌝)%I.
  wp_apply (wp_MapIter_fold _ _ _ P with "HpeersM [HtermlRef HdecreelRef HnRef]").
  { do 3 iExists _. iFrame.
    iNamed "Hprep".
    iExists {[ nid := l ]}.
    rewrite big_sepM_singleton.
    iFrame "#". iPureIntro.
    split; first by apply map_empty_subseteq.
    split; first set_solver.
    split; first by rewrite map_Forall_singleton.
    split.
    { unfold latest_before_quorum.
      rewrite map_fmap_singleton map_fold_singleton.
      unfold latest_before_quorum_step. lia.
    }
    rewrite dom_singleton size_singleton. word.
  }
  { clear Φ.
    iIntros (mdone nidpeer pxpeer Φ) "!> [HP [%Hdone %Hin]] HΦ". iNamed "HP".
    wp_pures.
    iDestruct (big_sepM_lookup with "Hpaxos") as "Hpeer"; first by apply Hin.
    wp_apply (wp_Paxos__prepare with "Hpeer").
    iClear "Hprep". iIntros (termpeer decreepeer ok) "Hprep".
    wp_pures.
    wp_if_destruct.
    { wp_load. wp_store. wp_load. wp_pures.
      wp_apply (wp_If_join_evar with "[HtermlRef HdecreelRef]").
      { iIntros (b Eqb).
        case_bool_decide.
        - wp_if_true. do 2 wp_store.
          iModIntro.
          iSplit; first done.
          replace #termpeer with #(if b then termpeer else terml) by by rewrite Eqb.
          replace #(LitString decreepeer) with
            #(if b then (LitString decreepeer) else (LitString decreel)) by by rewrite Eqb.
          iNamedAccu.
        - wp_if_false.
          iModIntro.
          iSplit; first done.
          rewrite Eqb. iFrame.
      }
      iIntros "H". iNamed "H".
      iApply "HΦ".
      do 2 rewrite ite_apply.
      set terml' := if (bool_decide _) then termpeer else _.
      set decreel' := if (bool_decide _) then decreepeer else _.
      do 3 iExists _. iFrame.
      iNamed "Hprep".
      iExists (<[nidpeer := l]> bsqlb).
      assert (Hnidpeer : bsqlb !! nidpeer = None).
      { clear -Hdom Hdone Hin Hnotin.
        assert (Hne : nid ≠ nidpeer).
        { apply elem_of_dom_2 in Hin. set_solver. }
        rewrite -not_elem_of_dom.
        rewrite -not_elem_of_dom in Hdone.
        set_solver.
      }
      iSplit.
      { rewrite big_sepM_insert; [by iFrame "#" | done]. }
      iSplit.
      { subst terml' decreel'. case_bool_decide; by iFrame "#". }
      iPureIntro.
      split; first by apply insert_subseteq_l.
      split; first set_solver.
      split; first by rewrite map_Forall_insert.
      split.
      { unfold latest_before_quorum.
        rewrite fmap_insert map_fold_insert_L; last first.
        { rewrite lookup_fmap. by rewrite Hnidpeer. }
        { unfold latest_before_quorum_step. lia. }
        unfold latest_before_quorum in Hlq. rewrite Hlq.
        unfold latest_before_quorum_step.
        subst terml'. case_bool_decide; lia.
      }
      rewrite dom_insert_L size_union; last first.
      { rewrite -not_elem_of_dom in Hnidpeer. set_solver. }
      rewrite size_singleton. rewrite Hn.
      assert (Hsz : (size (dom bsqlb) ≤ max_nodes)).
      { apply subseteq_size in Hdom.
        apply subseteq_dom in Hm.
        rewrite size_union in Hdom; last first.
        { rewrite disjoint_singleton_l. set_solver. }
        apply subseteq_size in Hm.
        rewrite size_singleton in Hdom.
        rewrite -size_dom in Hszpeers.
        clear -Hdom Hm Hszpeers.
        unfold max_nodes. unfold max_nodes in Hszpeers. lia.
      }
      unfold max_nodes in Hsz. word.
    }
    iApply "HΦ". do 4 iExists _. iFrame "∗ # %". iPureIntro.
    split; [by apply insert_subseteq_l | set_solver].
  }
  iIntros "[HpeersM HP]".
  wp_pures.

  (*@     // Did not reach a majority.                                        @*)
  (*@     if !px.major(nPrepared) {                                           @*)
  (*@         return 0, "", false                                             @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  iNamed "HP". clear P.
  wp_load.
  wp_apply (wp_Paxos__major with "Hsc"); first apply Hscu64.
  iIntros (ok Hquorum). rewrite -Hn in Hquorum.
  wp_if_destruct; wp_pures; first by iApply "HΦ".

  (*@     return termLargest, decreeLargest, true                             @*)
  (*@ }                                                                       @*)
  do 2 wp_load. wp_pures.
  iApply "HΦ".
  iExists _.
  by iFrame "∗ # %".
Qed.

Definition quorum_accepted (term : u64) (sc : nat) (γ : spaxos_names) : iProp Σ :=
  ∃ (bsqlb : gmap u64 ballot),
    "#Hlbs"    ∷ ([∗ map] x ↦ l ∈ bsqlb, is_ballot_lb γ x l) ∗
    "%Hnacpt " ∷ ⌜reached_quorum sc (size (dom bsqlb))⌝ ∗
    "%Haccin"  ∷ ⌜map_Forall (λ _ l, accepted_in l (uint.nat term)) bsqlb⌝.

#[global]
Instance quorum_accepted_persistent term sc γ :
  Persistent (quorum_accepted γ term sc).
Proof. apply _. Qed.

Theorem wp_Paxos__acceptAll (px : loc) (term : u64) (decree : string) nid sc γ :
  node_accepted term decree nid γ -∗
  is_proposal γ (uint.nat term) decree -∗
  is_paxos_comm px nid sc γ -∗
  {{{ True }}}
    Paxos__acceptAll #px #term #(LitString decree)
  {{{ (ok : bool), RET #ok; if ok then quorum_accepted term sc γ else True }}}.
Proof.
  iIntros "#Hacpt #Hpsl #Hcomm" (Φ) "!> _ HΦ".
  wp_call.

  (*@ func (px *Paxos) acceptAll(term uint64, decree string) bool {           @*)
  (*@     var nAccepted uint64 = 1                                            @*)
  (*@                                                                         @*)
  wp_apply (wp_ref_to); first by auto.
  iIntros (nRef) "HnRef".
  wp_pures.

  (*@     for _, peer := range(px.peers) {                                    @*)
  (*@         ok := peer.accept(term, decree)                                 @*)
  (*@         if ok {                                                         @*)
  (*@             nAccepted++                                                 @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  iNamed "Hcomm".
  wp_loadField.
  iMod (readonly_load with "HpeersMR") as (q) "HpeersM".
  set P := (λ (m : gmap u64 loc),
    ∃ (n : u64) (bsqlb : gmap u64 ballot),
      "HnRef"   ∷ nRef ↦[uint64T] #n ∗
      "#Hlbs"   ∷ ([∗ map] x ↦ l ∈ bsqlb, is_ballot_lb γ x l) ∗
      (* [Hm], [Hdom] and [Hszpeers] in [is_paxos_comm] gives [size (dom bsqlb) ≤ max_nodes]. *)
      "%Hm"     ∷ ⌜m ⊆ peersM⌝ ∗
      (* [Hdom] gives [bsqlb !! nidpeer = None], where [nidpeer] is the nid of current iteration. *)
      "%Hdom"   ∷ ⌜dom bsqlb ⊆ {[ nid ]} ∪ dom m⌝ ∗
      "%Haccin" ∷ ⌜map_Forall (λ _ l, accepted_in l (uint.nat term)) bsqlb⌝ ∗
      "%Hn"     ∷ ⌜size (dom bsqlb) = uint.nat n⌝)%I.
  wp_apply (wp_MapIter_fold _ _ _ P with "HpeersM [HnRef]").
  { iExists _. iFrame.
    iNamed "Hacpt".
    iExists {[ nid := l ]}.
    rewrite big_sepM_singleton.
    iFrame "#". iPureIntro.
    split; first by apply map_empty_subseteq.
    split; first set_solver.
    split; first by rewrite map_Forall_singleton.
    rewrite dom_singleton size_singleton. word.
  }
  { clear Φ.
    iIntros (mdone nidpeer pxpeer Φ) "!> [HP [%Hdone %Hin]] HΦ". iNamed "HP".
    wp_pures.
    iDestruct (big_sepM_lookup with "Hpaxos") as "Hpeer"; first by apply Hin.
    wp_apply (wp_Paxos__accept with "Hpsl Hpeer").
    iClear "Hacpt". iIntros (ok) "Hacpt".
    wp_pures.
    wp_if_destruct.
    { wp_load. wp_store.
      iApply "HΦ".
      iExists _. iFrame.
      iNamed "Hacpt".
      iExists (<[nidpeer := l]> bsqlb).
      assert (Hnidpeer : bsqlb !! nidpeer = None).
      { clear -Hdom Hdone Hin Hnotin.
        assert (Hne : nid ≠ nidpeer).
        { apply elem_of_dom_2 in Hin. set_solver. }
        rewrite -not_elem_of_dom.
        rewrite -not_elem_of_dom in Hdone.
        set_solver.
      }
      iModIntro.
      iSplit.
      { rewrite big_sepM_insert; [by iFrame "#" | done]. }
      iPureIntro.
      split; first by apply insert_subseteq_l.
      split; first set_solver.
      split; first by rewrite map_Forall_insert.
      rewrite dom_insert_L size_union; last first.
      { rewrite -not_elem_of_dom in Hnidpeer. set_solver. }
      rewrite size_singleton. rewrite Hn.
      assert (Hsz : (size (dom bsqlb) ≤ max_nodes)).
      { apply subseteq_size in Hdom.
        apply subseteq_dom in Hm.
        rewrite size_union in Hdom; last first.
        { rewrite disjoint_singleton_l. set_solver. }
        apply subseteq_size in Hm.
        rewrite size_singleton in Hdom.
        rewrite -size_dom in Hszpeers.
        clear -Hdom Hm Hszpeers.
        unfold max_nodes. unfold max_nodes in Hszpeers. lia.
      }
      unfold max_nodes in Hsz. word.
    }
    iApply "HΦ". do 2 iExists _. iFrame "∗ # %". iPureIntro.
    split; [by apply insert_subseteq_l | set_solver].
  }
  iIntros "[HpeersM HP]".
  wp_pures.

  (*@     return px.major(nAccepted)                                          @*)
  (*@ }                                                                       @*)
  iNamed "HP". clear P.
  wp_load.
  wp_apply (wp_Paxos__major with "Hsc"); first apply Hscu64.
  iIntros (ok Hquorum). rewrite -Hn in Hquorum.
  iApply "HΦ".
  destruct ok; last done.
  iExists _.
  by iFrame "∗ # %".
Qed.

Theorem wp_Paxos__learn (px : loc) (term : u64) (decree : string) nid sc γ :
  is_proposal γ (uint.nat term) decree -∗
  is_chosen_commitment γ decree -∗
  is_paxos_node px nid sc γ -∗
  {{{ True }}}
    Paxos__learn #px #term #(LitString decree)
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hproposal #Hchosen #Hnode" (Φ) "!> _ HΦ".
  wp_call.

  (*@ func (px *Paxos) learn(term uint64, decree string) {                    @*)
  (*@     px.mu.Lock()                                                        @*)
  (*@                                                                         @*)
  iNamed "Hnode".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HpaxosOwn]".
  wp_pures.

  (*@     if term < px.termc {                                                @*)
  (*@         px.mu.Unlock()                                                  @*)
  (*@         return                                                          @*)
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
  (*@     px.decreep = decree                                                 @*)
  (*@     px.learned = true                                                   @*)
  (*@                                                                         @*)
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hoverflow).
  do 4 wp_storeField.

  (*@     // Ghost action:                                                    @*)
  (*@     // Extending the ballot of this node with [false] to @term and append one @*)
  (*@     // [true] at index @term.                                           @*)
  (*@                                                                         @*)
  set accept := λ l, (extend false (uint.nat term) l) ++ [true].
  set blt' := accept blt.
  set R := (own_ballot γ nid blt' ∗ own_term γ nid (uint.nat term))%I.
  iAssert (|={⊤}=> R)%I with "[Hballot Hterm]" as "> [Hballot Hterm]".
  { iInv "Hinv" as ">HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (ballot_lookup with "Hballot Hbs") as %Hblt.
    iDestruct (proposal_lookup with "Hproposal Hps") as %Hpsl.
    iDestruct (term_lookup with "Hterm Hts") as %Htm.
    assert (Hprev : gt_prev_term ts nid (uint.nat term)).
    { exists (uint.nat termp). split; first done.
      assert (uint.nat termp < uint.nat termc)%nat.
      { rewrite -Hcurrent -Hlatest. apply latest_before_lt. lia. }
      lia.
    }
    iMod (ballot_update blt' with "Hballot Hbs") as "[Hballot Hbs]".
    { apply prefix_app_r, extend_prefix. }
    rewrite -lookup_alter_Some; last done.
    iMod (term_update (uint.nat term) with "Hterm Hts") as "[Hterm Hts]".
    unshelve epose proof (vb_inv_accept nid (uint.nat term) _ _ Hvbs) as Hvbs'.
    { done. }
    { exists blt. split; first done. lia. }
    pose proof (vp_inv_accept nid (uint.nat term) Hvps) as Hvps'.
    pose proof (vc_inv_accept nid (uint.nat term) Hvc) as Hvc'.
    pose proof (vt_inv_advance Hprev Hvts) as Hvts'.
    iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 20 with iFrame.
    by iFrame.
  }
  clear R.
  iDestruct (ballot_witness with "Hballot") as "#Hbltlb".

  (*@     px.mu.Unlock()                                                      @*)
  (*@ }                                                                       @*)
  wp_loadField.
  iClear "Hproposed".
  iAssert (is_proposal_nz γ (uint.nat term) decree)%I as "#Hproposed".
  { unfold is_proposal_nz. case_decide; done. }
  wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]").
  { do 5 iExists _. iFrame "∗ #".
    iPureIntro.
    replace (uint.nat (word.add _ _)) with (S (uint.nat term)) by word.
    split; first done.
    split.
    { rewrite last_length extend_length. lia. }
    rewrite latest_term_snoc_true extend_length.
    lia.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

Theorem wp_Paxos__learnAll (px : loc) (term : u64) (decree : string) nid sc γ :
  is_proposal γ (uint.nat term) decree -∗
  is_chosen_commitment γ decree -∗
  is_paxos_comm px nid sc γ -∗
  {{{ True }}}
    Paxos__learnAll #px #term #(LitString decree)
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hproposal #Hchosen #Hcomm" (Φ) "!> _ HΦ".
  wp_call.

  (*@ func (px *Paxos) learnAll(term uint64, decree string) {                 @*)
  (*@     for _, peer := range(px.peers) {                                    @*)
  (*@         peer.learn(term, decree)                                        @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)
  iNamed "Hcomm".
  wp_loadField.
  iMod (readonly_load with "HpeersMR") as (q) "HpeersM".
  wp_apply (wp_MapIter_fold _ _ _ (λ _, True)%I with "HpeersM").
  { clear Φ.
    iIntros (mdone nidpeer pxpeer Φ) "!> [HP [_ %Hin]] HΦ". clear mdone.
    wp_pures.
    iDestruct (big_sepM_lookup with "Hpaxos") as "Hpeer"; first by apply Hin.
    wp_apply (wp_Paxos__learn with "Hproposal Hchosen Hpeer").
    by iApply "HΦ".
  }
  iIntros "_".
  wp_pures.
  by iApply "HΦ".
Qed.

End temp.

Section prog.
Context `{!heapGS Σ, !spaxos_ghostG Σ}.

Theorem wp_Paxos__Propose (px : loc) (v : string) nid sc γ :
  is_paxos px nid sc γ -∗
  {{{ True }}}
  <<< ∀∀ vs, own_candidates_half γ vs >>>
    Paxos__Propose #px #(LitString v) @ ↑spaxosN
  <<< own_candidates_half γ ({[v]} ∪ vs) >>>
  (* The return value serves as a hint to whether the user should immediately retry. *)
  {{{ (ok : bool), RET #ok; True }}}.
Proof.
  iIntros "#Hpaxos !>" (Φ) "_ HAU".
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
  wp_apply (wp_Paxos__prepareAll with "Hprep Hcomm").
  iIntros (terml decreel prepared) "Hprepq".
  wp_pures.
  
  (*@     if !prepared {                                                      @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct.
  { iNamed "Hnode".
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod "HAU" as (vs) "[Hvs' HAU]".
    iNamed "HinvO".
    iDestruct (candidates_combine with "Hvs Hvs'") as "[Hvs ->]".
    iMod (candidates_update ({[v]} ∪ vs) with "Hvs") as "Hvs"; first set_solver.
    iDestruct (candidates_split with "Hvs") as "[Hvs Hvs']".
    iMod ("HAU" with "Hvs'") as "HΦ".
    assert (Hpic' : proposals_incl_candidates ({[v]} ∪ vs) ps).
    { unfold proposals_incl_candidates. set_solver. }
    iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 10 with iFrame.
    by iApply "HΦ".
  }

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
  wp_apply (wp_Paxos__accept__proposer v with "Hprepq Hnode"); first done.
  { case_bool_decide.
    { case_decide; first done.
      inversion H as [Hterml]. subst terml.
      by replace (uint.nat (W64 0)) with O by word.
    }
    { case_decide; last done.
      replace terml with (W64 0) in H by word. done.
    }
  }
  iMod "HAU" as (vs) "[Hvs HAU]".
  iModIntro. iExists vs. iFrame.
  iIntros "Hvs".
  iMod ("HAU" with "Hvs") as "HΦ". iModIntro.
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
  wp_apply (wp_Paxos__acceptAll with "Hacpt Hpsl Hcomm").
  iIntros (accepted) "Hacptq".
  wp_pures.

  (*@     if !accepted {                                                      @*)
  (*@         return !helping                                                 @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct.
  { wp_load. wp_pures.
    case_bool_decide; by iApply "HΦ".
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
  iAssert (|={⊤}=> is_chosen_commitment γ decree)%I as "> #Hcommitment".
  { iNamed "Hnode".
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    rename v0 into c'.
    iAssert (⌜chosen bs ps decree⌝)%I as %Hchosen.
    { iNamed "Hacptq".
      iDestruct (ballots_prefix with "Hlbs Hbs") as "[%Hsubseteq %Hprefix]".
      iDestruct (proposal_lookup with "Hpsl Hps") as %Hatterm.
      iPureIntro.
      exists (uint.nat term).
      split; first done.
      split; first apply Hatterm.
      set bsq := bs ∩ bsqlb.
      exists bsq.
      assert (Hdoms : dom bsq = dom bsqlb).
      { rewrite dom_intersection_L. set_solver. }
      split; first by apply map_intersection_subseteq.
      split.
      { rewrite Hdoms. unfold quorum_size. by rewrite Hdombs. }
      intros x b Hxb.
      rewrite lookup_intersection_Some in Hxb.
      destruct Hxb as [Hb [blb Hblb]].
      specialize (Hprefix _ _ _ Hblb Hb).
      apply Haccin in Hblb.
      unfold accepted_in.
      eapply prefix_lookup_Some; [done | apply Hprefix].
    }
    iAssert (|==> own_commitment γ (Chosen decree))%I with "[Hc]" as "Hc".
    { destruct c as [decree' |] eqn:Ec.
      - (* Case [Chosen decree']. *)
        unfold valid_commitment in Hvc.
        pose proof (vb_vp_impl_consistency Hvbs Hvps) as Hconsistency.
        rewrite (Hconsistency _ _ Hvc Hchosen).
        by iFrame.
      - (* Case [Free]. *)
        iMod (commitment_update decree with "Hc") as "Hc".
        by iFrame.
    }
    iMod "Hc".
    iDestruct (commitment_witness with "Hc") as "#Hcommitment".
    assert (Hcic' : consented_impl_committed c' (Chosen decree)).
    { destruct c' as [v' |]; last done.
      simpl in Hcic. subst c. simpl in Hvc.
      pose proof (vb_vp_impl_consistency Hvbs Hvps) as Hconsistency.
      by rewrite (Hconsistency _ _ Hvc Hchosen).
    }
    by iMod ("HinvC" with "[Hv Hvs Hc Hbs Hps Hts]") as "_"; first by eauto 10 with iFrame.
  }

  (*@     // Phase 3.                                                         @*)
  (*@     // Goal of this phase is to broadcast the consensus to other nodes. @*)
  (*@     px.learn(decree)                                                    @*)
  (*@     px.learnAll(decree)                                                 @*)
  (*@                                                                         @*)
  wp_load.
  wp_apply (wp_Paxos__learn with "Hpsl Hcommitment Hnode").
  wp_pures. wp_load.
  wp_apply (wp_Paxos__learnAll with "Hpsl Hcommitment Hcomm").
  wp_pures.

  (*@     // If @helping is true, return false since we're merely helping an early @*)
  (*@     // proposal go through, rather than proposing our own value @v.     @*)
  (*@     return !helping                                                     @*)
  (*@ }                                                                       @*)
  wp_load. wp_pures.
  case_bool_decide; by iApply "HΦ".
Qed.

End prog.
