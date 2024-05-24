From iris.bi.lib Require Import fractional.
From Perennial.base_logic.lib Require Import mono_nat.

From RecordUpdate Require Import RecordSet.

From Goose.github_com.mit_pdos.go_journal Require Import wal.

From Perennial.Helpers Require Import List Transitions.
From Perennial.program_proof Require Import disk_prelude disk_lib.
From Perennial.program_proof Require Import wal.lib.
From Perennial.program_proof Require Import marshal_block util_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

#[global]
Existing Instance r_mbind.

Module circΣ.
  Record t :=
    mk { upds: list update.t;
         start: u64;
       }.
  Global Instance _eta: Settable _ := settable! mk <upds; start>.
  Global Instance _witness: Inhabited t := populate!.
  Definition diskEnd (s:t): Z :=
    uint.Z s.(start) + Z.of_nat (length s.(upds)).
End circΣ.

Notation start := circΣ.start.
Notation upds := circΣ.upds.

Definition circ_read : transition circΣ.t (list update.t * u64) :=
  s ← reads (fun x => (upds x, start x));
  ret s.

Definition circ_advance (newStart : u64) : transition circΣ.t unit :=
  modify (fun σ => set upds (drop (Z.to_nat (uint.Z newStart - uint.Z σ.(start))%Z)) σ);;
  modify (set start (fun _ => newStart)).

Definition circ_append (l : list update.t) (endpos : u64) : transition circΣ.t unit :=
  modify (set circΣ.upds (fun u => u ++ l)).

Class circG Σ : Set :=
  { circ_list_u64 :> ghost_varG Σ (list u64);
    circ_list_block :> ghost_varG Σ (list Block);
    circ_mono_nat :> mono_natG Σ;
    circ_stagedG :> stagedG Σ;
  }.

Definition circΣ : gFunctors :=
  #[ghost_varΣ (list u64); ghost_varΣ (list Block); mono_natΣ; stagedΣ].

#[global]
Instance subG_circΣ Σ : subG circΣ Σ → circG Σ.
Proof. solve_inG. Qed.

Section heap.
Context `{!heapGS Σ}.
Context `{!circG Σ}.

Context (N: namespace).
Context (P: circΣ.t -> iProp Σ).

Record circ_names : Set :=
  { addrs_name: gname;
    blocks_name: gname;
    start_name: gname;
    diskEnd_name: gname; }.
Global Instance circ_names_inhabited : Inhabited circ_names := populate!.

Implicit Types (γ:circ_names).

Definition start_at_least γ (startpos: u64) :=
  mono_nat_lb_own γ.(start_name) (uint.nat startpos).

Definition start_is γ (q:Qp) (startpos: u64) :=
  mono_nat_auth_own γ.(start_name) q (uint.nat startpos).

Definition diskEnd_at_least γ (endpos: Z) :=
  mono_nat_lb_own γ.(diskEnd_name) (Z.to_nat endpos).

Definition diskEnd_is γ (q:Qp) (endpos: Z): iProp Σ :=
  ⌜0 <= endpos < 2^64⌝ ∗ mono_nat_auth_own γ.(diskEnd_name) q (Z.to_nat endpos) ∗
  diskEnd_at_least γ endpos.

Definition is_low_state (startpos endpos : u64) (addrs: list u64) (blocks : list Block) : iProp Σ :=
  ∃ hdr1 hdr2,
    ⌜block_encodes hdr1 ([EncUInt64 endpos] ++ (map EncUInt64 addrs))⌝ ∗
    ⌜block_encodes hdr2 [EncUInt64 startpos]⌝ ∗
    0 d↦ hdr1 ∗
    1 d↦ hdr2 ∗
    2 d↦∗ blocks.

Definition circ_wf (σ: circΣ.t) :=
  let start: Z := uint.Z σ.(start) in
  let endpos: Z := circΣ.diskEnd σ in
  start <= endpos <= start + LogSz ∧
  start + length σ.(upds) < 2^64 ∧
  length σ.(upds) <= LogSz.

Definition has_circ_updates σ (addrs: list u64) (blocks: list Block) :=
  forall (i: nat),
    let off := Z.to_nat ((uint.Z σ.(circΣ.start) + i) `mod` LogSz) in
    forall u, σ.(circΣ.upds) !! i = Some u ->
         addrs !! off = Some (update.addr u) ∧
         blocks !! off = Some (update.b u).

Definition circ_low_wf (addrs: list u64) (blocks: list Block) :=
  Z.of_nat (length addrs) = LogSz ∧
  Z.of_nat (length blocks) = LogSz.

Definition circ_own γ (addrs: list u64) (blocks: list Block): iProp Σ :=
  ⌜circ_low_wf addrs blocks⌝ ∗
  ghost_var γ.(addrs_name) (1/2) addrs ∗
  ghost_var γ.(blocks_name) (1/2) blocks.

Definition circ_own_dup γ (addrs: list u64) (blocks: list Block): iProp Σ :=
  ∃ q,
  ⌜circ_low_wf addrs blocks⌝ ∗
  ghost_var γ.(addrs_name) q addrs ∗
  ghost_var γ.(blocks_name) q blocks.

Lemma circ_own_dup_agree γ addrs1 addrs2 blocks1 blocks2 :
  circ_own_dup γ addrs1 blocks1 -∗
  circ_own_dup γ addrs2 blocks2 -∗
  ⌜ addrs1 = addrs2 ∧ blocks1 = blocks2 ⌝.
Proof.
  iIntros "Hown1 Hown2".
  iDestruct "Hown1" as (q1 Hwf1) "(Haddrs1&Hblocks1)".
  iDestruct "Hown2" as (q2 Hwf2) "(Haddrs2&Hblocks2)".
  iDestruct (ghost_var_agree with "Haddrs1 Haddrs2") as %->.
  iDestruct (ghost_var_agree with "Hblocks1 Hblocks2") as %->.
  eauto.
Qed.

Theorem circ_state_wf γ addrs blocks :
  circ_own γ addrs blocks -∗ ⌜circ_low_wf addrs blocks⌝.
Proof. iIntros "[% _] //". Qed.

Definition circ_positions γ σ: iProp Σ :=
  start_is γ (1/2) (circΣ.start σ) ∗
  diskEnd_is γ (1/2) (circΣ.diskEnd σ).

Definition circ_positions_dup γ σ: iProp Σ :=
  ∃ q,
  start_is γ q (circΣ.start σ) ∗
  diskEnd_is γ q (circΣ.diskEnd σ).

Theorem start_is_to_eq γ σ q startpos :
  circ_positions γ σ -∗
  start_is γ q startpos -∗
  ⌜start σ = startpos⌝.
Proof.
  iIntros "[Hstart1 _] Hstart2".
  rewrite /start_is.
  iDestruct (mono_nat_auth_own_agree with "Hstart1 Hstart2") as %[_ Heq].
  iPureIntro.
  word.
Qed.

Theorem start_at_least_to_le γ σ startpos :
  circ_positions γ σ -∗
  start_at_least γ startpos -∗
  ⌜uint.Z startpos <= uint.Z (start σ)⌝.
Proof.
  iIntros "[Hstart1 _] Hstart2".
  rewrite /start_is.
  iDestruct (mono_nat_lb_own_valid with "Hstart1 Hstart2") as %[_ Hlt].
  iPureIntro.
  word.
Qed.

Theorem start_is_to_at_least (γ: circ_names) (x: u64) q :
  start_is γ q x -∗ start_at_least γ x.
Proof.
  iIntros "H".
  iDestruct (mono_nat_lb_own_get with "H") as "#Hlb".
  auto with iFrame.
Qed.

Instance diskEnd_fractional γ endpos : Fractional (λ q, diskEnd_is γ q endpos).
Proof.
  intros p q.
  iSplit.
  - iIntros "[% [Hend #Hatleast]]".
    iDestruct "Hend" as "[Hend1 Hend2]".
    iFrame "# % Hend1 Hend2".
  - iIntros "[[% [Hend1 #Hatleast]] [% [Hend2 #Hatleast2]]]".
    iCombine "Hend1 Hend2" as "$".
    iFrame "Hatleast".
    iPureIntro; auto.
Qed.

Instance diskEnd_as_fractional γ q endpos :
  AsFractional (diskEnd_is γ q endpos) (λ q, diskEnd_is γ q endpos) q.
Proof. split; first by done. apply _. Qed.

Theorem diskEnd_is_to_eq γ σ q endpos :
  circ_positions γ σ -∗
  diskEnd_is γ q endpos -∗
  ⌜circΣ.diskEnd σ = endpos⌝.
Proof.
  iIntros "[_ Hend1] Hend2".
  iDestruct "Hend1" as "[_ [Hend1 _]]".
  iDestruct "Hend2" as "[% [Hend2 _]]".
  iDestruct (mono_nat_auth_own_agree with "Hend1 Hend2") as %[_ Heq].
  iPureIntro.
  rewrite /circΣ.diskEnd in H, Heq |- *.
  word.
Qed.

Theorem diskEnd_at_least_mono (γ: circ_names) (lb1 lb2: Z) :
  lb1 ≤ lb2 ->
  diskEnd_at_least γ lb2 -∗
  diskEnd_at_least γ lb1.
Proof.
  rewrite /diskEnd_at_least.
  iIntros (Hle) "Hlb".
  iApply (mono_nat_lb_own_le with "Hlb").
  word.
Qed.

Theorem diskEnd_is_to_at_least (γ: circ_names) (x: Z) q :
  diskEnd_is γ q x -∗
  diskEnd_at_least γ x.
Proof.
  rewrite /diskEnd_is.
  iIntros "[% [_ H]]". iFrame.
Qed.

Theorem diskEnd_at_least_to_le γ σ endpos_lb :
  circ_positions γ σ -∗
  diskEnd_at_least γ endpos_lb -∗
  ⌜endpos_lb ≤ circΣ.diskEnd σ ⌝.
Proof.
  iIntros "[_ Hend1] Hend_lb".
  iDestruct "Hend1" as "[% [Hend1 _]]".
  rewrite /diskEnd_is /diskEnd_at_least.
  iDestruct (mono_nat_lb_own_valid with "Hend1 Hend_lb") as %[_ Hlt].
  iPureIntro.
  rewrite /circΣ.diskEnd in H, Hlt |- *.
  word.
Qed.

(* Normal representation predicate (state interpretation) *)
Definition is_circular_state γ (σ : circΣ.t) : iProp Σ :=
  ⌜circ_wf σ⌝ ∗
   circ_positions γ σ ∗
  ∃ (addrs: list u64) (blocks: list Block),
    ⌜has_circ_updates σ addrs blocks⌝ ∗
    circ_own γ addrs blocks ∗
    is_low_state σ.(start) (circΣ.diskEnd σ) addrs blocks.

(* Precondition for recovery *)
Definition is_circular_state_pre_rec γ σ : iProp Σ :=
  ⌜circ_wf σ⌝ ∗
   circ_positions γ σ ∗
  ∃ (addrs: list u64) (blocks: list Block),
    ⌜has_circ_updates σ addrs blocks⌝ ∗
    circ_own_dup γ addrs blocks ∗
    is_low_state σ.(start) (circΣ.diskEnd σ) addrs blocks.

(* "Crash" state interpretation *)
Definition is_circular_state_crash γ σ : iProp Σ :=
  ⌜circ_wf σ⌝ ∗
   circ_positions_dup γ σ ∗
  ∃ (addrs: list u64) (blocks: list Block),
    ⌜has_circ_updates σ addrs blocks⌝ ∗
    circ_own_dup γ addrs blocks.

Definition circular_crash_ghost_exchange (γold γnew : circ_names) : iProp Σ := True%I.
(*
  ∃ (addrs : list u64) (blocks: list Block) start dend,
  ((ghost_var γold.(addrs_name) (1/2) addrs ∗ ghost_var γold.(blocks_name) (1/2) blocks) ∨
   (ghost_var γnew.(addrs_name) (1/2) addrs ∗ ghost_var γnew.(blocks_name) (1/2) blocks)) ∗
  (start_is γold (1/2) start ∨ start_is γnew (1/2) start) ∗
  (diskEnd_is γold (1/2) dend ∨ diskEnd_is γnew (1/2) dend).
*)

Definition is_circular γ : iProp Σ :=
  ncinv N (∃ σ, is_circular_state γ σ ∗ P σ).

Definition is_circular_appender γ (circ: loc) : iProp Σ :=
  ∃ s (addrs : list u64) (blocks: list Block),
    ⌜circ_low_wf addrs blocks⌝ ∗
    ghost_var γ.(addrs_name) (1/2) addrs ∗
    ghost_var γ.(blocks_name) (1/2) blocks ∗
    circ ↦[circularAppender :: "diskAddrs"] (slice_val s) ∗
    own_slice_small s uint64T (DfracOwn 1) addrs.

Definition init_ghost_state γ :=
  ("Haddrs'" ∷ ghost_var γ.(addrs_name) 1 ([] : list u64) ∗
  "Hblocks'" ∷ ghost_var γ.(blocks_name) 1 ([] : list Block) ∗
  "Hstart1" ∷ mono_nat_auth_own γ.(start_name) 1 0 ∗
  "HdiskEnd1" ∷ mono_nat_auth_own γ.(diskEnd_name) 1 0)%I.

Lemma alloc_init_ghost_state :
  ⊢ |==> ∃ γnew, init_ghost_state γnew.
Proof.
  iMod (ghost_var_alloc ([] : list u64)) as (addrs_name') "Haddrs'".
  iMod (ghost_var_alloc ([] : list Block)) as (blocks_name') "Hblocks'".
  iMod (mono_nat_own_alloc O) as (start_name') "[Hstart1 _]".
  iMod (mono_nat_own_alloc O) as (diskEnd_name') "[HdiskEnd1 _]".
  set (γnew := {| addrs_name := addrs_name';
                blocks_name := blocks_name';
                start_name := start_name';
                diskEnd_name := diskEnd_name'; |}).
  iExists γnew.
  by iFrame.
Qed.

Definition is_circular_appender_pre γ : iProp Σ :=
  ∃ addrs blocks,
    ⌜circ_low_wf addrs blocks⌝ ∗
    ghost_var γ.(addrs_name) (1/2) addrs ∗ ghost_var γ.(blocks_name) (1/2) blocks.

Definition circ_resources γ σ : iProp Σ :=
  start_is γ (1/2) (circΣ.start σ) ∗
  diskEnd_is γ (1/2) (circΣ.diskEnd σ) ∗
  is_circular_appender_pre γ.

Lemma crash_upd γold γnew σ :
  is_circular_state γold σ -∗ init_ghost_state γnew ==∗
  is_circular_state γnew σ ∗
  circ_resources γnew σ ∗
  is_circular_state_crash γold σ ∗
  circular_crash_ghost_exchange γold γnew.
Proof.
  iStartProof.

  iIntros "Hcs". iNamed 1.

  iDestruct "Hcs" as (Hwf) "[Hpos Hcs]".
  iDestruct "Hcs" as (addrs0 blocks0 Hupds) "(Hown & Hlow)".
  iDestruct "Hown" as (Hlow_wf) "[Haddrs Hblocks]".
  iDestruct "Hpos" as "(Hstart&%&Hend&Hend_at_least)".

  iMod (ghost_var_update addrs0 with "Haddrs'") as "[Haddrs' Hγaddrs]".
  iMod (ghost_var_update blocks0 with "Hblocks'") as "[Hblocks' Hγblocks]".
  iMod (mono_nat_own_update (uint.nat σ.(start)) with "Hstart1") as "[[Hstart1 Hstart2] _]".
  { lia. }
  iMod (mono_nat_own_update (Z.to_nat (circΣ.diskEnd σ)) with "HdiskEnd1") as "[[HdiskEnd1 HdiskEnd2] #HdiskEnd_lb]".
  { lia. }

  iSplitL "Haddrs' Hblocks' Hstart1 HdiskEnd1 Hlow".
  { iModIntro.
    rewrite /is_circular_state.
    iSplitR; first eauto.
    rewrite /circ_positions.
    iFrame "Hstart1 HdiskEnd1".
    iSplitR; first eauto.
    iExists _, _. iFrame. eauto.
  }
  iSplitL "Hstart2 HdiskEnd2 Hγaddrs Hγblocks".
  { iFrame "∗#". eauto. }
  iSplitL "Haddrs Hblocks Hstart Hend Hend_at_least".
  { iModIntro.
    rewrite /is_circular_state_crash.
    iSplitR; first eauto.
    rewrite /circ_positions_dup.
    iSplitL "Hstart Hend Hend_at_least".
    { iExists (1/2)%Qp. iFrame. eauto. }
    iExists _, _.
    iSplitR; first eauto.
    rewrite /circ_own_dup.
    iExists (1/2)%Qp. iFrame. eauto.
  }
  eauto.
Qed.

Lemma is_circular_state_wf γ σ :
  is_circular_state γ σ -∗ ⌜ circ_wf σ ⌝.
Proof. iDestruct 1 as "($&_)". Qed.

Lemma diskEnd_is_agree γ q1 q2 endpos1 endpos2 :
  diskEnd_is γ q1 endpos1 -∗
  diskEnd_is γ q2 endpos2 -∗
  ⌜endpos1 = endpos2⌝.
Proof.
  iIntros "[% [Hend1 _]] [% [Hend2 _]]".
  iDestruct (mono_nat_auth_own_agree with "Hend1 Hend2") as %[_ Heq].
  iPureIntro.
  word.
Qed.

Lemma diskEnd_is_agree_2 γ q endpos lb :
  diskEnd_is γ q endpos -∗
  diskEnd_at_least γ lb -∗
  ⌜lb ≤ endpos ⌝.
Proof.
  iIntros "[% [Hend _]] Hlb".
  iDestruct (mono_nat_lb_own_valid with "Hend Hlb") as %[_ Hlb].
  iPureIntro.
  word.
Qed.

Lemma start_is_agree γ q1 q2 startpos1 startpos2 :
  start_is γ q1 startpos1 -∗
  start_is γ q2 startpos2 -∗
  ⌜startpos1 = startpos2⌝.
Proof.
  iIntros "Hstart1 Hstart2".
  iDestruct (mono_nat_auth_own_agree with "Hstart1 Hstart2") as %[_ Heq].
  iPureIntro.
  word.
Qed.

Lemma start_is_agree_2 γ q startpos lb :
  start_is γ q startpos -∗
  start_at_least γ lb -∗
  ⌜uint.Z lb ≤ uint.Z startpos ⌝.
Proof.
  iIntros "Hstart Hlb".
  iDestruct (mono_nat_lb_own_valid with "Hstart Hlb") as %[_ Hlb].
  iPureIntro.
  word.
Qed.

Global Instance is_circular_state_timeless γ σ :
  Timeless (is_circular_state γ σ) := _.

Global Instance is_circular_state_discretizable γ σ:
  Discretizable (is_circular_state γ σ).
Proof. apply _. Qed.

Theorem is_circular_state_pos_acc γ σ :
  is_circular_state γ σ -∗
    circ_positions γ σ  ∗
    (circ_positions γ σ -∗ is_circular_state γ σ).
Proof.
  iIntros "His_circ".
  iDestruct "His_circ" as "(%Hwf&$&Hrest)"; iIntros "Hpos".
  iFrame "∗%".
Qed.

Theorem is_circular_inner_wf γ addrs blocks σ :
  ghost_var γ.(addrs_name) (1/2) addrs ∗
  ghost_var γ.(blocks_name) (1/2) blocks -∗
  is_circular_state γ σ -∗
  ⌜circ_low_wf addrs blocks⌝.
Proof.
  iIntros "[Hγaddrs Hγblocks] [_ His_circ]".
  iDestruct "His_circ" as "(_&His_circ)".
  iDestruct "His_circ" as (addrs' blocks') "(_&Hown&_)".
  iDestruct "Hown" as "(%Hlow_wf&Haddrs&Hblocks)".
  (* FIXME: use unify_ghost_var does not handle [var1 = var2] well. *)
  iDestruct (ghost_var_agree with "Haddrs Hγaddrs") as %->.
  iDestruct (ghost_var_agree with "Hblocks Hγblocks") as %->.
  auto.
Qed.

Theorem is_circular_appender_wf γ addrs blocks :
  is_circular γ -∗
  ghost_var γ.(addrs_name) (1/2) addrs ∗
  ghost_var γ.(blocks_name) (1/2) blocks -∗
  |NC={⊤}=> ⌜circ_low_wf addrs blocks⌝.
Proof.
  iIntros "#Hcirc [Hγaddrs Hγblocks]".
  iMod (ncinv_dup_acc ⌜circ_low_wf addrs blocks⌝ with "Hcirc [Hγaddrs Hγblocks]") as ">%Hwf"; auto.
  iIntros "Hinv".
  iDestruct "Hinv" as (σ) "[Hstate HP]".
  iDestruct (is_circular_inner_wf with "[$Hγaddrs $Hγblocks] Hstate") as %Hwf.
  iSplitL; auto.
  iExists _; iFrame.
Qed.

Theorem wp_hdr2 (newStart: u64) :
  {{{ True }}}
    hdr2 #newStart
  {{{ s b, RET slice_val s; is_block s (DfracOwn 1) b ∗
                            ⌜block_encodes b [EncUInt64 newStart]⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_new_enc.
  iIntros (enc) "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc"); first by word.
  iIntros "Henc".
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s b) "[%Henc Hs]".
  iApply "HΦ".
  iFrame.
  eauto.
Qed.

Theorem wp_hdr1 (circ: loc) (newStart: u64) s (addrs: list u64) :
  length addrs = Z.to_nat LogSz ->
  {{{ circ ↦[circularAppender :: "diskAddrs"] (slice_val s) ∗
       own_slice_small s uint64T (DfracOwn 1) addrs }}}
    circularAppender__hdr1 #circ #newStart
  {{{ b_s b, RET slice_val b_s;
      circ ↦[circularAppender :: "diskAddrs"] (slice_val s) ∗
      own_slice_small s uint64T (DfracOwn 1) addrs ∗
      is_block b_s (DfracOwn 1) b ∗
      ⌜block_encodes b ([EncUInt64 newStart] ++ (EncUInt64 <$> addrs))⌝ }}}.
Proof.
  iIntros (Haddrlen Φ) "[HdiskAddrs Hs] HΦ".
  wp_call.
  wp_apply wp_new_enc.
  iIntros (enc) "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc"); first by word.
  iIntros "Henc".
  wp_loadField.
  wp_apply (wp_Enc__PutInts with "[$Henc $Hs]"); first by word.
  iIntros "[Henc Hs]".
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s' b) "[%Henc Hs']".
  iApply "HΦ".
  iFrame.
  eauto.
Qed.

Lemma circ_wf_advance:
  ∀ (newStart : u64) (σ : circΣ.t),
    circ_wf σ
    → uint.Z (start σ) ≤ uint.Z newStart
      ∧ uint.Z newStart ≤ uint.Z (start σ) + length (upds σ)
    → circ_wf
        (set start (λ _ : u64, newStart)
             (set upds (drop (Z.to_nat (uint.Z newStart - uint.Z (start σ)))) σ)).
Proof.
  destruct σ as [upds start].
  rewrite /circ_wf /circΣ.diskEnd; simpl; intros.
  len.
Qed.

Lemma diskEnd_advance_unchanged:
  ∀ (newStart : u64) (σ : circΣ.t),
    uint.Z (start σ) <= uint.Z newStart <= circΣ.diskEnd σ ->
    circΣ.diskEnd
        (set start (λ _ : u64, newStart)
             (set upds (drop (Z.to_nat (uint.Z newStart - uint.Z (start σ)))) σ))
    = circΣ.diskEnd σ.
Proof.
  rewrite /circΣ.diskEnd /=.
  intros.
  len.
Qed.

Lemma has_circ_updates_advance :
  ∀ (newStart : u64) (σ : circΣ.t) (addrs : list u64) (blocks : list Block)
    (Hbounds: uint.Z (start σ) <= uint.Z newStart <= uint.Z (start σ) + length (upds σ))
    (Hupds: has_circ_updates σ addrs blocks),
    has_circ_updates
        (set start (λ _ : u64, newStart)
             (set upds (drop (Z.to_nat (uint.Z newStart - uint.Z (start σ)))) σ)) addrs
        blocks.
Proof.
  rewrite /has_circ_updates /=.
  intros.
  rewrite lookup_drop in H.
  apply Hupds in H.
  match type of H with
  | ?P => match goal with
         | |- ?g => replace g with P; [ exact H | ]
         end
  end.
  repeat (f_equal; try lia).
Qed.

Hint Unfold circ_low_wf : word.
Hint Unfold circΣ.diskEnd : word.

Lemma circ_positions_advance (newStart: u64) γ σ (start0: u64) :
  circ_wf σ ->
  uint.Z start0 <= uint.Z newStart <= circΣ.diskEnd σ ->
  circ_positions γ σ ∗ start_is γ (1/2) start0 ==∗
  circ_positions γ (set start (λ _ : u64, newStart)
                        (set upds (drop (Z.to_nat (uint.Z newStart - uint.Z (start σ)))) σ)) ∗
  start_is γ (1/2) newStart ∗ start_at_least γ newStart.
Proof.
  iIntros (Hwf Hmono) "[Hpos Hstart1]".
  iDestruct (start_is_to_eq with "[$] [$]") as %?; subst.
  iDestruct "Hpos" as "[Hstart2 Hend2]".
  rewrite /start_is /circ_positions.
  rewrite -> diskEnd_advance_unchanged by word.
  iCombine "Hstart1 Hstart2" as "Hstart".
  iMod (mono_nat_own_update (uint.nat newStart) with "Hstart")
    as "[[Hstart1 Hstart2] #Hstart_lb]"; first by lia.
  by iFrame.
Qed.

Theorem wp_circular__Advance (Q: iProp Σ) γ (d: val) (start0: u64) (newStart : u64) (diskEnd_lb: Z) :
  {{{ is_circular γ ∗
      start_is γ (1/2) start0 ∗
      diskEnd_at_least γ diskEnd_lb ∗
      ⌜uint.Z start0 ≤ uint.Z newStart ≤ diskEnd_lb⌝ ∗
    (∀ σ, ⌜circ_wf σ⌝ ∗ P σ ∗ ⌜σ.(circΣ.start) = start0⌝ -∗
      (∀ σ' b, ⌜relation.denote (circ_advance newStart) σ σ' b⌝ ∗ ⌜circ_wf σ'⌝ -∗ |NC={⊤ ∖↑ N}=> P σ' ∗ Q))
  }}}
    Advance d #newStart
  {{{ RET #(); Q ∗ start_is γ (1/2) newStart }}}.
Proof.
  iIntros (Φ) "(#Hcirc&Hstart&#Hend&%&Hfupd) HΦ".
  rename H into Hpre.
  wp_call.
  wp_apply wp_hdr2; iIntros (s hdr2) "[Hb %Henchdr2]".
  wp_pure1_credit "Hcred".
  wp_apply (wp_Write_atomic with "Hb").
  rewrite /is_circular.
  iInv "Hcirc" as "Hcirc_inv" "Hclose".
  iDestruct "Hcirc_inv" as (σ) "[>Hcirc_state HP]".
  iDestruct "Hcirc_state" as (Hwf) "(Hpos&Hcirc_state)".
  iDestruct "Hcirc_state" as (addrs blocks Hupds) "(Hown&Hlow)".
  iDestruct (start_is_to_eq with "[$] [$]") as %<-.
  iDestruct (diskEnd_at_least_to_le with "[$] Hend") as %HdiskEnd_lb.
  iDestruct (circ_state_wf with "Hown") as %Hlow_wf.
  iDestruct (circ_state_wf with "Hown") as %(Hlen1&Hlen2).
  iDestruct "Hlow" as (hdr1 hdr2_0 Hhdr1 Hhdr2) "(Hhdr1&Hhdr2&Hblocks)".
  iExists hdr2_0; iFrame "Hhdr2".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE Hhdr2".
  iMod "HcloseE" as "_".
  iMod (lc_fupd_elim_later with "Hcred HP") as "HP".
  iDestruct ("Hfupd" with "[$HP]") as "Hfupd"; first by eauto.
  rewrite difference_empty_L.
  iMod ("Hfupd" with "[]") as "[HP' HQ]".
  { iPureIntro.
    split.
    - simpl; monad_simpl.
    - eapply circ_wf_advance; eauto.
      word. }
  simpl.
  iMod (circ_positions_advance newStart with "[$Hpos Hstart]") as "(Hpos&Hstart&Hstart_lb)"; auto.
  { word. }
  iMod ("Hclose" with "[-HQ HΦ Hstart Hstart_lb]") as "_".
  { iNext.
    iExists _; iFrame.
    iSplitR.
    - iPureIntro.
      apply circ_wf_advance; eauto.
      word.
    - iSplitR; [ iPureIntro | ].
      { eapply has_circ_updates_advance; eauto; word. }
      iSplitR; auto.
      iPureIntro.
      rewrite -> diskEnd_advance_unchanged by word.
      auto. } (* done restoring invariant *)

  iIntros "!> Hs". (* done committing to disk *)

  wp_apply wp_Barrier.
  wp_pures. iApply ("HΦ" with "[$]").
Qed.

Fixpoint update_list_circ {A B} (f: B -> A) (xs: list A) (start: Z) (upds: list B): list A :=
  match upds with
 | nil => xs
 | u::upds => update_list_circ f (<[Z.to_nat (start `mod` LogSz) := f u]> xs) (start + 1) upds
  end.

Definition update_addrs (addrs: list u64) : Z -> list update.t -> list u64 :=
  update_list_circ (update.addr) addrs.

Definition update_blocks (blocks: list Block) : Z -> list update.t -> list Block :=
  update_list_circ (update.b) blocks.

Ltac mod_bound :=
  (* TODO: repeat *)
  match goal with
 | |- context[?x `mod` ?m] =>
   pose proof (Z.mod_bound_pos x m)
  end.

Theorem wrap_small_log_addr (x:u64) :
  word.wrap (word:=w64_instance.w64) (2 + uint.Z x `mod` word.wrap (word:=w64_instance.w64) LogSz) =
  2 + uint.Z x `mod` LogSz.
Proof.
  unfold LogSz.
  change (word.wrap 511) with 511.
  rewrite wrap_small //.
  mod_bound; word.
Qed.

Theorem mod_neq_lt a b k :
  0 < k ->
  0 <= a < b ->
  b - a < k ->
  a `mod` k ≠ b `mod` k.
Proof.
  intros.
  assert (k ≠ 0) by lia.
  replace b with (a + (b - a)) by lia.
  assert (0 < b - a) by lia.
  generalize dependent (b - a); intros d **.
  intros ?.
  assert ((a + d) `mod` k - a `mod` k = 0) by lia.
  assert (((a + d) `mod` k - a `mod` k) `mod` k = 0).
  { rewrite H5.
    rewrite Z.mod_0_l; lia. }
  rewrite -Zminus_mod in H6.
  replace (a + d - a) with d in H6 by lia.
  rewrite -> Z.mod_small in H6 by lia.
  lia.
Qed.

Theorem mod_neq_gt a b k :
  0 < k ->
  0 <= a < b ->
  b - a < k ->
  b `mod` k ≠ a `mod` k.
Proof.
  intros ** Heq%eq_sym%mod_neq_lt; lia.
Qed.

Theorem Zto_nat_neq_inj z1 z2 :
  0 <= z1 ->
  0 <= z2 ->
  z1 ≠ z2 ->
  Z.to_nat z1 ≠ Z.to_nat z2.
Proof.
  lia.
Qed.

Lemma has_circ_updates_blocks σ addrs blocks (i : u64) bi :
  length (circ_proof.upds σ) + uint.Z i < LogSz ->
  has_circ_updates σ addrs blocks ->
  has_circ_updates σ addrs (<[Z.to_nat ((circΣ.diskEnd σ + uint.Z i) `mod` LogSz) := bi]> blocks).
Proof.
  clear.
  rewrite /has_circ_updates; intros Hbound Hhas_upds i0 u **.
  assert (0 ≤ i0 < length (upds σ)).
  { apply lookup_lt_Some in H.
    word. }
  intuition.
  { apply Hhas_upds; eauto. }
  rewrite list_lookup_insert_ne.
  { apply Hhas_upds; eauto. }
  rewrite /circΣ.diskEnd.
  apply Zto_nat_neq_inj.
  { mod_bound; word. }
  { mod_bound; word. }
  apply mod_neq_gt; word.
Qed.

Lemma circ_low_wf_blocks addrs blocks (i : nat) bi :
  circ_low_wf addrs blocks ->
  circ_low_wf addrs (<[i := bi]> blocks).
Proof.
  rewrite /circ_low_wf; len.
Qed.

Theorem update_list_circ_length {A B} (f: A -> B) xs start upds :
  length (update_list_circ f xs start upds) = length xs.
Proof.
  revert xs start.
  induction upds; simpl; intros; auto.
  rewrite IHupds; len.
Qed.

Theorem update_addrs_length addrs start upds :
  length (update_addrs addrs start upds) = length addrs.
Proof. apply update_list_circ_length. Qed.

Theorem update_blocks_length blocks start upds :
  length (update_blocks blocks start upds) = length blocks.
Proof. apply update_list_circ_length. Qed.

Hint Rewrite update_addrs_length : len.
Hint Rewrite update_blocks_length : len.

Lemma update_blocks_S :
  ∀ upds blocks endpos addr_i b_i,
  update_blocks blocks endpos (upds ++ [ {| update.addr := addr_i; update.b := b_i |} ]) =
  <[Z.to_nat ((endpos + length upds) `mod` 511) := b_i]> (update_blocks blocks endpos upds).
Proof.
  rewrite /update_blocks.
  induction upds; simpl; intros.
  - f_equal. f_equal. f_equal. lia.
  - rewrite IHupds. f_equal. f_equal. f_equal. lia.
Qed.

Lemma update_blocks_take_S upds blocks endpos (i : u64) addr_i b_i :
  upds !! uint.nat i = Some {| update.addr := addr_i; update.b := b_i |} ->
  update_blocks blocks endpos (take (S (uint.nat i)) upds) =
  <[Z.to_nat ((endpos + uint.Z i) `mod` 511) := b_i]> (update_blocks blocks endpos (take (uint.nat i) upds)).
Proof.
  intros.
  erewrite take_S_r; eauto.
  rewrite update_blocks_S.
  f_equal. f_equal.
  apply lookup_lt_Some in H.
  rewrite -> firstn_length_le by lia.
  word.
Qed.

Lemma update_addrs_S :
  ∀ upds addrs endpos addr_i b_i,
  update_addrs addrs endpos (upds ++ [ {| update.addr := addr_i; update.b := b_i |} ]) =
  <[Z.to_nat ((endpos + length upds) `mod` 511) := addr_i]> (update_addrs addrs endpos upds).
Proof.
  rewrite /update_addrs.
  induction upds; simpl; intros.
  - f_equal. f_equal. f_equal. lia.
  - rewrite IHupds. f_equal. f_equal. f_equal. lia.
Qed.

Lemma update_addrs_take_S upds addrs endpos (i : u64) addr_i b_i :
  upds !! uint.nat i = Some {| update.addr := addr_i; update.b := b_i |} ->
  update_addrs addrs endpos (take (S (uint.nat i)) upds) =
  <[Z.to_nat ((endpos + uint.Z i) `mod` 511) := addr_i]> (update_addrs addrs endpos (take (uint.nat i) upds)).
Proof.
  intros.
  erewrite take_S_r; eauto.
  rewrite update_addrs_S.
  f_equal. f_equal.
  apply lookup_lt_Some in H.
  rewrite -> firstn_length_le by lia.
  word.
Qed.

Theorem wp_circularAppender__logBlocks γ c (d: val)
        (startpos_lb endpos : u64) (bufs : Slice.t) q
        (addrs : list u64) (blocks : list Block) diskaddrslice (upds : list update.t) :
  length addrs = Z.to_nat LogSz ->
  uint.Z endpos + Z.of_nat (length upds) < 2^64 ->
  (uint.Z endpos - uint.Z startpos_lb) + length upds ≤ LogSz ->
  {{{ is_circular γ ∗
      ghost_var γ.(blocks_name) (1/2) blocks ∗
      start_at_least γ startpos_lb ∗
      diskEnd_is γ (1/2) (uint.Z endpos) ∗
      c ↦[circularAppender :: "diskAddrs"] (slice_val diskaddrslice) ∗
      own_slice_small diskaddrslice uint64T (DfracOwn 1) addrs ∗
      updates_slice_frag bufs q upds
  }}}
    circularAppender__logBlocks #c d #endpos (slice_val bufs)
  {{{ RET #();
      let addrs' := update_addrs addrs (uint.Z endpos) upds in
      let blocks' := update_blocks blocks (uint.Z endpos) upds in
      ghost_var γ.(blocks_name) (1/2) blocks' ∗
      diskEnd_is γ (1/2) (uint.Z endpos) ∗
      c ↦[circularAppender :: "diskAddrs"] (slice_val diskaddrslice) ∗
      own_slice_small diskaddrslice uint64T (DfracOwn 1) addrs' ∗
      updates_slice_frag bufs q upds
  }}}.
Proof.
  iIntros (Haddrs_len Hendpos_overflow Hhasspace Φ) "(#Hcirc & Hγblocks & #Hstart & Hend & Hdiskaddrs & Hslice & Hupdslice) HΦ".
  wp_lam. wp_let. wp_let. wp_let.
  iDestruct (updates_slice_frag_len with "Hupdslice") as %Hupdlen.
  iDestruct "Hupdslice" as (bks) "[Hupdslice Hbks]".

  iDestruct (slice.own_slice_small_sz with "Hupdslice") as %Hslen.
  rewrite fmap_length in Hslen.
  iDestruct (big_sepL2_length with "Hbks") as %Hslen2.

  wp_apply (slice.wp_forSlice (fun i =>
    let addrs' := update_addrs addrs (uint.Z endpos) (take (uint.nat i) upds) in
    let blocks' := update_blocks blocks (uint.Z endpos) (take (uint.nat i) upds) in
    ghost_var γ.(blocks_name) (1/2) blocks' ∗
    c ↦[circularAppender :: "diskAddrs"] (slice_val diskaddrslice) ∗
    own_slice_small diskaddrslice uint64T (DfracOwn 1) addrs' ∗
    diskEnd_is γ (1/2) (uint.Z endpos) ∗
    ( [∗ list] b_upd;upd ∈ bks;upds, is_update b_upd q upd)
    )%I (* XXX why is %I needed? *)
    with "[] [$Hγblocks $Hdiskaddrs $Hslice $Hupdslice $Hend $Hbks]").

  2: {
    iIntros "(HI&Hupdslice)".
    iDestruct "HI" as "(?&? & Hblocks&Hend&Hupds)".
    wp_pures. iModIntro. iApply "HΦ"; iFrame.
    rewrite -> take_ge by lia.
    iFrame.
  }

  iIntros (i bk Φₗ) "!> [HI [% %]] HΦ".
  iDestruct "HI" as "(Hγblocks&HdiskAddrs&Haddrs&Hend&Hbks)".
  rewrite list_lookup_fmap in H0.
  apply fmap_Some in H0.
  destruct H0 as [[addr bk_s] [Hbkseq ->]].
  list_elem upds i as u.
  iDestruct (big_sepL2_lookup_acc with "Hbks") as "[Hi Hbks]"; eauto.
  destruct u as [addr_i b_i]; simpl.
  iDestruct "Hi" as "[%Heq Hi]".
  simpl in Heq; subst.

  wp_pures.
  wp_apply wp_DPrintf.
  wp_pures.
  change (word.divu (word.sub 4096 8) 8) with (W64 LogSz).
  wp_apply (wp_Write_atomic with "Hi").
  word_cleanup.
  rewrite wrap_small_log_addr.
  word_cleanup.

  iInv "Hcirc" as "HcircI" "Hclose".
  iDestruct "HcircI" as (σ) "[>Hσ HP]".
  iDestruct "Hσ" as (Hwf) "[Hpos Hσ]".
  iDestruct "Hσ" as (addrs' blocks'' Hhas_upds) "(Hown&Hlow)".
  iDestruct (circ_state_wf with "Hown") as %Hlowwf.
  iDestruct (circ_state_wf with "Hown") as %[Hlen1 Hlen2].
  iDestruct (diskEnd_is_to_eq with "[$] [$]") as %HdiskEnd.
  iDestruct (start_at_least_to_le with "[$] Hstart") as %Hstart_lb.
  iDestruct "Hlow" as (hdr1 hdr2 Hhdr1 Hhdr2) "(Hd0&Hd1&Hd2)".
  pose proof (Z.mod_bound_pos (uint.Z endpos + uint.Z i) LogSz); intuition (try word).
  list_elem blocks'' ((uint.Z endpos + uint.Z i) `mod` LogSz) as b.
  iDestruct (disk_array_acc _ _ ((uint.Z endpos + uint.Z i) `mod` LogSz) with "[$Hd2]") as "[Hdi Hd2]"; eauto.
  { word. }
  iExists b.
  assert (length (circ_proof.upds σ ++ upds) ≤ LogSz ∧
          uint.Z endpos = circΣ.diskEnd σ ∧
          uint.Z endpos + Z.of_nat (length upds) < 2^64) by len.

  iFrame "Hdi".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE Hdi".
  iMod "HcloseE" as "_".
  iSpecialize ("Hd2" with "Hdi").
  iDestruct "Hown" as (_) "[Haddrs_auth Hblocks_auth]".
  iDestruct (ghost_var_agree γ.(blocks_name) with "Hblocks_auth Hγblocks") as %->.
  iMod (ghost_var_update_halves _
          with "Hblocks_auth Hγblocks") as "[Hblocks_auth Hγblocks]".
  iMod ("Hclose" with "[-Hγblocks Hend HΦ HdiskAddrs Haddrs Hbks]") as "_".
  { iModIntro.
    iExists _; iFrame "HP".
    iSplitR; first by auto.
    iFrame "Hpos".
    iExists _, _; iFrame.
    iSplitR.
    { iPureIntro.
      generalize dependent (update_blocks blocks (uint.Z endpos)
                                          (take (uint.nat i) upds)); intros blocks' **.
      replace (uint.Z endpos) with (circΣ.diskEnd σ) by word.
      eapply has_circ_updates_blocks; eauto.
      autorewrite with len in *. word.
    }
    iSplitR.
    { iPureIntro.
      eapply circ_low_wf_blocks; eauto.
    }
    by iFrame.
  }
  iIntros "!> Hs".
  wp_loadField.
  wp_apply (slice.wp_SliceSet with "[$Haddrs]").
  { iPureIntro.
    split; auto.
    rewrite list_lookup_fmap.
    apply fmap_is_Some.
    change (word.divu (word.sub 4096 8) 8) with (W64 511).
    word_cleanup.
    apply lookup_lt_is_Some_2; len.
  }
  iIntros "Haddrs".
  iApply "HΦ".
  change (word.divu (word.sub 4096 8) 8) with (W64 511).
  word_cleanup.
  iFrame.
  iSplitL "Hγblocks".
  { replace (Z.to_nat (uint.Z i + 1)) with (S (uint.nat i)) by lia.
    erewrite update_blocks_take_S; eauto. }
  iSplitL "Haddrs".
  { replace (Z.to_nat (uint.Z i + 1)) with (S (uint.nat i)) by lia.
    erewrite update_addrs_take_S; eauto.
    replace (uint.Z (word.add endpos i)) with (uint.Z endpos + uint.Z i) by word.
    rewrite /own_slice_small /list.untype.
    rewrite list_fmap_insert //.
  }
  iApply "Hbks".
  iFrame. eauto.
Qed.

Lemma circ_wf_app upds0 upds start :
  length (upds0 ++ upds) ≤ LogSz ->
  circΣ.diskEnd {| circΣ.upds := upds0; circΣ.start := start |} +
     length upds < 2^64 ->
  circ_wf {| circΣ.upds := upds0; circΣ.start := start |} ->
  circ_wf {| circΣ.upds := upds0 ++ upds; circΣ.start := start |}.
Proof.
  rewrite /circ_wf /circΣ.diskEnd /=; len.
Qed.

Theorem lookup_update_circ_old {A B} (f: A -> B) xs (endpos: Z) upds i :
  0 <= i < endpos ->
  endpos - i + length upds <= LogSz ->
  update_list_circ f xs endpos upds
  !! Z.to_nat (i `mod` LogSz) =
  xs !! Z.to_nat (i `mod` LogSz).
Proof.
  revert xs endpos i.
  induction upds; simpl; intros; auto.
  rewrite -> IHupds by word.
  rewrite list_lookup_insert_ne; auto.
  apply Zto_nat_neq_inj; try (mod_bound; word).
  apply mod_neq_gt; try word.
Qed.

Theorem lookup_update_circ_new {A B} (f: A -> B) xs (endpos: Z) upds i :
  0 <= endpos ->
  length upds <= LogSz ->
  endpos <= i < endpos + length upds ->
  length xs = Z.to_nat LogSz ->
  update_list_circ f xs endpos upds
  !! Z.to_nat (i `mod` LogSz) =
  f <$> upds !! Z.to_nat (i - endpos).
Proof.
  revert xs endpos i.
  induction upds; simpl; intros; auto.
  { lia. }
  destruct (decide (i = endpos)); subst.
  - rewrite lookup_update_circ_old; try lia.
    rewrite -> list_lookup_insert by (mod_bound; lia).
    replace (Z.to_nat (endpos - endpos)) with 0%nat by lia.
    auto.
  - rewrite -> IHupds by len.
    f_equal.
    replace ((Z.to_nat) $ (i - endpos)) with
        (S $ (Z.to_nat) $ (i - (endpos + 1))) by lia.
    reflexivity.
Qed.

Lemma has_circ_updates_app upds0 start addrs blocks (endpos : u64) upds :
  uint.Z endpos = circΣ.diskEnd {| circΣ.upds := upds0; circΣ.start := start |} ->
  length (upds0 ++ upds) ≤ LogSz ->
  circ_low_wf addrs (update_blocks blocks (uint.Z endpos) upds) ->
  has_circ_updates
    {| circΣ.upds := upds0; circΣ.start := start |} addrs
    (update_blocks blocks (uint.Z endpos) upds) ->
  has_circ_updates
    {| circΣ.upds := upds0 ++ upds; circΣ.start := start |}
    (update_addrs addrs (uint.Z endpos) upds)
    (update_blocks blocks (uint.Z endpos) upds).
Proof.
  rewrite /has_circ_updates /=.
  intros Hendpos Hupdlen [Hbound1 Hbound2] Hupds.
  rewrite /circΣ.diskEnd /= in Hendpos.
  autorewrite with len in Hbound2, Hupdlen.
  intros.
  destruct (decide (i < length upds0)).
  - rewrite -> lookup_app_l in H by lia.
    apply Hupds in H; intuition.
    rewrite /update_addrs.
    rewrite -> lookup_update_circ_old by word; auto.
  - rewrite -> lookup_app_r in H by lia.
    pose proof (lookup_lt_Some _ _ _ H).
    rewrite /update_addrs /update_blocks.
    rewrite -> lookup_update_circ_new by word.
    rewrite -> ?lookup_update_circ_new by word.
    replace (Z.to_nat (uint.Z start + i - uint.Z endpos)) with
        (i - length upds0)%nat by word.
    rewrite H; intuition eauto.
Qed.

Theorem circ_low_wf_log_blocks addrs blocks' endpos upds :
  circ_low_wf addrs (update_blocks blocks' endpos upds) ->
  circ_low_wf (update_addrs addrs endpos upds)
              (update_blocks blocks' endpos upds).
Proof.
  rewrite /circ_low_wf; len.
Qed.

Hint Resolve circ_low_wf_log_blocks : core.

Lemma circ_low_wf_update_addrs
      (endpos : u64) (upds : list update.t) (addrs : list u64)
      (blocks' : list Block) :
  circ_low_wf addrs blocks'
  → circ_low_wf (update_addrs addrs (uint.Z endpos) upds)
                (update_blocks blocks' (uint.Z endpos) upds).
Proof.
  rewrite /circ_low_wf; len.
Qed.

Lemma circ_positions_append upds γ σ (startpos endpos: u64) :
  uint.Z endpos + Z.of_nat (length upds) < 2^64 ->
  (uint.Z endpos - uint.Z startpos) + length upds ≤ LogSz ->
  circ_positions γ σ -∗
  start_at_least γ startpos -∗
  diskEnd_is γ (1/2) (uint.Z endpos) -∗
  |==> circ_positions γ (set circ_proof.upds (λ u : list update.t, u ++ upds) σ) ∗
       diskEnd_is γ (1/2) (uint.Z endpos + length upds).
Proof.
  iIntros (Hendpos_overflow Hhasspace) "[$ Hend1] #Hstart Hend2".
  rewrite /circΣ.diskEnd /=; autorewrite with len.
  iDestruct (diskEnd_is_agree with "Hend1 Hend2") as %Heq; rewrite Heq.
  iCombine "Hend1 Hend2" as "Hend".
  iDestruct "Hend" as "[% [Hend _]]".
  iMod (mono_nat_own_update (uint.nat endpos + length upds)%nat with "Hend") as "[[Hend1 Hend2] #Hatleast]"; first by len.
  iModIntro.
  iSplitR "Hend2".
  2: {
    rewrite /diskEnd_is /diskEnd_at_least.
    replace (Z.to_nat (uint.Z endpos + length upds))
      with (uint.nat endpos + length upds)%nat by lia. iFrame "Hatleast".
    iSplitR. { iPureIntro. split; word. }
    iFrame.
  }

  rewrite /diskEnd_is /diskEnd_at_least.
  replace (Z.to_nat
         (uint.Z (start σ) + (length (circ_proof.upds σ) + length upds)%nat))
    with (uint.nat endpos + length upds)%nat by lia.
  iFrame "Hatleast".
  iSplitR. { iPureIntro. split; word. }
  iFrame.
Qed.

Theorem wp_circular__Append (Q: iProp Σ) γ (d: val) q (startpos endpos : u64) (bufs : Slice.t) (upds : list update.t) c :
  uint.Z endpos + Z.of_nat (length upds) < 2^64 ->
  (uint.Z endpos - uint.Z startpos) + length upds ≤ LogSz ->
  {{{ is_circular γ ∗
      updates_slice_frag bufs q upds ∗
      diskEnd_is γ (1/2) (uint.Z endpos) ∗
      start_at_least γ startpos ∗
      is_circular_appender γ c ∗
      (∀ σ, ⌜circ_wf σ⌝ ∗ ⌜circΣ.diskEnd σ = uint.Z endpos⌝ ∗ P σ -∗
          ∀ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝ ∗ ⌜circ_wf σ'⌝ -∗ |NC={⊤ ∖↑ N}=> P σ' ∗ Q)
  }}}
    circularAppender__Append #c d #endpos (slice_val bufs)
  {{{ RET #(); Q ∗
      updates_slice_frag bufs q upds ∗
      is_circular_appender γ c ∗
      diskEnd_is γ (1/2) (uint.Z endpos + length upds)
  }}}.
Proof.
  iIntros (Hendpos_overflow Hhasspace Φ) "(#Hcirc & Hslice & Hend & #Hstart & Hca & Hfupd) HΦ".
  wp_call.
  iDestruct "Hca" as (bk_s addrs blocks' Hlow_wf) "(Hγaddrs&Hγblocks&HdiskAddrs&Haddrs)".

  wp_apply (wp_circularAppender__logBlocks with "[$Hcirc $Hγblocks $HdiskAddrs $Hstart $Hend $Haddrs $Hslice]"); try word.
  iIntros "(Hγblocks&Hend&HdiskAddrs&Hs&Hupds)".
  iDestruct (updates_slice_frag_len with "Hupds") as %Hbufsz.
  wp_pures.
  wp_apply wp_Barrier.
  wp_apply wp_slice_len.
  wp_pures.
  wp_apply (wp_hdr1 with "[$HdiskAddrs $Hs]"); first by len.
  iIntros (b_s b) "(HdiskAddrs&Hs&Hb&%)".
  wp_pure1_credit "Hcred".
  wp_pures.

  iDestruct (slice.own_slice_small_sz with "Hb") as %Hslen.
  wp_apply (wp_Write_atomic with "Hb").  (*   *)
  rewrite fmap_length in Hslen.

  iInv N as "Hcircopen" "Hclose".
  iDestruct "Hcircopen" as (σ) "[>[%Hwf Hcs] HP]".
  iDestruct "Hcs" as "[Hpos Hcs]".
  iDestruct (diskEnd_is_to_eq with "[$] [$]") as %HdiskEnd.
  iDestruct (start_at_least_to_le with "[$] Hstart") as %Hstart_lb.
  iDestruct "Hcs" as (addrs0 blocks0 Hupds) "[Hown Hlow]".
  iDestruct "Hown" as (Hlow_wf') "[Haddrs Hblocks]".
  iDestruct "Hlow" as (hdr1 hdr2 Hhdr1 Hhdr2) "(Hd0 & Hd1 & Hd2)".
  iExists _. iFrame "Hd0".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE Hd0".
  iMod "HcloseE" as "_".

  iDestruct (ghost_var_agree with "Hblocks Hγblocks") as %->.
  iDestruct (ghost_var_agree with "Haddrs Hγaddrs") as %->.
  iMod (ghost_var_update_halves (update_addrs addrs (uint.Z endpos) upds) with "Haddrs Hγaddrs") as "[Haddrs Hγaddrs]".
  iMod (circ_positions_append upds with "[$] Hstart [$]") as "[Hpos Hend]"; [ done | done | ].
  iDestruct (diskEnd_is_to_eq with "[$] [$]") as %HdiskEnd'.
  iDestruct (start_at_least_to_le with "[$] Hstart") as %Hstart_lb'.

  rewrite difference_empty_L.
  iMod (lc_fupd_elim_later with "Hcred HP") as "HP".
  iMod ("Hfupd" with "[$HP //] []") as "[HP HQ]".
  { iPureIntro.
    split.
    - simpl; monad_simpl.
    - destruct σ. rewrite /=.
      rewrite /circΣ.diskEnd /set /= in HdiskEnd', Hstart_lb' |- *.
      autorewrite with len in HdiskEnd'.
      apply circ_wf_app; auto; len.
  }
  iMod ("Hclose" with "[-Hγblocks Hγaddrs Hend HΦ HQ HdiskAddrs Hupds Hs]") as "_".
  { 
    iNext. iExists _. iFrame.
    destruct σ. rewrite /=.
    iSplitR.
    { iPureIntro.
      rewrite /circΣ.diskEnd /set /= in HdiskEnd', Hstart_lb' |- *.
      autorewrite with len in HdiskEnd'.
      apply circ_wf_app; auto; len.
    }
    iSplitR.
    { iPureIntro.
      rewrite /circΣ.diskEnd /set /= in HdiskEnd', Hstart_lb' |- *.
      autorewrite with len in HdiskEnd'.
      apply has_circ_updates_app; auto; len.
    }
    iSplitR; first by eauto.
    iPureIntro; intuition.
    { eapply block_encodes_eq; eauto. simpl.
      f_equal. f_equal.
      rewrite /circΣ.diskEnd /set /= in HdiskEnd', Hstart_lb' |- *.
      autorewrite with len in HdiskEnd'.
      cbn [circ_proof.start circ_proof.upds] in *.
      len. }
  }
  iIntros "!> Hb_s".
  wp_apply wp_Barrier.
  wp_pures. iModIntro. iApply "HΦ". iFrame.
  eauto using circ_low_wf_update_addrs.
Qed.

Theorem wp_decodeHdr1 stk E s (hdr1: Block) (endpos: u64) (addrs: list u64) :
  block_encodes hdr1 ([EncUInt64 endpos] ++ (EncUInt64 <$> addrs)) →
  length addrs = Z.to_nat LogSz ->
  {{{ is_block s (DfracOwn 1) hdr1 }}}
    decodeHdr1 (slice_val s) @ stk; E
  {{{ (a_s:Slice.t), RET (#endpos, slice_val a_s);
      own_slice a_s uint64T (DfracOwn 1) addrs }}}.
Proof.
  iIntros (Hhdr1 Haddrlen Φ) "Hb HΦ".
  wp_call.

  wp_apply (wp_new_dec with "Hb"); first by eauto.
  iIntros (dec0) "Hdec0".
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec0"); iIntros "Hdec0".
  wp_pures.
  rewrite -(app_nil_r (EncUInt64 <$> addrs)).
  wp_apply (wp_Dec__GetInts with "Hdec0").
  { change (word.divu _ _) with (W64 LogSz).
    word. }
  iIntros (a_s) "[_ Hdiskaddrs]".
  wp_pures.
  iApply ("HΦ" with "[$]").
Qed.

Theorem wp_decodeHdr2 stk E s (hdr2: Block) (startpos: u64) :
  block_encodes hdr2 [EncUInt64 startpos] ->
  {{{ is_block s (DfracOwn 1) hdr2 }}}
    decodeHdr2 (slice_val s) @ stk; E
  {{{ RET #startpos; True }}}.
Proof.
  iIntros (Hhdr2 Φ) "Hb HΦ".

  wp_call.
  wp_apply (wp_new_dec with "Hb"); first eauto.
  iIntros (dec1) "Hdec1".
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec1").
  iIntros "_".
  wp_pures.
  iApply ("HΦ" with "[$]").
Qed.

Theorem circ_low_wf_empty logblocks :
  length logblocks = Z.to_nat LogSz ->
  circ_low_wf (replicate (Z.to_nat LogSz) (W64 0)) logblocks.
Proof.
  intros.
  split; auto.
  word.
Qed.

Theorem wp_initCircular d logblocks :
  {{{ 0 d↦∗ logblocks ∗ ⌜length logblocks = Z.to_nat (2 + LogSz)⌝ }}}
    initCircular #d
  {{{ γ σ (c:loc), RET #c;
      ⌜σ = circΣ.mk [] (W64 0)⌝ ∗
      ⌜circ_wf σ⌝ ∗
      is_circular_state γ σ ∗
      is_circular_appender γ c ∗
      start_is γ (1/2) (W64 0) ∗
      diskEnd_is γ (1/2) 0
  }}}.
Proof.
  iIntros (Φ) "[Hd %Hbkslen] HΦ".
  destruct logblocks; first by (simpl in Hbkslen; word).
  destruct logblocks; first by (simpl in Hbkslen; word).
  iDestruct (disk_array_cons with "Hd") as "[Hd0 Hd]".
  iDestruct (disk_array_cons with "Hd") as "[Hd1 Hd2]".
  change (0 + 1) with 1.
  change (1 + 1) with 2.
  iMod (ghost_var_alloc (replicate (Z.to_nat LogSz) (W64 0))) as (addrs_name') "[Haddrs' Hγaddrs]".
  iMod (ghost_var_alloc logblocks) as (blocks_name') "[Hblocks' Hγblocks]".
  iMod (mono_nat_own_alloc 0%nat) as (start_name') "[[Hstart1 Hstart2] #HstartLb]".
  iMod (mono_nat_own_alloc 0%nat) as (diskEnd_name') "[[HdiskEnd1 HdiskEnd2] #HdiskEndLb]".
  wp_call.
  wp_apply wp_new_slice; first by auto.
  iIntros (zero_s) "Hzero".
  iDestruct (slice.own_slice_to_small with "Hzero") as "Hzero".
  wp_pures.
  rewrite replicate_zero_to_block0.
  wp_apply (wp_Write with "[Hd0 $Hzero]").
  { iExists _; iFrame. }
  iIntros "[Hd0 Hzero]".
  wp_apply (wp_Write with "[Hd1 $Hzero]").
  { iExists _; iFrame. }
  iIntros "[Hd1 Hzero]".
  wp_apply wp_new_slice; first by auto.
  change (uint.nat (word.divu (word.sub 4096 8) 8)) with (Z.to_nat LogSz).
  iIntros (upd_s) "Hupd".
  wp_apply wp_allocStruct; first by auto.
  iIntros (l) "Hs".
  iApply ("HΦ" $! {| addrs_name := addrs_name';
                     blocks_name := blocks_name';
                     start_name := start_name';
                     diskEnd_name := diskEnd_name'; |}).
  iSplit; first by eauto.
  iSplit; first by eauto.
  iSplitL "Hstart1 HdiskEnd1 Haddrs' Hblocks' Hd0 Hd1 Hd2".
  { iFrame "Hstart1 HdiskEnd1 HdiskEndLb".
    iSplit; first by eauto.
    iSplit; first by eauto.
    iExists _, _; iFrame "Haddrs' Hblocks'".
    iSplit; auto.
    iSplit.
    { iPureIntro.
      simpl in Hbkslen.
      apply circ_low_wf_empty; word. }
    change (uint.Z 0) with 0.
    change (uint.Z 1) with 1.
    iExists block0, block0.
    iFrame.
    iPureIntro.
    { split.
      - reflexivity.
      - reflexivity. }
    }
  iFrame "Hstart2 HdiskEnd2".
  iSplit; auto.
  iExists _, _, _; iFrame "Hγaddrs Hγblocks".
  iSplit.
  { iPureIntro.
    simpl in Hbkslen.
    apply circ_low_wf_empty; word. }
  iDestruct (struct_fields_split with "Hs") as "($&_)".
  iDestruct (slice.own_slice_to_small with "Hupd") as "Hupd".
  rewrite -fmap_replicate.
  iFrame "Hupd".
Qed.


End heap.
