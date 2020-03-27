From RecordUpdate Require Import RecordSet.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import marshal_proof util_proof.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import GenHeap.

From Perennial.Helpers Require Import Transitions.
Existing Instance r_mbind.

Definition LogSz := 511.

Module circΣ.
  Record t :=
    mk { upds: list update.t;
         start: u64;
       }.
  Global Instance _eta: Settable _ := settable! mk <upds; start>.
  Definition diskEnd (s:t): Z :=
    int.val s.(start) + Z.of_nat (length s.(upds)).
  Definition empty (s:t): t :=
    mk [] (diskEnd s).
End circΣ.

Notation start := circΣ.start.
Notation upds := circΣ.upds.

Definition circ_read : transition circΣ.t (list update.t * u64) :=
  s ← reads (fun x => (upds x, start x));
  ret s.

Definition assert `(P : T -> Prop) : transition T unit :=
  suchThat (gen:=fun _ _ => None) (fun σ _ => P σ).

Definition circ_advance (newStart : u64) : transition circΣ.t unit :=
  assert (fun σ => int.val σ.(start) <= int.val newStart <= int.val σ.(start) + length σ.(upds));;
  modify (fun σ => set upds (drop (Z.to_nat (int.val newStart - int.val σ.(start))%Z)) σ);;
  modify (set start (fun _ => newStart)).

Definition circ_append (l : list update.t) (endpos : u64) : transition circΣ.t unit :=
  assert (fun σ => circΣ.diskEnd σ = int.val endpos);;
  assert (fun σ => circΣ.diskEnd σ + length l < 2^64);;
  modify (set circΣ.upds (fun u => u ++ l));;
  assert (fun σ => length σ.(upds) <= LogSz).

Canonical Structure updateO := leibnizO update.t.
Canonical Structure blockO := leibnizO Block.
Canonical Structure u64O := leibnizO u64.

Section heap.
Context `{!heapG Σ}.
Context `{!inG Σ (authR (optionUR (exclR (listO u64O))))}.
Context `{!inG Σ (authR (optionUR (exclR (listO blockO))))}.

Context (N: namespace).
Context (P: circΣ.t -> iProp Σ).
Context {Ptimeless: forall σ, Timeless (P σ)}.

Record circ_names :=
  { addrs_name: gname;
    blocks_name: gname; }.

Implicit Types (γ:circ_names).

Definition is_low_state (startpos endpos : u64) (addrs: list u64) (blocks : list Block) : iProp Σ :=
  ∃ hdr1 hdr2 hdr2extra,
    ⌜Block_to_vals hdr1 = b2val <$> encode ([EncUInt64 endpos] ++ (map EncUInt64 addrs))⌝ ∗
    ⌜Block_to_vals hdr2 = b2val <$> encode [EncUInt64 startpos] ++ hdr2extra⌝ ∗
    0 d↦ hdr1 ∗
    1 d↦ hdr2 ∗
    2 d↦∗ blocks.

Definition circ_wf (σ: circΣ.t) :=
  let start: Z := int.val σ.(start) in
  let endpos: Z := circΣ.diskEnd σ in
  start <= endpos < start + LogSz ∧
  start + length σ.(upds) < 2^64 ∧
  length σ.(upds) <= LogSz.

Definition has_circ_updates σ (addrs: list u64) (blocks: list Block) :=
  forall (i: nat),
    let off := Z.to_nat ((int.val σ.(circΣ.start) + i) `mod` LogSz) in
    forall u, σ.(circΣ.upds) !! i = Some u ->
         addrs !! off = Some (update.addr u) ∧
         blocks !! off = Some (update.b u).

Definition circ_low_wf (addrs: list u64) (blocks: list Block) :=
  Z.of_nat (length addrs) = LogSz ∧
  Z.of_nat (length blocks) = LogSz.

Definition circ_own γ (addrs: list u64) (blocks: list Block): iProp Σ :=
  ⌜circ_low_wf addrs blocks⌝ ∗
  own γ.(addrs_name) (● (Excl' addrs)) ∗
  own γ.(blocks_name) (● (Excl' blocks)).

Theorem circ_state_wf γ addrs blocks :
  circ_own γ addrs blocks -∗ ⌜circ_low_wf addrs blocks⌝.
Proof. iIntros "[% _] //". Qed.

Definition is_circular_state γ (σ : circΣ.t) : iProp Σ :=
  ⌜circ_wf σ⌝ ∗
  ∃ (addrs: list u64) (blocks: list Block),
    ⌜has_circ_updates σ addrs blocks⌝ ∗
    circ_own γ addrs blocks ∗
    is_low_state σ.(start) (circΣ.diskEnd σ) addrs blocks
.

Definition is_circular γ : iProp Σ :=
  inv N (∃ σ, is_circular_state γ σ ∗ P σ).

Definition is_circular_appender γ (circ: loc) : iProp Σ :=
  ∃ s (addrs : list u64) (blocks: list Block),
    own γ.(addrs_name) (◯ (Excl' addrs)) ∗
    own γ.(blocks_name) (◯ (Excl' blocks)) ∗
    circ ↦[circularAppender.S :: "diskAddrs"] (slice_val s) ∗
    is_slice_small s uint64T 1 (u64val <$> addrs).

Theorem wp_hdr2 (newStart: u64) :
  {{{ True }}}
    hdr2 #newStart
  {{{ s b, RET slice_val s; is_block s b ∗
                            ∃ extra,
                              ⌜Block_to_vals b = b2val <$> encode [EncUInt64 newStart] ++ extra⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_new_enc.
  iIntros (enc) "[Henc %]".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc"); first by word.
  iIntros "Henc".
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s) "[Hs %]".
  iApply "HΦ".
  iFrame.
  rewrite H in H0.
  autorewrite with len in *.
  replace (int.nat 4096) with (Z.to_nat 4096) in H0.
  rewrite -list_to_block_to_vals; len.
  iFrame.
  iExists _; iPureIntro.
  rewrite list_to_block_to_vals; len.
  eauto.
Qed.

Lemma circ_wf_advance:
  ∀ (newStart : u64) (σ : circΣ.t),
    circ_wf σ
    → int.val (start σ) ≤ int.val newStart
      ∧ int.val newStart ≤ int.val (start σ) + length (upds σ)
    → circ_wf
        (set start (λ _ : u64, newStart)
             (set upds (drop (Z.to_nat (int.val newStart - int.val (start σ)))) σ)).
Proof.
  destruct σ as [upds start].
  rewrite /circ_wf /circΣ.diskEnd; simpl; intros.
  len.
Qed.

Lemma diskEnd_advance_unchanged:
  ∀ (newStart : u64) (σ : circΣ.t),
    int.val (start σ) <= int.val newStart <= int.val (start σ) + length (upds σ) ->
    circΣ.diskEnd
        (set start (λ _ : u64, newStart)
             (set upds (drop (Z.to_nat (int.val newStart - int.val (start σ)))) σ))
    = circΣ.diskEnd σ.
Proof.
  rewrite /circΣ.diskEnd /=.
  intros.
  len.
Qed.

Lemma has_circ_updates_advance :
  ∀ (newStart : u64) (σ : circΣ.t) (addrs : list u64) (blocks : list Block)
    (Hbounds: int.val (start σ) <= int.val newStart <= int.val (start σ) + length (upds σ))
    (Hupds: has_circ_updates σ addrs blocks),
    has_circ_updates
        (set start (λ _ : u64, newStart)
             (set upds (drop (Z.to_nat (int.val newStart - int.val (start σ)))) σ)) addrs
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

Theorem wp_circular__Advance (Q: iProp Σ) γ d (newStart : u64) :
  {{{ is_circular γ ∗
    (∀ σ, P σ -∗
      ( (∃ σ' b, ⌜relation.denote (circ_advance newStart) σ σ' b⌝) ∧
        (∀ σ' b, ⌜relation.denote (circ_advance newStart) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q)))
  }}}
    Advance #d #newStart
  {{{ RET #(); Q }}}.
Proof using Ptimeless.
  iIntros (Φ) "[#Hcirc Hfupd] HΦ".
  wp_call.
  wp_apply wp_hdr2; iIntros (s hdr2) "[Hb Hextra]".
  iDestruct "Hextra" as (extra) "%".
  wp_apply (wp_Write_fupd (⊤ ∖ ↑N) Q with "[$Hb Hfupd]").
  { rewrite /is_circular.
    iInv "Hcirc" as ">Hcirc_inv" "Hclose".
    iDestruct "Hcirc_inv" as (σ) "[Hcirc_state HP]".
    iDestruct "Hcirc_state" as (Hwf addrs blocks Hupds) "(Hγ&Hlow)".
    iDestruct (circ_state_wf with "Hγ") as %(Hlen1&Hlen2).
    iDestruct "Hlow" as (hdr1 hdr2_0 hdr2extra Hhdr1 Hhdr2) "(Hhdr1&Hhdr2&Hblocks)".
    iDestruct ("Hfupd" with "HP") as "[% Hfupd]".
    destruct H0 as [σ' [[] Hstep]].
    iMod ("Hfupd" $! σ' () with "[//]") as "[HP' HQ]".
    simpl in Hstep |- *; monad_inv.

    iExists hdr2_0.
    iFrame "Hhdr2". iIntros "!> Hhdr2".
    iMod ("Hclose" with "[-HQ]").
    { iNext.
      iExists _; iFrame.
      iSplitR.
      - iPureIntro.
        apply circ_wf_advance; eauto.
      - iExists _, _; iFrame "Hγ".
        iSplitR; [ iPureIntro | ].
        { eapply has_circ_updates_advance; eauto; word. }
        iExists _, _, _; iFrame.
        iSplitR; auto.
        rewrite Hhdr1.
        iPureIntro.
        rewrite -> diskEnd_advance_unchanged by word.
        auto. }
    iModIntro; auto. }
  iIntros "[_ HQ]".
  wp_apply wp_Barrier.
  iApply ("HΦ" with "HQ").
Qed.

Fixpoint update_addrs (addrs: list u64) (start: Z) (upds: list update.t): list u64 :=
  match upds with
 | nil => addrs
 | u::upds => update_addrs (<[Z.to_nat (start `mod` LogSz) := u.(update.addr) ]> addrs) (start + 1) upds
  end.

Theorem wrap_small_log_addr (x:u64) :
  word.wrap (word:=u64_instance.u64) (2 + int.val x `mod` word.wrap (word:=u64_instance.u64) LogSz) =
  2 + int.val x `mod` LogSz.
Proof.
  unfold LogSz.
  change (word.wrap 511) with 511.
  rewrite wrap_small //.
  pose proof (Z.mod_bound_pos (int.val x) 511).
  word.
Qed.

Theorem wp_circularAppender__logBlocks γ c d
        (endpos : u64) (bufs : Slice.t)
        (addrs : list u64) (blocks : list Block) diskaddrslice (upds : list update.t) :
  int.val endpos + LogSz < 2^64 ->
  Z.of_nat (length upds) < LogSz ->
  length addrs = Z.to_nat LogSz ->
  {{{ is_circular γ ∗
      own γ.(addrs_name) (◯ Excl' addrs) ∗
      own γ.(blocks_name) (◯ Excl' blocks) ∗
      c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
      is_slice_small diskaddrslice uint64T 1 (u64val <$> addrs) ∗
      updates_slice bufs upds }}}
    circularAppender__logBlocks #c #d #endpos (slice_val bufs)
  {{{ blocks', RET #();
      let addrs' := update_addrs addrs (int.val endpos) upds in
      own γ.(addrs_name) (◯ Excl' addrs') ∗
      own γ.(blocks_name) (◯ Excl' blocks') ∗
      c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
      is_slice_small diskaddrslice uint64T 1 (u64val <$> addrs') ∗
      updates_slice bufs upds
  }}}.
Proof.
  iIntros (Hendpos_overflow Hfits_log Haddrs_len Φ) "(#Hcirc & Hγaddrs & Hγblocks & Hdiskaddrs & Hslice & Hupdslice) HΦ".
  wp_lam. wp_let. wp_let. wp_let.
  iDestruct "Hupdslice" as (bks) "[Hupdslice Hbks]".

  iDestruct (is_slice_small_sz with "Hupdslice") as %Hslen.
  rewrite fmap_length in Hslen.
  iDestruct (big_sepL2_length with "Hbks") as %Hslen2.

  wp_apply (wp_forSlice (fun i =>
    ∃ (addrs': list u64) (blocks': list Block),
      own γ.(addrs_name) (◯ Excl' addrs') ∗
      own γ.(blocks_name) (◯ Excl' blocks') ∗
      c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
      is_slice_small diskaddrslice uint64T 1 (u64val <$> addrs') ∗
      ( [∗ list] b_upd;upd ∈ bks;upds, let '{| update.addr := a; update.b := b |} := upd in
                                         is_block b_upd.2 b ∗ ⌜b_upd.1 = a⌝) ∗
      ⌜addrs' = update_addrs addrs (int.val endpos) (take (int.nat i) upds)⌝)%I
    with "[] [Hγaddrs Hγblocks Hdiskaddrs Hslice Hupdslice $Hbks]").

  2: {
    iFrame.
    iExists _, _; iFrame.
    rewrite take_0 //=.
  }

  2: {
    iIntros "[HI Hs]".
    iDestruct "HI" as (addrs' blocks') "(?&? & Haddrs&Hblocks&Hupds&->)".
    iApply "HΦ"; iFrame.
    rewrite -> take_ge by lia.
    iFrame.
    rewrite /updates_slice.
    iExists _; iFrame.
  }

  iIntros (i bk Φₗ) "!> [HI [% %]] HΦ".
  iDestruct "HI" as (addrs' blocks') "(Hγaddrs&Hγblocks&HdiskAddrs&Haddrs&Hbks&->)".
  rewrite list_lookup_fmap in H0.
  apply fmap_Some in H0.
  destruct H0 as [[addr bk_s] [Hbkseq ->]].
  destruct (list_lookup_lt _ upds (int.nat i)); first by word.
  iDestruct (big_sepL2_insert_acc with "Hbks") as "[Hi Hbks]"; eauto.
  destruct x as [addr_i b_i]; simpl.
  iDestruct "Hi" as "[Hi ->]".

  wp_pures.
  wp_apply wp_DPrintf.
  wp_pures.
  change (word.divu (word.sub 4096 8) 8) with (U64 LogSz).
  wp_apply (wp_Write_fupd with "[$Hi Hγaddrs Hγblocks]").
  { word_cleanup.
    2: unfold LogSz; auto.
    rewrite wrap_small_log_addr.
    word_cleanup.

    iInv "Hcirc" as ">HcircI" "Hclose".
    iModIntro.
    iDestruct "HcircI" as (σ) "[Hσ HP]".
    iDestruct "Hσ" as (Hwf addrs' blocks'' Hhas_upds) "(Hown&Hlow)".
    iDestruct (circ_state_wf with "Hown") as %[Hlen1 Hlen2].
    iDestruct "Hlow" as (hdr1 hdr2 hdr2extra Hhdr1 Hhdr2) "(Hd0&Hd1&Hd2)".
    pose proof (Z.mod_bound_pos (int.val endpos + int.val i) LogSz); intuition (try word).
    destruct (list_lookup_lt _ blocks'' (Z.to_nat $ (int.val endpos + int.val i) `mod` LogSz)) as [b ?]; first by word.
    iDestruct (disk_array_acc _ _ ((int.val endpos + int.val i) `mod` LogSz) with "[$Hd2]") as "[Hdi Hd2]"; eauto.
    { word. }
    iExists b.
    iFrame.
    iIntros "Hdi".
    iSpecialize ("Hd2" with "Hdi").
    iDestruct "Hown" as (_) "[Haddrs_auth Hblocks_auth]".
    (* iMod (ghost_var_update
            γ.(addrs_name)
                (update_addrs addrs (int.val endpos)
                              (take (S (int.nat i)) upds)) with "Haddrs_auth Hγaddrs") as "[Haddrs_auth Hγaddrs]". *)
    iMod (ghost_var_update γ.(blocks_name)
                               (<[Z.to_nat ((int.val endpos + int.val i) `mod` LogSz):=b_i]> blocks'') with "Hblocks_auth Hγblocks") as "[Hblocks_auth Hγblocks]".
    iApply ("Hclose" with "[-Hγaddrs Hγblocks]").
    { iModIntro.
      iExists _; iFrame "HP".
      iSplitR; first by auto.
      iExists _, _; iFrame.
      iSplitR.
      { iPureIntro.
        admit. (* has_circ_updates transition *) }
      iSplitR.
      { iPureIntro.
        admit. (* circ_low_wf transition *) }
      iExists hdr1, hdr2, hdr2extra.
      by iFrame.
    }
  }
Abort.

Theorem wp_circular__Append (Q: iProp Σ) γ d (endpos : u64) (bufs : Slice.t) (upds : list update.t) c (circAppenderList : list u64) :
  {{{ is_circular γ ∗
      updates_slice bufs upds ∗
      is_circular_appender γ c ∗
      (∀ σ, P σ -∗
        ( (∃ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝) ∧
          (∀ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q)))
  }}}
    circularAppender__Append #c #d #endpos (slice_val bufs)
  {{{ RET #(); Q }}}.
Proof using Ptimeless.
  iIntros (Φ) "(#Hcirc & Hslice & Hca & Hfupd) HΦ".
Admitted.

Theorem wp_recoverCircular (Q: iProp Σ) d σ γ :
  {{{ is_circular_state γ σ }}}
    recoverCircular #d
  {{{ (c:loc) (diskStart diskEnd: u64) (bufSlice:Slice.t) (upds: list update.t),
      RET (#c, #diskStart, #diskEnd, slice_val bufSlice);
      updates_slice bufSlice upds ∗
      is_circular_state γ σ ∗
      is_circular_appender γ c ∗
      ⌜σ.(circΣ.start) = diskStart⌝ ∗
      ⌜σ.(circΣ.upds) = upds⌝
  }}}.
Proof.
Abort.

End heap.
