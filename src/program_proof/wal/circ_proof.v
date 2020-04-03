From RecordUpdate Require Import RecordSet.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import marshal_proof util_proof.
From Perennial.program_proof Require Import disk_lib.

From Perennial.algebra Require Import deletable_heap.

From Perennial.Helpers Require Import Transitions.
Existing Instance r_mbind.

Definition LogSz := 511.

Hint Unfold LogSz : word.

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
Context `{!crashG Σ}.

Context `{!inG Σ (authR (optionUR (exclR (listO u64O))))}.
Context `{!inG Σ (authR (optionUR (exclR (listO blockO))))}.
Context `{!inG Σ fmcounterUR}.

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
  start <= endpos <= start + LogSz ∧
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
    ⌜circ_low_wf addrs blocks⌝ ∗
    own γ.(addrs_name) (◯ (Excl' addrs)) ∗
    own γ.(blocks_name) (◯ (Excl' blocks)) ∗
    circ ↦[circularAppender.S :: "diskAddrs"] (slice_val s) ∗
    is_slice_small s uint64T 1 (u64val <$> addrs).

Theorem is_circular_inner_wf γ addrs blocks :
  own γ.(addrs_name) (◯ Excl' addrs) ∗
  own γ.(blocks_name) (◯ Excl' blocks) -∗
  ▷ (∃ σ, is_circular_state γ σ ∗ P σ) -∗
  ▷ ⌜circ_low_wf addrs blocks⌝.
Proof.
  iIntros "[Hγaddrs Hγblocks] Hinv".
  iNext.
  iDestruct "Hinv" as (σ) "[[_ His_circ] _]".
  iDestruct "His_circ" as (addrs' blocks') "(_&Hown&_)".
  iDestruct "Hown" as "(%&Haddrs&Hblocks)".
  iDestruct (ghost_var_agree with "Haddrs Hγaddrs") as %->.
  iDestruct (ghost_var_agree with "Hblocks Hγblocks") as %->.
  auto.
Qed.

(* hmm, this doesn't seem doable... *)
Theorem is_circular_appender_wf γ addrs blocks :
  is_circular γ -∗
  own γ.(addrs_name) (◯ Excl' addrs) ∗
  own γ.(blocks_name) (◯ Excl' blocks) -∗
  |={⊤}=> ▷ ⌜circ_low_wf addrs blocks⌝.
Proof.
  iIntros "#Hcirc [Hγaddrs Hγblocks]".
  iInv "Hcirc" as "Hinv".
  iModIntro.
  iDestruct (is_circular_inner_wf with "[$Hγaddrs $Hγblocks] Hinv") as "Hwf".
  iSplitR.
  - admit.
  - iModIntro.
    iFrame.
Abort.

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

Theorem wp_hdr1 (circ: loc) (newStart: u64) s addrs :
  length addrs = Z.to_nat LogSz ->
  {{{ circ ↦[circularAppender.S :: "diskAddrs"] (slice_val s) ∗
       is_slice_small s uint64T 1 (u64val <$> addrs) }}}
    circularAppender__hdr1 #circ #newStart
  {{{ b_s b, RET slice_val b_s;
      circ ↦[circularAppender.S :: "diskAddrs"] (slice_val s) ∗
      is_slice_small s uint64T 1 (u64val <$> addrs) ∗
      is_block b_s b ∗
      ⌜Block_to_vals b = b2val <$> encode ([EncUInt64 newStart] ++ (EncUInt64 <$> addrs))⌝ }}}.
Proof.
  iIntros (Haddrlen Φ) "[HdiskAddrs Hs] HΦ".
  wp_call.
  wp_apply wp_new_enc.
  iIntros (enc) "[Henc %]".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc"); first by word.
  iIntros "Henc".
  wp_loadField.
  wp_apply (wp_Enc__PutInts with "[$Henc $Hs]"); first by word.
  iIntros "[Henc Hs]".
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s') "[Hs' %]".
  iApply "HΦ".
  iFrame.
  rewrite H in H0.
  autorewrite with len in *.
  change (int.nat 4096) with (Z.to_nat 4096) in H0.
  rewrite -list_to_block_to_vals; len.
  iFrame.
  iPureIntro.
  rewrite list_to_block_to_vals; len.
  replace (Z.to_nat (int.val 4096 - 8 - 8 * length addrs)) with 0%nat by word.
  rewrite replicate_0.
  rewrite -app_assoc app_nil_r //.
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

Hint Unfold circ_low_wf : word.

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
    iDestruct (circ_state_wf with "Hγ") as %Hlow_wf.
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
  word.wrap (word:=u64_instance.u64) (2 + int.val x `mod` word.wrap (word:=u64_instance.u64) LogSz) =
  2 + int.val x `mod` LogSz.
Proof.
  unfold LogSz.
  change (word.wrap 511) with 511.
  rewrite wrap_small //.
  mod_bound; word.
Qed.

Lemma mod_add_modulus a k :
  k ≠ 0 ->
  a `mod` k = (a + k) `mod` k.
Proof.
  intros.
  rewrite -> Z.add_mod by auto.
  rewrite -> Z.mod_same by auto.
  rewrite Z.add_0_r.
  rewrite -> Z.mod_mod by auto.
  auto.
Qed.

Lemma mod_sub_modulus a k :
  k ≠ 0 ->
  a `mod` k = (a - k) `mod` k.
Proof.
  intros.
  rewrite -> Zminus_mod by auto.
  rewrite -> Z.mod_same by auto.
  rewrite Z.sub_0_r.
  rewrite -> Z.mod_mod by auto.
  auto.
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
  length (circ_proof.upds σ) + int.val i < LogSz ->
  has_circ_updates σ addrs blocks ->
  has_circ_updates σ addrs (<[Z.to_nat ((circΣ.diskEnd σ + int.val i) `mod` LogSz) := bi]> blocks).
Proof.
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
  upds !! int.nat i = Some {| update.addr := addr_i; update.b := b_i |} ->
  update_blocks blocks endpos (take (S (int.nat i)) upds) =
  <[Z.to_nat ((endpos + int.val i) `mod` 511) := b_i]> (update_blocks blocks endpos (take (int.nat i) upds)).
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
  upds !! int.nat i = Some {| update.addr := addr_i; update.b := b_i |} ->
  update_addrs addrs endpos (take (S (int.nat i)) upds) =
  <[Z.to_nat ((endpos + int.val i) `mod` 511) := addr_i]> (update_addrs addrs endpos (take (int.nat i) upds)).
Proof.
  intros.
  erewrite take_S_r; eauto.
  rewrite update_addrs_S.
  f_equal. f_equal.
  apply lookup_lt_Some in H.
  rewrite -> firstn_length_le by lia.
  word.
Qed.

Theorem wp_circularAppender__logBlocks γ c d
        (endpos : u64) (bufs : Slice.t)
        (addrs : list u64) (blocks : list Block) diskaddrslice (upds : list update.t) Q :
  length addrs = Z.to_nat LogSz ->
  {{{ is_circular γ ∗
      own γ.(blocks_name) (◯ Excl' blocks) ∗
      c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
      is_slice_small diskaddrslice uint64T 1 (u64val <$> addrs) ∗
      updates_slice bufs upds ∗
      (∀ σ, P σ -∗
        (∃ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝) ∧
        (∀ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q))
  }}}
    circularAppender__logBlocks #c #d #endpos (slice_val bufs)
  {{{ RET #();
      let addrs' := update_addrs addrs (int.val endpos) upds in
      let blocks' := update_blocks blocks (int.val endpos) upds in
      own γ.(blocks_name) (◯ Excl' blocks') ∗
      c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
      is_slice_small diskaddrslice uint64T 1 (u64val <$> addrs') ∗
      updates_slice bufs upds ∗
      (∀ σ, P σ -∗
        (∃ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝) ∧
        (∀ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q))
  }}}.
Proof using Ptimeless.
  iIntros ( (* Hendpos_overflow Hfits_log *) Haddrs_len Φ) "(#Hcirc & Hγblocks & Hdiskaddrs & Hslice & Hupdslice & Hhasspace) HΦ".
  wp_lam. wp_let. wp_let. wp_let.
  iDestruct (updates_slice_len with "Hupdslice") as %Hupdlen.
  iDestruct "Hupdslice" as (bks) "[Hupdslice Hbks]".

  iDestruct (is_slice_sz with "Hupdslice") as %Hslen.
  rewrite fmap_length in Hslen.
  iDestruct (big_sepL2_length with "Hbks") as %Hslen2.

  iDestruct (is_slice_small_acc with "Hupdslice") as "[Hupdslice Hupdslice_rest]".

  wp_apply (wp_forSlice (fun i =>
    let addrs' := update_addrs addrs (int.val endpos) (take (int.nat i) upds) in
    let blocks' := update_blocks blocks (int.val endpos) (take (int.nat i) upds) in
    own γ.(blocks_name) (◯ Excl' blocks') ∗
    c ↦[circularAppender.S :: "diskAddrs"] (slice_val diskaddrslice) ∗
    is_slice_small diskaddrslice uint64T 1 (u64val <$> addrs') ∗
    ( [∗ list] b_upd;upd ∈ bks;upds, let '{| update.addr := a; update.b := b |} := upd in
                                       is_block b_upd.2 b ∗ ⌜b_upd.1 = a⌝) ∗
    (∀ σ, P σ -∗
      (∃ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝) ∧
      (∀ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q))
    )%I (* XXX why is %I needed? *)
    with "[] [$Hγblocks $Hdiskaddrs $Hslice $Hupdslice $Hhasspace $Hbks]").

  2: {
    iIntros "[HI Hupdslice]".
    iDestruct "HI" as "(?&? & Hblocks&Hupds&Hhasspace)".
    iApply "HΦ"; iFrame.
    rewrite -> take_ge by lia.
    iFrame.
    rewrite /updates_slice.
    iDestruct ("Hupdslice_rest" with "Hupdslice") as "Hupdslice".
    iExists _; iFrame.
  }

  iIntros (i bk Φₗ) "!> [HI [% %]] HΦ".
  iDestruct "HI" as "(Hγblocks&HdiskAddrs&Haddrs&Hbks&Hhasspace)".
  rewrite list_lookup_fmap in H0.
  apply fmap_Some in H0.
  destruct H0 as [[addr bk_s] [Hbkseq ->]].
  destruct (list_lookup_lt _ upds (int.nat i)); first by word.
  iDestruct (big_sepL2_lookup_acc with "Hbks") as "[Hi Hbks]"; eauto.
  destruct x as [addr_i b_i]; simpl.
  iDestruct "Hi" as "[Hi ->]".

  wp_pures.
  wp_apply wp_DPrintf.
  wp_pures.
  change (word.divu (word.sub 4096 8) 8) with (U64 LogSz).
  let blocks'' := constr:(<[Z.to_nat ((int.val endpos + int.val i) `mod` LogSz):=b_i]> (update_blocks blocks (int.val endpos) (take (int.nat i) upds))) in
  wp_apply (wp_Write_fupd (⊤ ∖ ↑N)
    (own γ.(blocks_name) (◯ Excl' blocks'') ∗
     ⌜ int.val endpos + Z.of_nat (length upds) < 2^64 ⌝ ∗
     (∀ σ, P σ -∗
       (∃ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝) ∧
       (∀ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q))
    )
    with "[$Hi Hγblocks Hhasspace]").
  { word_cleanup.
    rewrite wrap_small_log_addr.
    word_cleanup.

    iInv "Hcirc" as ">HcircI" "Hclose".
    iModIntro.
    iDestruct "HcircI" as (σ) "[Hσ HP]".
    iDestruct "Hσ" as (Hwf addrs' blocks'' Hhas_upds) "(Hown&Hlow)".
    iDestruct (circ_state_wf with "Hown") as %Hlowwf.
    iDestruct (circ_state_wf with "Hown") as %[Hlen1 Hlen2].
    iDestruct "Hlow" as (hdr1 hdr2 hdr2extra Hhdr1 Hhdr2) "(Hd0&Hd1&Hd2)".
    pose proof (Z.mod_bound_pos (int.val endpos + int.val i) LogSz); intuition (try word).
    destruct (list_lookup_lt _ blocks'' (Z.to_nat $ (int.val endpos + int.val i) `mod` LogSz)) as [b ?]; first by word.
    iDestruct (disk_array_acc _ _ ((int.val endpos + int.val i) `mod` LogSz) with "[$Hd2]") as "[Hdi Hd2]"; eauto.
    { word. }
    iExists b.

    destruct (decide (length (circ_proof.upds σ ++ upds) ≤ LogSz ∧
                      int.val endpos = circΣ.diskEnd σ ∧
                      int.val endpos + Z.of_nat (length upds) < 2^64)).
    2: {
      iDestruct ("Hhasspace" with "HP") as "[Hhasspace _]".
      iDestruct "Hhasspace" as (σ' b0) "%".
      monad_inv.
      simpl in *. word.
    }

    word_cleanup.
    iFrame.
    iIntros "Hdi".
    iSpecialize ("Hd2" with "Hdi").
    iDestruct "Hown" as (_) "[Haddrs_auth Hblocks_auth]".
    iDestruct (ghost_var_agree γ.(blocks_name) with "Hblocks_auth Hγblocks") as %->.
    iMod (ghost_var_update γ.(blocks_name) _
            with "Hblocks_auth Hγblocks") as "[Hblocks_auth Hγblocks]".
    iFrame "Hγblocks".
    iMod ("Hclose" with "[-]").
    { iModIntro.
      iExists _; iFrame "HP".
      iSplitR; first by auto.
      iExists _, _; iFrame.
      iSplitR.
      { iPureIntro.
        generalize dependent (update_blocks blocks (int.val endpos)
                 (take (int.nat i) upds)); intros blocks' **.
        replace (int.val endpos) with (circΣ.diskEnd σ) by word.
        eapply has_circ_updates_blocks; eauto.
        autorewrite with len in *. word.
      }
      iSplitR.
      { iPureIntro.
        eapply circ_low_wf_blocks; eauto.
      }
      iExists hdr1, hdr2, hdr2extra.
      by iFrame.
    }
    iPureIntro. word.
  }
  iIntros "(Hs & Hγblocks & % & Hhasspace)".
  wp_loadField.
  wp_apply (wp_SliceSet with "[$Haddrs]").
  { iPureIntro.
    split; auto.
    rewrite list_lookup_fmap.
    apply fmap_is_Some.
    change (word.divu (word.sub 4096 8) 8) with (U64 511).
    word_cleanup.
    apply lookup_lt_is_Some_2; len.
    rewrite Haddrs_len.
    pose proof (Z_mod_lt (int.val (word.add endpos i)) 511).
    (* XXX why doesn't word work? *)
    lia.
  }
  iIntros "Haddrs".
  iApply "HΦ".
  change (word.divu (word.sub 4096 8) 8) with (U64 511).
  word_cleanup.
  iFrame.
  iSplitL "Hγblocks".
  { replace (Z.to_nat (int.val i + 1)) with (S (int.nat i)) by lia.
    erewrite update_blocks_take_S; eauto. }
  iSplitL "Haddrs".
  { replace (Z.to_nat (int.val i + 1)) with (S (int.nat i)) by lia.
    erewrite update_addrs_take_S; eauto.
    rewrite list_fmap_insert.
    replace (int.val (word.add endpos i)) with (int.val endpos + int.val i) by word.
    iFrame.
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
    replace (Z.to_nat $ i - endpos) with
        (S $ Z.to_nat $ i - (endpos + 1)) by lia.
    reflexivity.
Qed.

Lemma has_circ_updates_app upds0 start addrs blocks (endpos : u64) upds :
  int.val endpos = circΣ.diskEnd {| circΣ.upds := upds0; circΣ.start := start |} ->
  length (upds0 ++ upds) ≤ LogSz ->
  circ_low_wf addrs (update_blocks blocks (int.val endpos) upds) ->
  has_circ_updates
    {| circΣ.upds := upds0; circΣ.start := start |} addrs
    (update_blocks blocks (int.val endpos) upds) ->
  has_circ_updates
    {| circΣ.upds := upds0 ++ upds; circΣ.start := start |}
    (update_addrs addrs (int.val endpos) upds)
    (update_blocks blocks (int.val endpos) upds).
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
    replace (Z.to_nat (int.val start + i - int.val endpos)) with
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

Hint Resolve circ_low_wf_log_blocks.


Lemma circ_low_wf_update_addrs
      (endpos : u64) (upds : list update.t) (addrs : list u64)
      (blocks' : list Block) :
  circ_low_wf addrs blocks'
  → circ_low_wf (update_addrs addrs (int.val endpos) upds)
                (update_blocks blocks' (int.val endpos) upds).
Proof.
  rewrite /circ_low_wf; len.
Qed.

Theorem wp_circular__Append (Q: iProp Σ) γ d (endpos : u64) (bufs : Slice.t) (upds : list update.t) c (circAppenderList : list u64) :
  {{{ is_circular γ ∗
      updates_slice bufs upds ∗
      is_circular_appender γ c ∗
      (∀ σ, P σ -∗
        ( (∃ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝) ∧
          (∀ σ' b, ⌜relation.denote (circ_append upds endpos) σ σ' b⌝ ={⊤ ∖↑ N}=∗ P σ' ∗ Q)))
  }}}
    circularAppender__Append #c #d #endpos (slice_val bufs)
  {{{ RET #(); Q ∗
      updates_slice bufs upds ∗
      is_circular_appender γ c }}}.
Proof using Ptimeless.
  iIntros (Φ) "(#Hcirc & Hslice & Hca & Hfupd) HΦ".
  wp_call.
  iDestruct "Hca" as (bk_s addrs blocks' Hlow_wf) "(Hγaddrs&Hγblocks&HdiskAddrs&Haddrs)".

  wp_apply (wp_circularAppender__logBlocks with "[$Hcirc $Hγblocks $HdiskAddrs $Haddrs $Hslice $Hfupd]"); try word.
  iIntros "(Hγblocks&HdiskAddrs&Hs&Hupds&Hfupd)".
  iDestruct (updates_slice_len with "Hupds") as %Hbufsz.
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  wp_apply (wp_hdr1 with "[$HdiskAddrs $Hs]"); first by len.
  iIntros (b_s b) "(HdiskAddrs&Hs&Hb&%)".
  wp_pures.

  wp_apply (wp_Write_fupd _
    (
      Q ∗
      own γ.(blocks_name) (◯ Excl' (update_blocks blocks' (int.val endpos) upds)) ∗
      own γ.(addrs_name) (◯ Excl' (update_addrs addrs (int.val endpos) upds))
    ) with "[Hb Hγblocks Hγaddrs Hfupd]").
  {
    iDestruct (is_slice_small_sz with "Hb") as %Hslen.
    rewrite fmap_length in Hslen.

    iFrame "Hb".

    iInv N as ">Hcircopen" "Hclose".
    iDestruct "Hcircopen" as (σ) "[[% Hcs] HP]".
    iDestruct "Hcs" as (addrs0 blocks0 Hupds) "[Hown Hlow]".
    iDestruct "Hown" as (Hlow_wf') "[Haddrs Hblocks]".
    iDestruct "Hlow" as (hdr1 hdr2 hdr2extra Hhdr1 Hhdr2) "(Hd0 & Hd1 & Hd2)".
    iExists _. iFrame "Hd0".
    iModIntro.
    iIntros "Hd0".

    iDestruct (ghost_var_agree with "Hblocks Hγblocks") as %->.
    iDestruct (ghost_var_agree with "Haddrs Hγaddrs") as %->.
    iMod (ghost_var_update γ.(addrs_name) (update_addrs addrs (int.val endpos) upds) with "Haddrs Hγaddrs") as "[Haddrs Hγaddrs]".

    iDestruct ("Hfupd" with "HP") as "[Hex Hfupd]".
    iDestruct "Hex" as (eσ' eb) "Hex".
    iDestruct "Hex" as %Hex.

    iSpecialize ("Hfupd" $! eσ' eb).
    simpl in Hex. monad_inv.

    iDestruct ("Hfupd" with "[]") as "Hfupd".
    { iPureIntro. repeat econstructor; lia. }

    iMod "Hfupd" as "[HP HQ]". iFrame.
    iApply "Hclose".

    iNext. iExists _. iFrame.
    destruct σ. rewrite /=.
    iSplitR.
    { iPureIntro.
      simpl in H4. rewrite /set /=.
      apply circ_wf_app; eauto.
    }
    iExists _, _; iFrame "Haddrs Hblocks".
    iSplitR.
    { iPureIntro.
      simpl in H4. rewrite /set /=.
      apply has_circ_updates_app; eauto.
    }
    iSplitR; first by eauto.
    iExists _, _, _. iFrame.
    iPureIntro; intuition.
    { rewrite H. f_equal. f_equal. f_equal.
      f_equal. f_equal. rewrite /circΣ.diskEnd.
      rewrite /set /= in H4 |- *.
      autorewrite with len in H4 |- *.
      destruct H0 as (?&?&?).
      unfold circΣ.diskEnd in *.
      cbn [circ_proof.start circ_proof.upds] in *.
      word. }
    rewrite Hhdr2. eauto.
  }
  iIntros "[Hb_s (HQ & Ho1 & Ho2)]".
  wp_apply wp_Barrier.
  iApply ("HΦ" with "[$HQ Ho1 Ho2 HdiskAddrs Hs $Hupds]").
  iExists _, _, _. iFrame.
  eauto using circ_low_wf_update_addrs.

  Unshelve.
  all: eauto. (* TODO: why? *)
Qed.

Theorem wp_SliceAppend_update stk E bufSlice (a:u64) (b_s: Slice.t) (b: Block) upds :
  int.val bufSlice.(Slice.sz) + 1 < 2^64 ->
  {{{ updates_slice bufSlice upds ∗
      is_block b_s b }}}
    SliceAppend (struct.t Update.S) (slice_val bufSlice) (#a, (slice_val b_s, #()))%V @ stk; E
  {{{ (bufSlice': Slice.t), RET (slice_val bufSlice');
      updates_slice bufSlice' (upds ++ [update.mk a b]) }}}.
Proof.
  iIntros (Hsz Φ) "[Hupds Hb] HΦ".
  iDestruct "Hupds" as (bk_s) "[Hupds_s Hblocks]".
  (* TODO: replace opacity with a proper sealing plan *)
  Transparent slice.T.
  wp_apply (wp_SliceAppend with "[Hupds_s]"); eauto.
  Opaque slice.T.
  iIntros (s') "Hs'".
  iApply "HΦ".
  iExists _; iFrame.
  iSplitL "Hs'".
  2: {
    iApply (big_sepL2_app _ _ [(a, b_s)] with "Hblocks").
    simpl. iFrame. done.
  }
  iExactEq "Hs'"; f_equal.
  rewrite fmap_app. auto.
Qed.

Theorem wp_recoverCircular (Q: iProp Σ) d σ γ :
  {{{ is_circular_state γ σ }}}
    recoverCircular #d
  {{{ γ' (c:loc) (diskStart diskEnd: u64) (bufSlice:Slice.t) (upds: list update.t),
      RET (#c, #diskStart, #diskEnd, slice_val bufSlice);
      updates_slice bufSlice upds ∗
      is_circular_state γ' σ ∗
      is_circular_appender γ' c ∗
      ⌜σ.(circΣ.start) = diskStart⌝ ∗
      ⌜σ.(circΣ.upds) = upds⌝
  }}}.
Proof.
  iIntros (Φ) "Hcs HΦ".

  Opaque struct.t.
  wp_call.

  iDestruct "Hcs" as (Hwf addrs0 blocks0 Hupds) "(Hown & Hlow)".
  iDestruct "Hown" as (Hlow_wf) "[Haddrs Hblocks]".
  iDestruct "Hlow" as (hdr1 hdr2 hdr2extra Hhdr1 Hhdr2) "(Hd0 & Hd1 & Hd2)".
  wp_apply (wp_Read with "[Hd0]").
  { iFrame. }
  iIntros (s0) "[Hd0 Hs0]".
  wp_pures.
  wp_apply (wp_NewDec _ _ _ _ nil with "[Hs0]").
  { iApply is_slice_to_small.
    rewrite Hhdr1. rewrite app_nil_r. iFrame. }
  iIntros (dec0) "[Hdec0 %]".
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec0"); iIntros "Hdec0".
  wp_pures.
  wp_apply (wp_Dec__GetInts _ _ _ _ _ nil with "[Hdec0]").
  { rewrite app_nil_r. iFrame.
    change (word.divu (word.sub 4096 8) 8) with (U64 LogSz).
    unfold circ_low_wf in Hlow_wf; intuition.
  }
  iIntros (addrs) "[Hdec0 Hdiskaddrs]".
  wp_pures.

  wp_apply (wp_Read with "[Hd1]").
  { iFrame. }
  iIntros (s1) "[Hd1 Hs1]".
  wp_pures.
  wp_apply (wp_NewDec with "[Hs1]").
  { iApply is_slice_to_small.
    rewrite Hhdr2. iFrame. }
  iIntros (dec1) "[Hdec1 %]".
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec1"); iIntros "Hdec1".
  wp_pures.

  wp_apply wp_ref_of_zero; eauto.
  iIntros (bufsloc) "Hbufsloc".
  wp_pures.

  wp_apply wp_ref_to; eauto.
  iIntros (pos) "Hpos".

  wp_pures.
  wp_apply (wp_forUpto' (fun i =>
    (∃ bufSlice,
      bufsloc ↦[slice.T (struct.t Update.S)] (slice_val bufSlice) ∗
      updates_slice bufSlice (take (int.nat i - int.nat σ.(start)) σ.(upds))) ∗
      is_slice_small addrs uint64T 1 (u64val <$> addrs0) ∗
      2 d↦∗ blocks0
    )%I with "[] [Hbufsloc $Hpos $Hd2 Hdiskaddrs]").
  - word_cleanup.
    destruct Hwf.
    rewrite /circΣ.diskEnd.
    word.
  - iIntros (i Φₗ) "!> (HI&Hpos&%) HΦ".
    iDestruct "HI" as "(Hbufs&Hdiskaddrs&Hd2)".
    iDestruct "Hbufs" as (bufSlice) "[Hbufsloc Hupds]".
    iDestruct (updates_slice_len with "Hupds") as %Hupdslen.
    wp_pures.
    wp_apply (wp_load with "[Hpos]"); [ | iIntros "Hpos" ].
    { iDestruct "Hpos" as "[[Hpos _] %]".
      simpl.
      rewrite loc_add_0.
      iFrame. }
    wp_pures.
    change (word.divu (word.sub 4096 8) 8) with (U64 LogSz).
    destruct (list_lookup_lt _ addrs0 (Z.to_nat $ int.val i `mod` LogSz)) as [a Halookup].
    { destruct Hlow_wf.
      mod_bound; word. }
    wp_apply (wp_SliceGet with "[$Hdiskaddrs]"); eauto.
    { iPureIntro.
      rewrite list_lookup_fmap.
      word_cleanup.
      rewrite Halookup.
      eauto. }
    iIntros "[Hdiskaddrs _]".
    wp_apply (wp_load with "Hpos"); iIntros "Hpos".
    wp_pures.
    change (word.divu (word.sub 4096 8) 8) with (U64 LogSz).
    destruct (list_lookup_lt _ blocks0 (Z.to_nat $ int.val i `mod` LogSz)) as [b Hblookup].
    { destruct Hlow_wf.
      mod_bound; word. }
    iDestruct (disk_array_acc _ blocks0 (int.val i `mod` LogSz) with "[Hd2]") as "[Hdi Hd2']"; eauto.
    { mod_bound; word. }
    wp_apply (wp_Read with "[Hdi]").
    { iExactEq "Hdi".
      f_equal.
      mod_bound; word. }
    iIntros (b_s) "[Hdi Hb_s]".
    wp_load.

    iDestruct ("Hd2'" with "[Hdi]") as "Hd2".
    { iExactEq "Hdi".
      f_equal.
      mod_bound; word. }
    rewrite list_insert_id; eauto.

    wp_apply (wp_SliceAppend_update with "[$Hupds Hb_s]").
    { autorewrite with len in Hupdslen.
      word. }
    { iApply is_slice_to_small. iFrame. }
    iIntros (bufSlice') "Hupds'".
    wp_store.

    iApply "HΦ".
    iFrame.
    iSplitR "Hpos".
    { iExists _. iFrame.
      iExactEq "Hupds'".
      f_equal.
      rewrite /circΣ.diskEnd in H1.
      word_cleanup.
      revert H1; word_cleanup; intros.
      replace (Z.to_nat (int.val i + 1) - int.nat (start σ))%nat with (S (int.nat i - int.nat (start σ))) by admit.
      erewrite take_S_r; eauto.
      admit. }

    iSplitL; auto.
    { iSplitL. { rewrite loc_add_0. iFrame. } done. }

  - iDestruct (is_slice_to_small with "Hdiskaddrs") as "Hdiskaddrs".
    iFrame.
    rewrite zero_slice_val.
    iExists _. iFrame.
    iExists nil; simpl.
    iSplitL.
    { iApply is_slice_zero. }
    replace (int.nat (start σ) - int.nat (start σ))%nat with 0%nat by lia.
    rewrite take_0.
    rewrite big_sepL2_nil.
    auto.

  - iIntros "[(HI & Hdiskaddrs & Hd2) Hpos]".
    iDestruct "HI" as (bufSlice) "[Hbufsloc Hupds]".
    Transparent struct.t.
    wp_apply wp_allocStruct; first by eauto.
    Opaque struct.t.
    iIntros (ca) "Hca".
    wp_load.

    iMod (ghost_var_alloc (addrs0 : listO u64O)) as (addrs_name') "[Haddrs' Hγaddrs]".
    iMod (ghost_var_alloc (blocks0 : listO blockO)) as (blocks_name') "[Hblocks' Hγblocks]".
    set (γ' := {| addrs_name := addrs_name'; blocks_name := blocks_name' |}).

    wp_pures.
    iApply ("HΦ" $! γ').
    iFrame.
    iSplitR "Hca Hdiskaddrs Hγaddrs Hγblocks".
    { iSplitR; eauto.
      iExists _, _.
      iSplitR; eauto.
      iSplitL "Haddrs' Hblocks'".
      { iSplitR; eauto.
        iFrame. }
      iExists _, _, _.
      iFrame.
      iPureIntro; eauto.
    }
    iSplitL.
    {
      iExists _, _, _.
      iDestruct (struct_fields_split with "Hca") as "[Hca _]".
      by iFrame. }
    iPureIntro; intuition eauto.
    rewrite take_ge; auto.
    rewrite /circΣ.diskEnd /=.
    destruct Hwf; word.
Admitted.

Theorem wpc_recoverCircular stk k E1 E2 (Q: iProp Σ) d σ γ :
  {{{ is_circular_state γ σ }}}
    recoverCircular #d @ stk; k; E1; E2
  {{{ γ' (c:loc) (diskStart diskEnd: u64) (bufSlice:Slice.t) (upds: list update.t),
      RET (#c, #diskStart, #diskEnd, slice_val bufSlice);
      updates_slice bufSlice upds ∗
      is_circular_state γ' σ ∗
      is_circular_appender γ' c ∗
      ⌜σ.(circΣ.start) = diskStart⌝ ∗
      ⌜σ.(circΣ.upds) = upds⌝
  }}}
  {{{ is_circular_state γ σ }}}.
Proof.
  iIntros (Φ Φc) "Hcs HΦ".

  Opaque struct.t.
  rewrite /recoverCircular.
  wpc_pures; first iFrame.

  iDestruct "Hcs" as (Hwf addrs0 blocks0 Hupds) "(Hown & Hlow)".
  iDestruct "Hown" as (Hlow_wf) "[Haddrs Hblocks]".
  iDestruct "Hlow" as (hdr1 hdr2 hdr2extra Hhdr1 Hhdr2) "(Hd0 & Hd1 & Hd2)".

  wpc_apply (wpc_Read with "[Hd0]"); first iFrame.
  iSplit.
  (* XXX why do we still need to re-prove the invariant with WPC? *)
  { iDestruct "HΦ" as "[HΦc _]". iIntros "Hd0". iApply "HΦc".
    iSplitR; eauto.
    iExists _, _. iSplitR; eauto.
    iFrame. iSplitR; eauto.
    iExists _, _, _. iFrame. eauto. }
Admitted.

End heap.
