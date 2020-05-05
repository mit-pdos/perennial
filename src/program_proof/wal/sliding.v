From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Export NamedProps.

From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Export wal.lib.
From Perennial.program_proof Require Import wal.highest.

Module slidingM.
  Record t :=
    mk { log: list update.t;
         start: u64;
         mutable: u64; }.
  Global Instance _eta : Settable _ := settable! mk <log; start; mutable>.
  Global Instance _witness : Inhabited t := populate!.

  Definition endPos (σ:t): u64 :=
    word.add σ.(start) (U64 $ Z.of_nat $ length σ.(log)).
  Definition numMutable (σ:t): u64 :=
    word.sub σ.(mutable) σ.(start).
  Definition addrPosMap (σ:t): gmap u64 u64 :=
    compute_memLogMap σ.(log) σ.(start).

  Definition wf (σ:t) :=
    int.val σ.(start) ≤ int.val σ.(mutable) ∧
    int.val σ.(start) + length σ.(log) < 2^64 ∧
    (* TODO: derive this from the invariant *)
    int.val (numMutable σ) <= length σ.(log).
End slidingM.

Section goose_lang.
Context `{!heapG Σ}.

Implicit Types (l: loc) (σ: slidingM.t).

Definition readonly_log logSlice σ : iProp Σ :=
      readonly (updates_slice_frag
                  (slice_take logSlice (struct.t Update.S) (slidingM.numMutable σ)) 1
                  (take (int.nat (slidingM.numMutable σ)) σ.(slidingM.log))).

Definition mutable_log logSlice σ : iProp Σ :=
  "%logSlice_wf" ∷ ⌜int.nat logSlice.(Slice.sz) = length σ.(slidingM.log)⌝ ∗
  "log_mutable" ∷ updates_slice_frag
        (slice_skip logSlice (struct.t Update.S) (slidingM.numMutable σ)) 1
        (drop (int.nat (slidingM.numMutable σ)) σ.(slidingM.log)).

Definition is_sliding (l: loc) (σ: slidingM.t) : iProp Σ :=
  "%Hwf" ∷ ⌜slidingM.wf σ⌝ ∗
  "Hinv" ∷ ∃ (logSlice: Slice.t) (addrPosPtr: loc),
    "log" ∷ l ↦[sliding.S :: "log"] (slice_val logSlice) ∗
    "start" ∷ l ↦[sliding.S :: "start"] #σ.(slidingM.start) ∗
    "mutable" ∷ l ↦[sliding.S :: "mutable"] #σ.(slidingM.mutable) ∗
    "addrPos" ∷ l ↦[sliding.S :: "addrPos"] #addrPosPtr ∗
    "#log_readonly" ∷ readonly_log logSlice σ ∗
    "log_mutable" ∷ mutable_log logSlice σ ∗
    "is_addrPos" ∷ is_map addrPosPtr (slidingM.addrPosMap σ).

Theorem is_sliding_wf l σ : is_sliding l σ -∗ ⌜slidingM.wf σ⌝.
Proof.
  iIntros "H"; iNamed "H"; auto.
Qed.

Lemma take_0 {A} (l: list A) : take 0 l = [].
Proof. reflexivity. Qed.

Lemma compute_memLogMap_nil start : compute_memLogMap nil start = ∅.
Proof.
  rewrite /compute_memLogMap.
  simpl.
  rewrite fmap_empty //.
Qed.

Theorem find_highest_index_app1 poss (pos: u64) :
  find_highest_index (poss ++ [pos]) pos = Some (length poss).
Proof.
  rewrite find_highest_index'_ok.
  induction poss; simpl.
  { destruct (decide (pos = pos)); congruence. }
  rewrite IHposs //=.
Qed.

Theorem find_highest_index_app_ne poss (pos pos': u64) :
  pos ≠ pos' ->
  find_highest_index (poss ++ [pos]) pos' =
  find_highest_index poss pos'.
Proof.
  induction poss; simpl; intros.
  { destruct (decide (pos' = pos)); congruence. }
  rewrite IHposs; auto.
Qed.

Theorem memLogMap_append log start u (i: u64) :
  int.nat i = length log ->
  int.nat start + length log < 2^64 ->
  compute_memLogMap (log ++ [u]) start =
  map_insert (compute_memLogMap log start) u.(update.addr) (word.add start i).
Proof.
  intros Hlen Hoverflow.
  rewrite /compute_memLogMap.
  rewrite fmap_app; simpl.
  destruct u as [a0 ?]; simpl.
  apply map_eq; intros a.
  rewrite lookup_fmap.
  rewrite pos_indices_lookup.
  rewrite -option_fmap_compose.
  destruct (decide (a = a0)); subst; [ rewrite lookup_insert | rewrite lookup_insert_ne; auto ].
  - rewrite find_highest_index_app1 /=.
    autorewrite with len.
    f_equal.
    word.
  - rewrite -> find_highest_index_app_ne by auto.
    rewrite lookup_fmap.
    rewrite pos_indices_lookup.
    rewrite -option_fmap_compose.
    auto.
Qed.

Theorem wp_mkSliding s log (start: u64) :
  int.val start + length log < 2^64 ->
  {{{ updates_slice_frag s 1 log }}}
    mkSliding (slice_val s) #start
  {{{ (l: loc), RET #l; is_sliding l (slidingM.mk log start start) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  rewrite /mkSliding; wp_pures.
  wp_apply (wp_NewMap u64 (t:=uint64T)).
  iIntros (addrPosPtr) "His_map".
  wp_pures.
  iDestruct (updates_slice_frag_len with "Hs") as %Hlen.
  iDestruct "Hs" as (bks) "[Hs Hblocks]".

  wp_apply (wp_forSlice
              (fun i => "Hm" ∷ is_map addrPosPtr
                               (compute_memLogMap (take (int.nat i) log) start) ∗
                      "Hblocks" ∷ [∗ list] b_upd;upd ∈ bks;log, disk_lib.is_block b_upd.2 1 upd.(update.b)
                                                                ∗ ⌜b_upd.1 = upd.(update.addr)⌝
              )%I
           with "[] [His_map $Hblocks $Hs]").
  2: {
    rewrite take_0 compute_memLogMap_nil.
    iFrame.
  }
  { clear Φ.
    iIntros (i us).
    iIntros "!>" (Φ) "(HI&%Hlt&%Hlookup) HΦ"; iNamed "HI".
    rewrite list_lookup_fmap in Hlookup.
    apply fmap_Some_1 in Hlookup as [uv [Hlookup ->]].
    wp_pures.
    wp_apply (wp_MapInsert with "Hm"); auto.
    iIntros "Hm".
    iApply "HΦ".
    replace (int.nat (word.add i 1)) with (1 + int.nat i)%nat by word.
    destruct (list_lookup_lt _ log (int.nat i)) as [u Hlookup']; first by word.
    iDestruct (big_sepL2_lookup_acc with "Hblocks") as "[[Hb %Huaddr] Hblocks]"; eauto.
    iSpecialize ("Hblocks" with "[$Hb //]").
    iFrame "Hblocks".
    rewrite Huaddr.
    erewrite take_S_r; eauto.
    erewrite memLogMap_append; eauto; len.
  }

  rewrite -> take_ge by len.
  iIntros "(HI&Hs)"; iNamed "HI".
  wp_pures.
  wp_apply wp_slice_len.
  wp_apply wp_allocStruct; auto.
  iIntros (l) "Hl".
  iDestruct (struct_fields_split with "Hl") as "(Hf1&Hf2&Hf3&Hf4)".
  iApply "HΦ".
  iAssert (updates_slice_frag s 1 log) with "[Hs Hblocks]" as "Hlog".
  { iExists _; iFrame. }
Admitted.

Theorem is_slice_small_take_drop s t q n vs :
  (int.nat n <= int.nat s.(Slice.sz))%nat ->
   is_slice_small (slice_skip s t n) t q (drop (int.nat n) vs) ∗
   is_slice_small (slice_take s t n) t q (take (int.nat n) vs) ⊣⊢
  is_slice_small s t q vs.
Proof.
  intros Hbound.
  iSplit.
  - iIntros "(Hs1 & Hs2)".
    iDestruct "Hs1" as "[Ha1 %Hlen1]".
    iDestruct "Hs2" as "[Ha2 %Hlen2]".
    autorewrite with len in Hlen1, Hlen2.
    simpl in Hlen1, Hlen2 |- *.
    iDestruct (array_split with "[$Ha1 $Ha2]") as "Ha"; try word.
    iFrame.
    iPureIntro.
    revert Hlen1; word.
  - iIntros "Hs".
    iDestruct "Hs" as "[Ha %Hlen]".
    iDestruct (array_split (int.nat n) with "Ha") as "[Ha1 Ha2]"; try word.
    rewrite Z2Nat.id; try word.
    iFrame.
    iPureIntro; simpl; len.
Qed.

Theorem is_slice_small_take_drop_1 s t q n vs :
  (int.nat n <= int.nat s.(Slice.sz))%nat ->
  is_slice_small (slice_skip s t n) t q (drop (int.nat n) vs) ∗
                  is_slice_small (slice_take s t n) t q (take (int.nat n) vs) -∗
  is_slice_small s t q vs.
Proof.
  intros Hbound.
  rewrite is_slice_small_take_drop; auto.
Qed.

Theorem updates_slice_frag_combine s q (n: u64) log :
  (int.nat n <= int.nat s.(Slice.sz))%nat ->
  updates_slice_frag (slice_skip s (struct.t Update.S) n) q (drop (int.nat n) log) ∗
  updates_slice_frag (slice_take s (struct.t Update.S) n) q (take (int.nat n) log) -∗
  updates_slice_frag s q log.
Proof.
  iIntros (Hbound) "[Hs2 Hs1]".
  iDestruct (updates_slice_frag_len with "Hs1") as %Hlenlog1.
  iDestruct (updates_slice_frag_len with "Hs2") as %Hlenlog2.
  iDestruct "Hs1" as (bks1) "[Hs1 Hblocks1]".
  iDestruct "Hs2" as (bks2) "[Hs2 Hblocks2]".
  iDestruct (is_slice_small_sz with "Hs1") as %Hsz1.
  iDestruct (is_slice_small_sz with "Hs2") as %Hsz2.
  autorewrite with len in *.
  simpl in *.
  iDestruct  (is_slice_small_take_drop_1 s _ _ n (update_val <$> bks1 ++ bks2) with "[Hs1 Hs2]") as "Hs".
  { word. }
  { rewrite fmap_app.
    rewrite drop_app_ge; len.
    rewrite take_app_le; len.
    rewrite take_ge; len.
    rewrite Hsz1 minus_diag drop_0.
    iFrame. }
  iExists _; iFrame.
  rewrite -{3}(take_drop (int.nat n) log).
  iApply (big_sepL2_app with "Hblocks1 Hblocks2").
Qed.

Theorem updates_slice_frag_split s q (n: u64) log :
  (int.nat n <= int.nat s.(Slice.sz))%nat ->
  updates_slice_frag s q log -∗
  updates_slice_frag (slice_skip s (struct.t Update.S) n) q (drop (int.nat n) log) ∗
  updates_slice_frag (slice_take s (struct.t Update.S) n) q (take (int.nat n) log).
Proof.
  iIntros (Hbound) "Hs".
  iDestruct (updates_slice_frag_len with "Hs") as %Hlen.
  iDestruct "Hs" as (bks) "[Hs Hblocks]".
  iDestruct (is_slice_small_sz with "Hs") as %Hbks_len.
  autorewrite with len in Hbks_len.
  iDestruct (is_slice_small_take_drop _ _ _ n with "Hs") as "[Hs1 Hs2]"; eauto.
  rewrite -{1}(take_drop (int.nat n) log) -{1}(take_drop (int.nat n) bks).
  iDestruct (big_sepL2_app_inv with "Hblocks") as "[Hblocks2 Hblocks1]".
  { len. }
  rewrite -fmap_drop -fmap_take.
  iSplitL "Hs1 Hblocks1".
  - iExists _; iFrame.
  - iExists _; iFrame.
Qed.

Hint Unfold slidingM.wf : word.
Hint Unfold slidingM.numMutable : word.

Theorem memLog_combine s σ :
  slidingM.wf σ ->
  readonly_log s σ -∗
  mutable_log s σ -∗
  |={⊤}=> ∃ q, updates_slice_frag s q (slidingM.log σ) ∗
       (updates_slice_frag s q (slidingM.log σ) -∗ mutable_log s σ).
Proof.
  rewrite /mutable_log.
  iIntros (Hwf) "Hread Hmut".
  iDestruct "Hmut" as "(%logSlice_wf&Hmut)"; rewrite /named.
  iMod (readonly_load_lt with "Hread") as (q) "[%Hqlt HreadLog]"; first by auto.
  iModIntro.
  destruct (Qextra.Qp_split_1 _ Hqlt) as [q' Hqq'].
  iEval (rewrite -Hqq') in "Hmut".
  iDestruct (fractional.fractional_split_1 with "Hmut") as "[Hmut Hq']".
  iDestruct (updates_slice_frag_len with "HreadLog") as %Hlen1.
  iDestruct (updates_slice_frag_len with "Hmut") as %Hlen2.
  autorewrite with len in Hlen1, Hlen2.
  simpl in Hlen1, Hlen2.
  iDestruct (updates_slice_frag_combine with "[$Hmut $HreadLog]") as "Hlog".
  { destruct Hwf as (?&?&?).
    revert Hlen1 Hlen2; word. }
  iExists q; iFrame.
  iIntros "Hupds".
  rewrite -Hqq'.
  iDestruct (updates_slice_frag_split _ _ (slidingM.numMutable σ) with "Hupds") as "[Hupds2 Hupds1]".
  { revert Hlen1 Hlen2; word. }
  iSplit; auto.
  iApply (fractional.fractional_split_2 with "Hupds2 Hq'").
Qed.

Theorem memLog_sz s σ :
  mutable_log s σ -∗
  ⌜int.nat s.(Slice.sz) = length (slidingM.log σ)⌝.
Proof.
  iIntros "H".
  iNamed "H".
  auto.
Qed.

Theorem wp_sliding__end l σ :
  {{{ is_sliding l σ }}}
    sliding__end #l
  {{{ (endPos:u64), RET #endPos; ⌜int.val endPos = (int.val σ.(slidingM.start) + length σ.(slidingM.log))%Z⌝ ∗
                                 is_sliding l σ }}}.
Proof.
  iIntros (Φ) "Hs HΦ".
  iNamed "Hs"; iNamed "Hinv".
  iDestruct (memLog_sz with "log_mutable") as %Hlog_sz.
  wp_call.
  wp_loadField.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  iApply "HΦ".
  iSplit.
  { iPureIntro.
    word. }
  iSplit; auto.
  iExists _, _; iFrame "# ∗".
Qed.

End goose_lang.
