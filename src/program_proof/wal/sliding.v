From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Export NamedProps List.

From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Export wal.lib.
From Perennial.program_proof Require Import wal.highest.
From Perennial.program_proof Require Import disk_lib.

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
  Definition logIndex (σ:t) (pos: u64) : nat :=
    (int.nat pos - int.nat σ.(start))%nat.

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
                      "Hblocks" ∷ [∗ list] b_upd;upd ∈ bks;log, is_update b_upd 1 upd
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
    iDestruct (big_sepL2_lookup_acc with "Hblocks") as "[[%Huaddr Hb] Hblocks]"; eauto.
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

Hint Unfold slidingM.endPos : word.

Theorem slidingM_endPos_val σ :
  slidingM.wf σ ->
  int.val (slidingM.endPos σ) = int.val σ.(slidingM.start) + length σ.(slidingM.log).
Proof.
  intros.
  word.
Qed.

Theorem wp_sliding__end l σ :
  {{{ is_sliding l σ }}}
    sliding__end #l
  {{{ RET #(slidingM.endPos σ); is_sliding l σ }}}.
Proof.
  iIntros (Φ) "Hsliding HΦ".
  iNamed "Hsliding"; iNamed "Hinv".
  iDestruct (memLog_sz with "log_mutable") as %Hlog_sz.
  wp_call.
  wp_loadField.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  replace (word.add σ.(slidingM.start) logSlice.(Slice.sz)) with (slidingM.endPos σ) by word.
  iApply "HΦ".
  iSplit; auto.
  iExists _, _; iFrame "# ∗".
Qed.

Hint Unfold slidingM.logIndex : word.

Theorem wp_sliding__get l σ (pos: u64) (u: update.t) :
  int.val σ.(slidingM.start) ≤ int.val pos ->
  σ.(slidingM.log) !! (slidingM.logIndex σ pos) = Some u ->
  {{{ is_sliding l σ }}}
    sliding__get #l #pos
  {{{ uv q, RET update_val uv;
      is_update uv q u ∗
        (is_block uv.2 q u.(update.b) -∗ is_sliding l σ)
  }}}.
Proof.
  iIntros (Hbound Hlookup Φ) "Hsliding HΦ".
  iNamed "Hsliding"; iNamed "Hinv".
  wp_call.
  wp_loadField. wp_loadField.
  iMod (memLog_combine with "log_readonly log_mutable") as (q') "[Hlog Hlog_mutable]"; auto.
  wp_apply (wp_SliceGet_updates with "[$Hlog]").
  { iPureIntro.
    lazymatch type of Hlookup with
    | _ !! ?i = _ =>
      lazymatch goal with
      | [ |- _ !! ?i' = _ ] =>
        replace i' with i by word; eassumption
      end
    end.
  }
  iIntros (uv) "(Hu&Hlog)".
  iApply "HΦ".
  iFrame.
  iIntros "Hb"; iSpecialize ("Hlog" with "Hb").
  iSpecialize ("Hlog_mutable" with "Hlog").
  iSplit; auto.
  iExists _, _; iFrame "# ∗".
Qed.

Lemma readonly_log_update_mutable logSlice σ (pos: u64) u :
  slidingM.wf σ ->
  int.val σ.(slidingM.mutable) ≤ int.val pos ->
  readonly_log logSlice σ -∗
  readonly_log logSlice (set slidingM.log
    (λ log : list update.t,
      <[(int.nat pos - int.nat σ.(slidingM.start))%nat:=u]> log) σ).
Proof.
  iIntros (Hwf Hbound) "Hreadonly".
  rewrite /readonly_log.
  iExactEq "Hreadonly".
  rewrite /slidingM.numMutable /=.
  match goal with
  | [ |- readonly (updates_slice_frag _ _ ?us1) =
    readonly (updates_slice_frag _ _ ?us2) ] =>
    replace us1 with us2; auto
  end.
  rewrite take_insert; auto.
  word.
Qed.

Lemma numMutable_set_log f σ :
  slidingM.numMutable (set slidingM.log f σ) =
  slidingM.numMutable σ.
Proof.
  rewrite /slidingM.numMutable //=.
Qed.

Theorem option_fmap_nat_max (m: option nat) :
  Nat.max 0 <$> m = m.
Proof.
  destruct m; auto.
Qed.

Theorem find_highest_index_insert_present `{!EqDecision A} (poss: list A) i pos pos' :
  poss !! i = Some pos ->
  find_highest_index (<[i := pos]> poss) pos' =
  find_highest_index poss pos'.
Proof.
  intros Hlookup.
  generalize dependent i.
  induction poss; simpl; intros; auto.
  destruct (decide (i = 0%nat)); subst.
  - simpl.
    inversion Hlookup; subst; clear Hlookup.
    destruct (decide (pos' = pos')); try congruence.
  - replace i with (S (i - 1)) in * by lia; simpl in *.
    generalize dependent (i - 1)%nat; clear i; intros i Hlookup ?.
    rewrite IHposs; eauto.
Qed.

Lemma addrPosMap_absorb_eq pos u u0 σ :
  σ.(slidingM.log) !! slidingM.logIndex σ pos = Some u0 ->
  u0.(update.addr) = u.(update.addr) ->
  slidingM.addrPosMap
    (set slidingM.log
          (λ log : list update.t,
                  <[(int.nat pos - int.nat σ.(slidingM.start))%nat:=u]> log) σ) =
  slidingM.addrPosMap σ.
Proof.
  intros Hlookup Haddreq.
  rewrite /slidingM.addrPosMap /=.
  rewrite /compute_memLogMap.
  f_equal.
  apply map_eq; intros pos'.
  rewrite !pos_indices_lookup.
  f_equal.
  rewrite list_fmap_insert.
  rewrite find_highest_index_insert_present; auto.
  rewrite list_lookup_fmap.
  rewrite Hlookup /=; congruence.
Qed.

Theorem wp_sliding__update l σ (pos: u64) uv u0 u :
  σ.(slidingM.log) !! (slidingM.logIndex σ pos) = Some u0 ->
  int.val σ.(slidingM.mutable) ≤ int.val pos ->
  (* must be an absorption update, since we don't update addrPos map *)
  u0.(update.addr) = u.(update.addr) ->
  {{{ is_sliding l σ ∗ is_update uv 1 u }}}
    sliding__update #l #pos (update_val uv)
  {{{ RET #();
      is_sliding l (set slidingM.log
                        (λ log, <[ (int.nat pos - int.nat σ.(slidingM.start))%nat := u]> log) σ)
  }}}.
Proof.
  iIntros (Hlookup Hmutable_bound Haddreq Φ) "[Hsliding Hu] HΦ".
  iNamed "Hsliding"; iNamed "Hinv".
  iDestruct (memLog_sz with "log_mutable") as %Hsz.
  wp_call.
  wp_loadField. wp_loadField. wp_loadField. wp_loadField.
  iNamed "log_mutable".
  wp_apply wp_SliceSkip'.
  { iPureIntro.
    revert Hwf; word. }
  fold (slidingM.numMutable σ).
  wp_apply (wp_SliceSet_updates with "[$log_mutable $Hu]").
  { rewrite lookup_drop.
    rewrite <- Hlookup.
    f_equal.
    word. }
  iIntros "log_mutable".
  iApply "HΦ".
  iSplit.
  - iPureIntro.
    rewrite /slidingM.wf /=.
    split_and; try word.
    rewrite !numMutable_set_log.
    revert Hwf; len.
  - iExists _, _; iFrame.
    iSplitL "".
    { iApply (readonly_log_update_mutable with "log_readonly"); auto. }
    iSplitL "log_mutable".
    + iSplit.
      { iPureIntro; simpl; len. }
      rewrite !numMutable_set_log /=.
      rewrite -> drop_insert_le by len.
      iExactEq "log_mutable".
      rewrite /named.
      f_equal.
      f_equal.
      word.
    + iExactEq "is_addrPos".
      rewrite /named.
      f_equal.
      erewrite addrPosMap_absorb_eq; eauto.
Qed.

Theorem wp_sliding_append l σ uv u :
  {{{ is_sliding l σ ∗ is_update uv 1 u }}}
    sliding__append #l (update_val uv)
  {{{ RET #(); is_sliding l (set slidingM.log (λ log, log ++ [u]) σ) }}}.
Proof.
  iIntros (Φ) "[Hsliding Hu] HΦ".
  iNamed "Hsliding"; iNamed "Hinv".
Admitted.

Theorem wp_sliding__takeFrom l σ (start: u64) :
  int.val σ.(slidingM.start) ≤ int.val start ≤ int.val σ.(slidingM.mutable) ->
  {{{ is_sliding l σ }}}
    sliding__takeFrom #l #start
  {{{ q s, RET (slice_val s); is_sliding l σ ∗
           let from := slidingM.logIndex σ start in
           let to := slidingM.logIndex σ σ.(slidingM.mutable) in
           updates_slice_frag s q (subslice from to σ.(slidingM.log)) }}}.
Proof.
Admitted.

Theorem wp_sliding__takeTill l σ (endPos: u64) :
  int.val σ.(slidingM.start) ≤ int.val endPos ≤ int.val σ.(slidingM.mutable) ->
  {{{ is_sliding l σ }}}
    sliding__takeTill #l #endPos
  {{{ q s, RET (slice_val s); is_sliding l σ ∗
           let to := slidingM.logIndex σ endPos in
           updates_slice_frag s q (take to σ.(slidingM.log)) }}}.
Proof.
Admitted.

Theorem wp_sliding__deleteFrom l σ (newStart: u64) :
  int.val σ.(slidingM.start) ≤ int.val newStart ≤ int.val σ.(slidingM.mutable) ->
  {{{ is_sliding l σ }}}
    sliding__deleteFrom #l #newStart
  {{{ RET #(); is_sliding l
        (set slidingM.log (drop (slidingM.logIndex σ newStart)) σ) }}}.
Proof.
Admitted.

Lemma numMutable_after_clear σ :
  slidingM.wf σ ->
  slidingM.numMutable (set slidingM.mutable (λ _ : u64, slidingM.endPos σ) σ) =
  U64 (length σ.(slidingM.log)).
Proof.
  intros Hwf.
  rewrite /slidingM.numMutable /slidingM.endPos /=.
  word_cleanup.
  word.
Qed.

Theorem wp_sliding__clearMutable l σ :
  {{{ is_sliding l σ }}}
    sliding__clearMutable #l
  {{{ RET #(); is_sliding l (set slidingM.mutable (λ _, slidingM.endPos σ) σ) }}}.
Proof.
  iIntros (Φ) "Hsliding HΦ".
  wp_call.
  wp_apply (wp_sliding__end with "Hsliding"); iIntros "Hsliding".
  iNamed "Hsliding"; iNamed "Hinv".
  rewrite -wp_fupd.
  wp_storeField.
  iNamed "log_mutable".
  unshelve iMod (readonly_alloc_1 with "log_mutable") as "readonly_new".
  2: apply _.
  rewrite /readonly_log.
  iDestruct (readonly_extend with "log_readonly readonly_new") as "log_readonly'".
  iClear "log_readonly".
  iModIntro.
  iApply "HΦ".
  iSplit.
  - iPureIntro.
    split_and!; simpl; try word.
    rewrite numMutable_after_clear; auto.
    word.
  - simpl.
    iExists _, _; iFrame.
    iSplitL.
    + rewrite /readonly_log.
      simpl.
      iApply (readonly_iff with "log_readonly'").
      intros q; simpl.
      rewrite numMutable_after_clear; auto.
      iSplit.
      { iIntros "[Hupds1 Hupds2]".
        iDestruct (updates_slice_frag_combine with "[$Hupds1 $Hupds2]") as "Hupds".
        { revert Hwf; word. }
        rewrite take_ge; len.
        iDestruct "Hupds" as (bks) "[Hs Hbks]".
        iExists _; iFrame.
        admit. (* taking all of a slice preserves is_slice_small (removes capacity) *)
      }
      iIntros "Hupds".
      rewrite {1}take_ge; len.
      iDestruct (updates_slice_frag_split _ _ (slidingM.numMutable σ) with "Hupds") as "[Hupds1 Hupds2]".
      { simpl; revert Hwf; word. }
      iFrame.
      iDestruct "Hupds1" as (bks) "[Hs Hbks]".
      iExists _; iFrame.
      admit. (* similar, took whole slice before skipping *)
    + rewrite /mutable_log /=.
      iSplit.
      { iPureIntro; word. }
      rewrite numMutable_after_clear; auto.
      rewrite drop_ge; len.
      iExists nil; simpl.
      admit. (* is_slice_small nil *)
Admitted.

Theorem wp_sliding__posForAddr l σ (a: u64) :
  {{{ is_sliding l σ }}}
    sliding__posForAddr #l #a
  {{{ (pos: u64) (ok: bool), RET (#pos, #ok);
      is_sliding l σ ∗
      ⌜if ok then int.val σ.(slidingM.start) ≤ int.val pos ≤ int.val (slidingM.endPos σ) ∧
                  find_highest_index (update.addr <$> σ.(slidingM.log)) a = Some (slidingM.logIndex σ pos)
      else find_highest_index (update.addr <$> σ.(slidingM.log)) a = None⌝
  }}}.
Proof.
Admitted.

End goose_lang.
