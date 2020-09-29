From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Export NamedProps.

From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Export wal.sliding.
From Perennial.program_proof Require Import disk_lib.

Section goose_lang.
Context `{!heapG Σ}.

Implicit Types (l: loc) (σ: slidingM.t).

Definition readonly_log logSlice σ : iProp Σ :=
      readonly (updates_slice_frag
                  (slice_take logSlice (struct.t Update.S) (slidingM.numMutable σ)) 1
                  (take (int.nat (slidingM.numMutable σ)) σ.(slidingM.log))).

Definition mutable_log logSlice σ : iProp Σ :=
  "%logSlice_wf" ∷ ⌜int.nat logSlice.(Slice.sz) = length σ.(slidingM.log) ∧ int.val logSlice.(Slice.sz) ≤ int.val logSlice.(Slice.cap)⌝ ∗
  "log_mutable" ∷ updates_slice
        (slice_skip logSlice (struct.t Update.S) (slidingM.numMutable σ))
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
  iNamed 1; auto.
Qed.

Theorem memLog_sz s σ :
  mutable_log s σ -∗
  ⌜int.nat s.(Slice.sz) = length (slidingM.log σ)⌝.
Proof.
  iNamed 1.
  iPureIntro; word.
Qed.

Theorem wp_log_len l σ :
  {{{ is_sliding l σ }}}
    slice.len (struct.loadF sliding.S "log" #l)
  {{{ RET #(U64 $ length σ.(slidingM.log)); is_sliding l σ }}}.
Proof.
  iIntros (Φ) "Hsliding HΦ".
  iNamed "Hsliding"; iNamed "Hinv".
  iDestruct (memLog_sz with "log_mutable") as %Hsz.
  wp_loadField.
  rewrite /slice.len; wp_pures. (* XXX: wp_apply wp_slice_len doesn't work for some reason *)
  replace logSlice.(Slice.sz) with (U64 $ length σ.(slidingM.log)) by word.
  iApply "HΦ".
  iSplit; auto.
  iExists _, _; iFrame "# ∗".
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

Theorem wp_mkSliding s log (start: u64) :
  int.val start + length log < 2^64 ->
  {{{ updates_slice_frag s 1 log ∗ is_slice_cap s (struct.t Update.S) }}}
    mkSliding (slice_val s) #start
  {{{ (l: loc), RET #l; is_sliding l (slidingM.mk log start (int.val start + length log)) }}}.
Proof.
  iIntros (Hbound Φ) "[Hs Hcap] HΦ".
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
  rewrite -wp_fupd.
  wp_apply wp_allocStruct; auto.
  iIntros (l) "Hl".
  iDestruct (struct_fields_split with "Hl") as "(Hf1&Hf2&Hf3&Hf4&%)".
  iAssert (updates_slice_frag s 1 log) with "[Hs Hblocks]" as "Hlog".
  { iExists _; iFrame. }
  iDestruct (updates_slice_frag_split _ _ (U64 $ length log) with "Hlog") as "[Hmut Hreadonly]".
  { word. }
  rewrite -> drop_ge by word.
  rewrite -> take_ge by word.
  iMod (readonly_alloc_1 with "Hreadonly") as "#Hreadonly".
  iModIntro.
  iApply "HΦ".
  iSplitL "".
  { iPureIntro. rewrite /slidingM.wf//=; split; word. }
  iExists _, _. iFrame; simpl.
  iSplitL "Hf3".
  { rewrite /named. iExactEq "Hf3". do 3 f_equal.
    word. }
  iDestruct (is_slice_cap_wf with "Hcap") as %Hcap.
  iSplitR.
  - rewrite /readonly_log /slidingM.numMutable /=.
    rewrite -> take_ge by word.
    replace (word.sub (int.val start + length log) start)
            with (U64 (length log)) by word.
    iFrame "Hreadonly".
  - rewrite /mutable_log /slidingM.numMutable /=.
    iSplit.
    + iPureIntro.
      word.
    + rewrite -> drop_ge by word.
      replace (word.sub (int.val start + length log) start)
              with (U64 (length log)) by word.
      rewrite updates_slice_cap_acc.
      iFrame.
      iApply (is_slice_cap_skip with "Hcap"); first by word.
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
  iMod (readonly_load_lt with "Hread") as (q) "[%Hqlt HreadLog]".
  iModIntro.
  destruct (Qextra.Qp_split_1 _ Hqlt) as [q' Hqq'].
  iDestruct (updates_slice_frag_acc with "Hmut") as "[Hmut Hmut_full]".
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
  iCombine "Hupds2 Hq'" as "Hmut".
  iSpecialize ("Hmut_full" with "Hmut").
  iFrame.
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

Theorem addrPosMap_lookup_inv σ pos :
  slidingM.addrPosMap σ !! pos = (λ (n:nat), U64 (Z.of_nat (int.nat σ.(slidingM.start) + n)%nat)) <$> (find_highest_index (update.addr <$> σ.(slidingM.log)) pos).
Proof.
  rewrite /slidingM.addrPosMap /compute_memLogMap.
  rewrite lookup_fmap.
  rewrite pos_indices_lookup.
  rewrite -option_fmap_compose.
  auto.
Qed.

Theorem wp_sliding__posForAddr l σ (a: u64) :
  {{{ is_sliding l σ }}}
    sliding__posForAddr #l #a
  {{{ (pos: u64) (ok: bool), RET (#pos, #ok);
      is_sliding l σ ∗
      ⌜if ok then int.val σ.(slidingM.start) ≤ int.val pos < slidingM.memEnd σ ∧
                  find_highest_index (update.addr <$> σ.(slidingM.log)) a = Some (slidingM.logIndex σ pos)
      else find_highest_index (update.addr <$> σ.(slidingM.log)) a = None⌝
  }}}.
Proof.
  iIntros (Φ) "Hs HΦ".
  iNamed "Hs".
  iNamed "Hinv".
  wp_call.
  wp_loadField.
  wp_apply (wp_MapGet with "is_addrPos").
  iIntros (pos ok) "(%Hmapget&is_addrPos)".
  wp_pures.
  iApply "HΦ".
  iSplitL.
  { iFrame "% ∗".
    iExists _, _; iFrame "# ∗". }
  iPureIntro.
  destruct ok.
  - apply map_get_true in Hmapget.
    rewrite addrPosMap_lookup_inv in Hmapget.
    apply fmap_Some_1 in Hmapget as [i [Hindex ->]]; simpl.
    pose proof (find_highest_index_ok' _ _ _ Hindex) as [Hlookup _].
    apply lookup_lt_Some in Hlookup.
    rewrite /slidingM.memEnd.
    autorewrite with len in Hlookup.
    split.
    + word.
    + rewrite Hindex.
      f_equal.
      word.
  - apply map_get_false in Hmapget as [Hmapget ->].
    rewrite addrPosMap_lookup_inv in Hmapget.
    apply fmap_None in Hmapget.
    auto.
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

Theorem wp_sliding__update l σ (pos: u64) uv u :
  (* must be an absorption update, since we don't update addrPos map *)
  update.addr <$> σ.(slidingM.log) !! (slidingM.logIndex σ pos) = Some u.(update.addr) ->
  int.val σ.(slidingM.mutable) ≤ int.val pos ->
  {{{ is_sliding l σ ∗ is_update uv 1 u }}}
    sliding__update #l #pos (update_val uv)
  {{{ RET #();
      is_sliding l (set slidingM.log
                        (λ log, <[ (int.nat pos - int.nat σ.(slidingM.start))%nat := u]> log) σ)
  }}}.
Proof.
  iIntros (Hlookup Hmutable_bound Φ) "[Hsliding Hu] HΦ".
  apply fmap_Some_1 in Hlookup as [u0 [Hlookup Haddreq]].
  iNamed "Hsliding"; iNamed "Hinv".
  iDestruct (memLog_sz with "log_mutable") as %Hsz.
  wp_call.
  wp_loadField. wp_loadField. wp_loadField. wp_loadField.
  iNamed "log_mutable".
  wp_apply wp_SliceSkip'.
  { iPureIntro.
    word. }
  fold (slidingM.numMutable σ).
  iDestruct (updates_slice_frag_acc with "log_mutable") as "[log_mutable log_mutable_full]".
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
    revert Hwf; len.
  - iExists _, _; iFrame.
    iSplitL "".
    { iApply (readonly_log_update_mutable with "log_readonly"); auto. }
    iDestruct ("log_mutable_full" with "log_mutable") as "log_mutable".
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

Lemma wp_SliceAppend_log s σ uv u :
  {{{ readonly_log s σ ∗ mutable_log s σ ∗ is_update uv 1 u }}}
    SliceAppend (struct.t Update.S) (slice_val s) (update_val uv)
  {{{ s', RET slice_val s';
      let σ' := set slidingM.log (λ log, log ++ [u]) σ in
      readonly_log s' σ' ∗ mutable_log s' σ' ∗
      (* non-overflow comes from doing a slice append *)
      ⌜slidingM.wf σ'⌝ }}}.
Proof.
  iIntros (Φ) "(#Hrolog & Hmutlog & Hupdate) HΦ".
  iMod (readonly_load with "Hrolog") as (q) "Hrolog'".
  iNamed "Hmutlog".
  iDestruct "Hupdate" as "[% Hupdate]".
  wp_apply (wp_SliceAppend_updates with "[Hrolog' log_mutable $Hupdate]").
  { rewrite /updates_slice /updates_slice_frag.
    iDestruct "Hrolog'" as (bks0) "[Hrolog' Hbks0]".
    iDestruct "log_mutable" as (bks1) "[Hmutable Hbks1]".
    iExists (bks0 ++ bks1).
    iSplitL "Hrolog' Hmutable".
    { iDestruct "Hmutable" as "[Hmutable_sm Hcap]".
      iDestruct (is_slice_combine with "Hrolog' [Hmutable_sm]") as "Hsm".
      {
        (* XXX need sliding.wf somewhere? *)
        admit.
      }

      {
        (* XXX need to reduce 1%Qp to q *)
        admit.
      }

      iSplitR "Hcap".
      {
        (* XXX SliceAppend is too strong: it requires 1%Qp ownership of is_slice_small.. *)
        admit.
      }

      (* XXX need the opposite of is_slice_cap_skip *)
      admit.
    }

    iApply (big_sepL2_app with "[Hbks0] [Hbks1]").
    { iApply (big_sepL2_mono with "Hbks0"). iIntros (k y1 y2 Hy1 Hy2).
      iIntros "H". iDestruct "H" as "[% H]".
      destruct y2; simpl in *.
      (* XXX this wants 1%Qp ownership but we only have q *)
      admit.
    }

    { iFrame. }
  }

  iIntros (s') "Hlog".
  iApply "HΦ".
  admit.
Admitted.

Lemma addrPosMap_insert_fresh:
  ∀ σ (uv : u64 * Slice.t) (u : update.t) (logSlice : Slice.t),
    uv.1 = update.addr u
    → int.nat logSlice.(Slice.sz) = length σ.(slidingM.log)
    → slidingM.wf (set slidingM.log (λ log : list update.t, log ++ [u]) σ)
    → slidingM.addrPosMap
          (set slidingM.log (λ log : list update.t, log ++ [u]) σ) =
        map_insert (slidingM.addrPosMap σ) uv.1
                    (word.add σ.(slidingM.start) logSlice.(Slice.sz)).
Proof.
  intros σ uv u logSlice Haddr HlogLen Hwf'.
  rewrite -> Haddr in *.
  destruct Hwf' as (?&?&?); simpl in *.
  autorewrite with len in H0, H1.
  rewrite /slidingM.addrPosMap /=.
  rewrite (memLogMap_append _ _ _ logSlice.(Slice.sz)) //; word.
Qed.

Theorem wp_sliding_append l σ uv u :
  {{{ is_sliding l σ ∗ is_update uv 1 u }}}
    sliding__append #l (update_val uv)
  {{{ RET #(); is_sliding l (set slidingM.log (λ log, log ++ [u]) σ) }}}.
Proof.
  iIntros (Φ) "[Hsliding Hu] HΦ".
  iDestruct (is_update_addr with "Hu") as %Haddr.
  iNamed "Hsliding"; iNamed "Hinv".
  wp_call.
  wp_loadField.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  wp_loadField.
  iDestruct (memLog_sz with "log_mutable") as %Hlogsize.
  wp_apply (wp_SliceAppend_log with "[$log_readonly $log_mutable $Hu]").
  iIntros (logSlice') "(#log_readonly'&log_mutable&%Hwf')".
  wp_apply (wp_storeField with "log").
  { rewrite /field_ty //=.
    val_ty. }
  iIntros "log".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapInsert_to_val with "is_addrPos").
  iIntros "is_addrPos".
  iApply "HΦ".
  iSplitR.
  { eauto. }
  iExists _, _; iFrame "# ∗".
  iExactEq "is_addrPos".
  rewrite /named.
  f_equal.
  erewrite addrPosMap_insert_fresh; eauto.
Qed.

Theorem wp_if_mutable l memLog (ok: bool) (pos: u64) :
  {{{ is_sliding l memLog }}}
    if: #ok then #pos ≥ struct.loadF sliding.S "mutable" #l else #false
  {{{ RET #(bool_decide (ok = true ∧ int.val memLog.(slidingM.mutable) ≤ int.val pos));
      is_sliding l memLog }}}.
Proof.
  iIntros (Φ) "Hs HΦ".
  wp_if_destruct.
  - iNamed "Hs".
    iNamed "Hinv".
    wp_loadField.
    wp_pures.
    iSpecialize ("HΦ" with "[-]").
    { iFrame "% ∗".
      iExists _, _; iFrame "# ∗". }
    iExactEq "HΦ".
    erewrite bool_decide_iff; eauto.
    intuition auto.
  - simpl.
    iApply ("HΦ" with "[$]").
Qed.

Theorem wp_sliding__memWrite l memLog bufs upds :
  {{{ is_sliding l memLog ∗ updates_slice_frag bufs 1 upds }}}
    sliding__memWrite #l (slice_val bufs)
  {{{ RET #(); is_sliding l (memWrite memLog upds) }}}.
Proof.
  iIntros (Φ) "(Hs&Hupds) HΦ".
  wp_call.
  wp_apply (wp_sliding__end with "Hs"); iIntros "Hs".
  wp_apply wp_ref_to; [ val_ty | iIntros (pos_l) "pos" ].
  rewrite /LogPosition.
  wp_apply (wp_forSlicePrefix_updates_consume
              (λ done todo,
               "*" ∷ (∃ (pos_val: u64), "pos" ∷ pos_l ↦[uint64T] #pos_val) ∗
               "Hs" ∷ is_sliding l (memWrite memLog done))%I
           with "[] [$Hupds pos Hs]").
  2: {
    simpl; iFrame.
    iExists _; iFrame.
  }
  { clear Φ.
    iIntros (i uv u done todo).
    iIntros "!>" (Φ) "(Hpre&Hupd&%Hiteration) HΦ". iNamed "Hpre".
    wp_pures.
    iDestruct (is_update_addr with "Hupd") as %Haddr_eq.
    wp_apply (wp_sliding__posForAddr with "[$]").
    iIntros (pos ok) "(Hs&%Hlookup)".
    iDestruct (is_sliding_wf with "Hs") as %Hwf.
    wp_pures.
    wp_apply (wp_if_mutable with "Hs"); iIntros "Hs".
    wp_if_destruct.

    (* absorption *)
    - destruct Heqb as [-> Hpos_large].
      destruct Hlookup as (HposBound&Hlookup).
      wp_apply util_proof.wp_DPrintf.
      wp_apply (wp_sliding__update with "[$Hs $Hupd]"); auto.
      { destruct_and? Hlookup.
        apply find_highest_index_ok' in Hlookup as [Hlookup Hhighest].
        rewrite list_lookup_fmap in Hlookup.
        congruence. }
      iIntros "Hs".
      iApply "HΦ".
      iSplitL "pos".
      { iExists _; iFrame. }
      rewrite memWrite_app1.
      set (memLog':=memWrite memLog done) in *.
      iExactEq "Hs".
      rewrite /named.
      f_equal.
      rewrite /memWrite_one.
      replace u.(update.addr).
      rewrite Hlookup.
      destruct (decide
      (int.val memLog'.(slidingM.mutable) - int.val memLog'.(slidingM.start)
       ≤ slidingM.logIndex memLog' pos)); [ auto | word ].

    (* append *)
    - wp_bind (If _ _ _).
      wp_apply (wp_If_join emp).
      { iSplit.
        - iIntros "[-> Hwp]".
          wp_apply util_proof.wp_DPrintf.
          iApply "Hwp"; auto.
        - iIntros "[-> Hwp]".
          wp_apply util_proof.wp_DPrintf.
          iApply "Hwp"; auto.
      }
      iIntros "_"; wp_pures.
      wp_apply (wp_sliding_append with "[$Hs $Hupd]"); iIntros "Hs".
      wp_pures.
      wp_load.
      wp_store.
      iApply "HΦ".
      iFrame.
      iSplitL "pos".
      { iExists _; iFrame. }
      iExactEq "Hs".
      rewrite /named.
      f_equal.
      rewrite memWrite_app1.
      rewrite /memWrite_one.
      replace (u.(update.addr)).
      destruct_with_eqn (find_highest_index (update.addr <$> (memWrite memLog done).(slidingM.log)) uv.1); auto.
      destruct (decide
                  (int.val (memWrite memLog done).(slidingM.mutable) -
                  int.val (memWrite memLog done).(slidingM.start) ≤ n)); auto.
      exfalso.
      destruct ok; try congruence.
      destruct Hlookup as [? Heq]; inversion Heq; subst.
      contradiction Heqb.
      split; auto.
      word.
  }
  iNamed 1.
  iApply "HΦ"; iFrame.
Qed.

Hint Unfold slidingM.numMutable : word.

Theorem wp_sliding__takeFrom l σ (start: u64) :
  int.val σ.(slidingM.start) ≤ int.val start ≤ int.val σ.(slidingM.mutable) ->
  {{{ is_sliding l σ }}}
    sliding__takeFrom #l #start
  {{{ q s, RET (slice_val s); is_sliding l σ ∗
           let from := slidingM.logIndex σ start in
           let to := slidingM.logIndex σ σ.(slidingM.mutable) in
           updates_slice_frag s q (subslice from to σ.(slidingM.log)) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iNamed "Hs"; iNamed "Hinv".
  wp_call.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  iDestruct (memLog_sz with "log_mutable") as %Hs.
  iMod (readonly_load with "log_readonly") as (q) "Hlog".
  iDestruct "Hlog" as (bks) "[Hs Hblocks]".
  wp_apply (wp_SliceTake (uint64T * (blockT * unitT))%ht); first by word.
  wp_apply wp_SliceSkip'.
  { iPureIntro.
    simpl; word. }
  iDestruct (big_sepL2_length with "Hblocks") as %Hbks_len.
  autorewrite with len in Hbks_len.
  fold (slidingM.numMutable σ).
  change (uint64T * (blockT * unitT))%ht with (struct.t Update.S).
  set (s':=slice_take logSlice (struct.t Update.S) (slidingM.numMutable σ)).
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  autorewrite with len in Hsz.
  iDestruct (is_slice_small_take_drop _ _ _ (word.sub start σ.(slidingM.start)) with "Hs") as "[Hs2 Hs1]".
  { revert Hbks_len; word. }
  iApply "HΦ".
  iSplitR "Hs2 Hblocks".
  { iFrame "% ∗".
    iExists _, _; iFrame "# ∗". }
  iExists _.
  rewrite -fmap_drop.
  iFrame "Hs2".
  set (numMutable := int.nat (slidingM.numMutable σ)) in *.
  assert (numMutable ≤ length σ.(slidingM.log))%nat by (rewrite /numMutable; word).
  replace (numMutable `min` length σ.(slidingM.log))%nat with numMutable in * by word.
  assert (int.nat (word.sub start σ.(slidingM.start)) = int.nat start - int.nat σ.(slidingM.start))%nat
    as Hstart_off by word.
  rewrite Hstart_off.
  rewrite -{1}(take_drop (int.nat start - int.nat σ.(slidingM.start)) bks).
  iDestruct (big_sepL2_app_inv_l with "Hblocks") as (bks1 bks2 Hbks12) "[Hblocks1 Hblocks2]".
  iDestruct (big_sepL2_length with "Hblocks1") as %Hlen1.
  iDestruct (big_sepL2_length with "Hblocks2") as %Hlen2.
  autorewrite with len in Hlen1, Hlen2.
  iExactEq "Hblocks2".
  f_equal.
  rewrite subslice_take_drop.
  replace (slidingM.logIndex σ σ.(slidingM.mutable)) with
      (int.nat (slidingM.numMutable σ)) by word.
  rewrite -/numMutable.
  rewrite Hbks12.
  assert (length bks1 = slidingM.logIndex σ start).
  { rewrite -Hlen1.
    rewrite Hbks_len /numMutable.
    word. }
  rewrite -> drop_app_ge by lia.
  replace (slidingM.logIndex σ start - length bks1)%nat with 0%nat by lia; auto.
Qed.

Theorem wp_SliceTake_updates s (n: u64) q (upds: list update.t) :
  int.val n ≤ length upds →
  {{{ updates_slice_frag s q upds }}}
    SliceTake (slice_val s) #n
  {{{ RET (slice_val (slice_take s (struct.t Update.S) n));
      updates_slice_frag (slice_take s (struct.t Update.S) n) q (take (int.nat n) upds) }}}.
Proof.
  iIntros (Hbound Φ) "Hupds HΦ".
  iDestruct (updates_slice_frag_len with "Hupds") as %Hlen.
  wp_apply wp_SliceTake; first by word.
  iApply "HΦ".
  iDestruct (updates_slice_frag_split with "Hupds") as "[_ $]".
  word.
Qed.

Theorem wp_sliding__takeTill l σ (endPos: u64) :
  int.val σ.(slidingM.start) ≤ int.val endPos ≤ int.val σ.(slidingM.mutable) ->
  {{{ is_sliding l σ }}}
    sliding__takeTill #l #endPos
  {{{ q s, RET (slice_val s); is_sliding l σ ∗
           let to := slidingM.logIndex σ endPos in
           updates_slice_frag s q (take to σ.(slidingM.log)) }}}.
Proof.
  iIntros (Hbound Φ) "Hs HΦ".
  iNamed "Hs"; iNamed "Hinv".
  wp_call.
  repeat wp_loadField.
  iDestruct (memLog_sz with "log_mutable") as %Hsz.
  iMod (readonly_load with "log_readonly") as (q) "Hlog".
  wp_apply wp_SliceTake.
  { word. }
  wp_apply (wp_SliceTake_updates with "Hlog"); first by len.
  iIntros "Hupds".
  iApply "HΦ".
  iSplitR "Hupds".
  { iSplit; auto.
    iExists _, _; iFrame "# ∗". }
  rewrite take_take.
  iExactEq "Hupds".
  repeat (f_equal; try word).
Qed.

Theorem memLogMap_drop1_not_highest (σ: slidingM.t) (upd: update.t) i :
  slidingM.wf σ
  → σ.(slidingM.log) !! O = Some upd
  → find_highest_index (update.addr <$> σ.(slidingM.log)) upd.(update.addr) = Some i
  → (i > 0)%nat
  → slidingM.addrPosMap
      (set slidingM.start (word.add 1)
        (set slidingM.log (drop 1) σ)) =
    slidingM.addrPosMap σ.
Proof.
  intros (_ & Hbounds & _) Hlookup Hhighest Hgt.
  rewrite /slidingM.addrPosMap /compute_memLogMap.
  rewrite /set /=.
  rewrite fmap_drop.
  remember (update.addr <$> σ.(slidingM.log)) as addrs.
  assert (addrs !! O = Some upd.(update.addr))
    by rewrite Heqaddrs list_lookup_fmap Hlookup //=.
  remember upd.(update.addr) as addr.
  remember σ.(slidingM.start) as start.
  replace (length σ.(slidingM.log)) with (length addrs) in Hbounds
    by rewrite Heqaddrs map_length //.
  clear Heqaddr Heqaddrs upd Hlookup Heqstart σ.

  f_equal.
  apply map_eq.
  intros oaddr.
  rewrite pos_indices_lookup pos_indices_lookup.
  destruct addrs; first by eauto.
  rewrite /= drop_0.
  rewrite /= in H.
  inversion H. clear H.
  rewrite /= in Hbounds.
  rewrite /= decide_True in Hhighest. 2: eauto.
  destruct (find_highest_index addrs addr) eqn:Hn; inversion Hhighest.
  2: lia.
  subst.
  clear Hhighest Hgt.
  destruct (decide (oaddr = addr)).
  {
    subst.
    rewrite Hn /=.
    f_equal.
    word.
  }
  destruct (find_highest_index addrs oaddr).
  2: eauto.
  simpl.
  f_equal.
  word.
Qed.

Theorem memLogMap_drop1_highest (σ: slidingM.t) (upd: update.t) :
  slidingM.wf σ
  → σ.(slidingM.log) !! O = Some upd
  → find_highest_index (update.addr <$> σ.(slidingM.log)) upd.(update.addr) = Some O
  → slidingM.addrPosMap
      (set slidingM.start (word.add 1)
        (set slidingM.log (drop 1) σ)) =
    map_del (slidingM.addrPosMap σ) upd.(update.addr).
Proof.
  intros (_ & Hbounds & _) Hlookup Hhighest.
  rewrite /slidingM.addrPosMap /compute_memLogMap.
  rewrite /set /=.
  rewrite fmap_drop.
  remember (update.addr <$> σ.(slidingM.log)) as addrs.
  assert (addrs !! O = Some upd.(update.addr))
    by rewrite Heqaddrs list_lookup_fmap Hlookup //=.
  remember upd.(update.addr) as addr.
  remember σ.(slidingM.start) as start.
  replace (length σ.(slidingM.log)) with (length addrs) in Hbounds
    by rewrite Heqaddrs map_length //.
  clear Heqaddr Heqaddrs upd Hlookup Heqstart σ.

  rewrite /map_del -fmap_delete.
  f_equal.
  apply map_eq.
  intros oaddr.
  rewrite pos_indices_lookup.
  destruct addrs; first by eauto.
  rewrite /= drop_0.
  rewrite /= in H.
  inversion H. clear H. subst.
  rewrite /= in Hbounds.
  rewrite /= decide_True in Hhighest. 2: eauto.
  destruct (find_highest_index addrs addr) eqn:Hn; first by inversion Hhighest.
  destruct (decide (oaddr = addr)).
  1: subst; rewrite lookup_delete Hn /= //.
  rewrite lookup_delete_ne. 2: eauto.
  rewrite lookup_partial_alter_ne. 2: eauto.
  rewrite pos_indices_lookup.
  repeat f_equal.
  word.
Qed.

Theorem wp_sliding__deleteFrom l σ (newStart: u64) :
  int.val σ.(slidingM.start) ≤ int.val newStart ≤ int.val σ.(slidingM.mutable) ->
  {{{ is_sliding l σ }}}
    sliding__deleteFrom #l #newStart
  {{{ RET #(); is_sliding l
        (set slidingM.start (λ _, newStart)
          (set slidingM.log (drop (slidingM.logIndex σ newStart)) σ)
        ) }}}.
Proof.
  iIntros (HnewStart Hmutable) "Hsliding HΦ".
  iNamed "Hsliding".
  iNamed "Hinv".
  iNamed "log_mutable".
  wp_call.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_loadField.
  iMod (readonly_load with "log_readonly") as (q) "Hlog".
  wp_apply (wp_SliceTake (uint64T * (blockT * unitT)%ht)); first by word.
  wp_apply (wp_SliceTake_updates with "Hlog"); first by len.
  iIntros "Hupds".
  iDestruct "Hupds" as (bks) "[HlogSlice Hbks] /=".
  rewrite take_take min_l. 2: word.
  wp_apply (wp_forSlice (fun i =>
    "start" ∷ l ↦[sliding.S :: "start"] #σ.(slidingM.start) ∗
    "addrPos" ∷ l ↦[sliding.S :: "addrPos"] #addrPosPtr ∗
    "HaddrPos" ∷ is_map addrPosPtr (slidingM.addrPosMap
      (set slidingM.start (word.add i)
        (set slidingM.log (drop (int.nat i)) σ)
      )
    ) ∗
    "Hbks" ∷ [∗ list] uv;upd ∈ bks; take (int.nat (word.sub newStart σ.(slidingM.start))) σ.(slidingM.log),
      is_update uv q upd
  )%I with "[] [$HlogSlice $start $addrPos is_addrPos $Hbks]").
  2: {
    rewrite /set drop_0 /=.
    replace (word.add 0 σ.(slidingM.start)) with σ.(slidingM.start) by word.
    iFrame.
  }
  {
    iIntros (i u).
    iIntros "!>" (Φ) "(HI & %Hlt & %Hlookup) HΦ".
    iNamed "HI".
    rewrite /slice_take /= in Hlt.
    replace (int.val (word.sub newStart σ.(slidingM.start))) with ((int.val newStart) - (int.val σ.(slidingM.start))) in Hlt by word.
    rewrite list_lookup_fmap in Hlookup.
    apply fmap_Some_1 in Hlookup as [uv [Hlookup ->]].
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapGet with "HaddrPos").
    iIntros (pos ok) "[%Hmapget HaddrPos]".
    wp_pures.

    assert ((int.nat i) <
      length (take (int.nat (word.sub newStart σ.(slidingM.start))) σ.(slidingM.log))
    )%nat as Hlt' by (rewrite take_length; word).
    destruct (list_lookup_lt _ _ _ Hlt') as (upd & Hupd).
    clear Hlt'.
    iDestruct (big_sepL2_lookup_acc with "Hbks") as "[[%Huaddr Hb] Hbks]"; eauto.
    iAssert (is_update uv q upd) with "[Hb]" as "Hbk"; first by (iFrame; eauto).
    iPoseProof ("Hbks" with "Hbk") as "Hbks".
    rewrite lookup_take in Hupd. 2: word.

    destruct ok; wp_pures.
    2: {
      (* contradiction: blkno must exist in s.addrPos *)
      apply map_get_false in Hmapget.
      destruct Hmapget as [Hmapget _].
      rewrite addrPosMap_lookup_inv /= in Hmapget.
      apply fmap_None in Hmapget.
      apply find_highest_index_none with (txn_id := O) in Hmapget.
      rewrite Huaddr list_lookup_fmap lookup_drop Nat.add_0_r in Hmapget.
      replace (slidingM.logIndex σ (word.add σ.(slidingM.start) i)) with (int.nat i) in Hmapget by word.
      rewrite Hupd //= in Hmapget.
    }
    apply map_get_true in Hmapget.
    rewrite addrPosMap_lookup_inv /= in Hmapget.
    apply fmap_Some_1 in Hmapget as [oldPos [Hindex ->]]; simpl.
    rewrite Huaddr in Hindex.
    pose proof (find_highest_index_ok' _ _ _ Hindex) as [Hlookup_oldPos _].
    apply lookup_lt_Some in Hlookup_oldPos.
    rewrite fmap_length drop_length in Hlookup_oldPos.

    remember (set slidingM.start (word.add i)
      (set slidingM.log (drop (int.nat i)) σ))
      as σtrunc.
    replace (set slidingM.start (word.add (word.add i 1))
      (set slidingM.log (drop (int.nat (word.add i 1))) σ))
      with (set slidingM.start (word.add 1)
      (set slidingM.log (drop 1) σtrunc)).
    2: {
      subst.
      destruct σ.
      rewrite /set /=.
      f_equal.
      - rewrite drop_drop.
        f_equal.
        word.
      - word_cleanup.
        rewrite /word.wrap Zplus_mod_idemp_r.
        f_equal.
        lia.
    }

    replace (int.nat (word.add i σ.(slidingM.start))) with (int.nat i + int.nat σ.(slidingM.start))%nat by word.
    replace (int.val (word.add σ.(slidingM.start) i)) with (int.val (int.nat i + int.nat σ.(slidingM.start))%nat) by word.
    replace (int.val (int.nat i + int.nat σ.(slidingM.start) + oldPos)%nat) with (int.val i + int.val σ.(slidingM.start) + oldPos) by word.
    replace (int.val (int.nat i + int.nat σ.(slidingM.start))%nat) with (int.val i + int.val σ.(slidingM.start)) by word.

    wp_if_destruct.
    2: {
      iApply "HΦ".
      iFrame.
      erewrite memLogMap_drop1_not_highest.
      - iFrame.
      - rewrite Heqσtrunc /slidingM.wf drop_length /=.
        word.
      - rewrite Heqσtrunc /set /= lookup_drop Nat.add_0_r Hupd //.
      - rewrite Heqσtrunc /set /= Hindex //.
      - word.
    }

    wp_pures.
    wp_apply util_proof.wp_DPrintf.
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapDelete with "HaddrPos").
    iIntros "HaddrPos".
    rewrite Huaddr.
    iApply "HΦ".
    iFrame.
    assert (oldPos = O) by lia.
    subst oldPos.
    erewrite memLogMap_drop1_highest.
    - iFrame.
    - rewrite Heqσtrunc /slidingM.wf drop_length /=.
      word.
    - rewrite Heqσtrunc /set /= lookup_drop Nat.add_0_r Hupd //.
    - rewrite Heqσtrunc /set /= Hindex //.
  }
  iIntros "[HI HlogSlice]".
  iNamed "HI".
  wp_pures.
  wp_loadField.
  wp_apply wp_SliceSkip'; first by (simpl; iPureIntro; word).
  wp_bind (struct.storeF _ _ _ _).
  iApply (wp_storeField with "log"); first by (rewrite /field_ty /=; eauto).
  iIntros "!> log".
  wp_pures.

  destruct σ eqn:Hσ.
  rewrite /slidingM.logIndex /set /readonly_log /slidingM.numMutable /=.
  rewrite /= in logSlice_wf.
  rewrite /= in HnewStart.
  rewrite /slidingM.wf /= in Hwf.

  iAssert (∀ q, (updates_slice_frag
                      (slice_take logSlice
                         (uint64T * (blockT * unitT)%ht)
                         (word.sub mutable start)) q
                      (take (int.nat (word.sub mutable start))
                         log)) -∗
    (updates_slice_frag
       (slice_take
          (slice_skip logSlice (uint64T * (blockT * unitT)%ht)
             (word.sub newStart start))
          (uint64T * (blockT * unitT)%ht)
          (word.sub mutable newStart)) q
       (take (int.nat (word.sub mutable newStart))
          (drop (int.nat newStart - int.nat start) log))))%I as "Hlog_implies".
  {
    clear q.
    iIntros (q) "Hlog".
    iPoseProof (updates_slice_frag_split _ _ (int.nat newStart - int.nat start) with "Hlog") as "[Hlog _]".
    {
      rewrite /slice_take /=.
      word.
    }
    iExactEq "Hlog".
    f_equal.
    - rewrite /slice_take /slice_skip /=.
      repeat (f_equal; try word).
    - rewrite firstn_skipn_comm.
      repeat (f_equal; try word).
  }
  iPoseProof (readonly_weaken with "Hlog_implies log_readonly") as "> Hlog_frag".
  iClear "Hlog_implies".

  wp_storeField.
  iApply "HΦ".
  iFrame.
  iSplit.
  {
    iPureIntro.
    rewrite /slidingM.wf drop_length /=.
    word.
  }
  iExists _, _.
  iFrame.
  iSplitL "log_mutable".
  {
    rewrite /mutable_log /set drop_length /=.
    iSplit; first by (iPureIntro; word).
    rewrite /slice_skip /slidingM.numMutable drop_drop loc_add_assoc -Z.mul_add_distr_l /=.
    iExactEq "log_mutable".
    rewrite /named.
    repeat (f_equal; try word).
  }
  iExactEq "HaddrPos".
  rewrite /named.
  repeat (f_equal; try word).
Qed.

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

Theorem is_slice_small_take_all s t q vs (n: u64) :
  int.val n = int.nat s.(Slice.sz) →
  is_slice_small (slice_take s t n) t q vs ⊣⊢
  is_slice_small s t q vs.
Proof.
  intros.
  rewrite /is_slice_small.
  simpl.
  f_equiv.
  iPureIntro; intuition idtac.
  - word.
  - word.
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
  iDestruct (updates_slice_cap_acc with "log_mutable") as "[log_mutable log_mutable_cap]".
  unshelve iMod (readonly_alloc_1 with "log_mutable") as "readonly_new";
    (* XXX: why is this necessary to trigger typeclass resolution? *)
    [ | apply _ | ].
  rewrite /readonly_log.
  iMod (readonly_extend with "log_readonly readonly_new") as "log_readonly'".
  iClear "log_readonly".
  iModIntro.
  iApply "HΦ".
  iSplit.
  - iPureIntro.
    split_and!; simpl; try word.
  - simpl.
    iExists logSlice, addrPosPtr; iFrame.
    iSplitL "log_readonly'".

    + rewrite /readonly_log.
      simpl.
      iApply (readonly_iff with "log_readonly'").
      intros q; simpl.
      rewrite numMutable_after_clear; auto.
      iSplit.
      { iIntros "[Hupds1 Hupds2]".
        iDestruct (updates_slice_frag_combine with "[$Hupds1 $Hupds2]") as "Hupds".
        { word. }
        rewrite take_ge; len.
        iDestruct "Hupds" as (bks) "[Hs Hbks]".
        iExists _; iFrame.
        rewrite -> is_slice_small_take_all by word.
        iFrame.
      }
      iIntros "Hupds".
      rewrite {1}take_ge; len.
      iDestruct (updates_slice_frag_split _ _ (slidingM.numMutable σ) with "Hupds") as "[Hupds1 Hupds2]".
      { simpl; word. }
      iFrame.
      iDestruct "Hupds1" as (bks) "[Hs Hbks]".
      iExists _; iFrame.
      rewrite slice_skip_take_commute.
      rewrite -> is_slice_small_take_all by (simpl; word).
      iFrame.

    + rewrite /mutable_log /=.
      iSplit.
      { iPureIntro; word. }
      rewrite numMutable_after_clear; auto.
      rewrite drop_ge; len.
      rewrite updates_slice_cap_acc.
      iSplitR.
      { iExists nil; simpl.
        iSplit; auto.
        iApply is_slice_small_nil; simpl; word. }
      iApply (is_slice_cap_skip_more with "log_mutable_cap"); try word.
Qed.

End goose_lang.

Opaque is_sliding.
