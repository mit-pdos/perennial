From Goose.github_com.mit_pdos.gokv.tutorial Require Import queue.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.program_proof Require Import proof_prelude.

Record qt :=
  mk { queue: list u64;
       first: u64;
       count: u64; }.

Section proof.

Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Definition valid_elems (slice : list u64) (first : u64) (count : u64) : list u64 :=
  subslice (uint.nat first) (uint.nat first + uint.nat count) (slice ++ slice).

Definition queue_size_inv (count : u64) (first : u64) (queue_size : Z): iProp Σ :=
  (⌜word.unsigned count <= queue_size⌝ ∗ ⌜word.unsigned first < queue_size⌝ ∗ ⌜queue_size > 0⌝ ∗ ⌜queue_size + 1 < 2 ^ 63⌝)%I.

Definition queue_inv_inner (q : loc) (queue : list u64) (first : u64) (count : u64) (queueSlice: Slice.t) : iProp Σ :=
  "#Hqueue" ∷ readonly (q ↦[Queue :: "queue"] (slice_val queueSlice)) ∗
  "Hfirst" ∷ (q ↦[Queue :: "first"] #first) ∗
  "Hcount" ∷ (q ↦[Queue :: "count"] #count) ∗
  "isSlice" ∷ own_slice_small queueSlice uint64T (DfracOwn 1) queue ∗
  "%Hqueue_size_inv" ∷ queue_size_inv count first (length queue).

Definition queue_inv (q : loc) (queueSlice: Slice.t) (P : u64 -> iProp Σ): iProp Σ :=
  ∃ (first : u64) (count : u64) (queue : list u64),
    "Hinner" ∷ queue_inv_inner q queue first count queueSlice ∗
    "Helem" ∷ ([∗ list] _ ↦ elem ∈ valid_elems queue first count, P elem). (* or not in queue *)

Definition is_queue (q : loc) (P : u64 -> iProp Σ) : iProp Σ :=
  ∃ (lk : loc) (cond : loc) (queueSlice: Slice.t),  
    "#Hlock" ∷ readonly (q ↦[Queue :: "lock"] #lk) ∗
    "#HlockC" ∷ is_lock nroot #lk (queue_inv q queueSlice P) ∗
    "#Hrcond" ∷ readonly (q ↦[Queue :: "cond"] #cond) ∗
    "#HrcondC" ∷ is_cond cond #lk.

Theorem init : forall slice, valid_elems slice 0 0 = nil.
Proof.
  eauto.
Qed.

Lemma add_one_lemma_1 : forall slice (first : u64) (count : u64) (e : u64),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  uint.Z count < length slice ->
  subslice (uint.nat first) (uint.nat first + uint.nat count)
  (<[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice ++
   <[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice) = subslice (uint.nat first) (uint.nat first + uint.nat count) (slice ++ slice).
Proof.
  intuition.
  assert (uint.nat first0 + uint.nat count0 < length slice ∨ (length slice <= uint.nat first0 + uint.nat count0 < length slice + length slice)).
  { word. }
  destruct H3.
  - replace (Z.to_nat(uint.Z (word.add first0 count0) `mod` length slice)) with (uint.nat(uint.nat first0 + uint.nat count0)).
    + rewrite subslice_take_drop.
      rewrite subslice_take_drop.
      rewrite take_app_le.
      2: { rewrite insert_length. word. }
      rewrite take_app_le.
      2: { word. }
      (* Check take_insert. *)
      rewrite take_insert.
      { done. }
      word.
    + word_cleanup.
      (* Search (_ `mod` _ = _). *)
      rewrite Z.mod_small.
      { done. }
      word.
  - replace (Z.to_nat(uint.Z (word.add first0 count0) `mod` length slice)) with (uint.nat(uint.nat first0 + uint.nat count0 - length slice)).
    + epose proof (subslice_split_r (uint.nat first0) (length slice) _ (_ ++ _)).
      rewrite H4.
      2: word.
      2: { rewrite app_length. rewrite insert_length. word. }
      epose proof (subslice_split_r (uint.nat first0) (length slice) _ (slice ++ slice)).
      rewrite H5.
      2: word.
      2: { rewrite app_length. word. }
      assert (subslice (uint.nat first0) (length slice)
      (<[uint.nat
           (uint.nat first0 + uint.nat count0 -
            length slice):=e]> slice ++
       <[uint.nat
           (uint.nat first0 + uint.nat count0 -
            length slice):=e]> slice) = subslice (uint.nat first0) (length slice)
            (slice ++ slice)).
        {
          rewrite <- subslice_before_app_eq.
          2: { rewrite insert_length. word. }
          rewrite <- subslice_before_app_eq.
          2: word.
          rewrite subslice_take_drop.
          rewrite subslice_take_drop.
          epose proof (insert_length slice (uint.nat (uint.nat first0 + uint.nat count0 - length slice)) e).
          rewrite firstn_all.
          replace ((take (length slice)
          (<[uint.nat
               (uint.nat first0 + uint.nat count0 -
                length slice):=e]> slice))) with (take (length (<[uint.nat
                (uint.nat first0 + uint.nat count0 -
                 length slice):=e]> slice))
                (<[uint.nat
                     (uint.nat first0 + uint.nat count0 -
                      length slice):=e]> slice)).
          2: { rewrite H6. eauto. }
          rewrite firstn_all.
          rewrite drop_insert_gt. 
          {done. }
          word_cleanup.
        }
      rewrite H6.
      rewrite app_inv_head_iff.
      rewrite subslice_comm.
      rewrite subslice_comm.
      rewrite drop_app_length.
      epose proof (insert_length slice (uint.nat (uint.nat first0 + uint.nat count0 - length slice)) e).
      replace ((drop (length slice)
                (<[uint.nat (uint.nat first0 + uint.nat count0 - length slice):=e]> slice ++
                <[uint.nat (uint.nat first0 + uint.nat count0 - length slice):=e]> slice))) with (drop (length (<[uint.nat
                (uint.nat first0 + uint.nat count0 -
                 length slice):=e]> slice))
                 (<[uint.nat (uint.nat first0 + uint.nat count0 - length slice):=e]> slice ++
                 <[uint.nat (uint.nat first0 + uint.nat count0 - length slice):=e]> slice)).
      2: { rewrite H7. eauto. }
      rewrite drop_app_length.
      rewrite take_insert.
      { eauto. }
      word_cleanup.
    + word_cleanup.
      assert (uint.Z first0 + uint.Z count0 = uint.Z first0 + uint.Z count0 - length slice + 1 * length slice).
      { word. }
      rewrite H7.
      rewrite Z_mod_plus.
      { rewrite Z.mod_small. 2: word. word_cleanup. }
      word.
  Unshelve.
  { exact u64. }
  { exact (uint.nat first0 + uint.nat count0)%nat. }
  { exact (<[uint.nat
  (uint.nat first0 + uint.nat count0 - length slice)%Z:=e]>
slice). }
  { exact (<[uint.nat
  (uint.nat first0 + uint.nat count0 - length slice)%Z:=e]>
slice). }
  exact (uint.nat first0 + uint.nat count0)%nat.
Qed.

Lemma add_one_lemma_2 : forall slice (first : u64) (count : u64) (e : u64),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  uint.Z count < length slice ->
  subslice (uint.nat first + uint.nat count) (uint.nat first + Z.to_nat(uint.Z count + 1))
  (<[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice ++
   <[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice) = [e].
Proof.
  intuition.
  assert (uint.nat first0 + uint.nat count0 < length slice ∨ (length slice <= uint.nat first0 + uint.nat count0 < length slice + length slice)).
  { word. }
  destruct H3.
  - replace (Z.to_nat(uint.Z (word.add first0 count0) `mod` length slice)) with (uint.nat(uint.nat first0 + uint.nat count0)).
    + rewrite subslice_comm.
      rewrite drop_app_le.
      2: { rewrite insert_length. word. }
      rewrite drop_insert_le.
      2: { word. }
      assert ((uint.nat (uint.nat first0 + uint.nat count0)%Z -
      (uint.nat first0 + uint.nat count0))%nat = uint.nat 0).
      { word_cleanup. }
      rewrite H4.
      match goal with
        | |- context [take ?n _] => replace n with 1%nat
      end.
      { rewrite insert_take_drop.
        { rewrite take_0.
          rewrite app_nil_l.
          rewrite firstn_cons.
          rewrite take_0.
          done.
        }
        rewrite drop_length.
        word.
      }
      word_cleanup.
    + word_cleanup.
      rewrite Z.mod_small.
      { done. }
      word.
  - replace (Z.to_nat(uint.Z (word.add first0 count0) `mod` length slice)) with (uint.nat(uint.nat first0 + uint.nat count0 - length slice)).
    + rewrite subslice_comm.
      rewrite drop_app_ge.
      2: { rewrite insert_length. word. }
      rewrite insert_length.
      rewrite drop_insert_le.
      2: { word. }
      assert ((uint.nat (uint.nat first0 + uint.nat count0 - length slice)%Z -
      (uint.nat first0 + uint.nat count0 - length slice))%nat = uint.nat 0).
      { word_cleanup. }
      rewrite H4.
      match goal with
        | |- context [take ?n _] => replace n with 1%nat
      end.
      { rewrite insert_take_drop.
        { rewrite take_0.
          rewrite app_nil_l.
          rewrite firstn_cons.
          rewrite take_0.
          done.
        }
        rewrite drop_length.
        word.
      }
      word.
    + word_cleanup.
      assert (uint.Z first0 + uint.Z count0 = uint.Z first0 + uint.Z count0 - length slice + 1 * length slice).
      { word. }
      rewrite H7.
      rewrite Z_mod_plus.
      { rewrite Z.mod_small. 2: word. word_cleanup. }
      word.
Qed.

Theorem add_one : forall slice (first : u64) (count : u64) e, 
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  uint.Z count < length slice ->
  valid_elems (<[uint.nat (word.modu ((word.add) first count) (length slice)):= e]> slice) first (word.add count 1) 
  = valid_elems slice first count ++ [e].
Proof.
  intuition.
  unfold valid_elems.
  word_cleanup.
  rewrite (subslice_split_r (uint.nat first0) (uint.nat first0 + uint.nat count0) _ (_ ++ _)).
  - rewrite add_one_lemma_1; eauto.
    rewrite app_inv_head_iff.
    apply add_one_lemma_2; eauto.
  - word.
  - rewrite app_length.
    rewrite insert_length.
    word.
Qed.

Lemma remove_one_lemma_1 : forall slice (first : u64) (e : u64),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  slice !! uint.nat first = Some e -> 
  subslice (uint.nat first) (uint.nat first + 1) (slice ++ slice) = [e].
Proof.
  intuition.
  rewrite subslice_comm.
  match goal with
    | |- context [take ?n _] => replace n with 1%nat
  end.
  2: { word. }
  rewrite drop_app_le.
  2: word.
  rewrite <- (take_drop_middle (slice) (uint.nat first0) e).
  2: eauto.
  rewrite drop_app_length'.
  2: { rewrite take_length. word. }
  rewrite firstn_cons.
  rewrite take_0.
  done.
Qed.

Lemma remove_one_lemma_2 : forall (slice : list u64) (first : u64) (count : u64) (e : u64),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  0 < uint.Z count <= length slice ->
  subslice (uint.nat first + 1) (uint.nat first + uint.nat count) (slice ++ slice) = 
  subslice (Z.to_nat
  (uint.Z (word.add first 1)
    `mod` length slice))
  (Z.to_nat
    (uint.Z (word.add first 1)
    `mod` length slice) + Z.to_nat (uint.Z count - 1)) (slice ++ slice).
Proof.
  intuition.
  assert (uint.Z first0 < length slice - 1 ∨ uint.Z first0 = length slice - 1).
  { word. }
  destruct H2.
  - rewrite Z.mod_small. 2: { word. }
    word_cleanup.
    replace (Init.Nat.add (Z.to_nat (word.unsigned first0)) 1)
      with (Z.to_nat (Z.add (word.unsigned first0) 1)).
    2: word.
    replace (Init.Nat.add (Z.to_nat (Z.add (word.unsigned first0) 1))
        (Z.to_nat (Z.sub (word.unsigned count0) 1)))
      with (Init.Nat.add (Z.to_nat (word.unsigned first0))
        (Z.to_nat (word.unsigned count0))).
    2: word.
    done.
  - rewrite H2.
    replace (Init.Nat.add (Z.to_nat (Z.sub (Datatypes.length slice) 1)) 1) with ((length slice)).
    2: word.
    replace (word.unsigned (word.add first0 1)) with (uint.Z (length slice)).
    2: word.
    replace ((uint.Z (length slice) `mod` length slice)) with 0.
    2: { rewrite Z_u64. { rewrite Z_mod_same. { done. } word. } word. }
    rewrite Z2Nat.inj_0.
    replace (Init.Nat.add 0 (Z.to_nat (Z.sub (word.unsigned count0) 1))) with (Z.to_nat (Z.sub (word.unsigned count0) 1)).
    2: word.
    rewrite subslice_comm.
    rewrite drop_app_length.
    rewrite subslice_comm.
    rewrite drop_0.
    replace (Init.Nat.sub (Z.to_nat (Z.sub (word.unsigned count0) 1)) 0) with (Z.to_nat (Z.sub (word.unsigned count0) 1)).
    2: word.
    replace (Init.Nat.sub
    (Init.Nat.add (Z.to_nat (Z.sub (Datatypes.length slice) 1))
       (Z.to_nat (word.unsigned count0)))
    (Datatypes.length slice)) with (Z.to_nat (Z.sub (word.unsigned count0) 1)).
    2: word.
    rewrite take_app_le.
    2: word.
    done.
Qed.

Theorem remove_one : forall slice (first : u64) (count : u64) e, 
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  0 < uint.Z count <= length slice ->
  slice !! uint.nat first = Some e -> 
  valid_elems slice first count = e :: valid_elems slice (word.modu ((word.add) first 1) (length slice)) (word.sub count 1).
Proof.
  intuition.
  unfold valid_elems.
  word_cleanup.
  rewrite (subslice_split_r (uint.nat first0) (uint.nat first0 + 1) _ (_++_)).
  - rewrite (remove_one_lemma_1 slice first0 e); eauto.
    rewrite app_inv_head_iff.
    apply remove_one_lemma_2; eauto.
  - word.
  - rewrite app_length. word.
Qed.

Lemma queue_peek_valid (q : loc) (gamma : namespace) (P : u64 -> iProp Σ):
  {{{ is_queue q P}}} Queue__Peek #q {{{ v ok, RET (#v, #ok); True }}}.
Proof.
  iIntros (Φ) "#Pre Post".
  unfold Queue__Peek.
  wp_pures.
  iNamed "Pre".
  wp_loadField.
  wp_apply acquire_spec.
  { iFrame "HlockC". }
  iIntros "[H0 H1]".
  wp_pures.
  iNamed "H1".
  iNamed "Hinner".
  wp_loadField.
  wp_if_destruct.
  - wp_loadField.
    wp_loadField.
    unfold queue_size_inv.
    edestruct (list_lookup_Z_lt queue0 (uint.Z first0)).
    { word. }
    { wp_apply (wp_SliceGet with "[isSlice]"). 
      { 
        (* iApply is_slice_to_small in "isSlice". *)
        iFrame "isSlice".
        eauto.
      }
      { iIntros "H1".
        wp_pures.
        wp_loadField.
        wp_apply (release_spec with "[HlockC H0 Hqueue Hfirst Hcount H1 Helem]").
        { iFrame "∗#". iNext. iExists _, _, _. iFrame. eauto. }
        wp_pures.
        iModIntro.
        iApply "Post".
        done.
      } }
  - wp_loadField.
    wp_apply (release_spec with "[HlockC H0 Hqueue Hfirst Hcount isSlice Helem]").
    { iFrame "∗#". iNext. iExists _,_,_. iFrame. eauto. }
    wp_pures.
    iModIntro.
    iApply "Post".
    done.
Qed.

Lemma readonly_struct_field_pointsto_agree E l d f v1 v2 :
  readonly (l ↦[d :: f] v1) -∗
    readonly (l ↦[d :: f] v2) -∗
      |={E}=> ⌜v1 = v2⌝.
Proof.
  iIntros "#H1 #H2".
  iMod (readonly_load with "H1") as (q1) "Hv1".
  iMod (readonly_load with "H2") as (q2) "Hv2".
  iDestruct (struct_field_pointsto_agree with "Hv1 Hv2") as "%Hv".
  done.
Qed.
(* src/program_proof/wal/installer_proof.v *)

Lemma enqueue_valid (q : loc) (a : u64) (gamma : namespace) (lk : val) (P : u64 -> iProp Σ):
  {{{ is_queue q P ∗ P a}}} Queue__Enqueue #q #a {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#Pre HP] Post".
  unfold Queue__Enqueue.
  wp_pures.
  iNamed "Pre".
  wp_loadField.
  wp_apply acquire_spec.
  {iFrame "HlockC". }
  iIntros "[H0 H1]".
  iNamed "H1".
  iNamed "Hinner".
  wp_pures.
  wp_apply (wp_loadField_ro with "Hqueue").
  wp_apply wp_slice_len.
  wp_apply wp_ref_to. {val_ty. }
  iIntros (queue_size) "H2".
  wp_pures.
  iPoseProof (own_slice_small_sz with "isSlice") as "%".
  (* Check wp_forBreak_cond. *)
  wp_apply (wp_forBreak_cond 
      (fun r =>
      ∃ (first : u64) (count : u64) (queue : list u64),
                queue_inv_inner q queue first count queueSlice ∗ 
                "Helem" ∷ ([∗ list] _ ↦ elem ∈ valid_elems queue first count, P elem) ∗ 
                queue_size ↦[uint64T] #queueSlice.(Slice.sz) ∗ 
                locked #lk0 ∗ 
                match r with
                  | false => ⌜uint.Z queueSlice.(Slice.sz) > uint.Z (count)⌝
                  | true => True
                end
                )%I with "[] [H0 Hqueue Hfirst Hcount isSlice H2 Helem]"). (* takes care of for loops of wait*)
  - iIntros (Φ') "".
    iModIntro.
    iIntros "H0".
    iDestruct "H0" as (first1 count1 queue1) "(H0 & Helem & H1 & H2 &H3)".
    iIntros "Post".
    iRename "Hqueue" into "Hqueue0".
    iNamed "H0".
    wp_load.
    wp_loadField.
    wp_if_destruct.
    + wp_loadField.
      wp_apply (wp_condWait with "[H2 Hfirst Hcount isSlice Helem]").
      { iFrame "# H2". iExists first1, count1, queue1. iFrame. eauto. }
      iIntros "[H0 H2]".
      wp_pures.
      iModIntro.
      iApply "Post".
      iFrame.
      iRename "Hqueue" into "Hqueue1".
      iNamed "H2".
      iExists first2, count2, queue2.
      iFrame.
    + iModIntro.
      iApply "Post".
      iFrame.
      iFrame "Hqueue".
      apply Z.lt_nge in Heqb.
      iPureIntro.
      word.
  - iFrame "H2".
    iFrame "H0".
    iExists first0, count0, queue0.
    iFrame.
    iFrame "Hqueue".
    eauto.
  - iIntros "H0".
    iDestruct "H0" as (first1 count1 queue1) "(H0 & Helem & H1 & H2 & %Hcount)".
    wp_pures.
    iRename "Hqueue" into "Hqueue0".
    iNamed "H0".
    wp_loadField.
    wp_loadField.
    wp_load.
    wp_pures.
    wp_apply wp_ref_to.
    { val_ty. }
    iIntros (l) "Hl".
    wp_pures.
    wp_load.
    wp_loadField.
    (* Search SliceSet. *)
    (* Search is_slice_small length Slice.sz. *)
    iPoseProof (own_slice_small_sz with "isSlice") as "%".
    wp_apply (wp_SliceSet (V:=u64) with "[isSlice]").
    { iFrame. iPureIntro. apply lookup_lt_is_Some_2. rewrite H0.
      (* Search word.modu. *)
      (* Search (_ `mod` _) (_ < _).  *)
      (* Z_mod_lt: ∀ a b : Z, b > 0 → 0 ≤ a `mod` b < b *)
      epose proof (Z_mod_lt _ (uint.Z queueSlice.(Slice.sz))).
      destruct H1.
      { epose proof (u64_Z_through_nat (queueSlice.(Slice.sz))).
        (* Check u64_Z_through_nat. *)
        (* Check u64_Z. *)
        rewrite <- H1.
        rewrite <- H0.
        apply Hqueue_size_inv0.
        }
      apply Nat2Z.inj_lt.
      assert (uint.Z queueSlice.(Slice.sz) ≠ 0).
      { epose proof (u64_Z_through_nat (queueSlice.(Slice.sz))).
        rewrite <- H3.
        rewrite <- H0.
        word.
      }
      epose proof (word.unsigned_modu_nowrap (word.add first1 count1) queueSlice.(Slice.sz)).
      epose proof (u64_Z_through_nat (word.modu
      (word.add first1 count1)
      queueSlice.(Slice.sz))).
      rewrite H5.
      rewrite H4.
      { epose proof (u64_Z_through_nat (queueSlice.(Slice.sz))).
        rewrite H6.
        apply H2. 
      }
      eauto. }
    iIntros "H4".
    wp_pures.
    wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[H2 Hqueue Hfirst Hcount H4 Helem HP]").
    { iFrame "HlockC". 
      iFrame "H2". iNext. iExists _, (word.add count1 1).
      iExists (<[uint.nat
      (word.modu
         (word.add first1 count1)
         queueSlice.(Slice.sz)):=a]> queue1). 
      iFrame.
      iFrame "Hqueue".
      (* Search big_opL insert. *)
      iSplitR.
      { 
        iPureIntro.
        (* Search length insert list. *)
        rewrite insert_length.
        intuition eauto.
        word.
      }
      edestruct (list_lookup_Z_lt queue1 (uint.nat
      (word.modu
        (word.add first1 count1)
        queueSlice.(Slice.sz)))).
        { split. { word. }
          epose proof (Z_mod_lt _ (length queue1)).
          destruct H1. { word. }
          epose proof (word.unsigned_modu_nowrap (word.add first1 count1) queueSlice.(Slice.sz)).
          rewrite u64_Z_through_nat.
          rewrite H3.
          { epose proof (u64_Z_through_nat (queueSlice.(Slice.sz))).
            rewrite <- H4.
            rewrite <- H0.
            apply H2. }
          word. }
          replace queueSlice.(Slice.sz) with (W64 (length queue1)).
          { rewrite add_one. 
            { rewrite big_sepL_app. simpl. iFrame. }
            { destruct Hqueue_size_inv. destruct H3. word. }
            { intuition. }
            { word. }
            word.
          }
          word. }
    wp_pures.
    wp_loadField.
    wp_apply (wp_condBroadcast with "HrcondC").
    wp_pures.
    iModIntro.
    iApply "Post".
    done.
Qed.

Lemma enqueue_dequeue (q : loc) (gamma : namespace) (lk : val) (P : u64 -> iProp Σ):
  {{{ is_queue q P }}} Queue__Dequeue #q {{{ (a:u64), RET #a; P a }}}.
Proof.
  iIntros (Φ) "#Pre Post".
  unfold Queue__Dequeue.
  wp_pures.
  iNamed "Pre".
  wp_loadField.
  wp_apply acquire_spec.
  { iFrame "HlockC". }
  iIntros "[H0 H1]".
  wp_pures.
  iNamed "H1".
  iNamed "Hinner".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_apply wp_ref_to. {val_ty. }
  iIntros (queue_size) "H2".
  wp_pures.
  iPoseProof (own_slice_small_sz with "isSlice") as "%".
  wp_apply (wp_forBreak_cond 
  (fun r =>
  ∃ (first : u64) (count : u64) (queue : list u64),
            queue_inv_inner q queue first count queueSlice ∗ 
            "Helem" ∷ ([∗ list] _ ↦ elem ∈ valid_elems queue first count, P elem) ∗ 
            queue_size ↦[uint64T] #queueSlice.(Slice.sz) ∗ 
            locked #lk0 ∗ 
            match r with
              | false => ⌜uint.Z (count) ≠ 0⌝
              | true => True
            end
            )%I with "[] [H0 Hqueue Hfirst Hcount isSlice H2 Helem]").
  - iIntros (Φ') "".
    iModIntro.
    iIntros "H0".
    iDestruct "H0" as (first1 count1 queue1) "(H0 & Helem & H1 & H2 & H3)".
    iIntros "Post".
    iRename "Hqueue" into "Hqueue0".
    iNamed "H0".
    wp_loadField.
    wp_if_destruct.
    + wp_pures.
      wp_loadField.
      wp_apply (wp_condWait with "[H2 Hfirst Hcount isSlice Helem]").
      { iFrame "# H2". iExists first1, (W64 0), queue1. iFrame. eauto. }
      iIntros "[H2 H4]".
      wp_pures.
      iModIntro.
      iApply "Post".
      iFrame.
      iRename "Hqueue" into "Hqueue1".
      iNamed "H4".
      iExists first2, count1, queue2.
      iFrame.
    + iModIntro.
      iApply "Post".
      iFrame.
      iFrame "Hqueue".
      iPureIntro.
      apply u64_val_ne in Heqb.
      rewrite unsigned_U64_0 in Heqb.
      word.
  - iExists first0, count0, queue0.
    iFrame.
    iFrame "Hqueue".
    eauto.
  - iIntros "H0".
    iDestruct "H0" as (first1 count1 queue1) "(H0 & Helem & H1 & H2 & %Hcount)".
    wp_pures.
    iRename "Hqueue" into "Hqueue0".
    iNamed "H0".
    wp_loadField.
    wp_loadField.
    iPoseProof (own_slice_small_sz with "isSlice") as "%".
    edestruct (list_lookup_Z_lt queue1 (uint.Z first1)).
    { word. }
    wp_apply (wp_SliceGet with "[isSlice]"). 
    { 
      iFrame "isSlice".
      eauto.
    }
    iIntros "H3".
    wp_pures.
    wp_loadField.
    wp_pures.
    wp_load.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_loadField.
    erewrite (remove_one queue1 first1 count1); eauto; try word.
    iDestruct "Helem" as "[Hp Helem]". 
    wp_apply (release_spec with "[HlockC H2 Hqueue Hfirst Hcount H3 Helem]").
    { iFrame "∗#". 
      iNext.
      iExists _, (word.sub count1 1).
      iExists _. 
      iFrame "Hfirst Hcount H3". 
      iFrame "Hqueue".
      iSplitR.
      { 
        iPureIntro.
        intuition eauto.
        { word. }
        word_cleanup.
        rewrite H0.
        rewrite u64_Z_through_nat.
        apply Z_mod_lt.
        word.
      }
      iRename "Helem" into "Helem_old".
      iExactEq "Helem_old". unfold named. rewrite H0. f_equal. f_equal. f_equal.
      rewrite <- u64_Z. rewrite u64_Z_through_nat.
      reflexivity. 
      }
      wp_pures.
      wp_loadField.
      wp_apply (wp_condBroadcast with "HrcondC").
      wp_pures.
      iModIntro.
      iApply "Post".
      iFrame.
Qed.

End proof.
