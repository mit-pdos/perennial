From Perennial.Helpers Require Import List ListLen.

(* TODO: might need pure theory from here *)
(* From Perennial.goose_lang.lib Require Import encoding. *)

From New.proof Require Import
  github_com.goose_lang.std
  github_com.goose_lang.primitive
  encoding.binary.
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.tchajed Require Import marshal.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : marshal.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) marshal := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) marshal := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop marshal get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    marshal.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init marshal }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ") as "Hown".
  { destruct Hinit as (-> & ?). reflexivity. }
  wp_apply (std.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (binary.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

(* Some helper definition for working with slices of primitive values. *)

Definition uint64_has_encoding (encoded : list u8) (x : u64) : Prop :=
  encoded = u64_le x.

Definition uint32_has_encoding (encoded : list u8) (x : u32) : Prop :=
  encoded = u32_le x.

Definition bool_has_encoding (encoded : list u8) (x : bool) : Prop :=
  encoded = [if x then W8 1 else W8 0].

Definition string_has_encoding (encoded : list u8) (x : byte_string) : Prop :=
  encoded = x.

Definition byte_has_encoding (encoded : list u8) (x : list u8) : Prop :=
  encoded = x.

Theorem wp_ReadInt tail (s : slice.t) dq x :
  {{{ is_pkg_init marshal ∗ s ↦*{dq} (u64_le x ++ tail) }}}
    @! marshal.ReadInt #s
  {{{ s', RET (#x, #s'); s' ↦*{dq} tail }}}.
Proof.
  wp_start as "Hs". wp_auto.
  (*
  wp_apply (wp_UInt64Get_unchanged with "Hs").
  { rewrite /list.untype fmap_app take_app_length' //. len. }
  iIntros "Hs".
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'". wp_auto. iApply "HΦ".
  rewrite drop_app_length'; [done|len].
Qed.
*)
Admitted.

Theorem wp_ReadInt32 tail s dq (x: u32) :
  {{{ is_pkg_init marshal ∗ s ↦*{dq} (u32_le x ++ tail) }}}
    @! marshal.ReadInt32 #s
  {{{ s', RET (#x, #s'); s' ↦*{dq} tail }}}.
Proof.
  wp_start as "Hs". wp_auto.
(*
  wp_apply (wp_UInt32Get_unchanged with "Hs").
  { rewrite /list.untype fmap_app take_app_length' //. len. }
  iIntros "Hs".
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'". wp_auto. iApply "HΦ".
  rewrite drop_app_length'; [done|len].
Qed.
*)
Admitted.

Theorem wp_ReadBytes s dq (len: u64) (head tail : list u8) :
  length head = uint.nat len →
  {{{ is_pkg_init marshal ∗ s ↦*{dq} (head ++ tail) }}}
    @! marshal.ReadBytes #s #len
  {{{ b s', RET (#b, #s'); b ↦*{dq} head ∗ s' ↦*{dq} tail }}}.
Proof.
  iIntros (Hlen). wp_start as "Hs". wp_auto.
(*
  iDestruct (own_slice_len with "Hs") as %Hsz.
  autorewrite with len in Hsz.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_apply (wp_SliceTake).
  { word. }
  wp_apply (wp_SliceSkip).
  { word. }
  wp_auto.
  iModIntro.
  iApply "HΦ".
  iDestruct (slice_small_split _ len with "Hs") as "[Hs1 Hs2]".
  { len. }
  iSplitL "Hs1".
  - rewrite take_app_length' //.
  - rewrite drop_app_length' //.
Qed.
*)
Admitted.

Theorem wp_ReadBytesCopy s q (len: u64) (head tail : list u8) :
  length head = uint.nat len →
  {{{ is_pkg_init marshal ∗ s ↦*{q} (head ++ tail) }}}
    @! marshal.ReadBytesCopy #s #len
  {{{ b s', RET (#b, #s'); b ↦*{DfracOwn 1} head ∗ s' ↦*{q} tail }}}.
Proof.
  iIntros (Hlen). wp_start as "Hs". wp_auto.
(*
  wp_apply wp_NewSlice. iIntros (b) "Hb".
  iDestruct (own_slice_len with "Hs") as %Hsz.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  rewrite length_app in Hsz.
  wp_apply wp_SliceTake.
  { word. }
  iDestruct (slice_small_split _ len with "Hs") as "[Hs Hsclose]".
  { rewrite length_app. word. }
  iDestruct (own_slice_acc with "Hb") as "[Hb Hbclose]".
  wp_apply (wp_SliceCopy_full with "[$Hs $Hb]").
  { iPureIntro. len. }
  iIntros (l) "(%Hl_val & Hs & Hb)".
  iDestruct (own_slice_combine with "Hs Hsclose") as "Hs".
  { word. }
  rewrite take_drop.
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'".
  wp_auto. iApply "HΦ". iModIntro. iSplitR "Hs'".
  - iApply "Hbclose". rewrite take_app_length' //.
  - rewrite drop_app_length' //.
Qed.
*)
Admitted.

Theorem wp_ReadLenPrefixedBytes s q (len: u64) (head tail : list u8):
  length head = uint.nat len →
  {{{
        is_pkg_init marshal ∗
        s ↦*{q} ((u64_le len) ++ head ++ tail)
  }}}
    @! marshal.ReadLenPrefixedBytes #s
  {{{
        b s', RET (#b, #s'); b ↦*{q} head ∗ s' ↦*{q} tail
  }}}.
Proof.
  iIntros (Hlen).
  wp_start as "Hs". wp_auto.
  wp_apply (wp_ReadInt with "[$Hs]").
  iIntros (?) "Hs". wp_auto.
  wp_apply (wp_ReadBytes with "[$]"); first trivial.
  iIntros (??) "[Hb Hs]". wp_auto.
  iApply "HΦ". iFrame.
Qed.

Theorem wp_ReadBool s q (bit: u8) (tail: list u8) :
  {{{ is_pkg_init marshal ∗ s ↦*{q} (bit :: tail) }}}
    @! marshal.ReadBool (#s)
  {{{ (b: bool) s', RET (#b, #s');
      ⌜b = bool_decide (uint.Z bit ≠ 0)⌝ ∗
      s' ↦*{q} tail }}}.
Proof.
  wp_start as "Hs". wp_auto.
(*
  wp_apply (wp_SliceGet with "[$Hs]"); [ auto | ].
  iIntros "Hs".
  wp_auto.
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs".
  wp_auto. iModIntro.
  iApply "HΦ".
  iSplit.
  { iPureIntro. rewrite -bool_decide_not !bool_decide_decide.
    assert (#bit ≠ #(U8 0) ↔ uint.Z bit ≠ 0).
    { apply not_iff_compat.
      split.
    - inversion 1; subst; auto.
    - intros H.
      repeat (f_equal; try word).
    }
    destruct (decide _), (decide _); auto; tauto.
  }
  iApply "Hs".
Qed.
*)
Admitted.

Lemma drop_succ :
  forall {A : Type} (l : list A) (x : A) (l' : list A) (n : nat),
  l !! n = Some x -> drop n l = x :: l' -> drop (S n) l = l'.
Proof.
  intros A l x l' n Helem Hd.
  pose proof drop_S l x n. apply H in Helem. rewrite Helem in Hd.
  inversion Hd. reflexivity.
Qed.

Fixpoint encodes {A:Type} (enc : list u8) (xs : list A) (has_encoding : list u8 -> A -> Prop): Prop :=
  match xs with
    | [] => enc = []
    | x :: xs' => exists bs bs', xs = x :: xs' /\ enc = bs ++ bs' /\ has_encoding bs x /\ encodes bs' xs' has_encoding
  end.

Local Theorem wp_compute_new_cap (old_cap min_cap : u64) :
  {{{ is_pkg_init marshal }}}
    @! marshal.compute_new_cap #old_cap #min_cap
  {{{ (new_cap : u64), RET #new_cap; ⌜uint.Z min_cap ≤ uint.Z new_cap⌝ }}}.
Proof.
  wp_start as "_". wp_auto.
  case_bool_decide; wp_auto.
  - iApply "HΦ". word.
  - iApply "HΦ". word.
Qed.

Local Theorem wp_reserve s (extra : u64) (vs : list u8) :
  {{{ is_pkg_init marshal ∗ s ↦*{DfracOwn 1} vs ∗ own_slice_cap w8 s (DfracOwn 1) }}}
    @! marshal.reserve (#s) #extra
  {{{ s', RET #s';
      ⌜uint.Z extra ≤ uint.Z (slice.cap s') - uint.Z (slice.len s')⌝ ∗
      s' ↦*{DfracOwn 1} vs ∗ own_slice_cap w8 s' (DfracOwn 1) }}}.
Proof.
  wp_start as "[Hs Hcap]". wp_auto.
(*
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len.
  wp_apply wp_SumAssumeNoOverflow. iIntros (Hsum).
  wp_auto. wp_apply wp_slice_cap.
  wp_if_destruct.
  - (* we have to grow. *)
    wp_apply wp_slice_cap.
    wp_apply wp_compute_new_cap.
    iIntros (new_cap Hcap).
    wp_apply wp_slice_len.
    wp_apply wp_new_slice_cap; first done.
    { word. }
    iIntros (ptr) "Hnew". wp_auto.
    iDestruct (slice.own_slice_to_small with "Hs") as "Hs".
    iDestruct (slice.own_slice_acc with "Hnew") as "[Hnew Hcl]".
    wp_apply (slice.wp_SliceCopy_full with "[Hnew Hs]").
    { iFrame. iPureIntro. rewrite list_untype_length Hsz length_replicate //. }
    iIntros "[_ Hnew]". iDestruct ("Hcl" with "Hnew") as "Hnew".
    wp_auto. iApply "HΦ". iModIntro. iFrame. iPureIntro. simpl. word.
  - (* already big enough *)
    iApply "HΦ". iFrame. word.
Qed.
*)
Admitted.

Theorem wp_WriteInt s x (vs : list u8) :
  {{{ is_pkg_init marshal ∗ s ↦*{DfracOwn 1} vs ∗ own_slice_cap w8 s (DfracOwn 1) }}}
    @! marshal.WriteInt (#s) #x
  {{{ s', RET #s'; s' ↦*{DfracOwn 1} (vs ++ u64_le x) ∗ own_slice_cap w8 s' (DfracOwn 1) }}}.
Proof.
  wp_start as "[Hs Hcap]". wp_auto.
(*
  wp_apply (wp_reserve with "Hs"). clear s. iIntros (s) "[% Hs]". wp_auto.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len. wp_auto.
  wp_apply (wp_SliceTake_full_cap with "Hs").
  { word. }
  iIntros (ex) "[%Hex Hsl]".
  set (s' := slice_take _ _).
  wp_apply wp_SliceSkip.
  { rewrite /slice_take /=. word. }
  iDestruct (slice.own_slice_split_acc s.(slice.len_f) with "Hsl") as "[Hsl Hclose]".
  { len. }
  wp_apply (wp_UInt64Put with "Hsl").
  { len. }
  iIntros "Hsl". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_auto. iApply "HΦ". iModIntro.
  rewrite /own_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  { rewrite take_app_length' //. len. }
  rewrite drop_ge; [|len].
  by list_simplifier.
Qed.
*)
Admitted.

Theorem wp_WriteInt32 s x (vs : list u8) :
  {{{ is_pkg_init marshal ∗ s ↦*{DfracOwn 1} vs ∗ own_slice_cap w8 s (DfracOwn 1) }}}
    @! marshal.WriteInt32 (#s) #x
  {{{ s', RET #s'; s' ↦*{DfracOwn 1} (vs ++ u32_le x) ∗ own_slice_cap w8 s' (DfracOwn 1) }}}.
Proof.
  wp_start as "[Hs Hcap]". wp_auto.
(*
  wp_apply (wp_reserve with "Hs"). clear s. iIntros (s) "[% Hs]". wp_auto.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len. wp_auto.
  wp_apply (wp_SliceTake_full_cap with "Hs").
  { word. }
  iIntros (ex) "[%Hex Hsl]".
  set (s' := slice_take _ _).
  wp_apply wp_SliceSkip.
  { rewrite /slice_take /=. word. }
  iDestruct (slice.own_slice_split_acc s.(slice.len_f) with "Hsl") as "[Hsl Hclose]".
  { len. }
  wp_apply (wp_UInt32Put with "Hsl").
  { len. }
  iIntros "Hsl". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_auto. iApply "HΦ". iModIntro.
  rewrite /own_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  { rewrite take_app_length' //. len. }
  rewrite drop_ge; [|len].
  by list_simplifier.
Qed.
*)
Admitted.

Theorem wp_WriteBytes s (vs : list u8) data_sl q (data : list u8) :
  {{{ is_pkg_init marshal ∗ s ↦*{DfracOwn 1} vs ∗ data_sl ↦*{q} data ∗ own_slice_cap w8 s (DfracOwn 1) }}}
    @! marshal.WriteBytes (#s) (#data_sl)
  {{{ s', RET #s';
    s' ↦*{DfracOwn 1} (vs ++ data) ∗
    own_slice_cap w8 s' (DfracOwn 1) ∗
    data_sl ↦*{q} data
  }}}.
Proof.
  wp_start as "(Hs & Hcap & Hdata)". wp_auto.
(*
  wp_apply (wp_SliceAppendSlice with "[$Hs $Hdata]"); first done.
  iIntros (s') "[Hs' Hdata]".
  iApply ("HΦ" with "[$]").
Qed.
*)
Admitted.

Theorem wp_WriteLenPrefixedBytes s (vs : list u8) data_sl q (data : list u8) :
  {{{
        is_pkg_init marshal ∗
        s ↦*{DfracOwn 1} vs ∗
        data_sl ↦*{q} data ∗
        own_slice_cap w8 s (DfracOwn 1)
  }}}
    @! marshal.WriteLenPrefixedBytes #s #data_sl
  {{{
        s', RET #s';
        s' ↦*{DfracOwn 1} (vs ++ (u64_le $ (W64 $ length data)) ++ data) ∗
        own_slice_cap w8 s' (DfracOwn 1) ∗
        data_sl ↦*{q} data
  }}}.
Proof.
  wp_start as "(Hs & Hdata & Hscap)". wp_auto.
  wp_apply (wp_WriteInt with "[$Hs $Hscap]").
  iIntros (s') "[Hs' Hscap]". wp_auto.
  wp_apply (wp_WriteBytes with "[$Hs' $Hdata $Hscap]").
  iIntros (s'0) "(Hs & Hscap & Hdata)". wp_auto.
  iApply "HΦ".
  rewrite -app_assoc.
  iDestruct (own_slice_len with "Hdata") as "[%Hdlen %]".
  rewrite Hdlen.
  iFrame.
  iExactEq "Hs".
  repeat (f_equal; try word).
Qed.

Theorem wp_WriteBool s (vs: list u8) (b: bool) :
  {{{ is_pkg_init marshal ∗ s ↦*{DfracOwn 1} vs ∗ own_slice_cap w8 s (DfracOwn 1) }}}
    @! marshal.WriteBool #s #b
  {{{ s', RET (#s');
      s' ↦*{DfracOwn 1} (vs ++ [if b then W8 1 else W8 0]) ∗
      own_slice_cap w8 s' (DfracOwn 1)
   }}}.
Proof.
  wp_start as "[Hs Hcap]". wp_auto.
  destruct b; wp_auto.
(*
  - wp_apply (wp_SliceAppend with "Hs"); auto.
  - wp_apply (wp_SliceAppend with "Hs"); auto.
Qed.
*)
Admitted.

End wps.
