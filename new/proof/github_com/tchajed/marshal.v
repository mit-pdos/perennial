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
  iDestruct (own_slice_len with "Hs") as %[Hsz Hpos].
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (is_pkg_init_unfold_deps with "[$]") as "(#Hbin & _)".
  wp_apply (wp_LittleEndian_Uint64 with "[$Hbin $Hs]").
  { rewrite u64_le_length //. }
  iIntros "Hs". wp_auto.
  rewrite length_app u64_le_length in Hsz.
  rewrite -> decide_True by word.
  wp_auto. rewrite u64_le_to_word. iApply "HΦ".
  assert (Hb: 0 ≤ sint.Z (W64 8) ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.len)) by word.
  iEval (rewrite (own_slice_slice (W64 8) s.(slice.len) s dq (u64_le x ++ tail) Hb)) in "Hs".
  iDestruct "Hs" as "(_ & Htail & _)".
  iExactEq "Htail". f_equal.
  rewrite /subslice.
  replace (sint.nat (W64 8)) with 8%nat by word.
  replace (sint.nat s.(slice.len)) with (8 + length tail)%nat by word.
  rewrite take_ge; [|rewrite length_app u64_le_length; lia].
  rewrite drop_app_length'; [done|rewrite u64_le_length //].
Qed.

Theorem wp_ReadInt32 tail s dq (x: u32) :
  {{{ is_pkg_init marshal ∗ s ↦*{dq} (u32_le x ++ tail) }}}
    @! marshal.ReadInt32 #s
  {{{ s', RET (#x, #s'); s' ↦*{dq} tail }}}.
Proof.
  wp_start as "Hs". wp_auto.
  iDestruct (own_slice_len with "Hs") as %[Hsz Hpos].
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (is_pkg_init_unfold_deps with "[$]") as "(#Hbin & _)".
  wp_apply (wp_LittleEndian_Uint32 with "[$Hbin $Hs]").
  { rewrite u32_le_length //. }
  iIntros "Hs". wp_auto.
  rewrite length_app u32_le_length in Hsz.
  rewrite -> decide_True by word.
  wp_auto. rewrite u32_le_to_word. iApply "HΦ".
  assert (Hb: 0 ≤ sint.Z (W64 4) ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.len)) by word.
  iEval (rewrite (own_slice_slice (W64 4) s.(slice.len) s dq (u32_le x ++ tail) Hb)) in "Hs".
  iDestruct "Hs" as "(_ & Htail & _)".
  iExactEq "Htail". f_equal.
  rewrite /subslice.
  replace (sint.nat (W64 4)) with 4%nat by word.
  replace (sint.nat s.(slice.len)) with (4 + length tail)%nat by word.
  rewrite take_ge; [|rewrite length_app u32_le_length; lia].
  rewrite drop_app_length'; [done|rewrite u32_le_length //].
Qed.

Theorem wp_ReadBytes s dq (len: u64) (head tail : list u8) :
  length head = uint.nat len →
  {{{ is_pkg_init marshal ∗ s ↦*{dq} (head ++ tail) }}}
    @! marshal.ReadBytes #s #len
  {{{ b s', RET (#b, #s'); b ↦*{dq} head ∗ s' ↦*{dq} tail }}}.
Proof.
  iIntros (Hlen). wp_start as "Hs". wp_auto.
  iDestruct (own_slice_len with "Hs") as %[Hsz Hpos].
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  rewrite length_app in Hsz.
  rewrite -> decide_True by word. wp_auto.
  rewrite -> decide_True by word. wp_auto.
  iApply "HΦ".
  assert (Hb: 0 ≤ sint.Z len ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.len)) by word.
  iEval (rewrite (own_slice_slice len s.(slice.len) s dq (head ++ tail) Hb)) in "Hs".
  iDestruct "Hs" as "(H1 & H2 & _)".
  iSplitL "H1".
  - iExactEq "H1". f_equal.
    replace (sint.nat len) with (length head) by word.
    rewrite take_app_length' //.
  - iExactEq "H2". f_equal. rewrite /subslice.
    replace (sint.nat s.(slice.len)) with (length head + length tail)%nat by word.
    rewrite take_ge; [|rewrite length_app; lia].
    replace (sint.nat len) with (length head) by word.
    rewrite drop_app_length' //.
Qed.

Theorem wp_ReadBytesCopy s q (len: u64) (head tail : list u8) :
  length head = uint.nat len →
  {{{ is_pkg_init marshal ∗ s ↦*{q} (head ++ tail) }}}
    @! marshal.ReadBytesCopy #s #len
  {{{ b s', RET (#b, #s'); b ↦*{DfracOwn 1} head ∗ s' ↦*{q} tail }}}.
Proof.
  iIntros (Hlen). wp_start as "Hs". wp_auto.
  iDestruct (own_slice_len with "Hs") as %[Hsz Hpos].
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  rewrite length_app in Hsz.
  wp_apply wp_slice_make2.
  { word. }
  iIntros (sl) "[Hsl Hcap]". wp_auto.
  rewrite -> decide_True by word. wp_auto.
  assert (Hb: 0 ≤ sint.Z len ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.len)) by word.
  iEval (rewrite (own_slice_slice len s.(slice.len) s q (head ++ tail) Hb)) in "Hs".
  iDestruct "Hs" as "(Hhead & Htail & _)".
  wp_apply (wp_slice_copy with "[$Hsl $Hhead]") as (n) "(%Hn & Hsl & Hhead)".
  rewrite -> decide_True by word. wp_auto.
  iApply "HΦ".
  iSplitL "Hsl".
  - iExactEq "Hsl". f_equal.
    replace (sint.nat len) with (length head) by word.
    rewrite length_replicate.
    rewrite take_app_length'; [|done].
    rewrite take_ge; [|done].
    rewrite drop_ge; [|rewrite length_replicate; done].
    rewrite app_nil_r //.
  - iExactEq "Htail". f_equal. rewrite /subslice.
    replace (sint.nat s.(slice.len)) with (length head + length tail)%nat by word.
    rewrite take_ge; [|rewrite length_app; lia].
    replace (sint.nat len) with (length head) by word.
    rewrite drop_app_length' //.
Qed.

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
  wp_apply (wp_ReadInt with "[$Hs]") as (?) "Hs".
  wp_apply (wp_ReadBytes with "[$]") as (? ?) "[Hb Hs]"; first trivial.
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
  iDestruct (own_slice_len with "Hs") as %[Hsz Hpos].
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  simpl in Hsz.
  rewrite -> decide_True by word.
  wp_apply (wp_load_slice_index with "[$Hs]") as "Hs"; [word | | ].
  { iPureIntro. reflexivity. }
  wp_auto.
  rewrite -> decide_True by word.
  wp_auto.
  iApply "HΦ".
  iSplit.
  - iPureIntro.
    case_bool_decide as H1; case_bool_decide as H2; simpl; try reflexivity; exfalso.
    + apply H2. subst bit. word.
    + apply H1. word.
  - assert (Hb: 0 ≤ sint.Z (W64 1) ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.len)) by word.
    iEval (rewrite (own_slice_slice (W64 1) s.(slice.len) s q (bit :: tail) Hb)) in "Hs".
    iDestruct "Hs" as "(_ & H & _)".
    iExactEq "H". f_equal. rewrite /subslice.
    replace (sint.nat s.(slice.len)) with (S (length tail)) by word.
    rewrite take_ge; [|simpl; lia].
    replace (sint.nat (W64 1)) with 1%nat by word.
    reflexivity.
Qed.

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
  iDestruct (is_pkg_init_unfold_deps with "[$]") as "(#Hbin & #Hstd & _)".
  wp_apply (wp_reserve with "[$Hs $Hcap]") as "%s2 (%Hroom & Hs & Hcap)".
  iDestruct (own_slice_len with "Hs") as %[Hsz Hpos].
  iDestruct (own_slice_cap_wf with "Hcap") as %Hcapwf.
  rewrite -> decide_True by word.
  wp_auto.
  set (B := slice.slice s2 w8 (W64 0) (word.add s2.(slice.len) (W64 8))).
  iDestruct (own_slice_slice_into_capacity (W64 0) (word.add s2.(slice.len) (W64 8)) s2 vs
              with "[$Hs $Hcap]") as (vs_cap) "(_ & Hb3 & Hb3cap)".
  { word. }
  rewrite drop_0. fold B.
  iDestruct (own_slice_cap_wf with "Hb3cap") as %HBwf.
  iDestruct (own_slice_len with "Hb3") as %[Hb3len _].
  rewrite length_app in Hb3len.
  assert (HBlen : sint.nat B.(slice.len) = (length vs + 8)%nat) by (subst B; simpl; word).
  assert (Hvc : length vs_cap = 8%nat) by lia.
  rewrite -> decide_True by (subst B; simpl; word).
  wp_auto.
  assert (Hbd : 0 ≤ sint.Z s2.(slice.len) ≤ sint.Z B.(slice.len) ≤ sint.Z B.(slice.len))
    by (subst B; simpl; word).
  iEval (rewrite (own_slice_slice s2.(slice.len) B.(slice.len) B _ (vs ++ vs_cap) Hbd)) in "Hb3".
  iDestruct "Hb3" as "(H0 & Hput & _)".
  assert (Htake : take (sint.nat s2.(slice.len)) (vs ++ vs_cap) = vs).
  { replace (sint.nat s2.(slice.len)) with (length vs) by word.
    rewrite take_app_length' //. }
  assert (Hsub : subslice (sint.nat s2.(slice.len)) (sint.nat B.(slice.len)) (vs ++ vs_cap) = vs_cap).
  { rewrite /subslice. rewrite take_ge; [|rewrite length_app; word].
    replace (sint.nat s2.(slice.len)) with (length vs) by word.
    rewrite drop_app_length' //. }
  iEval (rewrite Hsub) in "Hput".
  iEval (rewrite -{1}(app_nil_r vs_cap)) in "Hput".
  iEval (rewrite Htake) in "H0".
  wp_apply (wp_LittleEndian_PutUint64 with "[$Hbin $Hput]").
  { exact Hvc. }
  iIntros "Hput". wp_auto.
  iApply "HΦ". iFrame "Hb3cap".
  iApply own_slice_trivial_slice.
  iDestruct (own_slice_combine s2.(slice.len) with "H0 Hput") as "H".
  { split.
    - rewrite Hsz. word.
    - replace (sint.Z (W64 0)) with 0%Z by word. lia. }
  iExactEq "H". rewrite app_nil_r //.
Qed.

Theorem wp_WriteInt32 s x (vs : list u8) :
  {{{ is_pkg_init marshal ∗ s ↦*{DfracOwn 1} vs ∗ own_slice_cap w8 s (DfracOwn 1) }}}
    @! marshal.WriteInt32 (#s) #x
  {{{ s', RET #s'; s' ↦*{DfracOwn 1} (vs ++ u32_le x) ∗ own_slice_cap w8 s' (DfracOwn 1) }}}.
Proof.
  wp_start as "[Hs Hcap]". wp_auto.
  iDestruct (is_pkg_init_unfold_deps with "[$]") as "(#Hbin & #Hstd & _)".
  wp_apply (wp_reserve with "[$Hs $Hcap]") as "%s2 (%Hroom & Hs & Hcap)".
  iDestruct (own_slice_len with "Hs") as %[Hsz Hpos].
  iDestruct (own_slice_cap_wf with "Hcap") as %Hcapwf.
  rewrite -> decide_True by word.
  wp_auto.
  set (B := slice.slice s2 w8 (W64 0) (word.add s2.(slice.len) (W64 4))).
  iDestruct (own_slice_slice_into_capacity (W64 0) (word.add s2.(slice.len) (W64 4)) s2 vs
              with "[$Hs $Hcap]") as (vs_cap) "(_ & Hb3 & Hb3cap)".
  { word. }
  rewrite drop_0. fold B.
  iDestruct (own_slice_cap_wf with "Hb3cap") as %HBwf.
  iDestruct (own_slice_len with "Hb3") as %[Hb3len _].
  rewrite length_app in Hb3len.
  assert (HBlen : sint.nat B.(slice.len) = (length vs + 4)%nat) by (subst B; simpl; word).
  assert (Hvc : length vs_cap = 4%nat) by lia.
  rewrite -> decide_True by (subst B; simpl; word).
  wp_auto.
  assert (Hbd : 0 ≤ sint.Z s2.(slice.len) ≤ sint.Z B.(slice.len) ≤ sint.Z B.(slice.len))
    by (subst B; simpl; word).
  iEval (rewrite (own_slice_slice s2.(slice.len) B.(slice.len) B _ (vs ++ vs_cap) Hbd)) in "Hb3".
  iDestruct "Hb3" as "(H0 & Hput & _)".
  assert (Htake : take (sint.nat s2.(slice.len)) (vs ++ vs_cap) = vs).
  { replace (sint.nat s2.(slice.len)) with (length vs) by word.
    rewrite take_app_length' //. }
  assert (Hsub : subslice (sint.nat s2.(slice.len)) (sint.nat B.(slice.len)) (vs ++ vs_cap) = vs_cap).
  { rewrite /subslice. rewrite take_ge; [|rewrite length_app; word].
    replace (sint.nat s2.(slice.len)) with (length vs) by word.
    rewrite drop_app_length' //. }
  iEval (rewrite Hsub) in "Hput".
  iEval (rewrite -{1}(app_nil_r vs_cap)) in "Hput".
  iEval (rewrite Htake) in "H0".
  wp_apply (wp_LittleEndian_PutUint32 with "[$Hbin $Hput]").
  { exact Hvc. }
  iIntros "Hput". wp_auto.
  iApply "HΦ". iFrame "Hb3cap".
  iApply own_slice_trivial_slice.
  iDestruct (own_slice_combine s2.(slice.len) with "H0 Hput") as "H".
  { split.
    - rewrite Hsz. word.
    - replace (sint.Z (W64 0)) with 0%Z by word. lia. }
  iExactEq "H". rewrite app_nil_r //.
Qed.

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
  wp_apply (wp_slice_append with "[$Hs $Hdata $Hcap]") as (s') "(Hs' & Hcap' & Hdata')".
  iApply "HΦ". iFrame.
Qed.

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
  wp_apply (wp_WriteInt with "[$Hs $Hscap]") as (s') "[Hs' Hscap]".
  wp_apply (wp_WriteBytes with "[$Hs' $Hdata $Hscap]") as (s'0) "(Hs & Hscap & Hdata)".
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
  - wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [Hsl _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hs $Hcap $Hsl]") as (s') "(Hs' & Hcap' & _)".
    iApply "HΦ". iFrame.
  - wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [Hsl _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hs $Hcap $Hsl]") as (s') "(Hs' & Hcap' & _)".
    iApply "HΦ". iFrame.
Qed.

End wps.
