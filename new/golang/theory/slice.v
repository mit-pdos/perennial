From New.golang.defn Require Export slice.
From New.golang.theory Require Export array loop auto assume.

#[local]
Transparent slice.for_range.

Section defns_and_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Definition own_slice_def {V} `{!ZeroVal V} `{!TypedPointsto V}
  (s : slice.t) (dq : dfrac) (vs : list V)
  : iProp Σ :=
  (s.(slice.ptr) ↦{dq} (array.mk (sint.Z s.(slice.len)) vs)) ∗
  ⌜ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap) ⌝.
Program Definition own_slice := sealed @own_slice_def.
Definition own_slice_unseal : own_slice = _ := seal_eq _.

Global Arguments own_slice {_ _ _} (s dq vs).

Notation "s ↦* dq vs" := (own_slice s dq vs)
                           (at level 20, dq custom dfrac at level 50, format "s  ↦* dq  vs").

Definition own_slice_cap_def {V} `{!ZeroVal V} `{!TypedPointsto V}
  (s : slice.t) (dq : dfrac) : iProp Σ :=
  ⌜ 0 ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap) ⌝ ∗
  (* The capacity buffer has arbitrary values, which is often desirable, but
  there are some niche cases where code could be aware of the contents of the
  capacity (for example, when sub-slicing from a larger slice) - actually taking
  advantage of that seems questionable though. *)
  ∃ (a : array.t V $ (sint.Z s.(slice.cap) - sint.Z s.(slice.len))),
    (slice_index_ref V (sint.Z s.(slice.len)) s) ↦{dq} a.
Program Definition own_slice_cap := sealed @own_slice_cap_def.
Definition own_slice_cap_unseal : own_slice_cap = _ := seal_eq _.
Global Arguments own_slice_cap (_) {_ _} (s dq).

Context `[!ZeroVal V] `[!TypedPointsto (Σ:=Σ) V].
Implicit Type (vs : list V).

Ltac unseal := rewrite ?own_slice_unseal /own_slice_def
                 ?own_slice_cap_unseal /own_slice_cap_def.

Lemma own_slice_nil dq :
  ⊢ slice.nil ↦*{dq} ([] : list V).
Proof.
  unseal. simpl. iDestruct array_empty as "$". done.
Qed.

Lemma own_slice_empty dq s :
  sint.Z s.(slice.len) = 0 ->
  0 ≤ sint.Z s.(slice.cap) ->
  ⊢ s ↦*{dq} ([] : list V).
Proof.
  unseal. intros Hsz Hcap. destruct s. simpl in *.
  rewrite Hsz.
  iDestruct array_empty as "$". word.
Qed.

Lemma own_slice_cap_none s :
  s.(slice.len) = s.(slice.cap) →
  0 ≤ sint.Z s.(slice.len) →
  ⊢ own_slice_cap V s (DfracOwn 1).
Proof.
  destruct s; simpl; intros Hcap Hlen. rewrite own_slice_cap_unseal /own_slice_cap_def /=.
  iSplit; [ word | ].
  iExists (array.mk _ []). rewrite /slice_index_ref /=.
  subst.
  replace (_ - _) with 0 by word.
  iDestruct (array_empty (array_index_ref V _ ptr) (DfracOwn 1)) as "H".
  iExactEq "H".  f_equal.
Qed.

Lemma own_slice_len s dq vs :
  s ↦*{dq} vs -∗ ⌜length vs = sint.nat s.(slice.len) ∧ 0 ≤ sint.Z s.(slice.len)⌝.
Proof.
  unseal. iIntros "(H&%)". iDestruct (array_len with "H") as %?. word.
Qed.

Lemma own_slice_agree s dq1 dq2 vs1 vs2 :
  s ↦*{dq1} vs1 -∗
  s ↦*{dq2} vs2 -∗
  ⌜vs1 = vs2⌝.
Proof.
  unseal. iIntros "[Hs1 %] [Hs2 %]".
  iCombine "Hs1 Hs2" gives %[=->]. done.
Qed.

Global Instance own_slice_persistent s vs : Persistent (s ↦*□ vs).
Proof. unseal. apply _. Qed.

#[global]
Instance own_slice_dfractional s vs :
  DFractional (λ dq, s ↦*{dq} vs).
Proof. unseal; apply _. Qed.

#[global]
Instance own_slice_as_dfractional s dq vs :
  AsDFractional (s ↦*{dq} vs) (λ dq, s ↦*{dq} vs) dq.
Proof. auto. Qed.

#[global]
Instance own_slice_as_fractional s q vs :
  fractional.AsFractional (s ↦*{#q} vs) (λ q, s ↦*{#q} vs) q.
Proof.
  split; auto.
  change (λ q0 : Qp, s ↦*{#q0} vs) with (λ q : Qp, (λ dq, s ↦*{dq} vs) (DfracOwn q)).
  apply fractional_of_dfractional.
  apply _.
Qed.

Global Instance own_slice_combine_sep_gives s dq1 dq2 vs1 vs2 :
  CombineSepGives (s ↦*{dq1} vs1) (s ↦*{dq2} vs2) (⌜ vs1 = vs2 ⌝).
Proof.
  rewrite /CombineSepGives.
  iIntros "[H0 H1]".
  iDestruct (own_slice_agree with "H0 H1") as %->.
  naive_solver.
Qed.

Global Instance own_slice_combine_sep_as s dq1 dq2 vs1 vs2 :
  CombineSepAs (s ↦*{dq1} vs1) (s ↦*{dq2} vs2) (s ↦*{dq1 ⋅ dq2} vs1) | 60.
Proof.
  rewrite /CombineSepAs.
  iIntros "[H0 H1]".
  iDestruct (own_slice_agree with "H0 H1") as %->.
  by iCombine "H0 H1" as "?".
Qed.

Global Instance own_slice_cap_persistent s : Persistent (own_slice_cap V s (□)).
Proof. unseal; apply _. Qed.

#[global]
Instance own_slice_cap_dfractional s :
  DFractional (λ dq, own_slice_cap V s dq).
Proof.
  unseal.
  apply dfractional_sep; [apply _|].
  split.
  - intros ??. iSplit.
    + iIntros "[% [H0 H1]]". iFrame.
    + iIntros "[[% H0] [% H1]]".
      iCombine "H0 H1" gives %[=->].
      iCombine "H0 H1" as "H".
      iFrame.
  - apply _.
  - iIntros (?) "[% H]". iPersist "H". by iFrame "#".
Qed.

#[global]
Instance own_slice_cap_as_dfractional s dq :
  AsDFractional (own_slice_cap V s dq) (λ dq, own_slice_cap V s dq) dq.
Proof. auto. Qed.

Lemma own_slice_persist s dq vs:
  s ↦*{dq} vs ==∗ s ↦*□ vs.
Proof.
  iIntros "H". iPersist "H". done.
Qed.

#[global]
Instance own_slice_update_to_persistent s dq vs :
  UpdateIntoPersistently (s ↦*{dq} vs) (s ↦*□ vs).
Proof. apply _. Qed.

Global Instance own_slice_cap_update_to_persistent s dq :
  UpdateIntoPersistently (own_slice_cap V s dq) (own_slice_cap V s (□)).
Proof. apply _. Qed.

Global Instance own_slice_timeless s dq vs : Timeless (s ↦*{dq} vs).
Proof. unseal. apply _. Qed.

Lemma own_slice_cap_wf s dq :
  own_slice_cap V s dq -∗ ⌜0 ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap)⌝.
Proof.
  unseal. iIntros "[% Hcap]".
  word.
Qed.
(* NOTE: only for backwards compatibility; non-primed version is more precise
about signed length *)
Lemma own_slice_cap_wf' s dq :
  own_slice_cap V s dq -∗ ⌜uint.Z s.(slice.len) ≤ uint.Z s.(slice.cap)⌝.
Proof.
  iIntros "H". iDestruct (own_slice_cap_wf with "H") as "%". word.
Qed.

Lemma own_slice_wf s dq vs :
  s ↦*{dq} vs -∗ ⌜0 ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap)⌝.
Proof.
  unseal.
  iIntros "[? %]". iDestruct (array_len with "[$]") as %Hlen. word.
Qed.

(* NOTE: only for backwards compatibility; non-primed version is more precise
about signed length *)
Lemma own_slice_wf' s dq vs :
  s ↦*{dq} vs -∗ ⌜uint.Z s.(slice.len) ≤ uint.Z s.(slice.cap)⌝.
Proof.
  iIntros "H". iDestruct (own_slice_wf with "H") as "%". word.
Qed.

Lemma own_slice_cap_nil :
  ⊢ own_slice_cap V slice.nil (DfracOwn 1).
Proof.
  rewrite own_slice_cap_unseal /own_slice_cap_def /=.
  iSplit; [ word | ].
  iExists (array.mk _ nil). iApply array_empty; done.
Qed.

Lemma slice_to_full_slice s low high :
  slice.slice s V low high = slice.full_slice s V low high (slice.cap s).
Proof. reflexivity. Qed.

Local Set Default Proof Using "All".

(* introduce a slice.slice for lemmas that require it *)
Lemma slice_slice_trivial s :
  s = slice.slice s V (W64 0) (slice.len s).
Proof.
  destruct s; simpl.
  rewrite /slice.slice /=.
  f_equal; try word.
  rewrite /slice_index_ref /= go.array_index_ref_0 //.
Qed.

(* a variant of [slice_slice_trivial] that's easier to use with [iDestruct] and
more discoverable with Search. *)
Lemma own_slice_trivial_slice s dq (vs: list V) :
  s ↦*{dq} vs ⊣⊢ (slice.slice s V (W64 0) (slice.len s)) ↦*{dq} vs.
Proof.
  rewrite -slice_slice_trivial //.
Qed.

Lemma own_slice_trivial_slice_2 s dq (vs: list V) :
  (slice.slice s V (W64 0) (slice.len s)) ↦*{dq} vs ⊢ s ↦*{dq} vs.
Proof.
  rewrite -own_slice_trivial_slice //.
Qed.

Lemma slice_slice s low high low' high' :
  0 ≤ sint.Z low + sint.Z low' < 2^63 →
  slice.slice (slice.slice s V low high) V low' high' =
    slice.slice s V (word.add low low') (word.add low high').
Proof.
  intros Hoverflow.
  rewrite /slice.slice /=.
  rewrite /slice_index_ref /= -go.array_index_ref_add.
  f_equal; [|word ..]. f_equal. word.
Qed.

Lemma own_slice_elem_acc (i : w64) v s dq vs :
  0 ≤ sint.Z i →
  vs !! (sint.nat i) = Some v →
  s ↦*{dq} vs -∗
  slice_index_ref V (sint.Z i) s ↦{dq} v ∗
  (∀ v', slice_index_ref V (sint.Z i) s ↦{dq} v' -∗
        s ↦*{dq} (<[sint.nat i := v']> vs)).
Proof.
  iIntros (Hpos Hlookup) "Hsl".
  rewrite own_slice_unseal /own_slice_def.
  iDestruct "Hsl" as "[Hsl %]".
  iDestruct (array_acc with "Hsl") as "[? Hsl]"; try eassumption.
  iFrame. iIntros (?) "Hv'".
  iSpecialize ("Hsl" with "[$]"). iFrame. word.
Qed.

(* FIXME: maintain that owned array length doesn't overflow 64 bits? *)
Lemma slice_array l n (a : array.t V n) :
  length (array.arr a) < 2^63 →
  l ↦ a -∗
  (slice.mk l (W64 n) (W64 n)) ↦* (array.arr a).
Proof.
  iIntros "%Hlen H". rewrite own_slice_unseal.
  destruct a. iDestruct (array_len with "H") as %?. subst.
  simpl in *. rewrite /own_slice_def /=.
  replace (sint.Z _) with (Z.of_nat $ length arr) by word.
  iFrame. done.
Qed.

End defns_and_lemmas.

Global Notation "s ↦* dq vs" := (own_slice s dq vs)
                            (at level 20, dq custom dfrac at level 50, format "s  ↦* dq  vs").

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.
Local Set Default Proof Using "All".

Global Instance pure_wp_slice_len t (s : slice.t) :
  PureWp True (#(functions go.len [go.SliceType t]) (#s)) #(slice.len s).
Proof.
  pure_wp_start. rewrite func_unfold. wp_auto_lc 1. by iApply "HΦ".
Qed.

Global Instance pure_wp_slice_cap t (s : slice.t) :
  PureWp True (#(functions go.cap [go.SliceType t]) (#s)) #(slice.cap s).
Proof.
  pure_wp_start. rewrite func_unfold. wp_auto_lc 1. by iApply "HΦ".
Qed.

Global Instance pure_wp_slice_for_range (sl : slice.t) (body : val) t :
  PureWp True (slice.for_range t #sl body)%E
       (let: "i" := alloc go.int #(W64 0) in
        for: (λ: <>, ![go.int] "i" <⟨go.int⟩ FuncResolve go.len [go.SliceType t] (# ()) (# sl)) ;
        (λ: <>, "i" <-[go.int] ![go.int] "i" + # (W64 1)) :=
          λ: <>, body ![go.int] "i" (![t] (IndexRef (go.SliceType t) (# sl, ![go.int] "i"))))%E.
Proof.
  iIntros (?????) "HΦ".
  wp_call_lc "?". by iApply "HΦ".
Qed.

Context [V] `[!ZeroVal V] `[!TypedPointsto (Σ:=Σ) V].

Lemma wp_slice_make3 `[!go.TypeRepr t V] `[!IntoValTyped V t] stk E (len cap : w64) :
  0 ≤ sint.Z len ≤ sint.Z cap →
  {{{ True }}}
    (#(functions go.make3 [go.SliceType t]) #len #cap) @ stk; E
  {{{ (sl : slice.t), RET #sl;
      sl ↦* (replicate (sint.nat len) (zero_val V)) ∗
      own_slice_cap V sl (DfracOwn 1) ∗
      ⌜ sl.(slice.cap) = cap ⌝
  }}}.
Proof.
  intros ?. wp_start.
  wp_if_destruct.
  { exfalso. word. }
  wp_if_destruct.
  { exfalso. word. }
  case_bool_decide; wp_auto.
  { subst.
    wp_apply (wp_ArbitraryInt). iIntros "% _".
    wp_auto. iApply "HΦ".
    assert (len = W64 0) by word; subst.
    simpl. iDestruct (own_slice_empty) as "$"; [simpl; word..|].
    iDestruct (own_slice_cap_none) as "$"; simpl; word. }
  iApply "HΦ".
  rewrite own_slice_unseal/ own_slice_def /=.

  iDestruct (array_split (sint.Z len) with "p") as "[Hsl Hcap]"; first word.
  simpl. rewrite take_replicate.
  iSplitL "Hsl".
  { iSplitL; last word.
    replace (_ `min` _)%nat with (sint.nat len) by word.
    iExactEq "Hsl".
    replace (word.signed (W64 _)) with (sint.Z len) by word.
    done. }
  rewrite own_slice_cap_unseal /own_slice_cap_def /=.
  iSplitL; last done. iSplitR; first word.
  iExists _. rewrite /slice_index_ref.
  replace (sint.Z (sint.Z len)) with (sint.Z len) by word.
  iFrame.
Qed.

Lemma wp_slice_make2 `[!go.TypeRepr t V] `[!IntoValTyped V t] stk E (len : u64) :
  {{{ ⌜0 ≤ sint.Z len⌝ }}}
    #(functions go.make2 [go.SliceType t]) #len @ stk; E
  {{{ sl, RET #sl;
      sl ↦* (replicate (sint.nat len) (zero_val V)) ∗
      own_slice_cap V sl (DfracOwn 1)
  }}}.
Proof.
  wp_start as "%".
  wp_apply wp_slice_make3; first word.
  iIntros (?) "(? & ? & ?)".
  iApply "HΦ". iFrame.
Qed.

Lemma own_slice_split k s dq (vs: list V) low high :
  0 ≤ sint.Z low ≤ sint.Z k ≤ sint.Z high →
  slice.slice s V low high ↦*{dq} vs ⊣⊢
  slice.slice s V low k ↦*{dq} take (sint.nat k - sint.nat low)%nat vs ∗
  slice.slice s V k high ↦*{dq} drop (sint.nat k - sint.nat low)%nat vs.
Proof.
  intros Hle.
  rewrite -{1}(take_drop (sint.nat k - sint.nat low)%nat vs).
  rewrite own_slice_unseal /own_slice_def /=.
  rewrite /slice_index_ref /=. iSplit.
  - iIntros "[H %]".
    iDestruct (array_len with "H") as %Hlen.
    iDestruct (array_split (word.sub k low) with "H") as "[H1 H2]".
    { word. }
    iSplitL "H1".
    + iSplitL; last by len. iExactEq "H1". f_equal. f_equal.
      rewrite take_app_le. 2:{ revert Hlen. len. } rewrite take_take. f_equal. word.
    + iSplitL; last by len. rewrite -go.array_index_ref_add.
      iExactEq "H2".
      replace (word.signed (word.sub high low) - word.signed (word.sub k low)) with
        (word.signed (word.sub high k)) by word. f_equal.
      * f_equal. word.
      * f_equal. rewrite drop_app_ge.
        2:{ revert Hlen. len. }
        rewrite drop_drop. f_equal. revert Hlen. len.
  - iIntros "[[H1 %] [H2 %]]". iSplitL; last by len.
    iDestruct (array_len with "H1") as %Hlen1.
    iDestruct (array_len with "H1") as %Hlen2.
    iApply (array_split (word.sub k low)).
    { word. }
    iSplitL "H1".
    + iExactEq "H1". f_equal. f_equal.
      rewrite take_app_le. 2:{ revert Hlen1 Hlen2. len. } rewrite take_take. f_equal. word.
    + rewrite -go.array_index_ref_add.
      replace (word.signed (word.sub high low) - word.signed (word.sub k low)) with
        (word.signed (word.sub high k)) by word.
      iExactEq "H2". f_equal.
      * f_equal. word.
      * f_equal. rewrite drop_app_ge.
        2:{ revert Hlen1 Hlen2. len. }
        rewrite drop_drop. f_equal. revert Hlen1 Hlen2. len.
Qed.

Lemma own_slice_combine k s dq (vs1 vs2: list V) low high :
  length vs1 = (sint.nat k - sint.nat low)%nat ∧
  0 ≤ sint.Z low ≤ sint.Z k ≤ sint.Z high →
  slice.slice s V low k ↦*{dq} vs1 -∗
  slice.slice s V k high ↦*{dq} vs2 -∗
  slice.slice s V low high ↦*{dq} (vs1 ++ vs2).
Proof.
  iIntros (Hwf) "Hs1 Hs2".
  iApply (own_slice_split k).
  { lia. }
  rewrite -> take_app_le, take_ge by lia.
  rewrite -> drop_app_le, drop_ge, app_nil_l by lia.
  iFrame.
Qed.

Lemma own_slice_split_all k s dq (vs: list V) :
  0 ≤ sint.Z k ≤ sint.Z s.(slice.len) →
  s ↦*{dq} vs ⊣⊢
  slice.slice s V (W64 0) k ↦*{dq} take (sint.nat k) vs ∗
  slice.slice s V k s.(slice.len) ↦*{dq} drop (sint.nat k)%nat vs.
Proof.
  intros Hle.
  rewrite {1}(own_slice_trivial_slice s).
  rewrite -> (own_slice_split k) by word.
  replace (sint.nat (W64 0)) with 0%nat by word.
  replace (sint.nat k - 0)%nat with (sint.nat k) by lia.
  auto.
Qed.

Local Lemma own_slice_cap_same_end s s' dq :
  slice_index_ref V (sint.Z s.(slice.len)) s = slice_index_ref V (sint.Z s'.(slice.len)) s' →
  sint.Z (slice.cap s) - sint.Z (slice.len s) = sint.Z (slice.cap s') - sint.Z (slice.len s') →
  0 ≤ sint.Z (slice.len s) ∧ 0 ≤ sint.Z (slice.len s') →
  own_slice_cap V s dq ⊣⊢ own_slice_cap V s' dq.
Proof.
  intros Hend Hcap Hwf.
  rewrite own_slice_cap_unseal /own_slice_cap_def Hend Hcap.
  iSplit; iIntros "[% H]"; iFrame; word.
Qed.

(* [own_slice_cap] only depends on where the end of the slice is *)
Lemma own_slice_cap_slice_change_first s low low' high dq :
  sint.Z high ≤ sint.Z s.(slice.cap) ∧
  0 ≤ sint.Z low ≤ sint.Z high ∧ 0 ≤ sint.Z low' ≤ sint.Z high →
  own_slice_cap V (slice.slice s V low high) dq ⊢ own_slice_cap V (slice.slice s V low' high) dq.
Proof.
  intros Hbound.
  rewrite own_slice_cap_same_end //.
  { rewrite /slice_index_ref /= /slice_index_ref.
    rewrite -!go.array_index_ref_add. f_equal. word. }
  { simpl in *. word. }
  { simpl in *. word. }
Qed.

Lemma own_slice_cap_slice s low dq :
  0 ≤ sint.Z low ≤ sint.Z (slice.len s) ≤ sint.Z (slice.cap s) →
  own_slice_cap V s dq ⊣⊢ own_slice_cap V (slice.slice s V low s.(slice.len)) dq.
Proof.
  intros Hbound.
  rewrite own_slice_cap_same_end //.
  { rewrite /slice_index_ref /= /slice_index_ref /=. rewrite -!go.array_index_ref_add.
    f_equal. word. }
  { simpl in *; word. }
  { simpl in *; word. }
Qed.

(* Divide ownership of [s ↦* vs] around a slice [slice.slice s V low high].

This is not the only choice; see [own_slice_slice_with_cap] for a variation that uses
capacity. *)
Lemma own_slice_slice (low high : w64) s dq (vs : list V) :
  0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.len) →
  s ↦*{dq} vs
  ⊣⊢
  (slice.slice s V (W64 0) low) ↦*{dq} (take (sint.nat low) vs) ∗
  (slice.slice s V low high) ↦*{dq} (subslice (sint.nat low) (sint.nat high) vs) ∗
  (* after the sliced part *)
  (slice.slice s V high (slice.len s)) ↦*{dq} (drop (sint.nat high) vs).
Proof.
  intros. rewrite /subslice.

  rewrite {1}(slice_slice_trivial (V:=V) s).
  rewrite (own_slice_split low); [|word].
  rewrite (own_slice_split high _ _ _ low); [|word].

  rewrite take_drop_commute drop_drop.
  replace (_ - sint.nat (W64 0))%nat with (sint.nat low)%nat by word.
  by replace (_ + _)%nat with (sint.nat high)%nat by word.
Qed.

Lemma own_slice_slice_absorb_capacity s (vs : list V) (low high : w64) :
  0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.len) →
  slice.slice s V high (slice.len s) ↦* vs ∗
  own_slice_cap V s (DfracOwn 1) ⊢
  own_slice_cap V (slice.slice s V low high) (DfracOwn 1).
Proof.
  iIntros (?) "[Hvs Hcap]".
  iDestruct (own_slice_len with "Hvs") as %Hlen.
  simpl in Hlen.
  iDestruct (own_slice_wf with "Hvs") as %Hwf.
  simpl in Hwf.
  iDestruct (own_slice_cap_wf with "Hcap") as %Hwf'.
  iApply (own_slice_cap_slice_change_first _ (W64 0)).
  { word. }
  rewrite own_slice_cap_unseal /own_slice_cap_def.
  iDestruct "Hcap" as "[_ [%vs' Hvs']]".
  destruct vs' as [vs']. iDestruct (array_len with "Hvs'") as %Hlen'.
  simpl in Hlen'.
  simpl.
  iSplit; [ word | ].
  rewrite /slice.slice /= /slice_index_ref /=. rewrite -!go.array_index_ref_add.
  rewrite !word.sub_0_r Z.add_0_l.
  iExists (array.mk _ (vs ++ vs')).
  iApply (array_split (word.sub (slice.len s) high)).
  { simpl in *. word. }
  simpl.
  rewrite -> take_app_le, take_ge by (move: Hlen Hlen'; word).
  rewrite own_slice_unseal. iDestruct "Hvs" as "[Hvs _]". simpl.
  iFrame "Hvs".
  rewrite -> drop_app_ge, drop_eq_0 by (move: Hlen Hlen'; word).
  rewrite -!go.array_index_ref_add.
  replace (sint.Z s.(slice.cap) - sint.Z high - _)
    with (word.signed (slice.cap s) - word.signed (slice.len s)) by word.
  replace (word.signed high + word.signed (word.sub (slice.len s) high)) with
    (word.signed (slice.len s)) by word.
  iFrame "Hvs'".
Qed.

(* divide ownership of [s ↦* vs ∗ own_slice_cap V s] around a slice [slice_f s t
low high], moving ownership between high and [slice.len s] into the capacity of the
slice *)
(* TODO: could generalize to ⊣⊢. just need to generalize some deps. *)
Lemma own_slice_slice_with_cap (low high : w64) s (vs: list V) :
  0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.len) →
  s ↦* vs ∗ own_slice_cap V s (DfracOwn 1)
  ⊢
  (slice.slice s V (W64 0) low) ↦* (take (sint.nat low) vs) ∗
  (slice.slice s V low high) ↦* (subslice (sint.nat low) (sint.nat high) vs) ∗
  (* after the sliced part + capacity of original slice *)
  own_slice_cap V (slice.slice s V low high) (DfracOwn 1).
Proof.
  iIntros (?) "(Hs & Hcap)".
  rewrite own_slice_slice; [|done].
  iDestruct "Hs" as "(Hs1 & Hs2 & Hs3)".
  iFrame "Hs1 Hs2".
  iDestruct (own_slice_slice_absorb_capacity with "[$Hs3 $Hcap]") as "$".
  { word. }
Qed.

Lemma own_slice_cap_split high s :
  own_slice_cap V s (DfracOwn 1) ∗
  ⌜ 0 ≤ sint.Z high ≤ sint.Z s.(slice.cap)⌝ ⊢
  ∃ (vs' : list V), (slice.slice s V s.(slice.len) high) ↦* vs' ∗
         own_slice_cap V (slice.slice s V s.(slice.len) high) (DfracOwn 1).
Proof.
Admitted.

(* An unusual use case for slicing where in s[low:high] we have len(s) ≤ high. This
   moves elements from the hidden capacity of s into its actual contents. *)
Lemma own_slice_slice_into_capacity (low high : w64) s (vs : list V) :
  s ↦* vs ∗ own_slice_cap V s (DfracOwn 1) ∗
  ⌜ 0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.cap)⌝ ⊢
  ∃ (vs_cap : list V),
    (slice.slice s V (W64 0) low) ↦* (take (sint.nat low) (vs ++ vs_cap)) ∗
    (slice.slice s V low high) ↦* (drop (sint.nat low) (vs ++ vs_cap)) ∗
    own_slice_cap V (slice.slice s V low high) (DfracOwn 1).
Proof.
  iIntros "(Hs & Hcap & %)".
  iDestruct (own_slice_cap_split high with "[$Hcap]") as "H".
  { word. }
  iDestruct "H" as "(% & Hs' & Hcap)".
  iDestruct (own_slice_len with "Hs") as %Hlen.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_cap_wf with "Hcap") as %Hwfcap.
  simpl in *.
  iDestruct (own_slice_cap_slice_change_first _ _ low with "Hcap") as "$".
  { word. }
  iExists vs'.
  destruct (decide (sint.Z low ≤ sint.Z s.(slice.len))).
  - iDestruct (own_slice_split_all low with "Hs") as "[Hs1 Hs2]"; first word.
    rewrite take_app_le; last word. iFrame.
    iDestruct (own_slice_combine with "Hs2 [$]") as "H"; first by len.
    rewrite drop_app_le; last by word. iFrame.
  - iDestruct (own_slice_split low with "Hs'") as "[Hs1 Hs2]"; first word.
    rewrite drop_app_ge; last word.
    replace (length vs) with (sint.nat s.(slice.len)) by word. iFrame.
    iApply (own_slice_split s.(slice.len)); first word.
    rewrite -own_slice_trivial_slice. rewrite take_take.
    rewrite take_app_le; last word. rewrite take_app_ge; last word.
    rewrite (take_ge vs); last word. iFrame.
    iExactEq "Hs1". f_equal. rewrite drop_app_length'; last word.
    f_equal. word.
Qed.

Lemma wp_load_slice_index `[!IntoValTyped V t] s i (vs : list V) dq v :
  0 ≤ i →
  {{{ s ↦*{dq} vs ∗ ⌜ vs !! (Z.to_nat i) = Some v ⌝ }}}
    load t #(slice_index_ref V i s)
  {{{ RET #v; s ↦*{dq} vs }}}.
Proof.
  intros Hpos.
  iIntros "% [Hs %Hlookup] HΦ".
  iDestruct (own_slice_len with "Hs") as %Hlen.
  pose proof (lookup_lt_Some _ _ _ Hlookup) as Hineq.
  iDestruct (own_slice_elem_acc i with "Hs") as "[Hv Hs]"; [ word | eauto | ].
  { replace (sint.Z i) with i by word. done. }
  replace (sint.Z i) with i by word.
  wp_apply (wp_load with "Hv"). iIntros "Hv".
  iApply "HΦ".
  iDestruct ("Hs" with "Hv") as "Hs".
  rewrite -> list_insert_id by auto.
  iFrame.
Qed.

Lemma wp_store_slice_index `[!IntoValTyped V t] s i (vs : list V) (v' : V) :
  {{{ s ↦* vs ∗ ⌜0 ≤ i < Z.of_nat (length vs)⌝ }}}
    store t #(slice_index_ref V i s) #v'
  {{{ RET #(); s ↦* (<[Z.to_nat i := v']> vs) }}}.
Proof.
  iIntros "% [Hs %Hbound] HΦ".
  iDestruct (own_slice_len with "Hs") as %Hlen.
  list_elem vs i as v.
  iDestruct (own_slice_elem_acc i with "Hs") as "[Hv Hs]"; [ word | eauto | ].
  { replace (sint.Z i) with i by word. done. }
  replace (sint.Z i) with i by word.
  wp_apply (wp_store with "Hv"). iIntros "Hv".
  iApply "HΦ".
  iDestruct ("Hs" with "Hv") as "Hs".
  iFrame.
Qed.

(** slice.copy copies as much as possible (the smaller of len(s) and len(s2)) and returns
the number of bytes copied. See https://pkg.go.dev/builtin#copy.

Use [take_ge] and [drop_ge] to simplify the resulting list expression.
 *)
Lemma wp_slice_copy `[!IntoValTyped V t] `[!go.TypeRepr t V] (s: slice.t) (vs: list V) (s2: slice.t) (vs': list V) dq :
  {{{ s ↦* vs ∗ s2 ↦*{dq} vs' }}}
    #(functions go.copy [go.SliceType t]) #s #s2
  {{{ (n: w64), RET #n; ⌜sint.nat n = Nat.min (length vs) (length vs')⌝ ∗
                          s ↦* (take (length vs) vs' ++ drop (length vs') vs) ∗
                          s2 ↦*{dq} vs' }}}.
Proof.
  wp_start as "(Hs1 & Hs2)". wp_auto.
  iDestruct (own_slice_len with "Hs1") as %Hlen1.
  iDestruct (own_slice_len with "Hs2") as %Hlen2.
  iAssert (∃ (i:w64),
      "Hs1" ∷ s ↦* (take (sint.nat i) vs' ++ drop (sint.nat i) vs) ∗
      "Hs2" ∷ s2 ↦*{dq} vs' ∗
      "i" ∷ i_ptr ↦ i ∗
      "%" ∷ ⌜0 ≤ sint.Z i ≤ Z.min (sint.Z s.(slice.len)) (sint.Z s2.(slice.len))⌝
    )%I with "[Hs1 Hs2 i]" as "IH".
  { iFrame. simpl. word. }
  wp_for "IH".
  wp_if_destruct.
  - wp_auto. wp_if_destruct.
    {
      list_elem vs' (sint.Z i) as y.
      rewrite decide_True //.
      wp_auto. rewrite decide_True; last word.
      wp_auto. rewrite decide_True; last word. wp_auto.
      wp_apply (wp_load_slice_index with "[$Hs2]") as "Hs2".
      { word. }
      { eauto. }
      wp_apply (wp_store_slice_index with "[$Hs1]") as "Hs1".
      { len. }
      wp_for_post.
      iFrame.
      replace (sint.nat (word.add i (W64 1))) with
        (S (sint.nat i)) by word.
      iSplit; [ | word ].
      iExactEq "Hs1".
      rewrite /named.
      f_equal.
      (* TODO: automate list simplification for take/drop/app? *)
      rewrite -> insert_take_drop by len.
      rewrite -> take_app_le, -> drop_app_ge by len.
      rewrite take_take drop_drop.
      rewrite -> Nat.min_l by word.
      erewrite take_S_r; eauto.
      rewrite -app_assoc /=.
      rewrite -> length_take_le by word.
      repeat (f_equal; try word).
    }
    rewrite decide_False; last naive_solver. rewrite decide_True //.
    wp_auto.
    iApply "HΦ".
    iSplit; [ word | ].
    iFrame "Hs2".
    rewrite -> !take_ge by word.
    iExactEq "Hs1".
    repeat (f_equal; try word).
  - rewrite decide_False; last naive_solver. rewrite decide_True //.
    wp_auto. iApply "HΦ".
    iSplit; [ word | ].
    iFrame "Hs2".
    rewrite -> !drop_ge, !app_nil_r by word.
    iExactEq "Hs1".
    repeat (f_equal; try word).
Qed.

Lemma wp_slice_clear `[!go.TypeRepr t V] `[!IntoValTyped V t] s (vs : list V) :
  {{{ s ↦* vs }}}
    #(functions go.clear [go.SliceType t]) #s
  {{{ RET #(); s ↦* replicate (length vs) (zero_val V) }}}.
Proof.
  wp_start as "Hs".
  iDestruct (own_slice_len with "Hs") as %Hlen.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_apply wp_slice_make2; first word.
  iIntros (zero_sl) "[? _]". wp_auto.
  wp_apply (wp_slice_copy with "[-HΦ]"); first iFrame.
  iIntros (?) "(%Hlen' & Hsl & _)".
  wp_auto. iApply "HΦ".
  rewrite drop_ge; last len.
  rewrite take_ge; last len. rewrite app_nil_r.
  replace (sint.nat _) with (length vs) by word.
  iFrame.
Qed.

Lemma own_slice_update_to_dfrac dq (s: slice.t) (vs: list V) :
  ✓dq →
  s ↦* vs ⊢ |==> s ↦*{dq} vs.
Proof.
  iIntros (Hvalid) "Hs".
  iMod (dfractional_update_to_dfrac (λ dq, s ↦*{dq} vs) with "Hs") as "$"; auto.
Qed.

Lemma wp__new_cap (l: w64) :
  {{{ True }}}
    slice._new_cap #l
  {{{ (cap: w64), RET #cap; ⌜sint.Z l ≤ sint.Z cap⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call. wp_apply wp_ArbitraryInt.
  iIntros (x) "_".
  wp_pures.
  match goal with
  | |- context[bool_decide ?P] => destruct (bool_decide_reflect P); wp_pures
  end.
  - iApply "HΦ".
    word.
  - iApply "HΦ".
    word.
Qed.

Lemma wp_slice_append `[!go.TypeRepr t V] `[!IntoValTyped V t] (s: slice.t) (vs: list V) (s2: slice.t) (vs': list V) dq :
  {{{ s ↦* vs ∗ own_slice_cap V s (DfracOwn 1) ∗ s2 ↦*{dq} vs' }}}
    #(functions go.append [go.SliceType t]) #s #s2
  {{{ (s' : slice.t), RET #s';
      s' ↦* (vs ++ vs') ∗ own_slice_cap V s' (DfracOwn 1) ∗ s2 ↦*{dq} vs' }}}.
Proof.
  wp_start as "(Hs & Hcap & Hs2)".
  iDestruct (own_slice_len with "Hs") as %Hs.
  iDestruct (own_slice_len with "Hs2") as %Hs2.
  iDestruct (own_slice_wf with "Hs") as %Hwf1.
  iDestruct (own_slice_wf with "Hs2") as %Hwf2.
  wp_apply wp_sum_assume_no_overflow_signed as "%Hoverflow".
  wp_if_destruct.
  - rewrite decide_True; last word. wp_auto.
    rewrite decide_True; last word. wp_auto.
    rewrite slice_slice; last word.
    do 2 ereplace (word.add (W64 0) ?[e]) with ?e by word.
    iDestruct (own_slice_slice_into_capacity
                 s.(slice.len) (word.add s.(slice.len) s2.(slice.len)) with "[$Hs $Hcap]") as
        (vs'') "(Hs & Hs_new & Hcap)"; [ word | ].
    iDestruct (own_slice_len with "Hs_new") as %Hlen.
    simpl in Hlen; autorewrite with len in Hlen.
    wp_apply (wp_slice_copy with "[$Hs_new $Hs2]").
    autorewrite with len.
    rewrite -> !Nat.min_l by word.
    iIntros (n) "(%Hn & Hs_new & Hs2)".
    rewrite -> drop_ge, app_nil_r by len.
    wp_auto.
    iApply "HΦ".
    iFrame "Hs2".
    iSplitL "Hs Hs_new".
    { iDestruct (own_slice_combine s.(slice.len) with "Hs Hs_new") as "Hs_new".
      { len. }
      rewrite -> !take_app_le, !take_ge by word.
      iFrame "Hs_new".
    }
    iApply (own_slice_cap_slice_change_first with "Hcap").
    move: l; word.
  - wp_apply (wp__new_cap) as "%x %Hcap_ge".
    wp_apply wp_slice_make3.
    { word. }
    iIntros (sl) "(Hnew & Hnew_cap & %Hcap)".
    iDestruct (own_slice_wf with "Hnew") as %Hsl_wf.
    iDestruct (own_slice_len with "Hnew") as %Hsl_len.
    autorewrite with len in Hsl_len.
    assert (word.add (slice.len s) (slice.len s2) = slice.len sl) as Hsl_len'.
    { apply word.unsigned_inj.
      move: Hsl_len; word. }
    wp_auto.
    wp_apply (wp_slice_copy with "[$Hnew $Hs]").
    autorewrite with len.
    rewrite -> !Nat.min_r by word.
    iIntros (n') "(%Hn' & Hnew & Hs)".
    rewrite -> take_ge by len.
    rewrite drop_replicate.
    wp_auto. rewrite decide_True; last word.
    iDestruct (own_slice_slice
                 s.(slice.len) (word.add s.(slice.len) s2.(slice.len)) with "Hnew") as
        "(Hnew1 & Hnew2 & _)".
    { word. }
    wp_auto.
    wp_apply (wp_slice_copy with "[$Hnew2 $Hs2]").
    autorewrite with len.
    rewrite -> !Nat.min_r by word.
    iIntros (n'') "(%Hn'' & Hnew2 & Hs2)".
    rewrite -> !drop_ge, app_nil_r by len.
    rewrite -> !take_app_le, !take_ge by word.
    wp_auto.
    iApply "HΦ".
    iFrame "Hs2".
    iSplitL "Hnew1 Hnew2".
    {
      iDestruct (own_slice_combine with "Hnew1 Hnew2") as "Hnew".
      { len. }
      iDestruct (own_slice_len with "Hnew") as %Hlen.
      simpl in Hlen.
      autorewrite with len in Hlen.
      iExactEq "Hnew".
      f_equal.
      rewrite {2}(slice_slice_trivial sl (V:=V)).
      f_equal.
      word.
    }
    iFrame.
Qed.

End wps.

Notation "s ↦* dq vs" := (own_slice s dq vs)
                            (at level 20, dq custom dfrac at level 50,
                              vs constr at next level, format "s  ↦* dq  vs").
