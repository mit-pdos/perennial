From Perennial.Helpers Require Import List ListLen Fractional NamedProps.
From iris.algebra Require Import dfrac.
From Perennial.iris_lib Require Import dfractional.
From Perennial.goose_lang Require Import ipersist.
From New.golang.defn Require Export slice.
From New.golang.theory Require Export loop array primitive.
From Perennial Require Import base.

Set Default Proof Using "Type".

#[local]
Transparent slice.for_range slice.literal.

Module slice.
Section def.
Context `{GoContext}.
Definition slice (sl : slice.t) (et : go.type) (n1 n2 : u64) : slice.t :=
  slice.mk (slice_index_ref et (sint.Z n1) sl) (word.sub n2 n1) (word.sub sl.(slice.cap) n1).

Definition full_slice (sl : slice.t) (et : go.type) (n1 n2 n3 : u64) : slice.t :=
  slice.mk (slice_index_ref et (sint.Z n1) sl) (word.sub n2 n1) (word.sub n3 n1).
End def.
End slice.

Section defns_and_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {core_sem : go.CoreSemantics} {slice_sem : go.SliceSemantics}.

Definition own_slice_def {V} t `{!IntoVal V} `{!TypedPointsto V} `{!IntoValTyped V t}
  (s : slice.t) (dq : dfrac) (vs : list V)
  : iProp Σ :=
  (s.(slice.ptr) ↦{dq} (array.mk t (sint.Z s.(slice.len)) vs)) ∗
  ⌜ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap) ⌝.
Program Definition own_slice := sealed @own_slice_def.
Definition own_slice_unseal : own_slice = _ := seal_eq _.

Global Arguments own_slice {_} (t) {_ _ _} (s dq vs).

Notation "s ↦[ t ]* dq vs" := (own_slice t s dq vs)
                            (at level 20, dq custom dfrac at level 50, format "s  ↦[ t ]* dq  vs").

Context `{!IntoVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.
Implicit Type (vs : list V).

Definition own_slice_cap_def (s : slice.t) (dq : dfrac) : iProp Σ :=
  ⌜ 0 ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap) ⌝ ∗
(* Two notes about this definition. First, it is written using [own_slice] to
get some reuse, though an intermediate array points-to would be more useful
here. Second, the capacity has arbitrary values, which is often desirable,
but there are some niche cases where code could be aware of the contents of the
capacity (for example, when sub-slicing from a larger slice) - actually taking
advantage of that seems questionable though. *)
  ∃ (vs: list V), own_slice t
                    (slice.mk
                       (slice_index_ref t (sint.Z s.(slice.len)) s)
                       (word.sub s.(slice.cap) s.(slice.len))
                       (word.sub s.(slice.cap) s.(slice.len))) dq vs.
Program Definition own_slice_cap := sealed @own_slice_cap_def.
Definition own_slice_cap_unseal : own_slice_cap = _ := seal_eq _.

Ltac unseal := rewrite ?own_slice_unseal /own_slice_def
                 ?own_slice_cap_unseal /own_slice_cap_def.

Lemma own_slice_nil dq :
  ⊢ slice.nil ↦[t]*{dq} ([] : list V).
Proof.
  unseal. simpl. iDestruct array_empty as "$". done.
Qed.

Lemma own_slice_empty dq s :
  sint.Z s.(slice.len) = 0 ->
  0 ≤ sint.Z s.(slice.cap) ->
  ⊢ s ↦[t]*{dq} ([] : list V).
Proof.
  unseal. intros Hsz Hcap. destruct s. simpl in *.
  rewrite Hsz. iDestruct array_empty as "$". word.
Qed.

Lemma own_slice_cap_none s :
  s.(slice.len) = s.(slice.cap) →
  0 ≤ sint.Z s.(slice.len) →
  ⊢ own_slice_cap s (DfracOwn 1).
Proof.
  destruct s; simpl; intros -> Hlen. rewrite own_slice_cap_unseal /own_slice_cap_def /=.
  iSplit; [ word | ].
  iExists [].
  iApply own_slice_empty.
  - simpl. word.
  - simpl. word.
Qed.

Lemma own_slice_len s dq vs :
  s ↦[t]*{dq} vs -∗ ⌜length vs = sint.nat s.(slice.len) ∧ 0 ≤ sint.Z s.(slice.len)⌝.
Proof.
  unseal. iIntros "(H&%)". iDestruct (array_len with "H") as %?. word.
Qed.

Lemma own_slice_agree s dq1 dq2 vs1 vs2 :
  s ↦[t]*{dq1} vs1 -∗
  s ↦[t]*{dq2} vs2 -∗
  ⌜vs1 = vs2⌝.
Proof.
  unseal. iIntros "[Hs1 %] [Hs2 %]".
  iCombine "Hs1 Hs2" gives %[=->]. done.
Qed.

Global Instance own_slice_persistent s vs : Persistent (s ↦[t]*□ vs).
Proof. unseal. apply _. Qed.

#[global]
Instance own_slice_dfractional s vs :
  DFractional (λ dq, s ↦[t]*{dq} vs).
Proof. unseal; apply _. Qed.

#[global]
Instance own_slice_as_dfractional s dq vs :
  AsDFractional (s ↦[t]*{dq} vs) (λ dq, s ↦[t]*{dq} vs) dq.
Proof. auto. Qed.

#[global]
Instance own_slice_as_fractional s q vs :
  fractional.AsFractional (s ↦[t]*{#q} vs) (λ q, s ↦[t]*{#q} vs) q.
Proof.
  split; auto.
  change (λ q0 : Qp, s ↦[t]*{#q0} vs) with (λ q : Qp, (λ dq, s ↦[t]*{dq} vs) (DfracOwn q)).
  apply fractional_of_dfractional.
  apply _.
Qed.

Global Instance own_slice_combine_sep_gives s dq1 dq2 vs1 vs2 :
  CombineSepGives (s ↦[t]*{dq1} vs1) (s ↦[t]*{dq2} vs2) (⌜ vs1 = vs2 ⌝).
Proof.
  rewrite /CombineSepGives.
  iIntros "[H0 H1]".
  iDestruct (own_slice_agree with "H0 H1") as %->.
  naive_solver.
Qed.

Global Instance own_slice_combine_sep_as s dq1 dq2 vs1 vs2 :
  CombineSepAs (s ↦[t]*{dq1} vs1) (s ↦[t]*{dq2} vs2) (s ↦[t]*{dq1 ⋅ dq2} vs1) | 60.
Proof.
  rewrite /CombineSepAs.
  iIntros "[H0 H1]".
  iDestruct (own_slice_agree with "H0 H1") as %->.
  by iCombine "H0 H1" as "?".
Qed.

Global Instance own_slice_cap_persistent s : Persistent (own_slice_cap s (□)).
Proof. unseal; apply _. Qed.

#[global]
Instance own_slice_cap_dfractional s :
  DFractional (λ dq, own_slice_cap s dq).
Proof.
  unseal.
  apply dfractional_sep; [apply _|].
  split.
  - intros ??. iSplit.
    + iIntros "[% [H0 H1]]". iFrame.
    + iIntros "[[% H0] [% H1]]".
      iDestruct (own_slice_agree with "H0 H1") as %->.
      iCombine "H0 H1" as "H".
      iFrame.
  - apply _.
  - iIntros (?) "[% H]". iPersist "H". by iFrame "#".
Qed.

#[global]
Instance own_slice_cap_as_dfractional s dq :
  AsDFractional (own_slice_cap s dq) (λ dq, own_slice_cap s dq) dq.
Proof. auto. Qed.

Lemma own_slice_persist s dq vs:
  s ↦[t]*{dq} vs ==∗ s ↦[t]*□ vs.
Proof.
  iIntros "H". iPersist "H". done.
Qed.

#[global]
Instance own_slice_update_to_persistent s dq vs :
  UpdateIntoPersistently (s ↦[t]*{dq} vs) (s ↦[t]*□ vs).
Proof. apply _. Qed.

Global Instance own_slice_cap_update_to_persistent s dq :
  UpdateIntoPersistently (own_slice_cap s dq) (own_slice_cap s (□)).
Proof. apply _. Qed.

Global Instance own_slice_timeless s dq vs : Timeless (s ↦[t]*{dq} vs).
Proof. unseal. apply _. Qed.

Lemma own_slice_cap_wf s dq :
  own_slice_cap s dq -∗ ⌜0 ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap)⌝.
Proof.
  unseal. iIntros "[% Hcap]".
  word.
Qed.
(* NOTE: only for backwards compatibility; non-primed version is more precise
about signed length *)
Lemma own_slice_cap_wf' s dq :
  own_slice_cap s dq -∗ ⌜uint.Z s.(slice.len) ≤ uint.Z s.(slice.cap)⌝.
Proof.
  iIntros "H". iDestruct (own_slice_cap_wf with "H") as "%". word.
Qed.

Lemma own_slice_wf s dq vs :
  s ↦[t]*{dq} vs -∗ ⌜0 ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap)⌝.
Proof.
  unseal.
  iIntros "[? %]". iDestruct (array_len with "[$]") as %Hlen. word.
Qed.

(* NOTE: only for backwards compatibility; non-primed version is more precise
about signed length *)
Lemma own_slice_wf' s dq vs :
  s ↦[t]*{dq} vs -∗ ⌜uint.Z s.(slice.len) ≤ uint.Z s.(slice.cap)⌝.
Proof.
  iIntros "H". iDestruct (own_slice_wf with "H") as "%". word.
Qed.

Lemma own_slice_cap_nil :
  ⊢ own_slice_cap slice.nil (DfracOwn 1).
Proof.
  rewrite own_slice_cap_unseal /own_slice_cap_def /=.
  iSplit; [ word | ].
  iExists nil. iApply own_slice_empty; done.
Qed.

Lemma slice_to_full_slice s n m :
  slice.slice s t n m = slice.full_slice s t n m (slice.cap s).
Proof. reflexivity. Qed.

Local Set Default Proof Using "Type core_sem slice_sem".

(* introduce a slice.slice for lemmas that require it *)
Lemma slice_slice_trivial s :
  s = slice.slice s t (W64 0) (slice.len s).
Proof.
  destruct s; simpl.
  rewrite /slice.slice /=.
  f_equal; try word.
  rewrite /slice_index_ref /= go.array_index_ref_0 //.
Qed.

(* a variant of [slice_slice_trivial] that's easier to use with [iDestruct] and
more discoverable with Search. *)
Lemma own_slice_trivial_slice s dq (vs: list V) :
  s ↦[t]*{dq} vs ⊣⊢ (slice.slice s t (W64 0) (slice.len s)) ↦[t]*{dq} vs.
Proof.
  rewrite -slice_slice_trivial //.
Qed.

Lemma own_slice_trivial_slice_2 s dq (vs: list V) :
  own_slice t (slice.slice s t (W64 0) (slice.len s)) dq vs ⊢ own_slice t s dq vs.
Proof.
  rewrite -own_slice_trivial_slice //.
Qed.

Lemma slice_slice s n m n' m' :
  0 ≤ sint.Z n + sint.Z n' < 2^63 →
  0 ≤ sint.Z m' ≤ sint.Z m - sint.Z n →
  slice.slice (slice.slice s t n m) t n' m' =
    slice.slice s t (word.add n n') (word.add n m').
Proof.
  intros Hoverflow Hle.
  rewrite /slice.slice /=.
  rewrite /slice_index_ref /= -go.array_index_ref_add.
  f_equal; [|word ..]. f_equal. word.
Qed.

Lemma own_slice_elem_acc (i : w64) v s dq vs :
  0 ≤ sint.Z i →
  vs !! (sint.nat i) = Some v →
  s ↦[t]*{dq} vs -∗
  slice_index_ref t (sint.Z i) s ↦{dq} v ∗
  (∀ v', slice_index_ref t (sint.Z i) s ↦{dq} v' -∗
        s ↦[t]*{dq} (<[sint.nat i := v']> vs)).
Proof.
  iIntros (Hpos Hlookup) "Hsl".
  rewrite own_slice_unseal /own_slice_def.
  iDestruct "Hsl" as "[Hsl %]".
  iDestruct (array_acc with "Hsl") as "[? Hsl]"; try eassumption.
  iFrame. iIntros (?) "Hv'".
  iSpecialize ("Hsl" with "[$]"). iFrame. word.
Qed.

End defns_and_lemmas.

Global Notation "s ↦[ t ]* dq vs" := (own_slice t s dq vs)
                            (at level 20, dq custom dfrac at level 50, format "s  ↦[ t ]* dq  vs").

Global Arguments own_slice_cap {_ _ _ _ _ _ _ _ _ _} (t) {_} s dq.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}
  {core_sem : go.CoreSemantics} {slice_sem : go.SliceSemantics}.
Local Set Default Proof Using "Type core_sem slice_sem".

Local Notation st e := [go.TypeLit $ go.SliceType e].
Lemma wp_slice_len stk E et (s : slice.t) (Φ : val -> iProp Σ) :
    Φ #(s.(slice.len)) -∗
    WP #(functions len (st et)) #s @ stk; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ". wp_pures. rewrite go.len_slice. wp_pures. iApply "HΦ".
Qed.

Lemma wp_slice_cap stk E et (s : slice.t) (Φ : val -> iProp Σ) :
  Φ #(s.(slice.cap)) -∗
  WP #(functions cap (st et)) (#s) @ stk; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ". wp_pures. rewrite go.cap_slice. wp_pures. iApply "HΦ".
Qed.

Context `{!IntoVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.

Lemma wp_slice_make3 stk E (len cap : w64) :
  0 ≤ sint.Z len ≤ sint.Z cap →
  {{{ True }}}
    #(functions make3 (st t)) #len #cap @ stk; E
  {{{ sl, RET #sl;
      sl ↦[t]* (replicate (sint.nat len) (zero_val V)) ∗
      own_slice_cap t sl (DfracOwn 1) ∗
      ⌜ sl.(slice.cap) = cap ⌝
  }}}.
Proof.
  iIntros (? Φ) "_ HΦ".
  rewrite go.make3_slice. wp_pures.
  wp_pures.
  wp_if_destruct.
  { exfalso. word. }
  wp_if_destruct.
  { exfalso. word. }
  case_bool_decide; wp_pures.
  {
    subst.
    wp_apply (wp_ArbitraryInt). iIntros "%".
    wp_pures. iApply "HΦ".
    assert (len = W64 0) by word; subst.
    simpl.
    iDestruct (own_slice_empty) as "$".
    { simpl. word. }
    { simpl. word. }
    iDestruct (own_slice_cap_none) as "$"; simpl; word.
  }
  wp_apply wp_alloc.
  { instantiate (3:=(array.t t V (word.signed cap))). apply _. } (* FIXME: tc search *)
  iIntros (ptr) "Hsl". wp_pures. iApply "HΦ".
  rewrite own_slice_unseal/ own_slice_def /=.
  (* TODO: split array lemma. *)

  iFrame.
  wp_bind (AllocN _ _).
  rewrite [in #cap]to_val_unseal.
  iApply (wp_allocN_seq with "[//]").
  { word. }
  iNext.
  iIntros (?) "Hp".
  replace (uint.nat cap) with (sint.nat cap) by word.
  wp_pures.
  replace (LitV l) with (#l); last by rewrite to_val_unseal //.
  replace (LitV cap) with (#cap); last by rewrite to_val_unseal //.
  rewrite slice_val_fold. iApply "HΦ".
  rewrite own_slice_unseal own_slice_cap_unseal.
  assert (sint.nat cap = sint.nat len + (sint.nat cap - sint.nat len))%nat as Hsplit by word.
  rewrite Hsplit seq_app.
  iDestruct "Hp" as "[Hsl Hcap]".
  iSplitL "Hsl".
  {
    iSplitL.
    2:{ iPureIntro. simpl. rewrite length_replicate. word. }
    erewrite <- (seq_replicate_fmap O).
    iApply (big_sepL_fmap with "[Hsl]").
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros.
    rewrite /pointsto_vals typed_pointsto_unseal /typed_pointsto_def /=.
    rewrite default_val_eq_zero_val.
    erewrite has_go_type_len.
    2:{ apply zero_val_has_go_type. }
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros. iFrame.
    apply lookup_seq in H0 as [? ?].
    subst. iFrame.
  }
  {
    iSplitL.
    2:{ iPureIntro. done. }
    rewrite /own_slice_cap_def /=.
    iSplitR; first iPureIntro.
    { word. }
    erewrite has_go_type_len.
    2:{ apply to_val_has_go_type. }
    iExists (replicate (sint.nat cap - sint.nat len)%nat (default_val V)).
    rewrite own_slice_unseal /own_slice_def /=.
    iSplit; [ | len ].
    rewrite big_sepL_replicate_seq.
    rewrite (big_sepL_offset _ (sint.nat len)).
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros.
    rewrite /pointsto_vals typed_pointsto_unseal /typed_pointsto_def /=.
    rewrite default_val_eq_zero_val.
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros (???) "Hp". iExactEq "Hp".
    rewrite !loc_add_assoc.
    do 2 f_equal.
    (* TODO: word limitation *)
    rewrite !Nat2Z.inj_add.
    nat_cleanup.
    word.
  }
Qed.

Lemma wp_slice_make2 stk E (len : u64) :
  {{{ ⌜0 ≤ sint.Z len⌝ }}}
    slice.make2 t #len @ stk; E
  {{{ sl, RET #sl;
      sl ↦[t]* (replicate (sint.nat len) (default_val V)) ∗
      own_slice_cap V sl (DfracOwn 1)
  }}}.
Proof.
  iIntros (Φ) "% HΦ".
  wp_call.
  wp_apply wp_slice_make3.
  { word. }
  iIntros (?) "(? & ? & ?)".
  iApply "HΦ". iFrame.
Qed.

Global Instance pure_slice_ptr (s : slice.t) :
  PureWp True (slice.ptr (#s)) #(slice.ptr s).
Proof.
  rewrite to_val_unseal.
  iIntros (?????) "HΦ".
  wp_call_lc "?". rewrite to_val_unseal.
  by iApply "HΦ".
Qed.

Global Instance pure_slice_len (s : slice.t) :
  PureWp True (slice.len (#s)) #(slice.len s).
Proof.
  rewrite to_val_unseal.
  iIntros (?????) "HΦ".
  wp_call_lc "?". rewrite to_val_unseal. by iApply "HΦ".
Qed.

Global Instance pure_slice_cap (s : slice.t) :
  PureWp True (slice.cap (#s)) #(slice.cap s).
Proof.
  rewrite to_val_unseal.
  iIntros (?????) "HΦ".
  wp_call_lc "?". rewrite to_val_unseal. by iApply "HΦ".
Qed.

Global Instance pure_elem_ref s (i : w64) :
  PureWp (0 ≤ sint.Z i < sint.Z s.(slice.len)) (slice.elem_ref t #s #i)
    #(slice.elem_ref_f s t i).
Proof.
  iIntros (?????) "HΦ".
  wp_call_lc "?".
  rewrite bool_decide_true; last word.
  wp_pures. replace (uint.Z i) with (sint.Z i) by word.
  by iApply "HΦ".
Qed.

Global Instance pure_slice_slice s (n m : w64) :
  PureWp (0 ≤ sint.Z n ≤ sint.Z m ≤ sint.Z (slice.cap s) ∧
          0 ≤ sint.Z (slice.len s) ≤ sint.Z (slice.cap s)) (slice.slice t #s #n #m)
    #(slice.slice_f s t n m).
Proof.
  iIntros (?????) "HΦ".
  wp_call_lc "?".
  rewrite bool_decide_true; last word.
  wp_pures.
  rewrite bool_decide_true; last word.
  wp_pures.
  rewrite bool_decide_true; last word.
  wp_pures.
  iDestruct ("HΦ" with "[$]") as "HΦ".
  replace (uint.Z n) with (sint.Z n) by word.
  wp_pures.
  iExactEq "HΦ".
  repeat f_equal.
  rewrite !to_val_unseal /=.
  rewrite !to_val_unseal /=.
  reflexivity.
Qed.

Global Instance pure_full_slice s (n m c : w64) :
  PureWp (0 ≤ sint.Z n ≤ sint.Z m ≤ sint.Z c ∧
          0 ≤ sint.Z c ≤ sint.Z (slice.cap s)) (slice.full_slice t #s #n #m #c)
    #(slice.full_slice_f s t n m c).
Proof.
  iIntros (?????) "HΦ".
  wp_call_lc "?".
  rewrite bool_decide_true; last word.
  wp_pures.
  rewrite bool_decide_true; last word.
  wp_pures.
  rewrite bool_decide_true; last word.
  wp_pures.
  rewrite bool_decide_true; last word.
  wp_pures.
  iDestruct ("HΦ" with "[$]") as "HΦ".
  replace (uint.Z n) with (sint.Z n) by word.
  iExactEq "HΦ".
  repeat f_equal.
  rewrite /slice.full_slice_f.
  rewrite !to_val_unseal /=.
  rewrite !to_val_unseal /=.
  reflexivity.
Qed.

(** WP version of PureWp for discoverability and use with wp_apply.

TODO: if PureWp instances had their pure side conditions dispatched with [word]
this lemma would be pretty much unnecessary.
*)
Lemma wp_slice_slice_pure s (n m: w64) :
  {{{ ⌜0 ≤ sint.Z n ≤ sint.Z m ≤ sint.Z s.(slice.cap) ∧
        0 ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap)⌝ }}}
    slice.slice t #s #n #m
  {{{ RET #(slice.slice_f s t n m); True }}}.
Proof.
  wp_start as "%".
  wp_pure.
  wp_pures.
  iApply "HΦ". done.
Qed.

Lemma own_slice_split k s dq (vs: list V) n m :
  0 ≤ sint.Z n ≤ sint.Z k ≤ sint.Z m →
  slice.slice_f s t n m ↦[t]*{dq} vs ⊣⊢
  slice.slice_f s t n k ↦[t]*{dq} take (sint.nat k - sint.nat n)%nat vs ∗
  slice.slice_f s t k m ↦[t]*{dq} drop (sint.nat k - sint.nat n)%nat vs.
Proof.
  intros Hle.
  rewrite -{1}(take_drop (sint.nat k - sint.nat n)%nat vs).
  rewrite own_slice_unseal /own_slice_def /=.
  setoid_rewrite loc_add_assoc; setoid_rewrite <- Z.mul_add_distr_l.
  rewrite big_sepL_app.
  len.
  replace (sint.nat (word.sub m n)) with (sint.nat m - sint.nat n)%nat by word.
  iSplit.
  - iIntros "((Hvs1 & Hvs2) & %Hwf)".
    iSplitL "Hvs1".
    + iSplit; [ | iPureIntro; move: Hwf; word ].
      iFrame "Hvs1".
    + iSplit; [ | iPureIntro; move: Hwf; word ].
      iExactEq "Hvs2".
      apply big_opL_ext => i v Hget.
      do 3 f_equal.
      word.
  - iIntros "((Hvs1 & %Hwf1) & (Hvs2 & %Hwf2))".
    iFrame "Hvs1".
    iSplit; [ | iPureIntro; move: Hwf1 Hwf2; word ].
    iExactEq "Hvs2".
    apply big_opL_ext  => i v Hget.
    do 3 f_equal.
    move: Hwf1 Hwf2; word.
Qed.

Lemma own_slice_combine k s dq (vs1 vs2: list V) n m :
  length vs1 = (sint.nat k - sint.nat n)%nat ∧
  0 ≤ sint.Z n ≤ sint.Z k ≤ sint.Z m →
  slice.slice_f s t n k ↦[t]*{dq} vs1 -∗
  slice.slice_f s t k m ↦[t]*{dq} vs2 -∗
  slice.slice_f s t n m ↦[t]*{dq} (vs1 ++ vs2).
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
  s ↦[t]*{dq} vs ⊣⊢
  slice.slice_f s t (W64 0) k ↦[t]*{dq} take (sint.nat k) vs ∗
  slice.slice_f s t k s.(slice.len) ↦[t]*{dq} drop (sint.nat k)%nat vs.
Proof.
  intros Hle.
  rewrite {1}(own_slice_trivial_slice_f s).
  rewrite -> (own_slice_split k) by word.
  replace (sint.nat (W64 0)) with 0%nat by word.
  replace (sint.nat k - 0)%nat with (sint.nat k) by lia.
  auto.
Qed.

(* [own_slice_cap] only depends on where the end of the slice is *)
Lemma own_slice_cap_same_end s s' dq :
  slice.ptr s +ₗ[t] sint.Z (slice.len s) = slice.ptr s' +ₗ[t] sint.Z (slice.len s') →
  sint.Z (slice.cap s) - sint.Z (slice.len s) = sint.Z (slice.cap s') - sint.Z (slice.len s') →
  0 ≤ sint.Z (slice.len s) ∧ 0 ≤ sint.Z (slice.len s') →
  own_slice_cap V s dq ⊣⊢ own_slice_cap V s' dq.
Proof.
  intros Hend Hcap Hwf.
  rewrite own_slice_cap_unseal /own_slice_cap_def.
  assert (word.sub (slice.cap s) (slice.len s) = word.sub (slice.cap s') (slice.len s'))
    as Hdiff by word.
  rewrite -Hdiff.
  rewrite -!Hend.
  f_equiv.
  iPureIntro; word.
Qed.

Lemma own_slice_cap_slice_f_change_first s n n' m dq :
  sint.Z m ≤ sint.Z s.(slice.cap) ∧
  0 ≤ sint.Z n ≤ sint.Z m ∧ 0≤ sint.Z n' ≤ sint.Z m →
  own_slice_cap V (slice.slice_f s t n m) dq ⊣⊢ own_slice_cap V (slice.slice_f s t n' m) dq.
Proof.
  intros Hbound.
  apply own_slice_cap_same_end; simpl.
  - rewrite !loc_add_assoc -!Z.mul_add_distr_l.
    repeat (f_equal; try word).
  - word.
  - word.
Qed.

Lemma own_slice_cap_slice_f s n dq :
  0 ≤ sint.Z n ≤ sint.Z (slice.len s) ≤ sint.Z (slice.cap s) →
  own_slice_cap V s dq ⊣⊢ own_slice_cap V (slice.slice_f s t n s.(slice.len)) dq.
Proof.
  intros Hwf.
  apply own_slice_cap_same_end; simpl.
  - rewrite !loc_add_assoc -!Z.mul_add_distr_l.
    repeat (f_equal; try word).
  - word.
  - word.
Qed.

(* Divide ownership of [s ↦[t]* vs] around a slice [slice.slice_f s t n m].

This is not the only choice; see [own_slice_f_cap] for a variation that uses
capacity. *)
Lemma own_slice_f (n m: w64) s dq (vs: list V) :
  0 ≤ sint.Z n ≤ sint.Z m ≤ sint.Z s.(slice.len) →
  s ↦[t]*{dq} vs
  ⊣⊢
  (slice.slice_f s t (W64 0) n) ↦[t]*{dq} (take (sint.nat n) vs) ∗
  (slice.slice_f s t n m) ↦[t]*{dq} (subslice (sint.nat n) (sint.nat m) vs) ∗
  (* after the sliced part *)
  (slice.slice_f s t m (slice.len s)) ↦[t]*{dq} (drop (sint.nat m) vs).
Proof.
  intros. rewrite /subslice.

  rewrite {1}(slice_slice_trivial (t:=t) s).
  rewrite (own_slice_split n); [|word].
  rewrite (own_slice_split m _ _ _ n); [|word].

  rewrite take_drop_commute drop_drop.
  replace (_ - sint.nat (W64 0))%nat with (sint.nat n)%nat by word.
  by replace (_ + _)%nat with (sint.nat m)%nat by word.
Qed.

Lemma own_slice_slice_absorb_capacity s (vs: list V) (n m: w64) :
  0 ≤ sint.Z n ≤ sint.Z m ≤ sint.Z s.(slice.len) →
  slice.slice_f s t m (slice.len s) ↦[t]* vs ∗
  own_slice_cap V s (DfracOwn 1) ⊢
  own_slice_cap V (slice.slice_f s t n m) (DfracOwn 1).
Proof.
  iIntros (?) "[Hvs Hcap]".
  iDestruct (own_slice_len with "Hvs") as %Hlen.
  simpl in Hlen.
  iDestruct (own_slice_wf with "Hvs") as %Hwf.
  simpl in Hwf.
  iDestruct (own_slice_cap_wf with "Hcap") as %Hwf'.
  iApply (own_slice_cap_slice_f_change_first _ (W64 0)).
  { word. }
  rewrite own_slice_cap_unseal /own_slice_cap_def.
  iDestruct "Hcap" as "[_ [%vs' Hvs']]".
  iDestruct (own_slice_len with "Hvs'") as %Hlen'.
  simpl in Hlen'.
  simpl.
  iSplit; [ word | ].
  rewrite Z.mul_0_r loc_add_0 !word.sub_0_r.
  iExists (vs ++ vs').
  iApply (own_slice_split s.(slice.len)).
  { word. }
  rewrite -> take_app_le, take_ge by (move: Hlen Hlen'; word).
  iFrame "Hvs".
  rewrite -> drop_app_ge, drop_eq_0 by (move: Hlen Hlen'; word).
  iFrame "Hvs'".
Qed.

(* divide ownership of [s ↦[t]* vs ∗ own_slice_cap V s] around a slice [slice_f s t
n m], moving ownership between m and [slice.len s] into the capacity of the
slice *)
(* TODO: could generalize to ⊣⊢. just need to generalize some deps. *)
Lemma own_slice_f_cap (n m: w64) s (vs: list V) :
  0 ≤ sint.Z n ≤ sint.Z m ≤ sint.Z s.(slice.len) →
  s ↦[t]* vs ∗ own_slice_cap V s (DfracOwn 1)
  ⊢
  (slice.slice_f s t (W64 0) n) ↦[t]* (take (sint.nat n) vs) ∗
  (slice.slice_f s t n m) ↦[t]* (subslice (sint.nat n) (sint.nat m) vs) ∗
  (* after the sliced part + capacity of original slice *)
  own_slice_cap V (slice.slice_f s t n m) (DfracOwn 1).
Proof.
  iIntros (?) "(Hs & Hcap)".
  rewrite own_slice_f; [|done].
  iDestruct "Hs" as "(Hs1 & Hs2 & Hs3)".
  iFrame "Hs1 Hs2".
  iDestruct (own_slice_slice_absorb_capacity with "[$Hs3 $Hcap]") as "$".
  { word. }
Qed.

(** wp variant of [own_slice_f]

TODO: try to avoid using this and use the canonical pure WP for slice.slice (plus directly using [own_slice_f])
instead
*)
Lemma wp_slice_slice s dq (vs: list V) (n m : w64) :
  {{{ s ↦[t]*{dq} vs ∗ ⌜0 ≤ sint.Z n ≤ sint.Z m ≤ sint.Z s.(slice.len)⌝ }}}
    slice.slice t #s #n #m
  {{{ RET #(slice.slice_f s t n m);
      (* before the sliced part *)
      (slice.slice_f s t (W64 0) n) ↦[t]*{dq} (take (sint.nat n) vs) ∗
      (slice.slice_f s t n m) ↦[t]*{dq} (subslice (sint.nat n) (sint.nat m) vs) ∗
      (* after the sliced part *)
      (slice.slice_f s t m (slice.len s)) ↦[t]*{dq} (drop (sint.nat m) vs)
  }}}.
Proof.
  wp_start as "[Hs %]".
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_apply wp_slice_slice_pure.
  { word. }
  iApply "HΦ".
  rewrite -own_slice_f; [|word].
  iFrame.
Qed.

(** wp variant of [own_slice_f_cap]

TODO: try to avoid using this and use the canonical pure WP for slice.slice (plus directly using [own_slice_f])
instead
*)
Lemma wp_slice_slice_with_cap s (vs: list V) (n m : w64) :
  {{{ s ↦[t]* vs ∗ own_slice_cap V s (DfracOwn 1) ∗
            ⌜0 ≤ sint.Z n ≤ sint.Z m ≤ sint.Z s.(slice.len)⌝ }}}
    slice.slice t #s #n #m
  {{{ RET #(slice.slice_f s t n m);
      (* before the sliced part *)
      (slice.slice_f s t (W64 0) n) ↦[t]* (take (sint.nat n) vs) ∗
      (slice.slice_f s t n m) ↦[t]* (subslice (sint.nat n) (sint.nat m) vs) ∗
      (* after the sliced part becomes part of this capacity *)
      own_slice_cap V (slice.slice_f s t n m) (DfracOwn 1)
  }}}.
Proof.
  wp_start as "(Hs & Hcap & %)".
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_apply wp_slice_slice_pure.
  { word. }
  iApply "HΦ".
  iDestruct (own_slice_f_cap n m with "[$Hs $Hcap]") as "(Hs_pre & Hs & Hs_cap)".
  { word. }
  iFrame.
Qed.

(* An unusual use case for slicing where in s[n:m] we have len(s) ≤ m. This
moves elements from the hidden capacity of s into its actual contents. *)
Lemma own_slice_slice_into_capacity (n m: w64) s (vs: list V) :
  s ↦[t]* vs ∗ own_slice_cap V s (DfracOwn 1) ∗
      ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z s.(slice.len) ≤ sint.Z m ≤ sint.Z s.(slice.cap)⌝ ⊢
  ∃ (vs': list V),
  (slice.slice_f s t (W64 0) n) ↦[t]* (take (sint.nat n) vs) ∗
      (slice.slice_f s t n m) ↦[t]* (drop (sint.nat n) vs ++ vs') ∗
      own_slice_cap V (slice.slice_f s t n m) (DfracOwn 1).
Proof.
  iIntros "(Hs & Hcap & %)".
  iDestruct (own_slice_len with "Hs") as %Hlen.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  rewrite own_slice_cap_unseal /own_slice_cap_def /=.
  iDestruct "Hcap" as "[_ [%vs' Hcap]]".
  iDestruct (own_slice_len with "Hcap") as %Hlen'.
  simpl in Hlen'.
  iExists (take (sint.nat m - sint.nat s.(slice.len))%nat vs').
  iDestruct (own_slice_split_all n with "Hs") as "[Hs1 Hs2]";
    [ word | ].
  iDestruct (own_slice_split_all (word.sub m s.(slice.len)) with "Hcap") as "[Hvs' Hcap']".
  { simpl. word. }
  simpl.
  iSplitL "Hs1".
  { iFrame. }
  iSplitL "Hs2 Hvs'".
  {
    iApply (own_slice_split s.(slice.len)).
    { word. }
    iSplitL "Hs2".
    { iExactEq "Hs2".
      f_equal.
      rewrite -> take_app_ge; len.
      match goal with
      | |- context[_ ++ take ?n _] => replace n with 0%nat by word
      end.
      rewrite take_0 app_nil_r //.
    }

    rewrite -> drop_app_le by len.
    rewrite drop_drop.
    rewrite -> drop_ge by len.
    rewrite app_nil_l.
    replace (sint.nat (word.sub m (slice.len s))) with
      (sint.nat m - sint.nat (slice.len s))%nat by word.
    set (k := (sint.nat m - sint.nat (slice.len s))%nat).

    rewrite own_slice_unseal /own_slice_def /=.
    iDestruct "Hvs'" as "[Hvs' %Hwf']".
    iSplit.
    2: {
      iPureIntro; move: Hwf' Hlen'; len.
    }
    change (sint.Z (W64 0)) with 0.
    rewrite Z.mul_0_r.
    iExactEq "Hvs'".
    rewrite loc_add_0 //.
  }
  iSplit.
  { iPureIntro; move: Hlen'; len. }
  iExists (drop (sint.nat (word.sub m (slice.len s))) vs').
  rewrite /slice.slice_f /=.
  rewrite !loc_add_assoc -!Z.mul_add_distr_l.
  iExactEq "Hcap'".
  repeat (f_equal; try word).

  (* FIXME: automate these simplifications that were helpful to see the proof *)
  (*
  replace (word.sub (word.sub (slice.cap s) (slice.len s)) (word.sub m (slice.len s))) with
    (word.sub s.(slice.cap) m) by word.
  replace (word.sub (word.sub (slice.cap s) n) (word.sub m n))
            with (word.sub s.(slice.cap) m) by word.
  replace (uint.Z n + uint.Z (word.sub m n)) with
    (uint.Z m) by word.
  replace (uint.Z (slice.len s) + uint.Z (word.sub m (slice.len s))) with
    (uint.Z m) by word.

  iDestruct (own_slice_split (word.sub s.(slice.cap) s.(slice.len)) with "Hcap'") as "[_ Hcap]".
  { word. }
  rewrite /slice.slice_f /=.
  rewrite !loc_add_assoc -!Z.mul_add_distr_l.
  replace (uint.nat (word.sub m s.(slice.len))) with (uint.nat m - uint.nat s.(slice.len))%nat by word.
  replace (uint.nat (word.sub s.(slice.cap) s.(slice.len))) with (uint.nat s.(slice.cap) - uint.nat s.(slice.len))%nat by word.
  replace (uint.Z n + uint.Z (word.sub m n)) with (uint.Z m) by word.
  rewrite drop_drop.
  replace (uint.nat m - uint.nat (slice.len s) +
     (uint.nat (slice.cap s) -
        uint.nat (slice.len s) -
        (uint.nat m -
           uint.nat (slice.len s))))%nat with
    (uint.nat s.(slice.cap) - uint.nat s.(slice.len))%nat by word.
  iExists (drop (uint.nat (slice.cap s) -
                   uint.nat (slice.len s))
             vs').
*)
Qed.

Lemma wp_slice_for_range {stk E} sl dq (vs : list V) (body : val) Φ :
  sl ↦[t]*{dq} vs -∗
  (fold_right (λ v P (i : w64),
                 WP body #i #v @ stk ; E {{ v', ⌜ v' = execute_val ⌝ ∗ P (word.add i 1) }})
    (λ (_ : w64), sl ↦[t]*{dq} vs -∗ Φ (execute_val))
    vs) (W64 0) -∗
  WP slice.for_range t #sl body @ stk ; E {{ Φ }}
.
Proof.
  iIntros "Hsl HΦ".
  wp_call.
  wp_alloc j_ptr as "Hi".
  wp_pures.
  iAssert (
      ∃ (j : u64),
        "Hi" ∷ j_ptr ↦ j ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z j ≤ Z.of_nat (length vs)⌝ ∗
        "Hiters" ∷ (fold_right _ _ (drop (sint.nat j) vs)) j
    )%I with "[Hi HΦ]" as "Hinv".
  { iExists (W64 0). iFrame. word. }
  wp_for "Hinv".
  iDestruct (own_slice_len with "Hsl") as %Hlen.
  wp_if_destruct.
  - (* Case: execute loop body *)
    wp_auto.
    pose proof (list_lookup_lt vs (sint.nat j) ltac:(word)) as [w Hlookup].
    iDestruct (own_slice_elem_acc j with "[$]") as "[Helem Hown]"; [word|done|].
    wp_pure.
    { word. }
    wp_load.
    iDestruct ("Hown" with "Helem") as "Hown".
    rewrite list_insert_id; [|assumption].
    wp_load.
    erewrite drop_S; last eassumption.
    simpl.
    wp_apply (wp_wand with "Hiters").
    iIntros (?) "[-> Hiters]".
    wp_for_post.
    iFrame.
    replace (sint.nat (word.add _ $ W64 1)) with (S $ sint.nat j) by word.
    iFrame.
    word.
  - simpl.  (* Case: done with loop body. *)
    rewrite drop_ge.
    2:{ word. }
    iApply "Hiters". by iFrame.
Qed.

Lemma wp_slice_literal {stk E} (l : list V) :
  {{{ True }}}
    slice.literal t #l @ stk ; E
  {{{ sl, RET #sl; sl ↦[t]* l }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_list_Length.
  iIntros "%Hlen".
  (* TODO: list.Length to give <2^63, not <2^64 *)
  assert (length l = sint.nat (W64 (length l))) as Hlen' by admit.
  wp_pures.
  wp_apply wp_slice_make2.
  { word. }
  iIntros (?) "[Hsl Hcap]".
  wp_pures.
  wp_bind (ref _)%E.
  iApply (wp_alloc_untyped with "[//]").
  { instantiate (1:=#l). rewrite to_val_unseal /=. by destruct l. }
  iNext. iIntros (l_ptr) "Hl".
  wp_pures.
  wp_alloc i_ptr as "Hi".
  wp_pures.
  iDestruct (own_slice_len with "Hsl") as %Hsz.
  rewrite length_replicate in Hsz.
  iAssert (∃ (i : w64),
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ Z.of_nat (length l) ⌝ ∗
      "Hi" ∷ i_ptr ↦ i ∗
      "Hl" ∷ heap_pointsto l_ptr (DfracOwn 1) (# (drop (sint.nat i) l)) ∗
      "Hsl" ∷ sl ↦[t]* (take (sint.nat i) l ++ replicate (length l - sint.nat i) (default_val V))
    )%I
    with "[Hi Hl Hsl]" as "Hloop".
  {
    iExists _; iFrame.
    autorewrite with list in *.
    simpl.
    rewrite drop_0 take_0 Nat.sub_0_r -Hlen' /=.
    iFrame. word.
  }
  wp_for.
  iNamed "Hloop".
  wp_pures.
  wp_load.
  wp_pures.
  autorewrite with list in *.
  case_bool_decide as Hlt.
  {
    simpl.
    rewrite decide_True //.
    wp_pures.
    wp_bind (! _)%E.
    iApply (wp_load with "[$]").
    iNext. iIntros "Hl".
    wp_pures.
    destruct (drop _ _) eqn:Hdrop.
    { exfalso. apply (f_equal length) in Hdrop.
      rewrite length_drop /= in Hdrop.
      autorewrite with list in *. word. }
    simpl.
    wp_pures.
    wp_apply (wp_store with "[$]").
    iIntros "Hl".
    wp_pures.
    wp_load.
    autorewrite with list in *.
    wp_pure.
    { word. }
    iDestruct (own_slice_elem_acc i with "Hsl") as "[Hptsto Hsl]".
    { word. }
    {
      rewrite lookup_app_r.
      2:{ rewrite length_take. word. }
      rewrite length_take.
      rewrite lookup_replicate.
      split; first done.
      word.
    }
    wp_store.
    wp_pures.
    wp_for_post.
    iFrame.
    replace (sint.nat (word.add i (W64 1))) with (sint.nat i + 1)%nat by word.
    rewrite -drop_drop.
    rewrite Hdrop.
    rewrite /= drop_0.
    iFrame.
    iSpecialize ("Hsl" with "Hptsto").
    iSplitR.
    { word. }
    iApply to_named.
    iExactEq "Hsl".
    repeat f_equal.
    rewrite insert_app_r_alt.
    2:{ rewrite length_take. word. }
    rewrite take_more.
    2:{ word. }
    rewrite -app_assoc.
    f_equal.
    rewrite insert_replicate_lt.
    2:{ rewrite length_take. word. }
    rewrite length_take.
    rewrite Nat.min_l.
    2:{ word. }
    rewrite Nat.sub_diag Hdrop.
    simpl.
    f_equal.
    f_equal.
    word.
  }
  {
    simpl.
    rewrite decide_False; last naive_solver.
    rewrite decide_True; last naive_solver.
    wp_pures.
    iApply "HΦ".
    replace (sint.Z i) with (sint.Z (length l)).
    2:{ word. }
    iExactEq "Hsl".
    rewrite take_ge; [ | word ].
    rewrite replicate_eq_0; [ | word ].
    rewrite app_nil_r //.
  }
  Fail idtac.
Admitted.

(* TODO: not sound, need 0 ≤ sint i *)
Global Instance points_to_access_slice_elem_ref s (i : w64) (vs : list V) dq v
  {Hlookup : TCSimpl (vs !! (sint.nat i)) (Some v)}
  : PointsToAccess (slice.elem_ref_f s t i) v dq (s ↦[t]*{dq} vs)
      (λ v', s ↦[t]*{dq} <[(sint.nat i) := v']> vs).
Proof.
(*
  constructor.
  - inv Hlookup.
    iIntros "Hs".
    iDestruct (own_slice_elem_acc with "Hs") as "Hs"; eauto.
  - inv Hlookup.
    rewrite list_insert_id //.
Qed.
*)
Admitted.

Lemma wp_load_slice_elem s (i: w64) (vs: list V) dq v :
  0 ≤ sint.Z i →
  {{{ s ↦[t]*{dq} vs ∗ ⌜vs !! (sint.nat i) = Some v⌝ }}}
    ![t] #(slice.elem_ref_f s t i)
  {{{ RET #v; s ↦[t]*{dq} vs }}}.
Proof.
  intros Hpos.
  wp_start_folded as "[Hs %Hlookup]".
  iDestruct (own_slice_elem_acc with "Hs") as "[Hv Hs]"; [ | eauto | ].
  { word. }
  (* NOTE: cannot use [wp_load] because we need to strip a later *)
  wp_apply (wp_mem_load with "Hv"). iIntros "Hv".
  iApply "HΦ".
  iDestruct ("Hs" with "Hv") as "Hs".
  rewrite -> list_insert_id by auto.
  iFrame.
Qed.

Lemma wp_store_slice_elem s (i: w64) (vs: list V) (v': V) :
  {{{ s ↦[t]* vs ∗ ⌜0 ≤ sint.Z i < Z.of_nat (length vs)⌝ }}}
    #(slice.elem_ref_f s t i) <-[t] #v'
  {{{ RET #(); s ↦[t]* (<[sint.nat i := v']> vs) }}}.
Proof.
  wp_start_folded as "[Hs %bound]".
  list_elem vs (sint.Z i) as v.
  iDestruct (own_slice_elem_acc with "Hs") as "[Hv Hs]"; [ | eauto | ].
  { word. }
  (* NOTE: cannot use [wp_store] because we need to strip a later *)
  wp_apply (wp_mem_store with "Hv"). iIntros "Hv".
  iApply "HΦ".
  iDestruct ("Hs" with "Hv") as "Hs".
  iFrame.
Qed.

(** slice.copy copies as much as possible (the smaller of len(s) and len(s2)) and returns
the number of bytes copied. See https://pkg.go.dev/builtin#copy.

Use [take_ge] and [drop_ge] to simplify the resulting list expression.
 *)
Lemma wp_slice_copy (s: slice.t) (vs: list V) (s2: slice.t) (vs': list V) dq :
  {{{ s ↦[t]* vs ∗ s2 ↦[t]*{dq} vs' }}}
    slice.copy t #s #s2
  {{{ (n: w64), RET #n; ⌜sint.nat n = Nat.min (length vs) (length vs')⌝ ∗
                          s ↦[t]* (take (length vs) vs' ++ drop (length vs') vs) ∗
                          s2 ↦[t]*{dq} vs' }}}.
Proof.
  wp_start as "(Hs1 & Hs2)".
  wp_call. wp_auto.
  iDestruct (own_slice_len with "Hs1") as %Hlen1.
  iDestruct (own_slice_len with "Hs2") as %Hlen2.
  iAssert (∃ (i:w64),
      "Hs1" ∷ s ↦[t]* (take (sint.nat i) vs' ++ drop (sint.nat i) vs) ∗
      "Hs2" ∷ s2 ↦[t]*{dq} vs' ∗
      "i" ∷ i_ptr ↦ i ∗
      "%" ∷ ⌜0 ≤ sint.Z i ≤ Z.min (sint.Z s.(slice.len)) (sint.Z s2.(slice.len))⌝
    )%I with "[Hs1 Hs2 i]" as "IH".
  { iFrame. simpl. word. }
  wp_for "IH".
  wp_if_destruct; try wp_auto.
  - wp_if_destruct; try wp_auto.
    {
      list_elem vs' (sint.Z i) as y.
      wp_pure; [ word | ].
      wp_apply (wp_load_slice_elem with "[$Hs2]") as "Hs2".
      { word. }
      { eauto. }
      wp_pure; [ word | ].
      wp_apply (wp_store_slice_elem with "[$Hs1]") as "Hs1".
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
      repeat (f_equal; try word). }
    rewrite decide_False.
    2: { inv 1. }
    rewrite decide_True //.
    wp_auto.
    assert (i = slice.len s2) by word; subst i.
    iApply "HΦ".
    iSplit; [ word | ].
    iFrame "Hs2".
    rewrite -> !take_ge by word.
    iExactEq "Hs1".
    repeat (f_equal; try word).
  - rewrite decide_False.
    2: { inv 1. }
    rewrite decide_True //.
    wp_auto.
    assert (i = slice.len s) by word; subst i.
    iApply "HΦ".
    iSplit; [ word | ].
    iFrame "Hs2".
    rewrite -> !drop_ge, !app_nil_r by word.
    iExactEq "Hs1".
    repeat (f_equal; try word).
Qed.

Lemma own_slice_update_to_dfrac dq (s: slice.t) (vs: list V) :
  ✓dq →
  s ↦[t]* vs ⊢ |==> s ↦[t]*{dq} vs.
Proof.
  iIntros (Hvalid) "Hs".
  iMod (dfractional_update_to_dfrac (λ dq, s ↦[t]*{dq} vs) with "Hs") as "$"; auto.
Qed.

Lemma own_slice_zero_size (s: slice.t) (vs: list V) dq :
  go_type_size t = 0%nat →
  length vs = uint.nat (slice.len s) →
  0 ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap) →
  ⊢ s ↦[t]*{dq} vs.
Proof using IntoValTyped0.
  intros Hz Hlen Hwf.
  rewrite own_slice_unseal /own_slice_def.
  iSplit; [ | word ].
  iApply big_sepL_intro.
  iIntros "!> % % %Hget".
  iApply (typed_pointsto_zero_size (t:=t)); auto.
Qed.

Lemma own_slice_cap_zero_size (s: slice.t) :
  go_type_size t = 0%nat →
  0 ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap) →
  ⊢ own_slice_cap V s (DfracOwn 1).
Proof using IntoValTyped0.
  intros Hz Hwf.
  rewrite own_slice_cap_unseal /own_slice_cap_def.
  iSplit; [ word | ].
  iExists (replicate (sint.nat (word.sub (slice.cap s) (slice.len s))) (default_val V)).
  iApply own_slice_zero_size; simpl; auto; len.
Qed.

Lemma wp__new_cap (l: w64) :
  {{{ True }}}
    slice._new_cap #l
  {{{ (cap: w64), RET #cap; ⌜sint.Z l ≤ sint.Z cap⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call. wp_apply wp_ArbitraryInt.
  iIntros (x).
  wp_pures.
  match goal with
  | |- context[bool_decide ?P] => destruct (bool_decide_reflect P); wp_pures
  end.
  - iApply "HΦ".
    word.
  - iApply "HΦ".
    word.
Qed.

Lemma wp_slice_append (s: slice.t) (vs: list V) (s2: slice.t) (vs': list V) dq :
  {{{ s ↦[t]* vs ∗ own_slice_cap V s (DfracOwn 1) ∗ s2 ↦[t]*{dq} vs' }}}
    slice.append t #s #s2
  {{{ (s': slice.t), RET #s';
      s' ↦[t]* (vs ++ vs') ∗ own_slice_cap V s' (DfracOwn 1) ∗ s2 ↦[t]*{dq} vs' }}}.
Proof.
  iIntros (Φ) "(Hs & Hcap & Hs2) HΦ".
  wp_call.
  iDestruct (own_slice_len with "Hs") as %Hs.
  iDestruct (own_slice_len with "Hs2") as %Hs2.
  iDestruct (own_slice_wf with "Hs") as %Hwf1.
  iDestruct (own_slice_wf with "Hs2") as %Hwf2.
  wp_apply wp_sum_assume_no_overflow_signed as "%Hoverflow".
  wp_if_destruct; try wp_auto.
  - wp_pure.
    { word. }
    match goal with
    | |- context[slice.slice_f _ _ ?n ?m] =>
        iDestruct (own_slice_slice_into_capacity n m with "[$Hs $Hcap]") as
        (vs'') "(Hs & Hs_new & Hcap)"; [ word | ]
    end.
    wp_auto.
    rewrite take_0 drop_0.
    iClear "Hs". (* empty *)
    iDestruct (own_slice_len with "Hs_new") as %Hlen.
    simpl in Hlen; autorewrite with len in Hlen.
    assert (length vs'' = sint.nat s2.(slice.len)) by (move: Hlen; word).
    wp_apply (wp_slice_slice_with_cap with "[$Hs_new $Hcap]").
    { iPureIntro; simpl; by len. }
    iIntros "(Hs_new1 & Hs_new2 & Hs_new_cap)".
    rewrite -> !slice_f_slice_f by word.
    rewrite !word.add_0_l.
    wp_apply (wp_slice_copy with "[$Hs_new2 $Hs2]").
    autorewrite with len.
    rewrite -> !Nat.min_l by word.
    iIntros (n) "(%Hn & Hs_new2 & Hs2)".
    rewrite -> drop_ge, app_nil_r by len.
    wp_pures.
    iApply "HΦ".
    iFrame "Hs2".
    iSplitL "Hs_new1 Hs_new2".
    { iDestruct (own_slice_combine s.(slice.len) with "Hs_new1 Hs_new2") as "Hs_new".
      { len. }
      rewrite -> !take_app_le, !take_ge by word.
      iFrame "Hs_new".
    }
    iApply (own_slice_cap_slice_f_change_first with "Hs_new_cap").
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
    wp_pures.
    wp_apply (wp_slice_copy with "[$Hnew $Hs]").
    autorewrite with len.
    rewrite -> !Nat.min_r by word.
    iIntros (n') "(%Hn' & Hnew & Hs)".
    rewrite -> take_ge by len.
    rewrite drop_replicate.
    wp_pures.
    wp_apply (wp_slice_slice_with_cap with "[$Hnew $Hnew_cap]").
    { len. }
    iIntros "(Hnew1 & Hnew2 & Hnew_cap)".
    wp_apply (wp_slice_copy with "[$Hnew2 $Hs2]").
    autorewrite with len.
    rewrite -> !Nat.min_r by word.
    iIntros (n'') "(%Hn'' & Hnew2 & Hs2)".
    rewrite -> !drop_ge, app_nil_r by len.
    rewrite -> !take_app_le, !take_ge by word.
    wp_pures.
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
      rewrite {2}(slice_slice_trivial sl (t:=t)).
      f_equal.
      word.
    }
    iEval (rewrite (slice_slice_trivial sl (t:=t))).
    rewrite Hsl_len'.
    iApply (own_slice_cap_slice_f_change_first with "Hnew_cap").
    word.
Qed.

End wps.

Notation "s ↦[t]* dq vs" := (own_slice s dq vs)
                            (at level 20, dq custom dfrac at level 50,
                              vs constr at next level, format "s  ↦[t]* dq  vs").
