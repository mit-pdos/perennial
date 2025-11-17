From New.golang.defn Require Export slice.
From New.golang.theory Require Export array loop.

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
  {core_sem : go.CoreSemantics}
  {pre_sem : go.PredeclaredSemantics}
  {array_sem : go.ArraySemantics}
  {slice_sem : go.SliceSemantics}.

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
  (* Want to make this definition depend on [IntoValTyped], so it can be used a
  typeclass for looking up V given t. At some point, we could introduce a
  separate typeclass just for doing that. *)
  let _ := wp_alloc (E:=⊤) (s:=NotStuck) (t:=t) (λ _, True)%I in
  ⌜ 0 ≤ sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap) ⌝ ∗
(* A notes about this definition. The capacity has arbitrary values, which is
often desirable, but there are some niche cases where code could be aware of the
contents of the capacity (for example, when sub-slicing from a larger slice) -
actually taking advantage of that seems questionable though. *)
  ∃ (a : array.t t V $ (sint.Z s.(slice.cap) - sint.Z s.(slice.len))),
    (slice_index_ref t (sint.Z s.(slice.len)) s) ↦{dq} a.
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
  rewrite Hsz.
  iDestruct array_empty as "$". word.
Qed.

Lemma own_slice_cap_none s :
  s.(slice.len) = s.(slice.cap) →
  0 ≤ sint.Z s.(slice.len) →
  ⊢ own_slice_cap s (DfracOwn 1).
Proof.
  destruct s; simpl; intros Hcap Hlen. rewrite own_slice_cap_unseal /own_slice_cap_def /=.
  iSplit; [ word | ].
  iExists (array.mk _ _ []). rewrite /slice_index_ref /=.
  subst.
  replace (_ - _) with 0 by word.
  iDestruct (array_empty (array_index_ref t _ ptr) (DfracOwn 1)) as "H".
  iExactEq "H".  f_equal.
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
      iCombine "H0 H1" gives %[=->].
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
  iExists (array.mk _ _ nil). iApply array_empty; done.
Qed.

Lemma slice_to_full_slice s low high :
  slice.slice s t low high = slice.full_slice s t low high (slice.cap s).
Proof. reflexivity. Qed.

Local Set Default Proof Using "Type core_sem pre_sem array_sem slice_sem".

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

Lemma slice_slice s low high low' high' :
  0 ≤ sint.Z low + sint.Z low' < 2^63 →
  0 ≤ sint.Z high' ≤ sint.Z high - sint.Z low →
  slice.slice (slice.slice s t low high) t low' high' =
    slice.slice s t (word.add low low') (word.add low high').
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
  {core_sem : go.CoreSemantics}
  {pre_sem : go.PredeclaredSemantics}
  {array_sem : go.ArraySemantics}
  {slice_sem : go.SliceSemantics}.
Local Set Default Proof Using "Type core_sem pre_sem array_sem slice_sem".

Local Notation st e := [go.TypeLit $ go.SliceType e].
Lemma wp_slice_len stk E et (s : slice.t) (Φ : val -> iProp Σ) :
    Φ #(s.(slice.len)) -∗
    WP #(functions go.len (st et)) #s @ stk; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ". wp_pures. rewrite go.len_slice. wp_pures. iApply "HΦ".
Qed.

Lemma wp_slice_cap stk E et (s : slice.t) (Φ : val -> iProp Σ) :
  Φ #(s.(slice.cap)) -∗
  WP #(functions go.cap (st et)) (#s) @ stk; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ". wp_pures. rewrite go.cap_slice. wp_pures. iApply "HΦ".
Qed.

Context `{!IntoVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.

Lemma wp_slice_make3 stk E (len cap : w64) :
  0 ≤ sint.Z len ≤ sint.Z cap →
  {{{ True }}}
    #(functions go.make3 (st t)) #len #cap @ stk; E
  {{{ (sl : slice.t), RET #sl;
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
  { subst.
    wp_apply (wp_ArbitraryInt). iIntros "% _".
    wp_pures. iApply "HΦ".
    assert (len = W64 0) by word; subst.
    simpl. iDestruct (own_slice_empty) as "$"; [simpl; word..|].
    iDestruct (own_slice_cap_none) as "$"; simpl; word. }
  wp_apply wp_alloc.
  iIntros (ptr) "Hsl". wp_pures. iApply "HΦ".
  rewrite own_slice_unseal/ own_slice_def /=.

  iDestruct (array_split (sint.Z len) with "Hsl") as "[Hsl Hcap]"; first word.
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

Lemma wp_slice_make2 stk E (len : u64) :
  {{{ ⌜0 ≤ sint.Z len⌝ }}}
    #(functions go.make2 (st t)) #len @ stk; E
  {{{ sl, RET #sl;
      sl ↦[t]* (replicate (sint.nat len) (zero_val V)) ∗
      own_slice_cap t sl (DfracOwn 1)
  }}}.
Proof.
  iIntros (Φ) "% HΦ".
  rewrite go.make2_slice. wp_pures.
  wp_apply wp_slice_make3.
  { word. }
  iIntros (?) "(? & ? & ?)".
  iApply "HΦ". iFrame.
Qed.

Global Instance pure_slice_len (s : slice.t) :
  PureWp True (#(functions go.len (st t)) (#s)) #(slice.len s).
Proof.
  iIntros (?????) "HΦ". rewrite go.len_slice. wp_pure_lc "Hlc". wp_pures. by iApply "HΦ".
Qed.

Global Instance pure_slice_cap (s : slice.t) :
  PureWp True (#(functions go.cap (st t)) (#s)) #(slice.cap s).
Proof.
  iIntros (?????) "HΦ". rewrite go.cap_slice. wp_pure_lc "Hlc". wp_pures. by iApply "HΦ".
Qed.

Global Instance wp_slice_index_ref s (i : w64) :
  PureWp (0 ≤ sint.Z i < sint.Z s.(slice.len)) (IndexRef (go.SliceType t) (#s, #i)%V)
    #(slice_index_ref t (sint.Z i) s).
Proof.
  iIntros (?????) "HΦ". wp_pure_lc "Hlc". rewrite go.index_ref_slice //.
  by iApply "HΦ".
Qed.

(* FIXME: full slice expression vs simple slice expr. *)
Global Instance pure_slice_slice s (low high : w64) :
  PureWp (0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z (slice.cap s))
    (Slice (go.SliceType t) (#s, (#low, #high))%V)
    #(slice.slice s t low high).
Proof.
  iIntros "% * % % HΦ"; iApply wp_GoInstruction;
  [ intros; repeat econstructor | ].
  iNext; iIntros "* %Hstep"; inv Hstep; inv Hpure.
  eapply inj in H3, H4; try tc_solve. subst.
  rewrite decide_True //.
  iIntros "? $ !>". by iApply "HΦ".
Qed.

Global Instance pure_full_slice s (low high c : w64) :
  PureWp (0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z c ∧ sint.Z c ≤ sint.Z (slice.cap s))
    (FullSlice (go.SliceType t) (#s, (#low, #high, #c))%V)
    #(slice.full_slice s t low high c).
Proof.
  iIntros "% * % % HΦ"; iApply wp_GoInstruction;
  [ intros; repeat econstructor | ].
  iNext; iIntros "* %Hstep"; inv Hstep; inv Hpure.
  eapply inj in H3, H4, H5; try tc_solve. subst.
  rewrite decide_True //.
  iIntros "? $ !>". by iApply "HΦ".
Qed.

(** WP version of PureWp for discoverability and use with wp_apply.

TODO: if PureWp instances had their pure side conditions dispatched with [word]
this lemma would be pretty much unnecessary.
*)
Lemma wp_slice_slice_pure s (low high: w64) :
  {{{ ⌜ 0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.cap) ⌝ }}}
    Slice (go.SliceType t) (#s, (#low, #high))%V
  {{{ RET #(slice.slice s t low high); True }}}.
Proof.
  iIntros "% % HΦ".
  wp_pure. wp_pures.
  iApply "HΦ". done.
Qed.

Lemma own_slice_split k s dq (vs: list V) low high :
  0 ≤ sint.Z low ≤ sint.Z k ≤ sint.Z high →
  slice.slice s t low high ↦[t]*{dq} vs ⊣⊢
  slice.slice s t low k ↦[t]*{dq} take (sint.nat k - sint.nat low)%nat vs ∗
  slice.slice s t k high ↦[t]*{dq} drop (sint.nat k - sint.nat low)%nat vs.
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
  slice.slice s t low k ↦[t]*{dq} vs1 -∗
  slice.slice s t k high ↦[t]*{dq} vs2 -∗
  slice.slice s t low high ↦[t]*{dq} (vs1 ++ vs2).
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
  slice.slice s t (W64 0) k ↦[t]*{dq} take (sint.nat k) vs ∗
  slice.slice s t k s.(slice.len) ↦[t]*{dq} drop (sint.nat k)%nat vs.
Proof.
  intros Hle.
  rewrite {1}(own_slice_trivial_slice s).
  rewrite -> (own_slice_split k) by word.
  replace (sint.nat (W64 0)) with 0%nat by word.
  replace (sint.nat k - 0)%nat with (sint.nat k) by lia.
  auto.
Qed.

Local Lemma own_slice_cap_same_end s s' dq :
  slice_index_ref t (sint.Z s.(slice.len)) s = slice_index_ref t (sint.Z s'.(slice.len)) s' →
  sint.Z (slice.cap s) - sint.Z (slice.len s) = sint.Z (slice.cap s') - sint.Z (slice.len s') →
  0 ≤ sint.Z (slice.len s) ∧ 0 ≤ sint.Z (slice.len s') →
  own_slice_cap t s dq ⊣⊢ own_slice_cap t s' dq.
Proof.
  intros Hend Hcap Hwf.
  rewrite own_slice_cap_unseal /own_slice_cap_def Hend Hcap.
  iSplit; iIntros "[% H]"; iFrame; word.
Qed.

(* [own_slice_cap] only depends on where the end of the slice is *)
Lemma own_slice_cap_slice_change_first s low low' high dq :
  sint.Z high ≤ sint.Z s.(slice.cap) ∧
  0 ≤ sint.Z low ≤ sint.Z high ∧ 0 ≤ sint.Z low' ≤ sint.Z high →
  own_slice_cap t (slice.slice s t low high) dq ⊢ own_slice_cap t (slice.slice s t low' high) dq.
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
  own_slice_cap t s dq ⊣⊢ own_slice_cap t (slice.slice s t low s.(slice.len)) dq.
Proof.
  intros Hbound.
  rewrite own_slice_cap_same_end //.
  { rewrite /slice_index_ref /= /slice_index_ref /=. rewrite -!go.array_index_ref_add.
    f_equal. word. }
  { simpl in *; word. }
  { simpl in *; word. }
Qed.

(* Divide ownership of [s ↦[t]* vs] around a slice [slice.slice s t low high].

This is not the only choice; see [own_slice_slice_with_cap] for a variation that uses
capacity. *)
Lemma own_slice_slice (low high : w64) s dq (vs : list V) :
  0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.len) →
  s ↦[t]*{dq} vs
  ⊣⊢
  (slice.slice s t (W64 0) low) ↦[t]*{dq} (take (sint.nat low) vs) ∗
  (slice.slice s t low high) ↦[t]*{dq} (subslice (sint.nat low) (sint.nat high) vs) ∗
  (* after the sliced part *)
  (slice.slice s t high (slice.len s)) ↦[t]*{dq} (drop (sint.nat high) vs).
Proof.
  intros. rewrite /subslice.

  rewrite {1}(slice_slice_trivial (t:=t) s).
  rewrite (own_slice_split low); [|word].
  rewrite (own_slice_split high _ _ _ low); [|word].

  rewrite take_drop_commute drop_drop.
  replace (_ - sint.nat (W64 0))%nat with (sint.nat low)%nat by word.
  by replace (_ + _)%nat with (sint.nat high)%nat by word.
Qed.

Lemma own_slice_slice_absorb_capacity s (vs : list V) (low high : w64) :
  0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.len) →
  slice.slice s t high (slice.len s) ↦[t]* vs ∗
  own_slice_cap t s (DfracOwn 1) ⊢
  own_slice_cap t (slice.slice s t low high) (DfracOwn 1).
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
  iExists (array.mk _ _ (vs ++ vs')).
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

(* divide ownership of [s ↦[t]* vs ∗ own_slice_cap t s] around a slice [slice_f s t
low high], moving ownership between high and [slice.len s] into the capacity of the
slice *)
(* TODO: could generalize to ⊣⊢. just need to generalize some deps. *)
Lemma own_slice_slice_with_cap (low high : w64) s (vs: list V) :
  0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.len) →
  s ↦[t]* vs ∗ own_slice_cap t s (DfracOwn 1)
  ⊢
  (slice.slice s t (W64 0) low) ↦[t]* (take (sint.nat low) vs) ∗
  (slice.slice s t low high) ↦[t]* (subslice (sint.nat low) (sint.nat high) vs) ∗
  (* after the sliced part + capacity of original slice *)
  own_slice_cap t (slice.slice s t low high) (DfracOwn 1).
Proof.
  iIntros (?) "(Hs & Hcap)".
  rewrite own_slice_slice; [|done].
  iDestruct "Hs" as "(Hs1 & Hs2 & Hs3)".
  iFrame "Hs1 Hs2".
  iDestruct (own_slice_slice_absorb_capacity with "[$Hs3 $Hcap]") as "$".
  { word. }
Qed.

(** wp variant of [own_slice_slice]

TODO: try to avoid using this and use the canonical pure WP for Slice
(plus directly using [own_slice_slice]) instead
*)
Lemma wp_slice_slice s dq (vs: list V) (low high : w64) :
  {{{ s ↦[t]*{dq} vs ∗ ⌜ 0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.len) ⌝ }}}
    Slice (go.SliceType t) (#s, (#low, #high))%V
  {{{ RET #(slice.slice s t low high);
      (* before the sliced part *)
      (slice.slice s t (W64 0) low) ↦[t]*{dq} (take (sint.nat low) vs) ∗
      (slice.slice s t low high) ↦[t]*{dq} (subslice (sint.nat low) (sint.nat high) vs) ∗
      (* after the sliced part *)
      (slice.slice s t high (slice.len s)) ↦[t]*{dq} (drop (sint.nat high) vs)
  }}}.
Proof.
  iIntros (?) "[Hs %] HΦ".
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_pures. wp_pure; first word. wp_pures. iApply "HΦ".
  rewrite -own_slice_slice; [|word].
  iFrame.
Qed.

(** wp variant of [own_slice_slice_with_cap]

TODO: try to avoid using this and use the canonical pure WP for Slice
(plus directly using [own_slice_slice_with_cap]) instead
*)
Lemma wp_slice_slice_with_cap s (vs: list V) (low high : w64) :
  {{{ s ↦[t]* vs ∗ own_slice_cap t s (DfracOwn 1) ∗
            ⌜ 0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.len) ⌝ }}}
    Slice (go.SliceType t) (#s, (#low, #high))%V
  {{{ RET #(slice.slice s t low high);
      (* before the sliced part *)
      (slice.slice s t (W64 0) low) ↦[t]* (take (sint.nat low) vs) ∗
      (slice.slice s t low high) ↦[t]* (subslice (sint.nat low) (sint.nat high) vs) ∗
      (* after the sliced part becomes part of this capacity *)
      own_slice_cap t (slice.slice s t low high) (DfracOwn 1)
  }}}.
Proof.
  iIntros (?) "(Hs & Hcap & %) HΦ".
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_pures. wp_pure. { word. } wp_pures.
  iApply "HΦ".
  iDestruct (own_slice_slice_with_cap low high with "[$Hs $Hcap]") as "(Hs_pre & Hs & Hs_cap)".
  { word. }
  iFrame.
Qed.

Lemma own_slice_cap_split high s :
  own_slice_cap t s (DfracOwn 1) ∗
  ⌜ 0 ≤ sint.Z high ≤ sint.Z s.(slice.cap)⌝ ⊢
  ∃ vs', (slice.slice s t s.(slice.len) high) ↦[t]* vs' ∗
         own_slice_cap t (slice.slice s t s.(slice.len) high) (DfracOwn 1).
Proof.
Admitted.

(* An unusual use case for slicing where in s[low:high] we have len(s) ≤ high. This
   moves elements from the hidden capacity of s into its actual contents. *)
Lemma own_slice_slice_into_capacity (low high : w64) s (vs : list V) :
  s ↦[t]* vs ∗ own_slice_cap t s (DfracOwn 1) ∗
  ⌜ 0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.cap)⌝ ⊢
  ∃ (vs_cap : list V),
    (slice.slice s t (W64 0) low) ↦[t]* (take (sint.nat low) (vs ++ vs_cap)) ∗
    (slice.slice s t low high) ↦[t]* (drop (sint.nat low) (vs ++ vs_cap)) ∗
    own_slice_cap t (slice.slice s t low high) (DfracOwn 1).
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

Lemma wp_slice_literal {stk E} sz (l : list V) :
  {{{ ⌜ Z.of_nat $ length l = sint.Z sz ⌝ }}}
    slice.literal t sz (ArrayV (into_val <$> l)) @ stk ; E
  {{{ sl, RET #sl; sl ↦[t]* l }}}.
Proof.
  iIntros (Φ) "%Hlen HΦ".
  wp_call.
  wp_apply wp_slice_make2.
  { word. }
  iIntros (?) "[Hsl Hcap]".
  wp_pures.
  wp_apply (wp_alloc_untyped with "[]").
  { simpl. done. }
  iIntros (l_ptr) "Hl". iPersist "Hl".
  wp_pures. wp_apply wp_alloc. iIntros (i_ptr) "Hi".
  wp_pures.
  iDestruct (own_slice_len with "Hsl") as %Hsz.
  rewrite length_replicate in Hsz.
  iAssert (∃ (i : w64),
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ Z.of_nat (length l) ⌝ ∗
      "Hi" ∷ i_ptr ↦ i ∗
      "Hsl" ∷ sl ↦[t]* (take (sint.nat i) l ++ replicate (length l - sint.nat i) (zero_val V))
    )%I
    with "[Hi Hl Hsl]" as "Hloop".
  {
    iExists _; iFrame.
    autorewrite with list in *.
    simpl.
    rewrite take_0 Nat.sub_0_r -Hlen /=.
    replace (Z.to_nat (length l)) with (length l) by word.
    iFrame. word.
  }
  wp_for_core.
  iNamed "Hloop".
  wp_pures. wp_apply (wp_load with "[$]"). iIntros "Hi".
  wp_pures.
  autorewrite with list in *.
  case_bool_decide as Hlt.
  {
    simpl.
    rewrite decide_True //.
    wp_pures.
    wp_apply (wp_load with "[$]"). iIntros "Hi".
    wp_pures. wp_pure; first word. wp_pures.
    wp_apply (wp_load with "[$]"). iIntros "Hi".
    wp_pures.
    list_elem l (sint.Z i) as v.
    erewrite go.index_array.
    2:{ rewrite list_lookup_fmap Hv_lookup //. }
    wp_pures.
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
    wp_apply (wp_store with "[$]"). iIntros "H". iSpecialize ("Hsl" with "H").
    wp_pures.
    wp_for_post_core.
    wp_apply (wp_load with "[$]"). iIntros "Hi". wp_pures.
    wp_apply (wp_store with "[$]"). iIntros "Hi".
    iFrame "Hi". iFrame. iSplitR; first word.
    iApply to_named. iExactEq "Hsl". f_equal.
    replace (sint.nat (word.add i (W64 1))) with (sint.nat i + 1)%nat by word.
    rewrite insert_app_r_alt; last len.
    rewrite take_more; last len.
    rewrite -app_assoc.
    f_equal.
    rewrite insert_replicate_lt; last len.
    rewrite length_take. rewrite Nat.min_l; last len.
    rewrite Nat.sub_diag. simpl.
    erewrite take_S_r.
    2:{ rewrite lookup_drop. rewrite right_id. done. }
    simpl. f_equal. f_equal. len.
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
Qed.

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
  ⊢ own_slice_cap t s (DfracOwn 1).
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
  {{{ s ↦[t]* vs ∗ own_slice_cap t s (DfracOwn 1) ∗ s2 ↦[t]*{dq} vs' }}}
    slice.append t #s #s2
  {{{ (s': slice.t), RET #s';
      s' ↦[t]* (vs ++ vs') ∗ own_slice_cap t s' (DfracOwn 1) ∗ s2 ↦[t]*{dq} vs' }}}.
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
    | |- context[slice.slice _ _ ?low ?high] =>
        iDestruct (own_slice_slice_into_capacity low high with "[$Hs $Hcap]") as
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
