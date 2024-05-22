From Perennial.goose_lang Require Import notation proofmode typing.
From Perennial.goose_lang.lib Require Import typed_mem into_val.
From Perennial.goose_lang.lib Require Import map.impl.
From Perennial.goose_lang.lib Require map.map.
From Perennial.Helpers Require Import Map.
Import uPred.

Set Default Proof Using "Type".

Module Map.
Definition untype `{Countable K} `{IntoVal V}:
  gmap K V -> gmap K val * val :=
  fun m => (to_val <$> m, to_val (IntoVal_def V)).
End Map.

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Context `{!IntoVal K}.
Context `{!EqDecision K, !Countable K}.
Context `{!IntoValComparable K}.

Context `{!IntoVal V}.

Implicit Types (m: gmap K V) (k: K) (v:V).

Definition map_get m k : V * bool :=
  let r := default (IntoVal_def V) (m !! k) in
  let ok := bool_decide (is_Some (m !! k)) in
  (r, ok).

Definition map_insert m k v : gmap K V :=
  <[ k := v ]> m.

Definition map_del m k : gmap K V :=
  delete k m.

Lemma map_get_true k v m :
  map_get m k = (v, true) ->
  m !! k = Some v.
Proof.
  rewrite /map_get.
  destruct (m !! k); rewrite /=; congruence.
Qed.

Lemma map_get_false k v m :
  map_get m k = (v, false) ->
  m !! k = None ∧ v = (IntoVal_def V).
Proof.
  rewrite /map_get.
  destruct (m !! k); rewrite /=.
  - congruence.
  - intuition congruence.
Qed.

Lemma map_get_val k m :
  (map_get m k).1 = default (IntoVal_def V) (m !! k).
Proof. reflexivity. Qed.

Definition own_map (mref:loc) q (m: gmap K V) :=
  map.own_map mref q (Map.untype m).

Theorem own_map_untype mref q m : own_map mref q m -∗ map.own_map mref q (Map.untype m).
Proof.
  auto.
Qed.

Theorem own_map_retype mref q m : map.own_map mref q (to_val <$> m, to_val (IntoVal_def V)) -∗ own_map mref q m.
Proof.
  auto.
Qed.

Ltac untype :=
  rewrite /own_map /Map.untype.

Theorem wp_NewMap `{!IntoValForType V vt} kt stk E :
  {{{ True }}}
    NewMap kt vt #() @ stk; E
  {{{ mref, RET #mref;
      own_map mref (DfracOwn 1) ∅ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_apply map.wp_NewMap.
  iIntros (mref) "Hm".
  iApply "HΦ".
  iApply own_map_retype.
  rewrite def_is_zero fmap_empty.
  auto.
Qed.

Lemma map_get_fmap {m} {k} {vv: val} {ok: bool} :
  map.map_get (Map.untype m) k = (vv, ok) ->
  exists v, vv = to_val v ∧
            map_get m k = (v, ok).
Proof.
  rewrite /map.map_get /map_get.
  rewrite /Map.untype.
  intros H; inversion H; subst; clear H.
  destruct ((to_val <$> m) !! k) eqn:Hlookup; simpl; eauto.
  - rewrite lookup_fmap in Hlookup.
    apply fmap_Some in Hlookup as [x [Hlookup ->]].
    rewrite Hlookup; eauto.
  - eexists; intuition eauto.
    rewrite lookup_fmap in Hlookup.
    apply fmap_None in Hlookup.
    rewrite Hlookup; auto.
Qed.

Theorem wp_MapGet stk E mref q m k :
  {{{ own_map mref q m }}}
    MapGet #mref (to_val k) @ stk; E
  {{{ v ok, RET (to_val v, #ok);
      ⌜map_get m k = (v, ok)⌝ ∗
      own_map mref q m }}}.
Proof using IntoValComparable0.
  iIntros (Φ) "Hm HΦ".
  iDestruct (own_map_untype with "Hm") as "Hm".
  wp_apply (map.wp_MapGet with "Hm").
  iIntros (vv ok) "(%Hmapget&Hm)".
  apply map_get_fmap in Hmapget as [v [-> Hmapget]].
  iApply "HΦ".
  iSplit; [ auto | ].
  iApply (own_map_retype with "Hm").
Qed.

Theorem wp_MapGet' stk E mref q m k kk :
  {{{ own_map mref q m ∗ ⌜kk = to_val k⌝ }}}
    MapGet #mref kk @ stk; E
  {{{ v ok, RET (to_val v, #ok);
      ⌜map_get m k = (v, ok)⌝ ∗
      own_map mref q m }}}.
Proof using IntoValComparable0.
  iIntros (Φ) "[Hm ->] HΦ".
  wp_apply (wp_MapGet with "Hm").
  iIntros (v ok) "(% & Hm)".
  iApply "HΦ".
  iFrame.
  auto.
Qed.

Theorem map_insert_untype m k v' :
  map.map_insert (Map.untype m) k (to_val v') =
  Map.untype (map_insert m k v').
Proof.
  untype.
  rewrite /map.map_insert /map_insert.
  rewrite fmap_insert //.
Qed.

Theorem map_del_untype m k :
  map.map_del (Map.untype m) k =
  Map.untype (map_del m k).
Proof.
  untype.
  rewrite /map.map_del /map_del.
  rewrite fmap_delete //.
Qed.

Theorem wp_MapInsert v' stk E mref m k vv :
  vv = to_val v' ->
  {{{ own_map mref (DfracOwn 1) m }}}
    MapInsert #mref (to_val k) vv @ stk; E
  {{{ RET #(); own_map mref (DfracOwn 1) (map_insert m k v') }}}.
Proof.
  intros ->.
  iIntros (Φ) "Hm HΦ".
  iDestruct (own_map_untype with "Hm") as "Hm".
  wp_apply (map.wp_MapInsert with "Hm").
  iIntros "Hm".
  iApply "HΦ".
  rewrite map_insert_untype.
  iApply (own_map_retype with "Hm").
Qed.

Theorem wp_MapInsert_to_val stk E mref m k v' :
  {{{ own_map mref (DfracOwn 1) m }}}
    MapInsert #mref (to_val k) (to_val v') @ stk; E
  {{{ RET #(); own_map mref (DfracOwn 1) (map_insert m k v') }}}.
Proof.
  iIntros (Φ) "Hm HΦ".
  iApply (wp_MapInsert with "Hm"); first reflexivity.
  iFrame.
Qed.

Theorem wp_MapDelete stk E mref m k :
  {{{ own_map mref (DfracOwn 1) m }}}
    MapDelete #mref (to_val k) @ stk; E
  {{{ RET #(); own_map mref (DfracOwn 1) (map_del m k) }}}.
Proof using IntoValComparable0.
  iIntros (Φ) "Hm HΦ".
  iDestruct (own_map_untype with "Hm") as "Hm".
  wp_apply (map.wp_MapDelete with "Hm").
  iIntros "Hm".
  iApply "HΦ".
  rewrite map_del_untype.
  iApply (own_map_retype with "Hm").
Qed.

Lemma map_size_untype m:
  size m = size (Map.untype m).1.
Proof.
  unfold Map.untype.
  by rewrite map_size_fmap.
Qed.

Theorem wp_MapLen stk E mref m q :
  {{{ own_map mref q m }}}
    MapLen #mref @ stk; E
  {{{ RET #(size m); ⌜size m = uint.nat (size m)⌝ ∗ own_map mref q m }}}.
Proof using IntoValComparable0.
  iIntros (Φ) "Hm HΦ".
  iDestruct (own_map_untype with "Hm") as "Hm".
  wp_apply (map.wp_MapLen with "Hm").
  iIntros "[%Hsize Hm]".
  rewrite map_size_untype.
  iApply "HΦ".
  by iSplit.
Qed.

Theorem bi_iff_1 {PROP:bi} (P Q: PROP) :
  P ≡ Q ->
  ⊢ P -∗ Q.
Proof.
  intros ->; auto.
Qed.

Theorem bi_iff_2 {PROP:bi} (P Q: PROP) :
  P ≡ Q ->
  ⊢ Q -∗ P.
Proof.
  intros ->; auto.
Qed.

Theorem wp_MapIter stk E mref q m (I: iProp Σ) (P Q: K -> V -> iProp Σ) (body: val) Φ:
  own_map mref q m -∗
  I -∗
  ([∗ map] k ↦ v ∈ m, P k v) -∗
  (∀ (k: K) (v: V),
      {{{ I ∗ P k v }}}
        body (to_val k) (to_val v) @ stk; E
      {{{ RET #(); I ∗ Q k v }}}) -∗
  ▷ ((own_map mref q m ∗ I ∗ [∗ map] k ↦ v ∈ m, Q k v) -∗ Φ #()) -∗
  WP MapIter #mref body @ stk; E {{ v, Φ v }}.
Proof using IntoValComparable0.
  iIntros "Hm HI HP #Hbody HΦ".
  iDestruct (own_map_untype with "Hm") as "Hm".
  wp_apply (map.wp_MapIter _ _ _ _ _ _
    (λ k vv, ∃ v, ⌜vv = to_val v⌝ ∗ P k v)%I
    (λ k vv, ∃ v, ⌜vv = to_val v⌝ ∗ Q k v)%I with "Hm HI [HP] [Hbody]").
  { rewrite /Map.untype /=.
    iApply big_sepM_fmap.
    iApply (big_sepM_mono with "HP").
    iIntros.
    iExists _; iFrame; done. }
  { iIntros.
    iIntros (Φbody).
    iModIntro.
    iIntros "[HI HP] HΦ".
    iDestruct "HP" as (v0) "[-> HP]".
    wp_apply ("Hbody" with "[$HI $HP]").
    iIntros "[HI HQ]".
    iApply "HΦ"; iFrame. done. }
  iIntros "(Hm & HI & HQ)".
  iApply "HΦ". iFrame.
  rewrite /Map.untype /=.
  iApply (big_sepM_mono (λ k v, ∃ v0, ⌜to_val v = to_val v0⌝ ∗ Q k v0)%I).
  { iIntros (k v Hkv) "H".
    iDestruct "H" as (v0) "[% H]".
    apply (inj to_val) in H; subst. iFrame. }
  iDestruct (bi_iff_1 with "HQ") as "HQ"; first by iApply big_sepM_fmap.
  iFrame.
Qed.

Theorem wp_MapIter_2 stk E mref q m (I: gmap K V -> gmap K V -> iProp Σ) (body: val) Φ:
  own_map mref q m -∗
  I m ∅ -∗
  (∀ (k: K) (v: V) (mtodo mdone : gmap K V),
      {{{ I mtodo mdone ∗ ⌜mtodo !! k = Some v⌝ }}}
        body (to_val k) (to_val v) @ stk; E
      {{{ RET #(); I (delete k mtodo) (<[k := v]> mdone) }}}) -∗
  ((own_map mref q m ∗ I ∅ m) -∗ Φ #()) -∗
  WP MapIter #mref body @ stk; E {{ v, Φ v }}.
Proof using IntoValComparable0.
  iIntros "Hm HI #Hbody HΦ".
  iDestruct (own_map_untype with "Hm") as "Hm".
  wp_apply (map.wp_MapIter_2 _ _ _ _ _
    (λ mtodo mdone, ∃ mtodo' mdone',
      ⌜ mtodo = to_val <$> mtodo' ⌝ ∗
      ⌜ mdone = to_val <$> mdone' ⌝ ∗
      I mtodo' mdone')%I
    with "Hm [HI] [Hbody]").
  { rewrite /Map.untype /=.
    iExists m, ∅. iSplitR; first by done. rewrite fmap_empty. iSplitR; done. }
  { iIntros.
    iIntros (Φbody).
    iModIntro.
    iIntros "[HI %] HΦ".
    iDestruct "HI" as (mtodo' mdone') "(-> & -> & HI)".
    rewrite lookup_fmap in H.
    destruct (mtodo' !! k) eqn:He; simpl in H; try congruence.
    inversion H; clear H; subst.
    wp_apply ("Hbody" with "[$HI] [HΦ]"); eauto.
    iNext.
    iIntros "H".
    iApply "HΦ"; iFrame.
    iSplitR.
    - rewrite fmap_delete. done.
    - rewrite fmap_insert. done. }
  iIntros "(Hm & HI)".
  iDestruct "HI" as (mtodo' mdone') "(% & % & HI)".
  iApply "HΦ". iFrame.
  assert (mtodo' = ∅) by (eapply fmap_empty_iff; eauto); subst mtodo'.
  rewrite /Map.untype /= in H0.
  apply (inj (fmap to_val)) in H0; subst.
  done.
Qed.

Theorem wp_MapIter_3 stk E mref q m (I: gmap K V -> gmap K V -> iProp Σ) (body: val) Φ:
  own_map mref q m -∗
  I m ∅ -∗
  (∀ (k: K) (v: V) (mtodo mdone : gmap K V),
      {{{ I mtodo mdone ∗ ⌜m = mtodo ∪ mdone ∧ dom mtodo ## dom mdone ∧ mtodo !! k = Some v⌝ }}}
        body (to_val k) (to_val v) @ stk; E
      {{{ RET #(); I (delete k mtodo) (<[k := v]> mdone) }}}) -∗
  ((own_map mref q m ∗ I ∅ m) -∗ Φ #()) -∗
  WP MapIter #mref body @ stk; E {{ v, Φ v }}.
Proof using IntoValComparable0.
  iIntros "Hismap HI #Hbody HΦ".
  wp_apply (wp_MapIter_2 _ _ _ _ _
    (λ mtodo mdone,
      I mtodo mdone ∗ ⌜m = mtodo ∪ mdone ∧ dom mtodo ## dom mdone⌝)%I
    with "Hismap [$HI]").
  { iPureIntro; split.
    { rewrite right_id; eauto. }
    set_solver. }
  { iIntros (k v mtodo mdone).
    iModIntro.
    iIntros (Φ0) "[[HI %] %] HΦ".
    iApply ("Hbody" with "[$HI]").
    { iPureIntro. intuition eauto. }
    iNext.
    iIntros "HI".
    iApply "HΦ". iFrame "HI".
    iPureIntro; split.
    2: set_solver.
    rewrite union_delete_insert; intuition eauto. }
  iIntros "(Hm & HI & %)".
  iApply "HΦ". iFrame.
Qed.

Theorem wp_MapIter_empty {stk E} (mref: loc) q (body: val) :
  {{{ own_map mref q (∅: gmap K V) }}}
    MapIter #mref body @ stk; E
  {{{ RET #(); own_map mref q (∅: gmap K V) }}}.
Proof using IntoValComparable0.
  iIntros (Φ) "Hismap HΦ".
  wp_apply (wp_MapIter stk E _ _ _ (emp)%I
                       (λ _ _, False)%I
                       (λ _ _, False)%I body
              with "Hismap [] [] [] [HΦ]").
  - auto.
  - auto.
  - clear Φ.
    iIntros (k v) "!>".
    iIntros (Φ) "[_ []]".
  - iIntros "!> (Hmap & _ & _)".
    iApply ("HΦ" with "[$]").
Qed.

Theorem wp_MapIter_fold {stk E} (mref: loc) q (body: val)
        (P: gmap K V → iProp Σ) m Φ :
  own_map mref q m -∗
  P ∅ -∗
  (∀ m0 (k: K) v, {{{ P m0 ∗ ⌜m0 !! k = None ∧ m !! k = Some v⌝ }}}
                      body (to_val k) (to_val v) @ stk; E
                    {{{ RET #(); P (<[k:=v]> m0) }}}) -∗
  ▷ ((own_map mref q m ∗ P m) -∗ Φ #()) -∗
  WP MapIter #mref body @ stk; E {{ Φ }}.
Proof using IntoValComparable0.
  iIntros "Hm HP #Hbody".
  iIntros "HΦ".
  wp_apply (map.wp_MapIter_fold (λ mv, ∃ m, ⌜mv = (Map.untype m).1⌝ ∗ P m)%I
              with "[Hm] [HP]").
  { iFrame. }
  { iExists ∅; iFrame.
    rewrite /= fmap_empty //. }
  { clear Φ.
    iIntros (m0 k v) "!>".
    iIntros (Φ) "[HP %] HΦ".
    destruct H as [Hnone Hsome].
    iDestruct "HP" as (m') "[-> HP]".
    simpl in Hnone, Hsome.
    rewrite lookup_fmap in Hnone.
    rewrite lookup_fmap in Hsome.
    apply fmap_None in Hnone.
    apply fmap_Some_1 in Hsome as [v' [Hsome ->]].
    wp_apply ("Hbody" with "[$HP]"); auto.
    iIntros "HP".
    iApply "HΦ".
    iExists _; iFrame.
    iPureIntro.
    simpl.
    rewrite fmap_insert //. }
  iIntros "[Hmap HP]".
  iDestruct "HP" as (m') "[%Heq HP]".
  apply (inj (fmap to_val)) in Heq; subst.
  iApply "HΦ"; iFrame.
Qed.

Global Instance own_map_persistent mref m : Persistent (own_map mref DfracDiscarded m).
Proof. apply _. Qed.

Lemma own_map_persist mref dq m :
  own_map mref dq m ==∗ own_map mref DfracDiscarded m.
Proof.
  iIntros "H".
  iMod (map.own_map_persist with "H") as "H".
  iModIntro.
  iFrame.
Qed.

End heap.

Arguments wp_NewMap {_ _ _ _ _ _ _} K {_ _ _} V {_} {vt}.
Arguments wp_MapGet {_ _ _ _ _ _} K {_ _ _ _} V.
Arguments wp_MapInsert {_ _ _ _ _ _} K {_ _ _} V {_}.
Arguments wp_MapDelete {_ _ _ _ _ _} K {_ _ _ _} V {_}.
Arguments wp_MapLen {_ _ _ _ _ _} K {_ _ _ _} V {_}.

Typeclasses Opaque own_map.
