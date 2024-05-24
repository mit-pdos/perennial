From iris.proofmode Require Import coq_tactics reduction.
From Perennial.goose_lang Require Import notation proofmode.
From Perennial.goose_lang.lib Require Import typed_mem into_val.
From Perennial.goose_lang.lib Require Import control.
From Perennial.goose_lang.lib Require Export map.impl.
Import uPred.


Set Default Proof Using "Type".

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types t : ty.
Implicit Types stk : stuckness.
Implicit Types off : nat.

Context `{!IntoVal K}.
Context `{!IntoValComparable K}.
Context `{!EqDecision K, !Countable K}.

(* The model of a map is [gmap K val * val] (the second value is the default).

The abstraction relation (actually abstraction function) between a val mv and a
model m is m = map_val mv.

The models are canonical due to extensionality of gmaps, but the concrete
representation tracks all insertions (including duplicates). *)

Fixpoint map_val (v: val) : option (gmap K val * val) :=
  match v with
  | MapConsV kval v m =>
    match map_val m with
    | Some (m, def) =>
      match (from_val kval) with
      | Some k => Some (<[ k := v ]> m, def)
      | None => None
      end
    | None => None
    end
  | MapNilV def => Some (∅, def)
  | _ => None
  end.

(*
Definition val_of_map (m_def: gmap K val * val) : val :=
  let (m, def) := m_def in
  fold_right (λ '(k, v) mv, MapConsV k v mv)
             (MapNilV def)
             (map_to_list m).

Theorem map_val_id : forall v m_def,
    map_val v = Some m_def ->
    val_of_map m_def = v.
Proof.
  induction v; intros [m def]; try solve [ inversion 1 ]; simpl; intros H.
  - inversion H; subst; clear H.
    rewrite map_to_list_empty; simpl; auto.
  - destruct v; try congruence.
    destruct v1; try congruence.
    destruct v1_1; try congruence.
    destruct l; try congruence.
    destruct_with_eqn (map_val v2); try congruence.
    specialize (IHv p).
    destruct p as [m' def'].
    inversion H; subst; clear H.
    (* oops, the normal val induction principle is too weak to prove this *)
Abort. *)

Definition map_get (m_def: gmap K val * val) (k: K) : (val*bool) :=
  let (m, def) := m_def in
  let r := default def (m !! k) in
  let ok := bool_decide (is_Some (m !! k)) in
  (r, ok).

Definition map_insert (m_def: gmap K val * val) (k: K) (v: val) : gmap K val * val :=
  let (m, def) := m_def in
  (<[ k := v ]> m, def).

Definition map_del (m_def: gmap K val * val) (k: K) : gmap K val * val :=
  let (m, def) := m_def in
  (delete k m, def).


Lemma map_get_empty def k : map_get (∅, def) k = (def, false).
Proof.
  reflexivity.
Qed.

Lemma map_get_insert k v m def :
  map_get (<[k:=v]> m, def) k = (v, true).
Proof.
  rewrite /map_get.
  rewrite lookup_insert //.
Qed.

Lemma map_get_insert_ne k k' v m def :
  k ≠ k' ->
  map_get (<[k:=v]> m, def) k' = map_get (m, def) k'.
Proof.
  intros Hne.
  rewrite /map_get.
  rewrite lookup_insert_ne //.
Qed.

Lemma map_get_true k v m def :
  map_get (m, def) k = (v, true) ->
  m !! k = Some v.
Proof.
  rewrite /map_get.
  destruct (m !! k); rewrite /=; congruence.
Qed.

Lemma map_get_false k v m def :
  map_get (m, def) k = (v, false) ->
  m !! k = None ∧ v = def.
Proof.
  rewrite /map_get.
  destruct (m !! k); rewrite /=.
  - congruence.
  - intuition congruence.
Qed.

Lemma map_val_split mv m :
  map_val mv = Some m ->
  {∃ def, mv = MapNilV def ∧ m = (∅, def)} +
  {∃ k v mv' m', mv = MapConsV (to_val k) v mv' ∧ map_val mv' = Some m' ∧ m = (<[k:=v]> (fst m'), snd m')}.
Proof using IntoValComparable0.
  intros H.
  destruct mv; inversion H; subst; [ left | right ].
  - exists mv; auto.
  - destruct mv; try solve [ inversion H1 ].
    destruct mv1; try solve [ inversion H1 ].
    destruct (from_val mv1_1) eqn:?; try solve [ inversion H1 ].
    2:{ exfalso. by destruct (map_val mv2) as [[] |]. }
    destruct m; try solve [ inversion H1 ].
    destruct_with_eqn (map_val mv2); try solve [ inversion H1 ].
    destruct p; inversion H1; subst; clear H1.
    eexists k, _, _, _; intuition eauto.
    repeat f_equal.
    symmetry.
    by apply IntoValComparable_inj.
Qed.

Definition own_map (mref:loc) q (m: gmap K val * val): iProp Σ :=
  ∃ mv, ⌜map_val mv = Some m⌝ ∗ mref ↦{q} mv.

Global Instance own_map_timeless mref q m :
  Timeless (own_map mref q m) := _.

Theorem map_zero_val kt vt :
  flatten_struct (zero_val (mapValT kt vt)) = [MapNilV (zero_val vt)].
Proof. reflexivity. Qed.

Theorem wp_NewMap stk E kt vt :
  {{{ True }}}
    NewMap kt vt #() @ stk; E
  {{{ mref, RET #mref;
      own_map mref (DfracOwn 1) (∅, zero_val vt) }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply wp_alloc_untyped.
  { rewrite map_zero_val; auto. }
  iIntros (mref) "Hm".
  iApply "HΦ".
  iExists _; iSplitR; auto.
  done.
Qed.

Local Instance comparable_PureExec (ϕ: Prop) (v1 v2:val) :
  PureExec (is_comparable v1 ∧ is_comparable v2) 1 (v1 = v2)%E (#(bool_decide (v1 = v2)))%V.
Proof.
  intros ?.
  eapply nsteps_once.
  apply pure_base_step_pure_step.
  constructor.
  {
    intros; subst; do 4 eexists; constructor 1; cbn.
    rewrite /base_step /base_trans /bin_op_eval /bin_op_eval_eq /=.
    rewrite decide_True; last done.
    repeat (Transitions.monad_simpl; simpl).
  }
  {
    inversion 1; subst.
    simpl in *.
    rewrite /base_step /base_trans /bin_op_eval /bin_op_eval_eq /= in H1.
    rewrite decide_True in H1; last done.
    simpl in H1.
    by Transitions.monad_inv.
  }
Qed.


Theorem wp_MapGet stk E mref q (m: gmap K val * val) k :
  {{{ own_map mref q m }}}
    MapGet #mref (to_val k) @ stk; E
  {{{ v ok, RET (v, #ok); ⌜map_get m k = (v, ok)⌝ ∗
                          own_map mref q m }}}.
Proof using IntoValComparable0.
  iIntros (Φ) "Hmref HΦ".
  iDestruct "Hmref" as (mv H) "Hmref".
  wp_call.
  wp_untyped_load.
  wp_closure.
  iAssert (∀ v ok, ⌜map_get m k = (v, ok)⌝ -∗ Φ (v, #ok)%V)%I with "[Hmref HΦ]" as "HΦ".
  { iIntros (v ok) "%".
    iApply ("HΦ" with "[Hmref]").
    iSplitR; auto.
    iExists mv; by iFrame. }
  iLöb as "IH" forall (m mv H).
  wp_call.
  destruct (map_val_split _ _ H).
  - (* nil *)
    destruct e as [def ?]; intuition subst.
    wp_pures.
    iApply "HΦ".
    rewrite map_get_empty; auto.
  - destruct e as [k' [v [mv' [m' ?]]]]; intuition subst.
    wp_pures.

    wp_pure1.
    { split; apply IntoValComparable_comparable. }
    wp_if_destruct.
    + wp_pures.
      iApply "HΦ".
      eapply inj in Heqb.
      2: apply _.
      subst.
      rewrite map_get_insert //.
    + iApply "IH".
      * eauto.
      * iIntros (v' ok) "%".
        iApply "HΦ".
        rewrite map_get_insert_ne //; try congruence.
        destruct m'; eauto.
Qed.

Theorem wp_MapInsert stk E mref (m: gmap K val * val) k v' :
  {{{ own_map mref (DfracOwn 1) m }}}
    MapInsert #mref (to_val k) v' @ stk; E
  {{{ RET #(); own_map mref (DfracOwn 1) (map_insert m k v') }}}.
Proof.
  iIntros (Φ) "Hmref HΦ".
  iDestruct "Hmref" as (mv ?) "Hmref".
  wp_call.
  wp_untyped_load.
  wp_apply (wp_store with "Hmref"); iIntros "Hmref".
  iApply ("HΦ" with "[Hmref]").
  iExists _; iFrame.
  iPureIntro.
  simpl.
  rewrite H.
  rewrite IntoVal_inj'.
  destruct m; simpl; auto.
Qed.

Local Instance IntoVal_inj :
  Inj (A:=K) eq eq to_val.
Proof.
  apply _.
Qed.

Local Lemma wp_MapDelete' stk E mv (m: gmap K val * val) k :
  {{{ ⌜map_val mv = Some m⌝ }}}
    MapDelete' mv (to_val k) @ stk; E
  {{{ mv', RET mv'; ⌜map_val mv' = Some (map_del m k)⌝ }}}.
Proof using IntoValComparable0.
  destruct m.
  iIntros (Φ H) "HΦ".
  rewrite /MapDelete'.
  wp_lam. wp_let.
  wp_pure (Rec _ _ _).
  iLöb as "IH" forall (g v mv H Φ).
  apply map_val_split in H; intuition; repeat match goal with
    | H : ∃ _, _ |- _ => destruct H
    end; intuition; try congruence; subst.
  - wp_pures.
    iApply "HΦ".
    rewrite /=.
    inversion H1; subst.
    rewrite delete_empty. done.
  - destruct x2.
    wp_pures.
    wp_pure1.
    { split; apply IntoValComparable_comparable. }
    rewrite bool_decide_decide.
    destruct (decide (to_val k = to_val x)); wp_if.
    + inversion e; clear e; subst.
      iApply "IH".
      { eauto. }
      iIntros (mv' Hmv').
      iApply "HΦ"; iPureIntro.
      rewrite Hmv' H2 /map_del /=.
      apply (inj (R:=(=))) in H1; last apply _.
      subst.
      rewrite delete_insert_delete.
      auto.
    + iSpecialize ("IH" $! _ _ _ H).
      wp_bind (App _ _).
      iApply "IH".
      iIntros (mv' Hmv').
      wp_pures.
      iApply "HΦ"; iPureIntro.
      rewrite H2.
      rewrite /= Hmv' /map_del.
      f_equal.
      rewrite IntoVal_inj'.
      rewrite delete_insert_ne; first congruence.
      destruct (decide (k = x)).
      { by subst; exfalso. }
      done.
Qed.

(* Want this for u64 addition commutativity in wp_MapLen' *)
Add Ring u64ring : (word.ring_theory (word := w64_instance.w64))
                    (preprocess [autorewrite with rew_word_morphism],
                      morphism (word.ring_morph (word := w64_instance.w64)),
                      constants [word_cst]).

(* The postcondition guarantees that the size of the map actually fits in a u64 *)
Theorem wp_MapLen' stk E(mv:val) (m:gmap K val * val) :
  {{{
      ⌜Some m = map_val mv⌝
  }}}
    MapLen' mv @ stk ; E
  {{{
    RET #(W64 (size m.1)); ⌜size m.1 = uint.nat (size m.1)⌝
  }}}.
Proof using IntoValComparable0.
  iIntros (Φ) "%Hmapval HΦ".
  wp_lam.
  wp_pure (Rec _ _ _).
  iLöb as "IH" forall (m mv Hmapval Φ).
  wp_pures.
  destruct (map_val_split mv m).
  { done. }
  - destruct e as [def [Hmv Hmuntype]].
    rewrite Hmv.
    wp_match.
    replace (size m.1) with 0%nat; last first.
    { rewrite Hmuntype. simpl. done. }
    iApply "HΦ".
    done.
  - destruct e as [k [v [mv' [m' [Hmcons [Hmv Hmuntype]]]]]].
    rewrite Hmcons.
    wp_match.
    wp_pures.
    wp_apply (wp_MapDelete' with "[]").
    { eauto. }
    iIntros (mv'' Hmv'').

    wp_bind (_ mv'')%E.
    wp_apply "IH"; first done.
    iIntros (HsizeConversion).

    wp_pures.
    wp_apply (wp_Assume).
    iIntros (Hassume).
    apply bool_decide_eq_true in Hassume.
    wp_pures.
    assert ((size (map_del m' k).1) = (Init.Nat.pred (size m.1))) as Hsize.
    {
      unfold map_del.
      replace ((let (m0, def) := m' in (delete k m0, def)%core).1) with (delete k m'.1); last first.
      { destruct m'. done. }
      replace (delete k m'.1) with (delete k m.1); last first.
      { rewrite Hmuntype. by rewrite delete_insert_delete. }
      rewrite map_size_delete_Some; last first.
      { exists v. rewrite Hmuntype. simpl. apply lookup_insert. }
      done.
    }
    set (s:=size m.1) in *.
    rewrite Hsize in Hassume HsizeConversion |-*.
    assert (s = size m.1) by eauto.
    destruct s. (* Get rid of -1 by destructing s, and ruling out s=0 *)
    { exfalso.
      rewrite Hmuntype in H.
      simpl in H.
      symmetry in H.
      apply map_size_empty_iff in H.
      by apply insert_non_empty in H.
    }

    simpl in *.
    replace (word.add 1 s) with (word.add s 1) by ring.
    replace (word.add s 1) with (word.add (uint.nat s) 1); last first.
    { by rewrite -HsizeConversion. }
    rewrite u64_Z_through_nat.
    replace (word.add (uint.Z s) 1%Z) with (uint.Z (s + 1):u64); last first.
    { word. }
    replace (S s) with (s + 1)%nat in *; last lia.

    assert (Z.of_nat (s + 1) = (uint.Z (s + 1))).
    {
      rewrite -u64_Z_through_nat.
      word.
    }
    rewrite -H0.
    iApply "HΦ".
    rewrite -u64_Z_through_nat in H0.
    iPureIntro.
    word.
Qed.

Theorem wp_MapLen stk E mref q m :
  {{{
      own_map mref q m
  }}}
    (MapLen #mref) @ stk ; E
  {{{
    RET #(size m.1);
      ⌜size m.1 = uint.nat (size m.1)⌝ ∗
      own_map mref q m
  }}}.
Proof using IntoValComparable0.
  iIntros (Φ) "Hmap HΦ".
  wp_lam.
  iDestruct "Hmap" as (mv Hmapval) "Hmref".
  wp_apply (wp_load with "Hmref").
  iIntros "Hmref".
  wp_apply (wp_MapLen'); first done.
  iIntros (Hsize).
  iApply "HΦ".
  iSplitL ""; first done.
  iExists mv. eauto.
Qed.

Theorem wp_MapDelete stk E mref (m: gmap K val * val) k :
  {{{ own_map mref (DfracOwn 1) m }}}
    MapDelete #mref (to_val k) @ stk; E
  {{{ RET #(); own_map mref (DfracOwn 1) (map_del m k) }}}.
Proof using IntoValComparable0.
  iIntros (Φ) "Hmref HΦ".
  iDestruct "Hmref" as (mv ?) "Hmref".
  wp_call.
  wp_untyped_load.
  wp_apply wp_MapDelete'; eauto.
  iIntros (mv' Hmv').
  wp_apply (wp_store with "Hmref").
  iIntros "Hmref".
  iApply "HΦ". iExists _. iFrame. eauto.
Qed.

Theorem wp_MapIter stk E mref q (m: gmap K val * val) (I: iProp Σ) (P Q: K -> val -> iProp Σ) (body: val) Φ:
  own_map mref q m -∗
  I -∗
  ([∗ map] k ↦ v ∈ fst m, P k v) -∗
  (∀ (k: K) (v: val),
      {{{ I ∗ P k v }}}
        body (to_val k) v @ stk; E
      {{{ RET #(); I ∗ Q k v }}}) -∗
  ▷ ((own_map mref q m ∗ I ∗ [∗ map] k ↦ v ∈ fst m, Q k v) -∗ Φ #()) -∗
  WP MapIter #mref body @ stk; E {{ v, Φ v }}.
Proof using IntoValComparable0.
  iIntros "Hm Hi Hp #Hind HΦ".
  iDestruct "Hm" as (mv) "[% Hm]".
  wp_call.
  wp_apply (wp_start_read with "Hm").
  iIntros "[Hm0 Hm1]".
  wp_let.
  destruct m; simpl in *.
  wp_closure.
  match goal with
  | |- context[RecV (BNamed "mapIter") _ ?body] => set (loop:=body)
  end.
  apply map_val_split in H as HI.
  revert HI.
  generalize mv at 1 2 4; intro mvI.
  generalize g at 1 2 3 5; intro gI.
  intro HI.
  iLöb as "IH" forall (mvI gI HI).
  wp_pures.
  destruct HI as [[d HI]|[k [v0 [mv' [m' HI]]]]]; subst.
  - intuition subst.
    inversion H1; clear H1; subst.
    wp_pures.
    wp_apply (wp_finish_read with "[$Hm0 $Hm1]").
    iIntros "Hm".
    iApply "HΦ"; iFrame.
    iSplitR "Hp"; iFrame.
    + done.
    + iApply big_sepM_empty. done.
  - intuition subst.
    inversion H3; clear H3; subst.
    wp_pures.
    iDestruct (big_sepM_insert_delete with "Hp") as "[Hpk Hp]".
    wp_apply ("Hind" with "[$Hi $Hpk]").
    iIntros "[Hi Hq]".
    wp_pure (Rec _ _ _).
    wp_lam.
    wp_apply (wp_MapDelete'); eauto.
    iIntros (mv'') "%".
    iSpecialize ("IH" $! mv'' _ _ with "Hi Hp [Hq HΦ] Hm0 Hm1").
    { iIntros "(Hmref & Hi & Hqs)".
      iApply "HΦ"; iFrame.
      iApply big_sepM_insert_delete; iFrame.
    }
    iApply "IH".
Unshelve.
  apply map_val_split in H0; destruct m'; intuition idtac.
Qed.

Lemma union_with_Some_l {A} (x:A) my :
  union_with (λ (x _ : A), Some x) (Some x) my = Some x.
Proof.
  rewrite /union_with /=.
  destruct my; auto.
Qed.

Lemma union_with_Some_r {A} my :
  union_with (λ (x _ : A), Some x) None my = my.
Proof.
  rewrite /union_with /=.
  destruct my; auto.
Qed.

Lemma union_insert_delete:
  ∀ (m' : gmap K val) (k : K) (v: val) (mtodo : gmap K val),
    m' !! k = None →
    m' ##ₘ mtodo →
    mtodo !! k = Some v →
    <[k:=v]> m' ∪ delete k mtodo = m' ∪ mtodo.
Proof.
  intros m' k v mtodo Hnone Hdisj Hsome.
  apply map_eq; intros k0.
  rewrite !lookup_union.
  destruct (decide (k = k0)); subst.
  - rewrite lookup_insert Hnone Hsome.
    rewrite union_Some_l union_Some_r //.
  - rewrite lookup_insert_ne //.
    destruct_with_eqn (m' !! k0).
    + rewrite !union_Some_l //.
    + rewrite lookup_delete_ne //.
Qed.

Lemma union_delete_insert (m0 m1 : gmap K val) a v :
  delete a m0 ∪ <[a:=v]> m1 = <[a:=v]> m0 ∪ m1.
Proof.
  apply map_eq; intros k.
  rewrite !lookup_union.
  destruct (decide (a = k)); subst.
  - rewrite ?lookup_insert lookup_delete.
    destruct (m1 !! k); eauto.
  - rewrite ?lookup_insert_ne ?lookup_delete_ne //.
Qed.

Lemma insert_delete_disjoint:
  ∀ (m' : gmap K val) (k : K) (v: val) (mtodo : gmap K val),
    m' !! k = None →
    m' ##ₘ mtodo →
    mtodo !! k = Some v →
    <[k:=v]> m' ##ₘ delete k mtodo.
Proof.
  intros m' k v mtodo Hnone Hdisj Hsome.
  apply map_disjoint_alt.
  assert (forall i, m' !! i = None ∨ mtodo !! i = None) as Hdisj'.
  { apply map_disjoint_alt; auto. }
  intros.
  destruct (decide (k = i)); subst.
  - rewrite lookup_delete; eauto.
  - rewrite lookup_insert_ne //.
    destruct (Hdisj' i); eauto.
    rewrite lookup_delete_ne; eauto.
Qed.

Lemma delete_insert_disjoint (m0 m1 : gmap K val) a v :
  <[a:=v]> m0 ##ₘ m1 ->
  delete a m0 ##ₘ <[a:=v]> m1.
Proof.
  intro Hdisj.
  assert (∀ i, <[a:=v]> m0 !! i = None ∨ m1 !! i = None) as Hdisj'.
  { apply map_disjoint_alt; eauto. }
  apply map_disjoint_alt; intros.
  destruct (decide (a = i)); subst.
  - rewrite lookup_delete; eauto.
  - rewrite lookup_insert_ne //.
    destruct (Hdisj' i); eauto.
    rewrite lookup_insert_ne in H; eauto.
    rewrite lookup_delete_ne; eauto.
Qed.

Theorem wp_MapIter_fold {stk E} {mref: loc} {q} {body: val}
        (P: gmap K val → iProp Σ) m Φ :
  own_map mref q m -∗
  P ∅ -∗
  (∀ m0 (k: K) v, {{{ P m0 ∗ ⌜m0 !! k = None ∧ m.1 !! k = Some v⌝ }}}
                      body (to_val k) v @ stk; E
                    {{{ RET #(); P (<[k:=v]> m0) }}}) -∗
  ▷ ((own_map mref q m ∗ P m.1) -∗ Φ #()) -∗
  WP MapIter #mref body @ stk; E {{ Φ }}.
Proof using IntoValComparable0.
  iIntros "Hm HP #Hbody HΦ".
  iDestruct "Hm" as (mv) "[% Hm]".
  wp_call.
  wp_apply (wp_start_read with "Hm").
  iIntros "[Hm0 Hm1]".
  wp_let.
  destruct m; simpl in *.
  wp_pure (Rec _ _ _).
  match goal with
  | |- context[RecV (BNamed "mapIter") _ ?body] => set (loop:=body)
  end.
  apply map_val_split in H as HI.
  assert (g ∪ ∅ = g) as Hunion. { rewrite right_id; eauto. }
  assert (g ##ₘ ∅) as Hdisjoint. { apply map_disjoint_empty_r. }
  revert HI Hunion Hdisjoint.
  generalize mv at 1 2 4; intro mvI.
  generalize g at 1 2 3 5; intro gI.
  generalize (∅ : gmap K val) at 2 3 4; intro m0I.
  intros HI Hunion Hdisjoint.
  iLöb as "IH" forall (mvI gI m0I HI Hunion Hdisjoint).
  wp_pures.
  destruct HI as [[d HI]|[k [v0 [mv' [m' HI]]]]]; subst.
  - intuition subst.
    inversion H1; clear H1; subst.
    wp_pures.
    wp_apply (wp_finish_read with "[$Hm0 $Hm1]").
    iIntros "Hm".
    rewrite left_id.
    iApply "HΦ"; iFrame.
    rewrite H left_id. done.
  - intuition subst.
    inversion H3; clear H3; subst.
    wp_pures.
    wp_apply ("Hbody" with "[$HP]").
    { iPureIntro; split.
      { eapply map_disjoint_Some_l; eauto.
        rewrite lookup_insert; eauto. }
      erewrite lookup_union_Some_l; eauto.
      rewrite lookup_insert; eauto.
    }
    iIntros "HP".
    wp_pure (Rec _ _ _).
    wp_lam.
    wp_apply (wp_MapDelete'); eauto.
    iIntros (mv'') "%".
    apply map_val_split in H0. destruct m'.
    iSpecialize ("IH" $! mv'' _ _ H0 _ _ with "HP HΦ Hm0 Hm1").
    iApply "IH".
Unshelve.
  { simpl. apply union_delete_insert. }
  { apply delete_insert_disjoint; eauto. }
Qed.

Theorem wp_MapIter_2 stk E mref q (m: gmap K val * val) (I: gmap K val -> gmap K val -> iProp Σ) (body: val) Φ:
  own_map mref q m -∗
  I (fst m) ∅ -∗
  (∀ (k: K) (v: val) (mtodo mdone : gmap K val),
      {{{ I mtodo mdone ∗ ⌜mtodo !! k = Some v⌝ }}}
        body (to_val k) v @ stk; E
      {{{ RET #(); I (delete k mtodo) (<[k := v]> mdone) }}}) -∗
  ((own_map mref q m ∗ I ∅ (fst m)) -∗ Φ #()) -∗
  WP MapIter #mref body @ stk; E {{ v, Φ v }}.
Proof using IntoValComparable0.
  iIntros "Hm HI #Hbody HΦ".
  wp_apply (wp_MapIter_fold (λ mdone, ∃ mtodo, ⌜mdone ∪ mtodo = m.1 ∧ mdone ##ₘ mtodo⌝ ∗ I mtodo mdone)%I
           with "Hm [HI]").
  { iExists m.1; iFrame.
    iPureIntro.
    rewrite left_id_L.
    split; auto.
    apply map_disjoint_empty_l. }
  { clear Φ.
    iIntros (m' k v) "!>".
    destruct m as [m def].
    iIntros (Φ) "[HI %] HΦ".
    iDestruct "HI" as (mtodo) "[%Hunion HI]"; simpl in *.
    destruct Hunion as [<- Hdisj].
    destruct H as [Hnone Hsome].
    rewrite lookup_union in Hsome.
    rewrite Hnone /= in Hsome.
    rewrite left_id in Hsome.
    wp_apply ("Hbody" with "[$HI //]").
    iIntros "HI".
    iApply "HΦ".
    iExists _; iFrame.
    iPureIntro.
    split.
    + apply union_insert_delete; auto.
    + apply insert_delete_disjoint; auto. }
  iIntros "[Hm HI]".
  iDestruct "HI" as (mtodo) "[%Htodo HI]".
  iApply "HΦ"; iFrame.
  destruct Htodo.
  assert (mtodo = ∅).
  { destruct (decide (mtodo = ∅)); auto.
    destruct (map_choose mtodo) as (i & x & Hlookup); auto.
    pose proof Hlookup.
    eapply map_disjoint_Some_r in Hlookup; eauto.
    assert ( (m.1 ∪ mtodo) !! i = m.1 !! i) by congruence.
    rewrite Hlookup in H2.
    rewrite lookup_union_r // in H2.
    congruence. }
  subst.
  iFrame.
Qed.

Theorem wp_MapLen2 stk E mref q m :
  {{{
      own_map mref q m
  }}}
    (MapLen2 #mref) @ stk ; E
  {{{ (s: u64),
    RET #s; ⌜uint.nat s = size m.1⌝ ∗ own_map mref q m
  }}}.
Proof using IntoValComparable0.
  iIntros (Φ) "Hm HΦ".
  rewrite /MapLen2.
  wp_pures.
  wp_apply wp_alloc_untyped; first by done.
  iIntros (l) "Hlen".
  wp_pures.
  wp_apply (wp_MapIter_fold
              (λ m,
                ∃ (s: u64),
                  l ↦ #s ∗
                  ⌜uint.nat s = size m ∧ (uint.Z s < 2^64-1)%Z⌝)%I
  with "Hm [Hlen]").
  { (* I ∅ *)
    iExists (W64 0). iFrame.
    by iPureIntro. }
  { (* inductive step *)
    clear.
    iIntros (m0 _k _v Φ) "!> [HI [%Hk_not_in %Hk_some]] HΦ".
    iDestruct "HI" as (s) "[Hl [%Hs %Hs_bound]]".
    wp_pures.
    wp_apply (wp_load with "[$Hl]"); iIntros "Hl".
    wp_apply (wp_store with "[$Hl]"); iIntros "Hl".
    wp_apply (wp_load with "[$Hl]"); iIntros "Hl".
    wp_apply wp_Assume.
    iIntros (Hbounded_next%bool_decide_eq_true).
    iApply "HΦ".
    iExists _; iFrame.
    iPureIntro. split.
    - rewrite map_size_insert_None //.
      word.
    - revert Hbounded_next.
      word.
  }
  iIntros "[Hm HI]".
  iDestruct "HI" as (s) "[Hl [%Hs1 %Hs2]]".
  wp_apply (wp_load with "[$Hl]"); iIntros "Hl".
  iApply "HΦ"; iFrame.
  eauto.
Qed.

Global Instance own_map_persistent mref m : Persistent (own_map mref DfracDiscarded m).
Proof. apply _. Qed.

Lemma own_map_persist mref dq m :
  own_map mref dq m ==∗ own_map mref DfracDiscarded m.
Proof.
  rewrite /own_map.
  iIntros "H". iDestruct "H" as (mv) "[% H]".
  iMod (heap_pointsto_persist with "H") as "H".
  iModIntro.
  iExists _; iFrame. done.
Qed.

End heap.

Typeclasses Opaque own_map.

Arguments wp_NewMap {_ _ _ _ _ _ _} K {_ _ _}.
Arguments wp_MapGet {_ _ _ _ _ _} K {_ _ _ _}.
Arguments wp_MapInsert {_ _ _ _ _ _} K {_ _ _}.
Arguments wp_MapDelete {_ _ _ _ _ _} K {_ _ _ _}.
Arguments wp_MapLen {_ _ _ _ _ _} K {_ _ _ _}.
