From iris.proofmode Require Import coq_tactics reduction.
From Perennial.goose_lang Require Import notation proofmode typing.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Import map.impl.
From Perennial.goose_lang.lib Require map.map.
Import uPred.

From iris_string_ident Require Import ltac2_string_ident.

Set Default Proof Using "Type".

Class IntoVal {ext: ext_op} V :=
  { to_val: V -> val;
    IntoVal_def: V;
  }.

Class IntoValForType {ext V} (H: @IntoVal ext V) {ext_ty: ext_types ext} (t:ty) :=
    { def_is_zero: to_val IntoVal_def = zero_val t;
      (* TODO: this isn't necessary, but it seems reasonable *)
      to_val_ty: forall v, val_ty (to_val v) t; }.

Instance u64_IntoVal {ext: ext_op} : IntoVal u64 :=
  {| to_val := λ (x: u64), LitV (LitInt x);
     IntoVal_def := U64 0; |}.

Instance u64_IntoVal_uint64T {ext} {ext_ty: ext_types ext} : IntoValForType u64_IntoVal uint64T.
Proof.
  constructor; auto.
Qed.

Module Map.
  Definition t V {ext} `{@IntoVal ext V} := gmap u64 V.
  Definition untype `{IntoVal V}:
    t V -> gmap u64 val * val :=
    fun m => (to_val <$> m, to_val IntoVal_def).
End Map.

Section heap.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.

Context `{!IntoVal V}.
Context `{!IntoValForType IntoVal0 t}.

Implicit Types (m: Map.t V) (k: u64) (v:V).

Definition map_get m k : V * bool :=
  let r := default IntoVal_def (m !! k) in
  let ok := bool_decide (is_Some (m !! k)) in
  (r, ok).

Definition map_insert m k v : Map.t V :=
  <[ k := v ]> m.

Definition map_del m k : Map.t V :=
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
  m !! k = None ∧ v = IntoVal_def.
Proof.
  rewrite /map_get.
  destruct (m !! k); rewrite /=.
  - congruence.
  - intuition congruence.
Qed.

Definition is_tmap (mref:loc) (m: Map.t V) :=
  map.is_map mref (Map.untype m).

Theorem is_map_untype mref m : is_tmap mref m -∗ map.is_map mref (Map.untype m).
Proof.
  auto.
Qed.

Theorem is_map_retype mref m : map.is_map mref (to_val <$> m, to_val IntoVal_def) -∗ is_tmap mref m.
Proof.
  auto.
Qed.

Ltac untype :=
  rewrite /is_tmap /Map.untype.

Theorem wp_NewMap stk E :
  {{{ True }}}
    NewMap t @ stk; E
  {{{ mref, RET #mref;
      is_tmap mref ∅ }}}.
Proof using IntoValForType0.
  iIntros (Φ) "_ HΦ".
  wp_apply map.wp_NewMap.
  iIntros (mref) "Hm".
  iApply "HΦ".
  iApply is_map_retype.
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

Theorem wp_MapGet stk E mref m k :
  {{{ is_tmap mref m }}}
    MapGet #mref #k @ stk; E
  {{{ v ok, RET (to_val v, #ok);
      ⌜map_get m k = (v, ok)⌝ ∗
      is_tmap mref m }}}.
Proof.
  iIntros (Φ) "Hm HΦ".
  iDestruct (is_map_untype with "Hm") as "Hm".
  wp_apply (map.wp_MapGet with "Hm").
  iIntros (vv ok) "(%Hmapget&Hm)".
  apply map_get_fmap in Hmapget as [v [-> Hmapget]].
  iApply "HΦ".
  iSplit; [ auto | ].
  iApply (is_map_retype with "Hm").
Qed.

Theorem map_insert_fmap m k v' :
  map.map_insert (Map.untype m) k (to_val v') =
  Map.untype (map_insert m k v').
Proof.
  untype.
  rewrite /map.map_insert /map_insert.
  rewrite fmap_insert //.
Qed.

Theorem wp_MapInsert stk E mref m k v' vv :
  vv = to_val v' ->
  {{{ is_tmap mref m }}}
    MapInsert #mref #k vv @ stk; E
  {{{ RET #(); is_tmap mref (map_insert m k v') }}}.
Proof.
  intros ->.
  iIntros (Φ) "Hm HΦ".
  iDestruct (is_map_untype with "Hm") as "Hm".
  wp_apply (map.wp_MapInsert with "Hm").
  iIntros "Hm".
  iApply "HΦ".
  rewrite map_insert_fmap.
  iApply (is_map_retype with "Hm").
Qed.

End heap.
