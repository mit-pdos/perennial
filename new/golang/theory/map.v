From Perennial.Helpers Require Import NamedProps.
From Perennial.goose_lang Require Import ipersist.
From New.golang.defn Require Export map.
From New.golang.theory Require Import list mem exception loop typing.
From Perennial Require Import base.

Transparent map.insert map.get map.delete map.for_range map.len map.make.

Set Default Proof Using "Type".

Section defns_and_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

(* NOTE: we assume EqDecision explicitly here even though it is also available
through [IntoValTyped K kt] so that the instance used to type-check [gmap K V]
is independent of the [IntoValTyped] instance. Otherwise, these proofs end up
relying on a [gmap] with a particular proof of [EqDecision K]. *)
Context `{!IntoVal K} `{!EqDecision K} `{!Countable K} `{!IntoVal V}.

Local Fixpoint is_map_val (mv : val) (m : gmap K V) `{!IntoValTyped V vt} `{!IntoValTyped K kt} : Prop :=
  match mv with
  | InjLV d => m = ∅ ∧ d = #(default_val V)
  | InjRV ((kv', vv'), mv') =>
      (∃ k' v' m', kv' = #k' ∧ vv' = #v' ∧ is_map_val mv' m' ∧ m = <[k' := v']> m')
  | _ => False
end
.

Fixpoint map_list_val_def (m : list (K * V)) : val :=
  match m with
  | [] => InjLV #()
  | h :: tl => InjRV ((#(fst h), #(snd h)), map_list_val_def tl)
  end.
Program Definition map_list_val := sealed @map_list_val_def.
Definition map_list_val_unseal : map_list_val = _ := seal_eq _.

Definition own_map_def mptr dq (m : gmap K V)
 `{!IntoValTyped K kt} `{!IntoValTyped V vt}
  : iProp Σ :=
  ∃ (v : val) ,
    heap_pointsto mptr dq v ∗
    ⌜ is_comparable_go_type kt = true ⌝ ∗
    ⌜ is_map_val v m ⌝.
Program Definition own_map := sealed @own_map_def.
Definition own_map_unseal : own_map = _ := seal_eq _.

Arguments own_map mptr dq m {kt IntoValTyped0 vt IntoValTyped1}.

Context `{!IntoValTyped K kt} `{!IntoValTyped V vt}.
Notation "mref ↦$ dq m" := (own_map mref dq m)
                            (at level 20, dq custom dfrac at level 50, format "mref  ↦$ dq  m").

Lemma wp_map_literal_val (l:list (K * V)):
  {{{ True }}}
    map.literal_val #kt #vt (map_list_val l)
  {{{ v, RET v; ⌜ is_map_val v (list_to_map l) ⌝ }}}.
Proof. 
  iIntros (?) "_ HΦ".
  iInduction l as [| h tl] "IH" forall (Φ).
  + wp_call.
    rewrite map_list_val_unseal /=.
    rewrite list.Match_unseal /=.
    wp_call_lc "?".
    iApply "HΦ".
    iPureIntro.
    unfold is_map_val. 
    split.
    - done.
    - symmetry. apply default_val_eq_zero_val.
  + wp_call.
    rewrite map_list_val_unseal /=.
    rewrite list.Match_unseal /=.
    wp_call_lc "?".
    wp_bind (map.literal_val _ _ _)%E. 
    iApply ("IH" with "[HΦ]"). iNext.
    iIntros (?) "%Htl_map".
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    unfold is_map_val.
    exists (fst h), (snd h), (list_to_map tl).
    split; first reflexivity.
    split; first reflexivity.
    split.
    - destruct v; try by exfalso.
      * done.
      * done.
    - reflexivity.
Qed. 
     
Lemma wp_map_literal (l:list (K * V)):
  {{{ ⌜ is_comparable_go_type kt = true ⌝ }}}
    map.literal #kt #vt (map_list_val l)
    (* Should the return be LitV l or #l? I tend to think #l but I changed it to
       match wp_alloc_untyped's return structure *)
  {{{ l_ptr, RET (LitV l_ptr); l_ptr ↦$ (list_to_map l) }}}.
Proof.
  iIntros (?) "%Hcomp HΦ".
  wp_call.
  wp_apply wp_map_literal_val.
  iIntros (v) "%Hmv".
  iApply (wp_alloc_untyped with "[//]").
  { instantiate (1:=v). by destruct v. }
  iNext.
  iIntros (?) "Hm".
  iApply "HΦ".
  rewrite own_map_unseal.
  iUnfold own_map_def.
  iExists v.
  iFrame.
  done.
Qed.

Lemma wp_map_insert l (m : gmap K V) k v :
  {{{ l ↦$ m }}}
    map.insert #l #k #v
  {{{ RET #(); l ↦$ <[k := v]> m }}}.
Proof.
  rewrite [in #l]to_val_unseal own_map_unseal.
  iIntros (?) "Hm HΦ".
  iDestruct "Hm" as (?) "(Hm & % & %Hm)".
  wp_call.
  wp_bind (! _)%E.
  iApply (wp_load with "[$]"). iNext.
  iIntros "Hm".
  wp_pures.
  wp_apply (wp_store with "[$]").
  iIntros "?".
  rewrite [in #()]to_val_unseal.
  iApply "HΦ".
  iFrame. iPureIntro.
  naive_solver.
Qed.

Lemma wp_map_delete_aux (v: val) (k: K) (m: gmap K V) :
  {{{ ⌜ is_map_val v m ⌝ ∗
      ⌜ is_comparable_go_type kt = true ⌝ }}}
    map.delete_aux v #k
  {{{ vd, RET vd; ⌜is_map_val vd (delete k m)⌝ }}}.
Proof.
  iIntros (Φ) "[%Hm %Hcmp] HΦ".
  iLöb as "IH" forall (v m Hm Φ).
  wp_call.
  destruct v; try by exfalso.
  - wp_pures. iApply "HΦ". iPureIntro. naive_solver.
  - wp_pures. destruct v; try by exfalso. destruct v1; try by exfalso.
    destruct Hm as (k' & v' & ? & -> & -> & Hm' & ->).
    wp_pures.
    destruct (decide (k = k')).
    + subst. wp_pures. rewrite bool_decide_eq_true_2; eauto. wp_pures.
      iApply ("IH" with "[]"); first eauto.
      iNext. iIntros (vd ?). iApply "HΦ". rewrite delete_insert_eq. done.
    + rewrite bool_decide_eq_false_2; eauto. wp_pures.
      wp_bind.
      iApply ("IH" with "[]"); first eauto.
      iNext. iIntros (vd Hvd). wp_pures. iApply "HΦ". iPureIntro.
      rewrite delete_insert_ne //. naive_solver.
Qed.

Lemma wp_map_delete l (m : gmap K V) k :
  {{{ l ↦$ m }}}
    map.delete #l #k
  {{{ RET #(); l ↦$ delete k m }}}.
Proof.
  rewrite [in #l]to_val_unseal own_map_unseal.
  iIntros (?) "Hm HΦ".
  iDestruct "Hm" as (?) "(Hm & % & %Hm)".
  wp_call.
  wp_bind (! _)%E.
  iApply (wp_load with "[$]"). iNext.
  iIntros "Hm".
  wp_bind.
  iApply (wp_map_delete_aux); first eauto.
  iNext. iIntros (vd Hmd).
  iApply (wp_store with "[$]"). iNext.
  iIntros "Hm".
  rewrite [in #()]to_val_unseal.
  iApply "HΦ". iFrame. done.
Qed.

Lemma wp_map_get l (m : gmap K V) k dq :
  {{{ l ↦${dq} m }}}
    map.get #l #k
  {{{ RET (#(default (default_val V) (m !! k)), #(bool_decide (is_Some (m !! k)))); l ↦${dq} m }}}.
Proof.
  rewrite own_map_unseal.
  iIntros (?) "Hm HΦ".
  iDestruct "Hm" as (?) "(Hm & % & %Hm)".
  wp_call.
  wp_bind (! _)%E.
  rewrite [in #l]to_val_unseal /=.
  iApply (wp_load with "[$]").
  iIntros "!> Hm".
  wp_pure. iSpecialize ("HΦ" with "[Hm]").
  { iFrame "∗%". }
  iLöb as "IH" forall (v m Hm Φ).
  wp_pures. destruct v; try by exfalso.
  - wp_pures. destruct Hm as [-> ->]. done.
  - destruct v; try by exfalso.
    destruct v1; try by exfalso.
    destruct Hm as (k' & ? & ? & -> & -> & Hm & ->).
    wp_pures.
    destruct (decide (k = k')); subst.
    + rewrite lookup_insert_eq. rewrite !bool_decide_eq_true_2 //.
      wp_pures. done.
    + rewrite -> (bool_decide_eq_false_2 (k = k')) by congruence.
      rewrite lookup_insert_ne //.
      wp_pure. iApply ("IH" with "[//] HΦ").
Qed.

Lemma wp_map_make :
  is_comparable_go_type kt = true →
  {{{ True }}}
    map.make #kt #vt
  {{{ mref, RET #mref; mref ↦$ (∅ : gmap K V) }}}.
Proof.
  rewrite own_map_unseal.
  iIntros (??) "_ HΦ".
  wp_call.
  iApply wp_alloc_untyped; try done.
  iNext.
  iIntros (?) "Hl".
  replace (LitV l) with #l; last by rewrite to_val_unseal.
  iApply "HΦ".
  iFrame. iPureIntro.
  rewrite -default_val_eq_zero_val.
  naive_solver.
Qed.

#[global]
Instance own_map_discarded_persist mref m : Persistent (own_map mref DfracDiscarded m).
Proof.
  rewrite own_map_unseal.
  apply _.
Qed.

Lemma own_map_persist mref dq m :
  own_map mref dq m ==∗ own_map mref DfracDiscarded m.
Proof.
  rewrite own_map_unseal /own_map_def.
  iIntros "(%v & H & % & %)".
  iMod (heap_pointsto_persist with "H") as "H".
  iModIntro.
  iFrame.
  eauto.
Qed.

#[global]
Instance own_map_update_into_persistently mref dq m :
  UpdateIntoPersistently (own_map mref dq m) (own_map mref DfracDiscarded m).
Proof.
  red.
  iIntros "H".
  iMod (own_map_persist with "H") as "#H".
  iModIntro. iFrame "#".
Qed.

End defns_and_lemmas.

Notation "mref ↦$ dq m" := (own_map mref dq m)
                            (at level 20, dq custom dfrac at level 50, format "mref  ↦$ dq  m").

Arguments own_map {ext ffi ffi_interp0 Σ heapGS0} {K}%_type_scope
  {IntoVal0 EqDecision0 Countable0} {V}%_type_scope {IntoVal1} mptr dq m
  {kt IntoValTyped0 vt IntoValTyped1}.

Module test_own_map.
  Section proof.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Definition foo (mref: loc) (m: gmap w64 w64): iProp Σ :=
    own_map mref DfracDiscarded m.
  End proof.
End test_own_map.
