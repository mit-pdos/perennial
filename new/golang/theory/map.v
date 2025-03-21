From Perennial.Helpers Require Import NamedProps.
From Perennial.goose_lang Require Import ipersist.
From New.golang.defn Require Export map.
From New.golang.theory Require Export list mem exception loop typing.
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

Local Definition is_map_val (mv : val) (m : gmap K V)
  (* these arguments are written out manually so that the type of m directs
  inferring kt and vt *)
 `{!IntoValTyped K kt} `{!IntoValTyped V vt}
  : Prop :=
  ∀ (k : K),
  (fix go (mv : val) : Prop :=
     match mv with
     | InjLV d => (m !! k = None) ∧ d = #(default_val V)
     | InjRV ((kv', vv'), mv) =>
         ∃ k' v', kv' = #k' ∧ vv' = #v' ∧
                  if decide (k = k') then m !! k = Some v'
                  else go mv
     | _ => False
     end
  ) mv.

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
  rewrite /is_map_val.
  split; first done.
  intros k'.
  destruct (decide (k = k')).
  - subst. eexists _, _. split_and!; try reflexivity. rewrite decide_True //. rewrite lookup_insert //.
  - eexists _, _. split_and!; try reflexivity. rewrite decide_False //.
    + rewrite lookup_insert_ne //. apply Hm.
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
  wp_pures.
Admitted.

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
  iSpecialize ("HΦ" with "[Hm]").
  { iFrame "∗%". }
  wp_pure.
  specialize (Hm k).
  iLöb as "IH" forall (v Hm Φ).
  wp_pures.
  simpl in Hm.
  destruct v; try by exfalso.
  - wp_pures.
    destruct Hm as [-> ->]. done.
  - destruct v; try by exfalso.
    destruct v1; try by exfalso.
    destruct Hm as (? & ? & -> & -> & Hm).
    subst.
    wp_pures.
    simpl.
    destruct (decide (k = x)); subst.
    + rewrite !bool_decide_eq_true_2 //.
      wp_pures.
      rewrite Hm. done.
    + rewrite -> (bool_decide_eq_false_2 (k = x)) by congruence.
      wp_pure.
      iApply ("IH" with "[//] HΦ").
Qed.

Lemma wp_map_make :
  is_comparable_go_type kt = true →
  {{{ True }}}
    map.make kt vt #()
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
  split; first done.
  unfold is_map_val.
  intros ?.
  by rewrite default_val_eq_zero_val.
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
