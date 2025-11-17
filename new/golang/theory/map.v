From New.golang.defn Require Export map.
From New.golang.theory Require Export array predeclared auto.

Set Default Proof Using "Type".

Section defns_and_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {core_sem : go.CoreSemantics}
  {pre_sem : go.PredeclaredSemantics}
  {array_sem : go.ArraySemantics}
  {map_sem : go.MapSemantics}.

Local Set Default Proof Using "Type core_sem pre_sem array_sem map_sem".

Lemma wp_InternalMapDomain mv m :
  {{{ ⌜ go.is_map_pure mv m ⌝  }}}
    InternalMapDomain mv
  {{{ ks, RET (ArrayV ks); ⌜ is_map_domain mv ks ⌝ }}}.
Proof.
  iIntros (?) "% HΦ".
  wp_apply (wp_GoInstruction []).
  { intros.
    unshelve epose proof (go.is_map_domain_exists _ _ _) as [? ?];
      last (by repeat econstructor); done. }
  iIntros "* %Hstep".
  inv Hstep. inv Hpure.
  iIntros "? $ !>". simpl. wp_pures. iApply "HΦ". done.
Qed.


(* NOTE: we assume EqDecision explicitly here even though it is also available
through [IntoValTyped K kt] so that the instance used to type-check [gmap K V]
is independent of the [IntoValTyped] instance. Otherwise, these proofs end up
relying on a [gmap] with a particular proof of [EqDecision K]. *)
Context `{!IntoVal K} `{!EqDecision K} `{!Countable K} `{!IntoVal V}
  `{!Inj (=) (=) (into_val (V:=K))}.

Definition own_map_def mptr dq (m : gmap K V) : iProp Σ :=
  ∃ (mv : val) mp,
    "Hown" ∷ heap_pointsto mptr dq mv ∗
    "%His_map" ∷ ⌜ go.is_map_pure mv mp ⌝ ∗
    "%Hagree" ∷ ⌜ ∀ k, mp #k = (match m !! k with
                                | None => (false, #(zero_val V))
                                | Some v => (true, #v)
                                end) ⌝ ∗
    "%Hdefault" ∷ ⌜ go.map_default mv = #(zero_val V) ⌝.
Program Definition own_map := sealed @own_map_def.
Definition own_map_unseal : own_map = _ := seal_eq _.
Arguments own_map mptr dq m.

Notation "mref ↦$ dq m" := (own_map mref dq m)
                            (at level 20, dq custom dfrac at level 50, format "mref  ↦$ dq  m").

(*
Global Instance wp_kv_entry_pure_wp {A B:Type} `{!IntoVal A} `{!IntoVal B} (a: A) (b: B) :
  PureWp True ((map.kv_entry #a #b)%E) (#(a, b)).
Proof.
  pure_wp_start.
  rewrite map.kv_entry_unseal.
  unfold map.kv_entry_def.
  wp_pure_lc "?".
  wp_pures.
  rewrite [in #(_, _)]to_val_unseal /=.
  iApply "HΦ".
  done.
Qed.

Lemma wp_map_literal_val (l:list (K * V)):
  {{{ True }}}
    map.literal_val vt #l
  {{{ v, RET v; ⌜ is_map_val v (list_to_map l) ⌝ }}}.
Proof.
  iIntros (?) "% HΦ".
  iInduction l as [| h tl] "IH" forall (Φ).
  + wp_call.
    iApply "HΦ".
    iPureIntro.
    unfold is_map_val.
    done.
  + wp_call.
    wp_bind (map.literal_val _ _)%E.
    iApply ("IH" with "[HΦ]"). iNext.
    iIntros (?) "%Htl_map".
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    destruct h as [hk hv].
    rewrite to_val_unseal.
    simpl.
    exists hk, hv, (list_to_map tl).
    split; first reflexivity.
    split; first reflexivity.
    split.
    - destruct v; try by exfalso.
      * done.
      * done.
    - reflexivity.
Qed

Lemma wp_map_literal (l:list (K * V)):
  {{{ ⌜ is_comparable_go_type kt = true ⌝ }}}
    map.literal vt #l
  {{{ (l_ptr : loc), RET #l_ptr; l_ptr ↦$ (list_to_map l) }}}.
Proof.
  iIntros (?) "%Hcomp HΦ".
  wp_call.
  wp_apply wp_map_literal_val.
  iIntros (v) "%Hmv".
  iApply (wp_alloc_untyped with "[//]").
  { instantiate (1:=v). by destruct v. }
  iNext.
  iIntros (?) "Hm".
  rewrite to_val_unseal.
  iApply "HΦ".
  rewrite own_map_unseal.
  iUnfold own_map_def.
  iExists v.
  iFrame.
  done.
Qed. *)

Lemma wp_map_insert l (m : gmap K V) k v :
  {{{ l ↦$ m }}}
    map.insert #l #k #v
  {{{ RET #(); l ↦$ <[k := v]> m }}}.
Proof using Inj0.
  rewrite own_map_unseal.
  iIntros (?) "Hm HΦ".
  iNamed "Hm". wp_call.
  wp_apply (_internal_wp_untyped_read with "Hown"). iIntros "Hown".
  wp_auto.
  wp_apply (_internal_wp_untyped_store with "Hown"). iIntros "Hown".
  iApply "HΦ". iFrame "Hown".
  iPureIntro. eexists _. split_and!.
  - apply go.is_map_pure_map_insert. done.
  - intros k'. simpl. destruct decide.
    + assert (k = k') by naive_solver. subst. rewrite lookup_insert_eq //.
    + rewrite lookup_insert_ne; last naive_solver. apply Hagree.
  - by rewrite go.map_default_map_insert.
Qed.

Local Instance delete_unfold key_type elem_type :
  FuncUnfold go.delete [go.TypeLit $ go.MapType key_type elem_type] _ :=
  ltac:(constructor; apply go.delete_map).
Lemma wp_map_delete l (m : gmap K V) k key_type elem_type :
  {{{ l ↦$ m }}}
    #(functions go.delete [go.TypeLit $ go.MapType key_type elem_type])
        #l #k
  {{{ RET #(); l ↦$ delete k m }}}.
Proof using Inj0.
  wp_start as "Hm". rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_read with "Hown"). iIntros "Hown".
  wp_pures.
  wp_apply (_internal_wp_untyped_store with "Hown"). iIntros "Hown".
  iApply "HΦ". iFrame "Hown".
  iPureIntro. eexists. split_and!.
  - by apply go.is_map_pure_map_delete.
  - intros k'. simpl. destruct decide.
    + assert (k' = k) by naive_solver. subst. rewrite lookup_delete_eq Hdefault //.
    + rewrite lookup_delete_ne; last naive_solver. apply Hagree.
  - by rewrite go.map_default_map_delete.
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
