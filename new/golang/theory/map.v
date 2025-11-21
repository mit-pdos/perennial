From New.golang.defn Require Export map.
From New.golang.theory Require Export mem array predeclared auto slice.

Set Default Proof Using "Type".

Section defns_and_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {core_sem : go.CoreSemantics}
  {pre_sem : go.PredeclaredSemantics}
  {array_sem : go.ArraySemantics}
  {slice_sem : go.SliceSemantics}
  {map_sem : go.MapSemantics}.

Local Set Default Proof Using "Type core_sem pre_sem array_sem slice_sem map_sem".

(* TODO: reading from nil map. Want to say that an owned map is not nil, which
   requires knowing that wp_ref gives non-null pointers. *)

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
  iIntros "? $ !>". simpl. wp_auto. iApply "HΦ". done.
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
    "%Hdom" ∷ ⌜ ∀ kv, (mp kv).1 = true → ∃ (k : K), kv = #k ⌝ ∗
    "%Hdefault" ∷ ⌜ go.map_default mv = #(zero_val V) ⌝.
Program Definition own_map := sealed @own_map_def.
Definition own_map_unseal : own_map = _ := seal_eq _.

#[global] Instance own_map_timeless mptr dq (m: gmap K V)
  : Timeless (own_map mptr dq m).
Proof. rewrite own_map_unseal. apply _. Qed.

Notation "mref ↦$ dq m" := (own_map mref dq m)
                            (at level 20, dq custom dfrac at level 50, format "mref  ↦$ dq  m").

Class SafeMapKey key_type (k : K) :=
  {
    safe_map_go_eq :
      ∃ b, IsGoEq key_type #k #k b;
  }.

Global Instance safe_map_key_is_go_eq key_type k b :
  IsGoEq key_type #k #k b → SafeMapKey key_type k.
Proof.
  intros ?. constructor. by eexists.
Qed.

Lemma wp_map_insert key_type l (m : gmap K V) k v {Hsafe : SafeMapKey key_type k} :
  {{{ l ↦$ m }}}
    map.insert key_type #l #k #v
  {{{ RET #(); l ↦$ <[k := v]> m }}}.
Proof using Inj0.
  destruct Hsafe as [[? Hsafe]].
  rewrite own_map_unseal.
  iIntros (?) "Hm HΦ". iNamed "Hm". wp_call.
  wp_apply (_internal_wp_untyped_read with "Hown"). iIntros "Hown".
  wp_auto.
  wp_apply (_internal_wp_untyped_store with "Hown"). iIntros "Hown".
  iApply "HΦ". iFrame "Hown".
  iPureIntro. eexists _. split_and!.
  - apply go.is_map_pure_map_insert. done.
  - intros k'. simpl. destruct decide.
    + assert (k = k') by naive_solver. subst. rewrite lookup_insert_eq //.
    + rewrite lookup_insert_ne; last naive_solver. apply Hagree.
  - simpl. intros kv. destruct decide; naive_solver.
  - by rewrite go.map_default_map_insert.
Qed.

Local Instance delete_unfold key_type elem_type :
  FuncUnfold go.delete [go.TypeLit $ go.MapType key_type elem_type] _ :=
  ltac:(constructor; apply go.delete_map).
Lemma wp_map_delete l (m : gmap K V) k key_type elem_type {Hsafe : SafeMapKey key_type k} :
  {{{ l ↦$ m }}}
    #(functions go.delete [go.TypeLit $ go.MapType key_type elem_type])
        #l #k
  {{{ RET #(); l ↦$ delete k m }}}.
Proof using Inj0.
  destruct Hsafe as [[? Hsafe]].
  wp_start as "Hm". rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_read with "Hown") as "Hown".
  wp_apply (_internal_wp_untyped_store with "Hown") as "Hown".
  iApply "HΦ". iFrame "Hown".
  iPureIntro. eexists. split_and!.
  - by apply go.is_map_pure_map_delete.
  - intros k'. simpl. destruct decide.
    + assert (k' = k) by naive_solver. subst. rewrite lookup_delete_eq Hdefault //.
    + rewrite lookup_delete_ne; last naive_solver. apply Hagree.
  - simpl. intros kv. destruct decide; naive_solver.
  - by rewrite go.map_default_map_delete.
Qed.

Lemma wp_map_lookup2 key_type elem_type mref (m : gmap K V) k dq {Hsafe : SafeMapKey key_type k} :
  {{{ mref ↦${dq} m }}}
    map.lookup2 key_type elem_type #mref #k
  {{{ RET (#(default (zero_val V) (m !! k)), #(bool_decide (is_Some (m !! k)))); mref ↦${dq} m }}}.
Proof.
  destruct Hsafe as [[? Hsafe]].
  wp_start as "Hm". rewrite own_map_unseal. iNamed "Hm".
  iDestruct (heap_pointsto_non_null with "Hown") as "%H".
  rewrite go.go_eq_map_nil_l. wp_if_destruct.
  { exfalso. done. }
  wp_apply (_internal_wp_untyped_read with "Hown") as "Hown".
  erewrite go.map_lookup_pure; last done.
  pose proof (Hagree k) as Heq. rewrite Heq. destruct (m !! k); wp_auto.
  + iApply "HΦ". iFrame "∗#%".
  + iApply "HΦ". iFrame "∗#%".
Qed.

Global Instance pure_wp_map_nil_lookup2 key_type elem_type k
  `{!TypedPointsto V} `{!IntoValTyped V elem_type}
  {Hsafe : SafeMapKey key_type k} :
  PureWp True (map.lookup2 key_type elem_type #map.nil #k) (#(zero_val V), #false)%V.
Proof.
  destruct Hsafe as [[? Hsafe]].
  pure_wp_start.
  rewrite go.go_eq_map_nil_l. wp_if_destruct.
  2:{ exfalso. done. }
  wp_alloc tmp as "?". wp_auto. by iApply "HΦ".
Qed.

Lemma wp_map_lookup1 key_type elem_type mref (m : gmap K V) k dq {Hsafe : SafeMapKey key_type k} :
  {{{ mref ↦${dq} m }}}
    map.lookup1 key_type elem_type #mref #k
  {{{ RET (#(default (zero_val V) (m !! k))); mref ↦${dq} m }}}.
Proof.
  wp_start as "Hm". wp_apply (wp_map_lookup2 with "Hm") as "Hm". by iApply "HΦ".
Qed.

Global Instance pure_wp_map_nil_lookup1 key_type elem_type k
  `{!TypedPointsto V} `{!IntoValTyped V elem_type}
  {Hsafe : SafeMapKey key_type k} :
  PureWp True (map.lookup1 key_type elem_type #map.nil #k) #(zero_val V).
Proof. by pure_wp_start. Qed.

Local Instance make2_unfold key_type elem_type :
  FuncUnfold go.make2 [go.TypeLit $ go.MapType key_type elem_type] _ :=
  ltac:(constructor; apply go.make2_map).
Lemma wp_map_make2 (len : w64) key_type elem_type
  `{!TypedPointsto V} `{!IntoValTyped V elem_type} :
  {{{ True }}}
    #(functions go.make2 [go.TypeLit $ go.MapType key_type elem_type]) #len
  {{{ mref, RET #mref; mref ↦$ (∅ : gmap K V) }}}.
Proof.
  wp_start. wp_alloc tmp as "?". wp_auto.
  epose proof (go.is_map_pure_map_empty _).
  iApply wp_alloc_untyped; try done.
  { erewrite go.is_map_pure_flatten; done. }
  iNext.
  iIntros (?) "Hl".
  replace (LitV l) with #l; last by rewrite into_val_unseal.
  iApply "HΦ". rewrite own_map_unseal.
  iFrame "∗%". iPureIntro. split.
  - intros. rewrite lookup_empty //.
  - rewrite go.map_default_map_empty //.
Qed.

Local Instance make1_unfold key_type elem_type :
  FuncUnfold go.make1 [go.TypeLit $ go.MapType key_type elem_type] _ :=
  ltac:(constructor; apply go.make1_map).
Lemma wp_map_make1 key_type elem_type
  `{!TypedPointsto V} `{!IntoValTyped V elem_type} :
  {{{ True }}}
    #(functions go.make1 [go.TypeLit $ go.MapType key_type elem_type]) #()
  {{{ mref, RET #mref; mref ↦$ (∅ : gmap K V) }}}.
Proof. wp_start. by wp_apply wp_map_make2. Qed.

Lemma own_map_not_nil mref m dq :
  mref ↦${dq} m -∗ ⌜ mref ≠ map.nil ⌝.
Proof.
  rewrite own_map_unseal. iNamed 1. iDestruct (heap_pointsto_non_null with "Hown") as "$".
Qed.

Lemma wp_map_for_range (body : func.t) key_type elem_type mref m dq
  `{!TypedPointsto K} `{!IntoValTyped K key_type} :
  ∀ Φ,
  mref ↦${dq} m -∗
  (∀ keys_sl keys,
     ⌜ list_to_set keys = dom m ∧ length keys = size m ∧ NoDup keys ⌝ ∗
     keys_sl ↦[key_type]* keys -∗
     WP slice.for_range key_type
        (# {|
              func.f := <>;
              func.x := <>;
              func.e := (λ: "k"%string, # body "k"%string (map.lookup1 key_type elem_type (# mref) "k"%string))%E
            |}) (# keys_sl) {{ v, mref ↦${dq} m -∗ Φ v }}
  ) -∗
  WP map.for_range key_type elem_type #mref #body {{ Φ }}.
Proof using Inj0 pre_sem slice_sem.
  iIntros "% Hm HΦ".
  wp_call. rewrite go.go_eq_map_nil_l.
  iDestruct (own_map_not_nil with "[$]") as %?.
  wp_if_destruct; first by exfalso.
  rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_start_read with "Hown") as "Hown".
  wp_apply (wp_InternalMapDomain with "[//]"). iIntros "%ks %Hdom'".
  eapply go.is_map_domain_pure in Hdom'; last done.
  destruct Hdom' as [Hks_nodup Hks].
  assert (Forall (λ kv, ∃ (k : K), kv = #k) ks) as Heq.
  { rewrite Forall_forall. intros kv. rewrite -list_elem_of_In.
    intros Hk. specialize (Hks kv). specialize (Hdom kv).
    rewrite -Hks in Hk. apply Hdom in Hk. done. }
  apply Forall_exists_Forall2_l in Heq as [keys Heq].
  apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
  rewrite list_fmap_id in Heq. subst.
  wp_apply wp_slice_literal. iIntros "%keys_sl keys_sl". wp_auto.
  wp_bind (slice.for_range _ _ _).
  iSpecialize ("HΦ" with "[$keys_sl]").
  { iPureIntro.
    eassert _ as Hl.
    2:{ split; first eexact Hl.
        apply NoDup_fmap in Hks_nodup; last tc_solve.
        rewrite <- (size_list_to_set (C:=gset K)); last done.
        rewrite Hl. rewrite size_dom //. }
    rewrite sets.set_eq. intros k.
    rewrite elem_of_list_to_set.
    specialize (Hks #k). specialize (Hagree k).
    rewrite list_elem_of_fmap_inj in Hks.
    rewrite -Hks. rewrite Hagree. rewrite elem_of_dom.
    by destruct lookup.
  }
  iApply (wp_wand with "HΦ").
  iIntros "% HΦ". wp_auto. wp_apply "Hown" as "Hown".
  iApply "HΦ". iFrame "∗#%".
Qed.

Lemma wp_map_composite_literal key_type elem_type (kvs : list (K * V))
  `{!TypedPointsto V} `{!IntoValTyped V elem_type} :
  {{{ ⌜ Forall (λ '(pair k v), SafeMapKey key_type k) kvs ⌝ }}}
    composite_literal (go.MapType key_type elem_type) (ArrayV ((λ '(pair k v), (#k,#v)%V) <$> kvs))
  {{{ mref, RET #mref; mref ↦$ (foldl (λ m '(pair k v), insert k v m) ∅ kvs) }}}.
Proof using Inj0 array_sem core_sem pre_sem slice_sem.
  wp_start as "%Hsafe".
  rewrite go.composite_literal_map.
  wp_auto. wp_apply wp_map_make1.
  iIntros "%mref Hm". wp_auto.
  replace (subst "m" #mref _) with
    (foldl
       (λ (expr_so_far : expr) (kv : val), expr_so_far;; map.insert key_type #mref (Fst kv) (Snd kv))
       (# ()) ((λ '(pair k v), (# k, # v)%V) <$> kvs))%E.
  2:{ induction kvs using rev_ind; try done.
      simpl. rewrite fmap_app !foldl_snoc /=.
      rewrite IHkvs //. rewrite Forall_app in Hsafe. naive_solver. }
  wp_bind (foldl _ _ _).
  iApply (wp_wand _ _ _ (λ _, _)%I with "[-HΦ] [HΦ]").
  2:{ iIntros "% H". simpl. wp_auto. iApply "HΦ". iAccu. }
  clear Φ.
  iInduction kvs as [|] "IH" using rev_ind.
  - simpl. wp_auto. iFrame.
  - rewrite fmap_app !foldl_snoc.
    wp_bind (foldl _ _ _). apply Forall_app in Hsafe as [Hsafe Hsafe'].
    destruct x. rewrite Forall_singleton in Hsafe'.
    iSpecialize ("IH" with "[//] [$]").
    Search (Forall _ [_]).
    iApply (wp_wand with "IH"). iIntros "% H". wp_auto.
    wp_apply (wp_map_insert with "[$]") as "Hm".
    iFrame.
Qed.

Global Instance wp_map_nil_for_range (body : func.t) key_type elem_type :
  PureWp True (map.for_range key_type elem_type #map.nil #body) execute_val.
Proof.
  pure_wp_start. rewrite go.go_eq_map_nil_l. by wp_if_destruct.
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
  rewrite own_map_unseal /own_map_def. iNamed 1.
  iPersist "Hown". iModIntro. eauto.
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

Module test_own_map.
  Section proof.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
    {map_sem : go.MapSemantics}.
  Definition foo (mref: loc) (m: gmap w64 w64): iProp Σ :=
    own_map mref DfracDiscarded m.
  End proof.
End test_own_map.
