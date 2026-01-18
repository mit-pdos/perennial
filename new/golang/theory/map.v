From New.golang.defn Require Export map.
From New.golang.theory Require Export mem array predeclared auto.

Set Default Proof Using "Type".

Section safe_map_key.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext} {go_lctx : GoLocalContext}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.
Local Set Default Proof Using "All".
Class SafeMapKey {K} key_type (k : K) :=
  {
    safe_map_go_eq :
      ∃ (b : bool), go.GoExprEq (go_eq key_type #k #k) (#b);
  }.

Global Instance safe_map_key_is_go_eq {K} key_type (k : K) (b : bool) :
  go.GoExprEq (go_eq key_type #k #k) #b → SafeMapKey key_type k.
Proof.
  intros ?. constructor. by eexists.
Qed.
End safe_map_key.

Section defns_and_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.
Local Set Default Proof Using "All".

(* TODO: reading from nil map. Want to say that an owned map is not nil, which
   requires knowing that wp_ref gives non-null pointers. *)

Lemma wp_InternalMapForRange {stk E} mv m (body : val) key_type elem_type :
  ∀ Φ,
  (⌜ is_map_pure mv m ⌝)  -∗
  (∀ ks, ⌜ is_map_domain mv ks ⌝ -∗
         (WP foldr
            (λ (key0 : val) (remaining_loop : expr),
               let: "b" := body key0 (m key0).2 in
               if: Fst "b" =⟨go.string⟩ # "break"%go then return: (do: # ())
               else (do: # ()) ;;;
                      if: if: Fst "b" =⟨go.string⟩ # "continue"%go then # true
                          else Fst "b" =⟨go.string⟩ # "execute"%go
                      then ((λ: <>, remaining_loop)%V #()) else return: "b")
            (return: (do: # ())) ks
            @ stk; E {{ v, Φ v }})) -∗
  WP InternalMapForRange key_type elem_type (mv, body)%V @ stk; E {{ Φ }}.
Proof.
  iIntros (?) "% HΦ".
  wp_apply (wp_GoInstruction []).
  { intros.
    unshelve epose proof (go.is_map_domain_exists mv m H) as [? ?].
    repeat eexists.
    erewrite go.internal_map_domain_literal_step_pure; last done. repeat eexists; done. }
  iIntros "* %Hstep".
  simpl in *. erewrite go.internal_map_domain_literal_step_pure in Hstep; last done.
  destruct Hstep as (Hstep & ?). destruct Hstep as (? & ? & ?). subst.
  iIntros "? $ !>". iApply "HΦ". done.
Qed.

(* NOTE: we assume EqDecision explicitly here even though it is also available
through [IntoValTyped K kt] so that the instance used to type-check [gmap K V]
is independent of the [IntoValTyped] instance. Otherwise, these proofs end up
relying on a [gmap] with a particular proof of [EqDecision K]. *)
Context `[!ZeroVal K] `[!EqDecision K] `[!Countable K] `[!ZeroVal V]
  `[!go.IntoValInj K].

Definition own_map_def mptr dq (m : gmap K V) : iProp Σ :=
  ∃ (mv : val) mp,
    "Hown" ∷ heap_pointsto mptr dq mv ∗
    "%His_map" ∷ ⌜ is_map_pure mv mp ⌝ ∗
    "%Hagree" ∷ ⌜ ∀ k, mp #k = (match m !! k with
                                | None => (false, #(zero_val V))
                                | Some v => (true, #v)
                                end) ⌝ ∗
    "%Hdom" ∷ ⌜ ∀ kv, (mp kv).1 = true → ∃ (k : K), kv = #k ⌝ ∗
    "%Hdefault" ∷ ⌜ map_default mv = #(zero_val V) ⌝.
Program Definition own_map := sealed @own_map_def.
Definition own_map_unseal : own_map = _ := seal_eq _.

#[global] Instance own_map_timeless mptr dq (m: gmap K V)
  : Timeless (own_map mptr dq m).
Proof. rewrite own_map_unseal. apply _. Qed.

Notation "mref ↦$ dq m" := (own_map mref dq m)
                            (at level 20, dq custom dfrac at level 50, format "mref  ↦$ dq  m").

Lemma wp_map_insert key_type l (m : gmap K V) k v {Hsafe : SafeMapKey key_type k} :
  {{{ l ↦$ m }}}
    map.insert key_type #l #k #v
  {{{ RET #(); l ↦$ <[k := v]> m }}}.
Proof.
  destruct Hsafe as [[? Hsafe]].
  rewrite own_map_unseal.
  iIntros (?) "Hm HΦ". iNamed "Hm". wp_call. rewrite decide_True //. wp_auto.
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

Lemma wp_map_delete l (m : gmap K V) k key_type elem_type {Hsafe : SafeMapKey key_type k} :
  {{{ l ↦$ m }}}
    #(functions go.delete [go.MapType key_type elem_type])
        #l #k
  {{{ RET #(); l ↦$ delete k m }}}.
Proof.
  destruct Hsafe as [[? Hsafe]].
  wp_start as "Hm". rewrite own_map_unseal. iNamed "Hm". rewrite decide_True //. wp_auto.
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
  wp_start as "Hm".
  rewrite own_map_unseal. iNamed "Hm".
  iDestruct (heap_pointsto_non_null with "Hown") as "%H".
  rewrite decide_True //. wp_auto.
  wp_if_destruct; first by exfalso.
  wp_apply (_internal_wp_untyped_read with "Hown") as "Hown".
  erewrite go.map_lookup_pure; last done.
  pose proof (Hagree k) as Heq. rewrite Heq. destruct (m !! k); wp_auto.
  + iApply "HΦ". iFrame "∗#%".
  + iApply "HΦ". iFrame "∗#%".
Qed.

Global Instance pure_wp_map_nil_lookup2 key_type elem_type (k : K)
  `{!TypedPointsto V} `{!IntoValTyped V elem_type} `{!go.TypeRepr elem_type V}
  {Hsafe : SafeMapKey key_type k} :
  PureWp True (map.lookup2 key_type elem_type #map.nil #k) (#(zero_val V), #false)%V.
Proof.
  destruct Hsafe as [[? Hsafe]].
  pure_wp_start. rewrite decide_True //. wp_auto.
  by iApply "HΦ".
Qed.

Lemma wp_map_lookup1 key_type elem_type mref (m : gmap K V) k dq {Hsafe : SafeMapKey key_type k} :
  {{{ mref ↦${dq} m }}}
    map.lookup1 key_type elem_type #mref #k
  {{{ RET (#(default (zero_val V) (m !! k))); mref ↦${dq} m }}}.
Proof.
  wp_start as "Hm". wp_apply (wp_map_lookup2 with "Hm") as "Hm". by iApply "HΦ".
Qed.

Global Instance pure_wp_map_nil_lookup1 key_type elem_type (k : K)
  `{!TypedPointsto V} `{!IntoValTyped V elem_type} `{!go.TypeRepr elem_type V}
  {Hsafe : SafeMapKey key_type k} :
  PureWp True (map.lookup1 key_type elem_type #map.nil #k) #(zero_val V).
Proof. by pure_wp_start. Qed.

Lemma wp_map_make2 (len : w64) key_type elem_type
  `{!go.TypeRepr key_type K} (* to automatically fill in K *)
  `{!TypedPointsto V} `{!IntoValTyped V elem_type} `{!go.TypeRepr elem_type V} :
  {{{ True }}}
    #(functions go.make2 [go.MapType key_type elem_type]) #len
  {{{ mref, RET #mref; mref ↦$ (∅ : gmap K V) }}}.
Proof.
  wp_start.
  epose proof (go.is_map_pure_map_empty _).
  iApply wp_alloc_untyped; try done.
  { erewrite go.is_map_pure_flatten; done. }
  iNext.
  iIntros (?) "Hl".
  replace (LitV l) with #l; last by rewrite go.into_val_unfold.
  iApply "HΦ". rewrite own_map_unseal.
  iFrame "∗%". iPureIntro. split.
  - intros. rewrite lookup_empty //.
  - rewrite go.map_default_map_empty //.
Qed.

Lemma wp_map_make1 key_type elem_type
  `{!go.TypeRepr key_type K} `{!TypedPointsto V}
  `{!IntoValTyped V elem_type} `{!go.TypeRepr elem_type V} :
  {{{ True }}}
    #(functions go.make1 [go.MapType key_type elem_type]) #()
  {{{ mref, RET #mref; mref ↦$ (∅ : gmap K V) }}}.
Proof. wp_start. by wp_apply wp_map_make2. Qed.

Lemma wp_map_clear mref (m : gmap K V) key_type elem_type
  `{!go.TypeRepr key_type K} `{!TypedPointsto V}
  `{!IntoValTyped V elem_type} `{!go.TypeRepr elem_type V} :
  {{{ mref ↦$ m }}}
    #(functions go.clear [go.MapType key_type elem_type]) #mref
  {{{ RET #(); mref ↦$ ∅ }}}.
Proof.
  rewrite own_map_unseal. iIntros (?) "Hm HΦ".
  rewrite func_unfold. wp_auto. iNamed "Hm".
  wp_apply wp_map_make1. iIntros "% Hm'".
  rewrite own_map_unseal. iNamedSuffix "Hm'" "_2".
  wp_apply (_internal_wp_untyped_read with "Hown_2") as "Hown_2".
  wp_apply (_internal_wp_untyped_store with "Hown") as "Hown".
  iApply "HΦ". iFrame "∗#%".
Qed.

Lemma own_map_not_nil mref m dq :
  mref ↦${dq} m -∗ ⌜ mref ≠ map.nil ⌝.
Proof.
  rewrite own_map_unseal. iNamed 1. iDestruct (heap_pointsto_non_null with "Hown") as "$".
Qed.

(* FIXME: seal. *)
Definition for_map_postcondition P Φ bv : iProp Σ :=
            (⌜ bv = continue_val ⌝ ∗ P) ∨
            (⌜ bv = execute_val ⌝ ∗ P) ∨
            ⌜ bv = break_val ⌝ ∗ Φ execute_val ∨
            (∃ v, ⌜ bv = return_val v ⌝ ∗ Φ bv).

Lemma wp_map_for_range P stk E (body : func.t) key_type elem_type mref m dq
  `{!TypedPointsto K} `{!IntoValTyped K key_type} :
  ∀ Φ,
  mref ↦${dq} m -∗
  (∀ keys,
     ⌜ list_to_set keys = dom m ∧ length keys = size m ∧ NoDup keys ⌝ -∗
     (P keys 0 ∗
      □ (∀ i key v, ⌜ keys !! (Z.to_nat i) = Some key ∧ m !! key = Some v ⌝ -∗ P keys i -∗
                    WP #body #key #v @ stk; E
                      {{ v, for_map_postcondition (P keys (i+1)) Φ v }}) ∗
      (P keys (Z.of_nat (size m)) -∗ Φ execute_val))
  ) -∗
  WP map.for_range key_type elem_type #mref #body @ stk; E {{ Φ }}.
Proof.
  iIntros "% Hm HΦ".
  wp_call.
  iDestruct (own_map_not_nil with "[$]") as %?.
  wp_if_destruct; first by exfalso.
  rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_start_read with "Hown") as "Hown".
  wp_apply (wp_InternalMapForRange with "[//]"). iIntros "%ks %Hdom'".
  eapply go.is_map_domain_pure in Hdom'; last done.
  destruct Hdom' as [Hks_nodup Hks].
  assert (Forall (λ kv, ∃ (k : K), kv = #k) ks) as Heq.
  { rewrite Forall_forall. intros kv. rewrite -list_elem_of_In.
    intros Hk. specialize (Hks kv). specialize (Hdom kv).
    rewrite -Hks in Hk. apply Hdom in Hk. done. }
  apply Forall_exists_Forall2_l in Heq as [keys Heq].
  apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
  rewrite list_fmap_id in Heq. subst.
  iAssert (⌜ _ ⌝)%I with "[]" as "%Hfacts".
  2: iDestruct ("HΦ" $! keys with "[]") as "(HP & #Hiter & HΦ)".
  2: iPureIntro; exact Hfacts.
  { iPureIntro. eassert _ as Hl.
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
  (* foldr  *)
  pose (i := 0).
  change (P keys 0) with (P keys i).
  iFreeze "Hiter".
  replace (into_val <$> keys) with (into_val <$> (drop (Z.to_nat i) keys)).
  2:{ rewrite drop_0 //. }
  iThaw "Hiter".
  iAssert (⌜ 0 ≤ i ≤ length keys ⌝)%I as "-#Hi"; first word.
  generalize i. clear i. intros i.
  iLöb as "IH" forall (i). iDestruct "Hi" as "%".
  destruct (decide (i < length keys)).
  2:{
    assert (i = length keys) by word. subst.
    nat_cleanup. rewrite drop_all /=.
    wp_auto. wp_apply "Hown". iIntros "Hown".
    wp_auto. iApply "HΦ". iFrame. destruct Hfacts as (? & -> & ?).
    iFrame.
  }
  list_elem keys i as key.
  destruct (m !! key) eqn:Hlookup.
  2:{
    exfalso. apply not_elem_of_dom_2 in Hlookup as Hkey_m.
    destruct Hfacts as [Hfact _]. rewrite <- Hfact in Hkey_m.
    rewrite elem_of_list_to_set in Hkey_m.
    rewrite list_elem_of_lookup in Hkey_m. naive_solver.
  }
  iSpecialize ("Hiter" $! i key v with "[//] HP").
  erewrite drop_S; last done. rewrite fmap_cons foldr_cons.
  rewrite Hagree Hlookup /=. wp_apply (wp_wand with "Hiter").
  iIntros (execv) "Hpost".
  rewrite -Z2Nat.inj_succ; last lia.
  iDestruct "Hpost" as "[[-> H]|Hpost]".
  { wp_auto. rewrite continue_val_unseal. wp_auto.
    iApply ("IH" with "[$] [$] [$]").
    word. }
  wp_auto.
  iDestruct "Hpost" as "[[-> H]|Hpost]".
  { rewrite execute_val_unseal. wp_auto.
    iApply ("IH" with "[$] [$] [$]").
    word. }
  iDestruct "Hpost" as "[[-> H]|Hpost]".
  { rewrite break_val_unseal. wp_auto.
    wp_apply "Hown". iIntros "Hown". wp_auto. iFrame. }
  iDestruct "Hpost" as "(%  & -> & HΦ')".
  rewrite return_val_unseal.
  wp_auto. wp_apply "Hown" as "Hown". iFrame.
Qed.

Global Instance wp_map_nil_for_range (body : func.t) key_type elem_type :
  PureWp True (map.for_range key_type elem_type #map.nil #body) execute_val.
Proof.
  by pure_wp_start.
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

Module test.
  Section proof.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
    {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

  Definition foo (mref: loc) (m: gmap w64 w64): iProp Σ :=
    own_map mref DfracDiscarded m.

  Lemma test Φ :
    True -∗
    WP (CompositeLiteral (go.MapType go.int (go.ArrayType 2 go.int32))
          (LiteralValue
             [KeyedElement (Some $ KeyExpression #(W64 0))
                (ElementExpression $ CompositeLiteral (go.ArrayType 2 go.int32) $
                   LiteralValue [KeyedElement None (ElementExpression #(W32 0));
                                 KeyedElement None (ElementExpression #(W32 1))]);
              KeyedElement (Some $ KeyExpression #(W64 1))
                (ElementLiteralValue
                   [KeyedElement None (ElementExpression #(W32 0));
                    KeyedElement None (ElementExpression #(W32 1))])
      ])) {{ Φ }}.
  Proof.
    iIntros "_".
    wp_auto. wp_apply wp_map_make1.
    iIntros "% Hm". wp_auto.
    wp_apply (wp_map_insert with "Hm").
    iIntros "Hm". wp_auto.
    wp_apply (wp_map_insert with "Hm"). iIntros "Hm". wp_auto.
  Abort.
End proof.
End test.
