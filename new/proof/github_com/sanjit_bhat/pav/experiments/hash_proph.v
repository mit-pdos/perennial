From New.proof Require Import proof_prelude.

Notation hash_len := 32 (only parsing).

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!ghost_varG Σ (list (list w8))}.

(* [hash_fun] is the hash function itself: [hash_fun v] is the hash of [v].
 *)
Definition hash_fun : list w8 -> list w8.
Admitted.

Lemma hash_fun_len data :
  Z.of_nat (length (hash_fun data)) = hash_len.
Admitted.

Record hash_gnames := {
  hash_namespace: namespace;
  hash_hist: gname;
  hash_proph: proph_id;
  hashed_data: list (list w8);
}.

Definition is_hash_history γ (h: list (list w8)) : iProp Σ :=
  ghost_var (hash_hist γ) 1%Qp h.

Definition is_hash_prophecy γ (p: list (list w8)) : iProp Σ :=
  proph (hash_proph γ) (to_val <$> p).

Definition is_hash_map_inner γ : iProp Σ :=
  ∃ h p,
    is_hash_history γ h ∗
    is_hash_prophecy γ p ∗
    ⌜hashed_data γ = h ++ p⌝.

Definition is_hash_model γ : iProp Σ :=
  "#Hinv" ∷ inv (hash_namespace γ) (is_hash_map_inner γ).

Definition is_hash_collision_free γ : Prop :=
  ∀ data1 data2,
    data1 ∈ hashed_data γ ->
    data2 ∈ hashed_data γ ->
    hash_fun data1 = hash_fun data2 ->
    data1 = data2.

(* [hash_map m] is a map representing the hashes that have been
 * computed; [hash_map m !! h] is some input that hashes to [h],
 * or [None] if no input hashes to [h].
 *)
Definition hash_map γ : (gmap (list w8) (list w8)) :=
  list_to_map ((λ data, (hash_fun data, data)) <$> (hashed_data γ)).

#[global]
Instance is_hash_model_persistent γ : Persistent (is_hash_model γ).
Proof. refine _. Qed.

Lemma hash_map_wf γ :
  ∀ h data,
    (hash_map γ) !! h = Some data -> hash_fun data = h ∧ data ∈ (hashed_data γ).
Proof.
  rewrite /hash_map.
  intros h data Hm.
  apply elem_of_list_to_map_2 in Hm.
  apply list_elem_of_fmap_1 in Hm.
  destruct Hm as [d Hm].
  intuition subst.
  - inversion H; subst. done.
  - inversion H; subst. done.
Qed.

(* [is_hash] says what hash computation produces [hash]: either it's
 * [Some data], in which case, [hash_fun data = hash], or [None], in
 * which case there's no other possible [is_hash] for the same [hash].
 *)
Definition is_hash γ (odata : option (list w8)) (hash : list w8) : Prop :=
  match odata with
  | None => ∀ data', data' ∈ hashed_data γ -> hash_fun data' ≠ hash
  | Some data => data ∈ hashed_data γ ∧ hash_fun data = hash
  end.

Lemma is_hash_det γ data hash0 hash1 :
  is_hash γ (Some data) hash0 ->
  is_hash γ (Some data) hash1 ->
  hash0 = hash1.
Proof.
  simpl. intuition congruence.
Qed.

(* [is_hash_inj] states that there's only one pre-image that leads
 * to [hash].  Note that here [data0] and [data1] are [option (list w8)],
 * meaning that if there's an [is_hash None hash] fact, there cannot be
 * another [is_hash (Some x) hash] fact for the same [hash].
 *)
Lemma is_hash_inj γ data0 data1 hash :
  is_hash_collision_free γ ->
  is_hash γ data0 hash ->
  is_hash γ data1 hash ->
  data0 = data1.
Proof.
  destruct data0, data1; simpl; intuition; eauto.
  - specialize (H _ _ H2 H0). rewrite H; congruence.
  - exfalso; eauto.
  - exfalso; eauto.
Qed.

Lemma is_hash_len γ data hash :
  is_hash γ (Some data) hash -> Z.of_nat (length hash) = hash_len.
Proof.
  simpl; intuition.
  rewrite -H1.
  apply hash_fun_len.
Qed.

(* [is_hash_inv] says that, given a hash value, there's some
 * [option (list w8)] that corresponds to that hash value.
 * The [option] indicates that there's either some specific
 * [list w8] or there's no possible input that gives that hash.
 * This is the key lemma that builds on the prophecy model.
 *)
Lemma is_hash_inv γ hash :
  ∃ odata,
    is_hash γ odata hash.
Proof.
  exists (hash_map γ !! hash).
  destruct (hash_map γ !! hash) eqn:He; simpl.
  - apply hash_map_wf in He as He'. intuition eauto.
  - intros. intro.
    rewrite /hash_map in He.
    apply not_elem_of_list_to_map in He.
    apply He; clear He. subst.
    eapply list_elem_of_fmap_2'.
    + apply list_elem_of_fmap_2. eauto.
    + done.
Qed.

(* Example use of [is_hash_inv] to reason about commitment to
 * a chain of [list w8] values.  The [limit] value prevents a
 * theoretical infinite loop (i.e., a hash that corresponds to
 * an infinite cycle of commitments), which would prevent us
 * from being able to prove [is_chain_commitment_inv] below.
 *)
Fixpoint is_chain_commitment γ (limit: nat) (l : list (list w8)) (h : list w8) : Prop :=
  match limit with
  | O => l = []
  | S limit =>
    match l with
    | nil =>
      is_hash γ None h ∨
      (∃ data, is_hash γ (Some data) h ∧ Z.of_nat (length data) < hash_len)
    | v :: l' =>
      ∃ h',
        Z.of_nat (length h') = hash_len ∧
        is_chain_commitment γ limit l' h' ∧
        is_hash γ (Some (h' ++ v)) h
    end
  end.

Lemma is_chain_commitment_inj : ∀ γ, is_hash_collision_free γ ->
  ∀ limit0 limit1 l0 l1 h0 h1,
    (limit0 ≤ limit1)%nat ->
    is_chain_commitment γ limit0 l0 h0 ->
    is_chain_commitment γ limit1 l1 h1 ->
    h0 = h1 ->
    l0 = firstn limit0 l1.
Proof.
  intros γ Hγ.
  induction limit0; simpl.
  { intros. intuition subst. }
  intros.
  destruct limit1.
  { lia. }

  destruct l0, l1.
  + done.
  + exfalso. subst.
    destruct H0 as [H0 | [data' H0]].
    * destruct H1 as [h' [Hlen [Hcom Hhash]]].
      destruct Hhash as [Hhash0 Hhash1].
      specialize (H0 _ Hhash0). done.
    * simpl in H1. destruct H1 as [h' H1]. intuition. subst.
      apply Hγ in H7; eauto. subst. rewrite app_length in H3. lia.
  + exfalso. subst.
    destruct H1 as [H1 | [data' H1]].
    * destruct H0 as [h' [Hlen [Hcom Hhash]]].
      destruct Hhash as [Hhash0 Hhash1].
      specialize (H1 _ Hhash0). done.
    * destruct H0 as [h' H0]. intuition. subst.
      simpl in H0. intuition.
      apply Hγ in H6; eauto. subst. rewrite app_length in H4. lia.
  + simpl in *.
    destruct H0 as [h0' H0].
    destruct H1 as [h1' H1].
    intuition subst.
    apply Hγ in H9; eauto.
    apply app_inj_1 in H9; last lia.
    intuition subst.
    f_equal.
    eapply IHlimit0; try eassumption.
    * lia.
    * done.
Qed.

Lemma is_chain_commitment_inv γ limit : ∀ h,
  ∃ l,
    is_chain_commitment γ limit l h.
Proof.
  induction limit; intros h.
  - exists nil. done.
  - destruct (is_hash_inv γ h) as [odata Hodata].
    destruct odata as [data|].
    + destruct (decide (Z.of_nat (length data) < hash_len)).
      * exists nil. simpl. eauto.
      * destruct (IHlimit (firstn (Z.to_nat hash_len) data)) as [chain Hchain].
        exists (skipn (Z.to_nat hash_len) data :: chain).
        simpl. eexists _. intuition.
        2: eassumption.
        { rewrite length_take. lia. }
        { rewrite take_drop. simpl in Hodata. intuition. }
        rewrite take_drop. simpl in Hodata. intuition.
    + simpl in Hodata. exists nil. simpl. eauto.
Qed.

End proof.
