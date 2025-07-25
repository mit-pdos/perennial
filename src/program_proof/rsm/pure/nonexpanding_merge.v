From iris.proofmode Require Import proofmode.

(* NB: nonexpanding is not the most precise name, since it also says the domain
is nonshrinking. Something like domain preserving but more concise. *)
Definition mergef_nonexpanding {A B C} (f : option A -> option B -> option C) :=
  ∀ x y, is_Some (f x y) ↔ is_Some y.

Lemma mergef_nonexpanding_Some {A B C} {f : option A -> option B -> option C} x u :
  mergef_nonexpanding f ->
  ∃ v, f x (Some u) = Some v.
Proof.
  intros Hne. specialize (Hne x (Some u)).
  by destruct Hne as [_ [v Hne]]; last eauto.
Qed.

Lemma mergef_nonexpanding_None {A B C} {f : option A -> option B -> option C} x :
  mergef_nonexpanding f ->
  f x None = None.
Proof.
  intros Hne.
  destruct (f _ _) eqn:Hf; last done.
  by apply mk_is_Some, Hne, is_Some_None in Hf.
Qed.

Lemma gmap_nonexpanding_merge_empty `{Countable K} {A B C : Type}
  (m : gmap K A) (f : option A -> option B -> option C) :
  mergef_nonexpanding f ->
  merge f m ∅ = ∅.
Proof.
  intros Hne.
  apply map_eq. intros k.
  rewrite lookup_merge 2!lookup_empty.
  by destruct (m !! k); simpl; first rewrite mergef_nonexpanding_None.
Qed.

Lemma gmap_nonexpanding_merge_dom `{Countable K} {A B C : Type}
  (ma : gmap K A) (mb : gmap K B) (f : option A -> option B -> option C) :
  mergef_nonexpanding f ->
  dom (merge f ma mb) = dom mb.
Proof.
  intros Hne.
  apply set_eq. intros k. rewrite 2!elem_of_dom.
  split; intros Hdom.
  - destruct (ma !! k) as [u |] eqn:Hma, (mb !! k) as [v |] eqn:Hmb.
    + done.
    + by rewrite lookup_merge Hma Hmb /= Hne in Hdom.
    + done.
    + rewrite lookup_merge Hma Hmb /= in Hdom. by apply is_Some_None in Hdom.
  - destruct (ma !! k) as [u |] eqn:Hma, (mb !! k) as [v |] eqn:Hmb.
    + by rewrite lookup_merge Hma Hmb /= Hne.
    + by apply is_Some_None in Hdom.
    + by rewrite lookup_merge Hma Hmb /= Hne.
    + by apply is_Some_None in Hdom.
Qed.

Lemma gmap_nonexpanding_merge_difference_distr `{Countable K} {A B C : Type}
  (ma : gmap K A) (mb1 mb2 : gmap K B) (f : option A -> option B -> option C) :
  mergef_nonexpanding f ->
  merge f ma (mb1 ∖ mb2) = merge f ma mb1 ∖ merge f ma mb2.
Proof.
  intros Hne.
  apply map_eq. intros k.
  rewrite lookup_merge 2!lookup_difference 2!lookup_merge.
  destruct (ma !! k); simpl.
  - destruct (mb2 !! k); simpl.
    + rewrite mergef_nonexpanding_None; last done.
      apply (mergef_nonexpanding_Some (Some a) b) in Hne as [c Hc].
      by rewrite Hc.
    + by rewrite mergef_nonexpanding_None; last done.
  - destruct (mb2 !! k); simpl.
    + apply (mergef_nonexpanding_Some None b) in Hne as [c Hc].
      by rewrite Hc.
    + done.
Qed.

Lemma gmap_nonexpanding_merge_mono `{Countable K} {A B C : Type}
  (ma : gmap K A) (mb1 mb2 : gmap K B) (f : option A -> option B -> option C) :
  mergef_nonexpanding f ->
  mb1 ⊆ mb2 ->
  merge f ma mb1 ⊆ merge f ma mb2.
Proof.
  rewrite 2!map_subseteq_spec.
  intros Hne Hsubseteq.
  intros k c. rewrite 2!lookup_merge.
  destruct (ma !! k); simpl; intros Hkc.
  - destruct (mb1 !! k) eqn:Hmb1; simpl.
    + by erewrite Hsubseteq.
    + by rewrite mergef_nonexpanding_None in Hkc.
  - destruct (mb1 !! k) eqn:Hmb1; simpl.
    + by erewrite Hsubseteq.
    + done.
Qed.

Lemma gmap_nonexpanding_merge_filter_commute `{Countable K} {A B C : Type}
  (P : K -> Prop) {Hdec : ∀ x, Decision (P x)}
  (ma : gmap K A) (mb : gmap K B) (f : option A -> option B -> option C) :
  mergef_nonexpanding f ->
  merge f ma (filter (λ kv, P kv.1) mb) = filter (λ kv, P kv.1) (merge f ma mb).
Proof.
  intros Hne.
  induction mb as [| k t m Hlookup IH] using map_ind.
  { rewrite map_filter_empty. by rewrite gmap_nonexpanding_merge_empty. }
  destruct (decide (P k)) as [Hp | Hn].
  - rewrite map_filter_insert_True; last done.
    apply (mergef_nonexpanding_Some (ma !! k) t) in Hne.
    destruct Hne as [c Hc].
    erewrite <- insert_merge_r; last done.
    erewrite <- insert_merge_r; last done.
    rewrite map_filter_insert_True; last done.
    by rewrite IH.
  - rewrite map_filter_insert_False; last done.
    rewrite delete_id; last done.
    apply (mergef_nonexpanding_Some (ma !! k) t) in Hne as Hc.
    destruct Hc as [c Hc].
    erewrite <- insert_merge_r; last done.
    rewrite map_filter_insert_False; last done.
    rewrite delete_id; first apply IH.
    rewrite lookup_merge Hlookup.
    by destruct (ma !! k); simpl; [apply mergef_nonexpanding_None |].
Qed.
