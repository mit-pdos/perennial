From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl agree auth gmap csum.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import own.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

Definition mapUR (K V: Type) `{Countable K}: ucmraT :=
  gmapUR K (csumR (prodR fracR (agreeR (leibnizO V)))
                  (agreeR (leibnizO V))).

Class mapG Σ K V `{Countable K} :=
  { map_inG :> inG Σ (authUR (mapUR K V)); }.

Section auth_map.
  Context {K V: Type}  `{Countable0: Countable K}.
  Implicit Types (γ:gname) (k:K) (q:Qp) (v:V) (m: gmap K V).
  Context `{!mapG Σ K V}.

  Definition to_mapUR : gmap K (V*bool) → mapUR K V :=
    fmap (λ '(v, ro), if (ro:bool) then Cinr (to_agree (v : leibnizO V))
                      else Cinl (1%Qp, to_agree (v : leibnizO V))).

  Lemma to_mapUR_valid (m: gmap K (V*bool)) : ✓ to_mapUR m.
  Proof.
    intros k. rewrite lookup_fmap.
    destruct (m !! k) as [mv|] eqn:Heq; rewrite Heq //=.
    destruct mv as [v [|]]; rewrite //.
  Qed.

  Lemma lookup_to_mapUR_None (m: gmap K (V*bool)) k : m !! k = None → to_mapUR m !! k = None.
  Proof. rewrite lookup_fmap => -> //. Qed.

  Lemma to_mapUR_insert_inl k v (m: gmap K (V*bool)) :
    to_mapUR (<[k:=(v,false)]> m) = <[k:=Cinl (1%Qp, to_agree (v:leibnizO V))]> (to_mapUR m).
  Proof. rewrite /to_mapUR fmap_insert //. Qed.

  Lemma to_mapUR_insert_inr k v (m: gmap K (V*bool)) :
    to_mapUR (<[k:=(v,true)]> m) = <[k:=Cinr (to_agree (v:leibnizO V))]> (to_mapUR m).
  Proof. rewrite /to_mapUR fmap_insert //. Qed.

  Definition map_ctx γ q m : iProp Σ :=
    ∃ ro_m,
      ⌜m = fmap fst ro_m⌝ ∗
      own γ (●{q} to_mapUR ro_m).

  Global Instance map_ctx_fractional γ m : Fractional (λ q, map_ctx γ q m).
  Proof.
    iIntros (q1 q2).
    rewrite /map_ctx.
    setoid_rewrite auth_auth_frac_op.
    setoid_rewrite own_op.
    iSplit.
    - iIntros "H".
      iDestruct "H" as (ro_m) "[-> [H1 H2]]".
      iSplitL "H1"; eauto.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (ro_m1) "[-> H1]".
      iDestruct "H2" as (ro_m2) "[-> H2]".
      iDestruct (own_valid_2 with "H1 H2") as %Hvalid%auth_auth_frac_op_inv.
      rewrite Hvalid.
      iExists _; by iFrame.
  Qed.

  Global Instance map_ctx_AsFractional γ q m :
    AsFractional (map_ctx γ q m) (λ q, map_ctx γ q m) q.
  Proof.
    split; (apply _ || auto).
  Qed.

  Theorem map_ctx_agree γ q1 q2 m1 m2 :
    map_ctx γ q1 m1 -∗ map_ctx γ q2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iDestruct 1 as (ro_m1) "[-> H1]".
    iDestruct 1 as (ro_m2) "[-> H2]".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid%auth_auth_frac_op_inv.
    rewrite Hvalid.
    iCombine "H1 H2" as "H".
    iPureIntro.
    apply map_eq => k.
    apply option_eq => v.
    rewrite !lookup_fmap.
    rewrite !fmap_Some.

    assert (to_mapUR ro_m1 !! k ≡ to_mapUR ro_m2 !! k).
    { apply Hvalid. }
    inversion H; subst; clear H.
    (* TODO(tej): there's a lot of annoying inversion of to_mapUR, not sure if
    there's a better way *)
  Admitted.

  Definition ptsto_def γ k mq v :=
    own γ (◯ {[ k := match mq with
                     | Some q => Cinl (q, to_agree (v : leibnizO V))
                     | None => Cinr (to_agree (v : leibnizO V))
                     end ]}).
  Definition ptsto_aux : seal (@ptsto_def). Proof. by eexists. Qed.
  Definition ptsto := ptsto_aux.(unseal).
  Definition ptsto_eq : @ptsto = @ptsto_def := ptsto_aux.(seal_eq).

  Definition ptsto_mut γ k q v := ptsto γ k (Some q) v.
  Definition ptsto_ro γ k v := ptsto γ k None v.

  Notation "k [[ γ ]]↦{ q } v" := (ptsto_mut γ k q%Qp v)
    (at level 20, q at level 50, format "k  [[ γ ]]↦{ q }  v") : bi_scope.
  Notation "k [[ γ ]]↦ v" := (k [[γ]]↦{1} v)%I
    (at level 20, format "k  [[ γ ]]↦  v") : bi_scope.
  Notation "k [[ γ ]]↦ro v" := (ptsto_ro γ k v)
    (at level 20, format "k  [[ γ ]]↦ro  v") : bi_scope.

  Ltac unseal :=
    rewrite /ptsto_mut /ptsto_ro ?ptsto_eq.

  Global Instance ptsto_timeless : Timeless (ptsto γ k mq v).
  Proof. unseal; apply _. Qed.

  Global Instance ptsto_Fractional γ k v : Fractional (λ q, ptsto_mut γ k q v).
  Proof.
    unseal. intros p q. by rewrite -own_op -auth_frag_op
      singleton_op -Cinl_op -pair_op agree_idemp.
  Qed.
  Global Instance ptsto_AsFractional γ k q v : AsFractional (ptsto_mut γ k q v) (λ q, ptsto_mut γ k q v) q.
  Proof. split; auto; apply _. Qed.

  Global Instance ptsto_ro_timeless : Timeless (ptsto_ro γ k v).
  Proof. unseal; apply _. Qed.

  Global Instance ptsto_ro_persistent : Persistent (ptsto_ro γ k v).
  Proof. unseal; apply _. Qed.

  Lemma Cinl_valid (A B:cmraT) (x:A) :
    ✓ @Cinl A B x → ✓ x.
  Proof. auto. Qed.

  Lemma Cinr_valid (A B:cmraT) (x:B) :
    ✓ @Cinr A B x → ✓ x.
  Proof. auto. Qed.

  Lemma Cinl_Cinr_op (A B:cmraT) x y :
    @Cinl A B x ⋅ @Cinr A B y = CsumBot.
  Proof. reflexivity. Qed.

  Lemma Cinr_Cinl_op (A B:cmraT) x y :
    @Cinr A B y ⋅ @Cinl A B x = CsumBot.
  Proof. reflexivity. Qed.

  Lemma ptsto_agree_frac_value γ k mq1 mq2 v1 v2 :
    ptsto γ k mq1 v1 -∗ ptsto γ k mq2 v2 -∗
      ⌜v1 = v2 ∧ match mq1, mq2 with
                 | Some q1, Some q2 => ✓(q1+q2)%Qp
                 | None, None => True
                 | _, _ => False
                 end⌝.
  Proof.
    unseal; rewrite /ptsto_def.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    destruct mq1, mq2.
    - rewrite -Cinl_op -pair_op frac_op'.
      iDestruct (own_valid with "H") as %Hvalid.
      iPureIntro.
      (* unification doesn't work with apply *)
      apply auth_frag_valid in Hvalid as Hvalid%singleton_valid%Cinl_valid.
      apply pair_valid in Hvalid as [? ?%to_agree_op_inv%leibniz_equiv_iff].
      simpl in *.
      auto.
    - rewrite Cinl_Cinr_op.
      iDestruct (own_valid with "H") as %Hvalid.
      apply auth_frag_valid in Hvalid as []%singleton_valid.
    - rewrite Cinr_Cinl_op.
      iDestruct (own_valid with "H") as %Hvalid.
      apply auth_frag_valid in Hvalid as []%singleton_valid.
    - rewrite -Cinr_op.
      iDestruct (own_valid with "H") as %Hvalid.
      iPureIntro.
      (* unification doesn't work with apply *)
      apply auth_frag_valid in Hvalid as Hvalid%singleton_valid%Cinr_valid.
      apply to_agree_op_inv, leibniz_equiv_iff in Hvalid; auto.
  Qed.

  Lemma ptsto_mut_agree_frac_value γ k q1 q2 v1 v2 :
    ptsto_mut γ k q1 v1 -∗ ptsto_mut γ k q2 v2 -∗ ⌜v1 = v2 ∧ ✓(q1+q2)%Qp⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ptsto_agree_frac_value with "H1 H2") as %?; auto.
  Qed.

  Theorem ptsto_agree γ k mq1 mq2 v1 v2 :
    ptsto γ k mq1 v1 -∗ ptsto γ k mq2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ptsto_agree_frac_value with "H1 H2") as %[? ?].
    auto.
  Qed.

  Theorem ptsto_mut_valid γ k q v :
    ptsto_mut γ k q v -∗ ✓ q.
  Proof.
    unseal; rewrite /ptsto_def.
    rewrite own_valid.
    iIntros (Hvalid) "!%".
    apply (iffLR (auth_frag_valid _)) in Hvalid as
        Hvalid%singleton_valid%Cinl_valid.
    apply (iffLR (pair_valid _ _)) in Hvalid; intuition.
  Qed.
  Theorem ptsto_valid_2 γ k q1 q2 v1 v2 :
    ptsto_mut γ k q1 v1 -∗ ptsto_mut γ k q2 v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "H1 H2".
    iDestruct (ptsto_mut_agree_frac_value with "H1 H2") as %[? ?].
    auto.
  Qed.

  (* corollary of above lemmas for a useful special case *)
  Theorem ptsto_conflict γ k v1 v2 :
    ptsto_mut γ k 1 v1 -∗ ptsto_mut γ k 1 v2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ptsto_valid_2 with "H1 H2") as %?.
    apply (iffLR (frac_valid' _)) in H.
    contradiction H.
    auto.
  Qed.

  Lemma ptsto_ro_agree γ k v1 v2 :
    ptsto_ro γ k v1 -∗ ptsto_ro γ k v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ptsto_agree_frac_value with "H1 H2") as %[? ?]; auto.
  Qed.

  Theorem map_init m :
    ⊢ |==> ∃ γ, map_ctx γ 1 m.
  Proof.
    iMod (own_alloc (● to_mapUR ((., false) <$> m))) as (γ) "Hmap".
    { rewrite auth_auth_valid.
      apply to_mapUR_valid. }
    iModIntro.
    iExists γ, _; iFrame.
    iPureIntro.
    rewrite -map_fmap_compose map_fmap_id //.
  Qed.

  Theorem map_alloc {γ m} k v :
    m !! k = None →
    map_ctx γ 1 m ==∗ map_ctx γ 1 (<[k:=v]> m) ∗ ptsto_mut γ k 1 v.
  Proof.
    unseal.
    iIntros (Hlookup) "Hm".
    iDestruct "Hm" as (m_ro ->) "Hm".
    iMod (own_update with "Hm") as "[Hm Hk]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (Cinl (1%Qp, to_agree (v:leibnizO V))))=> //.
      apply lookup_to_mapUR_None.
      rewrite lookup_fmap in Hlookup.
      apply fmap_None in Hlookup; eauto. }
    iModIntro.
    iFrame "Hk".
    rewrite -to_mapUR_insert_inl.
    iExists _; iFrame.
    iPureIntro.
    rewrite fmap_insert //=.
  Qed.

  Lemma Cinl_included_inv (A B: cmraT) (x:A) (y:csumR A B) :
    Cinl x ≼ y →
    y = CsumBot ∨ ∃ x', y = Cinl x' ∧ x ≼ x'.
  Proof.
    rewrite csum_included; intros [|[|]]; eauto; right.
    - destruct H as [x' [x'' ?]]; intuition subst.
      inversion H0; subst; clear H0.
      eauto.
    - destruct H as [x' [x'' ?]]; intuition subst.
      inversion H0.
  Qed.

  Lemma Cinr_included_inv (A B: cmraT) (x:B) (y:csumR A B) :
    Cinr x ≼ y →
    y = CsumBot ∨ ∃ x', y = Cinr x' ∧ x ≼ x'.
  Proof.
    rewrite csum_included; intros [|[|]]; eauto; right.
    - destruct H as [x' [x'' ?]]; intuition subst.
      inversion H0.
    - destruct H as [x' [x'' ?]]; intuition subst.
      inversion H0; subst; clear H0.
      eauto.
  Qed.

  Lemma Some_included_inv (A: cmraT) (x y:A) :
    Some x ≼ Some y → x ≡ y ∨ x ≼ y.
  Proof.
    rewrite option_included.
    intros [|]; [ congruence | ].
    destruct H as [x' [y' ?]]; intuition idtac.
    - inversion H0; inversion H; subst.
      eauto.
    - inversion H0; inversion H; subst.
      eauto.
  Qed.

  Lemma Some_Cinl_included (A B: cmraT) (x:A) (y: csumR A B) :
    Some (Cinl x) ≼ Some y → y = CsumBot ∨ (∃ x', y = Cinl x' ∧ (x ≡ x' ∨ x ≼ x')).
  Proof.
    intros H%Some_included_inv.
    intuition idtac.
    - inversion H0; subst; eauto.
    - apply Cinl_included_inv in H0.
      intuition eauto.
      right.
      destruct H as [? (?&?)]; eauto.
  Qed.

  Lemma Some_Cinr_included (A B: cmraT) (x:B) (y: csumR A B) :
    Some (Cinr x) ≼ Some y → y = CsumBot ∨ (∃ x', y = Cinr x' ∧ (x ≡ x' ∨ x ≼ x')).
  Proof.
    intros H%Some_included_inv.
    intuition idtac.
    - inversion H0; subst; eauto.
    - apply Cinr_included_inv in H0.
      intuition eauto.
      right.
      destruct H as [? (?&?)]; eauto.
  Qed.

  Lemma map_ptsto_included k q v (m: gmap K (V*bool)) :
    {[k := Cinl (q, to_agree v)]} ≼ to_mapUR m → m !! k = Some (v, false).
  Proof.
    (* this proof is just a mess, it seems none of the lemmas needed are
    there *)
    rewrite singleton_included_l lookup_fmap.
    intros [y [Hequiv Hincl]].
    apply fmap_Some_equiv in Hequiv as [ [v' ro] [Hlookup Hy_equiv] ].
    rewrite Hlookup.
    f_equiv.
    apply Some_Cinl_included in Hincl as [-> | Hincl].
    { destruct ro; inversion Hy_equiv. }
    destruct Hincl as [ [q' v''] [-> Hequiv_incl ]].
    destruct ro; [ inversion Hy_equiv | ].
    f_equiv.
    inversion Hy_equiv; subst; clear Hy_equiv.
    rewrite -> H1 in Hequiv_incl.
    destruct Hequiv_incl as [Hequiv|Hincl].
    - inversion Hequiv; subst; simpl in *.
      apply (inj to_agree), leibniz_equiv_iff in H0; auto.
    - apply pair_included in Hincl as [_ Hincl]; simpl in Hincl.
      apply to_agree_included, leibniz_equiv in Hincl; auto.
  Qed.

  Lemma map_ptsto_ro_included k v (m: gmap K (V*bool)) :
    {[k := Cinr (to_agree v)]} ≼ to_mapUR m → m !! k = Some (v, true).
  Proof.
    (* this proof is also a mess *)
    rewrite singleton_included_l lookup_fmap.
    intros [y [Hequiv Hincl]].
    apply fmap_Some_equiv in Hequiv as [ [v' ro] [Hlookup Hy_equiv] ].
    rewrite Hlookup.
    f_equiv.
    apply Some_Cinr_included in Hincl as [-> | Hincl].
    { destruct ro; inversion Hy_equiv. }
    destruct Hincl as [ [q' v''] [-> Hequiv_incl ]].
    destruct ro; [ | by inversion Hy_equiv ].
    f_equiv.
    inversion Hy_equiv; subst; clear Hy_equiv.
    rewrite -> H1 in Hequiv_incl.
    destruct Hequiv_incl as [Hequiv|Hincl].
    - apply (inj to_agree), leibniz_equiv_iff in Hequiv; auto.
    - apply to_agree_included, leibniz_equiv in Hincl; auto.
  Qed.

  Theorem map_valid {γ m} k q mq v :
    map_ctx γ q m -∗ ptsto γ k mq v -∗ ⌜m !! k = Some v⌝.
  Proof.
    unseal; rewrite /ptsto_def.
    iDestruct 1 as (m_ro ->) "Hm".
    iIntros "Hk".
    rewrite lookup_fmap.
    destruct mq.
    - iDestruct (own_valid_2 with "Hm Hk") as
          %(_ & Hlookup%map_ptsto_included & _)%auth_both_frac_valid.
      iPureIntro.
      rewrite Hlookup //.
    - iDestruct (own_valid_2 with "Hm Hk") as
          %(_ & Hlookup%map_ptsto_ro_included & _)%auth_both_frac_valid.
      iPureIntro.
      rewrite Hlookup //.
  Qed.

  Theorem map_ro_valid {γ m} k q v :
    map_ctx γ q m -∗ ptsto_ro γ k v -∗ ⌜m !! k = Some v⌝.
  Proof. apply map_valid. Qed.

  Lemma map_update {γ m} k v1 v2 :
    map_ctx γ 1 m -∗ ptsto_mut γ k 1 v1 ==∗ map_ctx γ 1 (<[k:=v2]>m) ∗ ptsto_mut γ k 1 v2.
  Proof.
    unseal.
    iDestruct 1 as (m_ro ->) "Hm".
    iIntros "Hk".
    iDestruct (own_valid_2 with "Hm Hk") as
        %[Hlookup%map_ptsto_included _]%auth_both_valid.
    iMod (own_update_2 with "Hm Hk") as "[Hm $]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Cinl (1%Qp, to_agree (v2: leibnizO V))))=> //.
      rewrite lookup_fmap Hlookup //=. }
    iModIntro.
    rewrite -to_mapUR_insert_inl.
    iExists _; iFrame.
    iPureIntro.
    rewrite fmap_insert //.
  Qed.

  Theorem map_freeze γ m k v :
    map_ctx γ 1 m -∗
    ptsto_mut γ k 1 v ==∗ map_ctx γ 1 m ∗ ptsto_ro γ k v.
  Proof.
    unseal.
    iDestruct 1 as (m_ro ->) "Hm".
    iIntros "Hk".
    iDestruct (own_valid_2 with "Hm Hk") as
        %[Hlookup%map_ptsto_included _]%auth_both_valid.
    iMod (own_update_2 with "Hm Hk") as "[Hm $]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (Cinr (to_agree (v: leibnizO V))))=> //.
      rewrite lookup_fmap Hlookup //=. }
    iModIntro.
    rewrite -to_mapUR_insert_inr.
    iExists _; iFrame.
    iPureIntro.
    apply map_eq; intros k'; rewrite !lookup_fmap.
    destruct (decide (k = k')); subst.
    - rewrite lookup_insert Hlookup //.
    - rewrite lookup_insert_ne //.
  Qed.

  Theorem map_alloc_ro {γ m} k v :
    m !! k = None →
    map_ctx γ 1 m ==∗ map_ctx γ 1 (<[k:=v]> m) ∗ ptsto_ro γ k v.
  Proof.
    iIntros (?) "Hm".
    iMod (map_alloc k v with "Hm") as "[Hm Hk]"; auto.
    iMod (map_freeze with "Hm Hk") as "[$ $]".
    auto.
  Qed.

End auth_map.

(* TODO: this notation is cumbersome and also breaks [[ in Ltac, but that first
token needs to disambiguate the notation which makes it hard to use something
simple. *)

Notation "k [[ γ ]]↦{ q } v" := (ptsto_mut γ k q%Qp v)
  (at level 20, q at level 50, format "k  [[ γ ]]↦{ q }  v") : bi_scope.
Notation "k [[ γ ]]↦ v" := (k [[γ]]↦{1} v)%I
  (at level 20, format "k  [[ γ ]]↦  v") : bi_scope.
Notation "k [[ γ ]]↦ro v" := (ptsto_ro γ k v)
  (at level 20, format "k  [[ γ ]]↦ro  v") : bi_scope.
