From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl agree auth gmap csum.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import own.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

Definition mapUR (K V: Type) `{Countable K}: ucmraT :=
  gmapUR K (csumR (prodR fracR (agreeR (leibnizO V)))
                  (agreeR (leibnizO V))).

Class mapG K V `{Countable K} Σ :=
  { map_inG :> inG Σ (authUR (mapUR K V)); }.

Section auth_map.
  Context {K V: Type}  `{Countable0: Countable K}.
  Implicit Types (γ:gname) (k:K) (q:Qp) (v:V) (m: gmap K V).
  Context `{!mapG K V Σ}.

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

  Definition map_ctx γ m : iProp Σ :=
    ∃ ro_m,
      ⌜m = fmap fst ro_m⌝ ∗
      own γ (● to_mapUR ro_m).

  Definition ptsto_def γ k q v :=
    own γ (◯ {[ k := Cinl (q, to_agree (v : leibnizO V)) ]}).
  Definition ptsto_aux : seal (@ptsto_def). Proof. by eexists. Qed.
  Definition ptsto := ptsto_aux.(unseal).
  Definition ptsto_eq : @ptsto = @ptsto_def := ptsto_aux.(seal_eq).

  Definition ptsto_ro_def γ k v :=
    own γ (◯ {[ k := Cinr (to_agree (v : leibnizO V)) ]}).
  Definition ptsto_ro_aux : seal (@ptsto_ro_def). Proof. by eexists. Qed.
  Definition ptsto_ro := ptsto_ro_aux.(unseal).
  Definition ptsto_ro_eq : @ptsto_ro = @ptsto_ro_def := ptsto_ro_aux.(seal_eq).

  Ltac unseal :=
    rewrite ?ptsto_eq ?ptsto_ro_eq.

  Global Instance ptsto_timeless : Timeless (ptsto γ k q v).
  Proof. unseal; apply _. Qed.

  Global Instance ptsto_Fractional γ k v : Fractional (λ q, ptsto γ k q v).
  Proof.
    unseal. intros p q. by rewrite -own_op -auth_frag_op
      singleton_op -Cinl_op -pair_op agree_idemp.
  Qed.

  Global Instance ptsto_ro_timeless : Timeless (ptsto_ro γ k v).
  Proof. unseal; apply _. Qed.

  Global Instance ptsto_ro_persistent : Persistent (ptsto_ro γ k v).
  Proof. unseal; apply _. Qed.

  Theorem map_init m :
    ⊢ |==> ∃ γ, map_ctx γ m.
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
    map_ctx γ m ==∗ map_ctx γ (<[k:=v]> m) ∗ ptsto γ k 1 v.
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

  (* TODO: somehow this isn't upstream *)
  Lemma to_agree_equiv (A:ofeT) (x y:A) :
    to_agree x ≡ to_agree y →
    x ≡ y.
  Proof.
    intros H.
    apply equiv_dist => n.
    (* I apologize for this *)
    compute [equiv ofe_equiv agree_ofe_mixin agreeO agree_equiv to_agree] in H.
    destruct (H n) as [H' _].
    specialize (H' x ltac:(constructor)).
    destruct H' as (y'&Hin&Hyequiv).
    compute [elem_of] in Hin.
    apply elem_of_list_singleton in Hin; subst; auto.
  Qed.

  Lemma map_ptsto_included k q v (m: gmap K (V*bool)) :
    {[k := Cinl (q, to_agree v)]} ≼ to_mapUR m → m !! k = Some (v, false).
  Proof.
    (* this proof is just a mess, it seems none of the lemmas needed are
    there *)
    rewrite singleton_included_l lookup_fmap.
    intros [y [Hequiv Hincl]].
    apply fmap_Some_equiv in Hequiv as [[v' ro] [Hlookup Hy_equiv]].
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
      apply to_agree_equiv, leibniz_equiv_iff in H0; auto.
    - apply pair_included in Hincl as [_ Hincl]; simpl in Hincl.
      apply to_agree_included, leibniz_equiv in Hincl; auto.
  Qed.

  Lemma map_update {γ m} k v1 v2 :
    map_ctx γ m -∗ ptsto γ k 1 v1 ==∗ map_ctx γ (<[k:=v2]>m) ∗ ptsto γ k 1 v2.
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
    map_ctx γ m -∗
    ptsto γ k 1 v ==∗ map_ctx γ m ∗ ptsto_ro γ k v.
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
    map_ctx γ m ==∗ map_ctx γ (<[k:=v]> m) ∗ ptsto_ro γ k v.
  Proof.
    iIntros (?) "Hm".
    iMod (map_alloc k v with "Hm") as "[Hm Hk]"; auto.
    iMod (map_freeze with "Hm Hk") as "[$ $]".
    auto.
  Qed.

End auth_map.
