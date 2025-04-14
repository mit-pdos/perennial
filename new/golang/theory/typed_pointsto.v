From iris.bi.lib Require Import fractional.
From New.golang.theory Require Import proofmode list typing.
Require Import Coq.Program.Equality.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

  Context `{!IntoVal V}.
  Context `{!IntoValTyped V t}.
  Implicit Type v : V.
  Program Definition typed_pointsto_def l (dq : dfrac) (v : V) : iProp Σ :=
    (([∗ list] j↦vj ∈ flatten_struct (to_val v), heap_pointsto (l +ₗ j) dq vj))%I.
  Definition typed_pointsto_aux : seal (@typed_pointsto_def). Proof. by eexists. Qed.
  Definition typed_pointsto := typed_pointsto_aux.(unseal).
  Definition typed_pointsto_unseal : @typed_pointsto = @typed_pointsto_def := typed_pointsto_aux.(seal_eq).

  Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                                   (at level 20, dq custom dfrac at level 1,
                                    format "l  ↦ dq  v") : bi_scope.

  Ltac unseal := rewrite ?typed_pointsto_unseal /typed_pointsto_def.

  Global Instance typed_pointsto_timeless l q v : Timeless (l ↦{q} v).
  Proof. unseal. apply _. Qed.

  Global Instance typed_pointsto_persistent l v : Persistent (l ↦□ v).
  Proof. unseal. apply _. Qed.

  Global Instance typed_pointsto_dfractional l v : DFractional (λ dq, l ↦{dq} v)%I.
  Proof. unseal. apply _. Qed.
  Global Instance typed_pointsto_as_dfractional l v dq : AsDFractional
                                                     (l ↦{dq} v)
                                                     (λ dq, l ↦{dq} v)%I dq.
  Proof. auto. Qed.

  Global Instance typed_pointsto_fractional l v : Fractional (λ q, l ↦{#q} v)%I.
  Proof. unseal. apply _. Qed.

  Global Instance typed_pointsto_as_fractional l v q : AsFractional
                                                     (l ↦{#q} v)
                                                     (λ q, l ↦{#q} v)%I q.
  Proof. auto. Qed.

  Lemma alist_val_inj a b :
    alist_val a = alist_val b →
    a = b.
  Proof.
    rewrite alist_val_unseal.
    dependent induction b generalizing a.
    { by destruct a as [|[]]. }
    destruct a0.
    destruct a as [|[]]; first done.
    rewrite /= => [=].
    intros. subst.
    repeat f_equal.
    - by apply to_val_inj.
    - by apply IHb.
  Qed.

  Local Lemma flatten_struct_inj (v1 v2 : val) :
    has_go_type v1 t → has_go_type v2 t →
    flatten_struct v1 = flatten_struct v2 → v1 = v2.
  Proof.
    intros Hty1 Hty2 Heq.
    clear dependent V.
    dependent induction Hty1 generalizing v2.
    #[local] Ltac2 step () :=
      match! goal with
      | [ v : slice.t |- _ ] => let v := Control.hyp v in destruct $v
      | [ v : interface.t |- _ ] => let v := Control.hyp v in destruct $v
      (* | [ v : interface.tSome |- _ ] => let v := Control.hyp v in destruct $v *)
      | [ v : func.t |- _ ] => let v := Control.hyp v in destruct $v
      | [ v : option (go_string * go_string )|- _ ] => let v := Control.hyp v in destruct $v as [[??]|]
      | [ h : has_go_type _ _ |- _ ] => let h := Control.hyp h in (inversion_clear $h in Heq)
      | [ h : alist_val _ = alist_val _ |- _ ] => apply alist_val_inj in $h; subst

      (* unseal whatever's relevant *)
      | [ h : context [struct.val_aux]  |- _ ] => rewrite !struct.val_aux_unseal in $h
      | [ |- context [struct.val_aux] ] => rewrite !struct.val_aux_unseal
      | [ h : context [to_val]  |- _ ] => rewrite !to_val_unseal in $h
      | [ |- context [to_val] ] => rewrite !to_val_unseal

      | [ h : (flatten_struct _ = flatten_struct _) |- _ ] => progress (simpl in $h)
      | [ h : cons _ _ = cons _ _  |- _ ] =>
          Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None;
          clear $h; subst
      | [ h : context [length (cons _ _)] |- _ ] => progress (simpl in $h)
      | [ h : context [length []] |- _ ] => progress (simpl in $h)
      | [ |- _ ] => reflexivity
      | [ |- _ ] => discriminate
      end
    .
    all: repeat ltac2:(step ()).
    {
      (* XXX: need to reorder hyps to avoid an error in [dependent induction].... *)
      move a after a0.
      generalize dependent (uint.nat n); intros n' ??.
      dependent induction a generalizing a0; simpl in *; subst; simpl in *.
      { destruct a0; done. }
      destruct a0; try done.
      simpl in Heq.
      apply app_inj_1 in Heq as [? ?].
      2:{ by do 2 erewrite has_go_type_len by naive_solver. }
      simpl. f_equal.
      + apply H; naive_solver.
      + eapply IHa; naive_solver.
    }
    {
      induction d as [|[]d]; repeat ltac2:(step ()).
      simpl in *.
      apply app_inj_1 in Heq as [? ?].
      2:{ by do 2 erewrite has_go_type_len by naive_solver. }
      f_equal.
      + apply H; naive_solver.
      + apply IHd; naive_solver.
    }
  Qed.

  Lemma typed_pointsto_zero_size l dq v :
    go_type_size t = 0%nat →
    ⊢ l ↦{dq} v.
  Proof using IntoValTyped0.
    unseal.
    intros Hz.
    pose proof (to_val_has_go_type (V:=V) v) as Hlen%has_go_type_len.
    rewrite Hz in Hlen.
    apply length_zero_iff_nil in Hlen.
    rewrite Hlen /=.
    auto.
  Qed.

  Lemma typed_pointsto_valid l dq v :
    l ↦{dq} v ⊢ ⌜go_type_size t > 0 → ✓dq⌝.
  Proof using IntoValTyped0.
    iIntros "H".
    unseal.
    pose proof (to_val_has_go_type v) as H.
    destruct (flatten_struct (#v)) eqn:Hbad.
    { apply (f_equal length) in Hbad. rewrite (has_go_type_len (t:=t)) //= in Hbad.
      iPureIntro. lia. }
    iDestruct "H" as "[H1 H2]".
    iDestruct (heap_pointsto_valid with "H1") as %Hvalid; done.
  Qed.

  Global Instance typed_pointsto_combine_sep_gives l dq1 dq2 v1 v2 :
    CombineSepGives (l ↦{dq1} v1)%I (l ↦{dq2} v2)%I
                    ⌜ (go_type_size t > O → ✓(dq1 ⋅ dq2)) ∧ v1 = v2 ⌝%I.
  Proof using IntoValTyped0.
    unfold CombineSepGives.
    unseal.
    iIntros "[H1 H2]".
    rename l into l'.
    pose proof (to_val_has_go_type v1) as H1.
    pose proof (to_val_has_go_type v2) as H2.
    pose proof (flatten_struct_inj _ _ H1 H2).
    iDestruct (big_sepL2_sepL_2 with "H1 H2") as "H".
    { do 2 (erewrite has_go_type_len by done). done. }
    iDestruct (big_sepL2_impl with "H []") as "H".
    {
      iModIntro. iIntros "*%%[H1 H2]".
      iCombine "H1 H2" gives %Heq.
      instantiate(1:=(λ _ _ _, ⌜ _ ⌝%I )).
      simpl. iPureIntro. exact Heq.
    }
    iDestruct (big_sepL2_pure with "H") as %[Hlen Heq].
    iModIntro. iPureIntro.
    split.
    { intros. specialize (Heq 0%nat).
      destruct (flatten_struct (# v1)) eqn:Hbad.
      { exfalso. apply (f_equal length) in Hbad. rewrite (has_go_type_len (t:=t)) /= in Hbad; [lia|done]. }
      clear Hbad.
      destruct (flatten_struct (# v2)) eqn:Hbad.
      { exfalso. apply (f_equal length) in Hbad. rewrite (has_go_type_len (t:=t)) /= in Hbad; [lia|done]. }
      specialize (Heq v v0 ltac:(done) ltac:(done)) as [??]. assumption.
    }
    {
      apply to_val_inj, H.
      apply list_eq.
      intros.
      replace i with (i + 0)%nat by lia.
      rewrite <- !lookup_drop.
      destruct (drop i $ flatten_struct (# v1)) eqn:Hlen1, (drop i $ flatten_struct (# v2)) eqn:Hlen2.
      { done. }
      1-2: exfalso; apply (f_equal length) in Hlen1, Hlen2;
        rewrite !length_drop in Hlen1, Hlen2;
        simpl in *; lia.
      specialize (Heq i v v0).
      replace i with (i + 0)%nat in Heq by lia.
      rewrite <- !lookup_drop in Heq.
      rewrite Hlen1 Hlen2 in Heq.
      simpl in Heq.
      unshelve epose proof (Heq _ _); naive_solver.
    }
  Qed.

  Lemma typed_pointsto_persist l dq v :
    l ↦{dq} v ==∗ l ↦□ v.
  Proof.
    iIntros "H". iPersist "H". done.
  Qed.

  #[global]
  Instance typed_pointsto_update_persist l dq v :
    UpdateIntoPersistently (l ↦{dq} v) (l ↦□ v).
  Proof. apply _. Qed.

  Lemma typed_pointsto_not_null l dq v :
    go_type_size t > 0 →
    l ↦{dq} v -∗ ⌜ l ≠ null ⌝.
  Proof using IntoValTyped0.
    unseal. intros Hlen. iIntros "?".
    pose proof (to_val_has_go_type v) as Hty.
    generalize dependent (# v). clear dependent V. intros v Hty.
    iInduction Hty as [] "IH"; subst;
    simpl; rewrite ?to_val_unseal /= ?right_id ?loc_add_0;
      try (iApply heap_pointsto_non_null; by iFrame).
    - (* interface *)
      destruct i;
        simpl; rewrite ?to_val_unseal /= ?right_id ?loc_add_0;
        try (iApply heap_pointsto_non_null; by iFrame).
    - (* array *)
      rewrite go_type_size_unseal /= in Hlen.
      destruct a as [|v a'].
      { exfalso. simpl in *. lia. }
      destruct (decide (go_type_size_def elem = O)).
      { exfalso. rewrite e in Hlen. simpl in *. lia. }
      iDestruct select ([∗ list] _ ↦ _ ∈ _, _)%I as "[? _]".
      iApply ("IH" $! v with "").
      + naive_solver.
      + iPureIntro. rewrite go_type_size_unseal. lia.
      + iFrame.
    - (* struct *)
      rewrite go_type_size_unseal /= in Hlen.
      iInduction d as [|[a]] "IH2"; simpl in *.
      { exfalso. lia. }
      rewrite struct.val_aux_unseal /=.
      destruct (decide (go_type_size_def g = O)).
      {
        rewrite (nil_length_inv (flatten_struct (default _ _))).
        2:{
          erewrite has_go_type_len.
          { rewrite go_type_size_unseal. done. }
          apply Hfields. by left.
        }
        rewrite app_nil_l.
        iApply ("IH2" with "[] [] [] [$]").
        - iPureIntro. intros. apply Hfields. by right.
        - iPureIntro. lia.
        - iModIntro. iIntros. iApply ("IH" with "[] [] [$]").
          + iPureIntro. by right.
          + iPureIntro. lia.
      }
      {
        iDestruct select ([∗ list] _ ↦ _ ∈ _, _)%I as "[? _]".
        iApply ("IH" with "[] [] [$]").
        - iPureIntro. by left.
        - iPureIntro. rewrite go_type_size_unseal. lia.
      }
  Qed.

  Lemma wp_store stk E l (v v' : val) :
    {{{ ▷ heap_pointsto l (DfracOwn 1) v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ stk; E
    {{{ RET LitV LitUnit; heap_pointsto l (DfracOwn 1) v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". wp_call.
    wp_bind (PrepareWrite _).
    iApply (wp_prepare_write with "Hl"); iNext; iIntros "[Hl Hl']".
    wp_pures.
    by iApply (wp_finish_store with "[$Hl $Hl']").
  Qed.

End goose_lang.

Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                              (at level 20, dq custom dfrac at level 50,
                               format "l  ↦ dq  v") : bi_scope.

Section tac_lemmas.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

  Class PointsToAccess {V} {t} `{!IntoVal V} `{!IntoValTyped V t}
    (l : loc) (v : V) dq (P : iProp Σ) (P' : V → iProp Σ) : Prop :=
    {
      points_to_acc : P -∗ l ↦{dq} v ∗ (∀ v', l ↦{dq} v' -∗ P' v');
      points_to_update_eq : P' v ⊣⊢ P;
    }.

  Global Instance points_to_access_trivial {V} l (v : V) {t} `{!IntoVal V} `{!IntoValTyped V t} dq
    : PointsToAccess l v dq (l ↦{dq} v)%I (λ v', l ↦{dq} v')%I.
  Proof. constructor; [eauto with iFrame|done]. Qed.

End tac_lemmas.

(* TODO: move somewhere better *)
Ltac2 tc_solve_many () := solve [ltac1:(typeclasses eauto)].
Ltac2 ectx_simpl () := cbv [fill flip foldl ectxi_language.fill_item goose_ectxi_lang fill_item].
