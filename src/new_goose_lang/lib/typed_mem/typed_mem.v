From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
From Perennial.program_logic Require Import weakestpre.
From Perennial.goose_lang Require Import proofmode.
From Perennial.new_goose_lang Require Export typed_mem.impl struct.impl slice.
Require Import Coq.Program.Equality.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Inductive has_go_type_aux (F : val → go_type → Prop) : val → go_type → Prop :=
  | has_go_type_aux_bool (b : bool) : has_go_type_aux F #b boolT
  | has_go_type_aux_uint64 (x : w64) : has_go_type_aux F #x uint64T
  | has_go_type_aux_uint32 (x : w32) : has_go_type_aux F #x uint32T
  | has_go_type_aux_uint16 : has_go_type_aux F nil uint16T
  | has_go_type_aux_uint8 (x : w8) : has_go_type_aux F #x uint8T

  | has_go_type_aux_int64 (x : w64) : has_go_type_aux F #x int64T
  | has_go_type_aux_int32 (x : w32) : has_go_type_aux F #x int32T
  | has_go_type_aux_int16 : has_go_type_aux F nil int16T
  | has_go_type_aux_int8 (x : w8) : has_go_type_aux F #x int8T

  | has_go_type_aux_string (s : string) : has_go_type_aux F #(str s) stringT
  | has_go_type_aux_slice elem (s : slice.t) : has_go_type_aux F (slice_val s) (sliceT elem)
  | has_go_type_aux_slice_nil elem : has_go_type_aux F slice_nil (sliceT elem)

  (* This avoids requiring (NoDup d) so we can avoid having to require that for zero_val.
     So, the Hfields statement is a Forall over decls, to deal with the fact
     that decls might include the same field name multiple times.
   *)
  | has_go_type_aux_struct
      (d : descriptor) fvs
      (Hfields : Forall (λ '(f, t), F (default (zero_val t) (assocl_lookup fvs f)) t) d)
    : has_go_type_aux F (struct.mk_f d fvs) (structT d)
  | has_go_type_aux_ptr (l : loc) : has_go_type_aux F #l ptrT
  | has_go_type_aux_func f e v : has_go_type_aux F (RecV f e v) funcT
  | has_go_type_aux_func_nil : has_go_type_aux F nil funcT

  (* FIXME: interface_val *)
  | has_go_type_aux_interface (s : slice.t) : has_go_type_aux F (slice_val s) interfaceT
  | has_go_type_aux_interface_nil : has_go_type_aux F interface_nil interfaceT

  | has_go_type_aux_mapT kt vt (l : loc) : has_go_type_aux F #l (mapT kt vt)
  | has_go_type_aux_chanT t (l : loc) : has_go_type_aux F #l (chanT t)
  .

  Fixpoint has_go_type_step_indexed (n : nat) : val → go_type → Prop :=
    match n with
    | O => (λ _ _, False)
    | S n => has_go_type_aux (has_go_type_step_indexed n)
    end.

  Definition has_go_type (v : val) (t : go_type) : Prop :=
    ∃ n, has_go_type_step_indexed n v t
  .

  Local Fixpoint type_depth (t : go_type) : nat :=
    match t with
    | structT decls => S (fold_right max O (type_depth ∘ snd <$> decls))
    | _ => O
    end
  .

  Lemma has_go_type_aux_mono {F F' v t} :
    (∀ v' t', F v' t' → F' v' t') →
    has_go_type_aux F v t → has_go_type_aux F' v t.
  Proof.
    intros ? Hty.
    inversion Hty; subst; econstructor.
    eapply Forall_impl; first exact Hfields.
    intros. cbn in *. destruct x.
    by apply H.
  Qed.

  Lemma has_go_type_step_indexed_mono (n n' : nat) v t :
    n <= n' → has_go_type_step_indexed n v t → has_go_type_step_indexed n' v t.
  Proof.
    revert n. dependent induction n'.
    { intros. replace O with n by lia. done. }
    intros. cbn in *.
    induction n; first done.
    eapply (has_go_type_aux_mono _ H0).
    Unshelve. intros. eapply IHn'; last done. lia.
  Qed.

  Lemma has_go_type_bool (b : bool) : has_go_type #b boolT.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_uint64 (b : w64) : has_go_type #b uint64T.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_uint32 (b : w32) : has_go_type #b uint32T.
  Proof. exists 1%nat. econstructor. Qed.
  (* Lemma has_go_type_uint16 (b : w16 ) : has_go_type #b uint16T.
  Proof. exists 1%nat. econstructor. Qed. *)
  Lemma has_go_type_uint8 (b : w8) : has_go_type #b uint8T.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_int64 (b : w64) : has_go_type #b int64T.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_int32 (b : w32) : has_go_type #b int32T.
  Proof. exists 1%nat. econstructor. Qed.
  (* Lemma has_go_type_int16 (b : w16 ) : has_go_type #b int16T.
  Proof. exists 1%nat. econstructor. Qed. *)
  Lemma has_go_type_int8 (b : w8) : has_go_type #b int8T.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_string (s : string) : has_go_type #(str s) stringT.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_slice elem (s : slice.t) : has_go_type (slice_val s) (sliceT elem).
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_slice_nil elem : has_go_type slice_nil (sliceT elem).
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_struct d fvs :
    Forall (λ '(f, t), has_go_type (default (zero_val t) (assocl_lookup fvs f)) t) d →
    has_go_type (struct.mk_f d fvs) (structT d).
  Proof.
    intros Hfields.
    assert (∃ n, Forall (λ '(f, t), has_go_type_step_indexed n (default (zero_val t) (assocl_lookup fvs f))
                                                             t) d) as [n Hfields_si].
    {
      induction d.
      { exists 37%nat. done. }
      apply Forall_cons in Hfields as [Hfield Hfields].
      apply IHd in Hfields as [n Hfields].
      destruct a.
      destruct Hfield as [n' Hfield].
      exists (n `max` n')%nat.
      apply Forall_cons.
      split.
      { eapply has_go_type_step_indexed_mono; last done. lia. }
      eapply Forall_impl; first exact Hfields.
      intros. cbn in *. destruct x. (* destruct (assocl_lookup fvs s0); last done. *)
      eapply has_go_type_step_indexed_mono; [|done]; lia.
    }
    eexists (S n).
    econstructor. done.
  Qed.

  Lemma has_go_type_ptr (l : loc) : has_go_type #l ptrT.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_func f e v : has_go_type (RecV f e v) funcT.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_func_nil : has_go_type nil funcT.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_interface (s : slice.t) : has_go_type (slice_val s) interfaceT.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_interface_nil : has_go_type interface_nil interfaceT.
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_mapT kt vt (l : loc) : has_go_type #l (mapT kt vt).
  Proof. exists 1%nat. econstructor. Qed.
  Lemma has_go_type_chanT t (l : loc) : has_go_type #l (chanT t).
  Proof. exists 1%nat. econstructor. Qed.

  Lemma has_go_type_ind :
    ∀ P : val → go_type → Prop,
    (∀ (b : bool), P #b boolT) →
    (∀ (x : w64), P #x uint64T) →
    (∀ (x : w32), P #x uint32T) →
    (* (∀ (x : w16), P #x uint16T) → *)
    (P nil uint16T) →
    (∀ (x : w8), P #x uint8T) →
    (∀ (x : w64), P #x int64T) →
    (∀ (x : w32), P #x int32T) →
    (* (∀ (x : w16), P #x int16T) → *)
    (P nil int16T) →
    (∀ (x : w8), P #x int8T) →
    (∀ (s : string), P #(str s) stringT) →
    (∀ (s : slice.t) elem, P (slice_val s) $ sliceT elem) →
    (∀ elem, P slice_nil $ sliceT elem) →
    (∀ d fvs (Hfields : Forall (λ '(f, t), P (default (zero_val t) (assocl_lookup fvs f)) t) d),
       P (struct.mk_f d fvs) $ structT d) →
    (∀ (l : loc), P #l ptrT) →
    (∀ f e v, P (RecV f e v) funcT) →
    (P nil funcT) →
    (∀ s, P (slice_val s) interfaceT) →
    (P interface_nil interfaceT) →
    (∀ kt vt (l : loc), P #l $ mapT kt vt) →
    (∀ t (l : loc), P #l $ chanT t) →
    (∀ v t, has_go_type v t → P v t).
  Proof.
    intros ???????????????????????.
    revert v.

    assert (∃ (n : nat), type_depth t <= n) as [n Htype_depth].
    { eexists _; done. }
    generalize dependent t.
    induction n; intros ? Htype_depth ? Hty.
    {
      destruct Hty as [[|n] Hty]; first done.
      inversion Hty; subst;
        (repeat match goal with
                | [ H : _ |- _ ] => apply H
                end
        ).
      simpl in Htype_depth. exfalso. lia.
    }
    destruct Hty as [[|m] Hty]; first done.
    inversion Hty;
      subst;
      repeat match goal with
             | [ H : ?Q |- _ ] =>
               lazymatch Q with
               | context [type_depth] => fail
               | context [P] => apply H
               end
             end.
    induction d.
    { done. }
    apply Forall_cons in Hfields as [Hfield Hfields].
    apply Forall_cons. split.
    {
      cbn in *. destruct a.
      apply IHn. { cbn in *. lia. }
      by eexists _.
    }
    apply IHd.
    { cbn in *. lia. }
    { econstructor. done. }
    done.
  Qed.

  Inductive has_go_abstract_type : val → go_abstract_type → Prop :=
  | has_go_abstract_type_bool (b : bool) : has_go_abstract_type #b cellT
  | has_go_abstract_type_uint64 (x : w64) : has_go_abstract_type #x cellT
  | has_go_abstract_type_uint32 (x : w32) : has_go_abstract_type #x cellT
  (* | has_go_abstract_type_uint16 (x : w16) : has_go_abstract_type #x cellT *)
  | has_go_abstract_type_uint8 (x : w8) : has_go_abstract_type #x cellT
  | has_go_abstract_type_int64 (x : w64) : has_go_abstract_type #x cellT
  | has_go_abstract_type_int32 (x : w32) : has_go_abstract_type #x cellT
  (* | has_go_abstract_type_int16 (x : w16) : has_go_abstract_type #x cellT *)
  | has_go_abstract_type_int8 (x : w8) : has_go_abstract_type #x cellT
  | has_go_abstract_type_string (x : string) : has_go_abstract_type #(str x) cellT
  | has_go_abstract_type_ptr (x : loc) : has_go_abstract_type #x cellT
  | has_go_abstract_type_func f x e : has_go_abstract_type (RecV f x e) cellT
  | has_go_abstract_type_nil : has_go_abstract_type nil cellT
  | has_go_abstract_type_unit : has_go_abstract_type #() unitT
  | has_go_abstract_type_prod
      (v1 v2 : val) (t1 t2 : go_abstract_type)
      (Ht1 : has_go_abstract_type v1 t1)
      (Ht2 : has_go_abstract_type v2 t2)
    : has_go_abstract_type (v1, v2) (prodT t1 t2)
  .

  Lemma go_type_ind:
    ∀ P : go_type → Prop,
    P boolT
    → P uint8T
    → P uint16T
    → P uint32T
    → P uint64T
    → P int8T
    → P int16T
    → P int32T
    → P int64T
    → P stringT
    → (∀ elem : go_type, P elem → P (sliceT elem))
    → (∀ (decls : list (string * go_type)) (Hfields : Forall P (snd <$> decls)),
         P (structT decls))
    → P ptrT
    → P funcT
    → P interfaceT
    → (∀ key : go_type, P key → ∀ elem : go_type, P elem → P (mapT key elem))
    → (∀ elem : go_type, P elem → P (chanT elem)) → ∀ g : go_type, P g
  .
  Proof.
    intros.
    set type_depth := (fix f (t : go_type) : nat :=
      match t with
      | structT decls => S (fold_right max O (f ∘ snd <$> decls))
      | sliceT elem => S (f elem)
      | mapT kt vt => S ((f kt) `max` (f vt))
      | chanT t => S (f t)
      | _ => O
      end).

    assert (∃ (n : nat), type_depth g <= n) as [n Htype_depth]; [by eexists|].
    induction n.
    {
      induction g;
      repeat match goal with
              | [ H : _ |- _ ] => apply H
              end.
      all: cbn in *; lia.
    }
    induction g;
      repeat match goal with
             | [ H : _ |- _ ] => apply H
             end.
    all: try (cbn in *; lia).
    {
    }
    destruct (decide (type_depth g = S n)).
    2:{ apply IHn. lia. }
    clear Htype_depth. rename e into Htype_depth.
    clear IHn.
    all: try (cbn in *; lia).
    {
    }
    all: repeat match goal with
           | [ H : _ |- _ ] => apply H
           end.
    {
      cbn in *. lia.
    }
    - all: try (cbn in *; lia).
  Qed.

  Lemma zero_val_has_go_type t :
    has_go_type (zero_val t) t.
  Proof.
    assert (∃ (n : nat), type_depth t <= n) as [n Htype_depth]; [by eexists|].
    dependent induction n; simpl.
    {
      destruct t.
      all: try (exists 1%nat; econstructor).
      cbn in *. lia.
    }
    destruct (decide (type_depth t = S n)).
    2:{ apply IHn. lia. }
    clear Htype_depth. rename e into Htype_depth.
    destruct t.
    all: try (exfalso; cbn in *; lia).
    cbn in *.
    induction decls.
    { simpl. exists 1%nat. replace (#()) with (struct.mk_f [] []) by done. econstructor. done. }
    inversion
    epose proof (IHdecls _ _).
    Unshelve.
    {

    }
    destruct a. simpl.
    rewrite IHdecls.
    simpl. done.
    }
    replace (foldr PairV _ _) with (struct.mk_f decls []).
    { exists 1%nat. econstructor. simpl in *. apply Forall_true. intros. destruct x. done. }
  Qed.

  Local Lemma has_go_type_to_abstract_inductive :
    ∀ (n : nat), ∀ t, (type_depth t <= n)%nat → ∀ v, has_go_type v t → has_go_abstract_type v (go_type_interp t).
  Proof.
    intros n. induction n as [| n IH]; intros ? Hdepth ? Hty.
    + (* type depth 0 case *)
      inversion Hty as [n Hty_si].
      destruct n; first by exfalso.
      destruct t; simpl in *; try (inversion Hty_si; subst; repeat constructor).
      lia.
    + (* type depth (n+1) case *)
      inversion Hty as [m Hty_si].
      destruct m; first by exfalso.
      destruct t; cbn in *; try (inversion Hty_si; subst; repeat constructor).

      (* structT case *)
      clear Hty_si.
      induction decls; first constructor.
      destruct a. simpl.
      apply Forall_cons in Hfields as [Hfield Hfields].
      constructor.
      ++ clear IHdecls.
         destruct assocl_lookup; cbn in *.
         - apply IH; [lia| eexists _; apply Hfield ] .
         - apply IH; [ lia | apply zero_val_has_go_type ].
      ++ apply IHdecls.
         +++ cbn in *. etransitivity; [|exact Hdepth].
             apply le_n_S. lia.
         +++ exists (S m)%nat. econstructor.
             apply Hfields.
         +++ done.
  Qed.
  Lemma has_go_type_to_abstract v t :
    has_go_type v t → has_go_abstract_type v (go_type_interp t).
  Proof. eapply has_go_type_to_abstract_inductive. done. Qed.

  Definition typed_pointsto_def l (dq : dfrac) (t : go_type) (v : val): iProp Σ :=
    (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j) ↦{dq} vj) ∗ ⌜ has_go_type v t ⌝)%I.
  Definition typed_pointsto_aux : seal (@typed_pointsto_def). Proof. by eexists. Qed.
  Definition typed_pointsto := typed_pointsto_aux.(unseal).
  Definition typed_pointsto_eq : @typed_pointsto = @typed_pointsto_def := typed_pointsto_aux.(seal_eq).

  Notation "l ↦[ t ] dq v" := (typed_pointsto l dq t v%V)
                                   (at level 20, dq custom dfrac at level 1, t at level 50,
                                    format "l  ↦[ t ] dq  v") : bi_scope.

  Ltac unseal := rewrite ?typed_pointsto_eq /typed_pointsto_def.

  Global Instance typed_pointsto_timeless l t q v: Timeless (l ↦[t]{q} v).
  Proof. unseal. apply _. Qed.

  Global Instance typed_pointsto_fractional l t v: fractional.Fractional (λ q, l ↦[t]{#q} v)%I.
  Proof. unseal. apply _. Qed.

  Global Instance typed_pointsto_as_fractional l t v q: fractional.AsFractional
                                                     (l ↦[t]{#q} v)
                                                     (λ q, l ↦[t]{#q} v)%I q.
  Proof. constructor; auto. apply _. Qed.

  Local Lemma has_go_abstract_type_len {v t} :
    has_go_abstract_type v t ->
    length (flatten_struct v) = (go_abstract_type_size t).
  Proof.
    unfold go_type_size.
    induction 1; simpl; auto.
    rewrite app_length. lia.
  Qed.

  Local Lemma wp_AllocAt t stk E v :
    has_go_type v t ->
    {{{ True }}}
      ref v @ stk; E
    {{{ l, RET #l; l ↦[t] v }}}.
  Proof.
    iIntros (Hty Φ) "_ HΦ".
    wp_apply wp_allocN_seq; first by word.
    change (uint.nat 1) with 1%nat; simpl.
    iIntros (l) "[Hl _]".
    iApply "HΦ".
    unseal.
    iSplitL; auto.
    rewrite Z.mul_0_r loc_add_0.
    iFrame.
  Qed.

  Lemma wp_ref_to t stk E v :
    has_go_type v t ->
    {{{ True }}}
      ref_to t v @ stk; E
    {{{ l, RET #l; l ↦[t] v }}}.
  Proof.
    iIntros (Hty Φ) "_ HΦ".
    wp_call.
    wp_apply (wp_AllocAt t); auto.
  Qed.


  Lemma wp_ref_of_zero stk E t :
    {{{ True }}}
      ref (zero_val t) @ stk; E
    {{{ l, RET #l; l ↦[t] (zero_val t) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (wp_AllocAt t); eauto.
    apply zero_val_has_go_type.
  Qed.

  Lemma wp_typed_load stk E q l t v :
    {{{ ▷ l ↦[t]{q} v }}}
      load_ty t #l @ stk; E
    {{{ RET v; l ↦[t]{q} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ".
    unseal.
    iDestruct "Hl" as "[Hl %]".
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j)↦{q} vj) -∗ Φ v))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ".
      iSplit; eauto. }
    unfold load_ty.
    apply has_go_type_to_abstract in H.
    hnf in H.
    iInduction H as [ | | | | | | | | | | | | ] "IH" forall (l Φ);
      subst; simpl; wp_pures; rewrite ?loc_add_0 ?right_id.
    1-11: wp_apply (wp_load with "[$]"); auto.
    + by iApply "HΦ".
    + rewrite big_opL_app.
      iDestruct "Hl" as "[Hv1 Hv2]".
      wp_apply ("IH" with "Hv1"); iIntros "Hv1".
      wp_apply ("IH1" with "[Hv2]"); [ | iIntros "Hv2" ].
      { erewrite has_go_abstract_type_len; [|done].
        setoid_rewrite Z.mul_1_r.
        setoid_rewrite Nat2Z.inj_add.
        setoid_rewrite loc_add_assoc.
        iFrame. }
      wp_pures.
      iApply "HΦ"; iFrame.
      erewrite has_go_abstract_type_len; [|done].
      setoid_rewrite Z.mul_1_r.
      setoid_rewrite Nat2Z.inj_add.
      setoid_rewrite loc_add_assoc.
      by iFrame.
  Qed.

  Lemma tac_wp_load_ty Δ Δ' s E i K l q t v Φ is_pers :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (is_pers, typed_pointsto l q t v)%I →
    envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (load_ty t (LitV l)) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? ? Hwp.
    rewrite -wp_bind. eapply bi.wand_apply; first by apply bi.wand_entails, wp_typed_load.
    iIntros "H".
    rewrite into_laterN_env_sound -bi.later_sep envs_lookup_split //; simpl.
    iNext.
    destruct is_pers; simpl.
    + iDestruct "H" as "[#? H]". iFrame "#". iIntros.
      iSpecialize ("H" with "[$]"). by wp_apply Hwp.
    + iDestruct "H" as "[? H]". iFrame. iIntros.
      iSpecialize ("H" with "[$]"). by wp_apply Hwp.
  Qed.

  Lemma wp_store stk E l v v' :
    {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ stk; E
    {{{ RET LitV LitUnit; l ↦ v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". rewrite /Store.
    wp_apply (wp_prepare_write with "Hl"); iIntros "[Hl Hl']".
    by wp_apply (wp_finish_store with "[$Hl $Hl']").
  Qed.

  Instance into_ih_option_match {PROP : bi} {A} φ (oa : option A) Δ (Φ : A → PROP) :
    (∀ a : A, IntoIH (φ a) Δ (Φ a)) →
    IntoIH (match oa with | Some a => φ a | None => True end) Δ
           (match oa with | Some a => Φ a | None => True end).
  Proof.
    intros.
    unfold IntoIH.
    intros. iStartProof. iIntros "#Henv".
    destruct oa.
    { by iApply H. }
    done.
  Qed.

  Instance into_ih_let_pair {PROP : bi} {A B} φ (x : A*B) Δ (Φ : _ → _ → PROP) :
    (∀ (a : A) (b : B), IntoIH (φ a b) Δ (Φ a b)) →
    IntoIH (let '(a, b) := x in φ a b)
           Δ
           (let '(a, b) := x in Φ a b).
  Proof.
    intros.
    destruct x.
    apply _.
  Qed.

  Lemma wp_typed_store stk E l t v0 v :
    has_go_type v t ->
    {{{ ▷ l ↦[t] v0 }}}
      (#l <-[t] v)%V @ stk; E
    {{{ RET #(); l ↦[t] v }}}.
  Proof.
    intros Hty.
    iIntros (Φ) ">Hl HΦ".
    unseal.
    iDestruct "Hl" as "[Hl %Hty_old]".
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j)↦ vj) -∗ Φ #()))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ".
      iSplit; eauto. }
    unfold store_ty.
    (* apply has_go_type_to_abstract in Hty_old as Hty_abs_old.
    assert (∃ g, g = go_type_interp t) as [g Hty_eq].
    { by eexists _. }
    rewrite -Hty_eq in Hty_abs_old |- *. *)
    rename v into v'. rename v0 into v.
    rename l into l'.
    Locate "iInduction".
    Print IntoIH.
    Search IntoIH.
    (* generalize dependent t.
    generalize dependent v'.
    eapply (has_go_type_ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    {
    } *)
    iInduction Hty_old as [ | | | | | | | | | | | | | | | | | | |] "IH" using has_go_type_ind forall (v' Hty l' Φ) "HΦ".
    1-10: simpl; rewrite ?loc_add_0 ?right_id; wp_pures; wp_apply (wp_store with "[$]");
      auto; iIntros "H"; iApply "HΦ"; subst;
      match goal with
      | [ H : (has_go_type ?v ?T) |- _ ] =>
        eassert (∃ t, t = T ∧ has_go_type v t) as [? [Heq Hty2]]; first (eexists _; done)
      end;
      destruct Hty2 using has_go_type_ind; subst; try congruence; simpl;
      rewrite ?loc_add_0 ?right_id; iFrame.
    1-2,7-8: simpl; rewrite ?loc_add_0 ?right_id; wp_pures;
      match goal with
      | [ H : (has_go_type ?v ?T) |- _ ] =>
        eassert (∃ t, t = T ∧ has_go_type v t) as [? [Heq Hty2]]; first (eexists _; done)
      end; iDestruct "Hl" as "(Hl1 & Hl2 & Hl3)";
      destruct Hty2 using has_go_type_ind; subst; try congruence; simpl;
      rewrite /slice_val; wp_pures;
        wp_apply (wp_store with "[$Hl1]"); iIntros; wp_pures;
        wp_apply (wp_store with "[$Hl2]"); iIntros;
        wp_apply (wp_store with "[$Hl3]"); iIntros;
        iApply "HΦ"; rewrite ?loc_add_0 ?right_id; iFrame.
    2-6: simpl; rewrite ?loc_add_0 ?right_id; wp_pures; wp_apply (wp_store with "[$]");
      auto; iIntros "H"; iApply "HΦ"; subst;
      match goal with
      | [ H : (has_go_type ?v ?T) |- _ ] =>
        eassert (∃ t, t = T ∧ has_go_type v t) as [? [Heq Hty2]]; first (eexists _; done)
      end;
      destruct Hty2 using has_go_type_ind; subst; try congruence; simpl;
      rewrite ?loc_add_0 ?right_id; iFrame.

    (* case: structT *)
    - induction d.
      {
        simpl. wp_pures. iApply "HΦ".
        match goal with
        | [ H : (has_go_type ?v ?T) |- _ ] =>
          eassert (∃ t, t = T ∧ has_go_type v t) as [? [Heq Hty2]]; first (eexists _; done)
        end. destruct Hty2 using has_go_type_ind; subst; try congruence; simpl.
        inversion Heq; subst.
        simpl. done.
      }
      match goal with
      | [ H : (has_go_type ?v ?T) |- _ ] =>
        eassert (∃ t, t = T ∧ has_go_type v t) as [? [Heq Hty2]]; first (eexists _; done)
      end. destruct Hty2 using has_go_type_ind; subst; try congruence; simpl.
      inversion Heq; subst.

      destruct a.
      wp_pures.
      iDestruct "IH" as "[IH1 IH]".
      destruct assocl_lookup.
      wp_apply "IH1".

      rewrite big_opL_app.
      inversion Hty_abs; subst; clear Hty_abs.
      wp_pures.
      iDestruct "Hl" as "[Hv1 Hv2]".
      wp_apply ("IH" with "[] [] [] Hv1").
      2:{
        iPureIntro.
        revert v0.
        apply has_go_type_ind.
        inversion Hty. iPuredone.
      }
      iIntros "Hv1".
      wp_apply ("IH1" with "[//] [Hv2]"); [ | iIntros "Hv2" ].
      { erewrite has_go_abstract_type_len; [|done].
        setoid_rewrite Z.mul_1_r.
        setoid_rewrite Nat2Z.inj_add.
        setoid_rewrite loc_add_assoc.
        iFrame. }
      wp_pures.
      iApply "HΦ". iFrame.
      rewrite has_go_abstract_type_len; [|done].
      setoid_rewrite Z.mul_1_r.
      setoid_rewrite Nat2Z.inj_add.
      setoid_rewrite loc_add_assoc.
      by iFrame.
  Qed.

  Lemma tac_wp_store_ty Δ Δ' Δ'' stk E i K l t v v' Φ :
    has_go_type v' t ->
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, l ↦[t] v)%I →
    envs_simple_replace i false (Esnoc Enil i (l ↦[t] v')) Δ' = Some Δ'' →
    envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ stk; E {{ Φ }}) →
    envs_entails Δ (WP fill K (store_ty t (PairV (LitV l) v')) @ stk; E {{ Φ }}).
  Proof.
    intros Hty.
    rewrite envs_entails_unseal=> ????.
    rewrite -wp_bind. eapply bi.wand_apply; first by eapply bi.wand_entails, wp_typed_store.
    rewrite into_laterN_env_sound -bi.later_sep envs_simple_replace_sound //; simpl.
    rewrite right_id. by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
  Qed.

Lemma wp_typed_cmpxchg_fail s E l dq v' v1 v2 t :
  (go_type_interp t) = cellT →
  has_go_type v1 t →
  vals_compare_safe v' v1 →
  v' ≠ v1 →
  {{{ ▷ l ↦[t]{dq} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦[t]{dq} v' }}}.
Proof.
  unseal.
  unfold has_go_type in *.
  generalize dependent (go_type_interp t).
  intros. subst.
  iIntros "[Hpre >%Hv'] HΦ".
  inversion Hv'.
  all: subst; simpl;
    rewrite loc_add_0 right_id;
    wp_apply (wp_cmpxchg_fail with "[$]");
    [done| inversion H0; subst; done | iIntros "?"; iApply "HΦ"; iFrame; done].
Qed.

End goose_lang.


Notation "l ↦[ t ] dq v" := (typed_pointsto l dq t v%V)
                              (at level 20, dq custom dfrac at level 50, t at level 50,
                               format "l  ↦[ t ] dq  v") : bi_scope.

Tactic Notation "wp_load" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦[t] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    ( first
        [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load_ty _ _ _ _ _ K))
        |fail 1 "wp_load: cannot find 'load_ty' in" e];
      [tc_solve
      |solve_pointsto ()
      |wp_finish] )
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_] _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦[t] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store_ty _ _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'store_ty' in" e];
    [(tc_solve || fail "could not establish [has_go_type]") (* solve [has_go_type v' t] *)
    |tc_solve
    |solve_pointsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.
