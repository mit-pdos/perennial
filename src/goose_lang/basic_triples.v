From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export
     lang notation array typing struct
     tactics lifting proofmode.
From Perennial.goose_lang Require Import slice.
Import uPred.

Set Default Proof Using "Type".

Module Slice.
  Record t :=
    mk { ptr: loc;
         sz: u64;
         cap: u64; }.
  Notation extra s := (int.val (cap s) - int.val (sz s)).
End Slice.
Notation slice_extra s := (Slice.extra s).

Section heap.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types t : ty.
Implicit Types stk : stuckness.
Implicit Types off : nat.

Definition ArbitraryIntUpto: val :=
  λ: "bound",
  let: "z" := ArbitraryInt in
  if: Var "z" < Var "bound" then Var "z" else Var "bound".

Lemma wp_ArbitraryIntUpto stk E (max: u64) :
  {{{ True }}}
    ArbitraryIntUpto #max @ stk; E
  {{{ (x:u64), RET #x; ⌜int.val x <= int.val max⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_ArbitraryInt.
  iIntros (x) "_".
  wp_pures.
  wp_if_destruct.
  - iApply "HΦ".
    iPureIntro.
    word.
  - iApply "HΦ".
    iPureIntro.
    word.
Qed.

Lemma wp_ref_to stk E t v :
  val_ty v t ->
  {{{ True }}} ref_to t (Val v) @ stk; E {{{ l, RET LitV (LitLoc l); l ↦[t] v }}}.
Proof.
  iIntros (Hty Φ) "_ HΦ".
  wp_call.
  iApply wp_alloc; eauto with lia.
Qed.

Lemma tac_wp_alloc Δ Δ' s E j K v t Φ :
  val_ty v t ->
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦[t] v)) Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Val $ LitV l) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (ref_to t (Val v)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> Hty ? HΔ.
  rewrite -wp_bind /ref_to. eapply wand_apply; first exact: wp_ref_to.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite right_id wand_elim_r.
Qed.

Lemma wp_store s E l v v' :
  {{{ ▷ l ↦ Free v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ Free v }}}.
Proof.
  iIntros (Φ) "Hl HΦ". unfold Store.
  wp_lam. wp_let. wp_bind (PrepareWrite _).
  iApply (wp_prepare_write with "Hl").
  iIntros "!> Hl".
  wp_seq. by iApply (wp_finish_store with "Hl").
Qed.

Lemma tac_wp_store Δ Δ' Δ'' s E i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ Free v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ Free v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Store (LitV l) (Val v')) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ????.
  rewrite -wp_bind. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

(* local version just for this file *)
Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Theorem wp_forBreak (I X: iProp Σ) stk E (body: val) :
  {{{ I }}}
    body #() @ stk; E
  {{{ r, RET #r; I ∗ ⌜r=true⌝ ∨ X ∗ ⌜r=false⌝ }}} -∗
  {{{ I }}}
    (for: (λ: <>, #true)%V ; (λ: <>, (λ: <>, #())%V #())%V :=
       body) @ stk; E
  {{{ RET #(); X }}}.
Proof.
  iIntros "#Hbody".
  iIntros (Φ) "!> I HΦ".
  rewrite /For.
  wp_lam.
  wp_let.
  wp_let.
  wp_pure (Rec _ _ _).
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  iLöb as "IH".
  wp_pures.
  iDestruct ("Hbody" with "I") as "Hbody1".
  wp_bind (body _).
  iApply "Hbody1".
  iNext.
  iIntros (r) "Hr".
  iDestruct "Hr" as "[[I %] | [X %]]"; subst.
  - iDestruct ("IH" with "I HΦ") as "IH1".
    wp_let.
    wp_if.
    wp_lam.
    wp_lam.
    wp_pure (Rec _ _ _).
    wp_lam.
    iApply "IH1".
  - wp_pures.
    iApply "HΦ".
    iApply "X".
Qed.

Theorem wp_forUpto (I: u64 -> iProp Σ) stk E (max:u64) (l:loc) (body: val) :
  (∀ (i:u64),
      {{{ I i ∗ l ↦ Free #i ∗ ⌜int.val i < int.val max⌝ }}}
        body #() @ stk; E
      {{{ RET #true; I (word.add i (U64 1)) ∗ l ↦ Free #i }}}) -∗
  {{{ I 0 ∗ l ↦ Free #0 }}}
    (for: (λ:<>, #max > ![uint64T] #l)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l + #1)%V :=
       body) @ stk; E
  {{{ RET #(); I max ∗ l ↦ Free #max }}}.
Proof.
  iIntros "#Hbody".
  iIntros (Φ) "!> (H0 & Hl) HΦ".
  rewrite /For /Continue.
  wp_lam.
  wp_let.
  wp_let.
  wp_pure (Rec _ _ _).
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  remember (U64 0) as x.
  assert (0 <= int.val x <= int.val max) as Hbounds by (subst; word).
  clear Heqx.
  iDestruct "H0" as "HIx".
  iLöb as "IH" forall (x Hbounds).
  wp_pures.
  wp_load.
  wp_pures.
  wp_if_destruct.
  - wp_apply ("Hbody" with "[$HIx $Hl]").
    { iPureIntro; lia. }
    iIntros "[HIx Hl]".
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply (wp_store with "Hl"); iIntros "Hl".
    wp_seq.
    iApply ("IH" with "[] HIx Hl").
    { iPureIntro; word. }
    iFrame.
  - assert (int.val x = int.val max) by word.
    apply word.unsigned_inj in H; subst.
    iApply ("HΦ" with "[$]").
Qed.

Theorem val_ty_flatten_length v t :
  val_ty v t ->
  length (flatten_struct v) = length (flatten_ty t).
Proof.
  induction 1; simpl; auto.
  - inversion H; subst; auto.
  - rewrite ?app_length.
    lia.
Qed.

Theorem ty_size_offset t l j : l +ₗ (length (flatten_ty t) + j)%nat = l +ₗ ty_size t +ₗ j.
Proof.
  rewrite loc_add_assoc.
  f_equal.
  rewrite <- ty_size_length.
  pose proof (ty_size_ge0 t).
  lia.
Qed.

Theorem struct_ptsto_pair_split l v1 t1 v2 t2 :
  l ↦[t1 * t2] (v1, v2) ⊣⊢ l ↦[t1] v1 ∗ (l +ₗ ty_size t1) ↦[t2] v2.
Proof.
  rewrite /struct_mapsto /= big_opL_app.
  iSplit.
  - iIntros "[[Hv1 Hv2] %]".
    inversion H; subst; clear H.
    iSplitL "Hv1"; iFrame; eauto.
    iSplitL; eauto.
    erewrite val_ty_flatten_length by eauto.
    setoid_rewrite ty_size_offset.
    iFrame.
  - iIntros "[[Hv1 %] [Hv2 %]]".
    erewrite val_ty_flatten_length by eauto.
    setoid_rewrite ty_size_offset.
    iFrame.
    iPureIntro.
    constructor; auto.
Qed.

Lemma wp_LoadAt stk E l t v :
  {{{ l ↦[t] v }}}
    load_ty t #l @ stk; E
  {{{ RET v; l ↦[t] v }}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  iDestruct "Hl" as "[Hl %]".
  hnf in H.
  iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j)↦ Free vj) -∗ Φ v))%I with "[HΦ]" as "HΦ".
  { iIntros "!> HPost".
    iApply "HΦ".
    iSplit; eauto. }
  (* TODO: we have to rename this so it doesn't conflict with a name generated
  by induction; seems like a bug *)
  rename l into l'.
  (iInduction H as [ | | | | | | | ] "IH" forall (l' Φ));
    simpl;
    rewrite ?loc_add_0 ?right_id;
    wp_pures.
  - inversion H; subst; clear H; simpl; wp_load; iApply ("HΦ" with "[$]").
  - rewrite big_opL_app.
    iDestruct "Hl" as "[Hv1 Hv2]".
    wp_bind (load_ty t1 _).
    iApply ("IH" with "Hv1").
    iIntros "!> Hv1".
    wp_pures.
    rewrite Z.mul_1_r.
    wp_bind (load_ty t2 _).
    iApply ("IH1" with "[Hv2]").
    + erewrite val_ty_flatten_length; eauto.
      setoid_rewrite ty_size_offset.
      iFrame.
    + iIntros "!> Hv2".
      wp_pures.
      iApply "HΦ"; iFrame.
      erewrite val_ty_flatten_length by eauto.
      setoid_rewrite ty_size_offset.
      iFrame.
  - wp_load.
    iApply ("HΦ" with "[$]").
  - wp_load.
    iApply ("HΦ" with "[$]").
  - wp_load.
    iApply ("HΦ" with "[$]").
  - wp_load.
    iApply ("HΦ" with "[$]").
  - wp_load.
    iApply ("HΦ" with "[$]").
  - wp_load.
    iApply ("HΦ" with "[$]").
Qed.

Theorem struct_mapsto_ty l v t :
  l ↦[t] v -∗ ⌜val_ty v t⌝.
Proof.
  iIntros "[_ %] !%//".
Qed.

Lemma wp_load_offset s E l off t vs v :
  vs !! off = Some v →
  {{{ l ↦∗[t] vs }}} load_ty t #(l +ₗ[t] off) @ s; E {{{ RET v; l ↦∗[t] vs ∗ ⌜val_ty v t⌝ }}}.
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_LoadAt with "Hl1"). iIntros "!> Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iDestruct (struct_mapsto_ty with "Hl1") as %Hty.
  iSplitL; eauto.
  iApply ("Hl2" with "[$]").
Qed.

(* TODO: move this to common tactics *)
Ltac invc H := inversion H; subst; clear H.

Lemma wp_StoreAt stk E l t v0 v :
  val_ty v t ->
  {{{ l ↦[t] v0 }}}
    store_ty t #l v @ stk; E
  {{{ RET #(); l ↦[t] v }}}.
Proof.
  intros Hty; hnf in Hty.
  iIntros (Φ) "[Hl %] HΦ".
  hnf in H.
  iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j)↦ Free vj) -∗ Φ #()))%I with "[HΦ]" as "HΦ".
  { iIntros "!> HPost".
    iApply "HΦ".
    iSplit; eauto. }
  rename v into v'.
  rename l into l'.
  (iInduction H as [ | | | | | | | ] "IH" forall (v' Hty l' Φ));
    simpl;
    rewrite ?loc_add_0 ?right_id;
    wp_pures;
    try wp_store.
  - invc H; invc Hty;
      simpl;
      rewrite ?loc_add_0 ?right_id;
      wp_store;
      iApply ("HΦ" with "[$]").
  - rewrite big_opL_app.
    erewrite val_ty_flatten_length by eauto.
    setoid_rewrite ty_size_offset.
    invc Hty.
    { by invc H1. (* can't be a pair and a base literal *) }
    iDestruct "Hl" as "[Hv1 Hv2]".
    wp_pures.
    wp_bind (store_ty t1 _ _).
    iApply ("IH" with "[//] Hv1").
    iIntros "!> Hv1".
    wp_pures.
    rewrite Z.mul_1_r.
    iApply ("IH1" with "[//] Hv2").
    iIntros "!> Hv2".
    iApply "HΦ".
    simpl.
    rewrite big_opL_app.
    iFrame.
    erewrite val_ty_flatten_length by eauto.
    setoid_rewrite ty_size_offset.
    iFrame.
  - invc Hty; simpl; rewrite ?loc_add_0 ?right_id;
      iApply ("HΦ" with "[$]").
  - invc Hty; simpl; rewrite ?loc_add_0 ?right_id;
      iApply ("HΦ" with "[$]").
  - invc Hty; simpl; rewrite ?loc_add_0 ?right_id;
      iApply ("HΦ" with "[$]").
  - invc Hty; simpl; rewrite ?loc_add_0 ?right_id;
      iApply ("HΦ" with "[$]").
  - invc Hty; simpl; rewrite ?loc_add_0 ?right_id;
      iApply ("HΦ" with "[$]").
  - invc Hty; simpl; rewrite ?loc_add_0 ?right_id;
      iApply ("HΦ" with "[$]").
Qed.

Lemma wp_store_offset s E l off vs t v :
  is_Some (vs !! off) →
  val_ty v t ->
  {{{ ▷ l ↦∗[t] vs }}} store_ty t #(l +ₗ[t] off) v @ s; E {{{ RET #(); l ↦∗[t] <[off:=v]> vs }}}.
Proof.
  iIntros ([w Hlookup] Hty Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_StoreAt _ _ _ _ _ _ Hty with "Hl1"). iIntros "!> Hl1".
  iApply "HΦ". iApply ("Hl2" with "Hl1").
Qed.

Fixpoint getValField_fs (fs:list (string*ty)) (f0:string) (v:val) : option (val*ty) :=
  match fs with
  | nil => None
  | (f, t) :: nil => if String.eqb f f0 then Some (v, t) else None
  | (f, t) :: fs =>  match v with
                   | PairV v1 v2 =>
                     if String.eqb f f0
                     then Some (v1, t)
                     else getValField_fs fs f0 v2
                   | _ => None (* v is ill-typed *)
                   end
  end.

Definition getValField (d:descriptor) (f:string) (v:val) : option (val*ty) :=
  getValField_fs d.(fields) f v.

Theorem getValField_wt d f v :
  val_ty v (struct.t d) ->
  forall z t, field_offset d.(fields) f = Some (z, t) ->
         exists fv, getValField d f v = Some (fv, t) /\
               val_ty fv t.
Proof.
  rewrite /getValField.
  rewrite /struct.t.
  rename f into f0.
  destruct d as [fs].
  destruct fs as [|(f&t) fs].
  { cbn; intros; congruence. }
  cbn [fields struct_ty_prod snd].
  generalize dependent f.
  generalize dependent t.
  generalize dependent v.
  induction fs.
  - cbn; intros.
    destruct (String.eqb_spec f f0); inversion H0; subst; clear H0.
    eexists; eauto.
  - intros v t f.
    cbn [struct_ty_aux snd].
Abort.

Fixpoint setValField_fs (fs:list (string*ty)) (f0:string) (v:val) (fv':val) : option val :=
  match fs with
  | nil => None
  | (f, t) :: nil => if String.eqb f f0 then Some fv' else None
  | (f, t) :: fs =>  match v with
                   | PairV v1 v2 =>
                     if String.eqb f f0
                     then Some (fv', v2)%V
                     else (fun v2' => (v1, v2')%V) <$> setValField_fs fs f0 v2 fv'
                   | _ => None (* v is ill-typed *)
                   end
  end.

Definition setValField (d:descriptor) (f:string) (v:val) (fv':val) : option val :=
  setValField_fs d.(fields) f v fv'.

Theorem setValField_wt d f v fv' :
  val_ty v (struct.t d) ->
  forall z t, field_offset d.(fields) f = Some (z, t) ->
         val_ty fv' t ->
         exists v', setValField d f v fv' = Some v' /\
               val_ty v' (struct.t d).
Proof.
Abort.

(*
Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply wp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.
*)

Coercion slice_val (s: Slice.t) : val := (#s.(Slice.ptr), #s.(Slice.sz), #s.(Slice.cap)).

(* is_slice_small is a smaller footprint version if is_slice that imprecisely
ignores the extra capacity; it allows for weaker preconditions for code which
doesn't make use of capacity *)
Definition is_slice_small (s: Slice.t) (t:ty) (vs: list val): iProp Σ :=
  s.(Slice.ptr) ↦∗[t] vs ∗ ⌜length vs = int.nat s.(Slice.sz)⌝.

Definition is_slice (s: Slice.t) (t:ty) (vs: list val): iProp Σ :=
  is_slice_small s t vs ∗
  (⌜0 ≤ Slice.extra s⌝ ∗
   (s.(Slice.ptr) +ₗ[t] int.val s.(Slice.sz)) ↦∗[t]
      (replicate (Z.to_nat $ Slice.extra s) (zero_val t))).

Lemma is_slice_to_small s t vs :
  is_slice s t vs -∗ is_slice_small s t vs.
Proof.
  iDestruct 1 as "[$ _]".
Qed.

Lemma replicate_0 A (x:A) : replicate 0 x = [].
Proof. reflexivity. Qed.

Lemma is_slice_intro l t (sz: u64) vs :
  l ↦∗[t] vs -∗ ⌜length vs = int.nat sz⌝ -∗
  is_slice (Slice.mk l sz sz) t vs.
Proof.
  iIntros "H1 H2"; rewrite /is_slice; iFrame.
  simpl.
  rewrite Z.sub_diag.
  iSplitR; auto.
  rewrite replicate_0.
  rewrite array_nil.
  auto.
Qed.

Theorem is_slice_elim s t vs :
  is_slice s t vs -∗ s.(Slice.ptr) ↦∗[t] vs ∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  rewrite /is_slice.
  iIntros "[(Hs&%) (%&_)]".
  by iFrame.
Qed.

Definition slice_val_fold (ptr: loc) (sz: u64) (cap: u64) :
  (#ptr, #sz, #cap)%V = slice_val (Slice.mk ptr sz cap) := eq_refl.

(* TODO: order commands so primitives are opaque only after proofs *)
Transparent raw_slice.

Lemma wp_make_cap stk E (sz: u64) :
  {{{ True }}}
    make_cap #sz @ stk; E
  {{{ (cap:u64), RET #cap; ⌜int.val cap >= int.val sz⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_ArbitraryInt.
  iIntros (extra) "_".
  wp_pures.
  wp_if_destruct; wp_pures; iApply "HΦ"; iPureIntro.
  - rewrite word.unsigned_add /word.wrap in Heqb.
    rewrite word.unsigned_add /word.wrap.
    word.
  - word.
Qed.

Lemma wp_raw_slice stk E l vs (sz: u64) t :
  {{{ array l t vs ∗ ⌜length vs = int.nat sz⌝ }}}
    raw_slice t #l #sz @ stk; E
  {{{ sl, RET slice_val sl; is_slice sl t vs }}}.
Proof.
  iIntros (Φ) "(Hslice&%) HΦ".
  wp_call.
  rewrite slice_val_fold. iApply "HΦ".
  iApply (is_slice_intro with "Hslice").
  iPureIntro; auto.
Qed.

Lemma wp_slice_len stk E (s: Slice.t) (Φ: val -> iProp Σ) :
    Φ #(s.(Slice.sz)) -∗ WP slice.len (slice_val s) @ stk; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  wp_call.
  iApply "HΦ".
Qed.

Lemma wp_slice_ptr stk E (s: Slice.t) (Φ: val -> iProp Σ) :
    Φ #(s.(Slice.ptr)) -∗ WP slice.ptr (slice_val s) @ stk; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  wp_call.
  iApply "HΦ".
Qed.

Theorem is_slice_zero t :
  is_slice (Slice.mk null (U64 0) (U64 0)) t [].
Proof.
  rewrite /is_slice /=.
  rewrite /array.
  iSplit; auto.
  iSplit; auto.
  rewrite array_nil //.
Qed.

Theorem zero_slice_val t :
  zero_val (slice.T t) = slice_val (Slice.mk null (U64 0) (U64 0)).
Proof.
  reflexivity.
Qed.

Lemma u64_val_ne (x1 x2:u64) :
  #x1 ≠ #x2 -> int.val x1 ≠ int.val x2.
Proof.
  intros Hne.
  intros Heq%word.unsigned_inj.
  congruence.
Qed.

Lemma array_split (n:Z) l t vs :
  0 <= n ->
  Z.to_nat n <= length vs ->
  array l t vs ⊣⊢
        array l t (take (Z.to_nat n) vs) ∗ array (l +ₗ[t] n) t (drop (Z.to_nat n) vs).
Proof.
  intros Hn Hlength.
  rewrite <- (take_drop (Z.to_nat n) vs) at 1.
  rewrite array_app.
  rewrite take_length.
  rewrite Nat.min_l; last lia.
  rewrite Z2Nat.id; last lia.
  auto.
Qed.

Lemma array_replicate_split (n1 n2 n: nat) l t v :
  (n1 + n2 = n)%nat ->
  l ↦∗[t] replicate n v -∗
    l ↦∗[t] replicate n1 v ∗
    (l +ₗ[t] n1) ↦∗[t] replicate n2 v.
Proof.
  iIntros (<-) "Ha".
  iDestruct (array_split n1 with "Ha") as "[Ha1 Ha2]".
  { word. }
  { rewrite replicate_length.
    word. }
  rewrite take_replicate drop_replicate.
  rewrite -> Nat.min_l by word.
  iFrame.
  iSplitL "Ha1".
  - iExactEq "Ha1"; repeat (f_equal; try word).
  - iExactEq "Ha2"; repeat (f_equal; try word).
Qed.

Ltac word_eq :=
  repeat (f_equal; try word).

Lemma wp_new_slice s E t (sz: u64) :
  {{{ True }}}
    NewSlice t #sz @ s; E
  {{{ sl, RET slice_val sl; is_slice sl t (replicate (int.nat sz) (zero_val t)) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_if_destruct.
  - wp_pures.
    rewrite /slice.nil slice_val_fold.
    iApply "HΦ".
    rewrite replicate_0.
    iApply is_slice_zero.
  - wp_apply wp_make_cap.
    iIntros (cap Hcapge).
    wp_pures.
    wp_apply (wp_allocN _ _ _ t); eauto.
    { apply u64_val_ne in Heqb.
      change (int.val 0) with 0 in Heqb.
      word. }
  iIntros (l) "Hl".
  wp_pures.
  rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice /is_slice_small /=.
  iDestruct (array_replicate_split (int.nat sz) (int.nat cap - int.nat sz) with "Hl") as "[Hsz Hextra]";
    first by word.
  rewrite replicate_length.
  iFrame.
  iSplitR; first by auto.
  iSplitR; first by auto with lia.
  iExactEq "Hextra"; word_eq.
Qed.

Theorem wp_SliceSingleton Φ stk E t x :
  val_ty x t ->
  (∀ s, is_slice s t [x] -∗ Φ (slice_val s)) -∗
  WP SliceSingleton x @ stk; E {{ Φ }}.
Proof.
  iIntros (Hty) "HΦ".
  wp_call.
  wp_apply (wp_allocN _ _ _ t); eauto.
  { word. }
  change (replicate (int.nat 1) x) with [x].
  iIntros (l) "Hl".
  wp_steps.
  rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice /=.
  iFrame.
  iSplit; auto.
  iSplit; auto.
  rewrite replicate_0 array_nil //.
Qed.

Definition slice_take (sl: Slice.t) (t:ty) (n: u64) : Slice.t :=
  {| Slice.ptr := sl.(Slice.ptr);
     Slice.sz := n;
     Slice.cap := n;
  |}.

Definition slice_skip (sl: Slice.t) (t:ty) (n: u64) : Slice.t :=
  {| Slice.ptr := sl.(Slice.ptr) +ₗ[t] int.val n;
     Slice.sz := word.sub sl.(Slice.sz) n;
     Slice.cap := word.sub sl.(Slice.cap) n;
  |}.

Lemma slice_split sl (n: u64) t vs :
  0 <= int.val n ->
  int.nat n <= length vs ->
  is_slice sl t vs -∗ is_slice (slice_take sl t n) t (take (int.nat n) vs) ∗
           is_slice (slice_skip sl t n) t (drop (int.nat n) vs).
Proof.
  iIntros (Hpos Hbound) "Hs".
  iDestruct "Hs" as "((Hs&%)&(%&Hfree))".
  rewrite /slice_take /slice_skip /=.
  iDestruct (array_split (int.val n) with "Hs") as "(Htake&Hdrop)"; [ lia .. | ].
  iSplitL "Htake".
  - iApply (is_slice_intro with "Htake").
    rewrite take_length.
    iPureIntro; word.
  - rewrite /is_slice /is_slice_small /=.
    rewrite drop_length.
    iFrame.
    iSplitR; first by iPureIntro; word.
    iSplitR; first by iPureIntro; word.
    match goal with
    | |- context[Esnoc _ (INamed "Hfree") (?l ↦∗[_] replicate ?n _)] =>
      match goal with
      | |- context[envs_entails _ (?l' ↦∗[_] replicate ?n' _)] =>
        replace l with l';
          [ replace n with n' by word | ];
          [ iFrame | ]
      end
    end.
    rewrite loc_add_assoc.
    f_equal.
    word.
Qed.

Lemma wp_SliceSkip' Φ stk E s t (n: u64):
  ⌜int.val n ≤ int.val s.(Slice.sz)⌝ -∗
  Φ (slice_val (slice_skip s t n)) -∗
  WP (SliceSkip t (slice_val s) #n) @ stk; E {{ Φ }}.
Proof.
  iIntros "% HΦ".
  wp_call.
  wp_call.
  wp_call.
  wp_call.
  iApply "HΦ".
Qed.

Lemma wp_SliceTake Φ stk E s t vs (n: u64):
  ⌜int.val n ≤ int.val s.(Slice.sz)⌝ -∗
  Φ (slice_val (slice_take s t n)) -∗
  WP (SliceTake (slice_val s) #n) @ stk; E {{ Φ }}.
Proof.
  iIntros "% HΦ".
  wp_call.
  wp_call.
  wp_if_destruct.
  - wp_apply wp_panic.
    word.
  - wp_call.
    iApply "HΦ".
Qed.

Lemma wp_SliceSubslice Φ stk E s t (n1 n2: u64):
  ⌜int.val n1 ≤ int.val n2 ∧ int.val n2 ≤ int.val s.(Slice.sz)⌝ -∗
  Φ (slice_val (Slice.mk (s.(Slice.ptr) +ₗ[t] int.val n1) (word.sub n2 n1) (word.sub n2 n1))) -∗
  WP (SliceSubslice t (slice_val s) #n1 #n2) @ stk; E {{ Φ }}.
Proof.
  iIntros "% HΦ".
  wp_call.
  wp_if_destruct.
  - word.
  - wp_call.
    wp_if_destruct.
    + exfalso.
      rewrite word.unsigned_sub in Heqb0.
      rewrite -> wrap_small in Heqb0 by word.
      word.
    + wp_call.
      iApply "HΦ".
Qed.

Lemma wp_SliceGet stk E sl t vs (i: u64) v0 :
  {{{ is_slice_small sl t vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet t sl #i @ stk; E
  {{{ RET v0; is_slice_small sl t vs ∗ ⌜val_ty v0 t⌝ }}}.
Proof.
  iIntros (Φ) "[Hsl %] HΦ".
  destruct sl as [ptr sz].
  repeat wp_step.
  rewrite /is_slice_small /=.
  iDestruct "Hsl" as "(Hsl&%)"; simpl.
  repeat wp_call.
  iDestruct (update_array ptr _ _ _ _ H with "Hsl") as "[Hi Hsl']".
  pose proof (word.unsigned_range i).
  word_cleanup.
  iDestruct (struct_mapsto_ty with "Hi") as %Hty.
  wp_apply (wp_LoadAt with "Hi"); iIntros "Hi".
  iApply "HΦ".
  iFrame.
  { iDestruct ("Hsl'" with "Hi") as "Hsl".
    erewrite list_insert_id by eauto; auto. }
Qed.

Lemma list_lookup_lt A (l: list A) (i: nat) :
  (i < length l)%nat ->
  exists x, l !! i = Some x.
Proof.
  intros.
  destruct_with_eqn (l !! i); eauto.
  exfalso.
  apply lookup_ge_None in Heqo.
  lia.
Qed.

Lemma list_lookup_Z_lt {A} (l: list A) (i: Z) :
  (0 <= i < Z.of_nat (length l)) ->
  exists x, l !! Z.to_nat i = Some x.
Proof.
  intros.
  apply list_lookup_lt.
  apply Nat2Z.inj_le; lia.
Qed.

Lemma is_slice_small_sz s t vs :
  is_slice_small s t vs -∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  iIntros "(_&%) !% //".
Qed.

Lemma is_slice_sz s t vs :
  is_slice s t vs -∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  iIntros "((_&%)&_) !% //".
Qed.

Theorem wp_forSlice (I: u64 -> iProp Σ) stk E s t vs (body: val) :
  (∀ (i: u64) (x: val),
      {{{ I i ∗ ⌜int.val i < int.val s.(Slice.sz)⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ }}}
        body #i x @ stk; E
      {{{ RET #(); I (word.add i (U64 1)) }}}) -∗
    {{{ I (U64 0) ∗ is_slice_small s t vs }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) ∗ is_slice_small s t vs }}}.
Proof.
  iIntros "#Hind".
  iIntros (Φ) "!> [Hi0 Hs] HΦ".
  wp_call.
  wp_apply wp_slice_len.
  wp_steps.
  remember 0 as z.
  assert (0 <= z <= int.val s.(Slice.sz)) by word.
  iDestruct (is_slice_small_sz with "Hs") as %Hslen.
  clear Heqz; generalize dependent z.
  intros z Hzrange.
  pose proof (word.unsigned_range s.(Slice.sz)).
  assert (int.val (U64 z) = z) by (rewrite /U64; word).
  iRename "Hi0" into "Hiz".
  (iLöb as "IH" forall (z Hzrange H0) "Hiz").
  wp_if_destruct.
  - destruct (list_lookup_Z_lt vs z) as [xz Hlookup]; first word.
    wp_apply (wp_SliceGet with "[$Hs]").
    { replace (int.val z); eauto. }
    iIntros "[Hs Hty]".
    iDestruct "Hty" as %Hty.
    wp_steps.
    wp_apply ("Hind" with "[$Hiz]").
    { iPureIntro; split; eauto.
      replace (int.val z); eauto. }
    iIntros "Hiz1".
    wp_steps.
    assert (int.val (z + 1) = int.val z + 1).
    { rewrite word.unsigned_of_Z.
      rewrite wrap_small; try lia. }
    replace (word.add z 1) with (U64 (z + 1)); last first.
    { apply word.unsigned_inj.
      word. }
    iSpecialize ("IH" $! (z+1) with "[] []").
    { iPureIntro; lia. }
    { iPureIntro; lia. }
    wp_apply ("IH" with "Hs HΦ Hiz1").
  - assert (z = int.val s.(Slice.sz)) by lia; subst z.
    iApply "HΦ"; iFrame.
    replace (U64 (int.val s.(Slice.sz))) with s.(Slice.sz); auto.
    unfold U64.
    rewrite word.of_Z_unsigned; auto.
Qed.

Lemma u64_nat_0 (n: u64) : 0%nat = int.nat n -> n = U64 0.
Proof.
  intros.
  apply (f_equal Z.of_nat) in H.
  rewrite u64_Z_through_nat in H.
  apply word.unsigned_inj.
  rewrite <- H.
  reflexivity.
Qed.

Lemma wp_MemCpy_rec s E t dst vs1 src vs2 (n: u64) :
  {{{ dst ↦∗[t] vs1 ∗ src ↦∗[t] vs2 ∗
            ⌜ length vs1 = int.nat n /\ length vs2 >= length vs1 ⌝ }}}
    MemCpy_rec t #dst #src #n @ s; E
  {{{ RET #(); dst ↦∗[t] (take (int.nat n) vs2) ∗ src ↦∗[t] vs2 }}}.
Proof.
  iIntros (Φ) "(Hdst&Hsrc&Hbounds) HΦ".
  iDestruct "Hbounds" as %(Hvs1&Hvs2).
  (iLöb as "IH" forall (vs1 vs2 n dst src Hvs1 Hvs2) "Hdst Hsrc HΦ").
  wp_call.
  wp_if_destruct.
  - change (int.nat 0) with 0%nat.
    iEval (rewrite firstn_O array_nil) in "HΦ" .
    iApply "HΦ"; iFrame.
  - apply u64_val_ne in Heqb.
    change (int.val 0) with 0 in *.
    destruct vs1, vs2; simpl in Hvs1, Hvs2; try word.
    iDestruct (array_cons with "Hdst") as "[Hdst Hvs1]".
    iDestruct (array_cons with "Hsrc") as "[Hsrc Hvs2]".
    wp_apply (wp_LoadAt with "Hsrc"); iIntros "Hsrc".
    wp_bind (store_ty _ _ _).
    iDestruct (struct_mapsto_ty with "Hsrc") as %Hv0ty.
    wp_apply (wp_StoreAt with "Hdst"); [ done | iIntros "Hdst" ].
    wp_pures.
    rewrite Z.mul_1_r.
    wp_apply ("IH" $! vs1 vs2 with "[] [] [Hvs1] [Hvs2]");
      iFrame;
      try iPureIntro.
    + word.
    + word.
    + iIntros "(Hdst'&Hsrc')".
      iApply "HΦ".
      rewrite array_cons; iFrame.
      replace (take (int.nat n) (v0 :: vs2)) with
          (v0 :: take (int.nat n - 1) vs2).
      { replace (int.nat n - 1)%nat with (int.nat (word.sub n 1)) by word.
        rewrite array_cons; iFrame. }
      replace (int.nat n) with (1 + (int.nat n - 1))%nat at 2 by lia.
      auto.
Qed.

Transparent SliceAppend.

Lemma replicate_singleton {A} (x:A) :
  replicate 1 x = [x].
Proof. reflexivity. Qed.

Lemma wp_SliceAppend stk E s t vs x :
  {{{ is_slice s t vs ∗ ⌜int.val s.(Slice.sz) + 1 < 2^64⌝ ∗ ⌜val_ty x t⌝ }}}
    SliceAppend t s x @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t (vs ++ [x]) }}}.
Proof.
  iIntros (Φ) "(Hs&%) HΦ".
  destruct H as [Hbound Hty].
  wp_lam; repeat wp_step.
  repeat wp_step.
  iDestruct "Hs" as "((Hptr&%)&(%&Hfree))".
  wp_call.
  wp_call.
  wp_call.
  wp_if_destruct.
  - wp_call.
    rewrite word.unsigned_sub in Heqb.
    rewrite -> wrap_small in Heqb by word.
    iDestruct (array_replicate_split 1%nat (Z.to_nat (slice_extra s) - 1)%nat with "Hfree") as "[Hnew Hfree]".
    { word. }
    rewrite array_singleton.
    wp_call.
    wp_pures.
    wp_apply (wp_StoreAt with "Hnew"); [ auto | iIntros "Hnew" ].
    wp_pures.
    wp_call.
    rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice /=.
    iDestruct (array_app _ _ vs [x] with "[$Hptr Hnew]") as "Hptr".
    { rewrite array_singleton.
      iExactEq "Hnew"; f_equal.
      f_equal.
      f_equal.
      word. }
    iFrame.
    iSplitR.
    { rewrite app_length /=.
      iPureIntro.
      word. }
    iSplitR; first by iPureIntro; word.
    rewrite loc_add_assoc.
    iExactEq "Hfree"; repeat (f_equal; try word).

  - wp_apply wp_make_cap.
    iIntros (cap Hcapgt).
    rewrite word.unsigned_add in Hcapgt.
    rewrite -> wrap_small in Hcapgt by word.
    wp_apply (wp_allocN _ _ _ t); auto.
    { word. }
    iIntros (l) "Halloc".
    iDestruct (array_replicate_split (int.nat s.(Slice.sz) + 1) (int.nat cap - int.nat s.(Slice.sz) - 1) with "Halloc") as "[Halloc HnewFree]";
      first by word.
    iDestruct (array_replicate_split (int.nat s.(Slice.sz)) 1%nat with "Halloc") as "[Halloc_sz Halloc1]";
      first by word.
    rewrite array_singleton.
    wp_pures.
    wp_call.
    wp_call.
    wp_apply (wp_MemCpy_rec with "[$Halloc_sz $Hptr]").
    { iPureIntro.
      rewrite replicate_length.
      word. }
    iIntros "[Hvs Hsrc]".
    rewrite firstn_all2; last lia.

    wp_pures.
    wp_call.
    wp_apply (wp_StoreAt with "[Halloc1]"); [ auto | | iIntros "Hlast" ].
    { iExactEq "Halloc1"; word_eq. }
    wp_pures.

    rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice /is_slice_small /=.
    iSplitL "Hvs Hlast".
    + iSplitL.
      * rewrite array_app array_singleton.
        iFrame.
        iExactEq "Hlast"; word_eq.
      * iPureIntro.
        rewrite app_length /=.
        word.
    + iSplitR.
      { iPureIntro; word. }
      iExactEq "HnewFree"; word_eq.
Qed.

Lemma wp_SliceSet stk E s t vs (i: u64) (x: val) :
  {{{ is_slice s t vs ∗ ⌜ is_Some (vs !! int.nat i) ⌝ ∗ ⌜val_ty x t⌝ }}}
    SliceSet t s #i x @ stk; E
  {{{ RET #(); is_slice s t (<[int.nat i:=x]> vs) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  destruct H as [Hlookup Hty].
  destruct s as [ptr sz].
  wp_call.
  wp_call.
  iDestruct "Hs" as "( (Hptr&%) & (%&Hfree))".
  simpl in H, H0 |- *.
  replace (int.val i) with (Z.of_nat (int.nat i)) by word.
  wp_apply (wp_store_offset with "Hptr"); [ | done | iIntros "Hptr" ]; auto.
  iApply "HΦ".
  rewrite /is_slice /=.
  iFrame.
  iSplitL.
  { iSplitL.
    - iExactEq "Hptr"; word_eq.
    - iPureIntro; simpl.
      rewrite insert_length; auto.
  }
  iPureIntro.
  word.
Qed.

End heap.

Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
      eexists; split;
        [pm_reflexivity || fail "wp_alloc:" H "not fresh"
        |iDestructHyp Htmp as H; wp_finish] in
  wp_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc].
     If that fails, it tries to use the lemma [tac_wp_allocN] for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [val_ty
        |iSolveTC
        |finish ()]
    in process_single ()
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".

Ltac iFramePtsTo_core t :=
  match goal with
  | [ |- envs_entails ?Δ ((?l +ₗ ?z) ↦∗[_] ?v) ] =>
    match Δ with
    | context[Esnoc _ ?j ((l +ₗ ?z') ↦∗[_] ?v')] =>
      unify v v';
      replace z with z';
      [ iExact j | t ]
    end
  | [ |- envs_entails ?Δ (?l ↦ ?v) ] =>
    match Δ with
    | context[Esnoc _ ?j (l ↦ ?v')] =>
      replace v with v';
      [ iExact j | t ]
    end
  end.

Tactic Notation "iFramePtsTo" := iFramePtsTo_core ltac:(idtac).
Tactic Notation "iFramePtsTo" "by" tactic(t) := iFramePtsTo_core ltac:(by t).
