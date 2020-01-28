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
         sz: u64; }.
End Slice.

Section heap.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types off : nat.

(* TODO: this should probably be a val, or it's going to cause problems... *)
Definition AllocN_at (t:ty) (len:expr) (e:expr) := AllocN len e.

Lemma tac_wp_allocN Δ Δ' s E j K v t (n: u64) Φ :
  (0 < int.val n)%Z →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  val_ty v t ->
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (array l t (replicate (int.nat n) v))) Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (AllocN_at t (Val $ LitV $ LitInt n) (Val v)) @ s; E {{ Φ }}).
Proof using Type.
  rewrite envs_entails_eq=> ? ? Hty HΔ.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_allocN.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite right_id wand_elim_r.
Qed.

Theorem val_hasTy_flatten_length Γ v t :
  (Γ ⊢v v : t) ->
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
  pose proof (ty_size_gt0 t).
  lia.
Qed.

Theorem struct_ptsto_pair_split l v1 t1 v2 t2 :
  l ↦[t1 * t2] (v1, v2) ⊣⊢ l ↦[t1] v1 ∗ (l +ₗ ty_size t1) ↦[t2] v2.
Proof.
  rewrite /struct_mapsto /= big_opL_app.
  rewrite /val_ty.
  iSplit.
  - iIntros "[[Hv1 Hv2] %]".
    inversion H; subst; clear H.
    iSplitL "Hv1"; iFrame; eauto.
    iSplitL; eauto.
    erewrite val_hasTy_flatten_length by eauto.
    setoid_rewrite ty_size_offset.
    iFrame.
  - iIntros "[[Hv1 %] [Hv2 %]]".
    erewrite val_hasTy_flatten_length by eauto.
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
  (iInduction H as [ | | | | | | ] "IH" forall (l Φ));
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
    + erewrite val_hasTy_flatten_length; eauto.
      setoid_rewrite ty_size_offset.
      iFrame.
    + iIntros "!> Hv2".
      wp_pures.
      iApply "HΦ"; iFrame.
      erewrite val_hasTy_flatten_length by eauto.
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

Lemma wp_store s E l v v' :
  {{{ ▷ l ↦ Free v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ Free v }}}.
Proof using Type.
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
Proof using Type.
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
  (iInduction H as [ | | | | | | ] "IH" forall (v' Hty l Φ));
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
    erewrite val_hasTy_flatten_length by eauto.
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
    erewrite val_hasTy_flatten_length by eauto.
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
Qed.

Lemma wp_store_offset s E l off vs t v :
  is_Some (vs !! off) →
  val_ty v t ->
  {{{ ▷ l ↦∗[t] vs }}} store_ty t #(l +ₗ[t] off) v @ s; E {{{ RET #(); l ↦∗[t] <[off:=v]> vs }}}.
Proof using Type.
  iIntros ([w Hlookup] Hty Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_StoreAt _ _ _ _ _ _ Hty with "Hl1"). iIntros "!> Hl1".
  iApply "HΦ". iApply ("Hl2" with "Hl1").
Qed.

(*
Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof using Type.
  setoid_rewrite vec_to_list_insert. apply wp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.
*)

Coercion slice_val (s: Slice.t) : val := (#s.(Slice.ptr), #s.(Slice.sz)).

Definition is_slice (s: Slice.t) (t:ty) (vs: list val): iProp Σ :=
  s.(Slice.ptr) ↦∗[t] vs ∗ ⌜length vs = int.nat s.(Slice.sz)⌝.

Lemma is_slice_intro l t (sz: u64) vs :
  l ↦∗[t] vs -∗ ⌜length vs = int.nat sz⌝ -∗
  is_slice (Slice.mk l sz) t vs.
Proof using Type.
  iIntros "H1 H2"; rewrite /is_slice; iFrame.
Qed.

Theorem is_slice_elim s t vs :
  is_slice s t vs -∗ s.(Slice.ptr) ↦∗[t] vs ∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof using Type.
  rewrite /is_slice //.
Qed.

Definition slice_val_fold (ptr: loc) (sz: u64) :
  (#ptr, #sz)%V = slice_val (Slice.mk ptr sz) := eq_refl.

(* TODO: order commands so primitives are opaque only after proofs *)
Transparent raw_slice.

Lemma wp_raw_slice s E l vs (sz: u64) t :
  {{{ array l t vs ∗ ⌜length vs = int.nat sz⌝ }}}
    raw_slice t #l #sz @ s; E
  {{{ sl, RET slice_val sl; is_slice sl t vs }}}.
Proof using Type.
  iIntros (Φ) "Hslice HΦ".
  rewrite /raw_slice.
  wp_steps.
  rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice.
  iFrame.
Qed.

Ltac nat2Z_1 :=
  match goal with
  | _ => lia (* TODO: this only makes sense on Coq master where lia doesn't
    need any of the help below *)
  | |- @eq nat _ _ => apply Nat2Z.inj
  | [ H: @eq nat _ _ |- _ ] => apply Nat2Z.inj_iff in H
  | |- le _ _ => apply Nat2Z.inj_le
  | [ |- context[Z.of_nat (Z.to_nat ?z)] ] =>
    rewrite (Z2Nat.id z); [ | lia ]
  | [ |- context[Z.to_nat (Z.of_nat ?n)] ] =>
    rewrite (Nat2Z.id n)
  | [ H: context[Z.of_nat (Z.to_nat ?z)] |- _ ] =>
    rewrite (Z2Nat.id z) in H; [ | lia ]
  | [ H: context[Z.to_nat (Z.of_nat ?n)] |- _ ] =>
    rewrite (Nat2Z.id n) in H; [ | lia ]
  | [ H: context[Z.of_nat (?n - ?m)%nat] |- _ ] =>
    rewrite (Nat2Z.inj_sub n m) in H; [ | apply Nat2Z.inj_le; lia ]
  | [ H: context[Z.of_nat (?n + ?m)%nat] |- _ ] =>
    rewrite (Nat2Z.inj_add n m) in H; [ | apply Nat2Z.inj_le; lia ]
  | [ H: context[Z.to_nat (?n - ?m)%Z] |- _ ] =>
    rewrite (Nat2Z.inj_sub n m) in H; [ | apply Nat2Z.inj_le ]
  | [ H: context[Z.to_nat (?n + ?m)%Z] |- _ ] =>
    rewrite (Z2Nat.inj_add n m) in H; [ | lia | lia ]
  | [ H: context[Z.to_nat (?n - ?m)%Z] |- _ ] =>
    rewrite (Z2Nat.inj_sub n m) in H; [ | lia ]
  end.

Ltac nat2Z := repeat nat2Z_1.

Lemma wp_slice_len stk E (s: Slice.t) (Φ: val -> iProp Σ) :
    Φ #(s.(Slice.sz)) -∗ WP slice.len (slice_val s) @ stk; E {{ v, Φ v }}.
Proof using Type.
  iIntros "HΦ".
  wp_call.
  iApply "HΦ".
Qed.

Lemma wp_slice_ptr stk E (s: Slice.t) (Φ: val -> iProp Σ) :
    Φ #(s.(Slice.ptr)) -∗ WP slice.ptr (slice_val s) @ stk; E {{ v, Φ v }}.
Proof using Type.
  iIntros "HΦ".
  wp_call.
  iApply "HΦ".
Qed.

Lemma wp_new_slice s E t (sz: u64) :
  {{{ ⌜ 0 < int.val sz ⌝ }}}
    NewSlice t #sz @ s; E
  {{{ sl, RET slice_val sl; is_slice sl t (replicate (int.nat sz) (zero_val t)) }}}.
Proof using Type.
  iIntros (Φ) "% HΦ".
  repeat wp_step.
  wp_lam; repeat wp_step.
  wp_apply (wp_allocN _ _ _ t); eauto.
  { hnf.
    eapply zero_val_ty. }
  iIntros (l) "Hl".
  repeat wp_step.
  rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice.
  iFrame.
  iPureIntro.
  rewrite replicate_length //.
Qed.

Theorem wp_SliceSingleton Φ stk E t x :
  val_ty x t ->
  (∀ s, is_slice s t [x] -∗ Φ (slice_val s)) -∗
  WP SliceSingleton x @ stk; E {{ Φ }}.
Proof using Type.
  iIntros (Hty) "HΦ".
  wp_call.
  wp_apply (wp_allocN _ _ _ t); eauto.
  { word. }
  change (replicate (int.nat 1) x) with [x].
  iIntros (l) "Hl".
  wp_steps.
  rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice.
  iFrame.
  iPureIntro.
  simpl; word.
Qed.

Lemma array_split (n:Z) l t vs :
  0 <= n ->
  Z.to_nat n <= length vs ->
  array l t vs ⊣⊢
        array l t (take (Z.to_nat n) vs) ∗ array (l +ₗ[t] n) t (drop (Z.to_nat n) vs).
Proof using Type.
  intros Hn Hlength.
  rewrite <- (take_drop (Z.to_nat n) vs) at 1.
  rewrite array_app.
  rewrite take_length.
  rewrite Nat.min_l; last lia.
  rewrite Z2Nat.id; last lia.
  auto.
Qed.

Definition slice_take (sl: Slice.t) (t:ty) (n: u64) : Slice.t :=
  {| Slice.ptr := sl.(Slice.ptr);
     Slice.sz := n |}.

Definition slice_skip (sl: Slice.t) (t:ty) (n: u64) : Slice.t :=
  {| Slice.ptr := sl.(Slice.ptr) +ₗ[t] int.val n;
     Slice.sz := word.sub sl.(Slice.sz) n |}.

Lemma slice_split sl (n: u64) t vs :
  0 <= int.val n ->
  int.nat n <= length vs ->
  is_slice sl t vs -∗ is_slice (slice_take sl t n) t (take (int.nat n) vs) ∗
           is_slice (slice_skip sl t n) t (drop (int.nat n) vs).
Proof using Type.
  intros Hpos Hbound.
  rewrite /is_slice /slice_take /slice_skip /=.
  rewrite take_length drop_length.
  rewrite Nat.min_l; last lia.
  word_cleanup.
  rewrite (array_split (int.val n)); try lia.
  iIntros "[(Htake&Hdrop) %]".
  iFrame.
  iPureIntro; intuition auto.
  word.
Qed.

Lemma slice_combine sl (n: u64) t vs :
  0 <= int.val n ->
  int.nat n <= length vs ->
  int.val n <= int.val sl.(Slice.sz) ->
  is_slice (slice_take sl t n) t (take (int.nat n) vs) ∗
           is_slice (slice_skip sl t n) t (drop (int.nat n) vs) -∗
           is_slice sl t vs.
Proof using Type.
  intros Hpos Hbound Hsz_bound.
  rewrite /is_slice /slice_take /slice_skip /=.
  rewrite take_length drop_length.
  iIntros "((Htake&%)&(Hdrop&%))".
  iSplitL.
  { iApply (array_split (int.val n)); try lia; iFrame. }
  iPureIntro.
  word_cleanup.
  rewrite Nat.min_l in H; last lia.
  rewrite word.unsigned_sub in H0.
  rewrite wrap_small in H0; nat2Z.
Qed.

Lemma wp_SliceSkip stk E s t vs (n: u64) :
  {{{ is_slice s t vs ∗ ⌜int.val n <= Z.of_nat (length vs)⌝ }}}
    SliceSkip t s #n @ stk; E
  {{{ RET slice_val (slice_skip s t n);
      is_slice (slice_skip s t n) t (drop (int.nat n) vs) ∗
               array s.(Slice.ptr) t (take (int.nat n) vs) }}}.
Proof using Type.
  iIntros (Φ) "((Hs&%)&%) HΦ".
  wp_lam; repeat wp_step.
  wp_lam; repeat wp_step.
  repeat (wp_lam || wp_step).

  rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice.
  pose proof (word.unsigned_range n).
  pose proof (word.unsigned_range s.(Slice.sz)).
  iDestruct (array_split (int.nat n) with "Hs") as "[Htake Hskip]"; try lia.
  rewrite Z2Nat.id; last lia.
  iFrame.
  iPureIntro.
  rewrite drop_length /=.
  word.
Qed.

Lemma wp_SliceSkip' Φ stk E s t (n: u64):
  ⌜int.val n ≤ int.val s.(Slice.sz)⌝ -∗
  Φ (slice_val (slice_skip s t n)) -∗
  WP (SliceSkip t (slice_val s) #n) @ stk; E {{ Φ }}.
Proof using Type.
  iIntros "% HΦ".
  wp_call.
  wp_call.
  wp_call.
  iApply "HΦ".
Qed.

Lemma wp_SliceTake Φ stk E s t vs (n: u64):
  ⌜int.val n ≤ int.val s.(Slice.sz)⌝ -∗
  Φ (slice_val (slice_take s t n)) -∗
  WP (SliceTake (slice_val s) #n) @ stk; E {{ Φ }}.
Proof using Type.
  iIntros "% HΦ".
  wp_call.
  wp_call.
  wp_if_destruct.
  - exfalso.
    word.
  - wp_call.
    iApply "HΦ".
Qed.

Lemma wp_SliceSubslice Φ stk E s t (n1 n2: u64):
  ⌜int.val n1 ≤ int.val n2 ∧ int.val n2 ≤ int.val s.(Slice.sz)⌝ -∗
  Φ (slice_val (Slice.mk (s.(Slice.ptr) +ₗ[t] int.val n1) (word.sub n2 n1))) -∗
  WP (SliceSubslice t (slice_val s) #n1 #n2) @ stk; E {{ Φ }}.
Proof using Type.
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

Lemma wp_SliceGet s E sl t vs (i: u64) v0 :
  {{{ is_slice sl t vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet t sl #i @ s; E
  {{{ RET v0; is_slice sl t vs ∗ ⌜val_ty v0 t⌝ }}}.
Proof using Type.
  iIntros (Φ) "[Hsl %] HΦ".
  destruct sl as [ptr sz].
  repeat wp_step.
  iDestruct "Hsl" as "[Hsl %]".
  cbv [Slice.ptr Slice.sz] in *.
  repeat (wp_lam || wp_step).
  iDestruct (update_array ptr _ _ _ _ H with "Hsl") as "[Hi Hsl']".
  pose proof (word.unsigned_range i).
  nat2Z.
  iDestruct (struct_mapsto_ty with "Hi") as %Hty.
  iApply (wp_LoadAt with "Hi"); iIntros "!> Hi".
  iApply "HΦ".
  rewrite /is_slice /=.
  iSplitR ""; last by auto.
  iSplitR "".
  { iDestruct ("Hsl'" with "Hi") as "Hsl".
    erewrite list_insert_id by eauto; auto. }
  iPureIntro.
  word.
Qed.

Lemma list_lookup_lt A (l: list A) (i: nat) :
  (i < length l)%nat ->
  exists x, l !! i = Some x.
Proof using Type.
  intros.
  destruct_with_eqn (l !! i); eauto.
  exfalso.
  apply lookup_ge_None in Heqo.
  lia.
Qed.

Lemma list_lookup_Z_lt {A} (l: list A) (i: Z) :
  (0 <= i < Z.of_nat (length l)) ->
  exists x, l !! Z.to_nat i = Some x.
Proof using Type.
  intros.
  apply list_lookup_lt.
  apply Nat2Z.inj_le; lia.
Qed.

Lemma is_slice_sz s t vs :
  is_slice s t vs -∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof using Type.
  iIntros "[_ %] !%//".
Qed.

Theorem wp_forSlice (I: u64 -> iProp Σ) stk E s t vs (body: val) :
  (∀ (i: u64) (x: val),
      {{{ I i ∗ ⌜int.val i < int.val s.(Slice.sz)⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ }}}
        body #i x @ stk; E
      {{{ RET #(); I (word.add i (U64 1)) }}}) -∗
    {{{ I (U64 0) ∗ is_slice s t vs }}}
      forSlice t body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) ∗ is_slice s t vs }}}.
Proof using Type.
  iIntros "#Hind".
  iIntros (Φ) "!> [Hi0 Hs] HΦ".
  wp_call.
  wp_apply wp_slice_len.
  wp_steps.
  remember 0 as z.
  assert (0 <= z <= int.val s.(Slice.sz)) by word.
  iDestruct (is_slice_sz with "Hs") as %Hslen.
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
Proof using Type.
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
Proof using Type.
  iIntros (Φ) "(Hdst&Hsrc&Hbounds) HΦ".
  iDestruct "Hbounds" as %(Hvs1&Hvs2).
  (iLöb as "IH" forall (vs1 vs2 n dst src Hvs1 Hvs2) "Hdst Hsrc HΦ").
  wp_call.
  wp_if_destruct.
  - apply bool_decide_eq_true in Heqb.
    inversion Heqb; subst.
    change (int.nat 0) with 0%nat.
    iEval (rewrite firstn_O array_nil) in "HΦ" .
    iApply "HΦ"; iFrame.
  - apply bool_decide_eq_false in Heqb.
    assert (n ≠ 0).
    { congruence. }
    destruct vs1.
    { apply u64_nat_0 in Hvs1.
      congruence. }
    destruct vs2.
    { assert (n = U64 0); subst; try congruence.
      apply u64_nat_0.
      simpl in *.
      lia. }
    simpl in Hvs1, Hvs2.
    iDestruct (array_cons with "Hdst") as "[Hdst Hvs1]".
    iDestruct (array_cons with "Hsrc") as "[Hsrc Hvs2]".
    (* TODO: add support for typed load to wp_load *)
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

Lemma wp_SliceAppend stk E s t vs x :
  {{{ is_slice s t vs ∗ ⌜int.val s.(Slice.sz) + 1 < 2^64⌝ ∗ ⌜val_ty x t⌝ }}}
    SliceAppend t s x @ stk; E
  {{{ s', RET slice_val s'; is_slice s' t (vs ++ [x]) }}}.
Proof using Type.
  iIntros (Φ) "[Hs %] HΦ".
  destruct H as [Hbound Hty].
  wp_lam; repeat wp_step.
  repeat wp_step.
  iDestruct "Hs" as "[Hptr %]".
  wp_bind (AllocN _ _).
  wp_lam; repeat wp_step.
  iApply wp_allocN; auto.
  { word. }
  { apply zero_val_ty. }
  iIntros "!>".
  iIntros (l) "Halloc".
  repeat wp_step.
  wp_lam; repeat wp_step.
  wp_lam; repeat wp_step.

  iDestruct (array_split (int.val (Slice.sz s)) with "Halloc") as "[Halloc_sz Halloc1]".
  - word.
  - rewrite replicate_length.
    word.
  - rewrite take_replicate drop_replicate.
    rewrite Nat.min_l; last word.
    match goal with
    | |- context[replicate ?x] =>
      match x with
      | (_ - _)%nat => replace x with 1%nat
      end
    end.
    { simpl.
      rewrite array_singleton.
      wp_apply (wp_MemCpy_rec with "[$Halloc_sz $Hptr]").
      { iPureIntro.
        rewrite replicate_length.
        word. }
      iIntros "[Hvs Hsrc]".
      rewrite firstn_all2; last lia.
      wp_seq.
      wp_lam.
      wp_pures.
      wp_bind (store_ty _ _ _).
      wp_apply (wp_StoreAt with "Halloc1"); [ done | iIntros "Hlast" ].
      repeat wp_step.
      wp_lam; repeat wp_step.

      rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice /=.
      iSplitL "Hvs Hlast".
      - rewrite array_app.
        iFrame.
        rewrite H.
        rewrite array_singleton.
        rewrite Z2Nat.id; last word.
        iFrame.
      - iPureIntro.
        rewrite app_length /=.
        word.
    }
    word.
Qed.

Lemma wp_SliceSet stk E s t vs (i: u64) (x: val) :
  {{{ is_slice s t vs ∗ ⌜ is_Some (vs !! int.nat i) ⌝ ∗ ⌜val_ty x t⌝ }}}
    SliceSet t s #i x @ stk; E
  {{{ RET #(); is_slice s t (<[int.nat i:=x]> vs) }}}.
Proof using Type.
  iIntros (Φ) "[Hs %] HΦ".
  destruct H as [Hlookup Hty].
  destruct s as [ptr sz].
  wp_lam.
  wp_let.
  wp_let.
  wp_lam.
  iDestruct "Hs" as "[Hptr %]".
  cbv [Slice.ptr Slice.sz] in *.
  wp_pures.
  replace (int.val i) with (Z.of_nat (int.nat i)).
  - wp_apply (wp_store_offset with "Hptr"); [ | done | iIntros "Hptr" ]; auto.
    iApply "HΦ".
    rewrite u64_Z_through_nat.
    iFrame.
    iPureIntro.
    rewrite insert_length; auto.
  - word.
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
        [iSolveTC
        |finish ()]
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_allocN _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [idtac|iSolveTC
         |finish ()]
    in (process_single ()) || (process_array ())
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".
