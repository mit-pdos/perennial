From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.go_lang Require Export
     lang notation array typing
     tactics lifting proofmode.
From Perennial.go_lang Require Import slice encoding.
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

Lemma tac_wp_allocN Δ Δ' s E j K v (n: u64) Φ :
  (0 < int.val n)%Z →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (array l (replicate (int.nat n) v))) Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ? ? HΔ.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_allocN.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦∗ _)%I) right_id wand_elim_r.
Qed.
Lemma tac_twp_allocN Δ s E j K v (n: u64) Φ :
  (0 < int.val n)%Z →
  (∀ l, ∃ Δ',
    envs_app false (Esnoc Enil j (array l (replicate (int.nat n) v))) Δ
    = Some Δ' ∧
    envs_entails Δ' (WP fill K (Val $ LitV $ LitLoc l) @ s; E [{ Φ }])) →
  envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ? HΔ.
  rewrite -twp_bind. eapply wand_apply; first exact: twp_allocN.
  rewrite left_id. apply forall_intro=> l.
  destruct (HΔ l) as (Δ'&?&HΔ'). rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦∗ _)%I) right_id wand_elim_r.
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
Lemma twp_store s E l v v' :
  [[{ l ↦ Free v' }]] Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  [[{ RET LitV LitUnit; l ↦ Free v }]].
Proof.
  iIntros (Φ) "Hl HΦ". unfold Store.
  wp_lam. wp_let. wp_bind (PrepareWrite _).
  iApply (twp_prepare_write with "Hl").
  iIntros "Hl".
  wp_seq. by iApply (twp_finish_store with "Hl").
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
Lemma tac_twp_store Δ Δ' s E i K l v v' Φ :
  envs_lookup i Δ = Some (false, l ↦ Free v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ Free v')) Δ = Some Δ' →
  envs_entails Δ' (WP fill K (Val $ LitV LitUnit) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (Store (LitV l) v') @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq. intros. rewrite -twp_bind.
  eapply wand_apply; first by eapply twp_store.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

Lemma wp_store_offset s E l off vs v :
  is_Some (vs !! off) →
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.
Proof.
  iIntros ([w Hlookup] Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_store with "Hl1"). iNext. iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply wp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.

Coercion slice_val (s: Slice.t) : val := (#s.(Slice.ptr), #s.(Slice.sz)).

Definition is_slice (s: Slice.t) (vs: list val): iProp Σ :=
  s.(Slice.ptr) ↦∗ vs ∗ ⌜length vs = int.nat s.(Slice.sz)⌝.

Lemma is_slice_intro l (sz: u64) vs :
  l ↦∗ vs -∗ ⌜length vs = int.nat sz⌝ -∗
  is_slice (Slice.mk l sz) vs.
Proof.
  iIntros "H1 H2"; rewrite /is_slice; iFrame.
Qed.

Definition slice_val_fold (ptr: loc) (sz: u64) :
  (#ptr, #sz)%V = slice_val (Slice.mk ptr sz) := eq_refl.

(* TODO: order commands so primitives are opaque only after proofs *)
Transparent raw_slice.

Lemma wp_raw_slice s E l vs (sz: u64) t :
  {{{ array l vs ∗ ⌜length vs = int.nat sz⌝ }}}
    raw_slice t #l #sz @ s; E
  {{{ sl, RET slice_val sl; is_slice sl vs }}}.
Proof.
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

Lemma wp_new_slice s E t (sz: u64) :
  {{{ ⌜ 0 < int.val sz ⌝ }}}
    NewSlice t #sz @ s; E
  {{{ sl, RET slice_val sl; is_slice sl (replicate (int.nat sz) (zero_val t)) }}}.
Proof.
  iIntros (Φ) "% HΦ".
  repeat wp_step.
  wp_lam; repeat wp_step.
  wp_apply wp_allocN; eauto.
  iIntros (l) "[Hl _Hmeta]".
  repeat wp_step.
  rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice.
  iFrame.
  iPureIntro.
  rewrite replicate_length //.
Qed.

Lemma array_split (n:Z) l vs :
  0 <= n ->
  Z.to_nat n <= length vs ->
  array l vs ⊣⊢
        array l (take (Z.to_nat n) vs) ∗ array (l +ₗ n) (drop (Z.to_nat n) vs).
Proof.
  intros Hn Hlength.
  rewrite <- (take_drop (Z.to_nat n) vs) at 1.
  rewrite array_app.
  rewrite take_length.
  rewrite Nat.min_l; last lia.
  rewrite Z2Nat.id; last lia.
  auto.
Qed.

Definition slice_take (sl: Slice.t) (n: u64) : Slice.t :=
  {| Slice.ptr := sl.(Slice.ptr);
     Slice.sz := n |}.

Definition slice_skip (sl: Slice.t) (n: u64) : Slice.t :=
  {| Slice.ptr := sl.(Slice.ptr) +ₗ int.val n;
     Slice.sz := word.sub sl.(Slice.sz) n |}.

Lemma slice_split sl (n: u64) vs :
  0 <= int.val n ->
  int.nat n <= length vs ->
  is_slice sl vs -∗ is_slice (slice_take sl n) (take (int.nat n) vs) ∗
           is_slice (slice_skip sl n) (drop (int.nat n) vs).
Proof.
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

Lemma slice_combine sl (n: u64) vs :
  0 <= int.val n ->
  int.nat n <= length vs ->
  int.val n <= int.val sl.(Slice.sz) ->
  is_slice (slice_take sl n) (take (int.nat n) vs) ∗
           is_slice (slice_skip sl n) (drop (int.nat n) vs) -∗
           is_slice sl vs.
Proof.
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

Lemma wp_SliceSkip stk E s vs (n: u64) :
  {{{ is_slice s vs ∗ ⌜int.val n <= Z.of_nat (length vs)⌝ }}}
    SliceSkip s #n @ stk; E
  {{{ RET slice_val (slice_skip s n);
      is_slice (slice_skip s n) (drop (int.nat n) vs) ∗
               array s.(Slice.ptr) (take (int.nat n) vs) }}}.
Proof.
  iIntros (Φ) "[[Hs %] %] HΦ".
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

Lemma wp_SliceGet s E sl vs (i: u64) v0 :
  {{{ is_slice sl vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet sl #i @ s; E
  {{{ RET v0; is_slice sl vs }}}.
Proof.
  iIntros (Φ) "[Hsl %] HΦ".
  destruct sl as [ptr sz].
  repeat wp_step.
  iDestruct "Hsl" as "[Hsl %]".
  cbv [Slice.ptr Slice.sz] in *.
  repeat (wp_lam || wp_step).
  iDestruct (update_array ptr _ _ _ H with "Hsl") as "[Hi Hsl']".
  pose proof (word.unsigned_range i).
  nat2Z.
  wp_load.
  iApply "HΦ".
  rewrite /is_slice /=.
  iSplitR "".
  { iDestruct ("Hsl'" with "Hi") as "Hsl".
    erewrite list_insert_id by eauto; auto. }
  iPureIntro.
  word.
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

Lemma is_slice_sz s vs :
  is_slice s vs -∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  iIntros "[_ %]".
  auto.
Qed.

Theorem wp_forSlice (I: u64 -> iProp Σ) stk E s vs (body: val) :
  (∀ (i: u64) (x: val),
      {{{ I i ∗ ⌜int.val i < int.val s.(Slice.sz)⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ }}}
        body #i x @ stk; E
      {{{ RET #(); I (word.add i (U64 1)) }}}) -∗
    {{{ I (U64 0) ∗ is_slice s vs }}}
      forSlice body (slice_val s) @ stk; E
    {{{ RET #(); I s.(Slice.sz) ∗ is_slice s vs }}}.
Proof.
  iIntros "#Hind".
  iIntros (Φ) "!> [Hi0 Hs] HΦ".
  wp_call.
  wp_apply wp_slice_len.
  wp_steps.
  assert (1-1 <= 0 <= int.val s.(Slice.sz)) by word.
  iDestruct (is_slice_sz with "Hs") as %Hslen.
  generalize dependent 0.
  change (1-1) with 0.
  intros z Hzrange.
  pose proof (word.unsigned_range s.(Slice.sz)).
  assert (int.val (U64 z) = z) by (rewrite /U64; word).
  iRename "Hi0" into "Hiz".
  (iLöb as "IH" forall (z Hzrange H0) "Hiz").
  wp_if_destruct; rewrite word.unsigned_ltu in Heqb.
  - apply Z.ltb_lt in Heqb.
    destruct (list_lookup_Z_lt vs z) as [xz Hlookup]; first word.
    wp_apply (wp_SliceGet with "[$Hs]").
    { replace (int.val z); eauto. }
    iIntros "Hs".
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
  - apply Z.ltb_ge in Heqb.
    assert (z = int.val s.(Slice.sz)) by lia; subst z.
    iApply "HΦ"; iFrame.
    replace (U64 (int.val s.(Slice.sz))) with s.(Slice.sz); auto.
    unfold U64.
    rewrite word.of_Z_unsigned; auto.
Qed.

Lemma wp_MemCpy s E v dst vs1 src vs2 (n: u64) :
  {{{ array dst vs1 ∗ array src vs2 ∗
            ⌜ length vs1 = int.nat n /\ length vs2 >= length vs1 ⌝ }}}
    MemCpy #dst #src #n @ s; E
  {{{ RET #(); array dst (take (int.nat n) vs2) ∗ array src vs2 }}}.
Proof.
  iIntros (Φ) "(Hvs1&Hvs2&%) HΦ".
  wp_lam.
  wp_let.
  wp_let.
  wp_pures.
  iRevert (vs1 vs2 H) "Hvs1 Hvs2 HΦ".
  iLöb as "IH".
  iIntros (vs1 vs2) "(%&%) Hdst Hsrc HΦ".
  wp_pures.
  destruct_with_eqn (word.ltu (U64 0) n); wp_if.
  - wp_pures.
    destruct vs2.
    { admit. }
    destruct vs1.
    { admit. }
    change (int.val 0) with 0.
    rewrite loc_add_0.
    iDestruct (array_cons with "Hsrc") as "[Hsrc Hvs2]".
    wp_load.
    wp_pures.
    rewrite loc_add_0.
    iDestruct (array_cons with "Hdst") as "[Hdst Hvs1]".
    wp_bind (Store _ _).
    iApply (wp_store with "Hdst").
    iIntros "!> Hdst".
    wp_seq.
    wp_pures.
    change (word.add (U64 0) (U64 1)) with (U64 1).
Admitted.

Lemma u64_nat_0 (n: u64) : 0%nat = int.nat n -> n = U64 0.
Proof.
  intros.
  apply (f_equal Z.of_nat) in H.
  rewrite u64_Z_through_nat in H.
  apply word.unsigned_inj.
  rewrite <- H.
  reflexivity.
Qed.

Lemma wp_MemCpy_rec s E dst vs1 src vs2 (n: u64) :
  {{{ array dst vs1 ∗ array src vs2 ∗
            ⌜ length vs1 = int.nat n /\ length vs2 >= length vs1 ⌝ }}}
    MemCpy_rec #dst #src #n @ s; E
  {{{ RET #(); array dst (take (int.nat n) vs2) ∗ array src vs2 }}}.
Proof.
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
    wp_load.
    wp_bind (Store _ _).
    iApply (wp_store with "Hdst").
    iIntros "!> Hdst".
    wp_seq.
    wp_pures.
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

Lemma wp_SliceAppend stk E s vs x :
  {{{ is_slice s vs ∗ ⌜int.val s.(Slice.sz) + 1 < 2^64⌝ }}}
    SliceAppend s x @ stk; E
  {{{ s', RET slice_val s'; is_slice s' (vs ++ [x]) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  wp_lam; repeat wp_step.
  repeat wp_step.
  iDestruct "Hs" as "[Hptr %]".
  wp_bind (AllocN _ _).
  wp_lam; repeat wp_step.
  iApply wp_allocN; auto.
  { word. }
  iIntros "!>".
  iIntros (l) "[Halloc Hmeta]".
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
      wp_bind (Store _ _).
      wp_apply (wp_store with "Halloc1").
      iIntros "Hlast".
      repeat wp_step.
      wp_lam; repeat wp_step.

      rewrite slice_val_fold. iApply "HΦ". rewrite /is_slice /=.
      iSplitL "Hvs Hlast".
      - rewrite array_app.
        iFrame.
        rewrite H0.
        rewrite array_singleton.
        rewrite Z2Nat.id; last word.
        iFrame.
      - iPureIntro.
        rewrite app_length /=.
        word.
    }
    word.
Qed.

Lemma wp_SliceSet stk E s vs (i: u64) (x: val) :
  {{{ is_slice s vs ∗ ⌜ is_Some (vs !! int.nat i) ⌝ }}}
    SliceSet s #i x @ stk; E
  {{{ RET #(); is_slice s (<[int.nat i:=x]> vs) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  destruct s as [ptr sz].
  wp_lam.
  wp_let.
  wp_let.
  wp_lam.
  iDestruct "Hs" as "[Hptr %]".
  cbv [Slice.ptr Slice.sz] in *.
  wp_pures.
  replace (int.val i) with (Z.of_nat (int.nat i)).
  - iApply (wp_store_offset with "Hptr"); auto.
    iIntros "!> Hptr".
    iApply "HΦ".
    rewrite u64_Z_through_nat.
    iFrame.
    iPureIntro.
    rewrite insert_length; auto.
  - rewrite Z2Nat.id; auto.
    word.
Qed.

Lemma word_sru_0 width (word: Interface.word width) (ok: word.ok word)
      (x: word) s : int.val s = 0 -> word.sru x s = x.
Proof.
  intros.
  apply word.unsigned_inj.
  rewrite word.unsigned_sru.
  - rewrite H.
    rewrite Z.shiftr_0_r.
    unfold word.wrap.
    rewrite word.wrap_unsigned.
    auto.
  - rewrite H.
    apply word.width_pos.
Qed.

Theorem word_wrap_wrap `{word1: Interface.word width1} `{word2: Interface.word width2}
        {ok1: word.ok word1}
        {ok2: word.ok word2} z :
  width1 <= width2 ->
  word.wrap (word:=word1) (word.wrap (word:=word2) z) = word.wrap (word:=word1) z.
Proof.
  unfold word.wrap; intros.
  pose proof (@word.width_pos width1 _ _).
  pose proof (@word.width_pos width2 _ _).
  pose proof (Z.pow_pos_nonneg 2 width1 ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 width2 ltac:(lia) ltac:(lia)).
  rewrite <- Znumtheory.Zmod_div_mod; try lia.
  exists (2 ^ (width2 - width1)).
  rewrite <- Z.pow_add_r; try lia.
  f_equal.
  lia.
Qed.

Theorem word_wrap_wrap' `{word1: Interface.word width1} `{word2: Interface.word width2}
        {ok1: word.ok word1}
        {ok2: word.ok word2} z :
  width2 <= width1 ->
  word.wrap (word:=word1) (word.wrap (word:=word2) z) = word.wrap (word:=word2) z.
Proof.
  unfold word.wrap; intros.
  pose proof (@word.width_pos width1 _ _).
  pose proof (@word.width_pos width2 _ _).
  pose proof (Z.pow_pos_nonneg 2 width1 ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 width2 ltac:(lia) ltac:(lia)).
Admitted.

Hint Rewrite word.unsigned_of_Z : word.
Hint Rewrite word.unsigned_sru : word.

Theorem u32_le_to_sru (x: u32) :
  (λ (b:byte), #b) <$> u32_le x =
  cons #(u8_from_u32 (word.sru x (U32 (0%nat * 8))))
       (cons #(u8_from_u32 (word.sru x (U32 (1%nat * 8))))
             (cons #(u8_from_u32 (word.sru x (U32 (2%nat * 8))))
                   (cons #(u8_from_u32 (word.sru x (U32 (3%nat * 8))))
                         nil))).
Proof.
  change (0%nat * 8) with 0.
  change (1%nat * 8) with 8.
  change (2%nat * 8) with 16.
  change (3%nat * 8) with 24.
  cbv [u32_le fmap list_fmap LittleEndian.split HList.tuple.to_list List.map].
  repeat f_equal.
  - apply word.unsigned_inj.
    unfold u8_from_u32, U8.
    autorewrite with word.
    rewrite word.unsigned_sru;
      change (int.val (U32 0)) with 0;
      last lia.
    rewrite Z.shiftr_0_r.
    rewrite word_wrap_wrap; last lia.
    reflexivity.
  - apply word.unsigned_inj.
    unfold u8_from_u32, U8.
    autorewrite with word.
    rewrite word.unsigned_sru;
      change (int.val (U32 8)) with 8;
      last lia.
    rewrite word_wrap_wrap; last lia.
    reflexivity.
  - apply word.unsigned_inj.
    unfold u8_from_u32, U8.
    autorewrite with word.
    rewrite word.unsigned_sru;
      change (int.val (U32 16)) with 16;
      last lia.
    rewrite word_wrap_wrap; last lia.
    reflexivity.
  - apply word.unsigned_inj.
    unfold u8_from_u32, U8.
    autorewrite with word.
    rewrite word.unsigned_sru;
      change (int.val (U32 24)) with 24;
      last lia.
    rewrite word_wrap_wrap; last lia.
    reflexivity.
Qed.

Theorem wp_EncodeUInt32 (l: loc) (x: u32) vs s E :
  {{{ ▷ l ↦∗ vs ∗ ⌜ length vs = u32_bytes ⌝ }}}
    EncodeUInt32 #x #l @ s ; E
  {{{ RET #(); l ↦∗ ((λ (b: byte), #b) <$> u32_le x) }}}.
Proof.
  iIntros (Φ) "(>Hl & %) HΦ".
  unfold EncodeUInt32.
  wp_lam.
  wp_let.
  wp_pures.
  wp_bind (Store _ _).
  change (int.val 0) with (Z.of_nat 0).
  iApply (wp_store_offset with "Hl").
  { apply lookup_lt_is_Some_2; lia. }

  iIntros "!> Hl".
  wp_seq.
  wp_pures.
  wp_bind (Store _ _).
  change (int.val 1) with (Z.of_nat 1).
  iApply (wp_store_offset with "Hl").
  { apply lookup_lt_is_Some_2.
    rewrite ?insert_length; lia. }

  iIntros "!> Hl".
  wp_seq.
  wp_pures.
  wp_bind (Store _ _).
  change (int.val 2) with (Z.of_nat 2).
  iApply (wp_store_offset with "Hl").
  { apply lookup_lt_is_Some_2.
    rewrite ?insert_length; lia. }

  iIntros "!> Hl".
  wp_seq.
  wp_pures.
  change (int.val 3) with (Z.of_nat 3).
  iApply (wp_store_offset with "Hl").
  { apply lookup_lt_is_Some_2.
    rewrite ?insert_length; lia. }

  iIntros "!> Hl".
  iApply "HΦ".
  rewrite u32_le_to_sru.
  do 5 (destruct vs; try (simpl in H; lia)).
  simpl.
  iApply "Hl".
Qed.

Definition u64_le_bytes (x: u64) : list val :=
  (λ (b: byte), #b) <$> u64_le x.

Lemma u64_le_bytes_length x : length (u64_le_bytes x) = u64_bytes.
Proof.
  rewrite fmap_length //.
Qed.

Theorem wp_EncodeUInt64 (l: loc) (x: u64) vs stk E :
  {{{ ▷ l ↦∗ vs ∗ ⌜ length vs = u64_bytes ⌝ }}}
    EncodeUInt64 #x #l @ stk ; E
  {{{ RET #(); l ↦∗ ((λ (b: byte), #b) <$> u64_le x) }}}.
Proof.
Admitted.

Theorem is_slice_elim s vs :
  is_slice s vs -∗ array s.(Slice.ptr) vs ∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  rewrite /is_slice.
  auto.
Qed.

Theorem wp_UInt64Put stk E s x vs :
  {{{ is_slice s vs ∗ ⌜length vs >= u64_bytes⌝ }}}
    UInt64Put (slice_val s) #x @ stk; E
  {{{ RET #(); is_slice s (u64_le_bytes x ++ (drop u64_bytes vs)) }}}.
Proof.
  iIntros (Φ) "[Hsl %] HΦ".
  wp_lam.
  wp_let.
  wp_lam.
  wp_pures.
  iDestruct (is_slice_elim with "Hsl") as "[Hptr %]".
  iDestruct (array_split 8 with "Hptr") as "[Henc Hrest]"; [ lia .. | ].
  wp_apply (wp_EncodeUInt64 with "[$Henc]").
  { iPureIntro.
    rewrite take_length; lia. }
  iIntros "Henc".
  change (Z.to_nat 8) with 8%nat.
  iDestruct (array_app with "[$Henc $Hrest]") as "Htogether".
  iApply "HΦ".
  iFrame.
  rewrite app_length drop_length u64_le_bytes_length.
  iPureIntro.
  lia.
Qed.

Eval cbv [le_to_u32 map LittleEndian.combine length Datatypes.HList.tuple.of_list PrimitivePair.pair._1 PrimitivePair.pair._2]
  in (fun (v1 v2 v3 v4:u8) => le_to_u32 [v1;v2;v3;v4]).

Hint Rewrite word.unsigned_or_nowrap : word.
Hint Rewrite word.unsigned_slu : word.

Theorem val_u32 z :
  0 <= z < 2 ^ 32 ->
  int.val (U32 z) = z.
Proof.
  intros.
  unfold U32.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
Qed.

Ltac eval_term t :=
  let t' := (eval cbv in t) in change t with t'.

Ltac eval_u32 :=
  match goal with
  | |- context[int.val (U32 ?z)] =>
    rewrite  (val_u32 z ltac:(lia))
  end.

Theorem u8_to_from_u32 x :
  int.val (u8_to_u32 (u8_from_u32 x)) =
  int.val x `mod` 2 ^ 8.
Proof.
  unfold u8_to_u32, u8_from_u32, U8, U32.
  autorewrite with word.
  rewrite word.unsigned_of_Z.
  rewrite word_wrap_wrap'; last lia.
  reflexivity.
Qed.

Lemma val_u8_to_u32 x :
  int.val (u8_to_u32 x) = int.val x.
Proof.
  unfold u8_to_u32, U32.
  rewrite word.unsigned_of_Z.
  pose proof (word.unsigned_range x).
  rewrite wrap_small; lia.
Qed.

Theorem decode_encode x :
  word.or (u8_to_u32 (word.of_Z (int.val x)))
          (word.slu
             (word.or (u8_to_u32 (word.of_Z (int.val x ≫ 8)))
                      (word.slu
                         (word.or (u8_to_u32 (word.of_Z ((int.val x ≫ 8) ≫ 8)))
                                  (word.slu (u8_to_u32 (word.of_Z (((int.val x ≫ 8) ≫ 8) ≫ 8))) (U32 8)))
                         (U32 8))) (U32 8)) = x.
Proof.
  apply word.unsigned_inj.
  pose proof (u32_le_to_word x).
  cbv [le_to_u32 u32_le map LittleEndian.combine LittleEndian.split length Datatypes.HList.tuple.to_list Datatypes.HList.tuple.of_list PrimitivePair.pair._1 PrimitivePair.pair._2] in H.
  rewrite Z.shiftl_0_l in H.
  rewrite Z.lor_0_r in H.
  rewrite ?word.unsigned_of_Z in H.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u32; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u32; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u32; try lia.
  rewrite ?val_u8_to_u32.
  rewrite <- H at 5.
  rewrite ?word.unsigned_of_Z.
Admitted.

Theorem wp_DecodeUInt32 (l: loc) (x: u32) vs s E :
  {{{ ▷ l ↦∗ ((λ (b: byte), #b) <$> u32_le x) }}}
    DecodeUInt32 #l @ s ; E
  {{{ RET #x; l ↦∗ ((λ (b: byte), #b) <$> u32_le x) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  cbv [u32_le fmap list_fmap LittleEndian.split HList.tuple.to_list List.map].
  rewrite ?array_cons ?loc_add_assoc.
  iDestruct "Hl" as "(Hl0&Hl1&Hl2&Hl3&Hemp)".
  rewrite /DecodeUInt32.
  do 4 (wp_load; wp_steps).
  iSpecialize ("HΦ" with "[$]").
  rewrite decode_encode.
  iApply "HΦ".
Qed.

Theorem wp_DecodeUInt64 (l: loc) (x: u64) s E :
  {{{ ▷ l ↦∗ ((λ (b: byte), #b) <$> u64_le x) }}}
    DecodeUInt64 #l @ s ; E
  {{{ RET #x; l ↦∗ ((λ (b: byte), #b) <$> u64_le x) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  cbv [u64_le fmap list_fmap LittleEndian.split HList.tuple.to_list List.map].
  rewrite ?array_cons ?loc_add_assoc.
  iDestruct "Hl" as "(Hl0&Hl1&Hl2&Hl3&Hl4&Hl5&Hl6&Hl7&Hemp)".
  rewrite /DecodeUInt64.
  do 8 (wp_load; wp_steps).
  iSpecialize ("HΦ" with "[$]").
Admitted.

Theorem wp_UInt64Get stk E s (x: u64) vs :
  {{{ is_slice s vs ∗ ⌜take 8 vs = u64_le_bytes x⌝ }}}
    UInt64Get (slice_val s) @ stk; E
  {{{ RET #x; is_slice s (u64_le_bytes x ++ drop 8 vs) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  assert (vs = u64_le_bytes x ++ drop 8 vs).
  { rewrite -{1}(take_drop 8 vs).
    congruence. }
  rewrite [vs in is_slice _ vs](H0).
  wp_call.
  wp_apply wp_slice_ptr.
  iDestruct "Hs" as "[Hptr %]".
  iDestruct (array_app with "Hptr") as "[Htake Hrest]"; try lia;
    rewrite u64_le_bytes_length.
  wp_apply (wp_DecodeUInt64 with "[$Htake]").
  iIntros "Htake".
  iDestruct (array_app with "[$Htake Hrest]") as "Hptr".
  { rewrite fmap_length u64_le_length.
    iFrame. }
  iApply "HΦ".
  iFrame.
  iPureIntro.
  rewrite app_length u64_le_bytes_length drop_length in H1 |- *.
  lia.
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
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_store _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [solve_mapsto ()
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
     ie, [tac_wp_alloc] (respectively, [tac_twp_alloc]).
     If that fails, it tries to use the lemma [tac_wp_allocN]
     (respectively, [tac_twp_allocN]) for allocating an array.
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
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_twp_alloc _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        finish ()
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_twp_allocN _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        finish ()
    in (process_single ()) || (process_array ())
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".
