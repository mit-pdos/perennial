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

Definition is_slice (v: val) (s: Slice.t) (vs: list val): iProp Σ :=
  ⌜ v = (#s.(Slice.ptr), #s.(Slice.sz))%V ⌝ ∗
  array s.(Slice.ptr) vs ∗ ⌜length vs = int.nat s.(Slice.sz)⌝.

Lemma is_slice_intro l (sz: u64) vs :
  l ↦∗ vs ∗ ⌜length vs = int.nat sz⌝ -∗
  is_slice (#l, #sz) (Slice.mk l sz) vs.
Proof.
  iIntros "H".
  by iSplitR.
Qed.

(* TODO: order commands so primitives are opaque only after proofs *)
Transparent raw_slice.

Lemma wp_raw_slice s E l vs (sz: u64) t :
  {{{ array l vs ∗ ⌜length vs = int.nat sz⌝ }}}
    raw_slice t #l #sz @ s; E
  {{{ sl v, RET v; is_slice v sl vs }}}.
Proof.
  iIntros (Φ) "Hslice HΦ".
  rewrite /raw_slice.
  wp_lam.
  wp_let.
  wp_pures.
  iApply "HΦ".
  by iApply is_slice_intro.
Qed.

Lemma wp_new_slice s E t (sz: u64) :
  {{{ ⌜ 0 < int.val sz ⌝ }}}
    NewSlice t #sz @ s; E
  {{{ sl v, RET v; is_slice v sl (replicate (int.nat sz) (zero_val t)) }}}.
Proof.
  iIntros (Φ) "% HΦ".
  wp_lam.
  wp_bind (AllocN _ _).
  iApply wp_allocN; eauto.
  iIntros (l) "!> [Hl _Hmeta]".
  wp_pures.
  wp_lam.
  wp_pures.
  iApply "HΦ".
  iApply is_slice_intro; iFrame.
  iPureIntro.
  rewrite replicate_length //.
Qed.

(* TODO: this should be bidirectional but I'm not sure how to do that in the
proof mode *)
Lemma array_app_split l vs1 vs2 :
  array l (vs1 ++ vs2) -∗
        array l vs1 ∗ array (l +ₗ (length vs1)) vs2.
Proof.
  revert vs2.
  revert l.
  induction vs1; simpl.
  - iIntros (l vs2) "Hl".
    rewrite loc_add_0.
    rewrite array_nil; iFrame.
  - iIntros (l vs2) "Hl".
    iDestruct (array_cons with "Hl") as "[Hl Hl1]".
    rewrite array_cons.
    iFrame.
    iDestruct (IHvs1 with "Hl1") as "[Hl Hvs2]".
    rewrite loc_add_assoc.
    replace (1 + length vs1) with (Z.of_nat (S (length vs1))); last by lia.
    iFrame.
Qed.

Lemma array_split (n:Z) l vs :
  0 <= n ->
  Z.to_nat n < length vs ->
  array l vs -∗
        array l (take (Z.to_nat n) vs) ∗ array (l +ₗ n) (drop (Z.to_nat n) vs).
Proof.
  iIntros (Hn Hlength) "Hl".
  (* TODO: this is super slow *)
  rewrite <- (take_drop (Z.to_nat n) vs) at 1.
  iDestruct (array_app_split with "Hl") as "[H1 H2]".
  iSplitL "H1"; iFrame.
  rewrite take_length.
  rewrite Nat.min_l; last lia.
  rewrite Z2Nat.id; last lia.
  iFrame.
Qed.

Opaque word.unsigned word.ltu word.sub u64_instance.u64_word.

(* TODO: for now we drop the remainder of the slice on the floor *)
Lemma wp_subslice s E v sl vs (n1 n2: u64) :
  {{{ is_slice v sl vs ∗ ⌜ int.nat n1 ≤ int.nat n2 /\ int.nat n2 < int.nat (Slice.sz sl) ⌝ }}}
    SliceSubslice v #n1 #n2 @ s; E
  {{{ sl' v', RET v'; is_slice v' sl' (take (int.nat n2 - int.nat n1) (drop (int.nat n1) vs)) }}}.
Proof.
  iIntros (Φ) "[Hsl (%&%)] HΦ".
  wp_lam.
  wp_let.
  wp_pures.
  wp_lam.
  iDestruct "Hsl" as "[-> [Hsl %]]".
  wp_lam.
  wp_pures.
  destruct_with_eqn (word.ltu (word:=u64_instance.u64_word)
                              (Slice.sz sl)
                              (word.sub (word:=u64_instance.u64_word) n2 n1));
    wp_if.
  - rewrite word.unsigned_ltu word.unsigned_sub in Heqb.
    admit. (* TODO: need to derive a contradiction *)
  - wp_lam.
    wp_pures.
    iApply "HΦ".
    iApply is_slice_intro; iFrame.
    rewrite take_length drop_length.
    iSplitL.
    + iDestruct (array_split (int.val n1) with "Hsl") as "[Hsl1 Hsl2]".
      * pose proof (Properties.word.unsigned_range n1); lia.
      * unfold int.nat in *; lia.
      * iDestruct (array_split (int.val n1 - int.val n2) with "Hsl2") as "[Hsl2 Hsl3]".
        -- admit.
        -- rewrite drop_length.
           admit.
        -- fold (int.nat n1) (int.nat n2).
          replace (Z.to_nat (int.val n1 - int.val n2))
             with (int.nat n2 - int.nat n1)%nat.
          { iFrame. }
          admit.
    + iPureIntro.
      unfold int.nat.
      rewrite Nat.min_l.
      * admit.
      * admit.
Admitted.

Lemma wp_slice_get s E v sl vs (i: u64) v0 :
  {{{ is_slice v sl vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet v #i @ s; E
  {{{ RET v0; is_slice v sl vs }}}.
Proof.
  iIntros (Φ) "[Hsl %] HΦ".
  destruct sl as [ptr sz].
  wp_lam.
  wp_let.
  iDestruct "Hsl" as "[-> [Hsl %]]".
  cbv [Slice.ptr Slice.sz].
  wp_lam.
  wp_pures.
  iDestruct (update_array ptr _ _ _ H with "Hsl") as "[Hi Hsl']".
  rewrite Z2Nat.id.
  { wp_load.
    iApply "HΦ".
    iApply is_slice_intro.
    iSplitR ""; eauto.
    iDestruct ("Hsl'" with "Hi") as "Hsl".
    erewrite list_insert_id by eauto; auto. }
  pose proof (Properties.word.unsigned_range i); lia.
Qed.

Lemma wp_memcpy s E v dst vs1 src vs2 (n: u64) :
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
  wp_rec.
  wp_pures.
  destruct_with_eqn (word.ltu (word:=u64_instance.u64_word) (U64 0) n); wp_if.
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
    change (word.add (word:=u64_instance.u64_word) (U64 0) (U64 1)) with (U64 1).
Abort.

Lemma u64_nat_0 (n: u64) : 0%nat = int.nat n -> n = U64 0.
Proof.
Admitted.

Lemma wp_memcpy_rec s E v dst vs1 src vs2 (n: u64) :
  {{{ array dst vs1 ∗ array src vs2 ∗
            ⌜ length vs1 = int.nat n /\ length vs2 >= length vs1 ⌝ }}}
    MemCpy_rec #dst #src #n @ s; E
  {{{ RET #(); array dst (take (int.nat n) vs2) ∗ array src vs2 }}}.
Proof.
  iIntros (Φ) "(Hdst&Hsrc&(%&%)) HΦ".
  iRevert (vs1 vs2 n dst src H H0) "Hdst Hsrc HΦ".
  iLöb as "IH".
  iIntros (vs1 vs2 n dst src Hvs1 Hvs2) "Hdst Hsrc HΦ".
  wp_rec.
  wp_let.
  wp_let.
  wp_pures.
  destruct_with_eqn (bool_decide (#n = #0)); wp_if.
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
    + admit.
    + admit.
    + iIntros "(Hdst'&Hsrc')".
      iApply "HΦ".
      rewrite array_cons; iFrame.
      replace (take (int.nat n) (v1 :: vs2)) with
          (v1 :: take (int.nat n - 1) vs2).
      { replace (int.nat n - 1)%nat with (int.nat (word.sub n 1)).
        { rewrite array_cons; iFrame. }
        admit.
      }
      admit.
Admitted.

Lemma wp_slice_set s E v sl vs (i: u64) (x: val) :
  {{{ is_slice v sl vs ∗ ⌜ is_Some (vs !! int.nat i) ⌝ }}}
    SliceSet v #i x @ s; E
  {{{ RET #(); is_slice v sl (<[int.nat i:=x]> vs) }}}.
Proof.
  iIntros (Φ) "[Hsl %] HΦ".
  destruct sl as [ptr sz].
  wp_lam.
  wp_let.
  wp_let.
  wp_lam.
  iDestruct "Hsl" as "[-> [Hptr %]]".
  cbv [Slice.ptr Slice.sz] in *.
  wp_pures.
  replace (int.val i) with (Z.of_nat (int.nat i)).
  - iApply (wp_store_offset with "Hptr"); auto.
    iIntros "!> Hptr".
    iApply "HΦ".
    iApply is_slice_intro; iFrame.
    iPureIntro.
    rewrite insert_length; auto.
  - rewrite Z2Nat.id; auto.
    pose proof (Properties.word.unsigned_range i); lia.
Qed.

Lemma word_sru_0 width (word: Interface.word width) (ok: word.ok word)
      (x: word) s : int.val s = 0 -> word.sru x s = x.
Proof.
  intros.
  apply Properties.word.unsigned_inj.
  rewrite word.unsigned_sru.
  - rewrite H.
    rewrite Z.shiftr_0_r.
    unfold word.wrap.
    rewrite Properties.word.wrap_unsigned.
    auto.
  - rewrite H.
    apply word.width_pos.
Qed.

Canonical Structure u32_instance.u32_word.
Canonical Structure u8_instance.u8_word.

Theorem u32_le_to_sru (x: u32) :
  (λ (b:byte), #b) <$> u32_le x =
  cons #(u8_from_u32 (word.sru x (U32 (0%nat * 8))))
       (cons #(u8_from_u32 (word.sru x (U32 (1%nat * 8))))
             (cons #(u8_from_u32 (word.sru x (U32 (2%nat * 8))))
                   (cons #(u8_from_u32 (word.sru x (U32 (3%nat * 8))))
                         nil))).
Proof.
  cbv [u32_le fmap list_fmap LittleEndian.split HList.tuple.to_list List.map].
  repeat f_equal.
  - apply Properties.word.unsigned_inj.
    unfold u8_from_u32, U8.
    rewrite word.unsigned_of_Z.
    rewrite word.unsigned_sru.
Admitted.

Opaque word.sru.

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
