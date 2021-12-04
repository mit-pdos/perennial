(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export disk_prelude.
(* Import Coq model of our Goose program.*)
From Goose.go_mvcc Require Import tuple.

Section heap.
Context `{!heapGS Σ}.

Definition ver_to_val (x : u64 * u64 * u64) :=
  (#x.1.1, (#x.1.2, (#x.2, #())))%V.

Definition own_tuple (tuple_ptr : loc) : iProp Σ :=
  ∃ (tidown tidrd tidwr : u64) (vers : Slice.t)
    (versL : list (u64 * u64 * u64)),
    "Htidown" ∷ tuple_ptr ↦[Tuple :: "tidown"] #tidown ∗
    "Htidrd" ∷ tuple_ptr ↦[Tuple :: "tidrd"] #tidrd ∗
    "Htidwr" ∷ tuple_ptr ↦[Tuple :: "tidwr"] #tidwr ∗
    "Hvers" ∷ tuple_ptr ↦[Tuple :: "vers"] (to_val vers) ∗
    "HversL" ∷ slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL) ∗
    "_" ∷ True.

Local Hint Extern 1 (environments.envs_entails _ (own_tuple _)) => unfold own_tuple : core.

Definition is_tuple (tuple_ptr : loc) : iProp Σ :=
  ∃ (latch : loc) (rcond : loc) γ,
    "#Hlatch" ∷ readonly (tuple_ptr ↦[Tuple :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock γ #latch (own_tuple tuple_ptr) ∗
    "#Hrcond" ∷ readonly (tuple_ptr ↦[Tuple :: "rcond"] #rcond) ∗
    "#HrcondC" ∷ is_cond rcond #latch ∗
    "_" ∷ True.

Lemma val_to_ver_with_lookup (x : val) (l : list (u64 * u64 * u64)) (i : nat) :
  (ver_to_val <$> l) !! i = Some x ->
  (∃ (b e v : u64), x = ver_to_val (b, e, v) ∧ l !! i = Some (b, e, v)).
Proof.
  intros H.
  apply list_lookup_fmap_inv in H as [[[y1 y2] y3] [Heq Hsome]].
  naive_solver.
Qed.

(*****************************************************************)
(* func findRightVer(tid uint64, vers []Version) (Version, bool) *)
(*****************************************************************)
Local Theorem wp_findRightVer (tid : u64) (vers : Slice.t)
                              (versL : list (u64 * u64 * u64)) :
  {{{ slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL) }}}
    findRightVer #tid (to_val vers)
  {{{ (ver : (u64 * u64 * u64)) (found : bool), RET (ver_to_val ver, #found);
      ⌜found = false ∨ (found = true ∧ (int.Z ver.1.1 ≤ int.Z tid < int.Z ver.1.2))⌝ ∗
      slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL)
  }}}.
Proof.
  iIntros (Φ) "HversL HΦ".
  iDestruct (slice.is_slice_small_acc with "HversL") as "[HversL HversL_close]".
  wp_call.
  
  (***********************************************************)
  (* var ret Version                                         *)
  (* var found bool = false                                  *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first auto.
  iIntros (verR) "HverR".
  wp_pures.
  wp_apply wp_ref_to; first auto.
  iIntros (foundR) "HfoundR".

  (***********************************************************)
  (* for _, ver := range vers {                              *)
  (*   if ver.begin <= tid && tid < ver.end {                *)
  (*     ret = ver                                           *)
  (*     found = true                                        *)
  (*   }                                                     *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (slice.wp_forSlice
              (λ _, ∃ (ver : u64 * u64 * u64) (found : bool),
                 (verR ↦[struct.t Version] ver_to_val ver) ∗
                 (foundR ↦[boolT] #found) ∗
                 (⌜found = false ∨ (found = true ∧ (int.Z ver.1.1 ≤ int.Z tid < int.Z ver.1.2))⌝)
              )%I
              _ _ _ _ _ (ver_to_val <$> versL)
              with "[] [HverR HfoundR HversL]").
  { (* Loop body preserves the invariant. *)
    clear Φ.
    iIntros (i x Φ).
    iModIntro.
    iIntros "H HΦ".
    iDestruct "H" as "(H & %Hbound & %Hsome)".
    iDestruct "H" as (ver found) "(HverR & HfoundR & %Hright)".
    apply val_to_ver_with_lookup in Hsome as (b & e & v & Hx & Hsome).
    subst.
    wp_pures.
    wp_apply (wp_and_pure (int.Z b ≤ int.Z tid)%Z (int.Z tid < int.Z e)%Z with "[] []").
    { wp_pures. done. }
    { iIntros "_".
      wp_pures.
      done.
    }
    wp_if_destruct.
    - (* Is the correct version *)
      wp_store.
      wp_pures.
      wp_store.
      iApply "HΦ".
      iModIntro.
      iExists _, true.
      iSplitL "HverR"; auto.
    - (* Not the correct version *)
      iApply "HΦ".
      iModIntro.
      iExists ver, found.
      iSplitL "HverR"; auto.
  }
  { (* Loop invariant holds at the begining *)
    iFrame.
    simpl.
    iExists (_, _, _), false.
    iSplitL "HverR"; last auto.
    iFrame.
  }
  
  (***********************************************************)
  (* return ret, found                                       *)
  (***********************************************************)
  iIntros "[H HversL]".
  iDestruct "H" as (ver found) "(HverR & HfoundR & %Hright)".
  iDestruct ("HversL_close" with "HversL") as "HversL".
  wp_pures.
  wp_load.
  wp_load.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
  auto.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) ReadVersion(tid uint64) (uint64, bool)    *)
(*****************************************************************)
Theorem wp_tuple__ReadVersion tuple_ptr (tid : u64) :
  is_tuple tuple_ptr -∗
  {{{ True }}}
    Tuple__ReadVersion #tuple_ptr #tid
  {{{ (v : u64) (b : bool), RET (#v, #b); True }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "_ HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.

  (***********************************************************)
  (* for tid >= tuple.tidwr && tuple.tidown != 0 {           *)
  (*   tuple.rcond.Wait()                                    *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_forBreak_cond
              (λ _,
                 (own_tuple tuple_ptr) ∗
                 (locked #latch))%I
              with "[] [-HΦ]").
  (**
   * Q: Is it correct to say `wp_forBreak_cond` is used when the loop invariant
   * is the same as the pre/post conditions? Use `wp_apply (wp_forBreak_cond I)` for
   * customized loop invariant?
   *)
  (* Customize the loop invariant as waiting on condvar havocs the values. *)
  { (* Loop body preserves the invariant. *)
    clear Φ.
    iIntros (Φ).
    iModIntro.
    clear tidown tidrd tidwr vers versL.
    iIntros "[Hown Hlocked] HΦ".
    iNamed "Hown".
    wp_pures.
    wp_loadField.
    wp_pures.
    (**
     * Interesting thing going on here: `wp_and` seems to bind the wrong if.
     * Reason: Goose generate a similar form for both loops and logical ands.
     * Solution here is using `wp_bind` to focus on the right if:
     * `wp_bind (If #(bool_decide _) _ _).`
     *)
    wp_bind (If #(bool_decide _) _ _).
    (* Constructing the condition for blocking readers. *)
    wp_apply (wp_and with "Htidown").
    { wp_pures. done. }
    { iIntros "_ Htidown".
      wp_loadField.
      wp_pures.
      rewrite -bool_decide_not.
      eauto with iFrame.
    }
    iIntros "Htidown".
    wp_if_destruct.
    { wp_pures.
      wp_loadField.
      wp_apply (wp_condWait with "[-HΦ]").
      { eauto 10 with iFrame. }
      iIntros "[Hlocked Hown]".
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame.
    }
    iApply "HΦ".
    eauto 10 with iFrame.
  }
  { (* The invariant holds at the start. *)
    eauto 10 with iFrame.
  }
  clear tidown tidrd tidwr vers versL.
  iIntros "[Hown Hlocked]".
  iNamed "Hown".
  wp_pures.
  
  (***********************************************************)
  (* if tuple.tidrd < tid {                                  *)
  (*   tuple.tidrd = tid                                     *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_If_join_evar with "[-]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    - wp_if_true.
      wp_storeField.
      iSplit; first done.
      (* Update "Htidrd" to use `b'` for merging states. See comments of wp_If_join_evar in control.v. *)
      replace (#tid) with #(if b' then tid else tidrd) by by rewrite Eb'.
      iNamedAccu.
    - wp_if_false.
      iModIntro.
      rewrite Eb'.
      iFrame.
      done.
  }
  iIntros "H".
  iNamed "H".
  wp_pures.

  (***********************************************************)
  (* ver, found := findRightVer(tid, tuple.vers)             *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_findRightVer with "HversL").
  iIntros (ver found) "[%Hright HversL]".
  wp_pures.

  (***********************************************************)
  (* if !found {                                             *)
  (*   tuple.latch.Unlock()                                  *)
  (*   return 0, false                                       *)
  (* }                                                       *)
  (***********************************************************)
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    { case_bool_decide; eauto 10 with iFrame. }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    done.
  }

  (***********************************************************)
  (* val := ver.val                                          *)
  (***********************************************************)
  wp_pures.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  { case_bool_decide; eauto 10 with iFrame. }
  wp_pures.
  iModIntro.

  (***********************************************************)
  (* return val, true                                        *)
  (***********************************************************)
  iApply "HΦ".
  done.

  (**
   * Q1: Can we avoid simplying (zero_val (refT ..)) (to match the form of wp_ref_of_zero)?
   * Q2: How does (zero_val (refT ..)) get simplified when there is no case for refT in zero_val?
   *)
  (*
  replace #null with (zero_val (refT (struct.t Version))); last first.
  { simpl. reflexivity. }
  *)
Qed.

(*****************************************************************)
(* func (tuple *Tuple) AppendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__AppendVersion tuple_ptr (tid : u64) (val : u64) :
  is_tuple tuple_ptr -∗
  {{{ True }}}
    Tuple__AppendVersion #tuple_ptr #tid #val
  {{{ b, RET #b; True }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "_ HΦ".
  iNamed "Htuple".
  wp_call.

  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.

  (***********************************************************)
  (* if len(tuple.vers) > 0 {                                *)
  (*   idx := len(tuple.vers) - 1                            *)
  (*   verPrevRef := &tuple.vers[idx]                        *)
  (*   verPrevRef.end = tid                                  *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_apply wp_slice_len.

  (**
   * Note 1(a): We need to create `x` *before* using `wp_apply (wp_If_join_evar ...)`
   * to make sure that `x` is present at the time the goal evar is
   * created (so that `iNamedAccu` can succeed).
   * Q: Is there a better way to deal with this?
   *)
  assert (H : ∃ (x : u64 * u64 * u64),
                  (int.nat (word.sub vers.(Slice.sz) 1) < length versL)%nat ->
                  versL !! int.nat (word.sub vers.(Slice.sz) 1) = Some x).
  { destruct (bool_decide (int.nat (word.sub vers.(Slice.sz) 1) < length versL)%nat) eqn:E.
    - case_bool_decide; last congruence.
      apply list_lookup_lt in H as [x H].
      exists x.
      intros _.
      apply H.
    - case_bool_decide; first congruence.
      exists ((U64 0), (U64 0), (U64 0)).
      intros contra. destruct (H contra).
  }
  destruct H as [x Hx].
  
  wp_apply (wp_If_join_evar with "[-HΦ]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    - wp_if_true.
      wp_loadField.
      wp_apply wp_slice_len.
      wp_pures.
      wp_loadField.
      wp_lam.
      wp_pures.
      wp_apply wp_slice_len.
      
      wp_if_destruct; last first.
      { (* prove in-bound *)
        destruct Heqb. word.
      }
      wp_apply wp_slice_ptr.
      wp_pures.
      iDestruct (slice.is_slice_small_acc with "HversL") as "[HversL HversL_close]".
      rewrite /slice.is_slice_small.
      iDestruct "HversL" as "[HversA %HversLen]".
      (**
       * Note 1(b): Below is a wrong attempt which creates `x` after the
       * goal evar is created:
       * apply list_lookup_lt in HversLenLast as [x Hsome].
       *)
      iDestruct (update_array (off:=int.nat (word.sub vers.(Slice.sz) 1)) with "HversA") as "[Hver HversA]".
      { rewrite list_lookup_fmap.
        rewrite Hx; first done.
        rewrite fmap_length in HversLen. rewrite HversLen. word.
      }
      iDestruct (struct_fields_split with "Hver") as "Hver".
      iNamed "Hver".
      wp_apply (wp_storeField with "[end]"); first auto.
      { iNext.
        (* Set Printing Coercions. *)
        iExactEq "end".
        do 3 f_equal.
        word.
      }
      iIntros "end".
      word_cleanup.
      (**
       * Q: how does `set` know `+ₗ[struct.t Version] = +ₗ (1 + (1 + (1 + 0)))`?
       * `remember` below does not know:
       * remember (vers.(Slice.ptr) +ₗ[_] (int.Z vers.(Slice.sz) - 1)) as verLastR.
       *)
      set verLastR := (vers.(Slice.ptr) +ₗ[_] (int.Z vers.(Slice.sz) - 1)).
      set verLast := (x.1.1, tid, x.2).
      (* Q: Better way of closing struct? *)
      iAssert (verLastR ↦[struct.t Version] (ver_to_val verLast))%I with "[begin val end]" as "Hver".
      { iDestruct (struct_fields_split verLastR 1%Qp Version (ver_to_val verLast)
                    with "[begin end val]") as "Hver"; last iFrame.
        rewrite /struct_fields.
        iFrame.
        done.
      }
      iDestruct ("HversA" with "Hver") as "HversA".
      iDestruct ("HversL_close" with "[HversA]") as "HversL".
      { iFrame.
        iPureIntro.
        rewrite <- HversLen.
        apply insert_length.
      }
      iSplitL ""; first done.
      set new_vers := (<[_:=_]> (ver_to_val <$> versL)).
      replace new_vers with (if b' then new_vers else ver_to_val <$> versL) by by rewrite Eb'.
      (**
       * Note 1(c): `verLast` is created *after* the goal evar, so we
       * should remove `verLast` from the spatial context before
       * calling `iNamedAccu`.
       * UPDATE: Since we use `set` instead of `remember`, we don't
       * actually need to do the subst here.
       *)
      (* subst verLast. *)
      iNamedAccu.
    - wp_if_false.
      iModIntro.
      subst.
      iFrame.
      done.
  }

  (***********************************************************)
  (* verNext := Version{                                     *)
  (*   begin   : tid,                                        *)
  (*   end     : config.TID_SENTINEL,                        *)
  (*   val     : val,                                        *)
  (* }                                                       *)
  (* tuple.vers = append(tuple.vers, verNext)                *)
  (***********************************************************)
  iIntros "H".
  iNamed "H".
  wp_pures.
  wp_loadField.
  wp_apply (wp_SliceAppend' with "[HversL]").
  { done. }
  { auto. }
  { iFrame. }
  iIntros (vers') "HversL".
  wp_storeField.
  wp_pures.

  (***********************************************************)
  (* tuple.tidown = 0                                        *)
  (* tuple.tidwr = tid                                       *)
  (***********************************************************)
  wp_storeField.
  wp_storeField.

  (***********************************************************)
  (* tuple.rcond.Broadcast()                                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_condBroadcast with "[$HrcondC]").
  wp_pures.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  { (* Restoring the lock invariant. *)
    iFrame "Hlock Hlocked".
    iNext.
    rewrite /own_tuple.
    case_bool_decide.
    { (* Prove `is_slice` when the slice is updated and appended. *)
      do 4 iExists _. iExists (_ ++ [(tid, _, val)]).
      iFrame.
      rewrite -list_fmap_insert fmap_app.
      iFrame.
    }
    { (* Prove `is_slice` when the slice is appended. *)
      do 4 iExists _. iExists (_ ++ [(tid, _, val)]).
      iFrame.
      rewrite fmap_app.
      iFrame.
    }
  }
  wp_pures.
  iApply "HΦ".
  done.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) Free(tid uint64)                          *)
(*****************************************************************)
Theorem wp_tuple__Free tuple_ptr (tid : u64) :
  is_tuple tuple_ptr -∗
  {{{ True }}}
    Tuple__Free #tuple_ptr #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "_ HΦ".
  iNamed "Htuple".
  wp_call.

  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.

  (***********************************************************)
  (* tuple.tidown = 0                                        *)
  (***********************************************************)
  wp_storeField.

  (***********************************************************)
  (* tuple.rcond.Broadcast()                                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_condBroadcast with "[$HrcondC]").
  wp_pures.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  { eauto 10 with iFrame. }
  wp_pures.
  iApply "HΦ".
  done.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) Own(tid uint64) bool                      *)
(*****************************************************************)
Theorem wp_tuple__Own tuple_ptr (tid : u64) :
  is_tuple tuple_ptr -∗
  {{{ True }}}
    Tuple__Own #tuple_ptr #tid
  {{{ b, RET #b; True }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "_ HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.

  (***********************************************************)
  (* if tid < tuple.tidrd || tid < tuple.tidwr {             *)
  (*   tuple.latch.Unlock()                                  *)
  (*   return false                                          *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_or with "[Htidwr]").
  { iApply "Htidwr". }
  { wp_pures. done. }
  { iIntros "_ Hidwr". wp_loadField. wp_pures. iFrame. done. }
  iIntros "Hidrwr".
  wp_if_destruct.
  { (* Early return: `tid < tuple.tidrd || tid < tuple.tidwr` *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    { eauto 10 with iFrame. }
    wp_pures.
    iModIntro. iApply "HΦ". done.
  }

  (***********************************************************)
  (* if tuple.tidown != 0 {                                  *)
  (*   tuple.latch.Unlock()                                  *)
  (*   return false                                          *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_if_destruct.
  { (* Early return: `tuple.tidown != 0` *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    { eauto 10 with iFrame. }
    wp_pures.
    iModIntro. iApply "HΦ". done.
  }

  (***********************************************************)
  (* tuple.tidown = tid                                      *)
  (***********************************************************)
  wp_storeField.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  { eauto 10 with iFrame. }
  wp_pures.
  iModIntro.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iApply "HΦ".
  done.
Qed.

Definition mvccNS := nroot .@ "mvcc".

(*****************************************************************)
(* func MkTuple() *Tuple                                         *)
(*****************************************************************)
Theorem wp_MkTuple :
  {{{ True }}}
    MkTuple #()
  {{{ (t : loc), RET #t; is_tuple t }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.

  (***********************************************************)
  (* tuple := new(Tuple)                                     *)
  (***********************************************************)
  wp_apply (wp_allocStruct).
  { apply zero_val_ty'.
    simpl.
    repeat split.
  }
  iIntros (tuple) "Htuple".
  iDestruct (struct_fields_split with "Htuple") as "Htuple".
  iNamed "Htuple".
  simpl.
  wp_pures.
  
  (***********************************************************)
  (* tuple.latch = new(sync.Mutex)                           *)
  (***********************************************************)
  wp_apply (wp_new_free_lock).
  iIntros (latch) "Hfree".
  wp_storeField.
  
  (***********************************************************)
  (* tuple.rcond = sync.NewCond(tuple.latch)                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_newCond' with "Hfree").
  iIntros (rcond) "[Hfree #HrcondC]".
  
  (***********************************************************)
  (* tuple.tidown = 0                                        *)
  (* tuple.tidrd = 0                                         *)
  (* tuple.tidwr = 0                                         *)
  (***********************************************************)
  repeat wp_storeField.
  
  (***********************************************************)
  (* tuple.vers = make([]Version, 0, 16)                     *)
  (***********************************************************)
  wp_apply (wp_new_slice); first auto.
  iIntros (vers) "HversL".
  wp_storeField.
  
  (***********************************************************)
  (* return tuple                                            *)
  (***********************************************************)
  iMod (alloc_lock mvccNS _ latch (own_tuple tuple) with "[$Hfree] [-latch rcond HΦ]") as "#Hlock".
  { iNext.
    remember (replicate (int.nat 0) ((U64 0), (U64 0), (U64 0))) as versL.
    iExists (U64 0), (U64 0), (U64 0), vers, versL.
    iFrame.
    iSplit; last done.
    subst.
    auto.
  }
  iApply "HΦ".
  iExists latch, rcond, mvccNS.
  iMod (readonly_alloc_1 with "latch") as "$".
  iMod (readonly_alloc_1 with "rcond") as "$".
  iFrame "#".
  done.
Qed.

Lemma val_to_ver_with_val_ty (x : val) :
  val_ty x (uint64T * (uint64T * (uint64T * unitT))%ht) ->
  (∃ (b e v : u64), x = ver_to_val (b, e, v)).
Proof.
  intros H.
  inversion_clear H. 
  { inversion H0. }
  inversion_clear H0.
  inversion_clear H.
  inversion_clear H1.
  { inversion H. }
  inversion_clear H.
  inversion_clear H1.
  inversion_clear H0.
  { inversion H. }
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H.
  exists x0, x1, x2.
  reflexivity.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) RemoveVersions(tid uint64)                *)
(*****************************************************************)
Theorem wp_tuple__RemoveVersions tuple_ptr (tid : u64) :
  is_tuple tuple_ptr -∗
  {{{ True }}}
    Tuple__RemoveVersions #tuple_ptr #tid
  {{{ b, RET #b; True }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "_ HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.

  (***********************************************************)
  (* var idx uint64 = 0                                      *)
  (* for {                                                   *)
  (*   if idx >= uint64(len(tuple.vers)) {                   *)
  (*     break                                               *)
  (*   }                                                     *)
  (*   ver := tuple.vers[idx]                                *)
  (*   if ver.end > tid {                                    *)
  (*     break                                               *)
  (*   }                                                     *)
  (*   idx++                                                 *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (idxR) "HidxR".
  wp_pures.
  wp_apply (wp_forBreak
              (λ _,
                (tuple_ptr ↦[Tuple :: "vers"] to_val vers) ∗
                (slice.is_slice vers (struct.t Version) 1 (ver_to_val <$> versL)) ∗
                (∃ (idx : u64), (idxR ↦[uint64T] #idx) ∗
                                (⌜int.Z idx ≤ int.Z vers.(Slice.sz)⌝) ∗
                                ([∗ list] k ↦ ver ∈ (take (int.nat idx) versL), ⌜(int.Z ver.1.2) ≤ (int.Z tid)⌝))
                )%I
             with "[] [$Hvers $HversL HidxR]").
  { clear Φ.
    iIntros (Φ).
    iModIntro.
    iIntros "Hinv HΦ".
    iDestruct "Hinv" as "(Hvers & HversL & Hidx)".
    iDestruct "Hidx" as (idx) "(HidxR & %Hbound & HidxOrder)".
    wp_pures.
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_load.
    wp_pures.
    wp_if_destruct.
    { iModIntro.
      iApply "HΦ".
      eauto 10 with iFrame.
    }
    wp_load.
    wp_loadField.
    iDestruct (slice.is_slice_small_acc with "HversL") as "[HversS HversL]".
    iDestruct (slice.is_slice_small_sz with "[$HversS]") as "%HversSz".
    destruct (list_lookup_lt _ (ver_to_val <$> versL) (int.nat idx)) as [ver Hsome].
    { apply Z.nle_gt in Heqb.
      word.
    }
    wp_apply (slice.wp_SliceGet with "[HversS]"); first auto.
    iIntros "[HversS %HverT]".
    destruct (val_to_ver_with_val_ty _ HverT) as (b & e & v & H).
    subst.
    wp_pures.
    iDestruct ("HversL" with "HversS") as "HversL".
    wp_if_destruct.
    { iModIntro.
      iApply "HΦ".
      eauto with iFrame.
    }
    wp_load.
    wp_pures.
    wp_store.
    iModIntro.
    iApply "HΦ".
    iFrame.
    iExists (word.add idx 1%Z).
    iFrame.
    admit.
  }
  { iExists (U64 0).
    iFrame.
    iSplit.
    - iPureIntro. word.
    - change (int.nat 0) with 0%nat.
      rewrite take_0.
      naive_solver.
  }
  iIntros "(Hvers & HversL & Hidx)".
  iDestruct "Hidx" as (idx) "(HidxR & %Hbound & HidxOrder)".
  wp_pures.

  (***********************************************************)
  (* tuple.vers = tuple.vers[idx:]                           *)
  (***********************************************************)
  wp_load.
  wp_loadField.
  wp_apply (wp_SliceSkip').
  { eauto. }
  wp_storeField.
  (* Weaken is_slice. Should this go to the slice lib? *)
  iDestruct "HversL" as "[HversS HversC]".
  iDestruct (slice.is_slice_small_take_drop _ _ _ idx with "HversS") as "[HversS _]".
  { word. }
  iDestruct (slice.is_slice_cap_skip _ _ idx with "HversC") as "HversC".
  { word. }
  iDestruct (slice.is_slice_split with "[$HversS $HversC]") as "HversL".
  rewrite <- fmap_drop.
  
  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  { eauto 10 with iFrame. }
  wp_pures.
  iApply "HΦ".
  done.
Admitted.

End heap.
