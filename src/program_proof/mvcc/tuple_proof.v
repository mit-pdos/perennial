(* Import definitions/theorems of the Perennial framework. *)
From Perennial.program_proof Require Export proof_prelude.
(* Use disk FFI as a place holder. *)
From Perennial.goose_lang Require Export ffi.disk_prelude.
(* Import Coq model of our Goose program.*)
From Goose.go_mvcc Require Import tuple.

Section heap.
Context `{!heapGS Σ}.

Definition ver_to_val (x : u64 * u64 * u64) :=
  (#x.1.1, (#x.1.2, (#x.2, #())))%V.

Definition own_tuple (tuple_ptr : loc) (latch : val) : iProp Σ :=
  ∃ (tidown tidrd tidwr : u64) (vers : Slice.t)
    (versL : list (u64 * u64 * u64)),
    "Htidown" ∷ tuple_ptr ↦[Tuple :: "tidown"] #tidown ∗
    "Htidrd" ∷ tuple_ptr ↦[Tuple :: "tidrd"] #tidrd ∗
    "Htidwr" ∷ tuple_ptr ↦[Tuple :: "tidwr"] #tidwr ∗
    "Hvers" ∷ tuple_ptr ↦[Tuple :: "vers"] (to_val vers) ∗
    "HversL" ∷ slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL) ∗
    "_" ∷ True.

Definition is_tuple (tuple_ptr : loc) : iProp Σ :=
  ∃ (latch : val) (rcond : loc) γ,
    "#Hlatch" ∷ readonly (tuple_ptr ↦[Tuple :: "latch"] latch) ∗
    "#Hlock" ∷ is_lock γ latch (own_tuple tuple_ptr latch) ∗
    "#Hrcond" ∷ readonly (tuple_ptr ↦[Tuple :: "rcond"] #rcond) ∗
    "#HrcondC" ∷ is_cond rcond latch ∗
    "_" ∷ True.

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
  unfold Tuple__AppendVersion.

  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_pures.
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
  wp_if_destruct.
  { (* `vers` not empty *)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_pures.
    wp_loadField.
    wp_lam.
    wp_pures.
    wp_apply wp_slice_len.
    
    wp_if_destruct; last first.
    { (* prove in-bound *)
      exfalso.
      destruct (bool_decide (int.Z vers.(Slice.sz) = int.Z 0)) eqn:E.
      - apply bool_decide_eq_true in E. lia.
      - apply bool_decide_eq_false in E.
        destruct Heqb0.
        apply word.decrement_nonzero_lt. done.
    }
    wp_apply wp_slice_ptr.
    wp_pures.
    iDestruct (slice.is_slice_small_acc with "HversL") as "[HversL HversL_close]".
    rewrite /slice.is_slice_small.
    iDestruct "HversL" as "[HversA %HversLen]".
    (* Below we try to prove the last element of `versL` contains something. *)
    assert (HversLenLast : ((int.nat (word.sub vers.(Slice.sz) (U64 1))) < length versL)%nat).
    (* Set Printing Coercions. *)
    { rewrite fmap_length in HversLen. rewrite HversLen. word. }
    apply list_lookup_lt in HversLenLast as [x Hsome].
    iDestruct (update_array with "HversA") as "[Hver HversA]".
    (* Better proof? *)
    { rewrite list_lookup_fmap.
      instantiate (1:=ver_to_val x).
      instantiate (1:=int.nat (word.sub vers.(Slice.sz) 1)).
      rewrite Hsome.
      auto.
    }
    iDestruct (struct_fields_split with "Hver") as "Hver".
    iNamed "Hver".
    wp_apply (wp_storeField with "[end]"); first auto.
    { iNext.
      (* Set Printing Coercions. *)
      rewrite u64_Z_through_nat.
      iFrame.
    }
    iIntros "end".
    (* Close things. Better proof? *)
    remember (vers.(Slice.ptr) +ₗ[struct.t Version] int.nat (word.sub vers.(Slice.sz) 1)) as verLastR.
    remember (x.1.1, tid, x.2) as verLast.
    iAssert (verLastR ↦[struct.t Version] (ver_to_val verLast))%I with "[begin val end]" as "Hver".
    { iDestruct (struct_fields_split verLastR 1%Qp Version (ver_to_val verLast)
                  with "[begin end val]") as "Hver"; last iFrame.
      rewrite /struct_fields.
      simpl.
      subst.
      rewrite u64_Z_through_nat.
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
    
    (* Appending new version. *)
    wp_pures.
    wp_loadField.
    wp_apply (wp_SliceAppend' with "[HversL]").
    { done. }
    { auto. }
    { iFrame. }
    iIntros (vers') "HversL".
    wp_apply (wp_storeField with "[Hvers]").
    { apply slice_val_ty. }
    { done. }
    iIntros "Hvers".
    wp_storeField.
    wp_storeField.
    wp_loadField.
    wp_apply (wp_condBroadcast with "[$HrcondC]").
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    { iFrame "Hlock Hlocked".
      iNext.
      iExists (U64 0), tidrd, tid, vers', _.
      iFrame.
      iSplitL; last done.
      instantiate (1:=(<[int.nat (word.sub vers.(Slice.sz) 1):=verLast]> versL) ++ [(tid, (U64 18446744073709551615), val)]).
      rewrite fmap_app.
      rewrite list_fmap_insert.
      iFrame.
    }
    wp_pures.
    iApply "HΦ".
    done.
  }

  (* Appending new version (without updating the latest version). *)
  (***********************************************************)
  (* verNext := Version{                                     *)
  (*   begin   : tid,                                        *)
  (*   end     : config.TID_SENTINEL,                        *)
  (*   val     : val,                                        *)
  (* }                                                       *)
  (* tuple.vers = append(tuple.vers, verNext)                *)
  (***********************************************************)
  wp_pures.
  wp_loadField.
  wp_apply (wp_SliceAppend' with "[HversL]").
  { done. }
  { auto. }
  { iFrame. }
  iIntros (vers') "HversL".
  wp_apply (wp_storeField with "[Hvers]").
  { apply slice_val_ty. }
  { done.}
  iIntros "Hvers".
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
    remember (versL ++ [(tid, (U64 18446744073709551615), val)]) as versL'.
    iExists (U64 0), tidrd, tid, vers', versL'.
    iFrame.
    subst.
    rewrite fmap_app.
    iFrame.
  }
  wp_pures.
  iApply "HΦ".
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

Lemma val_to_ver_with_lookup (x : val) (l : list (u64 * u64 * u64)) (i : nat) :
  (ver_to_val <$> l) !! i = Some x ->
  (∃ (b e v : u64), x = ver_to_val (b, e, v) ∧ l !! i = Some (b, e, v)).
Proof.
  intros H.
  apply list_lookup_fmap_inv in H as [[[y1 y2] y3] [Heq Hsome]].
  subst.
  rewrite Hsome.
  exists y1, y2, y3.
  auto.
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
    (* More concise proof here? *)
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
      iExists (b, e, v), true.
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
    iExists ((U64 0), (U64 0), (U64 0)), false.
    iSplitL "HverR"; last auto.
    iFrame.
  }
  
  (***********************************************************)
  (*  return ret, found                                      *)
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
                 (own_tuple tuple_ptr latch) ∗
                 (locked latch))%I
              with "[] [-HΦ]").
  (**
   * Q: Is it correct to say `wp_forBreak_cond` is used when the loop invariant
   * is the same as the pre/post conditions? Use `wp_apply (wp_forBreak I)` for
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
      iFrame.
      iPureIntro.
      (* Maybe a more concise proof here? *)
      assert (H : ∀ (P : Prop) (dec : Decision P), negb (bool_decide P) = bool_decide (not P)).
      { intros P dec. case_bool_decide.
        - simpl. symmetry. rewrite bool_decide_eq_false. auto.
        - simpl. symmetry. rewrite bool_decide_eq_true. apply H. }
      rewrite H.
      reflexivity.
    }
    iIntros "Htidown".
    wp_if_destruct.
    { wp_pures.
      wp_loadField.
      wp_apply (wp_condWait with "[-HΦ]").
      { iFrame "Hlock Hlocked HrcondC".
        iExists tidown, tidrd, tidwr, vers, versL.
        iFrame "% # ∗".
      }
      iIntros "[Hlocked Hown]".
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame.
    }
    iApply "HΦ".
    iModIntro.
    iFrame.
    iExists tidown, tidrd, tidwr, vers, versL.
    iFrame.
  }
  { (* The invariant holds at the start. *)
    iFrame "Hlocked".
    iExists tidown, tidrd, tidwr, vers, versL.
    iFrame "% ∗".
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
      iAssert (tuple_ptr ↦[Tuple :: "tidrd"] #(if b' then tid else tidrd)) with "[Htidrd]" as "Htidrd".
      { rewrite Eb'. iFrame "Htidrd". }
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
    { iFrame "Hlock Hlocked".
      iNext.
      destruct (bool_decide (int.Z tidrd < int.Z tid)).
      - iExists tidown, tid, tidwr, vers, versL.
        iFrame.
      - iExists tidown, tidrd, tidwr, vers, versL.
        iFrame.
    }
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
  { iFrame "Hlock Hlocked".
    iNext.
    destruct (bool_decide (int.Z tidrd < int.Z tid)).
    - iExists tidown, tid, tidwr, vers, versL.
      iFrame.
    - iExists tidown, tidrd, tidwr, vers, versL.
      iFrame.
  }
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
  { iFrame "Hlock Hlocked".
    iNext.
    rewrite /own_tuple.
    iExists (U64 0), tidrd, tidwr, vers, versL.
    iFrame.
  }
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
    { iFrame "Hlock Hlocked".
      iNext.
      iExists tidown, tidrd, tidwr, vers, versL.
      iFrame.
    }
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
    { iFrame "Hlock Hlocked".
      iNext.
      iExists tidown, tidrd, tidwr, vers, versL.
      iFrame.
    }
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
  { iFrame "Hlock Hlocked".
    iNext.
    iExists tid, tidrd, tidwr, vers, versL.
    iFrame.
  }
  wp_pures.
  iModIntro.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iApply "HΦ".
  done.
Qed.
