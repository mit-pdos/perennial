(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export disk_prelude.
(* Import Coq model of our Goose program.*)
From Goose.github_com.mit_pdos.go_mvcc Require Import tuple.
From Perennial.program_proof.mvcc Require Import mvcc_ghost.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition ver_to_val (x : u64 * u64 * u64) :=
  (#x.1.1, (#x.1.2, (#x.2, #())))%V.

Definition own_versL γ (versL : list (u64 * u64 * u64)) := ghost_var γ.(tuple_vers_gn) (1/2) versL.

(* Logical representation of a version. *)
Record lver :=
  { dq : dfrac;
    v  : u64;
  }.

Definition pvers_rep (pvers : list (u64 * u64 * u64)) : iProp Σ :=
  (* TODO: end = begin of next ver *)
  (* TODO: end of the last ver = sentinel *)
  (* TODO: begin < end *)
  True.

Definition to_lvers (b e : nat) (v : u64) (dq : dfrac) : list lver :=
  replicate (e - b) {| dq := dq; v := v |}.
  
Definition pver_to_lvers (pver : u64 * u64 * u64) (dq : dfrac) : list lver :=
  to_lvers (int.nat pver.1.1) (int.nat pver.1.2) pver.2 dq.

(*
(* TODO: `pvers_to_lvers` hasn't handled empty values in the beginning. *)
Fixpoint pvers_to_lvers (pvers : list (u64 * u64 * u64)) (fixed : nat) : list lver :=
  match pvers with
  (* TODO: empty tuple is handled as a special case. *)
  | [] => []
  (* The last physical version is translated to a fixed part and a non-fixed part. *)
  | pver :: [] => (to_lvers (int.nat pver.1.1) fixed pver.2 DfracDiscarded) ++
                 (to_lvers fixed tid_sentinel pver.2 (DfracOwn 1))
  (* Non-last physical versions are always fixed. *)
  | pver :: tail => (pver_to_lvers pver DfracDiscarded) ++ (pvers_to_lvers tail fixed)
  end.
*)

Definition own_tuple (tuple : loc) (key : u64) (γ : mvcc_names) : iProp Σ :=
  ∃ (tidown tidrd tidwr : u64) (vers : Slice.t)
    (versL : list (u64 * u64 * u64))
    (* (fixed : nat) *),
    "Htidown" ∷ tuple ↦[Tuple :: "tidown"] #tidown ∗
    "Htidrd" ∷ tuple ↦[Tuple :: "tidrd"] #tidrd ∗
    "Htidwr" ∷ tuple ↦[Tuple :: "tidwr"] #tidwr ∗
    "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val vers) ∗
    "HversL" ∷ slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL) ∗
    "HversLI" ∷ own_versL γ versL ∗
    (*
    "HpversRep" ∷ pvers_rep versL ∗
    "Hfixed" ∷ ⌜fixed = max (int.nat tidrd) (int.nat tidwr)⌝ ∗
    "HfixedQ" ∷ (fixed_ptsto γ 1 key fixed ∧ ⌜tidown = (U64 0)⌝) ∨
                (fixed_ptsto γ (1/2) key fixed ∧ ⌜tidown ≠ (U64 0)⌝) ∗
    "Hdbptsto" ∷ [∗ list] ts ↦ v ∈ (pvers_to_lvers versL fixed), db_ptsto γ v.(dq) ts key v.(v) ∗
    *)
    "_" ∷ True.

Local Hint Extern 1 (environments.envs_entails _ (own_tuple _ _ _)) => unfold own_tuple : core.

Definition is_tuple (tuple : loc) (key : u64) (γ : mvcc_names) : iProp Σ :=
  ∃ (latch : loc) (rcond : loc),
    "#Hlatch" ∷ readonly (tuple ↦[Tuple :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_tuple tuple key γ) ∗
    "#Hrcond" ∷ readonly (tuple ↦[Tuple :: "rcond"] #rcond) ∗
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

Definition TID_SENTINEL := (U64 18446744073709551615).

Definition extend_verchain (tid : u64) (val : u64) versL :=
  match (last versL) with
  | Some v => <[pred (length versL) := (v.1.1, tid, v.2)]> versL
  | None => []
  end ++ [(tid, TID_SENTINEL, val)].

(*****************************************************************)
(* func (tuple *Tuple) AppendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__AppendVersion tuple (tid : u64) (val : u64) (key : u64) versL γ :
  is_tuple tuple key γ -∗
  {{{ own_versL γ versL }}}
    Tuple__AppendVersion #tuple #tid #val
  {{{ RET #(); own_versL γ (extend_verchain tid val versL) }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "HversLU HΦ".
  rename versL into versL'.
  iNamed "Htuple".
  wp_call.

  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  (* Keep the equation of the slice size and the list length. *)
  iDestruct (is_slice_sz with "HversL") as %HversLen.
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
      iDestruct "HversL" as "[HversA _]".
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
  set b := bool_decide _.
  iDestruct (ghost_var_agree with "HversLU HversLI") as %->.
  iMod (ghost_var_update_halves (if b then _ else _) with "HversLU HversLI") as "[HversLU HversLI]".
  wp_apply (release_spec with "[-HΦ HversLU]").
  { (* Restoring the lock invariant. *)
    iFrame "Hlock Hlocked".
    rewrite /own_tuple.
    unfold b.
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
  iModIntro.

  (* Prove the postcondition. Should have better proof... *)
  rewrite fmap_length in HversLen.
  rewrite /extend_verchain.
  unfold b.
  destruct (last versL) eqn:E.
  - case_bool_decide.
    + iExactEq "HversLU".
      f_equal.
      rewrite HversLen.
      replace p with x; last first.
      { rewrite last_lookup in E.
        assert (Hpx : Some p = Some x).
        { rewrite <- Hx; last word.
          rewrite <- E.
          f_equal.
          word.
        }
        inversion Hpx.
        done.
      }
      change ({| u64_car := _ |}) with TID_SENTINEL.
      apply app_inv_tail_iff.
      f_equal.
      word.
    + exfalso.
      apply mk_is_Some in E.
      apply last_is_Some in E.
      rewrite <- length_zero_iff_nil in E.
      word_cleanup.
      rewrite HversLen in E.
      change (int.Z (U64 0)) with 0%Z in *.
      lia.
  - case_bool_decide.
    + exfalso.
      apply last_None in E.
      subst.
      rewrite nil_length in HversLen.
      word.
    + iExactEq "HversLU".
      f_equal.
      change ({| u64_car := _ |}) with TID_SENTINEL.
      apply app_inv_tail_iff.
      apply last_None in E.
      apply E.
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

(**
 * The spec of `ReadVersion` is actually non-trivial. Reasons:
 * 1) The version chains before and after `ReadVersion` is not
 *    guaranteed to be the same. However, they should satisfy some
 *    condition(s). My guess is that the new one is the suffix of
 *    the old one, appened with at most one element.
 * 2) `ReadVersion` is allowed to return a false *only* when there
 *    is no correct version in the old version chain. This should
 *    be crucial to ensure repeatable read, and hence serializability.
 *)

(*****************************************************************)
(* func (tuple *Tuple) ReadVersion(tid uint64) (uint64, bool)    *)
(*****************************************************************)
Theorem wp_tuple__ReadVersion tuple (tid : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ True }}}
    Tuple__ReadVersion #tuple #tid
  {{{ (val : u64) (found : bool), RET (#val, #found); view_ptsto key val }}}.
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
                 (own_tuple tuple key γ) ∗
                 (locked #latch)
              )%I
              with "[] [-HΦ]").
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
Qed.

(*****************************************************************)
(* func (tuple *Tuple) Free(tid uint64)                          *)
(*****************************************************************)
Theorem wp_tuple__Free tuple (tid : u64) (key : u64) (versL : list (u64 * u64 * u64)) γ :
  is_tuple tuple key γ -∗
  {{{ True }}}
    Tuple__Free #tuple #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "_ HΦ".
  rename versL into versL'.
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
Theorem wp_tuple__Own tuple (tid : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ True }}}
    Tuple__Own #tuple #tid
  {{{ (b : bool), RET #b; if b
                        then mods_token key
                        else True
  }}}.
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

(**
 * The `safe_rm_verchain` says that,
 * 1) the new list is a sublist of the old list (so no new versions can be added).
 * 2) all the versions whose end timestamp is greater than `tid` are preserved.
 *
 * We could additionally specify the performance-related condition as follows:
 * 3) all the versions whose end timestamp is less than or equal to `tid` are removed.
 *)
Definition safe_rm_verchain (tid : u64) (versL versL' : list (u64 * u64 * u64)) : iProp Σ :=
  ⌜sublist versL' versL⌝ ∗
  [∗ list] ver ∈ versL, ⌜int.Z ver.1.2 > (int.Z tid) → ver ∈ versL'⌝.

(*****************************************************************)
(* func (tuple *Tuple) RemoveVersions(tid uint64)                *)
(*****************************************************************)
Theorem wp_tuple__RemoveVersions tuple (tid : u64) (key : u64) versL γ :
  is_tuple tuple key γ -∗
  {{{ own_versL γ versL }}}
    Tuple__RemoveVersions #tuple #tid
  {{{ b, RET #b; ∃ versL', own_versL γ versL' ∗ (safe_rm_verchain tid versL versL') }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "HversLU HΦ".
  rename versL into versL'.
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
                (tuple ↦[Tuple :: "vers"] to_val vers) ∗
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
    destruct (list_lookup_lt _ (ver_to_val <$> versL) (int.nat idx)) as [ver HSome].
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
    iSplit.
    { iPureIntro.
      word.
    }
    { replace (int.nat (word.add idx _)) with (S (int.nat idx)); last word.
      apply list_lookup_fmap_inv in HSome as (y & Heq & HSome).
      rewrite (take_S_r _ _ y); last apply HSome.
      iApply (big_sepL_app).
      iSplit; first done.
      iApply (big_sepL_singleton).
      iPureIntro.
      apply Znot_lt_ge in Heqb0.
      inversion Heq.
      rewrite H1 in Heqb0.
      (* Q: Why can't lia solve this... *)
      rewrite -Z.ge_le_iff.
      apply Heqb0.
    }
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
  iDestruct (ghost_var_agree with "HversLU HversLI") as %->.
  iMod (ghost_var_update_halves (drop (int.nat idx) versL) with "HversLU HversLI") as "[HversLU HversLI]".
  wp_apply (release_spec with "[-HidxOrder HversLU HΦ]").
  { eauto 10 with iFrame. }
  wp_pures.
  iApply "HΦ".
  iModIntro.
  iExists _.
  iFrame.
  rewrite /safe_rm_verchain.
  iSplit.
  { iPureIntro. apply sublist_drop. }
  replace versL with (take (int.nat idx) versL ++ drop (int.nat idx) versL) at 2 by apply take_drop.
  iApply (big_sepL_app).
  iSplit.
  { (* Versions in the removed part have their end timestamps less than or equal `tid`. *)
    iRevert "HidxOrder".
    iPureIntro.
    intros H i ver HSome Hgt.
    apply H in HSome.
    lia.
  }
  { (* Versions in the remaining part are in the old list. *)
    iPureIntro.
    intros i ver HSome _.
    by apply elem_of_list_lookup_2 in HSome.
  }
Qed.

(*****************************************************************)
(* func MkTuple() *Tuple                                         *)
(*****************************************************************)
Theorem wp_MkTuple (key : u64):
  {{{ True }}}
    MkTuple #()
  {{{ (t : loc) γ, RET #t;
         is_tuple t key γ ∗
         own_versL γ []
  }}}.
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
  iMod (ghost_var_alloc ([] : list (u64 * u64 * u64))) as (tuple_vers_gn) "[HversLI HversLU]".
  set γ := {| tuple_vers_gn := tuple_vers_gn |}.
  iMod (alloc_lock mvccN _ latch (own_tuple tuple key γ) with "[$Hfree] [-latch rcond HversLU HΦ]") as "#Hlock".
  { eauto 10 with iFrame. }
  iApply ("HΦ" $! _ γ).
  iSplitR "HversLU"; auto.
  iExists latch, rcond.
  iMod (readonly_alloc_1 with "latch") as "$".
  iMod (readonly_alloc_1 with "rcond") as "$".
  iFrame "#".
  done.
Qed.

End heap.
