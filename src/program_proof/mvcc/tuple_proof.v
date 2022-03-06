(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export disk_prelude.
(* Import Coq model of our Goose program.*)
From Goose.github_com.mit_pdos.go_mvcc Require Import tuple.
From Perennial.program_proof.mvcc Require Import mvcc_ghost.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition TID_SENTINEL := (U64 18446744073709551615).
Definition RET_SUCCESS := (U64 0).
Definition RET_NONEXIST := (U64 1).
Definition RET_RETRY := (U64 100).
Definition RET_UNSERIALIZABLE := (U64 200).

Definition pver := (u64 * bool * u64)%type.

(* TODO: rename to [pver_to_val]. *)
Definition ver_to_val (x : pver) :=
  (#x.1.1, (#x.1.2, (#x.2, #())))%V.

(*
Definition match_ver (tid : u64) (ver : u64 * u64 * u64) :=
  int.Z ver.1.1 < int.Z tid ≤ int.Z ver.1.2.

Definition no_match_vers tid versL :=
  Forall (λ ver, ¬(match_ver tid ver)) versL.

Definition pver_abs_present tid (vchain : list (option u64)) ver :=
  match_ver tid ver -> vchain !! (int.nat tid) = Some (Some ver.2).

Definition pvers_abs_present tid vchain pvers verlast :=
  (Forall (λ ver, pver_abs_present tid vchain ver)) pvers ∧ (pver_abs_present tid vchain verlast).

Definition pvers_abs_absent tid (vchain : list (option u64)) (tidlast : u64) pvers verlast :=
  int.Z tid ≤ int.Z tidlast ->
  no_match_vers tid pvers  ->
  no_match_vers tid [verlast] ->
  vchain !! (int.nat tid) = Some None.

Definition tuple_abs (tid : u64) (vchain : list (option u64)) (tidlast : u64) (verlast : u64 * u64 * u64) (versL : list (u64 * u64 * u64)) :=
  let verlast' := if decide (verlast.1.2 = TID_SENTINEL)
                  then (verlast.1.1, tidlast, verlast.2)
                  else verlast in
  pvers_abs_present tid vchain versL verlast' ∧
  pvers_abs_absent tid vchain tidlast versL verlast'.
*)

Definition spec_find_ver_step (tid : u64) (res : option pver) (ver : pver) : option pver :=
  match res with
  | Some x => Some x
  | None => if decide (int.Z tid > int.Z ver.1.1) then Some ver else None
  end.

Definition spec_find_ver_reverse (vers : list pver) (tid : u64) : option pver :=
  foldl (spec_find_ver_step tid) None vers.

Definition spec_find_ver (vers : list pver) (tid : u64) : option pver :=
  spec_find_ver_reverse (reverse vers) tid.

(* TODO: Renmae to [spec_lookup]. *)
Definition spec_lookup' (vers : list pver) (tid : u64) : dbval :=
  match (spec_find_ver vers tid) with
  | Some ver => if ver.1.2 then Nil else Value ver.2
  | None => Nil
  end.

Definition tuple_wellformed (vers : list pver) (tidlast : u64) : iProp Σ :=
  "%HtidlastGe" ∷ ⌜Forall (λ ver, int.Z ver.1.1 ≤ int.Z tidlast) vers⌝ ∗
  (* TODO: restrict tid ≥ tidgc *)
  "%HexistsLt" ∷ ⌜∀ (tid : u64), Exists (λ ver, int.Z ver.1.1 < int.Z tid) vers⌝.

Definition own_tuple (tuple : loc) (key : u64) (tidown tidlast : u64) versL (γ : mvcc_names) : iProp Σ :=
  ∃ (vers : Slice.t) (tidlbN : nat) (vchain : list dbval),
    "Htidown" ∷ tuple ↦[Tuple :: "tidown"] #tidown ∗
    "Htidlast" ∷ tuple ↦[Tuple :: "tidlast"] #tidlast ∗
    "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val vers) ∗
    "HversL" ∷ slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL) ∗
    "HtidlbN" ∷  min_tid_lb γ tidlbN ∗
    "%HtupleAbs" ∷ (∀ tid, ⌜int.Z tid ≤ int.Z tidlast -> vchain !! (int.nat tid) = Some (spec_lookup' versL tid)⌝) ∗
    (* TODO: The lock invariant should only own [1/2] of [vchain]. *)
    "Hvchain" ∷ vchain_ptsto γ (if decide (tidown = (U64 0)) then (1) else (1/4))%Qp key vchain ∗
    "%HvchainLen" ∷ ⌜(Z.of_nat (length vchain)) = ((int.Z tidlast) + 1)%Z⌝ ∗
    "Hwellformed" ∷ tuple_wellformed versL tidlast ∗
    (*
    "HtupleAbs" ∷ ∀ tid, ⌜tidlbN ≤ int.nat tid -> (tuple_abs vchain tidlast verlast versL tid)⌝ ∗
     *)
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (own_tuple _ _ _ _ _ _)) => unfold own_tuple : core.

Definition is_tuple (tuple : loc) (key : u64) (γ : mvcc_names) : iProp Σ :=
  ∃ (latch : loc) (rcond : loc),
    "#Hlatch" ∷ readonly (tuple ↦[Tuple :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (∃ tidown tidlast versL, own_tuple tuple key tidown tidlast versL γ) ∗
    "#Hrcond" ∷ readonly (tuple ↦[Tuple :: "rcond"] #rcond) ∗
    "#HrcondC" ∷ is_cond rcond #latch ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (is_tuple _ _ _)) => unfold is_tuple : core.

Lemma val_to_ver_with_lookup (x : val) (l : list (u64 * bool * u64)) (i : nat) :
  (ver_to_val <$> l) !! i = Some x ->
  (∃ (b : u64) (d : bool) (v : u64), x = ver_to_val (b, d, v) ∧ l !! i = Some (b, d, v)).
Proof.
  intros H.
  apply list_lookup_fmap_inv in H as [[[y1 y2] y3] [Heq Hsome]].
  naive_solver.
Qed.

(* TODO: Rename lemma names. *)

Local Lemma spec_lookup_reverse_Some vers tid ver :
  foldl (spec_find_ver_step tid) (Some ver) vers = Some ver.
Proof.
  induction vers; done.
Qed.

Local Lemma spec_find_ver_lt_Some (vers : list pver) (tid : u64) (ver : pver) :
  ver ∈ vers ->
  int.Z ver.1.1 < int.Z tid ->
  ∃ ver', spec_find_ver vers tid = Some ver'.
Proof.
  intros Hin Hlt.
  apply elem_of_reverse, elem_of_list_lookup_1 in Hin as [idx Hlookup].
  unfold spec_find_ver, spec_find_ver_reverse.
  rewrite -(take_drop_middle _ _ _ Hlookup).
  rewrite foldl_app.
  destruct (foldl _ None _) as [ver' |].
  - exists ver'.
    by rewrite spec_lookup_reverse_Some.
  - exists ver.
    simpl.
    case_decide; last word.
    by rewrite  spec_lookup_reverse_Some.
Qed.  

Local Lemma spec_lookup_reverse_match vers tid :
  ∀ vers_take vers_drop ver,
    vers_take ++ ver :: vers_drop = vers ->
    spec_find_ver_reverse vers_take tid = None ->
    (int.Z tid > int.Z ver.1.1) ->
    spec_find_ver_reverse vers tid = Some ver.
Proof.
  intros vers_take vers_drop ver Hvers Htake Hver.
  rewrite -Hvers.
  unfold spec_find_ver_reverse in *.
  rewrite foldl_app.
  rewrite Htake.
  simpl.
  case_decide.
  - induction vers_drop.
    + done.
    + by rewrite spec_lookup_reverse_Some.
  - contradiction.
Qed.

Local Lemma spec_lookup_reverse_not_match vers tid :
  ∀ vers_take ver,
    vers_take ++ [ver] = vers ->
    spec_find_ver_reverse vers_take tid = None ->
    (int.Z tid ≤ int.Z ver.1.1) ->
    spec_find_ver_reverse vers tid = None.
Proof.
  intros vers_take ver Hvers Htake Hver.
  rewrite -Hvers.
  unfold spec_find_ver_reverse in *.
  rewrite foldl_app.
  rewrite Htake.
  simpl.
  case_decide.
  - contradiction.
  - done.
Qed.

Local Lemma spec_lookup_extended vers (tidlast tid1 tid2 : u64) :
  int.Z tidlast < int.Z tid1 ->
  int.Z tidlast < int.Z tid2 ->
  Forall (λ ver, int.Z ver.1.1 ≤ int.Z tidlast) vers ->
  spec_find_ver vers tid1 = spec_find_ver vers tid2.
Proof.
  intros Htid1 Htid2 Hwellformed.
  unfold spec_find_ver.
  unfold spec_find_ver_reverse.
  destruct (reverse _) eqn:E; first done.
  simpl.
  setoid_rewrite Forall_forall in Hwellformed.
  assert (H : p ∈ vers).
  { apply elem_of_reverse. rewrite E. apply elem_of_list_here. }
  assert (H1 : int.Z p.1.1 < int.Z tid1).
  { apply Hwellformed in H. apply Z.le_lt_trans with (int.Z tidlast); done. }
  assert (H2 : int.Z p.1.1 < int.Z tid2).
  { apply Hwellformed in H. apply Z.le_lt_trans with (int.Z tidlast); done. }
  apply Z.lt_gt in H1, H2.
  do 2 (case_decide; last contradiction).
  by do 2 rewrite spec_lookup_reverse_Some.
Qed.
  
(*******************************************************************)
(* func findRightVer(tid uint64, vers []Version) Version           *)
(*******************************************************************)
Local Theorem wp_findRightVer (tid : u64) (vers : Slice.t)
                              (versL : list (u64 * bool * u64)) :
  {{{ ⌜∃ (ver : pver), (ver ∈ versL) ∧ (int.Z ver.1.1 < int.Z tid)⌝ ∗
      slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL)
  }}}
    findRightVer #tid (to_val vers)
  {{{ (ver : pver), RET (ver_to_val ver);
      ⌜spec_find_ver versL tid = Some ver⌝ ∗
      slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL)
  }}}.
Proof.
  iIntros (Φ) "[%Hlt HversL] HΦ".
  destruct Hlt as [ver'' [Hin Hlt]].
  destruct (nil_or_length_pos versL) as [| Hnonempty].
  { rewrite H in Hin. by destruct (not_elem_of_nil ver''). }
  iDestruct (slice.is_slice_small_acc with "HversL") as "[HversL HversL_close]".
  iDestruct (is_slice_small_sz with "HversL") as "%HversLen".
  rewrite fmap_length in HversLen.
  wp_call.
  
  (***********************************************************)
  (* var ver Version                                         *)
  (* length := uint64(len(vers))                             *)
  (* var idx uint64 = 0                                      *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first auto.
  iIntros (verR) "HverR".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_ref_to); first auto.
  iIntros (idxR) "HidxR".
  wp_pures.

  (***********************************************************)
  (* for {                                                   *)
  (*     if idx >= length {                                  *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     ver = vers[length - (1 + idx)]                      *)
  (*     if tid > ver.begin {                                *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     idx++                                               *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (∃ (ver : u64 * bool * u64) (idx : u64),
             "HverR" ∷ (verR ↦[struct.t Version] ver_to_val ver) ∗
             "HidxR" ∷ (idxR ↦[uint64T] #idx) ∗
             "HversL" ∷ is_slice_small vers (struct.t Version) 1 (ver_to_val <$> versL) ∗
             (* "%Hlookup" ∷ (⌜reverse versL !! (int.nat idx) = Some ver⌝) ∗ *)
             "%Hspec" ∷ if b
                        then ⌜spec_find_ver_reverse (take (int.nat idx) (reverse versL)) tid = None⌝
                        else ⌜spec_find_ver_reverse (reverse versL) tid = Some ver⌝)%I.
  wp_apply (wp_forBreak P with "[] [-HΦ HversL_close]").
  { (* Loop body. *)
    clear Φ.
    iIntros (Φ).
    iModIntro.
    iIntros "Hloop HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.
    wp_pures.
    wp_if_destruct.
    { (* Exceeding the bound. *)
      iModIntro.
      iApply "HΦ".
      unfold P.
      replace (take (int.nat idx) _) with (reverse versL) in Hspec; last first.
      { symmetry.
        pose proof (reverse_length versL) as HversRevLen.
        rewrite take_ge; first done.
        rewrite HversRevLen HversLen.
        word.
      }
      destruct (spec_find_ver_lt_Some _ _ _ Hin Hlt).
      unfold spec_find_ver in H.
      by rewrite H in Hspec.
    }
    wp_load.
    wp_pures.
    
    apply Znot_le_gt in Heqb.
    destruct (list_lookup_lt _ versL (length versL - S (int.nat idx))%nat) as [ver' Hver']; first word.
    wp_apply (wp_SliceGet with "[HversL]").
    { iFrame.
      iPureIntro.
      set x := vers.(Slice.sz).
      (**
       * Notes on rewriting between [word.sub] and [Z.sub].
       * 1. In general, to rewrite from [int.Z (word.sub x y)] to [int.Z x - int.Z y],
       * we need to have [int.Z x ≥ int.Z y] in the context.
       * 2. For nested [word.sub], e.g., [int.Z (word.sub (word.sub x y) z)], we can
       * first prove that [int.Z (word.sub x y) ≥ int.Z z], and then replace
       * [int.Z (word.sub (word.sub x y) z)] with [int.Z x - int.Z y - int.Z z].
       *)
      assert (H : Z.ge (int.Z (word.sub x idx)) 1).
      { subst x. word. }
      replace (int.Z (word.sub _ (U64 1))) with (int.Z vers.(Slice.sz) - int.Z idx - 1); last first.
      { subst x. word. }
      replace (Z.to_nat _) with ((length versL) - (S (int.nat idx)))%nat; last first.
      { rewrite HversLen. word. }
      rewrite list_lookup_fmap.
      rewrite Hver'.
      by apply fmap_Some_2.
    }
    iIntros "[HversL %Hvalty]".
    wp_store.
    wp_load.
    wp_pures.
    wp_if_destruct.
    { iModIntro.
      iApply "HΦ".
      unfold P.
      do 2 iExists _.
      iFrame "∗ %".
      iPureIntro.
      rewrite -reverse_lookup in Hver'; last first.
      { rewrite HversLen. word. }
      apply take_drop_middle in Hver'.
      apply (spec_lookup_reverse_match _ _ _ _ _ Hver'); [done | word].
    }
    wp_load.
    wp_store.
    iModIntro.
    iApply "HΦ".
    unfold P.
    do 2 iExists _.
    iFrame.
    iPureIntro.
    replace (int.nat (word.add _ _)) with (S (int.nat idx)); last word.
    rewrite -reverse_lookup in Hver'; last first.
    { rewrite HversLen. word. }
    rewrite (take_S_r _ _ ver'); last done.
    set vers_take := take _ _.
    set versL' := vers_take ++ _.
    apply Znot_lt_ge in Heqb0.
    apply (spec_lookup_reverse_not_match versL' _ vers_take ver'); [auto | auto | word].
  }
  { (* Loop entry. *)
    unfold P.
    iExists (U64 0, false, U64 0).
    iExists _.
    iFrame.
    iPureIntro.
    change (int.nat 0) with 0%nat.
    rewrite take_0.
    split; auto.
  }
  iIntros "Hloop".
  iNamed "Hloop".
  wp_pures.
  
  (***********************************************************)
  (* return ver                                              *)
  (***********************************************************)
  wp_load.
  iApply "HΦ".
  iDestruct ("HversL_close" with "HversL") as "HversL".
  by iFrame.
Qed.

(**
 * 1. [view_ptsto] in the postcondition can be obtained by applying
 *    the invariant between the logical and physical version chains to
 *    reading a physical verison.
 * 2. However, when GC is involved, the invariant should hold only for
 *    those physical versions created after a certain tid (the
 *    [tidlbN] in [own_tuple]).
 *    Thus, we need a proof of [(int.nat tid) ≥ tidlbN] in order to
 *    apply the invariant, which can be proved by:
 *    - [active_tid γ tid] in the precondition.
 *    - [min_tid_lb γ tidlbN] in the lock invariant.
 *)
Definition post_tuple__ReadVersion tid key val (ret : u64) γ : iProp Σ :=
  active_tid γ tid ∗
  match int.Z ret with
  | 0 => view_ptsto γ key (Value val) tid
  | 1 => view_ptsto γ key Nil tid
  | _ => False
  end.

(* Q: Existing tactic does this? *)
Local Lemma ite_apply (A B : Type) (b : bool) (f : A -> B) x y :
  (if b then f x else f y) = f (if b then x else y).
Proof.
  destruct b; done.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) ReadVersion(tid uint64) (uint64, uint64)  *)
(*****************************************************************)
Theorem wp_tuple__ReadVersion tuple (tid : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid }}}
    Tuple__ReadVersion #tuple #tid
  {{{ (val : u64) (ret : u64), RET (#val, #ret); post_tuple__ReadVersion tid key val ret γ }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Hactive HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iNamed "HtupleOwn".
  wp_pures.

  (***********************************************************)
  (* for tid > tuple.tidlast && tuple.tidown != 0 {          *)
  (*     tuple.rcond.Wait()                                  *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (∃ (tidown tidlast : u64) (versL : list (u64 * bool * u64)),
             "HtupleOwn" ∷ own_tuple tuple key tidown tidlast versL γ ∗
             "Hlocked" ∷ locked #latch ∗
             "%Hexit" ∷ if b then ⌜True⌝ else ⌜(int.Z tid) ≤ (int.Z tidlast) ∨ (int.Z tidown) = 0⌝)%I.
  wp_apply (wp_forBreak_cond P with "[] [-HΦ Hactive]").
  { (* Loop body preserves the invariant. *)
    clear Φ HtupleAbs HvchainLen.
    clear tidown tidlast versL.
    iIntros (Φ) "!> Hloop HΦ".
    iNamed "Hloop".
    iNamed "HtupleOwn".
    wp_pures.
    wp_loadField.
    wp_pures.
    (**
     * Directly applying [wp_and] seems to bind the wrong [if].
     * Reason: Goose generate a similar form for loops with conds and
     * logical ands.
     * Solution here is using [wp_bind] to focus on the right [if]:
     * [wp_bind (If #(bool_decide _) _ _)].
     *)
    wp_bind (If #(bool_decide _) _ _).
    wp_apply (wp_and with "Htidown").
    { (* Case: [tid > tidlast]. *)
      wp_pures. done.
    }
    { (* Case: [tuple.tidown ≠ 0]. *)
      iIntros "_ Htidown".
      wp_loadField.
      wp_pures.
      rewrite -bool_decide_not.
      eauto with iFrame.
    }
    iIntros "Htidown".
    wp_if_destruct.
    { (* Loop body. *)
      wp_pures.
      wp_loadField.
      wp_apply (wp_condWait with "[-HΦ]").
      { eauto 15 with iFrame. }
      iIntros "[Hlocked HtupleOwn]".
      iNamed "HtupleOwn".
      wp_pures.
      iModIntro.
      iApply "HΦ".
      unfold P.
      eauto 15 with iFrame.
    }
    (* Exiting loop. *)
    iApply "HΦ".
    apply not_and_l in Heqb.
    destruct Heqb; (iModIntro; do 3 iExists _; iFrame "Hlocked").
    { (* Case [verLast.begin ≥ tid]. *)
      iSplitR ""; first eauto 10 with iFrame.
      iPureIntro.
      left. word.
    }
    { (* Case [tuple.tidown = 0]. *)
      iSplitR ""; first eauto 10 with iFrame.
      iPureIntro.
      right.
      apply dec_stable in H.
      by inversion H.
    }
  }
  { (* The invariant holds at the start. *)
    unfold P.
    eauto 10 with iFrame.
  }
  clear HtupleAbs HvchainLen.
  clear tidown tidlast versL vchain.
  iIntros "Hloop".
  iNamed "Hloop".
  iNamed "HtupleOwn".
  iNamed "Hwellformed".
  wp_pures.

  (***********************************************************)
  (* ver := findRightVer(tid, tuple.vers)                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_findRightVer with "[$HversL]").
  { iPureIntro. by setoid_rewrite Exists_exists in HexistsLt. }
  iIntros (ver) "[%Hspec HversL]".
  wp_pures.

  (***********************************************************)
  (* var ret uint64                                          *)
  (* if ver.deleted {                                        *)
  (*     ret = common.RET_NONEXIST                           *)
  (* } else {                                                *)
  (*     ret = common.RET_SUCCESS                            *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (retR) "HretR".
  wp_pures.
  (* Q: Need to do this in order to use [case_bool_decide]. Why doesn't [destruct] work? *)
  replace ver.1.2 with (bool_decide (ver.1.2 = true)); last first.
  { case_bool_decide.
    - done.
    - by apply not_true_is_false in H.
  }
  wp_apply (wp_If_join_evar with "[HretR]").
  { iIntros (b') "%Eb'".
    (* XXX: destruct ver.1.2. *)
    case_bool_decide.
    - wp_if_true.
      wp_store.
      iModIntro.
      iSplit; first done.
      replace #1 with #(if b' then 1 else 0) by by rewrite Eb'.
      iNamedAccu.
    - wp_if_false.
      wp_store.
      iModIntro.
      iSplit; first done.
      by rewrite Eb'.
  }
  iIntros "H".
  iNamed "H".
  wp_pures.
  
  (***********************************************************)
  (* if tuple.tidlast < tid {                                *)
  (*     tuple.tidlast = tid                                 *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_If_join_evar with "[Htidlast]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    { (* Case [tuple.tidlast < tid]. *)
      wp_if_true.
      wp_storeField.
      iSplit; first done.
      (* Update "Htidrd" to use `b'` for merging states. See comments of wp_If_join_evar in control.v. *)
      replace #tid with #(if b' then tid else tidlast) by by rewrite Eb'.
      iNamedAccu.
    }
    { (* Case [tuple.tidlast ≥ tid]. *)
      wp_if_false.
      iModIntro.
      rewrite Eb'.
      by iFrame.
    }
  }
  iIntros "H".
  iNamed "H".
  wp_pures.

  set q := if decide (tidown = 0) then _ else _.
  repeat rewrite ite_apply.
  set tidlast' := if bool_decide _ then tid else tidlast.
  clear P.
  set P := (|==> ∃ (vchain : list (option u64)),
    "Hvchain" ∷ vchain_ptsto γ q key vchain ∗
    "#HvchainW" ∷ vchain_lb γ key vchain ∗
    "%HvchainLen" ∷ ⌜Z.of_nat (length vchain) = (int.Z tidlast' + 1)%Z⌝ ∗
    "%Hwellformed" ∷ tuple_wellformed versL tidlast' ∗
    "%HtupleAbs" ∷ (∀ tid, ⌜int.Z tid ≤ int.Z tidlast' -> vchain !! (int.nat tid) = Some (spec_lookup' versL tid)⌝))%I.
  iAssert P with "[Hvchain]" as "H".
  { unfold P.
    subst q.
    case_decide.
    - (* Case 1. [tidown = 0]. *)
      subst tidlast'.
      case_bool_decide.
      + (* Case 1a. [tidlast < tid]. Extending the version chain. *)
        set valtid := (if ver.1.2 then Nil else Value ver.2).
        set vals := replicate (int.nat (int.Z tid - int.Z tidlast)) valtid.
        set vchain' := vchain ++ vals.
        iExists vchain'.
        iMod (vchain_update vchain' with "Hvchain") as "Hvchain"; first by apply prefix_app_r.
        iDestruct (vchain_witness with "Hvchain") as "#HvchainW".
        iFrame "Hvchain HvchainW".
        iPureIntro.
        split.
        { (* Prove [HvchainLen]. *)
          subst vchain'.
          rewrite app_length.
          (* Set Printing Coercions. *)
          (* Q: weird that cannot simply [by word]. *)
          assert (Hxy : ∀ (x y : nat), Z.of_nat x + Z.of_nat y = Z.of_nat (x + y)) by word.
          replace (Z.of_nat _) with ((Z.of_nat (length vchain)) + (Z.of_nat (length vals))) by apply Hxy.
          rewrite HvchainLen.
          subst vals.
          rewrite replicate_length.
          replace (Z.of_nat _) with ((int.Z tid) - (int.Z tidlast)) by word.
          word.
        }
        split.
        { (* Prove [Hwellformed]. *)
          split; last done.
          apply (Forall_impl _ _ _ HtidlastGe).
          word.
        }
        { (* Prove [HtupleAbs]. *)
          intros x Hbound.
          destruct (decide (int.Z x ≤ int.Z tidlast)); subst vchain'.
          * (* [x ≤ tidlast]. *)
            rewrite lookup_app_l; last word.
            by apply HtupleAbs.
          * (* [tidlast < x]. *)
            rename n into HxLower.
            apply Znot_le_gt in HxLower.
            rewrite lookup_app_r; last word.
            subst vals.
            rewrite lookup_replicate_2; last word.
            f_equal.
            subst valtid.
            unfold spec_lookup'.
            rewrite (spec_lookup_extended _ tidlast x tid); auto using Z.gt_lt.
            by rewrite Hspec.
        }
      + (* Case 1b. [tidlast ≥ tid]. *)
        iExists vchain.
        iDestruct (vchain_witness with "Hvchain") as "#HvchainW".
        iFrame "Hvchain HvchainW".
        iPureIntro.
        apply Znot_lt_ge in H0.
        apply Z.ge_le in H0.
        do 2 (split; first auto).
        by apply HtupleAbs.
    - (* Case 2. [tidown ≠ 0]. *)
      iExists vchain.
      iDestruct (vchain_witness with "Hvchain") as "#HvchainW".
      iFrame "Hvchain HvchainW".
      iPureIntro.
      destruct Hexit; last first.
      { assert (contra : tidown = U64 0) by word.
        contradiction.
      }
      replace tidlast' with tidlast; last first.
      { subst tidlast'.
        case_bool_decide.
        - apply Zle_not_gt in H0.
          apply Z.lt_gt in H1.
          contradiction.
        - done.
      }
      auto.
  }

  clear HtupleAbs HvchainLen vchain.
  iMod "H".
  iNamed "H".
  clear P.

  iAssert (⌜vchain !! int.nat tid = Some (spec_lookup' versL tid)⌝)%I as "%Hlookup".
  { subst tidlast'.
    case_bool_decide; iPureIntro.
    - by apply HtupleAbs.
    - apply Znot_lt_ge, Z.ge_le in H. by apply HtupleAbs.
  }
  
  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hactive HretR]").
  { iFrame "Hlocked Hlock".
    iNext.
    do 3 iExists _.
    do 2 iExists _.
    iExists vchain.
    by iFrame.
  }
  wp_pures.
  
  (***********************************************************)
  (* return val, ret                                         *)
  (***********************************************************)
  (* Set Printing Coercions. *)
  wp_load.
  wp_pures.
  iApply "HΦ".
  iModIntro.
  unfold post_tuple__ReadVersion.
  iFrame "Hactive".
  case_bool_decide.
  { (* Case: [ret = RET_NONEXIST]. *)
    change (int.Z 1) with 1.
    simpl.
    (* Prove [view_ptsto]. *)
    unfold view_ptsto.
    iExists _.
    iFrame "HvchainW".
    iPureIntro.
    rewrite Hlookup.
    unfold spec_lookup'.
    by rewrite Hspec H.
  }
  { (* Case: [ret = RET_SUCCESS]. *)
    change (int.Z 0) with 0.
    simpl.
    (* Prove [view_ptsto]. *)
    unfold view_ptsto.
    apply not_true_is_false in H.
    iExists _.
    iFrame "HvchainW".
    iPureIntro.
    rewrite Hlookup.
    unfold spec_lookup'.
    by rewrite Hspec H.
  }
Qed.

Definition post_tuple__appendVersion tuple tid val key verlast versL γ : iProp Σ :=
  let tidown' := (U64 0) in
  let tidlast' := tid in
  let verslast' := (tid, TID_SENTINEL, val) in
  let end' := if decide (verlast.1.2 = TID_SENTINEL) then tid else verlast.1.2 in
  let versL' := versL ++ [(verlast.1.1, end', verlast.2)] in
  own_tuple tuple key tidown' tidlast' verslast' versL' γ.

(*****************************************************************)
(* func (tuple *Tuple) appendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__appendVersion tuple (tid : u64) (val : u64) (key : u64) tidown tidlast verlast versL γ :
  {{{ own_tuple tuple key tidown tidlast verlast versL γ }}}
    Tuple__appendVersion #tuple #tid #val
  {{{ RET #(); post_tuple__appendVersion tuple tid val key verlast versL γ }}}.
Proof.
  iIntros (Φ) "HtupleOwn HΦ".
  iNamed "HtupleOwn".
  wp_call.

  (***********************************************************)
  (* var verLast Version                                     *)
  (* verLast = tuple.verlast                                 *)
  (* if verLast.end == config.TID_SENTINEL {                 *)
  (*     verLast.end = tid                                   *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (verLastRef) "HverLastRef".
  wp_pures.
  wp_loadField.
  wp_store.
  wp_load.
  change (uint64T * _)%ht with (struct.t Version).
  rewrite struct_fields_split.
  iNamed "HverLastRef".
  wp_apply (wp_If_join_evar with "[-HΦ]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    - wp_if_true.
      wp_storeField.
      iSplit; first done.
      replace #tid with #(if b' then tid else verlast.1.2); last by by rewrite Eb'.
      (* replace tid with (if b' then tid else verlast.1.2); last by by rewrite Eb'. *)
      (* Q: What's the @ in the goal? *)
      iNamedAccu.
    - wp_if_false.
      rewrite Eb'.
      iFrame.
      by iFrame.
  }
  iIntros "H".
  iNamed "H".
  wp_pures.
  set b := bool_decide _.
  set verlast' := (verlast.1.1, (if b then tid else verlast.1.2), verlast.2).
  (* Group struct-field points-to to struct points-to. *)
  iAssert (verLastRef ↦[struct.t Version] (ver_to_val verlast'))%I with "[begin end val]" as "HverLastRef".
  { rewrite struct_fields_split. iFrame. destruct b; eauto. }
  
  (***********************************************************)
  (* tuple.vers = append(tuple.vers, verLast)                *)
  (***********************************************************)
  wp_load.
  wp_loadField.
  wp_apply (wp_SliceAppend' with "[HversL]"); [done | auto | auto |].
  iIntros (vers') "HversL".
  wp_storeField.

  (***********************************************************)
  (* verNext := Version{                                     *)
  (*     begin   : tid,                                      *)
  (*     end     : config.TID_SENTINEL,                      *)
  (*     val     : val,                                      *)
  (* }                                                       *)
  (* tuple.verlast = verNext                                 *)
  (***********************************************************)
  wp_pures.
  wp_storeField.

  (***********************************************************)
  (* tuple.tidown = 0                                        *)
  (* tuple.tidlast = tid                                     *)
  (***********************************************************)
  do 2 wp_storeField.

  iModIntro.
  iApply "HΦ".
  unfold post_tuple__appendVersion.
  do 3 iExists _.
  unfold named.
  iExactEq "HversL".
  rewrite fmap_app.
  do 2 f_equal.
  simpl.
  do 4 f_equal.
  subst b.
  (* Q: Is there an easier way of proving [if a then x else y = if b then x else y] by proving [a = b]? *)
  case_bool_decide.
  - inversion H. by rewrite H1.
  - rewrite decide_bool_decide.
    case_bool_decide.
    + rewrite H0 in H. unfold TID_SENTINEL in H. congruence.
    + done.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) AppendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__AppendVersion tuple (tid : u64) (val : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ True }}}
    Tuple__AppendVersion #tuple #tid #val
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
  iIntros "[Hlocked HtupleOwn]".
  iDestruct "HtupleOwn" as (tidown tidlast verlast versL) "HtupleOwn".
  wp_pures.
  
  (***********************************************************)
  (* tuple.appendVersion(tid, val)                           *)
  (***********************************************************)
  wp_apply (wp_tuple__appendVersion with "[$HtupleOwn]"); first eauto 10 with iFrame.
  iIntros "HtupleOwn".
  wp_pures.
  
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
  unfold post_tuple__appendVersion.
  wp_apply (release_spec with "[-HΦ]"); first eauto 10 with iFrame.
  wp_pures.
  by iApply "HΦ".
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
  iIntros "[Hlocked HtupleOwn]".
  iNamed "HtupleOwn".
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
  { eauto 15 with iFrame. }
  wp_pures.
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func (tuple *Tuple) Own(tid uint64) bool                      *)
(*****************************************************************)
Theorem wp_tuple__Own tuple (tid : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ True }}}
    Tuple__Own #tuple #tid
  {{{ (b : bool), RET #b; if b
                        then mods_token γ key tid
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
  iIntros "[Hlocked HtupleOwn]".
  iNamed "HtupleOwn".
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
    { eauto 15 with iFrame. }
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
    { eauto 15 with iFrame. }
    wp_pures.
    by iApply "HΦ".
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
  { eauto 15 with iFrame. }
  wp_pures.
  iModIntro.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iApply "HΦ".
  admit. (* TODO: prove mods_token *)
Admitted.

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
Definition safe_rm_verchain (tid : u64) (versL versL' : list (u64 * u64 * u64)) :=
  (sublist versL' versL) ∧
  (Forall (fun ver => int.Z ver.1.2 > (int.Z tid) -> ver ∈ versL')) versL.
  
(*****************************************************************)
(* func (tuple *Tuple) removeVersions(tid uint64)                *)
(*****************************************************************)
Theorem wp_tuple__removeVersions tuple (tid : u64) (key : u64) versL γ :
  {{{ own_tuple tuple key versL γ }}}
    Tuple__removeVersions #tuple #tid
  {{{ RET #(); ∃ versL', (own_tuple tuple key versL' γ) ∗ ⌜(safe_rm_verchain tid versL versL')⌝ }}}.
Proof.
  iIntros (Φ) "HtupleOwn HΦ".
  iNamed "HtupleOwn".
  wp_call.

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
  iDestruct "Hidx" as (idx) "(HidxR & %Hbound & %HidxOrder)".
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

  iApply "HΦ".
  iModIntro.
  set versL' := drop (int.nat idx) versL.
  iExists versL'.
  iSplit; first eauto 10 with iFrame.
  iPureIntro.
  
  (**
   * Proving the postcondition.
   *)
  split; first apply sublist_drop.
  replace versL with (take (int.nat idx) versL ++ drop (int.nat idx) versL) by apply take_drop.
  apply Forall_app.
  split; apply Forall_forall.
  { (* Versions in the removed part have their end timestamps less than or equal `tid`. *)
    intros ver Hin Hgt.
    apply elem_of_list_lookup_1 in Hin as [i HSome].
    apply HidxOrder in HSome.
    lia.
  }
  { (* Versions in the remaining part are in the old list. *)
    intros ver Hin _.
    apply elem_of_list_lookup_1 in Hin as [i HSome].
    by apply elem_of_list_lookup_2 in HSome.
  }
Qed.

(*****************************************************************)
(* func (tuple *Tuple) RemoveVersions(tid uint64)                *)
(*                                                               *)
(* Notes:                                                        *)
(* 1. This method keeps all versions ending after [tid].         *)
(* 2. The precondition says that [tid] is less than or equal to  *)
(*    a lower bound of the minimal active tid.                   *)
(* 3. Call [txnMgr.getMinActiveTID] before calling this method.  *)
(*****************************************************************)
Theorem wp_tuple__RemoveVersions tuple (tid : u64) (key : u64) (tidlbN : nat) γ :
  is_tuple tuple key γ -∗
  {{{ min_tid_lb γ tidlbN ∗ ⌜(int.nat tid ≤ tidlbN)%nat⌝ }}}
    Tuple__RemoveVersions #tuple #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> [HtidlbN %HtidN] HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iDestruct "HtupleOwn" as (versL) "HtupleOwn".
  wp_pures.

  (***********************************************************)
  (* tuple.removeVersions(tid)                               *)
  (***********************************************************)
  wp_apply (wp_tuple__removeVersions with "HtupleOwn").
  iIntros "HtupleOwn".
  iDestruct "HtupleOwn" as (versL') "[HtupleOwn Hsafe]".
  
  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  { eauto 10 with iFrame. }
  wp_pures.
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func MkTuple() *Tuple                                         *)
(*****************************************************************)
Theorem wp_MkTuple (key : u64) γ :
  {{{ True }}}
    MkTuple #()
  {{{ (tuple : loc), RET #tuple; is_tuple tuple key γ }}}.
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
  iMod (alloc_lock mvccN _ latch (∃ versL, own_tuple tuple key versL γ) with "[$Hfree] [-latch rcond HΦ]") as "#Hlock".
  { iNext.
    iExists [].
    unfold own_tuple.
    do 5 iExists _.
    iFrame.
    admit.
  }
  iApply "HΦ".
  iExists latch, rcond.
  iMod (readonly_alloc_1 with "latch") as "$".
  iMod (readonly_alloc_1 with "rcond") as "$".
  by iFrame "#".
Admitted.

End heap.
