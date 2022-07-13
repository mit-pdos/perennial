(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Tactical Require Import SimplMatch.
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

Definition spec_find_ver_step (tid : u64) (res : option pver) (ver : pver) : option pver :=
  match res with
  | Some x => Some x
  | None => if decide (int.Z tid > int.Z ver.1.1) then Some ver else None
  end.

Definition spec_find_ver_reverse (vers : list pver) (tid : u64) : option pver :=
  foldl (spec_find_ver_step tid) None vers.

Definition spec_find_ver (vers : list pver) (tid : u64) : option pver :=
  spec_find_ver_reverse (reverse vers) tid.

Definition spec_lookup (vers : list pver) (tid : u64) : dbval :=
  match (spec_find_ver vers tid) with
  | Some ver => if ver.1.2 then Nil else Value ver.2
  | None => Nil
  end.

Definition tuple_wellformed (vers : list pver) (tidlast tidgc : u64) : iProp Σ :=
  "%HtidlastGe" ∷ ⌜Forall (λ ver, int.Z ver.1.1 ≤ int.Z tidlast) vers⌝ ∗
  "%HexistsLt" ∷ ⌜∀ (tid : u64), 0 < int.Z tid -> int.Z tidgc ≤ int.Z tid -> Exists (λ ver, int.Z ver.1.1 < int.Z tid) vers⌝ ∗
  "%HtidgcLe" ∷ ⌜Forall (λ ver, int.Z tidgc ≤ int.Z ver.1.1) (tail vers)⌝ ∗
  "%Hnotnil" ∷ ⌜vers ≠ []⌝.

Definition own_tuple (tuple : loc) (key : u64) (tidown tidlast : u64) versL (γ : mvcc_names) : iProp Σ :=
  ∃ (vers : Slice.t) (tidgc : u64) (vchain : list dbval),
    "Htidown" ∷ tuple ↦[Tuple :: "tidown"] #tidown ∗
    "Htidlast" ∷ tuple ↦[Tuple :: "tidlast"] #tidlast ∗
    "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val vers) ∗
    "HversL" ∷ slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL) ∗
    "Hgclb" ∷  min_tid_lb γ (int.nat tidgc) ∗
    "%HtupleAbs" ∷ (∀ tid, ⌜int.Z tidgc ≤ int.Z tid ≤ int.Z tidlast -> vchain !! (int.nat tid) = Some (spec_lookup versL tid)⌝) ∗
    "Hvchain" ∷ vchain_ptsto γ (if decide (tidown = (U64 0)) then (1/2) else (1/4))%Qp key vchain ∗
    "%HvchainLen" ∷ ⌜(Z.of_nat (length vchain)) = ((int.Z tidlast) + 1)%Z⌝ ∗
    "Hwellformed" ∷ tuple_wellformed versL tidlast tidgc ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (own_tuple _ _ _ _ _ _)) => unfold own_tuple : core.

Definition is_tuple (tuple : loc) (key : u64) (γ : mvcc_names) : iProp Σ :=
  ∃ (latch : loc) (rcond : loc),
    "#Hlatch" ∷ readonly (tuple ↦[Tuple :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (∃ tidown tidlast versL, own_tuple tuple key tidown tidlast versL γ) ∗
    "#Hrcond" ∷ readonly (tuple ↦[Tuple :: "rcond"] #rcond) ∗
    "#HrcondC" ∷ is_cond rcond #latch ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "#Hinvtuple" ∷ mvcc_inv_tuple γ ∗
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

Local Lemma spec_find_ver_step_Some_noop vers tid ver :
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
    by rewrite spec_find_ver_step_Some_noop.
  - exists ver.
    simpl.
    case_decide; last word.
    by rewrite  spec_find_ver_step_Some_noop.
Qed.  

Local Lemma spec_find_ver_reverse_match vers tid :
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
    + by rewrite spec_find_ver_step_Some_noop.
  - contradiction.
Qed.

Local Lemma spec_find_ver_reverse_not_match vers tid :
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

Local Lemma spec_find_ver_extended vers (tidlast tid1 tid2 : u64) :
  int.Z tidlast < int.Z tid1 ->
  int.Z tidlast < int.Z tid2 ->
  Forall (λ ver, int.Z ver.1.1 ≤ int.Z tidlast) vers ->
  spec_find_ver vers tid1 = spec_find_ver vers tid2.
Proof.
  intros Htid1 Htid2 Hlast.
  unfold spec_find_ver.
  unfold spec_find_ver_reverse.
  destruct (reverse _) eqn:E; first done.
  simpl.
  setoid_rewrite Forall_forall in Hlast.
  assert (H : p ∈ vers).
  { apply elem_of_reverse. rewrite E. apply elem_of_list_here. }
  assert (H1 : int.Z p.1.1 < int.Z tid1).
  { apply Hlast in H. apply Z.le_lt_trans with (int.Z tidlast); done. }
  assert (H2 : int.Z p.1.1 < int.Z tid2).
  { apply Hlast in H. apply Z.le_lt_trans with (int.Z tidlast); done. }
  apply Z.lt_gt in H1, H2.
  do 2 (case_decide; last contradiction).
  by do 2 rewrite spec_find_ver_step_Some_noop.
Qed.

Local Lemma spec_lookup_snoc_l vers ver (tid tidx : u64) :
  ver.1.1 = tidx ->
  int.Z tid ≤ int.Z tidx ->
  spec_lookup (vers ++ [ver]) tid = spec_lookup vers tid.
Proof.
  intros Heq Hle.
  unfold spec_lookup, spec_find_ver, spec_find_ver_reverse.
  rewrite reverse_snoc.
  simpl.
  case_decide.
  - by rewrite Heq in H.
  - done.
Qed.

Local Lemma spec_lookup_snoc_r vers ver (tid tidx : u64) :
  ver.1.1 = tidx ->
  int.Z tidx < int.Z tid ->
  spec_lookup (vers ++ [ver]) tid = (if ver.1.2 then Nil else Some ver.2).
Proof.
  intros Heq Hle.
  unfold spec_lookup, spec_find_ver, spec_find_ver_reverse.
  rewrite reverse_snoc.
  simpl.
  case_decide.
  - by rewrite spec_find_ver_step_Some_noop.
  - rewrite Heq in H. word.
Qed.

Local Lemma spec_lookup_extended vers (tidlast tid1 tid2 : u64) :
  int.Z tidlast < int.Z tid1 ->
  int.Z tidlast < int.Z tid2 ->
  Forall (λ ver, int.Z ver.1.1 ≤ int.Z tidlast) vers ->
  spec_lookup vers tid1 = spec_lookup vers tid2.
Proof.
  intros Htid1 Htid2 Hlast.
  unfold spec_lookup.
  by rewrite (spec_find_ver_extended _ _ _ _ Htid1 Htid2); last done.
Qed.

(* Q: Existing tactic does this? *)
Local Lemma ite_apply (A B : Type) (b : bool) (f : A -> B) x y :
  (if b then f x else f y) = f (if b then x else y).
Proof.
  destruct b; done.
Qed.

(*****************************************************************)
(* func MkTuple() *Tuple                                         *)
(*****************************************************************)
Theorem wp_MkTuple (key : u64) γ :
  mvcc_inv_tuple γ -∗
  mvcc_inv_gc γ -∗
  {{{ vchain_ptsto γ (1/2) key [Nil] }}}
    MkTuple #()
  {{{ (tuple : loc), RET #tuple; is_tuple tuple key γ }}}.
Proof.
  iIntros "#Hinvtuple #Hinvgc" (Φ) "!> Hvchain HΦ".
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
  (* tuple.tidlast = 0                                       *)
  (***********************************************************)
  repeat wp_storeField.
  
  (***********************************************************)
  (* tuple.vers = make([]Version, 1, 16)                     *)
  (* tuple.vers[0] = Version{                                *)
  (*     deleted : true,                                     *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_new_slice); first auto.
  iIntros (vers) "HversL".
  wp_storeField.
  wp_loadField.
  iDestruct (is_slice_small_acc with "HversL") as "[HversL HversL_close]".
  wp_apply (wp_SliceSet with "[HversL]").
  { iFrame.
    iPureIntro.
    split; last auto.
    by rewrite lookup_replicate_2; last word.
  }
  iIntros "HversL".
  iDestruct ("HversL_close" with "HversL") as "HversL".
  wp_pures.
  
  (***********************************************************)
  (* return tuple                                            *)
  (***********************************************************)
  set P := (∃ tidown tidlast versL, own_tuple tuple key tidown tidlast versL γ)%I.
  iMod (alloc_lock mvccN _ latch P with "[$Hfree] [-latch rcond HΦ]") as "#Hlock".
  { iNext.
    unfold P.
    iExists (U64 0), (U64 0), [(U64 0, true, U64 0)].
    unfold own_tuple.
    iExists vers, (U64 0), [Nil].
    iFrame.
    iSplit.
    { (* Prove [Hgclb]. *)
      iApply min_tid_lb_zero.
    }
    iSplit.
    { (* Prove [HtupleAbs]. *)
      iPureIntro.
      simpl.
      intros tid Htid.
      replace (int.Z (U64 0)) with 0 in Htid by word.
      by replace tid with (U64 0) by word.
      (* word. *)
    }
    iSplit.
    { (* Prove [HvchainLen]. *)
      by rewrite singleton_length.
    }
    iSplit; last done.
    unfold tuple_wellformed.
    iPureIntro.
    split.
    { (* Prove [HtidlastGe]. *)
      by rewrite Forall_singleton.
    }
    split.
    { (* Prove [HexistsLt]. *)
      intros tid.
      rewrite Exists_cons.
      left.
      simpl.
      word.
    }
    split; last auto.
    by simpl.
  }
  iApply "HΦ".
  iExists latch, rcond.
  iMod (readonly_alloc_1 with "latch") as "$".
  iMod (readonly_alloc_1 with "rcond") as "$".
  by iFrame "#".
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
      apply (spec_find_ver_reverse_match _ _ _ _ _ Hver'); [done | word].
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
    apply (spec_find_ver_reverse_not_match versL' _ vers_take ver'); [auto | auto | word].
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
 *    - [active_tid γ sid tid] in the precondition.
 *    - [min_tid_lb γ tidlbN] in the lock invariant.
 *)
Definition post_tuple__ReadVersion tid key val (ret : u64) γ : iProp Σ :=
  match int.Z ret with
  | 0 => view_ptsto γ key (Value val) tid
  | 1 => view_ptsto γ key Nil tid
  | _ => False
  end.

Lemma case_tuple__ReadVersion tid key val (ret : u64) γ :
  post_tuple__ReadVersion tid key val ret γ -∗
  ⌜int.Z ret = 0 ∨ int.Z ret = 1⌝.
Proof.
  iIntros "H".
  unfold post_tuple__ReadVersion.
  destruct matches.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) ReadVersion(tid uint64) (uint64, uint64)  *)
(*****************************************************************)
Theorem wp_tuple__ReadVersion tuple (tid : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid }}}
    Tuple__ReadVersion #tuple #tid
  {{{ (val : u64) (ret : u64), RET (#val, #ret); active_tid γ tid sid ∗ post_tuple__ReadVersion tid key val ret γ }}}.
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
  clear tidown tidlast tidgc versL vchain.
  iIntros "Hloop".
  iNamed "Hloop".
  iNamed "HtupleOwn".
  iNamed "Hwellformed".
  wp_pures.

  (***********************************************************)
  (* ver := findRightVer(tid, tuple.vers)                    *)
  (***********************************************************)
  wp_loadField.
  iApply fupd_wp.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (active_ge_min with "HinvgcO Hactive Hgclb") as "%HtidGe".
  iAssert (⌜int.Z tid > 0⌝)%I with "[Hactive]" as "%HtidGZ".
  { iDestruct "Hactive" as "[_ %H]". iPureIntro. word. }
  iMod ("HinvgcC" with "HinvgcO") as "_".
  iModIntro.
  wp_apply (wp_findRightVer with "[$HversL]").
  { iPureIntro.
    setoid_rewrite Exists_exists in HexistsLt.
    apply HexistsLt; [word | done].
  }
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
  set P := (|={⊤}=> ∃ (vchain : list (option u64)),
    "Hvchain" ∷ vchain_ptsto γ q key vchain ∗
    "#HvchainW" ∷ vchain_lb γ key vchain ∗
    "%HvchainLen" ∷ ⌜Z.of_nat (length vchain) = (int.Z tidlast' + 1)%Z⌝ ∗
    "%Hwellformed" ∷ tuple_wellformed versL tidlast' tidgc ∗
    "%HtupleAbs" ∷ (∀ tid, ⌜int.Z tidgc ≤ int.Z tid ≤ int.Z tidlast' -> vchain !! (int.nat tid) = Some (spec_lookup versL tid)⌝))%I.
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

        (* Update from [vchain] to [vchain'] with the other half of the ownership in a global inv. *)
        iMod (vchain_update vchain' with "Hinvtuple Hvchain") as "Hvchain"; [by apply prefix_app_r | done |].
        (* Obtain a witness of this update. *)
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
            apply HtupleAbs.
            word.
          * (* [tidlast < x]. *)
            rename n into HxLower.
            apply Znot_le_gt in HxLower.
            rewrite lookup_app_r; last word.
            subst vals.
            rewrite lookup_replicate_2; last word.
            f_equal.
            subst valtid.
            unfold spec_lookup.
            rewrite (spec_find_ver_extended _ tidlast x tid); auto using Z.gt_lt.
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
      auto 10.
  }

  clear HtupleAbs HvchainLen vchain.
  iMod "H".
  iNamed "H".
  clear P.

  iAssert (⌜vchain !! int.nat tid = Some (spec_lookup versL tid)⌝)%I as "%Hlookup".
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
  iFrame "Hactive".
  unfold post_tuple__ReadVersion.
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
    unfold spec_lookup.
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
    unfold spec_lookup.
    by rewrite Hspec H.
  }
Qed.

Definition own_tuple_phys tuple tidown tidlast versL : iProp Σ :=
  ∃ vers,
    "Htidown" ∷ tuple ↦[Tuple :: "tidown"] #tidown ∗
    "Htidlast" ∷ tuple ↦[Tuple :: "tidlast"] #tidlast ∗
    "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val vers) ∗
    "HversL" ∷ slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL).

(*****************************************************************)
(* func (tuple *Tuple) appendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__appendVersion tuple (tid : u64) (val : u64) tidown tidlast versL :
  {{{ own_tuple_phys tuple tidown tidlast versL }}}
    Tuple__appendVersion #tuple #tid #val
  {{{ RET #(); own_tuple_phys tuple (U64 0) (U64 (int.Z tid + 1)) (versL ++ [(tid, false, val)]) }}}.
Proof.
  iIntros (Φ) "HtuplePhys HΦ".
  iNamed "HtuplePhys".
  wp_call.
  
  (***********************************************************)
  (* verNew := Version{                                      *)
  (*     begin   : tid,                                      *)
  (*     val     : val,                                      *)
  (*     deleted : false,                                    *)
  (* }                                                       *)
  (* tuple.vers = append(tuple.vers, verNew)                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_SliceAppend with "[HversL]"); [done | auto 10 with iFrame |].
  iIntros (vers') "HversL". 
  wp_storeField.

  (***********************************************************)
  (* tuple.tidown = 0                                        *)
  (* tuple.tidlast = tid + 1                                 *)
  (***********************************************************)
  do 2 wp_storeField.

  iModIntro.
  iApply "HΦ".
  unfold own_tuple_phys.
  iExists _.
  iFrame.
  iExactEq "HversL".
  unfold named.
  f_equal.
  by rewrite fmap_app.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) AppendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__AppendVersion tuple (tid : u64) (val : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid ∗ mods_token γ key tid }}}
    Tuple__AppendVersion #tuple #tid #val
  {{{ RET #(); active_tid γ tid sid ∗ view_ptsto γ key (Value val) (U64 (int.Z tid + 1)) }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> [Hactive Htoken] HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iDestruct "HtupleOwn" as (tidown tidlast versL) "HtupleOwn".
  iNamed "HtupleOwn".
  iApply fupd_wp.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (active_ge_min with "HinvgcO Hactive Hgclb") as "%HtidGe".
  iMod ("HinvgcC" with "HinvgcO") as "_".
  iModIntro.
  wp_pures.
  
  (***********************************************************)
  (* tuple.appendVersion(tid, val)                           *)
  (***********************************************************)
  wp_apply (wp_tuple__appendVersion with "[$Htidown $Htidlast Hvers HversL]"); first eauto with iFrame.
  iIntros "HtuplePhys".
  iNamed "HtuplePhys".
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
  unfold mods_token.
  iDestruct "Htoken" as (vchain') "[Hvchain' %HvchainLenLt]".

  iAssert (|={⊤}=> vchain_ptsto γ (1 / 2) key vchain ∧ ⌜vchain' = vchain⌝)%I with "[Hvchain Hvchain']" as ">[Hvchain ->]".
  { case_decide.
    - iDestruct (vchain_combine (3 / 4) with "Hvchain Hvchain'") as "[Hvchain _]"; first compute_done.
      iMod (vchain_false with "Hinvtuple Hvchain") as "[]"; done.
    - iDestruct (vchain_combine (1 / 2) with "Hvchain Hvchain'") as "[Hvchain ->]"; first compute_done.
      auto.
  }
  set vals := replicate (int.nat (int.Z tid - int.Z tidlast)) (spec_lookup versL tid).
  set vchain' := vchain ++ vals ++ [Some val].
  iMod (vchain_update vchain' with "Hinvtuple Hvchain") as "Hvchain"; [by apply prefix_app_r | done |].
  iDestruct (vchain_witness with "Hvchain") as "#HvchainW".
  iNamed "Hwellformed".

  assert (HlenN : length vchain = S (int.nat tidlast)) by word.
  iAssert (⌜int.Z tid < 2 ^ 64 - 1⌝)%I with "[Hactive]" as "%Htidmax".
  { iDestruct "Hactive" as "[_ %H]". iPureIntro. word. }
  wp_apply (release_spec with "[-HΦ Hactive]").
  { iFrame "Hlock Hlocked".
    iNext.
    iExists (U64 0), (U64 (int.Z tid + 1)), _.
    do 2 iExists _.
    iExists vchain'.
    iFrame.
    iSplit.
    { (* Prove [HtupleAbs]. *)
      iPureIntro.
      simpl.
      intros tidx Htidx.
      destruct (decide (int.Z tidx ≤ int.Z tidlast)); subst vchain'.
      - rewrite lookup_app_l; last word.
        rewrite HtupleAbs; last word.
        symmetry.
        f_equal.
        apply spec_lookup_snoc_l with tid; [auto | word].
      - rewrite lookup_app_r; last word.
        apply Znot_le_gt in n.
        destruct (decide (int.Z tidx ≤ int.Z tid)).
        + rewrite lookup_app_l; last first.
          { rewrite HlenN replicate_length. word. }
          subst vals.
          rewrite lookup_replicate_2; last word.
          f_equal.
          rewrite (spec_lookup_snoc_l _ _ _ tid); [| auto | word].
          apply spec_lookup_extended with tidlast; [word | word | auto].
        + apply Znot_le_gt in n0.
          rewrite lookup_app_r; last first.
          { rewrite HlenN replicate_length. word. }
          replace (int.Z (U64 _)) with (int.Z tid + 1) in Htidx by word.
          assert (Etidx : int.Z tidx = int.Z tid + 1) by word.
          replace (int.nat tidx - _ - _)%nat with 0%nat; last first.
          { rewrite replicate_length. word. }
          simpl. f_equal.
          rewrite (spec_lookup_snoc_r _ _ _ tid); [done | auto | word].
    }
    iSplit.
    { (* Prove [HvchainLen]. *)
      iPureIntro.
      subst vchain'.
      do 2 rewrite app_length.
      rewrite HlenN replicate_length singleton_length. word.
    }
    iSplit; last done.
    { (* Prove [Hwellformed]. *)
      iPureIntro.
      split.
      { (* Prove [HtidlastGe]. *)
        apply Forall_app_2.
        - apply (Forall_impl _ _ _ HtidlastGe).
          intros verx Hverx.
          trans (int.Z tid); word.
        - rewrite Forall_singleton. simpl. word.
      }
      split.
      { (* Prove [HexistsLt]. *)
        intros tidx HtidxGZ Htidx.
        apply Exists_app.
        left.
        apply HexistsLt; done.
      }
      split.
      { (* Prove [HtidgcLe]. *)
        destruct versL eqn:EversL; first contradiction.
        simpl.
        apply Forall_app_2; first done.
        by apply Forall_singleton.
      }
      { (* Prove [Hnotnil]. *)
        apply not_eq_sym.
        apply app_cons_not_nil.
      }
    }
  }
  
  wp_pures.
  iApply "HΦ".
  iModIntro.
  iFrame.
  iExists vchain'.
  iFrame "HvchainW".
  (* Prove [view_ptsto]. *)
  iPureIntro.
  subst vchain'.
  assert (HvchainAppLen : length (vchain ++ vals) = S (int.nat tid)).
  { rewrite app_length.
    rewrite HlenN.
    rewrite replicate_length. word.
  }
  rewrite app_assoc.
  rewrite lookup_app_r; last first.
  { rewrite HvchainAppLen. word. }
  replace (int.nat _ - length _)%nat with 0%nat; last first.
  { rewrite HvchainAppLen. word. }
  done.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) killVersion(tid uint64) bool              *)
(*****************************************************************)
Theorem wp_tuple__killVersion tuple (tid : u64) tidown tidlast versL :
  {{{ own_tuple_phys tuple tidown tidlast versL }}}
    Tuple__killVersion #tuple #tid
  {{{ (ok : bool), RET #ok; own_tuple_phys tuple (U64 0) (int.Z tid + 1) (versL ++ [(tid, true, (U64 0))]) }}}.
Proof.
  iIntros (Φ) "HtuplePhys HΦ".
  iNamed "HtuplePhys".
  wp_call.
  
  (***********************************************************)
  (* verNew := Version{                                      *)
  (*     begin   : tid,                                      *)
  (*     deleted : true,                                     *)
  (* }                                                       *)
  (* tuple.vers = append(tuple.vers, verNew)                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_SliceAppend with "[HversL]"); [done | auto 10 with iFrame |].
  iIntros (vers') "HversL". 
  wp_storeField.

  (***********************************************************)
  (* tuple.tidown = 0                                        *)
  (* tuple.tidlast = tid + 1                                 *)
  (***********************************************************)
  do 2 wp_storeField.

  iModIntro.
  iApply "HΦ".
  unfold own_tuple_phys.
  iExists _.
  iFrame.
  iExactEq "HversL".
  unfold named.
  f_equal.
  by rewrite fmap_app.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) KillVersion(tid uint64) uint64            *)
(*****************************************************************)
Theorem wp_tuple__KillVersion tuple (tid : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid ∗ mods_token γ key tid }}}
    Tuple__KillVersion #tuple #tid
  {{{ (ret : u64), RET #ret; active_tid γ tid sid ∗ view_ptsto γ key Nil (U64 (int.Z tid + 1)) }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> [Hactive Htoken] HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iDestruct "HtupleOwn" as (tidown tidlast versL) "HtupleOwn".
  iNamed "HtupleOwn".
  iApply fupd_wp.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (active_ge_min with "HinvgcO Hactive Hgclb") as "%HtidGe".
  iMod ("HinvgcC" with "HinvgcO") as "_".
  iModIntro.
  wp_pures.
  
  (***********************************************************)
  (* ok := tuple.killVersion(tid)                            *)
  (***********************************************************)
  wp_apply (wp_tuple__killVersion with "[$Htidown $Htidlast Hvers HversL]"); first eauto with iFrame.
  iIntros (ok) "HtuplePhys".
  iNamed "HtuplePhys".
  wp_pures.

  (***********************************************************)
  (* var ret uint64                                          *)
  (* if ok {                                                 *)
  (*     ret = common.RET_SUCCESS                            *)
  (* } else {                                                *)
  (*     ret = common.RET_NONEXIST                           *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (retR) "HretR".
  wp_pures.
  replace ok with (bool_decide (ok = true)); last first.
  { case_bool_decide.
    - done.
    - by apply not_true_is_false in H.
  }
  wp_apply (wp_If_join_evar with "[HretR]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    - wp_if_true.
      wp_store.
      iModIntro.
      iSplit; first done.
      replace #0 with #(if b' then 0 else 1) by by rewrite Eb'.
      iNamedAccu.
    - wp_if_false.
      wp_store.
      iModIntro.
      iSplit; first done.
      by rewrite Eb'.
  }
  iIntros "HretR".
  iNamed "HretR".
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
  unfold mods_token.
  iDestruct "Htoken" as (vchain') "[Hvchain' %HvchainLenLt]".

  iAssert (|={⊤}=> vchain_ptsto γ (1 / 2) key vchain ∧ ⌜vchain' = vchain⌝)%I with "[Hvchain Hvchain']" as ">[Hvchain ->]".
  { case_decide.
    - iDestruct (vchain_combine (3 / 4) with "Hvchain Hvchain'") as "[Hvchain _]"; first compute_done.
      iMod (vchain_false with "Hinvtuple Hvchain") as "[]"; done.
    - iDestruct (vchain_combine (1 / 2) with "Hvchain Hvchain'") as "[Hvchain ->]"; first compute_done.
      auto.
  }
  set vals := replicate (int.nat (int.Z tid - int.Z tidlast)) (spec_lookup versL tid).
  set vchain' := vchain ++ vals ++ [Nil].
  iMod (vchain_update vchain' with "Hinvtuple Hvchain") as "Hvchain"; [by apply prefix_app_r | done |].
  iDestruct (vchain_witness with "Hvchain") as "#HvchainW".
  iNamed "Hwellformed".
  
  assert (HlenN : length vchain = S (int.nat tidlast)) by word.
  iAssert (⌜int.Z tid < 2 ^ 64 - 1⌝)%I with "[Hactive]" as "%Htidmax".
  { iDestruct "Hactive" as "[_ %H]". iPureIntro. word. }
  wp_apply (release_spec with "[-HΦ Hactive HretR]").
  { iFrame "Hlock Hlocked".
    iNext.
    iExists (U64 0), (U64 (int.Z tid + 1)), _.
    do 2 iExists _.
    iExists vchain'.
    iFrame.
    iSplit.
    { (* Prove [HtupleAbs]. *)
      iPureIntro.
      simpl.
      intros tidx Htidx.
      destruct (decide (int.Z tidx ≤ int.Z tidlast)); subst vchain'.
      - rewrite lookup_app_l; last word.
        rewrite HtupleAbs; last word.
        symmetry.
        f_equal.
        apply spec_lookup_snoc_l with tid; [auto | word].
      - rewrite lookup_app_r; last word.
        apply Znot_le_gt in n.
        destruct (decide (int.Z tidx ≤ int.Z tid)).
        + rewrite lookup_app_l; last first.
          { rewrite HlenN replicate_length. word. }
          subst vals.
          rewrite lookup_replicate_2; last word.
          f_equal.
          rewrite (spec_lookup_snoc_l _ _ _ tid); [| auto | word].
          apply spec_lookup_extended with tidlast; [word | word | auto].
        + apply Znot_le_gt in n0.
          rewrite lookup_app_r; last first.
          { rewrite HlenN replicate_length. word. }
          replace (int.Z (U64 _)) with (int.Z tid + 1) in Htidx by word.
          assert (Etidx : int.Z tidx = int.Z tid + 1) by word.
          replace (int.nat tidx - _ - _)%nat with 0%nat; last first.
          { rewrite replicate_length. word. }
          simpl. f_equal.
          rewrite (spec_lookup_snoc_r _ _ _ tid); [done | auto | word].
    }
    iSplit.
    { (* Prove [HvchainLen]. *)
      iPureIntro.
      subst vchain'.
      do 2 rewrite app_length.
      rewrite HlenN replicate_length singleton_length. word.
    }
    iSplit; last done.
    { (* Prove [Hwellformed]. *)
      iPureIntro.
      split.
      { (* Prove [HtidlastGe]. *)
        apply Forall_app_2.
        - apply (Forall_impl _ _ _ HtidlastGe).
          intros verx Hverx.
          trans (int.Z tid); word.
        - rewrite Forall_singleton. simpl. word.
      }
      split.
      { (* Prove [HexistsLt]. *)
        intros tidx HtidxGZ Htidx.
        apply Exists_app.
        left.
        apply HexistsLt; done.
      }
      split.
      { (* Prove [HtidgcLe]. *)
        destruct versL eqn:EversL; first contradiction.
        simpl.
        apply Forall_app_2; first done.
        by apply Forall_singleton.
      }
      { (* Prove [Hnotnil]. *)
        apply not_eq_sym.
        apply app_cons_not_nil.
      }
    }
  }
  
  wp_pures.
  wp_load.
  rewrite ite_apply.
  iApply "HΦ".
  iModIntro.
  iFrame.
  iExists vchain'.
  iFrame "HvchainW".
  (* Prove [view_ptsto]. *)
  iPureIntro.
  subst vchain'.
  assert (HvchainAppLen : length (vchain ++ vals) = S (int.nat tid)).
  { rewrite app_length.
    rewrite HlenN.
    rewrite replicate_length. word.
  }
  rewrite app_assoc.
  rewrite lookup_app_r; last first.
  { rewrite HvchainAppLen. word. }
  replace (int.nat _ - length _)%nat with 0%nat; last first.
  { rewrite HvchainAppLen. word. }
  done.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) Free(tid uint64)                          *)
(*****************************************************************)
Theorem wp_tuple__Free tuple (tid : u64) (key : u64) (versL : list (u64 * u64 * u64)) γ :
  is_tuple tuple key γ -∗
  {{{ mods_token γ key tid }}}
    Tuple__Free #tuple #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Htoken HΦ".
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
  { iFrame "Hlock Hlocked".
    iNext.
    iExists (U64 0).
    do 2 iExists _.
    do 3 iExists _.
    iFrame "% ∗".
    iDestruct "Htoken" as (vchain') "[Hvchain' %HvchainLenLt]".
    case_decide; first iFrame.
    by iDestruct (vchain_combine (1 / 2) with "Hvchain Hvchain'") as "[Hvchain ->]"; first compute_done.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

Definition post_tuple__Own tid key (ret : u64) γ : iProp Σ :=
  match int.Z ret with
  | 0 => mods_token γ key tid
  | 200 | 400 => True
  | _ => False
  end.

(*****************************************************************)
(* func (tuple *Tuple) Own(tid uint64) bool                      *)
(*****************************************************************)
Theorem wp_tuple__Own tuple (tid : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid }}}
    Tuple__Own #tuple #tid
  {{{ (ret : u64), RET #ret; active_tid γ tid sid ∗ post_tuple__Own tid key ret γ
  }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Hactive HΦ".
  iAssert (⌜int.Z tid > 0⌝)%I with "[Hactive]" as "%Htid".
  { iDestruct "Hactive" as "[_ %Htid]". iPureIntro. word. }
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
  (* if tid < tuple.tidlast {                                *)
  (*   tuple.latch.Unlock()                                  *)
  (*   return common.RET_UNSERIALIZABLE                      *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[-HΦ Hactive]").
    { eauto 15 with iFrame. }
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }

  (***********************************************************)
  (* if tuple.tidown != 0 {                                  *)
  (*   tuple.latch.Unlock()                                  *)
  (*   return common.RET_RETRY                               *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[-HΦ Hactive]").
    { eauto 15 with iFrame. }
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }

  (***********************************************************)
  (* tuple.tidown = tid                                      *)
  (***********************************************************)
  wp_storeField.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  iDestruct (vchain_split (1 / 4) (1 / 4) with "Hvchain") as "[Hchain Hvchain']"; first compute_done.
  wp_apply (release_spec with "[-HΦ Hactive Hvchain']").
  { iFrame "Hlock Hlocked".
    iNext.
    iExists tid.
    do 2 iExists _.
    do 3 iExists _.
    iFrame "% ∗".
    case_decide.
    - by rewrite H in Htid.
    - iFrame.
  }
  wp_pures.
  iModIntro.

  (***********************************************************)
  (* return common.RET_SUCCESS                               *)
  (***********************************************************)
  iApply "HΦ".
  unfold post_tuple__Own.
  iFrame.
  change (int.Z 0) with 0.
  simpl.
  unfold mods_token.
  iExists vchain.
  iFrame.
  iPureIntro.
  word.
Qed.

Lemma val_to_ver_with_val_ty (x : val) :
  val_ty x (uint64T * (boolT * (uint64T * unitT))%ht) ->
  (∃ (b : u64)  (e : bool) (v : u64), x = ver_to_val (b, e, v)).
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

Lemma inv_ver_to_val (x y : pver) :
  ver_to_val x = ver_to_val y ->
  x = y.
Proof.
  intros H.
  inversion H.
  rewrite (surjective_pairing x).
  rewrite (surjective_pairing x.1).
  rewrite (surjective_pairing y).
  rewrite (surjective_pairing y.1).
  by rewrite H1 H2 H3.
Qed.

Lemma drop_1_tail {A : Type} (l : list A) :
  tail l = drop 1 l.
Proof.
  destruct l.
  - done.
  - simpl. rewrite drop_0. done.
Qed.

Lemma drop_tail_commute {A : Type} (n : nat) (l : list A) :
  tail (drop n l) = drop n (tail l).
Proof.
  do 2 rewrite drop_1_tail.
  do 2 rewrite drop_drop.
  f_equal.
  lia.
Qed.

Definition own_tuple_phys_vers tuple versL : iProp Σ :=
  ∃ vers,
    "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val vers) ∗
    "HversL" ∷ slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL).

(*****************************************************************)
(* func (tuple *Tuple) removeVersions(tid uint64)                *)
(*****************************************************************)
Theorem wp_tuple__removeVersions tuple (tid : u64) versL :
  {{{ own_tuple_phys_vers tuple versL ∧ ⌜versL ≠ []⌝ }}}
    Tuple__removeVersions #tuple #tid
  {{{ RET #();
        (∃ versL',
           own_tuple_phys_vers tuple versL' ∧
           (∃ vers_prefix, ⌜vers_prefix ≠ [] ∧ versL = vers_prefix ++ versL'⌝) ∧
           (⌜Forall (λ ver, int.Z tid ≤ int.Z ver.1.1) (tail versL')⌝) ∧
           (∃ ver, ⌜ver ∈ versL' ∧ int.Z ver.1.1 < int.Z tid⌝)) ∨
        (own_tuple_phys_vers tuple versL)
  }}}.
Proof.
  iIntros (Φ) "[HtuplePhys %Hnotnil] HΦ".
  iNamed "HtuplePhys".
  wp_call.

  iDestruct (is_slice_sz with "HversL") as "%HversLen".
  rewrite fmap_length in HversLen.
  iDestruct (is_slice_small_acc with "HversL") as "[HversS HversL]".

  (***********************************************************)
  (* var idx uint64                                          *)
  (* idx = uint64(len(tuple.vers)) - 1                       *)
  (* for {                                                   *)
  (*     if idx == 0 {                                       *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     ver := tuple.vers[idx]                              *)
  (*     if ver.begin < tid {                                *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     idx--                                               *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first auto.
  iIntros (idxR) "HidxR".
  wp_pures.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_store.
  wp_pures.
  set P := λ (b : bool), (∃ (idx : u64),
             "%Hbound" ∷ (⌜int.Z 0 ≤ int.Z idx < Z.of_nat (length versL)⌝) ∗
             "HidxR" ∷ idxR ↦[uint64T] #idx ∗
             "Hvers" ∷ tuple ↦[Tuple :: "vers"] to_val vers ∗
             "HversS" ∷ is_slice_small vers (struct.t Version) 1 (ver_to_val <$> versL) ∗
             "%HallLe" ∷ (⌜Forall (λ ver, int.Z tid ≤ int.Z ver.1.1) (drop (S (int.nat idx)) versL)⌝) ∗
             "%Hexit" ∷ if b
                        then ⌜True⌝
                        else ⌜(int.Z idx = 0) ∨
                              (0 < int.Z idx ∧
                               ∃ ver, ver ∈ (drop (int.nat idx) versL) ∧
                               int.Z ver.1.1 < int.Z tid)⌝)%I.
  wp_apply (wp_forBreak P with "[] [-HΦ HversL]").
  { (* Loop body. *)
    clear Φ.
    iIntros (Φ).
    iModIntro.
    iIntros "Hloop HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.
    wp_if_destruct.
    { (* [idx = 0]. *)
      iApply "HΦ".
      iModIntro.
      unfold P.
      iExists _.
      eauto 10 with iFrame.
    }
    wp_load.
    wp_loadField.
    destruct (list_lookup_lt _ (ver_to_val <$> versL) (int.nat idx)) as [ver HSome].
    { rewrite fmap_length. word. }
    wp_apply (wp_SliceGet with "[HversS]"); first auto.
    iIntros "[HversS %Hval_ty]".
    destruct (val_to_ver_with_val_ty ver) as (b & d & v & ->); first auto.
    wp_pures.
    apply u64_val_ne in Heqb.
    rewrite list_lookup_fmap in HSome.
    apply fmap_Some_1 in HSome as (verx & Hlookup & Everx).
    wp_if_destruct.
    { iApply "HΦ".
      iModIntro.
      unfold P.
      iExists _.
      iFrame "% ∗".
      iPureIntro.
      right.
      split; first word.
      exists (b, d, v).
      split; last done.
      apply (elem_of_list_lookup_2 _ 0).
      rewrite lookup_drop.
      rewrite -plus_n_O.
      rewrite Hlookup.
      f_equal.
      symmetry.
      by apply inv_ver_to_val.
    }
    wp_load.
    wp_store.
    iApply "HΦ".
    iExists _.
    iFrame.
    iPureIntro.
    split; first word.
    split; last done.
    replace (S _) with (int.nat idx); last word.
    rewrite (drop_S _ (b, d, v)); last first.
    { rewrite Hlookup. f_equal. by apply inv_ver_to_val. }
    apply Forall_cons_2; last done.
    apply Znot_lt_ge in Heqb0.
    simpl.
    word.
  }
  { (* Loop entry. *)
    unfold P.
    iExists _.
    iFrame.
    iPureIntro.
    assert (Hgt : 0 < int.Z vers.(Slice.sz)).
    { destruct (nil_or_length_pos versL); first contradiction. word. }
    split; first word.
    split; last done.
    replace (S _) with (length versL); last word.
    by rewrite drop_all.
  }

  iIntros "Hloop".
  iNamed "Hloop".

  wp_pures.
  wp_load.
  wp_loadField.
  wp_apply wp_SliceSkip.
  { word. }
  wp_storeField.

  iDestruct ("HversL" with "HversS") as "HversL".
  iDestruct "HversL" as "[HversS HversC]".
  iDestruct (slice.is_slice_small_take_drop _ _ _ idx with "HversS") as "[HversS _]"; first word.
  iDestruct (slice.is_slice_cap_skip _ _ idx with "HversC") as "HversC"; first word.
  iDestruct (slice.is_slice_split with "[$HversS $HversC]") as "HversL".
  rewrite <- fmap_drop.

  iApply "HΦ".
  iModIntro.
  destruct Hexit as [? | [Hgt HexistsLt]].
  - iRight.
    rewrite H.
    change (Z.to_nat 0) with 0%nat.
    rewrite drop_0.
    iExists _.
    iFrame.
  - iLeft.
    set versL' := drop (int.nat idx) versL.
    iExists versL'.
    iSplit.
    { iExists _.
      iFrame.
    }
    iPureIntro.
    split.
    { exists (take (int.nat idx) versL).
      split.
      { apply length_nonzero_neq_nil.
        rewrite take_length_le; first word.
        word.
      }
      { symmetry. apply take_drop. }
    }
    split.
    { subst versL'.
      replace (tail _) with (drop (S (int.nat idx)) versL); first done.
      destruct versL; by rewrite drop_tail_commute.
    }
    { auto. }
Qed.

Local Lemma spec_find_ver_suffix vers vers_prefix vers_suffix ver (tid : u64) :
  vers = vers_prefix ++ vers_suffix ->
  spec_find_ver vers_suffix tid = Some ver ->
  spec_find_ver vers tid = Some ver.
Proof.
  intros Hvers Hlookup.
  unfold spec_find_ver, spec_find_ver_reverse in *.
  rewrite Hvers.
  rewrite reverse_app.
  rewrite foldl_app.
  rewrite Hlookup.
  by rewrite spec_find_ver_step_Some_noop.
Qed.

Local Lemma spec_lookup_suffix vers vers_prefix vers_suffix (tid : u64) :
  vers = vers_prefix ++ vers_suffix ->
  Exists (λ ver, int.Z ver.1.1 < int.Z tid) vers_suffix ->
  spec_lookup vers tid = spec_lookup vers_suffix tid.
Proof.
  intros Hsuffix HexistsLt.
  rewrite Exists_exists in HexistsLt.
  destruct HexistsLt as (ver & Hin & Hlt).
  destruct (spec_find_ver_lt_Some vers_suffix tid ver) as [ver' HSome]; [auto | auto |].
  
  unfold spec_lookup.
  rewrite HSome.
  rewrite (spec_find_ver_suffix vers vers_prefix vers_suffix ver'); done.
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
Theorem wp_tuple__RemoveVersions tuple (tid : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ min_tid_lb γ (int.nat tid) }}}
    Tuple__RemoveVersions #tuple #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Hgclb' HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iNamed "HtupleOwn".
  iNamed "Hwellformed".
  wp_pures.

  (***********************************************************)
  (* tuple.removeVersions(tid)                               *)
  (***********************************************************)
  wp_apply (wp_tuple__removeVersions with "[Hvers HversL]").
  { unfold own_tuple_phys_vers. eauto with iFrame. }
  iIntros "HtuplePhys".
  
  iDestruct "HtuplePhys" as "[HtuplePhys | HtuplePhys]"; last first.
  { (* The list of physcial versions are not changed. *)
    iNamed "HtuplePhys".
    wp_pures.
    wp_loadField.
    iClear "Hgclb'".
    wp_apply (release_spec with "[-HΦ]"); first eauto 15 with iFrame.
    wp_pures.
    by iApply "HΦ".
  }

  (* The new list of physical versions is a suffix of the old one. *)
  iDestruct "HtuplePhys" as (versL') "(HtuplePhys & %Hsuffix & %HtailLe & %HtidGt)".
  clear vers.
  iNamed "HtuplePhys".
  wp_pures.

  assert (H2 : int.Z tidgc < int.Z tid).
  { destruct Hsuffix as [versPrefix [Hnotnil' Hsuffix]].
    destruct HtidGt as [verPivot [Hin HtidGt]].
    apply Z.le_lt_trans with (int.Z verPivot.1.1).
    - rewrite Forall_forall in HtidgcLe.
      apply HtidgcLe.
      rewrite Hsuffix.
      destruct versPrefix; first congruence.
      simpl.
      apply elem_of_app.
      by right.
    - done.
  }
  
  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  destruct HtidGt as (verHead & Hin & HtidGt).
  destruct Hsuffix as (versPrefix & Hprefix & Hsuffix).
  wp_apply (release_spec with "[-HΦ]").
  { iFrame "Hlock Hlocked".
    iNext.
    do 2 iExists _.
    iExists versL'.
    unfold own_tuple.
    iExists vers, tid, vchain.
    iFrame "% ∗".
    iSplit.
    { (* Prove [HtupleAbs]. *)
      iPureIntro.
      simpl.
      intros tidx Htidx.
      rewrite HtupleAbs; last word.
      f_equal.
      apply spec_lookup_suffix with versPrefix.
      { by rewrite Hsuffix. }
      { rewrite Exists_exists.
        exists verHead.
        split; [done | word].
      }
    }
    iPureIntro.
    split.
    { (* Prove [HtidlastGe]. *)
      rewrite Hsuffix in HtidlastGe.
      by apply Forall_app in HtidlastGe as [_ ?].
    }
    split.
    { (* Prove [HexistsLt]. *)
      intros tidx HtidxGZ Htidx.
      rewrite Exists_exists.
      exists verHead.
      split; [done | word].
    }
    { by apply elem_of_not_nil with verHead. }
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End heap.
