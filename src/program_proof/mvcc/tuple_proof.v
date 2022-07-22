(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Tactical Require Import SimplMatch.
From Perennial.program_proof Require Export grove_prelude.
(* Import Coq model of our Goose program.*)
From Goose.github_com.mit_pdos.go_mvcc Require Import tuple.
From Perennial.program_proof.mvcc Require Import mvcc_ghost.
(* prefer untyped slices *)
Import Perennial.goose_lang.lib.slice.slice.

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
  "%HexistsLt" ∷ ⌜∀ (tid : u64), 0 < int.Z tid ->
                                 int.Z tidgc ≤ int.Z tid ->
                                 Exists (λ ver, int.Z ver.1.1 < int.Z tid) vers⌝ ∗
  "%HtidgcLe" ∷ ⌜Forall (λ ver, int.Z tidgc ≤ int.Z ver.1.1) (tail vers)⌝ ∗
  "%Hnotnil" ∷ ⌜vers ≠ []⌝.

Definition own_tuple_phys
           (tuple : loc) (tidown tidlast : u64) (vers : list pver)
  : iProp Σ :=
  ∃ (versS : Slice.t),
    "Htidown" ∷ tuple ↦[Tuple :: "tidown"] #tidown ∗
    "Htidlast" ∷ tuple ↦[Tuple :: "tidlast"] #tidlast ∗
    "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val versS) ∗
    "HversS" ∷ slice.is_slice versS (structTy Version) 1 (ver_to_val <$> vers).
Local Hint Extern 1 (environments.envs_entails _ (own_tuple_phys _ _ _ _)) => unfold own_tuple_phys : core.

Definition own_tuple_abst
           (key : u64) (tidown tidlast tidgc : u64) (vers : list pver) (vchain : list dbval) γ
  : iProp Σ :=
  "Hvchain" ∷ ptuple_auth γ (if decide (tidown = (U64 0)) then (1/2) else (1/4))%Qp key vchain ∗
  "%HtupleAbs" ∷ (∀ tid, ⌜int.Z tidgc ≤ int.Z tid ≤ int.Z tidlast ->
                         vchain !! (int.nat tid) = Some (spec_lookup vers tid)⌝) ∗
  "%HvchainLen" ∷ ⌜(Z.of_nat (length vchain)) = ((int.Z tidlast) + 1)%Z⌝ ∗
  "#Hgclb" ∷  min_tid_lb γ (int.nat tidgc) ∗
  "Hwellformed" ∷ tuple_wellformed vers tidlast tidgc.
Local Hint Extern 1 (environments.envs_entails _ (own_tuple_abst _ _ _ _ _ _)) => unfold own_tuple_abst : core.

Definition own_tuple (tuple : loc) (key : u64) γ : iProp Σ :=
  ∃ (tidown tidlast tidgc : u64) (vers : list pver) (vchain : list dbval),
    "Hphys" ∷ own_tuple_phys tuple tidown tidlast vers ∗
    "Habst" ∷ own_tuple_abst key tidown tidlast tidgc vers vchain γ.
Local Hint Extern 1 (environments.envs_entails _ (own_tuple _ _ _)) => unfold own_tuple : core.

Definition is_tuple (tuple : loc) (key : u64) γ : iProp Σ :=
  ∃ (latch : loc) (rcond : loc),
    "#Hlatch" ∷ readonly (tuple ↦[Tuple :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_tuple tuple key γ) ∗
    "#Hrcond" ∷ readonly (tuple ↦[Tuple :: "rcond"] #rcond) ∗
    "#HrcondC" ∷ is_cond rcond #latch ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "#Hinvtuple" ∷ mvcc_inv_tuple γ ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (is_tuple _ _ _)) => unfold is_tuple : core.

Definition tuple_locked tuple (key : u64) (latch : loc) γ : iProp Σ :=
  "#Hlatch" ∷ readonly (tuple ↦[Tuple :: "latch"] #latch) ∗
  "#Hlock" ∷ is_lock mvccN #latch (own_tuple tuple key γ) ∗
  "Hlocked" ∷ locked #latch.

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
  {{{ ptuple_auth γ (1/2) key [Nil] }}}
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
  wp_apply (wp_new_slice_cap); [auto | word |].
  iIntros (vers) "HversS".
  wp_storeField.
  wp_loadField.
  iDestruct (is_slice_small_acc with "HversS") as "[HversS HversC]".
  wp_apply (wp_SliceSet with "[HversS]").
  { iFrame.
    iPureIntro.
    split; last auto.
    by rewrite lookup_replicate_2; last word.
  }
  iIntros "HversS".
  iDestruct ("HversC" with "HversS") as "HversS".
  wp_pures.
  
  (***********************************************************)
  (* return tuple                                            *)
  (***********************************************************)
  set P := (own_tuple tuple key γ)%I.
  iMod (alloc_lock mvccN _ latch P with "[$Hfree] [-latch rcond HΦ]") as "#Hlock".
  { iNext.
    unfold P.
    unfold own_tuple.
    iExists (U64 0), (U64 0), (U64 0), [(U64 0, true, U64 0)], [Nil].
    iFrame.
    iSplit.
    { iExists (Slice.mk vers 1 16). iFrame. }
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
    iSplit.
    { (* Prove [Hgclb]. *)
      iApply min_tid_lb_zero.
    }
    iSplit.
    { (* Prove [HtidlastGe]. *)
      by rewrite Forall_singleton.
    }
    iPureIntro.
    split.
    { (* Prove [HexistsLt]. *)
      intros tid.
      rewrite Exists_cons.
      left. simpl. word.
    }
    split; [by simpl | auto].
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
Local Theorem wp_findRightVer (tid : u64) (versS : Slice.t)
                              (vers : list (u64 * bool * u64)) :
  {{{ ⌜∃ (ver : pver), (ver ∈ vers) ∧ (int.Z ver.1.1 < int.Z tid)⌝ ∗
      slice.is_slice versS (structTy Version) 1 (ver_to_val <$> vers)
  }}}
    findRightVer #tid (to_val versS)
  {{{ (ver : pver), RET (ver_to_val ver);
      ⌜spec_find_ver vers tid = Some ver⌝ ∗
      slice.is_slice versS (structTy Version) 1 (ver_to_val <$> vers)
  }}}.
Proof.
  iIntros (Φ) "[%Hlt HversS] HΦ".
  destruct Hlt as [ver'' [Hin Hlt]].
  destruct (nil_or_length_pos vers) as [| Hnonempty].
  { rewrite H in Hin. by destruct (not_elem_of_nil ver''). }
  iDestruct (slice.is_slice_small_acc with "HversS") as "[HversS HversC]".
  iDestruct (is_slice_small_sz with "HversS") as "%HversLen".
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
             "HversS" ∷ is_slice_small versS (struct.t Version) 1 (ver_to_val <$> vers) ∗
             "%Hspec" ∷ if b
                        then ⌜spec_find_ver_reverse (take (int.nat idx) (reverse vers)) tid = None⌝
                        else ⌜spec_find_ver_reverse (reverse vers) tid = Some ver⌝)%I.
  wp_apply (wp_forBreak P with "[] [-HΦ HversC]").
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
      replace (take (int.nat idx) _) with (reverse vers) in Hspec; last first.
      { symmetry.
        pose proof (reverse_length vers) as HversRevLen.
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
    destruct (list_lookup_lt _ vers (length vers - S (int.nat idx))%nat) as [ver' Hver']; first word.
    wp_apply (wp_SliceGet with "[HversS]").
    { iFrame.
      iPureIntro.
      set x := versS.(Slice.sz).
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
      replace (int.Z (word.sub _ (U64 1))) with (int.Z versS.(Slice.sz) - int.Z idx - 1); last first.
      { subst x. word. }
      replace (Z.to_nat _) with ((length vers) - (S (int.nat idx)))%nat; last first.
      { rewrite HversLen. word. }
      rewrite list_lookup_fmap.
      rewrite Hver'.
      by apply fmap_Some_2.
    }
    iIntros "[HversS %Hvalty]".
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
    set vers' := vers_take ++ _.
    apply Znot_lt_ge in Heqb0.
    apply (spec_find_ver_reverse_not_match vers' _ vers_take ver'); [auto | auto | word].
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
  iDestruct ("HversC" with "HversS") as "HversS".
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

Definition tuple_read tuple tid key val (ret : u64) γ : iProp Σ :=
  ∃ (tidown tidlast tidgc : u64) (vers : list pver)
    (vchain : list dbval),
    (* physical state is updated, but logical state is not. *)
    let tidlast' := if bool_decide (int.Z tidlast < int.Z tid)
                    then tid
                    else tidlast
    in
    "Hphys" ∷ own_tuple_phys tuple tidown tidlast' vers ∗
    "Habst" ∷ own_tuple_abst key tidown tidlast tidgc vers vchain γ ∗
    "%Htid" ∷ ⌜int.Z tid ≤ int.Z tidlast ∨ int.Z tidown = 0⌝ ∗
    "%Hret" ∷ ⌜match int.Z ret with
               | 0 => spec_lookup vers tid = Value val
               | 1 => spec_lookup vers tid = Nil
               | _ => False
               end⌝.

(*
Lemma case_tuple__ReadVersion tuple tid key val (ret : u64) γ :
  post_tuple__ReadVersion tuple tid key val ret γ -∗
  ⌜int.Z ret = 0 ∨ int.Z ret = 1⌝.
Proof.
  iIntros "H".
  iNamed "H".
Admitted.
 *)

(*****************************************************************)
(* func (tuple *Tuple) ReadVersion(tid uint64) (uint64, uint64)  *)
(*****************************************************************)
Theorem wp_tuple__ReadVersion tuple (tid : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid }}}
    Tuple__ReadVersion #tuple #tid
  {{{ (val : u64) (ret : u64) (latch : loc), RET (#val, #ret);
      active_tid γ tid sid ∗
      tuple_locked tuple key latch γ ∗
      tuple_read tuple tid key val ret γ
  }}}.
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
  set P := λ (b : bool),
             (∃ (tidown tidlast tidgc : u64) (vers : list pver) (vchain : list dbval),
                 "Hphys" ∷ own_tuple_phys tuple tidown tidlast vers ∗
                 "Habst" ∷ own_tuple_abst key tidown tidlast tidgc vers vchain γ ∗
                 "Hlocked" ∷ locked #latch ∗
                 "%Hexit" ∷ if b then ⌜True⌝ else ⌜(int.Z tid) ≤ (int.Z tidlast) ∨ (int.Z tidown) = 0⌝)%I.
  wp_apply (wp_forBreak_cond P with "[] [-HΦ Hactive]").
  { (* Loop body preserves the invariant. *)
    clear Φ.
    clear tidown tidlast tidgc vers vchain.
    iIntros (Φ) "!> Hloop HΦ".
    iNamed "Hloop".
    iNamed "Hphys".
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
    destruct Heqb; (iModIntro; do 5 iExists _; iFrame "Hlocked Habst").
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
  clear tidown tidlast tidgc vers vchain.
  iIntros "Hloop".
  iNamed "Hloop".
  iNamed "Hphys".
  iNamed "Habst".
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
  wp_apply (wp_findRightVer with "[$HversS]").
  { iPureIntro.
    setoid_rewrite Exists_exists in HexistsLt.
    apply HexistsLt; [word | done].
  }
  iIntros (ver) "[%Hspec HversS]".
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

  (***********************************************************)
  (* return ver.val, ret                                     *)
  (***********************************************************)
  wp_load.
  wp_pures.
  (* Set Printing Coercions. *)
  repeat rewrite ite_apply.
  iModIntro.
  iApply "HΦ".
  iFrame "Hactive".
  iSplitL "Hlocked".
  { iFrame "# ∗". }
  unfold tuple_read.
  do 5 iExists _.
  iSplitL "Htidown Hvers HversS Htidlast".
  { eauto with iFrame. }
  iSplitL "Hvchain".
  { iFrame "% # ∗". }
  iFrame "%".
  iPureIntro.
  case_bool_decide.
  - change (int.Z (U64 1)) with 1. simpl.
    unfold spec_lookup. rewrite Hspec.
    by rewrite H.
  - change (int.Z (U64 0)) with 0. simpl.
    unfold spec_lookup. rewrite Hspec.
    apply not_true_is_false in H.
    by rewrite H.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) Release()                                 *)
(*****************************************************************)
Theorem wp_tuple__Release tuple (key : u64) (sid : u64) (latch : loc) γ :
  {{{ tuple_locked tuple key latch γ ∗ own_tuple tuple key γ }}}
    Tuple__Release #tuple
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[Hlocked Hown] HΦ".
  iNamed "Hlocked".
  wp_call.

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
(* func (tuple *Tuple) appendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__appendVersion tuple (tid : u64) (val : u64) tidown tidlast vers :
  {{{ own_tuple_phys tuple tidown tidlast vers }}}
    Tuple__appendVersion #tuple #tid #val
  {{{ RET #(); own_tuple_phys tuple (U64 0) (U64 (int.Z tid + 1)) (vers ++ [(tid, false, val)]) }}}.
Proof.
  iIntros (Φ) "Hphys HΦ".
  iNamed "Hphys".
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
  wp_apply (wp_SliceAppend with "[HversS]"); [done | auto 10 with iFrame |].
  iIntros (vers') "HversS". 
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
  iExactEq "HversS".
  unfold named.
  f_equal.
  by rewrite fmap_app.
Qed.

Definition tuple_appended tuple (tid : u64) (key : u64) (val : u64) γ : iProp Σ :=
  ∃ (tidown tidlast tidgc : u64) (vers : list pver)
    (vchain : list dbval),
    (* physical state is updated, but logical state is not. *)
    let vers' := vers ++ [(tid, false, val)] in
    "Hphys" ∷ own_tuple_phys tuple (U64 0) (U64 (int.Z tid + 1)) vers' ∗
    "Habst" ∷ own_tuple_abst key tidown tidlast tidgc vers vchain γ ∗
    "%Htid" ∷ ⌜int.Z tidgc ≤ int.Z tid⌝.

(*****************************************************************)
(* func (tuple *Tuple) AppendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__AppendVersion tuple (tid : u64) (val : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid }}}
    Tuple__AppendVersion #tuple #tid #val
  {{{ (latch : loc), RET #();
      active_tid γ tid sid ∗
      tuple_locked tuple key latch γ ∗
      tuple_appended tuple tid key val γ
  }}}.
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
  iNamed "Habst".
  
  (***********************************************************)
  (* tuple.appendVersion(tid, val)                           *)
  (***********************************************************)
  iNamed "Hphys".
  wp_apply (wp_tuple__appendVersion with "[$Htidown $Htidlast Hvers HversS]"); first eauto with iFrame.
  iIntros "Hphys".
  (* iNamed "HtuplePhys". *)
  wp_pures.
  
  (***********************************************************)
  (* tuple.rcond.Broadcast()                                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_condBroadcast with "[$HrcondC]").
  
  wp_pures.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (active_ge_min with "HinvgcO Hactive Hgclb") as "%HtidGe".
  iMod ("HinvgcC" with "HinvgcO") as "_".
  iModIntro.
  iApply "HΦ".
  iFrame "# ∗".
  unfold tuple_appended.
  do 5 iExists _.
  iFrame "Hphys".
  iSplit; last done.
  iFrame "% # ∗".
Qed.

(*****************************************************************)
(* func (tuple *Tuple) killVersion(tid uint64) bool              *)
(*****************************************************************)
Theorem wp_tuple__killVersion tuple (tid : u64) tidown tidlast vers :
  {{{ own_tuple_phys tuple tidown tidlast vers }}}
    Tuple__killVersion #tuple #tid
  {{{ (ok : bool), RET #ok; own_tuple_phys tuple (U64 0) (int.Z tid + 1) (vers ++ [(tid, true, (U64 0))]) }}}.
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
  wp_apply (wp_SliceAppend with "[HversS]"); [done | auto 10 with iFrame |].
  iIntros (vers') "HversS". 
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
  iExactEq "HversS".
  unfold named.
  f_equal.
  by rewrite fmap_app.
Qed.

Definition tuple_killed tuple (tid : u64) (key : u64) γ : iProp Σ :=
  ∃ (tidown tidlast tidgc : u64) (vers : list pver)
    (vchain : list dbval),
    (* physical state is updated, but logical state is not. *)
    let vers' := vers ++ [(tid, true, (U64 0))] in
    "Hphys" ∷ own_tuple_phys tuple (U64 0) (U64 (int.Z tid + 1)) vers' ∗
    "Habst" ∷ own_tuple_abst key tidown tidlast tidgc vers vchain γ ∗
    "%Htid" ∷ ⌜int.Z tidgc ≤ int.Z tid⌝.

(*****************************************************************)
(* func (tuple *Tuple) KillVersion(tid uint64) uint64            *)
(*****************************************************************)
Theorem wp_tuple__KillVersion tuple (tid : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid }}}
    Tuple__KillVersion #tuple #tid
  {{{ (latch : loc) (ret : u64), RET #ret;
      active_tid γ tid sid ∗
      tuple_locked tuple key latch γ ∗
      tuple_killed tuple tid key γ
  }}}.
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
  iNamed "Habst".

  (***********************************************************)
  (* ok := tuple.killVersion(tid)                            *)
  (***********************************************************)
  iNamed "Hphys".
  wp_apply (wp_tuple__killVersion with "[$Htidown $Htidlast Hvers HversS]"); first eauto with iFrame.
  iIntros (ok) "Hphys".
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
  wp_load.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (active_ge_min with "HinvgcO Hactive Hgclb") as "%HtidGe".
  iMod ("HinvgcC" with "HinvgcO") as "_".
  iModIntro.
  rewrite ite_apply.
  iApply "HΦ".
  iFrame "# ∗".
  unfold tuple_killed.
  do 5 iExists _.
  iFrame "Hphys".
  iSplit; last done.
  iFrame "% # ∗".
Qed.
  
(*****************************************************************)
(* func (tuple *Tuple) Free(tid uint64)                          *)
(*****************************************************************)
Theorem wp_tuple__Free tuple (tid : u64) (key : u64) (vers : list (u64 * u64 * u64)) γ :
  is_tuple tuple key γ -∗
  {{{ mods_token γ key tid }}}
    Tuple__Free #tuple #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Htoken HΦ".
  rename vers into vers'.
  iNamed "Htuple".
  wp_call.

  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iNamed "HtupleOwn".
  iNamed "Hphys".
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
  iNamed "Habst".
  wp_apply (release_spec with "[-HΦ]").
  { iFrame "Hlock Hlocked".
    iNext.
    iExists (U64 0).
    do 4 iExists _.
    iSplitL "Htidown Htidlast Hvers HversS".
    { eauto with iFrame. }
    iFrame "% # ∗".
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
  {{{ (ret : u64), RET #ret;
      active_tid γ tid sid ∗
      post_tuple__Own tid key ret γ
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
  iNamed "Hphys".
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
  iNamed "Habst".
  iDestruct (vchain_split (1 / 4) (1 / 4) with "Hvchain") as "[Hchain Hvchain']"; first compute_done.
  wp_apply (release_spec with "[-HΦ Hactive Hvchain']").
  { iFrame "Hlock Hlocked".
    iNext.
    iExists tid.
    do 4 iExists _.
    iSplitL "Htidown Htidlast Hvers HversS".
    { eauto with iFrame. }
    iFrame "% ∗".
    case_decide.
    - by rewrite H in Htid.
    - iFrame "# ∗".
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

Definition own_tuple_phys_vers tuple vers : iProp Σ :=
  ∃ versS,
    "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val versS) ∗
    "HversS" ∷ slice.is_slice versS (structTy Version) 1 (ver_to_val <$> vers).

(*****************************************************************)
(* func (tuple *Tuple) removeVersions(tid uint64)                *)
(*****************************************************************)
Theorem wp_tuple__removeVersions tuple (tid : u64) vers :
  {{{ own_tuple_phys_vers tuple vers ∧ ⌜vers ≠ []⌝ }}}
    Tuple__removeVersions #tuple #tid
  {{{ RET #();
        (∃ vers',
           own_tuple_phys_vers tuple vers' ∧
           (∃ vers_prefix, ⌜vers_prefix ≠ [] ∧ vers = vers_prefix ++ vers'⌝) ∧
           (⌜Forall (λ ver, int.Z tid ≤ int.Z ver.1.1) (tail vers')⌝) ∧
           (∃ ver, ⌜ver ∈ vers' ∧ int.Z ver.1.1 < int.Z tid⌝)) ∨
        (own_tuple_phys_vers tuple vers)
  }}}.
Proof.
  iIntros (Φ) "[HtuplePhys %Hnotnil] HΦ".
  iNamed "HtuplePhys".
  wp_call.

  iDestruct (is_slice_sz with "HversS") as "%HversLen".
  rewrite fmap_length in HversLen.
  iDestruct (is_slice_small_acc with "HversS") as "[HversX HversS]".

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
             "%Hbound" ∷ (⌜int.Z 0 ≤ int.Z idx < Z.of_nat (length vers)⌝) ∗
             "HidxR" ∷ idxR ↦[uint64T] #idx ∗
             "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val versS) ∗
             "HversX" ∷ is_slice_small versS (struct.t Version) 1 (ver_to_val <$> vers) ∗
             "%HallLe" ∷ (⌜Forall (λ ver, int.Z tid ≤ int.Z ver.1.1) (drop (S (int.nat idx)) vers)⌝) ∗
             "%Hexit" ∷ if b
                        then ⌜True⌝
                        else ⌜(int.Z idx = 0) ∨
                              (0 < int.Z idx ∧
                               ∃ ver, ver ∈ (drop (int.nat idx) vers) ∧
                               int.Z ver.1.1 < int.Z tid)⌝)%I.
  wp_apply (wp_forBreak P with "[] [-HΦ HversS]").
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
    destruct (list_lookup_lt _ (ver_to_val <$> vers) (int.nat idx)) as [ver HSome].
    { rewrite fmap_length. word. }
    wp_apply (wp_SliceGet with "[HversX]"); first auto.
    iIntros "[HversX %Hval_ty]".
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
    assert (Hgt : 0 < int.Z versS.(Slice.sz)).
    { destruct (nil_or_length_pos vers); first contradiction. word. }
    split; first word.
    split; last done.
    replace (S _) with (length vers); last word.
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

  iDestruct ("HversS" with "HversX") as "HversS".
  iDestruct "HversS" as "[HversX HversC]".
  iDestruct (slice.is_slice_small_take_drop _ _ _ idx with "HversX") as "[HversX _]"; first word.
  iDestruct (slice.is_slice_cap_skip _ _ idx with "HversC") as "HversC"; first word.
  iDestruct (slice.is_slice_split with "[$HversX $HversC]") as "HversS".
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
    set vers' := drop (int.nat idx) vers.
    iExists vers'.
    iSplit.
    { iExists _.
      iFrame.
    }
    iPureIntro.
    split.
    { exists (take (int.nat idx) vers).
      split.
      { apply length_nonzero_neq_nil.
        rewrite take_length_le; first word.
        word.
      }
      { symmetry. apply take_drop. }
    }
    split.
    { subst vers'.
      replace (tail _) with (drop (S (int.nat idx)) vers); first done.
      destruct vers; by rewrite drop_tail_commute.
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
  iIntros "#Htuple" (Φ) "!> #Hgclb' HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Htuple]".
  iNamed "Htuple".
  iNamed "Hphys".
  iNamed "Habst".
  iNamed "Hwellformed".
  wp_pures.

  (***********************************************************)
  (* tuple.removeVersions(tid)                               *)
  (***********************************************************)
  wp_apply (wp_tuple__removeVersions with "[Hvers HversS]").
  { unfold own_tuple_phys_vers. eauto with iFrame. }
  iIntros "HtuplePhys".
  
  iDestruct "HtuplePhys" as "[HtuplePhys | HtuplePhys]"; last first.
  { (* The list of physcial versions are not changed. *)
    iNamed "HtuplePhys".
    wp_pures.
    wp_loadField.
    iClear "Hgclb'".
    wp_apply (release_spec with "[-HΦ]"); first eauto 20 with iFrame.
    wp_pures.
    by iApply "HΦ".
  }

  (* The new list of physical versions is a suffix of the old one. *)
  iDestruct "HtuplePhys" as (vers') "(HtuplePhys & %Hsuffix & %HtailLe & %HtidGt)".
  clear versS.
  iNamed "HtuplePhys".
  wp_pures.

  assert (H2 : int.Z tidgc < int.Z tid).
  { destruct Hsuffix as [versPrefix [Hnotnil' Hsuffix]].
    destruct HtidGt as [verPivot [Hin HtidGt]].
    apply Z.le_lt_trans with (int.Z verPivot.1.1); last done.
    rewrite Forall_forall in HtidgcLe.
    apply HtidgcLe.
    rewrite Hsuffix.
    destruct versPrefix; first congruence.
    simpl.
    apply elem_of_app.
    by right.
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
    iExists tid, vers', vchain.
    iSplitL "Htidown Htidlast Hvers HversS".
    { eauto with iFrame. }
    iFrame "% # ∗".
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
