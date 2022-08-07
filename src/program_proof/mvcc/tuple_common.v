(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Tactical Require Export SimplMatch.
From Perennial.program_proof Require Export grove_prelude.
(* Import Coq model of our Goose program.*)
From Goose.github_com.mit_pdos.go_mvcc Require Export tuple.
From Perennial.program_proof.mvcc Require Export mvcc_ghost mvcc_inv.
(* prefer untyped slices *)
Export Perennial.goose_lang.lib.slice.slice.

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

Lemma val_to_ver_with_lookup (x : val) (l : list (u64 * bool * u64)) (i : nat) :
  (ver_to_val <$> l) !! i = Some x ->
  (∃ (b : u64) (d : bool) (v : u64), x = ver_to_val (b, d, v) ∧ l !! i = Some (b, d, v)).
Proof.
  intros H.
  apply list_lookup_fmap_inv in H as [[[y1 y2] y3] [Heq Hsome]].
  naive_solver.
Qed.

Lemma spec_find_ver_step_Some_noop vers tid ver :
  foldl (spec_find_ver_step tid) (Some ver) vers = Some ver.
Proof.
  induction vers; done.
Qed.

Lemma spec_find_ver_lt_Some (vers : list pver) (tid : u64) (ver : pver) :
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

Lemma spec_find_ver_reverse_match vers tid :
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

Lemma spec_find_ver_reverse_not_match vers tid :
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

Lemma spec_find_ver_extensible vers (tidlast tid1 tid2 : u64) :
  int.Z tidlast ≤ int.Z tid1 ->
  int.Z tidlast ≤ int.Z tid2 ->
  Forall (λ ver, int.Z ver.1.1 < int.Z tidlast) vers ->
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
  { apply Hlast in H. apply Z.lt_le_trans with (int.Z tidlast); done. }
  assert (H2 : int.Z p.1.1 < int.Z tid2).
  { apply Hlast in H. apply Z.lt_le_trans with (int.Z tidlast); done. }
  apply Z.lt_gt in H1, H2.
  do 2 (case_decide; last contradiction).
  by do 2 rewrite spec_find_ver_step_Some_noop.
Qed.

Lemma spec_lookup_snoc_l vers ver (tid tidx : u64) :
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

Lemma spec_lookup_snoc_r vers ver (tid tidx : u64) :
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

Lemma spec_lookup_extensible vers (tidlast tid1 tid2 : u64) :
  int.Z tidlast ≤ int.Z tid1 ->
  int.Z tidlast ≤ int.Z tid2 ->
  Forall (λ ver, int.Z ver.1.1 < int.Z tidlast) vers ->
  spec_lookup vers tid1 = spec_lookup vers tid2.
Proof.
  intros Htid1 Htid2 Hlast.
  unfold spec_lookup.
  by rewrite (spec_find_ver_extensible _ _ _ _ Htid1 Htid2); last done.
Qed.

(* Q: Existing tactic does this? *)
Lemma ite_apply (A B : Type) (b : bool) (f : A -> B) x y :
  (if b then f x else f y) = f (if b then x else y).
Proof.
  destruct b; done.
Qed.

Section def.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition tuple_wellformed (vers : list pver) (tidlast tidgc : u64) : iProp Σ :=
  "%HtidlastGt" ∷ ⌜Forall (λ ver, int.Z ver.1.1 < int.Z tidlast) vers⌝ ∗
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

Definition own_tuple_repr
           (key : u64) (tidlast tidgc : u64) (vers : list pver) (vchain : list dbval) γ
  : iProp Σ :=
  "%HtupleAbs" ∷ (∀ tid, ⌜int.Z tidgc ≤ int.Z tid ≤ int.Z tidlast ->
                         vchain !! (int.nat tid) = Some (spec_lookup vers tid)⌝) ∗
  (* We need this as [HtupleAbs] is not useful when [tidlast < tidgc]. *)
  "%Hlast" ∷ ⌜last vchain = Some (spec_lookup vers tidlast)⌝ ∗
  "%HvchainLen" ∷ ⌜(Z.of_nat (length vchain)) = ((int.Z tidlast) + 1)%Z⌝ ∗
  "#Hgclb" ∷  min_tid_lb γ (int.nat tidgc) ∗
  "#Hwellformed" ∷ tuple_wellformed vers tidlast tidgc.

Definition own_tuple (tuple : loc) (key : u64) γ : iProp Σ :=
  ∃ (tidown tidlast tidgc : u64) (vers : list pver) (vchain : list dbval),
    "Hphys"   ∷ own_tuple_phys tuple tidown tidlast vers ∗
    "Hrepr"   ∷ own_tuple_repr key tidlast tidgc vers vchain γ ∗
    "Hptuple" ∷ ptuple_auth γ (if decide (tidown = (U64 0)) then (1/2) else (1/4))%Qp key vchain.

Definition own_tuple_read
           (tuple : loc) (key : u64) (tidown : u64) (vchain : list dbval) γ
  : iProp Σ :=
  ∃ (tidlast tidgc : u64) (vers : list pver),
    "Hphys" ∷ own_tuple_phys tuple tidown tidlast vers ∗
    "Hrepr" ∷ own_tuple_repr key tidlast tidgc vers vchain γ.

Definition is_tuple_locked tuple (key : u64) γ : iProp Σ :=
  ∃ (latch : loc) (rcond : loc),
    "#Hlatch" ∷ readonly (tuple ↦[Tuple :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_tuple tuple key γ) ∗
    "#Hrcond" ∷ readonly (tuple ↦[Tuple :: "rcond"] #rcond) ∗
    "#HrcondC" ∷ is_cond rcond #latch ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "Hlocked" ∷ locked #latch.

Definition own_tuple_locked
           (tuple : loc) (key : u64) (tid : u64) (vchain vchain' : list dbval) γ
  : iProp Σ :=
  ∃ (tidown tidlast tidgc : u64) (vers : list pver),
    "Hphys"   ∷ own_tuple_phys tuple tidown tidlast vers ∗
    "Hrepr"   ∷ own_tuple_repr key tidlast tidgc vers vchain γ ∗
    "Hlock"   ∷ is_tuple_locked tuple key γ ∗
    "Hptuple" ∷ ptuple_auth γ (1 / 2)%Qp key vchain' ∗
    "%Hlen"   ∷ ⌜(length vchain ≤ S (int.nat tid))%nat⌝.

Definition is_tuple (tuple : loc) (key : u64) γ : iProp Σ :=
  ∃ (latch : loc) (rcond : loc) (p : proph_id),
    "#Hlatch" ∷ readonly (tuple ↦[Tuple :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_tuple tuple key γ) ∗
    "#Hrcond" ∷ readonly (tuple ↦[Tuple :: "rcond"] #rcond) ∗
    "#HrcondC" ∷ is_cond rcond #latch ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "#Hinv"   ∷ mvcc_inv_sst γ p ∗
    "_" ∷ True.

End def.

#[global]
Hint Extern 1 (environments.envs_entails _ (own_tuple_phys _ _ _ _)) => unfold own_tuple_phys : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_tuple_repr _ _ _ _ _ _)) => unfold own_tuple_repr : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_tuple_read _ _ _ _ _)) => unfold own_tuple_read : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_tuple_locked _ _ _ _ _)) => unfold own_tuple_locked : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_tuple _ _ _)) => unfold own_tuple : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (is_tuple _ _ _)) => unfold is_tuple : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (is_tuple_locked _ _ _)) => unfold is_tuple_locked : core.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Lemma is_tuple_invgc tuple key γ :
  is_tuple tuple key γ -∗
  mvcc_inv_gc γ.
Proof. iIntros "Htuple". by iNamed "Htuple". Qed.

(* TODO: move this to [tuple_mk.v]. *)
(*****************************************************************)
(* func MkTuple() *Tuple                                         *)
(*****************************************************************)
Theorem wp_MkTuple (key : u64) γ p :
  mvcc_inv_gc γ -∗
  mvcc_inv_sst γ p -∗
  {{{ ptuple_auth γ (1/2) key [Nil; Nil] }}}
    MkTuple #()
  {{{ (tuple : loc), RET #tuple; is_tuple tuple key γ }}}.
Proof.
  iIntros "#Hinvgc #Hinv" (Φ) "!> Hvchain HΦ".
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
  iMod (min_tid_lb_zero γ) as "#Hlb".
  set P := (own_tuple tuple key γ)%I.
  iMod (alloc_lock mvccN _ latch P with "[$Hfree] [-latch rcond HΦ]") as "#Hlock".
  { iNext.
    unfold P.
    unfold own_tuple.
    iExists (U64 0), (U64 1), (U64 0), [(U64 0, true, U64 0)], [Nil; Nil].
    iFrame.
    iSplit.
    { iExists (Slice.mk vers 1 16). iFrame. }
    iSplit.
    { (* Prove [HtupleAbs]. *)
      iPureIntro.
      simpl.
      intros tid Htid.
      assert (H : int.Z tid = 0 ∨ int.Z tid = 1) by word.
      destruct H.
      - by replace tid with (U64 0) by word.
      - by replace tid with (U64 1) by word.
    }
    iSplit; first done.
    iSplit.
    { (* Prove [HvchainLen]. *)
      iPureIntro. set_solver.
    }
    iSplit.
    { (* Prove [Hgclb]. *)
      done.
    }
    iSplit.
    { (* Prove [HtidlastGt]. *)
      rewrite Forall_singleton.
      by simpl.
    }
    iPureIntro.
    split.
    { (* Prove [HexistsLt]. *)
      intros tid.
      rewrite Exists_cons.
      left. simpl. word.
    }
    split; [by simpl | done].
  }
  iApply "HΦ".
  do 3 iExists _.
  iMod (readonly_alloc_1 with "latch") as "$".
  iMod (readonly_alloc_1 with "rcond") as "$".
  by iFrame "#".
Qed.

End proof.
