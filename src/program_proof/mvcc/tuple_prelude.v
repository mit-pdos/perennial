From Perennial.program_proof.mvcc Require Export mvcc_prelude mvcc_misc mvcc_ghost mvcc_inv.
From Goose.github_com.mit_pdos.go_mvcc Require Export tuple.

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
