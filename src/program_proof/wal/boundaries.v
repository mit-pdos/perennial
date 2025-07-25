From stdpp Require Import gmap.
From iris.algebra Require Import ofe.

From Perennial.Helpers Require Import List Integers.
From Perennial.program_proof Require Import abstraction.
From Perennial.program_proof Require Export wal.lib wal.highest.

Module mwrb.
  Record t := {
    txn : nat;
    upd : nat;
  }.
  Definition logend {A B} (txns: list A) (upds: list B) :=
    {| txn := length txns; upd := length upds |}.
End mwrb.

Theorem list_elem_of_insert_or {A} i (x: A) (l: list _) y :
  y ∈ <[i:=x]>l →
  y = x ∨ y ∈ l.
Proof.
  intros Hin.
  apply list_elem_of_lookup in Hin.
  destruct Hin as [j Hacc].
  destruct (decide (i = j)%nat) as [<-|Hj].
  {
    pose proof (lookup_lt_Some _ _ _ Hacc) as Hlt.
    rewrite length_insert in Hlt.
    rewrite list_lookup_insert_eq in Hacc; last by assumption.
    inversion Hacc; subst y; clear Hacc.
    left.
    reflexivity.
  }
  rewrite list_lookup_insert_ne in Hacc; last by assumption.
  right.
  apply list_elem_of_lookup_2 in Hacc.
  assumption.
Qed.

Theorem list_insert_filter_not {A} P `{∀ x, Decision (P x)} i old new (l: list A) :
  ¬ (P new) →
  ¬ (P old) →
  l !! i = Some old →
  filter P (<[i:=new]>l) = filter P l.
Proof.
  intros notnew notold.
  revert i.
  induction l as [|h l Hind]; first by trivial.
  intros i Hi.
  destruct i as [|i].
  {
    simpl.
    rewrite !filter_cons.
    simpl in Hi.
    inversion Hi; subst h; clear Hi.
    rewrite decide_False; last by assumption.
    rewrite decide_False; last by assumption.
    reflexivity.
  }
  simpl in Hi.
  apply Hind in Hi.
  rewrite !filter_cons !Hi //.
Qed.

Definition memLog_region_upds_match_some_txn (txns: list (u64 * _)) (upds: list _) :=
  ∀ upd,
    upd ∈ upds →
    ∃ txn,
      txn ∈ txns ∧
      ∀ d,
        apply_upds txn.2 d !! (uint.Z upd.(update.addr)) =
        Some upd.(update.b).

Definition is_memLog_region txns upds :=
  has_updates upds txns ∧
  memLog_region_upds_match_some_txn txns upds.

Definition is_memLog_boundaries txns upds (mwrbs: list _) :=
  (
    ∀ bndry,
      bndry ∈ mwrbs →
      (bndry.(mwrb.upd) ≤ length upds)%nat ∧
      (bndry.(mwrb.txn) ≤ length txns)%nat
  ) ∧
  ∀ i bndry1 bndry2,
    mwrbs !! i = Some bndry1 →
    mwrbs !! S i = Some bndry2 → (
      (bndry1.(mwrb.upd) ≤ bndry2.(mwrb.upd))%nat ∧
      (bndry1.(mwrb.txn) ≤ bndry2.(mwrb.txn))%nat ∧
      is_memLog_region
        (subslice bndry1.(mwrb.txn) bndry2.(mwrb.txn) txns)
        (subslice bndry1.(mwrb.upd) bndry2.(mwrb.upd) upds)
    ).

Theorem is_memLog_region_nil :
  is_memLog_region [] [].
Proof.
  split; first by apply has_updates_nil.
  intros upd Hin.
  apply elem_of_nil in Hin.
  contradiction.
Qed.

Theorem is_memLog_region_app txns1 txns2 upds1 upds2 :
  is_memLog_region txns1 upds1 →
  is_memLog_region txns2 upds2 →
  is_memLog_region (txns1 ++ txns2) (upds1 ++ upds2).
Proof.
  intros Hreg1 Hreg2.
  destruct Hreg1 as [Hhas1 Hmatch1].
  destruct Hreg2 as [Hhas2 Hmatch2].
  split.
  1: apply has_updates_app; assumption.
  intros upd Hupdin.
  apply elem_of_app in Hupdin.
  destruct Hupdin as [Hupdin|Hupdin].
  - destruct (Hmatch1 _ Hupdin) as [txn [Htin Hhas]].
    exists txn.
    split; last by assumption.
    apply elem_of_app.
    intuition.
  - destruct (Hmatch2 _ Hupdin) as [txn [Htin Hhas]].
    exists txn.
    split; last by assumption.
    apply elem_of_app.
    intuition.
Qed.

Theorem is_memLog_boundaries_region_consec i txns upds mwrbs bndry1 bndry2 :
  is_memLog_boundaries txns upds mwrbs →
  mwrbs !! i = Some bndry1 →
  mwrbs !! S i = Some bndry2 →
  (bndry1.(mwrb.upd) ≤ bndry2.(mwrb.upd))%nat ∧
  (bndry1.(mwrb.txn) ≤ bndry2.(mwrb.txn))%nat ∧
  is_memLog_region
    (subslice bndry1.(mwrb.txn) bndry2.(mwrb.txn) txns)
    (subslice bndry1.(mwrb.upd) bndry2.(mwrb.upd) upds).
Proof.
  intros Hbndrys Hbndry1 Hbndry2.
  destruct Hbndrys as (_&Hbndrys).
  apply (Hbndrys _ _ _ Hbndry1 Hbndry2).
Qed.

Local Lemma is_memLog_boundaries_region_ind i j txns upds mwrbs bndry1 bndry2 :
  is_memLog_boundaries txns upds mwrbs →
  mwrbs !! i = Some bndry1 →
  mwrbs !! (i + j)%nat = Some bndry2 →
  (bndry1.(mwrb.upd) ≤ bndry2.(mwrb.upd))%nat ∧
  (bndry1.(mwrb.txn) ≤ bndry2.(mwrb.txn))%nat ∧
  is_memLog_region
    (subslice bndry1.(mwrb.txn) bndry2.(mwrb.txn) txns)
    (subslice bndry1.(mwrb.upd) bndry2.(mwrb.upd) upds).
Proof.
  revert bndry2.
  induction j as [|j' Hind].
  {
    intros bndry2 Hbndrys Hbndry1 Hbndry2.
    rewrite Nat.add_0_r Hbndry1 in Hbndry2.
    inversion Hbndry2; subst bndry2; clear Hbndry2.
    rewrite !subslice_zero_length.
    split; first by lia.
    split; first by lia.
    apply is_memLog_region_nil.
  }
  intros bndry3 Hbndrys Hbndry1 Hbndry3.
  pose proof (lookup_lt_Some _ _ _ Hbndry3) as HiSj'bnd.
  assert (i + j' < length mwrbs)%nat as Hij'bnd by lia.
  apply list_lookup_lt in Hij'bnd.
  destruct Hij'bnd as [bndry2 Hbndry2].
  replace (i + S j')%nat with (S (i + j')%nat) in Hbndry3 by lia.
  specialize (Hind _ Hbndrys Hbndry1 Hbndry2) as (Hubnd1&Htbnd1&Hreg1).
  pose proof (
    is_memLog_boundaries_region_consec _ _ _ _ _ _ Hbndrys Hbndry2 Hbndry3
  ) as (Hubnd2&Htbnd2&Hreg2).
  split; first by lia.
  split; first by lia.
  rewrite (
    subslice_split_r bndry1.(mwrb.upd) bndry2.(mwrb.upd) bndry3.(mwrb.upd)
  ).
  2: lia.
  2: {
    destruct Hbndrys as (Hbnds&_).
    unshelve (eapply (Hbnds bndry2 _)).
    eapply list_elem_of_lookup_2.
    eassumption.
  }
  rewrite (
    subslice_split_r bndry1.(mwrb.txn) bndry2.(mwrb.txn) bndry3.(mwrb.txn)
  ).
  2: lia.
  2: {
    destruct Hbndrys as (Hbnds&_).
    unshelve (eapply (Hbnds bndry2 _)).
    eapply list_elem_of_lookup_2.
    eassumption.
  }
  apply is_memLog_region_app; assumption.
Qed.

Theorem is_memLog_boundaries_region i j txns upds mwrbs bndry1 bndry2 :
  (i ≤ j)%nat →
  is_memLog_boundaries txns upds mwrbs →
  mwrbs !! i = Some bndry1 →
  mwrbs !! j = Some bndry2 →
  (bndry1.(mwrb.upd) ≤ bndry2.(mwrb.upd))%nat ∧
  (bndry1.(mwrb.txn) ≤ bndry2.(mwrb.txn))%nat ∧
  is_memLog_region
    (subslice bndry1.(mwrb.txn) bndry2.(mwrb.txn) txns)
    (subslice bndry1.(mwrb.upd) bndry2.(mwrb.upd) upds).
Proof.
  intros Hleq.
  replace j with (i + (j - i))%nat by lia.
  apply is_memLog_boundaries_region_ind.
Qed.

Theorem is_memLog_boundaries_take_txns txns upds mwrbs t :
  mwrb.txn <$> last mwrbs = Some t →
  is_memLog_boundaries txns upds mwrbs →
  is_memLog_boundaries (take t txns) upds mwrbs.
Proof.
  intros Hlast Hbndrys.
  pose proof Hbndrys as [Hbnds Hreg].
  apply fmap_Some in Hlast.
  destruct Hlast as [blast [Hlast ->]].
  rewrite last_lookup in Hlast.
  pose proof (Hbnds _ (list_elem_of_lookup_2 _ _ _ Hlast)) as Hlastbnd.
  split.
  {
    intros bndry Hbndry.
    rewrite length_take.
    apply list_elem_of_lookup in Hbndry.
    destruct Hbndry as [i Hbndry].
    unshelve (
      epose proof (
        is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hbndry Hlast
      ) as Hbndrylast
    ).
    {
      apply lookup_lt_Some in Hbndry.
      lia.
    }
    lia.
  }
  intros i bndry1 bndry2 Hbndry1 Hbndry2.
  pose proof (Hreg _ _ _ Hbndry1 Hbndry2) as Hreg'.
  rewrite subslice_take.
  rewrite Nat.min_l.
  2: {
    unshelve (
      epose proof (
        is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hbndry2 Hlast
      ) as Hbndrylast
    ).
    {
      apply lookup_lt_Some in Hbndry2.
      lia.
    }
    lia.
  }
  intuition.
Qed.

Theorem is_memLog_boundaries_drop_upds txns upds mwrbs u :
  mwrb.upd <$> mwrbs !! 0%nat = Some u →
  is_memLog_boundaries txns upds mwrbs →
  is_memLog_boundaries
    txns (drop u upds)
    (
      (λ b,
        {| mwrb.txn := b.(mwrb.txn); mwrb.upd := b.(mwrb.upd) - u; |}
      ) <$> mwrbs
    ).
Proof.
  intros Hhead Hbndrys.
  pose proof Hbndrys as [Hbnds Hreg].
  apply fmap_Some in Hhead.
  destruct Hhead as [bhead [Hhead ->]].
  split.
  {
    rewrite length_drop.
    intros bndry Hbndry.
    apply list_elem_of_fmap_1 in Hbndry.
    destruct Hbndry as [bndry' [-> Hbndry'in]].
    simpl.
    apply Hbnds in Hbndry'in.
    lia.
  }
  intros i bndry1 bndry2 Hbndry1 Hbndry2.
  rewrite list_lookup_fmap in Hbndry1.
  rewrite list_lookup_fmap in Hbndry2.
  apply fmap_Some_1 in Hbndry1.
  apply fmap_Some_1 in Hbndry2.
  destruct Hbndry1 as [bndry1' [Hbndry1 ->]].
  destruct Hbndry2 as [bndry2' [Hbndry2 ->]].
  simpl.
  pose proof (Hreg _ _ _ Hbndry1 Hbndry2) as Hreg'.
  unshelve (
    epose proof (
      is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hhead Hbndry1
    ) as Hbndryhead
  ); first by lia.
  split; first by lia.
  split; first by lia.
  rewrite subslice_drop.
  rewrite -Nat.le_add_sub; last by lia.
  rewrite -Nat.le_add_sub; last by lia.
  intuition.
Qed.

Theorem is_memLog_boundaries_append_txns txns upds mwrbs txns' :
  is_memLog_boundaries txns upds mwrbs →
  is_memLog_boundaries (txns ++ txns') upds mwrbs.
Proof.
  intros Hbndrys.
  pose proof Hbndrys as [Hbnds Hreg].
  split.
  {
    intros bndry Hbndry.
    apply Hbnds in Hbndry.
    rewrite length_app.
    lia.
  }
  intros i bndry1 bndry2 Hbndry1 Hbndry2.
  pose proof (Hreg _ _ _ Hbndry1 Hbndry2) as Hreg'.
  rewrite subslice_app_1.
  2: {
    apply list_elem_of_lookup_2 in Hbndry2.
    apply Hbnds in Hbndry2.
    lia.
  }
  assumption.
Qed.

Theorem is_memLog_boundaries_move txns upds mwrbs i rbnd :
  is_memLog_boundaries txns upds mwrbs →
  mwrbs !! S i = Some rbnd →
  is_memLog_boundaries txns upds (<[i:=rbnd]>mwrbs).
Proof.
  intros Hbndrys Hrbnd.
  pose proof Hbndrys as (Hbndrys_len&_).
  pose proof (lookup_lt_Some _ _ _ Hrbnd) as HSilen.
  assert (i < length mwrbs)%nat as Hilen by lia.
  destruct (list_lookup_lt _ _ Hilen) as [lbnd Hlbnd].
  split.
  {
    intros bndry Hbndry.
    apply Hbndrys_len.
    destruct (list_elem_of_lookup_1 _ _ Hbndry) as [i' Hset].
    destruct (decide (i = i')) as [->|Hi'].
    {
      rewrite list_lookup_insert_eq in Hset; last by assumption.
      inversion Hset; subst bndry; clear Hset.
      apply (list_elem_of_lookup_2 _ _ _ Hrbnd).
    }
    rewrite (list_lookup_insert_ne _ _ _ _ Hi') in Hset.
    apply (list_elem_of_lookup_2 _ _ _ Hset).
  }

  intros i' bndry1 bndry2 Hbndry1 Hbndry2.

  destruct (decide (i = i')) as [->|Hi_i'].
  {
    rewrite list_lookup_insert_eq in Hbndry1; last by assumption.
    rewrite list_lookup_insert_ne in Hbndry2; last by lia.
    rewrite Hrbnd in Hbndry2.
    inversion Hbndry2; subst rbnd; clear Hbndry2.
    inversion Hbndry1; subst bndry2; clear Hbndry1.

    rewrite !subslice_zero_length.
    split; first by lia.
    split; first by lia.
    apply is_memLog_region_nil.
  }
  rewrite list_lookup_insert_ne in Hbndry1; last by assumption.
  destruct (decide (i = S i')) as [->|Hi_Si'].
  2: {
    rewrite list_lookup_insert_ne in Hbndry2; last by assumption.
    eapply is_memLog_boundaries_region.
    2-4: eassumption.
    lia.
  }
  rewrite list_lookup_insert_eq in Hbndry2; last by assumption.
  inversion Hbndry2; subst bndry2; clear Hbndry2.
  eapply is_memLog_boundaries_region.
  2-4: eassumption.
  lia.
Qed.

Definition memWrite_one_generic u_us (upds: list _) upd :=
  match find_highest_index (update.addr <$> upds) upd.(update.addr) with
  | Some u =>
    if decide (u_us ≤ u)%nat then
      <[u:=upd]>upds
    else
      upds ++ [upd]
  | None => upds ++ [upd]
  end.

Definition memWrite_generic u_us upds upds' :=
  foldl (memWrite_one_generic u_us) upds upds'.

Theorem memWrite_one_generic_split u_us upds upd' :
  (u_us ≤ length upds)%nat →
  memWrite_one_generic u_us upds upd' =
  (take u_us upds) ++ (memWrite_one_generic 0%nat (drop u_us upds) upd').
Proof.
  intros Hu_us.
  apply list_eq.
  intros i.
  destruct (decide (i < u_us)%nat) as [Hlt|Hgeq].
  {
    assert (i < length (take u_us upds))%nat as Hi;
      first by (rewrite length_take; lia).
    destruct (list_lookup_lt _ _ Hi) as [upd Hupd].
    rewrite (lookup_app_l_Some _ _ _ upd); last by assumption.
    rewrite /memWrite_one_generic.
    apply lookup_take_Some in Hupd.
    destruct (find_highest_index (update.addr <$> upds) upd'.(update.addr))
      as [i'|] eqn:Hi'.
    2: {
      rewrite lookup_app_l; last by lia.
      intuition.
    }
    destruct (decide (u_us ≤ i')%nat) as [Hi'bnd|Hi'bnd].
    2: {
      rewrite lookup_app_l; last by lia.
      intuition.
    }
    rewrite list_lookup_insert_ne; last by lia.
    intuition.
  }
  apply not_lt in Hgeq.
  rewrite lookup_app_r; last by (rewrite length_take; lia).
  rewrite length_take Nat.min_l; last by lia.
  rewrite /memWrite_one_generic.
  rewrite <- (take_drop u_us upds) at 1.
  rewrite /memWrite_one_generic fmap_app find_highest_index_app /=.
  destruct (
    find_highest_index (update.addr <$> drop u_us upds) upd'.(update.addr)
  ) as [opthi|] eqn:Hopthi.
  2: {
    replace (i - u_us)%nat with (i - length (take u_us upds))%nat.
    2: {
      rewrite length_take.
      f_equal.
      lia.
    }
    rewrite -lookup_app_r.
    2: {
      rewrite length_take.
      lia.
    }
    rewrite app_assoc take_drop.
    destruct (
      find_highest_index (update.addr <$> take u_us upds) upd'.(update.addr)
    ) as [opthi'|] eqn:Hopthi';
      last by reflexivity.
    destruct (decide (u_us ≤ opthi')%nat) as [Hleq|Hgt]; last by reflexivity.
    apply find_highest_index_Some in Hopthi'.
    destruct Hopthi' as [Hin _].
    apply list_lookup_fmap_Some_1 in Hin.
    destruct Hin as [upd'' [_ Hin'']].
    apply lookup_lt_Some in Hin''.
    rewrite length_take in Hin''.
    lia.
  }
  rewrite length_fmap length_take decide_True; last by lia.
  rewrite Nat.min_l; last by lia.
  rewrite <- (take_drop u_us upds) at 1.
  rewrite insert_app_r_alt length_take; last by lia.
  rewrite Nat.min_l; last by lia.
  rewrite Nat.add_sub'.
  rewrite lookup_app_r; last by (rewrite length_take; lia).
  rewrite length_take.
  f_equal.
  lia.
Qed.

Local Lemma apply_upds_lookup_in_ind upds1 iupd upds2 d :
  let upds := upds1 ++ iupd :: upds2 in
  highest_index_is
    (update.addr <$> upds)
    iupd.(update.addr) (length upds1) →
  apply_upds upds d !! (uint.Z iupd.(update.addr)) = Some iupd.(update.b).
Proof.
  simpl.
  revert d.
  induction upds1 as [|upd upds1 Hind].
  {
    destruct iupd as [iupda iupdb].
    simpl.
    intros d [_ Hhighest].
    rewrite apply_upds_notin'; first by rewrite lookup_insert_eq //.
    intros Hin.
    apply list_elem_of_fmap_1 in Hin.
    destruct Hin as [iupd [Hiupd Hin]].
    apply word.unsigned_inj in Hiupd.
    subst iupda.
    apply list_elem_of_lookup_1 in Hin.
    destruct Hin as [i Hin].
    assert (S i ≤ 0)%nat; last by lia.
    apply Hhighest.
    rewrite /= list_lookup_fmap Hin //.
  }
  destruct upd as [upda updb].
  simpl.
  intros d Hhighest.
  apply highest_index_is_cons in Hhighest.
  eapply Hind in Hhighest.
  apply Hhighest.
Qed.

Theorem apply_upds_lookup_in upds a i iupd d :
  highest_index_is (update.addr <$> upds) a i →
  upds !! i = Some iupd →
  apply_upds upds d !! (uint.Z a) = Some iupd.(update.b).
Proof.
  intros Hhighest Hiupd.
  pose proof Hhighest as [Ha _].
  rewrite list_lookup_fmap Hiupd /= in Ha.
  inversion Ha; subst a; clear Ha.
  apply list_elem_of_split_length in Hiupd.
  destruct Hiupd as (upds1&upds2&[-> ->]).
  apply apply_upds_lookup_in_ind.
  assumption.
Qed.

Theorem apply_upds_lookup_filter upds d a :
  apply_upds upds d !! a =
  match last (filter (λ u, uint.Z u.(update.addr) = a) upds) with
  | Some upd => Some upd.(update.b)
  | None => d !! a
  end.
Proof.
  rewrite -(rev_involutive upds).
  induction (rev upds) as [|upd updst Hind]; first by trivial.
  rewrite /= filter_app.
  unfold filter at 2.
  rewrite /= filter_nil apply_upds_app.
  destruct upd as [upda updb].
  simpl.
  destruct (decide (a = uint.Z upda)) as [->|Ha].
  {
    rewrite lookup_insert_eq decide_True; last by reflexivity.
    rewrite last_snoc //.
  }
  rewrite lookup_insert_ne; last by lia.
  rewrite decide_False; last by lia.
  rewrite app_nil_r.
  apply Hind.
Qed.

Theorem list_filter_nil_Forall {A} P `{∀ x, Decision (P x)} (l: list A) :
  filter P l = [] ↔ Forall (λ x, ¬ P x) l.
Proof.
  split.
  {
    induction l as [|x l Hind].
    {
      intros _.
      apply Forall_nil_2.
    }
    intros Hnil.
    rewrite filter_cons in Hnil.
    destruct (decide (P x)) as [HP|HP]; first by inversion Hnil.
    apply Hind in Hnil.
    apply Forall_cons_2; assumption.
  }
  intros HForall.
  apply elem_of_nil_inv.
  intros x Hin.
  apply list_elem_of_filter in Hin.
  destruct Hin as [HP Hin].
  apply (((iffLR (Forall_forall _ _)) HForall) _ Hin).
  assumption.
Qed.

Local Lemma memWrite_one_generic_0_apply_upds upds upd' d :
  apply_upds (memWrite_one_generic 0%nat upds upd') d =
  apply_upds (upds ++ [upd']) d.
Proof.
  rewrite /memWrite_one_generic.
  destruct (find_highest_index _ _) as [i|] eqn:Hhighest;
    last by reflexivity.
  apply find_highest_index_Some in Hhighest.
  (* TODO: Figure out why decide_True doesn't work here *)
  destruct (decide (0 <= i)%nat) as [_|]; last by lia.
  apply map_eq.
  intros a.

  pose proof Hhighest as [Hi_bnd _].
  apply lookup_lt_Some in Hi_bnd.
  rewrite length_fmap in Hi_bnd.
  pose proof Hhighest as [Hi _].
  rewrite list_lookup_fmap in Hi.
  apply fmap_Some_1 in Hi.
  destruct Hi as [oldupd [Holdupd Holdupdaddr]].

  rewrite !apply_upds_lookup_filter.
  destruct (last _) as [updopt1|] eqn:Hupdopt1.
  2: {
    apply last_None in Hupdopt1.
    apply list_filter_nil_Forall in Hupdopt1.
    replace (filter _ _) with ([]: list update.t); first by trivial.
    symmetry.
    apply list_filter_nil_Forall.
    apply Forall_forall.
    intros upd Hin.
    destruct (decide (upd.(update.addr) = upd'.(update.addr)))
      as [Haddr|Haddr].
    {
      rewrite Haddr.
      apply ((iffLR (Forall_forall _ _)) Hupdopt1).
      apply list_elem_of_insert.
      assumption.
    }
    apply elem_of_app in Hin.
    destruct Hin as [Hin|Hin].
    2: {
      apply list_elem_of_singleton in Hin.
      subst upd'.
      contradiction.
    }
    apply ((iffLR (Forall_forall _ _)) Hupdopt1).
    rewrite Holdupdaddr in Haddr.
    apply list_elem_of_lookup.
    apply list_elem_of_lookup in Hin.
    destruct Hin as [updi Hupdi].
    exists updi.
    rewrite list_lookup_insert_ne; first by assumption.
    intros <-.
    rewrite Holdupd in Hupdi.
    inversion Hupdi; subst oldupd; clear Hupdi.
    contradiction.
  }
  destruct (last (filter _ (_ ++ _))) as [updopt2|] eqn:Hupdopt2.
  2: {
    apply last_None in Hupdopt2.
    apply list_filter_nil_Forall in Hupdopt2.
    apply mk_is_Some in Hupdopt1.
    apply last_is_Some in Hupdopt1.
    exfalso.
    apply Hupdopt1.
    apply list_filter_nil_Forall.
    apply Forall_forall.
    intros upd Hin.
    apply ((iffLR (Forall_forall _ _)) Hupdopt2).
    apply elem_of_app.
    apply list_elem_of_insert_or in Hin.
    destruct Hin as [<-|Hin]; last by intuition.
    right.
    apply list_elem_of_singleton.
    reflexivity.
  }
  rewrite filter_app in Hupdopt2.
  destruct (decide (a = uint.Z upd'.(update.addr))) as [->|Ha].
  2: {
    rewrite filter_cons_False in Hupdopt2; last by trivial.
    rewrite filter_nil app_nil_r in Hupdopt2.
    rewrite (list_insert_filter_not _ _ oldupd) in Hupdopt1;
      last by assumption.
    2: lia.
    2: rewrite -Holdupdaddr; lia.
    rewrite Hupdopt2 in Hupdopt1.
    inversion Hupdopt1; subst updopt2; clear Hupdopt1.
    reflexivity.
  }
  rewrite filter_cons_True in Hupdopt2; last by reflexivity.
  rewrite filter_nil in Hupdopt2.
  rewrite last_snoc in Hupdopt2.
  inversion Hupdopt2; subst updopt2; clear Hupdopt2.
  pose proof (highest_index_is_drop _ _ _ Hhighest) as Hdrop.
  rewrite -(take_drop (S i) (<[_:=_]>_)) filter_app in Hupdopt1.
  rewrite (iffRL (list_filter_nil_Forall _ (drop _ _))) in Hupdopt1.
  2: {
    apply Forall_forall.
    intros upd Hupd Haddr.
    apply word.unsigned_inj in Haddr.
    rewrite -Haddr -fmap_drop in Hdrop.
    rewrite drop_insert_lt in Hupd; last by lia.
    apply Hdrop.
    apply list_elem_of_fmap_2.
    assumption.
  }
  rewrite app_nil_r in Hupdopt1.
  erewrite take_S_r in Hupdopt1; last by rewrite list_lookup_insert_eq //.
  rewrite filter_app filter_cons_True in Hupdopt1; last by trivial.
  rewrite filter_nil last_snoc in Hupdopt1.
  inversion Hupdopt1; subst updopt1; clear Hupdopt1.
  reflexivity.
Qed.

Local Lemma memWrite_generic_0_apply_upds upds upds' d :
  apply_upds (memWrite_generic 0%nat upds upds') d =
  apply_upds (upds ++ upds') d.
Proof.
  rewrite /memWrite_generic.
  rewrite -(rev_involutive upds').
  induction (rev upds') as [|upd' upds't Hind].
  1: rewrite app_nil_r //.
  rewrite /= foldl_app /=.
  rewrite memWrite_one_generic_0_apply_upds app_assoc apply_upds_app Hind
    !apply_upds_app //.
Qed.

Theorem memWrite_generic_has_updates txns upds txn :
  has_updates upds txns →
  has_updates (memWrite_generic 0%nat upds txn.2) (txns ++ [txn]).
Proof.
  rewrite /has_updates /txn_upds.
  intros Hhas d.
  rewrite fmap_app concat_app apply_upds_app -Hhas /=
    app_nil_r -apply_upds_app memWrite_generic_0_apply_upds //.
Qed.

Theorem memWrite_generic_split u_us upds aupds :
  (u_us ≤ length upds)%nat →
  memWrite_generic u_us upds aupds =
  (take u_us upds) ++ (memWrite_generic 0%nat (drop u_us upds) aupds).
Proof.
  intros Hu_us.
  rewrite -(rev_involutive aupds).
  induction (rev aupds); first by rewrite take_drop //.
  simpl.
  rewrite /memWrite_generic !foldl_app /=.
  rewrite /memWrite_generic in IHl.
  rewrite IHl.
  rewrite memWrite_one_generic_split.
  2: {
    rewrite length_app length_take.
    lia.
  }
  rewrite take_app_le.
  2: rewrite length_take; lia.
  rewrite take_take Nat.min_id.
  rewrite drop_app_length'; last by (rewrite length_take; lia).
  reflexivity.
Qed.


Theorem memWrite_generic_apply_upds u_us upds upds' d :
  (u_us ≤ length upds)%nat →
  apply_upds (memWrite_generic u_us upds upds') d =
  apply_upds (upds ++ upds') d.
Proof.
  intros Hbnd.
  rewrite memWrite_generic_split; last by assumption.
  rewrite <- (take_drop u_us upds) at 3.
  rewrite -app_assoc.
  rewrite apply_upds_app apply_upds_app.
  apply memWrite_generic_0_apply_upds.
Qed.

Local Lemma memWrite_one_generic_or u_us upds aupd :
  (∃ u,
    highest_index_is (update.addr <$> upds) aupd.(update.addr) u ∧
    (u_us ≤ u)%nat ∧
    memWrite_one_generic u_us upds aupd = <[u:=aupd]> upds
  ) ∨ memWrite_one_generic u_us upds aupd = upds ++ [aupd].
Proof.
  remember (memWrite_one_generic u_us upds aupd) as newupds.
  destruct (Classical_Prop.classic (
    newupds = upds ++ [aupd]
  )) as [-> | HmemWrite]; first by intuition.
  left.
  rewrite /memWrite_one_generic in Heqnewupds.
  destruct (find_highest_index _ _) as [i|] eqn:Hhighest in Heqnewupds;
    last by contradiction.
  destruct (decide _) as [Hbnd|_] in Heqnewupds;
    last by contradiction.
  apply find_highest_index_Some in Hhighest.
  eexists.
  split; first by eassumption.
  intuition.
Qed.

Lemma memWrite_one_generic_apply_upds_lookup u_us upds aupd d a :
  apply_upds (memWrite_one_generic u_us upds aupd) d !! uint.Z a =
  if decide (aupd.(update.addr) = a)
  then Some aupd.(update.b)
  else apply_upds upds d !! uint.Z a.
Proof.
  rewrite apply_upds_lookup_filter.
  pose proof (memWrite_one_generic_or u_us upds aupd) as HmemWrite.
  destruct (last _) as [lastupd|] eqn:Hlast.
  2: {
    apply last_None in Hlast.
    apply list_filter_nil_Forall in Hlast.
    destruct HmemWrite as [[u ([Hacc _]&_&HmemWrite)] | HmemWrite].
    2: {
      rewrite HmemWrite in Hlast.
      apply Forall_app in Hlast.
      destruct Hlast as [Hlast Haupd].
      apply (iffLR (Forall_singleton _ _)) in Haupd.
      simpl in Haupd.
      destruct (decide _) as [<-|Hneq]; first by contradiction.
      rewrite apply_upds_notin; first by reflexivity.
      intros Hin.
      apply list_elem_of_fmap_1 in Hin.
      destruct Hin as [i [-> Hin]].
      apply ((iffLR (Forall_forall _ _)) Hlast) in Hin.
      contradiction.
    }
    rewrite HmemWrite in Hlast.
    destruct (decide _) as [<-|Hneq].
    {
      unshelve (
        epose proof (((iffLR (Forall_forall _ _)) Hlast) _ _) as Haddr
      ).
      2: {
        apply list_elem_of_insert.
        apply lookup_lt_Some in Hacc.
        rewrite length_fmap in Hacc.
        assumption.
      }
      contradiction.
    }
    rewrite apply_upds_notin'; first by reflexivity.
    intros Hin.
    apply list_elem_of_fmap_1 in Hin.
    destruct Hin as [upd [Haddr Hin]].
    unshelve (
      epose proof (((iffLR (Forall_forall _ _)) Hlast) upd _) as Haddr'
    ).
    2: {
      simpl in Haddr'.
      rewrite Haddr // in Haddr'.
    }
    apply word.unsigned_inj in Haddr.
    subst a.
    apply list_elem_of_lookup.
    apply list_elem_of_lookup in Hin.
    destruct Hin as [j Hin].
    exists j.
    rewrite list_lookup_insert_ne; first by assumption.
    intros <-.
    rewrite list_lookup_fmap in Hacc.
    rewrite Hin in Hacc.
    simpl in Hacc.
    inversion Hacc as [Haddr].
    rewrite Haddr in Hneq.
    contradiction.
  }
  destruct HmemWrite as [[u (Hhighest&_&HmemWrite)] | HmemWrite].
  2: {
    rewrite HmemWrite in Hlast.
    rewrite filter_app in Hlast.
    destruct (decide _) as [<-|Hneq].
    {
      rewrite filter_cons_True in Hlast; last by reflexivity.
      rewrite filter_nil last_snoc in Hlast.
      inversion Hlast; subst lastupd.
      reflexivity.
    }
    rewrite filter_cons_False in Hlast.
    2: {
      intros Haddr.
      apply word.unsigned_inj in Haddr.
      subst a.
      contradiction.
    }
    rewrite filter_nil app_nil_r in Hlast.
    rewrite apply_upds_lookup_filter Hlast //.
  }
  rewrite HmemWrite in Hlast.
  pose proof Hhighest as [Hacc _].
  apply list_lookup_fmap_Some_1 in Hacc.
  destruct Hacc as [oldupd [Holdupdaddr Hacc]].
  destruct (decide _) as [<-|Hneq].
  2: {
    rewrite apply_upds_lookup_filter.
    rewrite (list_insert_filter_not _ _ oldupd) in Hlast;
      last by assumption.
    2: {
      intros Haddr.
      apply word.unsigned_inj in Haddr.
      contradiction.
    }
    2: {
      intros Haddr.
      apply word.unsigned_inj in Haddr.
      rewrite Holdupdaddr in Hneq.
      contradiction.
    }
    rewrite Hlast //.
  }
  pose proof (lookup_lt_Some _ _ _ Hacc) as Hubnd.
  rewrite -(take_drop (S u) upds) insert_app_l in Hlast.
  2: rewrite length_take; lia.
  rewrite filter_app in Hlast.
  rewrite (iffRL (list_filter_nil_Forall _ (drop _ _))) in Hlast.
  2: {
    apply highest_index_is_drop in Hhighest.
    apply Forall_forall.
    intros upd Hin Haddr.
    apply word.unsigned_inj in Haddr.
    rewrite -Haddr -fmap_drop in Hhighest.
    apply Hhighest.
    apply list_elem_of_fmap_2.
    assumption.
  }
  rewrite app_nil_r in Hlast.
  erewrite take_S_r in Hlast; last by eassumption.
  rewrite insert_app_r_alt in Hlast.
  2: rewrite length_take; lia.
  rewrite length_take Nat.min_l in Hlast; last by lia.
  rewrite Nat.sub_diag /= filter_app filter_cons_True in Hlast;
    last by reflexivity.
  rewrite filter_nil last_snoc in Hlast.
  inversion Hlast.
  reflexivity.
Qed.

Theorem memWrite_generic_apply_upds_lookup u_us upds aupds d a :
  apply_upds (memWrite_generic u_us upds aupds) d !! uint.Z a =
  match last (filter (λ u, u.(update.addr) = a) aupds) with
  | Some aupd => Some aupd.(update.b)
  | None => apply_upds upds d !! uint.Z a
  end.
Proof.
  revert upds.
  induction aupds as [|aupd aupds Hind]; first by trivial.
  simpl.
  intros upds.
  rewrite Hind memWrite_one_generic_apply_upds_lookup filter_cons.
  destruct (decide _) as [<-|Haddr]; last by reflexivity.
  rewrite last_cons.
  destruct (last _) as [lastupd|] eqn:Hlast; reflexivity.
Qed.

Lemma memWrite_generic_apply_upds_lookup_in_aupds u_us upds aupds a d :
  (u_us ≤ length upds)%nat →
  a ∈ update.addr <$> aupds →
  apply_upds (memWrite_generic u_us upds aupds) d !! uint.Z a =
  apply_upds aupds d !! uint.Z a.
Proof.
  intros Hbnd Hin.
  rewrite memWrite_generic_apply_upds; last by assumption.
  rewrite apply_upds_app.
  apply highest_index_is_exists in Hin.
  destruct Hin as [i Hin].
  pose proof Hin as [Hacc _].
  apply list_lookup_fmap_Some_1 in Hacc.
  destruct Hacc as [upd [-> Hacc]].
  erewrite apply_upds_lookup_in.
  2-3: eassumption.
  erewrite apply_upds_lookup_in.
  2-3: eassumption.
  reflexivity.
Qed.

Lemma memWrite_generic_app u_us upds aupds1 aupds2 :
  memWrite_generic u_us upds (aupds1 ++ aupds2) =
  memWrite_generic u_us (memWrite_generic u_us upds aupds1) aupds2.
Proof.
  apply foldl_app.
Qed.

Local Lemma memWrite_one_generic_0_expand upds upd :
  memWrite_one_generic 0%nat upds upd =
  match find_highest_index (update.addr <$> upds) upd.(update.addr) with
  | Some u =>
    <[u:=upd]>upds
  | None => upds ++ [upd]
  end.
Proof.
  f_equal.
Qed.

Lemma memWrite_one_generic_0_highest_index_is upds aupd a i :
  highest_index_is (update.addr <$> upds) a i →
  highest_index_is
    (update.addr <$> memWrite_one_generic 0%nat upds aupd)
    a i.
Proof.
  intros Hhighest.
  rewrite memWrite_one_generic_0_expand.
  destruct (find_highest_index _ _) as [highest|] eqn:Hhighest'.
  2: {
    apply find_highest_index_None in Hhighest'.
    apply find_highest_index_Some.
    rewrite fmap_app find_highest_index_app /= decide_False.
    2: {
      destruct Hhighest as [Hacc _].
      intros Heq.
      subst a.
      apply list_elem_of_lookup_2 in Hacc.
      contradiction.
    }
    apply highest_index_is_opt_to_find_highest_index.
    simpl.
    assumption.
  }
  apply find_highest_index_Some in Hhighest'.
  destruct Hhighest' as [Hacc' _].
  rewrite list_fmap_insert list_insert_id; last by assumption.
  assumption.
Qed.

Lemma memWrite_generic_0_highest_index_is upds aupds a i :
  highest_index_is (update.addr <$> upds) a i →
  highest_index_is
    (update.addr <$> memWrite_generic 0 upds aupds)
    a i.
Proof.
  rewrite -(rev_involutive aupds).
  induction (rev aupds) as [|aupd aupdst Hind]; first by intuition.
  intros Hhighest.
  apply Hind in Hhighest.
  rewrite /= memWrite_generic_app /=.
  apply memWrite_one_generic_0_highest_index_is.
  assumption.
Qed.

Local Lemma memWrite_one_generic_0_in upds aupd upd i :
  memWrite_one_generic 0%nat upds aupd !! i = Some upd →
  (
    upd = aupd ∧
    highest_index_is
      (update.addr <$> memWrite_one_generic 0%nat upds aupd)
      upd.(update.addr) i
  ) ∨ (
    upds !! i = Some upd ∧ (
      upd.(update.addr) ≠ aupd.(update.addr) ∨
      ¬ highest_index_is (update.addr <$> upds) upd.(update.addr) i
    )
  ).
Proof.
  rewrite memWrite_one_generic_0_expand.
  intros Hin.
  destruct (find_highest_index _ _) as [highest|] eqn:Hhighest.
  {
    apply find_highest_index_Some in Hhighest.
    destruct (decide (i = highest)) as [<-|Hh].
    {
      rewrite list_lookup_insert_eq in Hin.
      2: {
        destruct Hhighest as [Hacc _].
        apply lookup_lt_Some in Hacc.
        rewrite length_fmap in Hacc.
        assumption.
      }
      inversion Hin; subst aupd; clear Hin.
      left.
      split; first by reflexivity.
      rewrite list_fmap_insert.
      apply highest_index_is_insert_eq_eq.
      assumption.
    }
    rewrite list_lookup_insert_ne in Hin; last by lia.
    right.
    split; first by assumption.
    destruct (decide (upd.(update.addr) = aupd.(update.addr)))
      as [Haddr|Haddr]; last by intuition.
    right.
    rewrite -Haddr in Hhighest.
    intros Hhighest'.
    apply Hh.
    eapply highest_index_is_inj; eassumption.
  }
  apply find_highest_index_None in Hhighest.
  apply lookup_app_Some in Hin.
  destruct Hin as [Hin|[Hbnd Hin]].
  {
    right.
    split; first by assumption.
    left.
    intros Heq.
    rewrite -Heq in Hhighest.
    apply Hhighest.
    apply list_elem_of_lookup_2 in Hin.
    apply list_elem_of_fmap_2.
    assumption.
  }
  pose proof (list_elem_of_lookup_2 _ _ _ Hin) as Hin'.
  apply list_elem_of_singleton in Hin'.
  subst aupd.
  apply lookup_lt_Some in Hin.
  simpl in Hin.
  assert (i = length upds) as Hi by lia.
  subst i.
  left.
  split; first by reflexivity.
  rewrite fmap_app.
  simpl.
  replace (length upds) with (length (update.addr <$> upds)).
  2: rewrite length_fmap //.
  apply highest_index_is_app_r_id.
Qed.

Local Lemma memWrite_generic_0_in upds aupds upd i :
  memWrite_generic 0%nat upds aupds !! i = Some upd →
  (
    (
      upds !! i = Some upd ∧ (
        upd.(update.addr) ∉ update.addr <$> aupds ∨
        ¬ highest_index_is (update.addr <$> upds) upd.(update.addr) i
      )
    ) ∨
    (
      (∃ ai,
        aupds !! ai = Some upd ∧
        highest_index_is (update.addr <$> aupds) upd.(update.addr) ai
      ) ∧
      highest_index_is
        (update.addr <$> memWrite_generic 0%nat upds aupds)
        upd.(update.addr) i
    )
  ).
Proof.
  revert upd.
  rewrite -(rev_involutive aupds).
  induction (rev aupds) as [|aupd aupdst Hind].
  {
    simpl.
    intros upd Hacc.
    left.
    split; first by assumption.
    left.
    apply not_elem_of_nil.
  }
  intros upd Hin.
  simpl in Hin.
  rewrite memWrite_generic_app in Hin.
  simpl in Hin.
  apply memWrite_one_generic_0_in in Hin.
  destruct Hin as [[<- Hhighest]|[Hacc Hhighest]].
  {
    right.
    rewrite /= memWrite_generic_app /=.
    split; last by assumption.
    exists (length aupdst).
    split.
    {
      rewrite lookup_app_r.
      2: {
        rewrite rev_length.
        lia.
      }
      rewrite rev_length Nat.sub_diag.
      reflexivity.
    }
    rewrite fmap_app /=.
    replace (length aupdst) with (length (update.addr <$> rev aupdst)).
    2: rewrite length_fmap rev_length //.
    apply highest_index_is_app_r_id.
  }
  apply Hind in Hacc.
  destruct Hacc as [[Hacc Hhighesta]|[Hacc Hhighesta]].
  {
    left.
    split; first by assumption.
    destruct Hhighesta as [Hhighesta|Hhighesta]; last by intuition.
    destruct Hhighest as [Hhighest|Hhighest].
    {
      left.
      rewrite /= fmap_app /=.
      apply not_elem_of_app.
      split; first by assumption.
      intros Hin.
      apply list_elem_of_singleton in Hin.
      contradiction.
    }
    right.
    intros Hhighest_upds.
    apply Hhighest.
    apply memWrite_generic_0_highest_index_is.
    assumption.
  }
  right.
  destruct Hhighest as [Haddr|Hhighest]; last by contradiction.
  split.
  {
    destruct Hacc as [ai [Hacc Hhighest]].
    exists ai.
    simpl.
    rewrite lookup_app_l.
    2: {
      apply lookup_lt_Some in Hacc.
      assumption.
    }
    split; first by assumption.
    rewrite fmap_app /=.
    apply highest_index_is_app.
    right.
    split; last by assumption.
    intros Hin.
    apply list_elem_of_singleton in Hin.
    contradiction.
  }
  rewrite /= memWrite_generic_app.
  apply memWrite_generic_0_highest_index_is.
  assumption.
Qed.

Theorem memWrite_generic_0_region txns upds txn :
  is_memLog_region txns upds →
  is_memLog_region (txns ++ [txn]) (memWrite_generic 0%nat upds txn.2).
Proof.
  intros [Hhas Hmatch].
  split; first by apply memWrite_generic_has_updates.
  rewrite /memLog_region_upds_match_some_txn in Hmatch.
  rewrite /memLog_region_upds_match_some_txn.
  intros upd Hin.
  apply list_elem_of_lookup in Hin.
  destruct Hin as [i Hin].
  apply memWrite_generic_0_in in Hin.
  destruct Hin as [[Hacc Hhighest]|[Hacc Hhighest]].
  {
    apply list_elem_of_lookup_2 in Hacc.
    apply Hmatch in Hacc.
    destruct Hacc as [txn' [Hin Htxnmatch]].
    exists txn'.
    split.
    {
      apply elem_of_app.
      intuition.
    }
    apply Htxnmatch.
  }
  exists txn.
  split.
  {
    apply elem_of_app.
    right.
    apply list_elem_of_singleton.
    reflexivity.
  }
  intros d.
  destruct Hacc as [ai [Hacc Hhighest_txn]].
  erewrite apply_upds_lookup_in.
  1: reflexivity.
  1: eassumption.
  assumption.
Qed.

Theorem is_memLog_boundaries_modify_last txns upds mwrbs b txns' upds' :
  (length mwrbs > 1)%nat →
  mwrbs !! (length mwrbs - 2)%nat = Some b →
  is_memLog_region txns' upds' →
  is_memLog_boundaries txns upds mwrbs →
  is_memLog_boundaries
    (take b.(mwrb.txn) txns ++ txns') (take b.(mwrb.upd) upds ++ upds')
    (<[(length mwrbs - 1)%nat:= {|
      mwrb.txn := (b.(mwrb.txn) + length txns')%nat;
      mwrb.upd := (b.(mwrb.upd) + length upds')%nat;
    |}]>mwrbs).
Proof.
  intros Hmwrbs_len Hb Hreg Hbndrys.
  pose proof Hbndrys as [Hbnds Hregs].
  pose proof (list_elem_of_lookup_2 _ _ _ Hb) as Hbbnd.
  apply Hbnds in Hbbnd.
  split.
  {
    intros bndry Hbndry.
    apply list_elem_of_lookup in Hbndry.
    destruct Hbndry as [i Hbndry].
    destruct (decide (i = length mwrbs - 1)%nat) as [->|Hi].
    {
      rewrite list_lookup_insert_eq in Hbndry; last by lia.
      inversion Hbndry; subst bndry; clear Hbndry.
      simpl.
      rewrite !length_app !length_take.
      lia.
    }
    rewrite list_lookup_insert_ne in Hbndry; last by lia.
    pose proof (lookup_lt_Some _ _ _ Hbndry) as Hibnd.
    unshelve (epose proof (
      is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hbndry Hb
    ) as Hupto); first by lia.
    apply list_elem_of_lookup_2 in Hbndry.
    apply Hbnds in Hbndry.
    rewrite !length_app !length_take.
    lia.
  }
  intros i bndry1 bndry2 Hbndry1 Hbndry2.
  pose proof (lookup_lt_Some _ _ _ Hbndry2) as Hibnd.
  rewrite length_insert in Hibnd.
  rewrite list_lookup_insert_ne in Hbndry1; last by lia.
  destruct (decide (S i = length mwrbs - 1)%nat) as [Hi|Hi].
  2: {
    rewrite list_lookup_insert_ne in Hbndry2; last by lia.
    unshelve (epose proof (
      is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hbndry1 Hbndry2
    ) as Hreg'); first by lia.
    unshelve (epose proof (
      is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hbndry2 Hb
    ) as Hupto); first by lia.
    rewrite subslice_app_1.
    2: rewrite length_take; lia.
    rewrite subslice_app_1.
    2: rewrite length_take; lia.
    rewrite -(take_drop b.(mwrb.txn) txns) in Hreg'.
    rewrite -(take_drop b.(mwrb.upd) upds) in Hreg'.
    rewrite subslice_app_1 in Hreg'.
    2: rewrite length_take; lia.
    rewrite subslice_app_1 in Hreg'.
    2: rewrite length_take; lia.
    intuition.
  }
  rewrite Hi list_lookup_insert_eq in Hbndry2; last by lia.
  inversion Hbndry2; subst bndry2; clear Hbndry2.
  simpl.
  unshelve (epose proof (
    is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hbndry1 Hb
  ) as Hupto); first by lia.
  split; first by lia.
  split; first by lia.
  replace (_ - 2)%nat with (length mwrbs - 1 - 1)%nat in Hb by lia.
  rewrite -Hi /= Nat.sub_0_r Hbndry1 in Hb.
  inversion Hb; subst b; clear Hb.
  rewrite subslice_take_drop take_app_add'.
  2: rewrite length_take; lia.
  rewrite firstn_all.
  rewrite <- (length_take_le txns bndry1.(mwrb.txn)) at 1; last by lia.
  rewrite drop_app_length.
  rewrite subslice_take_drop take_app_add'.
  2: rewrite length_take; lia.
  rewrite firstn_all.
  rewrite <- (length_take_le upds bndry1.(mwrb.upd)) at 1; last by lia.
  rewrite drop_app_length.
  assumption.
Qed.

Theorem is_memLog_boundaries_memWrite_generic txns upds mwrbs unstStart txn :
  (length mwrbs > 1)%nat →
  is_memLog_boundaries txns upds mwrbs →
  mwrbs !! (length mwrbs - 1)%nat = Some (mwrb.logend txns upds) →
  mwrbs !! (length mwrbs - 2)%nat = Some unstStart →
  let ntxns := txns ++ [txn] in
  let nupds := memWrite_generic unstStart.(mwrb.upd) upds txn.2 in
  is_memLog_boundaries ntxns nupds
    (<[(length mwrbs - 1)%nat:=(mwrb.logend ntxns nupds)]>mwrbs).
Proof.
  intros Hmwrbs_len Hbndrys Hbndry2 Hbndry1.
  unshelve (epose proof (
    is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hbndry1 Hbndry2
  ) as (Hreg_upd&Hreg_txn&Hreg)); first by lia.
  simpl in Hreg_upd.
  simpl in Hreg_txn.
  simpl in Hreg.
  rewrite -!subslice_from_drop in Hreg.
  rewrite memWrite_generic_split; last by lia.
  rewrite /= /mwrb.logend !length_app length_take Nat.min_l; last by lia.
  simpl.
  split.
  {
    intros bndry Hbndry.
    rewrite !length_app length_take /=.
    apply list_elem_of_lookup_1 in Hbndry.
    destruct Hbndry as [bndryi Hbndry].
    destruct (decide (bndryi = length mwrbs - 1)%nat) as [Hbndryi|Hbndryi].
    {
      subst bndryi.
      rewrite list_lookup_insert_eq in Hbndry; last by lia.
      inversion Hbndry; subst bndry; clear Hbndry.
      simpl.
      split; first by lia.
      reflexivity.
    }
    rewrite list_lookup_insert_ne in Hbndry; last by lia.
    pose proof (lookup_lt_Some _ _ _ Hbndry) as Hbndryi_lt.
    unshelve (epose proof (
      is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hbndry Hbndry1
    ) as (Hreg_upd'&Hreg_txn'&_)); first by lia.
    lia.
  }
  intros bndryi bndry1' bndry2' Hbndry1' Hbndry2'.
  pose proof (lookup_lt_Some _ _ _ Hbndry2') as Hbndryi_lt.
  rewrite length_insert in Hbndryi_lt.
  rewrite list_lookup_insert_ne in Hbndry1'; last by lia.
  destruct (decide (S bndryi = length mwrbs - 1)%nat) as [Hbndryi|Hbndryi].
  2: {
    rewrite list_lookup_insert_ne in Hbndry2'; last by lia.
    unshelve (epose proof (
      is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hbndry1' Hbndry2'
    ) as (Hreg_upd'&Hreg_txn'&Hreg')); first by lia.
    split; first by assumption.
    split; first by assumption.
    unshelve (epose proof (
      is_memLog_boundaries_region _ _ _ _ _ _ _ _ Hbndrys Hbndry2' Hbndry1
    ) as (Hreg_upd''&Hreg_txn''&_)); first by lia.
    rewrite subslice_app_1; last by lia.
    rewrite subslice_app_1; last by (rewrite length_take; lia).
    rewrite subslice_take_all; last by lia.
    assumption.
  }
  rewrite Hbndryi list_lookup_insert_eq in Hbndry2'; last by lia.
  assert (bndryi = length mwrbs - 2)%nat by lia.
  subst bndryi.
  clear Hbndryi_lt Hbndryi.
  inversion Hbndry2'; subst bndry2'; clear Hbndry2'.
  rewrite Hbndry1 in Hbndry1'.
  inversion Hbndry1'; subst bndry1'; clear Hbndry1'.
  simpl.
  split; first by lia.
  split; first by lia.
  rewrite subslice_to_end; last by rewrite length_app //=.
  rewrite subslice_drop_take; last by lia.
  rewrite (drop_app_length' (take _ _)); last by (rewrite length_take; lia).
  rewrite Nat.add_sub'.
  rewrite firstn_all.
  rewrite drop_app_le; last by lia.
  apply memWrite_generic_0_region.
  assumption.
Qed.

Lemma is_memLog_region_prepend_nils txns upds nils :
  Forall (λ x, snd x = nil) nils →
  is_memLog_region (nils ++ txns) upds →
  is_memLog_region txns upds.
Proof.
  intros Hnils [Hhas Hmatch].
  apply has_updates_prepend_nils in Hhas; last by assumption.
  split; first by assumption.
  intros upd Hin.
  apply Hmatch in Hin.
  destruct Hin as [txn [Hin Happly]].
  apply elem_of_app in Hin.
  destruct Hin as [Hin|Hin].
  {
    specialize (Happly ∅).
    pose proof ((iffLR (Forall_forall _ _)) Hnils _ Hin) as Htxn.
    simpl in Htxn.
    rewrite Htxn /= lookup_empty in Happly.
    inversion Happly.
  }
  exists txn.
  intuition.
Qed.

Lemma is_memLog_region_prepend_nils_2 txns upds nils :
  Forall (λ x, snd x = nil) nils →
  is_memLog_region txns upds →
  is_memLog_region (nils ++ txns) upds.
Proof.
  intros Hnils [Hhas Hmatch].
  eapply has_updates_prepend_nils_2 in Hhas; last by eassumption.
  split; first by assumption.
  intros upd Hin.
  apply Hmatch in Hin.
  destruct Hin as [txn [Hin Happly]].
  exists txn.
  split; last by assumption.
  apply elem_of_app.
  intuition.
Qed.

Lemma is_memLog_region_append_nils txns upds nils :
  Forall (λ x, snd x = nil) nils →
  is_memLog_region txns upds →
  is_memLog_region (txns ++ nils) upds.
Proof.
  intros Hnils [Hhas Hmatch].
  eapply has_updates_app_nils in Hhas; last by eassumption.
  split; first by assumption.
  intros upd Hin.
  apply Hmatch in Hin.
  destruct Hin as [txn [Hin Happly]].
  exists txn.
  split.
  {
    apply elem_of_app.
    intuition.
  }
  assumption.
Qed.

Lemma is_memLog_region_append_nils_2 txns upds nils :
  Forall (λ x, snd x = nil) nils →
  is_memLog_region (txns ++ nils) upds →
  is_memLog_region txns upds.
Proof.
  intros Hnils [Hhas Hmatch].
  apply has_updates_app_nils_2 in Hhas; last by assumption.
  split; first by assumption.
  intros upd Hin.
  apply Hmatch in Hin.
  destruct Hin as [txn [Hin Happly]].
  apply elem_of_app in Hin.
  destruct Hin as [Hin|Hin].
  2: {
    specialize (Happly ∅).
    pose proof ((iffLR (Forall_forall _ _)) Hnils _ Hin) as Htxn.
    simpl in Htxn.
    rewrite Htxn /= lookup_empty in Happly.
    inversion Happly.
  }
  exists txn.
  intuition.
Qed.

Lemma is_memLog_region_nils txns :
  Forall (λ x, snd x = nil) txns →
  is_memLog_region txns [].
Proof.
  intros Hnils.
  apply (is_memLog_region_append_nils [] []) in Hnils;
    last by apply is_memLog_region_nil.
  simpl in Hnils.
  assumption.
Qed.

Theorem is_memLog_boundaries_move_nils txns upds mwrbs i lbnd newbnd rbnd :
  (lbnd ≤ newbnd ≤ rbnd)%nat →
  mwrb.txn <$> (mwrbs !! i) = Some lbnd →
  mwrb.txn <$> (mwrbs !! S i) = Some rbnd →
  Forall (λ x, x.2 = []) (subslice lbnd newbnd txns) →
  is_memLog_boundaries txns upds mwrbs →
  is_memLog_boundaries txns upds (
    alter (λ b, {| mwrb.txn := newbnd; mwrb.upd := b.(mwrb.upd); |})
      i mwrbs
  ).
Proof.
  intros Hbetween Hlbnd Hrbnd Hnils Hbndrys.
  pose proof Hbndrys as (Hbnds&Hregs).
  apply fmap_Some_1 in Hlbnd.
  apply fmap_Some_1 in Hrbnd.
  destruct Hlbnd as [b1 [Hlbnd ->]].
  destruct Hrbnd as [b2 [Hrbnd ->]].
  assert (b2.(mwrb.upd) ≤ length upds ∧ b2.(mwrb.txn) ≤ length txns)
    as Hb2bnd.
  {
    apply list_elem_of_lookup_2 in Hrbnd.
    apply Hbnds in Hrbnd.
    lia.
  }
  assert (b1.(mwrb.upd) ≤ b2.(mwrb.upd) ∧ b1.(mwrb.txn) ≤ b2.(mwrb.txn))
    as Hb1b2.
  {
    specialize (Hregs _ _ _ Hlbnd Hrbnd).
    lia.
  }
  split.
  {
    intros bndry Hbndry.
    destruct (list_elem_of_lookup_1 _ _ Hbndry) as [i' Hset].
    destruct (decide (i = i')) as [<-|Hi'].
    2: {
      rewrite list_lookup_alter_ne in Hset; last by lia.
      apply list_elem_of_lookup_2 in Hset.
      apply Hbnds in Hset.
      assumption.
    }
    rewrite list_lookup_alter_eq in Hset.
    rewrite Hlbnd in Hset.
    simpl in Hset; inversion Hset; subst bndry.
    simpl.
    lia.
  }

  intros i' bndry1 bndry2 Hbndry1 Hbndry2.
  destruct (decide (i = i')) as [<-|Hi_i'].
  {
    rewrite list_lookup_alter_eq in Hbndry1.
    rewrite list_lookup_alter_ne in Hbndry2; last by lia.
    rewrite Hrbnd in Hbndry2.
    rewrite Hlbnd in Hbndry1.
    inversion Hbndry1; subst bndry1; clear Hbndry1.
    inversion Hbndry2; subst bndry2; clear Hbndry2.
    simpl.
    split; first by lia.
    split; first by lia.
    eapply is_memLog_region_prepend_nils; first by eassumption.
    rewrite subslice_app_contig; last by lia.
    eapply Hregs; eassumption.
  }
  rewrite list_lookup_alter_ne in Hbndry1; last by assumption.
  destruct (decide (i = S i')) as [->|Hi_Si'].
  2: {
    rewrite list_lookup_alter_ne in Hbndry2; last by assumption.
    eapply is_memLog_boundaries_region.
    2-4: eassumption.
    lia.
  }
  rewrite list_lookup_alter_eq in Hbndry2.
  rewrite Hlbnd in Hbndry2.
  simpl in Hbndry2; inversion Hbndry2; subst bndry2; clear Hbndry2.
  destruct (Hregs _ _ _ Hbndry1 Hlbnd) as (Hbnd1&Hbnd2&Hreg).
  simpl.
  split; first by lia.
  split; first by lia.
  eapply is_memLog_region_append_nils in Hreg; last by eassumption.
  rewrite subslice_app_contig in Hreg; last by lia.
  assumption.
Qed.
