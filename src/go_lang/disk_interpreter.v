From RecordUpdate Require Import RecordSet.
From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From stdpp Require Import pretty.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From Perennial.Helpers Require Import Integers Transitions.
From Perennial.go_lang Require Export locations.
From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Import prelude.
From Perennial.go_lang Require Import interpret_types.
From Perennial.go_lang Require Import interpreter.

From Perennial.go_lang.examples Require Import goose_unittest.
From Perennial.go_lang.ffi Require Import disk.
Require Import Program.

Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Definition startstate : state := inhabitant.

(* More instances of mbind and mret, this time outside of the
go_lang_int section. *)
Instance statet_disk_option_bind : MBind (StateT state option) :=
  StateT_bind option option_fmap option_join option_bind.
Instance statet_disk_option_ret : MRet (StateT state option) :=
  StateT_ret option option_ret.
Instance statet_disk_error_bind : MBind (StateT state Error) :=
  StateT_bind Error Error_fmap Error_join Error_bind.
Instance statet_disk_error_ret : MRet (StateT state Error) :=
  StateT_ret Error Error_ret.

Definition free_val {A} (x: nonAtomic A) : option A :=
  match x with
  | Reading y 0 => Some y
  | _ => None
  end.

Definition byte_val (v: val) : option byte :=
  match v with
  | LitV (LitByte b) => Some b
  | _ => None
  end.

Definition read_block_from_heap (σ: state) (l: loc) : option Block :=
  navs <- state_readn_vec σ l block_bytes;
    (* list (nonAtomic val) -> list (option val) -> option (list val) -> list val *)
    vs <- commute_option_vec _ (vmap free_val navs);
    commute_option_vec _ (vmap byte_val vs).

(* If state_readn_vec succeeds, for each i in the range requested, the
heap at l + i should be some nonatomic value and that nonatomic value
should be at the return value in index i. *)
Lemma state_readn_vec_ok : forall n σ l v,
    (state_readn_vec σ l n = Some v) ->
    (forall (i:fin n),
        match σ.(heap) !! (l +ₗ i) with
        | Some nav => nav = v !!! i
        | _ => False
        end).
Proof.
  induction n.
  {
    intros.
    inversion i.
  }
  {
    intros.
    dependent destruction v.
    simpl in H.
    destruct (heap σ !! l) as [nav|] eqn:heap_at_l; try by inversion H.
    simpl in H.
    destruct (state_readn_vec σ (l +ₗ 1) n) as [vtl|] eqn:srv_ind; try by inversion H.
    simpl in H.
    unfold mret in H.
    inversion H.
    inv_fin i.
    {
      simpl.
      assert (l +ₗ 0%nat = l) as plus_zero.
      {
        unfold loc_add.
        rewrite Zplus_0_r.
        destruct l.
        simpl.
        reflexivity.
      }
      rewrite plus_zero heap_at_l; by exact H1.
    }
    {
      intros.
      assert (l +ₗ FS i = (l +ₗ 1) +ₗ i) as l_plus_one.
      {
        unfold loc_add.
        destruct l.
        simpl.
        replace (loc_car + S i) with (loc_car + 1 + i); [reflexivity|].
        lia.
      }
      rewrite l_plus_one.
      pose proof (IHn σ (l +ₗ 1) vtl srv_ind i).
      destruct (heap σ !! (l +ₗ 1 +ₗ i)) as [navi|] eqn:heap_at_l1i; [|contradiction].
      simpl.
      rewrite H0.
      apply Eqdep_dec.inj_pair2_eq_dec in H2.
      {
        rewrite H2; reflexivity.
      }
      exact Nat.eq_dec.
    }
  }
Qed.

Lemma commute_option_vec_ok {A} : forall n (ov: vec (option A) n) (v: vec A n),
    (commute_option_vec A ov = Some v) ->
    (forall (i:fin n), ov !!! i = Some (v !!! i)).
Proof.
  induction n.
  {
    intros.
    inversion i.
  }
  {
    intros.
    dependent destruction ov.
    simpl in H.
    destruct h as [a|]; [simpl in H|by inversion H].
    destruct (commute_option_vec A ov) as [v'|] eqn:cov_tail; [unfold mret, option_ret in H; simpl in H|by inversion H].
    pose proof (IHn _ _ cov_tail) as IH_tail.
    inversion H.
    inv_fin i.
    {
      simpl.
      reflexivity.
    }
    {
      intros i.
      simpl.
      exact (IH_tail i).
    }
  }
Qed.

Lemma read_block_from_heap_ok (σ: state) (l: loc) (b: Block) :
  (read_block_from_heap σ l = Some b) ->
  (forall (i:Z), 0 <= i -> i < 4096 ->
            match σ.(heap) !! (l +ₗ i) with
            | Some (Reading v _) => Block_to_vals b !! Z.to_nat i = Some v
            | _ => False
            end).
Proof.
  intros.
  unfold read_block_from_heap in H.
  unfold mbind in H.
  unfold option_bind in H.
  destruct (state_readn_vec σ l block_bytes) as [navs|] eqn:vec_at_l; try by inversion H.
  unfold block_bytes in *.
  destruct (commute_option_vec val (vmap free_val navs)) as [v|] eqn:all_free; try by inversion H.

  (* Only way to convert (Z.to_nat i) to a (fin 4096) is to have
  hypothesis that says exactly this. *)
  assert ((Z.to_nat i < 4096)%nat) as fin_i by lia. 
  
  pose proof (commute_option_vec_ok _ _ _ H (fin_of_nat fin_i)) as cov_ok_v.
  pose proof (commute_option_vec_ok _ _ _ all_free (fin_of_nat fin_i)) as cov_ok_navs.
  pose proof (state_readn_vec_ok _ _ _ _ vec_at_l (fin_of_nat fin_i)) as srv_ok_l.

  destruct (heap σ !! (l +ₗ fin_of_nat fin_i)) as [nav|] eqn:heap_at_fin_i; [|rewrite heap_at_fin_i in srv_ok_l; contradiction].
  assert ((l +ₗ i) = (l +ₗ fin_of_nat fin_i)).
  {
    unfold loc_add.
    replace (loc_car l + (fin_of_nat fin_i)) with (loc_car l + i); [reflexivity|].
    pose proof (fin_to_of_nat _ _ fin_i).
    rewrite H2.
    lia.
  }
  rewrite -> H2.
  rewrite heap_at_fin_i in srv_ok_l.
  rewrite heap_at_fin_i.
  rewrite srv_ok_l.
  rewrite -> (vlookup_map free_val navs (fin_of_nat fin_i)) in cov_ok_navs.
  unfold free_val in cov_ok_navs.
  destruct (navs !!! fin_of_nat fin_i) as [|nav'] eqn:navs_at_fin_i; inversion cov_ok_navs.
  destruct n eqn:n_is_free; inversion cov_ok_navs.
  clear cov_ok_navs navs_at_fin_i heap_at_fin_i H4 H5 H2 srv_ok_l nav'
        n n_is_free nav all_free H navs vec_at_l.
  unfold block_bytes in cov_ok_v. (* block_bytes doesn't show, but is here and needs to be unfolded *)
  rewrite -> (vlookup_map byte_val v (fin_of_nat fin_i)) in cov_ok_v.
  destruct (v !!! fin_of_nat fin_i) eqn:v_at_fin_i; try by inversion cov_ok_v.
  unfold Block_to_vals.
  pose proof (list_lookup_fmap b2val b (Z.to_nat i)) as llf.
  rewrite llf.
  simpl in cov_ok_v.
  destruct l0; try by inversion cov_ok_v.
  inversion cov_ok_v as [b_at_fin_i].
  rewrite <- b_at_fin_i.
  pose proof (vlookup_lookup' b (Z.to_nat i) n) as vll.
  assert ((b : list u8) !! Z.to_nat i = Some n).
  {
    apply vll.
    exists fin_i.
    rewrite b_at_fin_i; reflexivity.
  }
  rewrite H.
  unfold b2val.
  simpl; reflexivity.
Qed.

Fixpoint disk_interpret_step (op: DiskOp) (v: val) : StateT state Error expr :=
  match (op, v) with
  | (ReadOp, (LitV (LitInt a))) =>
    σ <- mget;
      b <- mlift (σ.(world) !! int.val a) ("ReadOp: No block at address " ++ (pretty a));
      let l := find_alloc_location σ 4096 in
      _ <- mput (state_insert_list l (Block_to_vals b) σ);
        mret (Val $ LitV (LitLoc l))
  | (WriteOp, (PairV (LitV (LitInt a)) (LitV (LitLoc l)))) =>
    σ <- mget;
      _ <- mlift (σ.(world) !! int.val a) ("WriteOp: No block at write address " ++ (pretty a));
      b <- mlift (read_block_from_heap σ l) "WriteOp: Read from heap failed";
      _ <- mput (set world <[ int.val a := b ]> σ);
      mret (Val $ LitV (LitUnit))
  | (SizeOp, LitV LitUnit) =>
    σ <- mget;
      mret (Val $ LitV $ LitInt (U64 (disk_size σ.(world))))
  | _ => mfail "DiskOp: Not a valid disk op and arg"
  end.

Lemma disk_interpret_ok : forall (eop : DiskOp) (arg : val) (result : expr) (σ σ': state),
    (runStateT (disk_interpret_step eop arg) σ = Works _ (result, σ')) ->
    exists m l, @language.nsteps heap_lang m ([ExternalOp eop (Val arg)], σ) l ([result], σ').
Proof.
  intros eop arg result σ σ' H.
  destruct eop; inversion H.
  { (* ReadOp *)
    destruct arg; try by inversion H1.
    destruct l; try by inversion H1.
    simpl in H1.
    destruct (world σ !! int.val n) eqn:disk_at_n; rewrite disk_at_n in H1; try by inversion H1.
    simpl in H1.
    inversion H1.
    do 2 eexists.
    single_step.
    rewrite disk_at_n.
    simpl.
    monad_simpl.
    pose proof (find_alloc_location_fresh σ 4096) as fresh.
    {
      eapply relation.bind_suchThat.
      {
        simpl.
        exact fresh.
      }
      monad_simpl.
    }
  }
  { (* WriteOp *)
    destruct arg; try by inversion H1.
    destruct arg1; try by inversion H1.
    destruct l; try by inversion H1.
    destruct arg2; try by inversion H1.
    destruct l; try by inversion H1. (* takes a very long time (why?) *)
    simpl in H1.
    destruct (world σ !! int.val n) eqn:disk_at_n; rewrite disk_at_n in H1; try by inversion H1. (* also takes a long time *)
    destruct (read_block_from_heap σ l) eqn:block_at_l; try by inversion H1.
    simpl in H1.
    inversion H1.
    do 2 eexists.
    single_step.
    rewrite disk_at_n.
    simpl.
    monad_simpl.
    pose proof (read_block_from_heap_ok _ _ _ block_at_l) as rbfsok.
    eapply relation.bind_suchThat; [exact rbfsok|].
    monad_simpl.
  }
  { (* SizeOp *)
    destruct arg; try by inversion H1.
    destruct l; try by inversion H1.
    simpl in H1.
    inversion H1.
    do 2 eexists.
    single_step.
  }
Qed.

Instance disk_interpretable : @ext_interpretable disk_op disk_model disk_semantics :=
  { ext_interpret_step := disk_interpret_step;
    ext_interpret_ok := disk_interpret_ok }.
