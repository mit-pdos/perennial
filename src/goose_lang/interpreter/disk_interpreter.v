From RecordUpdate Require Import RecordSet.
From stdpp Require Export binders strings gmap pretty.
From Perennial.Helpers Require Import Integers Transitions.
From Perennial.goose_lang Require Import prelude.

From Perennial.goose_lang.interpreter Require Import interpret_types.
From Perennial.goose_lang.interpreter Require Import pretty_types.
From Perennial.goose_lang.interpreter Require Import interpreter.

From Perennial.goose_lang.ffi Require Import disk disk_prelude.
Require Import Program.

Instance statet_disk_error_bind : MBind (StateT state Error) :=
  StateT_bind Error Error_fmap Error_join Error_bind.
Instance statet_disk_error_ret : MRet (StateT state Error) :=
  StateT_ret Error Error_ret.

Definition free_val {A} (x: nonAtomic A) : option A :=
  match x with
  | (Reading 0, y) => Some y
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
        replace (Z.of_nat 0%nat) with 0%Z by auto.
        apply loc_add_0.
      }
      rewrite plus_zero heap_at_l; by exact H1.
    }
    {
      intros.
      assert (l +ₗ FS i = (l +ₗ 1) +ₗ i) as l_plus_one.
      {
        simpl.
        replace (Z.of_nat (S i)) with (1 + i) by lia.
        rewrite loc_add_assoc //=.
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
            | Some (Reading _, v) => Block_to_vals b !! Z.to_nat i = Some v
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
  assert ((Z.to_nat i < Z.to_nat 4096)%nat) as fin_i by lia.
  
  pose proof (commute_option_vec_ok _ _ _ H (nat_to_fin fin_i)) as cov_ok_v.
  pose proof (commute_option_vec_ok _ _ _ all_free (nat_to_fin fin_i)) as cov_ok_navs.
  pose proof (state_readn_vec_ok _ _ _ _ vec_at_l (nat_to_fin fin_i)) as srv_ok_l.

  destruct (heap σ !! (l +ₗ nat_to_fin fin_i)) as [nav|] eqn:heap_at_fin_i; [| contradiction].
  assert ((l +ₗ i) = (l +ₗ nat_to_fin fin_i)).
  {
    replace (Z.of_nat (nat_to_fin fin_i)) with i; auto.
    pose proof (fin_to_nat_to_fin _ _ fin_i).
    rewrite H2.
    lia.
  }
  rewrite -> H2.
  rewrite heap_at_fin_i.
  rewrite srv_ok_l.
  rewrite -> (vlookup_map free_val navs (nat_to_fin fin_i)) in cov_ok_navs.
  unfold free_val in cov_ok_navs.
  destruct (navs !!! nat_to_fin fin_i) as ([|?], nav') eqn:navs_at_fin_i; inversion cov_ok_navs.
  destruct n eqn:n_is_free; inversion cov_ok_navs.
  clear cov_ok_navs navs_at_fin_i heap_at_fin_i H4 H5 H2 srv_ok_l nav'
        n n_is_free nav all_free H navs vec_at_l.
  unfold block_bytes in cov_ok_v. (* block_bytes doesn't show, but is here and needs to be unfolded *)
  rewrite -> (vlookup_map byte_val v (nat_to_fin fin_i)) in cov_ok_v.
  destruct (v !!! nat_to_fin fin_i) eqn:v_at_fin_i; try by inversion cov_ok_v.
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

Instance pretty_disk_op : Pretty DiskOp :=
  fun x => match x with
        | ReadOp => "ReadOp"
        | WriteOp => "WriteOp"
        | SizeOp => "SizeOp"
        end.

(* Not imported from interpreter.v? *)
Instance statet_error_bind : MBind (StateT btstate Error) :=
  StateT_bind Error Error_fmap Error_join Error_bind.
Instance statet_error_ret : MRet (StateT btstate Error) :=
  StateT_ret Error Error_ret.

(* Single-step interpreter for external disk operations. *)
Definition disk_interpret_step (op: DiskOp) (v: val) : StateT btstate Error expr :=
  match (op, v) with
  | (ReadOp, (LitV (LitInt _))) =>
    bts <- mget;
      let 'σg := fst bts in
      t <- mlift (Transitions.interpret [] (ext_step ReadOp v) σg) "Transitions.interpret failed in ReadOp";
      match t with
      | (hints, σg', v') => _ <- mput (σg', snd bts); mret (Val v')
      end
  | (WriteOp, (PairV (LitV (LitInt a)) (LitV (LitLoc l)))) =>
    bts <- mget;
      let '(σ,g) := fst bts in
      _ <- mlift (σ.(world) !! int.Z a) ("Disk WriteOp failed: No block at write address " ++ (pretty a));
      b <- mlift (read_block_from_heap σ l) ("Disk WriteOp failed: Read from heap failed at location " ++ (pretty l));
      _ <- mput ((set world <[ int.Z a := b ]> σ, g), snd bts);
      mret (Val $ LitV (LitUnit))
  | (SizeOp, LitV LitUnit) =>
    bts <- mget;
    let '(σ,g) := fst bts in
      mret (Val $ LitV $ LitInt (U64 (disk_size σ.(world))))
  | _ => mfail ("DiskOp failed: Invalid argument types for " ++ (pretty op))
  end.

Lemma disk_interpret_ok : forall (eop : DiskOp) (arg : val) (result : expr) (σ σ': state) (g g': global_state) (ws ws': btval),
    (runStateT (disk_interpret_step eop arg) ((σ,g), ws) = Works _ (result, ((σ',g'), ws'))) ->
    exists m l, @language.nsteps goose_lang m ([ExternalOp eop (Val arg)], (σ,g)) l ([result], (σ',g')).
Proof.
  intros eop arg result σ σ' g g' ws ws' H.
  destruct eop; [| inversion H | inversion H].
  { (* ReadOp *)
    unfold disk_interpret_step in H.
    destruct arg; try by inversion H.
    destruct l; try by inversion H.
    assert (runStateT mget ((σ,g), ws) = Works _ (((σ,g), ws), ((σ,g), ws))) by eauto.
    rewrite (runStateT_Error_bind _ _ _ _ _ _ _ H0) in H.
    destruct (Transitions.interpret [] (ext_step ReadOp #n) ((σ,g), ws).1) eqn:interp_res; simpl in H; try by inversion H.
    destruct p as ((l & s) & b).
    simpl in H.
    inversion H.
    subst.
    pose proof (Transitions.relation.interpret_sound _ _ _ interp_res) as interp_ok.
    simpl in interp_ok.
    monad_inv.
    simpl in interp_ok.
    do 2 eexists.
    single_step.
    (* TODO: rewrite using ltac (or a lemma) to handle adding a function at the end of a known relation (does that exist?) *)
    inversion interp_ok.
    econstructor; [exact H1|].
    monad_simpl.
    subst.
    inversion H2.
    econstructor; [exact H3|].
    monad_simpl.
    inversion H4.
    subst.
    econstructor.
    inversion H8. inversion H9.
    subst.
    simpl.
    inversion H5.
    rewrite H7.
    inversion H11.
    reflexivity.
  }
  { (* WriteOp *)
    destruct arg; try by inversion H1.
    destruct arg1; try by inversion H1.
    destruct l; try by inversion H1.
    destruct arg2; try by inversion H1.
    destruct l; try by inversion H1.
    simpl in H1.
    destruct (world σ !! int.Z n) eqn:disk_at_n; rewrite disk_at_n in H1; last by inversion H1.
    destruct (read_block_from_heap σ l) eqn:block_at_l; try by inversion H1.
    simpl in H1.
    inversion H1.
    do 2 eexists.
    single_step.
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
