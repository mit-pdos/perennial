From Goose.github_com.session Require Export server.
From Perennial.program_proof Require Export std_proof grove_prelude.

Create HintDb session_hints.

Module SessionPrelude.

  #[local] Obligation Tactic := intros.

  Class hsEq (A : Type) {well_formed : A -> Prop} : Type :=
    { eqProp (x : A) (y : A) : Prop
    ; eqb (x : A) (y : A) : bool 
    ; eqProp_reflexivity x
      (x_wf : well_formed x)
      : eqProp x x
    ; eqProp_symmetry x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      (x_eq_y : eqProp x y)
      : eqProp y x
    ; eqProp_transitivity x y z
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      (z_wf : well_formed z)
      (x_eq_y : eqProp x y)
      (y_eq_z : eqProp y z)
      : eqProp x z
    ; eqb_eq x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : eqb x y = true <-> eqProp x y
    ; eqb_neq x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : eqb x y = false <-> ~ eqProp x y
    }.

  #[global] Hint Resolve @eqProp_reflexivity @eqProp_symmetry @eqProp_transitivity : session_hints.
  #[global] Hint Rewrite @eqb_eq @eqb_neq : session_hints.

  Section hsEq_accessories.

    Context `{hsEq_A : hsEq A}.

    Lemma eqb_comm (x : A) (y : A)
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : eqb x y = eqb y x.
    Proof.
      destruct (eqb y x) as [ | ] eqn: H_OBS; [rewrite eqb_eq in H_OBS | rewrite eqb_neq in H_OBS]; trivial.
      - rewrite eqb_eq; eauto with *.
      - rewrite eqb_neq; eauto with *.
    Qed.

    Lemma eqb_obs (b : bool) (x : A) (y : A)
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : eqb x y = b <-> (if b then eqProp x y else ~ eqProp x y).
    Proof.
      destruct b; [eapply eqb_eq | eapply eqb_neq]; trivial.
    Qed.

  End hsEq_accessories.

  (** Section basic_instances_of_hsEq. *)

  #[global, program]
  Instance hsEq_preimage {A : Type} {B : Type}
    {B_well_formed : B -> Prop}
    {hsEq : hsEq B (well_formed := B_well_formed)}
    (f : A -> B)
    : SessionPrelude.hsEq A (well_formed := fun x : A => B_well_formed (f x)) :=
      { eqProp x y := eqProp (f x) (f y)
      ; eqb x y := eqb (f x) (f y)
      }.
  Next Obligation.
    simpl in *. eapply eqProp_reflexivity; trivial.
  Qed.
  Next Obligation.
    simpl in *. eapply eqProp_symmetry; trivial.
  Qed.
  Next Obligation.
    simpl in *. eapply eqProp_transitivity with (y := f y); trivial.
  Qed.
  Next Obligation.
    simpl. rewrite eqb_eq; trivial.
  Qed.
  Next Obligation.
    simpl. rewrite eqb_neq; trivial.
  Qed.

  #[global, program]
  Instance hsEq_nat : hsEq nat (well_formed := fun _ => True) :=
    { eqProp := @eq nat
    ; eqb := Nat.eqb
    ; eqProp_reflexivity := _
    ; eqProp_symmetry := _
    ; eqProp_transitivity := _
    ; eqb_eq x y _ _ := @Nat.eqb_eq x y
    ; eqb_neq x y _ _ := @Nat.eqb_neq x y
    }.
  Next Obligation.
    reflexivity; eauto.
  Qed.
  Next Obligation.
    symmetry; eauto.
  Qed.
  Next Obligation.
    etransitivity; eauto.
  Qed.

  #[global, program]
  Instance hsEq_Z : hsEq Z (well_formed := fun _ => True) :=
    { eqProp := @eq Z
    ; eqb := Z.eqb
    ; eqProp_reflexivity := _
    ; eqProp_symmetry := _
    ; eqProp_transitivity := _
    ; eqb_eq x y _ _ := @Z.eqb_eq x y
    ; eqb_neq x y _ _ := Z.eqb_neq x y
    }.
  Next Obligation.
    reflexivity; eauto.
  Qed.
  Next Obligation.
    symmetry; eauto.
  Qed.
  Next Obligation.
    etransitivity; eauto.
  Qed.

  #[global, program]
  Instance hsEq_u64 : hsEq u64 (well_formed := fun _ => True) :=
    { eqProp := @eq u64
    ; eqb x y := (uint.Z x =? uint.Z y)%Z
    ; eqProp_reflexivity := _
    ; eqProp_symmetry := _
    ; eqProp_transitivity := _
    ; eqb_eq := _
    ; eqb_neq := _
    }.
  Next Obligation.
    reflexivity; eauto.
  Qed.
  Next Obligation.
    symmetry; eauto.
  Qed.
  Next Obligation.
    etransitivity; eauto.
  Qed.
  Next Obligation.
    simpl. rewrite Z.eqb_eq. split.
    - intros EQ. word.
    - congruence.
  Qed.
  Next Obligation.
    simpl. rewrite Z.eqb_neq. split.
    - congruence.
    - intros NE. word.
  Qed.

  #[global, program]
  Instance hsEq_w64 : hsEq w64 (well_formed := fun _ => True) :=
    { eqProp := @eq w64
    ; eqb x y := (uint.Z x =? uint.Z y)%Z
    ; eqProp_reflexivity := _
    ; eqProp_symmetry := _
    ; eqProp_transitivity := _
    ; eqb_eq := _
    ; eqb_neq := _
    }.
  Next Obligation.
    reflexivity; eauto.
  Qed.
  Next Obligation.
    symmetry; eauto.
  Qed.
  Next Obligation.
    etransitivity; eauto.
  Qed.
  Next Obligation.
    simpl. rewrite Z.eqb_eq. split.
    - intros EQ. word.
    - congruence.
  Qed.
  Next Obligation.
    simpl. rewrite Z.eqb_neq. split.
    - congruence.
    - intros NE. word.
  Qed.

  (** End basic_instances_of_hsEq. *)

  Class hsOrd (A : Type) {well_formed : A -> Prop} {hsEq : hsEq A (well_formed := well_formed)} : Type :=
    { ltProp (x : A) (y : A) : Prop
    ; ltb (x : A) (y : A) : bool
    ; ltProp_irreflexivity x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      (x_eq_y : eqProp x y)
      : ~ ltProp x y
    ; ltProp_transitivity x y z
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      (z_wf : well_formed z)
      (x_lt_y : ltProp x y)
      (y_lt_z : ltProp y z)
      : ltProp x z
    ; ltProp_trichotomy x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : ltProp x y \/ eqProp x y \/ ltProp y x
    ; ltb_lt x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : ltb x y = true <-> ltProp x y
    ; ltb_nlt x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : ltb x y = false <-> ~ ltProp x y
    }.

  #[global] Hint Resolve @ltProp_irreflexivity @ltProp_transitivity : session_hints.
  #[global] Hint Rewrite @ltb_lt @ltb_nlt : session_hints.

  Section hsOrd_accessories.

    Context `{hsOrd_A : hsOrd A}.

    Lemma ltb_ge (x : A) (y : A)
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : ltb x y = (negb (ltb y x) && negb (eqb x y))%bool.
    Proof.
      (destruct (ltb x y) as [ | ] eqn: H_OBS0; [rewrite ltb_lt in H_OBS0 | rewrite ltb_nlt in H_OBS0]);
      (destruct (ltb y x) as [ | ] eqn: H_OBS1; [rewrite ltb_lt in H_OBS1 | rewrite ltb_nlt in H_OBS1]);
      (destruct (eqb x y) as [ | ] eqn: H_OBS2; [rewrite eqb_eq in H_OBS2 | rewrite eqb_neq in H_OBS2]);
      simpl in *; try congruence.
      - contradiction (ltProp_irreflexivity x y); try done.
      - contradiction (ltProp_irreflexivity y y).
        + eapply eqProp_reflexivity; try done.
        + eapply ltProp_transitivity with (y := x); try done.
      - contradiction (ltProp_irreflexivity x y); try done.
      - pose proof (ltProp_trichotomy x y); tauto.
    Qed.

  End hsOrd_accessories.

  (** Section basic_instances_of_hsOrd. *)

  #[global, program]
  Instance hsOrd_preimage {A : Type} {B : Type}
    {B_well_formed : B -> Prop}
    {hsEq : hsEq B (well_formed := B_well_formed)}
    {hsOrd : hsOrd B (hsEq := hsEq)}
    (f : A -> B)
    : SessionPrelude.hsOrd A (hsEq := hsEq_preimage f):=
      { ltProp x y := ltProp (f x) (f y)
      ; ltb x y := ltb (f x) (f y)
      }.
  Next Obligation.
    eapply (ltProp_irreflexivity (f x) (f y)); trivial.
  Qed.
  Next Obligation.
    eapply (ltProp_transitivity (f x) (f y) (f z)); trivial.
  Qed.
  Next Obligation.
    eapply (ltProp_trichotomy (f x) (f y)); trivial.
  Qed.
  Next Obligation.
    simpl. rewrite ltb_lt; trivial.
  Qed.
  Next Obligation.
    simpl. rewrite ltb_nlt; trivial.
  Qed.

  #[global, program]
  Instance hsOrd_nat : hsOrd nat :=
    { ltProp x y := (x < y)%nat
    ; ltb := Nat.ltb
    ; ltProp_irreflexivity := _
    ; ltProp_transitivity := _
    ; ltProp_trichotomy := _
    ; ltb_lt x y := _
    ; ltb_nlt x y := _
    }.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl. eapply Nat.ltb_lt.
  Qed.
  Next Obligation.
    simpl. rewrite Nat.ltb_ge. word.
  Qed.

  #[global, program]
  Instance hsOrd_Z : hsOrd Z :=
    { ltProp x y := (x < y)%Z
    ; ltb := Z.ltb
    ; ltProp_irreflexivity := _
    ; ltProp_transitivity := _
    ; ltProp_trichotomy := _
    ; ltb_lt x y := _
    ; ltb_nlt x y := _
    }.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl. rewrite Z.ltb_lt. word.
  Qed.
  Next Obligation.
    simpl. rewrite Z.ltb_ge. word.
  Qed.

  #[global, program]
  Instance hsOrd_u64 : hsOrd u64 :=
    { ltProp x y := (uint.Z x < uint.Z y)%Z
    ; ltb x y := (uint.Z y >? uint.Z x)%Z
    ; ltProp_irreflexivity := _
    ; ltProp_transitivity := _
    ; ltProp_trichotomy := _
    ; ltb_lt x y := _
    ; ltb_nlt x y := _
    }.
  Next Obligation.
    simpl. do 2 red in x_eq_y. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *.
    assert (uint.Z x < uint.Z y \/ uint.Z x = uint.Z y \/ uint.Z x > uint.Z y) as [LT | [EQ | GT]] by word.
    - left. word.
    - right. left. word. 
    - right. right. word.
  Qed.
  Next Obligation.
    rewrite Z.gtb_gt. word.
  Qed.
  Next Obligation.
    simpl. rewrite Z.gtb_ltb Z.ltb_ge. word.
  Qed.

  #[global, program]
  Instance hsOrd_w64 : hsOrd w64 :=
    { ltProp x y := (uint.Z x < uint.Z y)%Z
    ; ltb x y := (uint.Z y >? uint.Z x)%Z
    ; ltProp_irreflexivity := _
    ; ltProp_transitivity := _
    ; ltProp_trichotomy := _
    ; ltb_lt x y := _
    ; ltb_nlt x y := _
    }.
  Next Obligation.
    simpl. do 2 red in x_eq_y. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *.
    assert (uint.Z x < uint.Z y \/ uint.Z x = uint.Z y \/ uint.Z x > uint.Z y) as [LT | [EQ | GT]] by word.
    - left. word.
    - right. left. word. 
    - right. right. word.
  Qed.
  Next Obligation.
    rewrite Z.gtb_gt. word.
  Qed.
  Next Obligation.
    simpl. rewrite Z.gtb_ltb Z.ltb_ge. word.
  Qed.

  (** End basic_instances_of_hsOrd. *)

  Section SORTED.

    Context {A : Type} {well_formed : A -> Prop}.

    Lemma Forall_well_formed_elim (xs : list A)
      (xs_wf : Forall well_formed xs)
      : ∀ x : A, ∀ i : nat, xs !! i = Some x -> well_formed x.
    Proof.
      induction xs_wf as [ | x xs x_wf xs_wf IH]; intros x0 i H_x0.
      - rewrite lookup_nil in H_x0. congruence.
      - rewrite lookup_cons in H_x0. destruct i as [ | i'].
        + congruence.
        + eapply IH with (i := i'); trivial.
    Qed.

    #[local] Hint Resolve Forall_well_formed_elim : core.

    Context {hsEq : hsEq A (well_formed := well_formed)}.

    Context {hsOrd : hsOrd A (hsEq := hsEq)}.

    Definition is_sorted (xs : list A) : Prop :=
      ∀ i : nat, ∀ j : nat, (i < j)%nat ->
      ∀ x1 : A, ∀ x2 : A, xs !! i = Some x1 -> xs !! j = Some x2 -> ltb x1 x2 = true \/ eqb x2 x1 = true.

    Definition is_sorted' (xs : list A) : Prop :=
      ∀ i : nat, ∀ j : nat, (i <= j)%nat ->
      ∀ x1 : A, ∀ x2 : A, xs !! i = Some x1 -> xs !! j = Some x2 -> ltb x1 x2 = true \/ eqb x2 x1 = true.

    Lemma is_sorted_iff_is_sorted' xs
      (xs_wf : Forall well_formed xs)
      : is_sorted xs <-> is_sorted' xs.
    Proof with eauto.
      split; [intros SORTED | intros SORTED']; intros i j i_lt_j x1 x2 H_x1 H_x2.
      - assert (i = j \/ i < j)%nat as [EQ | GT] by word.
        + right. rewrite eqb_eq... replace x2 with x1 by congruence. eapply eqProp_reflexivity...
        + eapply SORTED with (i := i) (j := j); try (word || done).
      - eapply SORTED' with (i := i) (j := j); try (word || done).
    Qed.

    Fixpoint sortedInsert (l : list A) (i : A) : list A :=
      match l with
      | [] => [i]
      | h :: t => if ltb i h then i :: h :: t else h :: sortedInsert t i
      end.

    Lemma sortedInsert_spec (l : list A) (i : A) (l_wf : Forall well_formed l) (i_wf : well_formed i) :
      is_sorted l ->
      ∃ prefix, ∃ suffix, l = prefix ++ suffix /\
        sortedInsert l i = prefix ++ [i] ++ suffix /\
        (∀ n : nat, ∀ x, prefix !! n = Some x -> ltb x i = true \/ eqb i x = true) /\
        (∀ n : nat, ∀ x, suffix !! n = Some x -> ltb i x = true \/ eqb x i = true) /\
        Forall well_formed (sortedInsert l i).
    Proof with eauto.
      intros SORTED. rewrite is_sorted_iff_is_sorted' in SORTED... revert i SORTED i_wf. induction l_wf as [ | x1 xs x1_wf xs_wf IH]; intros x0 SORTED' x0_wf.
      - exists []. exists []. split. { done. } split. { reflexivity. } split.
        { intros n x H_x. rewrite lookup_nil in H_x. congruence. } split.
        { intros n x H_x. rewrite lookup_nil in H_x. congruence. } econstructor; eauto.
      - assert (SORTED : is_sorted xs).
        { intros i j i_lt_j x x' H_x H_x'. eapply SORTED' with (i := S i) (j := S j); try (word || done). }
        rewrite -> is_sorted_iff_is_sorted' in SORTED... specialize (IH x0 SORTED). destruct IH as (prefix & suffix & -> & EQ & H_prefix & H_suffix & H_wf)... simpl.
        destruct (ltb x0 x1) as [ | ] eqn: H_OBS; [rewrite ltb_lt in H_OBS | rewrite ltb_nlt in H_OBS]...
        { exists []. exists (x1 :: prefix ++ suffix)%list. repeat (split; try done).
          - intros n x H_x. enough (want_to_show : ltb x1 x = true \/ eqb x x1 = true).
            + destruct want_to_show as [H_lt | H_eq].
              * left. rewrite ltb_lt...  eapply ltProp_transitivity with (y := x1); try done... rewrite <- ltb_lt...
              * left. rewrite ltb_lt... rewrite eqb_eq in H_eq... pose proof (ltProp_trichotomy x0 x) as [? | [? | ?]]...
                { contradiction (ltProp_irreflexivity x0 x1)... eapply eqProp_transitivity with (y := x)... }
                { contradiction (ltProp_irreflexivity x x1); try done... eapply ltProp_transitivity with (y := x0)... }
            + red in SORTED'. eapply SORTED' with (i := 0%nat) (j := n); try (word || done)...
          - econstructor; eauto.
        }
        { exists (x1 :: prefix)%list. exists suffix. split. { done. } split. { simpl. rewrite EQ. simpl. reflexivity. } split.
          - intros [ | n]; simpl; intros x H_x.
            + assert (x = x1) as -> by congruence. clear H_x.
              rewrite ltb_lt... rewrite eqb_eq... pose proof (ltProp_trichotomy x0 x1) as [? | [? | ?]]; try done.
              * right; done.
              * left; done.
            + eapply H_prefix. exact H_x.
          - split. 
            + exact H_suffix.
            + eauto.
        }
    Qed.

    Lemma sortedInsert_is_sorted l i (l_wf : Forall well_formed l) (i_wf : well_formed i) :
      is_sorted l ->
      is_sorted (sortedInsert l i).
    Proof with try (word || congruence || eauto || done).
      intros SORTED. pose proof (sortedInsert_spec l i l_wf i_wf SORTED) as (prefix & suffix & H_l & -> & H_prefix & H_suffix & H_wf).
      rewrite is_sorted_iff_is_sorted'... rename i into x, l into xs. rewrite is_sorted_iff_is_sorted' in SORTED...
      unfold is_sorted' in SORTED. intros i j LE x1 x2 H_x1 H_x2.
      assert (i < length prefix \/ i = length prefix \/ i > length prefix)%nat as [i_lt | [i_eq | i_gt]] by word;
      assert (j < length prefix \/ j = length prefix \/ j > length prefix)%nat as [j_lt | [j_eq | j_gt]] by word.
      - eapply SORTED with (i := i) (j := j)...
        + rewrite H_l. rewrite lookup_app_l... rewrite lookup_app_l in H_x1...
        + rewrite H_l. rewrite lookup_app_l... rewrite lookup_app_l in H_x2...
      - rewrite list_lookup_middle in H_x2...
        assert (x = x2) as -> by congruence. clear H_x2.
        eapply H_prefix. rewrite lookup_app_l in H_x1...
      - cut (ltb x1 x = true \/ eqb x x1 = true).
        + intros H_middle.
          enough (H_middle' : ltb x x2 = true \/ eqb x x2 = true).
          { rewrite ltb_lt... rewrite ltb_lt in H_middle... rewrite ltb_lt in H_middle'...
            rewrite eqb_eq... rewrite eqb_eq in H_middle... rewrite eqb_eq in H_middle'...
            destruct H_middle as [H_middle | H_middle], H_middle' as [H_middle' | H_middle'].
            - left. eapply ltProp_transitivity with (y := x)...
            - left. pose proof (ltProp_trichotomy x1 x2) as [? | [? | ?]]...
              + contradiction (ltProp_irreflexivity x1 x)... eapply eqProp_transitivity with (y := x2)... eapply eqProp_symmetry...
              + contradiction (ltProp_irreflexivity x2 x)...
                * eapply eqProp_symmetry...
                * eapply ltProp_transitivity with (y := x1)...
            - left. pose proof (ltProp_trichotomy x1 x2) as [? | [? | ?]]...
              + contradiction (ltProp_irreflexivity x x2)... eapply eqProp_transitivity with (y := x1)...
              + contradiction (ltProp_irreflexivity x x1)... eapply ltProp_transitivity with (y := x2)...
            - right. eapply eqProp_transitivity with (y := x)... eapply eqProp_symmetry...
          }
          clear H_middle. rewrite eqb_comm...
          eapply H_suffix. rewrite app_assoc in H_x2. rewrite lookup_app_r in H_x2...
          rewrite length_app. simpl. word.
        + eapply H_prefix. rewrite lookup_app_l in H_x1...
      - rewrite list_lookup_middle in H_x1...
      - right. replace x2 with x1 by congruence. rewrite eqb_eq... eapply eqProp_reflexivity...
      - rewrite list_lookup_middle in H_x1...
        assert (x = x1) as -> by congruence. clear H_x1.
        eapply H_suffix. rewrite app_assoc in H_x2. rewrite lookup_app_r in H_x2...
        rewrite length_app. simpl. word.
      - word.
      - word.
      - eapply SORTED with (i := (i - 1)%nat) (j := (j - 1)%nat)...
        + rewrite H_l. rewrite lookup_app_r... rewrite app_assoc in H_x1. rewrite lookup_app_r in H_x1; simpl in *.
          * rewrite length_app in H_x1. simpl in *. replace (i - 1 - length prefix)%nat with (i - (length prefix + 1))%nat by word...
          * rewrite length_app. simpl...
        + rewrite H_l. rewrite lookup_app_r... rewrite app_assoc in H_x2. rewrite lookup_app_r in H_x2; simpl in *.
          * rewrite length_app in H_x2. simpl in *. replace (j - 1 - length prefix)%nat with (j - (length prefix + 1))%nat by word...
          * rewrite length_app. simpl...
    Qed.

  End SORTED.

  Section VECTOR.

    #[local] Open Scope list_scope.

    #[local] Notation "x =? y" := (SessionPrelude.eqb x y).

    #[local] Notation "x >? y" := (SessionPrelude.ltb y x).

    Context {A : Type} {well_formed : A -> Prop}.

    #[local] Hint Resolve (@Forall_well_formed_elim A well_formed) : core.

    Context {hsEq : hsEq A (well_formed := well_formed)}.

    Fixpoint vectorEq (v1 : list A) (v2 : list A) : bool :=
      match v1 with
      | [] => true
      | h1 :: t1 =>
        match v2 with
        | [] => true
        | h2 :: t2 => if negb (h1 =? h2) then false else vectorEq t1 t2
        end
      end.

    #[global, program]
    Instance hsEq_vector (len : nat) : SessionPrelude.hsEq (list A) (well_formed := fun l => Forall well_formed l /\ length l = len) :=
      { eqProp xs1 xs2 := ∀ i : nat, (i < len)%nat -> ∀ x1 : A, ∀ x2 : A, xs1 !! i = Some x1 -> xs2 !! i = Some x2 -> eqb x1 x2 = true
      ; eqb := vectorEq
      ; eqProp_reflexivity xs1 xs1_wf := _
      ; eqProp_symmetry xs1 xs2 xs1_wf xs2_wf xs1_eq_xs2 := _
      ; eqProp_transitivity xs1 xs2 xs3 xs1_wf xs2_wf xs3_wf xs1_eq_xs2 xs2_eq_xs3 := _
      }.
    Next Obligation with eauto 2.
      destruct xs1_wf as [xs1_wf xs1_len].
      intros i i_bound x1 x2 H_x1 H_x2; simpl in *.
      replace x1 with x2 by congruence.
      rewrite eqb_eq... eapply eqProp_reflexivity...
    Qed.
    Next Obligation with eauto 2.
      destruct xs1_wf as [xs1_wf xs1_len], xs2_wf as [xs2_wf xs2_len].
      intros i i_bound x1 x2 H_x1 H_x2; simpl in *.
      rewrite eqb_comm...
    Qed.
    Next Obligation with eauto 2.
      destruct xs1_wf as [xs1_wf xs1_len], xs2_wf as [xs2_wf xs2_len], xs3_wf as [xs3_wf xs3_len].
      intros i i_bound x1 x2 H_x1 H_x2; simpl in *.
      rewrite <- xs2_len in i_bound.
      pose proof (list_lookup_lt xs2 i i_bound) as (x3 & H_x3).
      rewrite eqb_eq... eapply eqProp_transitivity with (y := x3)...
      - rewrite <- eqb_eq... eapply xs1_eq_xs2 with (i := i)... rewrite <- xs2_len...
      - rewrite <- eqb_eq... eapply xs2_eq_xs3 with (i := i)... rewrite <- xs2_len...
    Qed.
    Next Obligation with eauto 2.
      destruct x_wf as [x_wf x_len], y_wf as [y_wf y_len]. simpl in *. split.
      - revert len x_len y y_len y_wf. induction x_wf as [ | hx tx hx_wf tx_wf IH]; intros ? <- [ | hy ty] LEN_EQ y_wf EQ [ | i'] i_bound x1 x2 H_x1 H_x2; simpl in *; try congruence; try word; inv y_wf.
        + rewrite eqb_eq... destruct (x1 =? x2) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS... all: simpl in *; congruence.
        + rewrite eqb_eq... destruct (hx =? hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS... all: simpl in *; try congruence.
          rewrite <- eqb_eq... eapply IH with (y := ty) (i := i')... all: try word || done.
      - revert len x_len y y_len y_wf. induction x_wf as [ | hx tx hx_wf tx_wf IH]; intros ? <- [ | hy ty] LEN_EQ y_wf EQ; simpl in *; try congruence; try word; inv y_wf.
        destruct (hx =? hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS; simpl in *...
        + eapply IH... all: try (word || done). intros i i_bound x1 x2 H_x1 H_x2.
          eapply EQ with (i := S i)... word.
        + contradiction H_OBS. rewrite <- eqb_eq... eapply EQ with (i := 0%nat)... word.
    Qed.
    Next Obligation with eauto 2.
      destruct x_wf as [x_wf x_len], y_wf as [y_wf y_len]. simpl in *. split.
      - revert len x_len y y_len y_wf. induction x_wf as [ | hx tx hx_wf tx_wf IH]; intros ? <- [ | hy ty] LEN_EQ y_wf NE H_contra; simpl in *; try congruence; try word; inv y_wf.
        destruct (hx =? hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS; simpl in *...
        + eapply IH with (y := ty)... all: try (word || done). intros i i_bound x1 x2 H_x1 H_x2.
          eapply H_contra with (i := S i)... word.
        + contradiction H_OBS. rewrite <- eqb_eq... eapply H_contra with (i := 0%nat)... word.
      - revert len x_len y y_len y_wf. induction x_wf as [ | hx tx hx_wf tx_wf IH]; intros ? <- [ | hy ty] LEN_EQ y_wf NE; simpl in *; try congruence; try word; inv y_wf.
        + contradiction NE. word.
        + destruct (hx =? hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS; simpl in *...
          eapply IH with (y := ty)... all: try (word || done). intros H_contra. contradiction NE.
          intros [ | i'] i_bound x1 x2 H_x1 H_x2; simpl in *...
          * rewrite eqb_eq... all: try congruence.
          * eapply H_contra with (i := i')... word.
    Qed.

    Context {hsOrd : hsOrd A (hsEq := hsEq)}.

    Fixpoint vectorGt (v1 : list A) (v2 : list A) : bool :=
      match v1 with
      | [] => false 
      | h1 :: t1 =>
        match v2 with
        | [] => false 
        | h2 :: t2 => if h1 =? h2 then vectorGt t1 t2 else h1 >? h2
        end
      end.

    Lemma vectorGt_transitive l1 l2 l3 (l1_wf : Forall well_formed l1) (l2_wf : Forall well_formed l2) (l3_wf : Forall well_formed l3) :
      vectorGt l3 l2 = true ->
      vectorGt l2 l1 = true ->
      vectorGt l3 l1 = true.
    Proof with congruence || trivial || eauto 2.
      revert l1 l3 l1_wf l3_wf; induction l2_wf as [ | x2 l2 x2_wf l2_wf IH]; intros ? ? [ | x1 l1 x1_wf l1_wf] [ | x3 l3 x3_wf l3_wf]; simpl in *...
      repeat (
        let H_OBS := fresh "H_OBS" in
        lazymatch goal with
        | [ |- context [ (eqb _ _) ] ] => destruct (eqb _ _) as [ | ] eqn: H_OBS; [rewrite eqb_eq in H_OBS | rewrite eqb_neq in H_OBS]; trivial
        | [ |- context [ (ltb _ _) ] ] => destruct (ltb _ _) as [ | ] eqn: H_OBS; [rewrite ltb_lt in H_OBS | rewrite ltb_nlt in H_OBS]; trivial
        end
      ); intros l3_gt_l2 l2_gt_l1...
      - contradiction H_OBS1. eapply eqProp_transitivity with (y := x2)...
      - contradiction H_OBS0. eapply eqProp_transitivity with (y := x3)... eapply eqProp_symmetry...
      - pose proof (ltProp_trichotomy x3 x1) as [? | [? | ?]]; try done.
        contradiction (ltProp_irreflexivity x3 x2)... eapply ltProp_transitivity with (y := x1)...
      - contradiction H_OBS. eapply eqProp_transitivity with (y := x1)... eapply eqProp_symmetry...
      - pose proof (ltProp_trichotomy x3 x1) as [? | [? | ?]]; try done.
        contradiction (ltProp_irreflexivity x2 x1)... eapply ltProp_transitivity with (y := x3)...
      - contradiction (ltProp_irreflexivity x1 x3); try done.
        + eapply eqProp_symmetry...
        + eapply ltProp_transitivity with (y := x2)...
      - contradiction H_OBS4. eapply ltProp_transitivity with (y := x2)...
    Qed.

    Lemma vectorGt_implies_not_vectorEq l1 l2 (l1_wf : Forall well_formed l1) (l2_wf : Forall well_formed l2) :
      vectorGt l1 l2 = true ->
      vectorEq l1 l2 = false.
    Proof.
      revert l2 l2_wf. induction l1_wf as [ | x1 xs1 x1_wf xs1_wf IH]; intros ? [ | x2 xs2 x2_wf xs2_wf]; simpl; intros EQ; try congruence.
      destruct (x1 =? x2) as [ | ] eqn: H_OBS; [rewrite eqb_eq in H_OBS | rewrite eqb_neq in H_OBS]; trivial; simpl in *.
      eapply IH; trivial.
    Qed.

    Lemma vectorEq_implies_not_vectorGt l1 l2 (l1_wf : Forall well_formed l1) (l2_wf : Forall well_formed l2) :
      vectorEq l1 l2 = true ->
      vectorGt l1 l2 = false.
    Proof.
      revert l2 l2_wf. induction l1_wf as [ | x1 xs1 x1_wf xs1_wf IH]; intros ? [ | x2 xs2 x2_wf xs2_wf]; simpl; intros EQ; try congruence.
      destruct (x1 =? x2) as [ | ] eqn: H_OBS; [rewrite eqb_eq in H_OBS | rewrite eqb_neq in H_OBS]; trivial; simpl in *.
      - eapply IH; trivial.
      - congruence.
    Qed.

    #[global, program]
    Instance hsOrd_vector (len : nat) : SessionPrelude.hsOrd (list A) (hsEq := hsEq_vector len) :=
      { ltProp xs1 xs2 := vectorGt xs2 xs1 = true
      ; ltb xs1 xs2 := vectorGt xs2 xs1
      }.
    Next Obligation with eauto 2.
      simpl in *. destruct x_wf as [x_wf x_len], y_wf as [y_wf y_len].
      rewrite vectorEq_implies_not_vectorGt...
      change vectorEq with (@eqb (list A) _ (hsEq_vector len)).
      rewrite eqb_comm... rewrite eqb_eq...
    Qed.
    Next Obligation with eauto 2.
      simpl in *. destruct x_wf as [x_wf x_len], y_wf as [y_wf y_len], z_wf as [z_wf z_len].
      simpl in *. eapply vectorGt_transitive with (l2 := y)...
    Qed.
    Next Obligation with eauto 2.
      simpl in *. destruct x_wf as [x_wf x_len], y_wf as [y_wf y_len]. revert y y_wf y_len. revert len x_len.
      induction x_wf as [ | hx tx hx_wf tx_wf IH]; intros ? <- ? [ | hy ty hy_wf ty_wf] LEN_EQ; simpl in *; try congruence...
      - right. left. word.
      - destruct (hx =? hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS; simpl in *...
        + apply eqProp_symmetry in H_OBS... rewrite <- eqb_eq in H_OBS... rewrite H_OBS. symmetry in LEN_EQ.
          specialize (IH (length ty) (f_equal Nat.pred LEN_EQ) ty ty_wf eq_refl). destruct IH as [IH | [IH | IH]]; try tauto.
          right. left. intros [ | i'] i_bound x1 x2 H_x1 H_x2; simpl in *.
          * rewrite eqb_comm in H_OBS... congruence.
          * eapply IH with (i := i')... word.
        + rewrite <- eqb_neq in H_OBS... rewrite eqb_comm in H_OBS... rewrite H_OBS...
          pose proof (ltProp_trichotomy hy hx) as [H_lt | [H_eq | H_gt]]...
          * rewrite <- ltb_lt in H_lt... right. right...
          * rewrite eqb_neq in H_OBS... contradiction H_OBS...
          * rewrite <- ltb_lt in H_gt...
    Qed.
    Next Obligation with eauto 2.
      simpl. reflexivity.
    Qed.
    Next Obligation with eauto 2.
      simpl in *. destruct (vectorGt y x) as [ | ]; split; intros ?; congruence.
    Qed.

  End VECTOR.

  Lemma Forall_True {A : Type} (xs : list A)
    : Forall (fun _ => True) xs.
  Proof.
    induction xs as [ | x xs IH]; eauto.
  Qed.

  Lemma vectorEq_true_iff `{hsEq_A : hsEq A (well_formed := fun _ => True)} (eqProp_spec : ∀ x : A, ∀ y : A, eqProp x y <-> x = y) (len : nat) (x : list A) (y : list A)
    (x_len : length x = len)
    (y_len : length y = len)
    : vectorEq x y = true <-> x = y.
  Proof.
    revert y len x_len y_len. induction x as [ | hx tx IH], y as [ | hy ty]; simpl; intros ? <- LEN_EQ; simpl; try congruence.
    - tauto.
    - destruct (eqb hx hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS; simpl; eauto 2.
      + rewrite eqProp_spec in H_OBS. rewrite IH; eauto 2. split; congruence.
      + rewrite eqProp_spec in H_OBS. split; congruence.
  Qed.

End SessionPrelude.
