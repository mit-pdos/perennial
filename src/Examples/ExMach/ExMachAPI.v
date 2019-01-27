From Coq Require Import List.

From stdpp Require Import gmap.
From RecoveryRefinement Require Export Lib.

Module ExMach.
  Definition size := 1000.
  Definition addr := nat.

  Inductive Op : Type -> Type :=
  | Read_Mem (i:addr) : Op nat
  | Write_Mem (i:addr) (v:nat) : Op unit
  | CAS (i:addr) (vold: nat) (vnew:nat) : Op nat
  | Read_Disk (i:addr) : Op nat
  | Write_Disk (i:addr) (v:nat) : Op unit.

  Record State := mkState { mem_state: gmap addr nat; disk_state: gmap addr nat }.

  Definition state_wf s :=
    (∀ i, is_Some (mem_state s !! i) ↔ i < size) ∧
    (∀ i, is_Some (disk_state s !! i) ↔ i < size).

  Definition get_default (i: addr) (s: gmap addr nat) : nat :=
    match s !! i with
    | Some n => n
    | None => 0
    end.

  Definition set_default (i: addr) (v: nat) (s: gmap addr nat) : gmap addr nat :=
    match s !! i with
    | Some _ => <[i := v]>s
    | None => s
    end.

  Definition get_mem (i: addr) : State -> nat :=
    fun s => get_default i (mem_state s).
  Definition get_disk (i: addr) : State -> nat :=
    fun s => get_default i (disk_state s).

  Definition set_mem (i: addr) (v: nat) : State -> State :=
    fun s => {| mem_state := set_default i v (mem_state s);
                disk_state := disk_state s |}.
  Definition set_disk (i: addr) (v: nat) : State -> State :=
    fun s => {| mem_state := mem_state s;
                disk_state := set_default i v (disk_state s) |}.


  Import RelationNotations.
  Definition cas_rel (i: addr) (vold: nat) (vnew: nat): RelationAlgebra.relation State State nat :=
    v <- reads (get_mem i);
    if nat_eq_dec v vold then
        puts (set_mem i vnew);;
        pure v
    else
        pure v.

  Fixpoint init_zero_aux (n: nat) (s: gmap addr nat) :=
    match n with
    | O => s
    | S n' => <[n' := O]>(init_zero_aux n' s)
    end.

  Definition init_zero := init_zero_aux size gmap_empty.

  Lemma init_zero_insert_zero i:
    i < size →
    <[i := 0]> init_zero = init_zero.
  Proof.
    rewrite /init_zero. induction 1.
    - rewrite //=. rewrite insert_insert //.
    - rewrite //=. rewrite insert_commute; last by lia. rewrite IHle //=.
  Qed.

  Lemma init_zero_lookup_lt_zero i:
    i < size →
    init_zero !! i = Some 0.
  Proof.
    rewrite /init_zero. induction 1.
    - rewrite lookup_insert //=.
    - rewrite //=. rewrite lookup_insert_ne; last (by lia). eauto.
  Qed.

  Lemma init_zero_lookup_ge_None i:
    ¬ i < size →
    init_zero !! i = None.
  Proof.
    revert i. rewrite /init_zero. induction size => i ?.
    - rewrite //=.
    - rewrite lookup_insert_ne; last by lia.
      rewrite IHn; auto.
  Qed.

  Lemma well_sized_mem_0_init (mem: gmap addr nat):
    (∀ i, is_Some (mem !! i) ↔ i < size) →
    (λ _, 0) <$> mem = init_zero.
  Proof.
    intros. rewrite -leibniz_equiv_iff => i.
    destruct (nat_lt_dec i size).
    * rewrite init_zero_lookup_lt_zero //.
      rewrite lookup_fmap.
      edestruct (H i). destruct H1; eauto. rewrite H1 //=.
    * rewrite lookup_fmap.
      edestruct (H i). destruct (mem !! i) as [|] eqn:Heq.
      ** rewrite Heq in H0. exfalso. intuition eauto.
      ** rewrite init_zero_lookup_ge_None //=.
  Qed.

  Definition crash_fun := (fun s => {| mem_state := init_zero; disk_state := disk_state s|}).

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Read_Mem i => reads (get_mem i)
         | Write_Mem i v => puts (set_mem i v)
         | Read_Disk i => reads (get_disk i)
         | Write_Disk i v => puts (set_disk i v)
         | CAS i vold vnew => cas_rel i vold vnew
         end;
       crash_step := puts crash_fun |}. 

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof. eexists; econstructor. Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof. inversion 1; congruence. Qed.

  Definition l : Layer Op :=
    {| Layer.State := State;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       crash_non_err := crash_non_err_ok;
       initP := fun s => s = {| mem_state := init_zero; disk_state := init_zero |} |}.
End ExMach.

Definition read_mem i := Call (ExMach.Read_Mem i).
Definition write_mem i v := Call (ExMach.Write_Mem i v).
Definition read_disk i := Call (ExMach.Read_Disk i).
Definition write_disk i v := Call (ExMach.Write_Disk i v).
Definition cas i vold vnew := Call (ExMach.CAS i vold vnew).

Definition lock i : proc ExMach.Op unit :=
  Loop (fun (_ : unit) =>
          x <- cas i 0 1;
          Ret (if nat_eq_dec x 0 then
                  DoneWithOutcome tt
                else
                  ContinueOutcome tt)
       )%proc tt.
Definition unlock i : proc ExMach.Op unit := write_mem i 0. 