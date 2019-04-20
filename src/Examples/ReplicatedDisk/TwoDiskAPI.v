From Coq Require Import List.

From stdpp Require Import gmap.
From RecoveryRefinement Require Export Lib.

Module TwoDisk.
  Definition size := 1000.
  Definition addr := nat.

  Inductive diskId :=
  | d0
  | d1.

  Definition disk := gmap addr nat.

  Inductive DisksState :=
  | BothDisks (d_0:disk) (d_1:disk)
  | OnlyDisk0 (d_0:disk)
  | OnlyDisk1 (d_1:disk).

  Inductive Op : Type -> Type :=
  | Read_Mem (i:addr) : Op nat
  | Write_Mem (i:addr) (v:nat) : Op unit
  | CAS (i:addr) (vold: nat) (vnew:nat) : Op nat
  | Read_Disk (id: diskId) (i:addr) : Op (option nat)
  | Write_Disk (id: diskId) (i:addr) (v:nat) : Op unit
  | MaybeFailDisk : Op unit
  | Fail : Op unit.

  Record State := mkState { mem_state: gmap addr nat; disks_state: DisksState }.

  Definition disk0 ds : option disk :=
    match disks_state ds with
    | BothDisks d_0 _ => Some d_0
    | OnlyDisk0 d => Some d
    | OnlyDisk1 _ => None
    end.

  Definition disk1 ds : option disk :=
    match disks_state ds with
    | BothDisks _ d_1 => Some d_1
    | OnlyDisk0 _ => None
    | OnlyDisk1 d => Some d
    end.

  Definition get_disk (i: diskId) (state: State) : option disk :=
    match i with
    | d0 => disk0 state
    | d1 => disk1 state
    end.

  Definition wf_range (d: gmap addr nat) :=
    (∀ i, is_Some (d !! i) ↔ i < size).

  Definition wf_disk (md: option disk) :=
    match md with
      | Some d => wf_range d
      | None => True
    end.

  Definition state_wf s :=
    wf_range (mem_state s) ∧ wf_disk (disk0 s) ∧ wf_disk (disk1 s).

  Definition lookup_default (i: addr) (s: gmap addr nat) : nat :=
    match s !! i with
    | Some n => n
    | None => 0
    end.

  Definition upd_default (i: addr) (v: nat) (s: gmap addr nat) : gmap addr nat :=
    match s !! i with
    | Some _ => <[i := v]>s
    | None => s
    end.

  Definition lookup_mem (i: addr) : State -> nat :=
    fun s => lookup_default i (mem_state s).

  Definition lookup_disk id (i: addr) : State -> option nat :=
    fun s =>
      match get_disk id s with
        | None => None
        | Some d => Some (lookup_default i d)
      end.

  Definition set_disk' (i:diskId) (state:DisksState) (d:disk) : DisksState :=
    match i with
    | d0 => match state with
            | BothDisks _ d_1 => BothDisks d d_1
            | OnlyDisk0 _ => OnlyDisk0 d
            | OnlyDisk1 d_1 => BothDisks d d_1
            end
    | d1 => match state with
            | BothDisks d_0 _ => BothDisks d_0 d
            | OnlyDisk0 d_0 => BothDisks d_0 d
            | OnlyDisk1 _ => OnlyDisk1 d
            end
    end.

  (* Fails disk i if both disks are active, otherwise has no effect *)
  Definition maybe_fail_disk' (i:diskId) (state:DisksState) : DisksState :=
    match i with
    | d0 => match state with
            | BothDisks _ d_1 => OnlyDisk1 d_1
            | _ => state
            end
    | d1 => match state with
            | BothDisks d_0 _ => OnlyDisk0 d_0
            | _ => state
            end
    end.

  Definition upd_mem (i: addr) (v: nat) :=
    fun s => {| mem_state := upd_default i v (mem_state s);
                disks_state := disks_state s |}.

  Definition upd_disk (id: diskId) (i: addr) (v: nat) : State -> State :=
    fun s => {| mem_state := mem_state s;
                disks_state :=
                  match get_disk id s with
                  | Some d => set_disk' id (disks_state s) (upd_default i v d)
                  | None => disks_state s
                  end|}.

  Definition maybe_fail_disk (id: diskId) : State -> State :=
    fun s => {| mem_state := mem_state s;
                disks_state := maybe_fail_disk' id (disks_state s) |}.

  Import RelationNotations.
  Definition cas_rel (i: addr) (vold: nat) (vnew: nat): RelationAlgebra.relation State State nat :=
    v <- reads (lookup_mem i);
    if nat_eq_dec v vold then
        puts (upd_mem i vnew);;
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

  Definition init_state :=
    {| mem_state := init_zero; disks_state := BothDisks init_zero init_zero |}.

  Lemma wf_init_zero: wf_range init_zero.
  Proof.
    intros i. split.
    - intros Hsome. apply not_ge. intros ?.
      rewrite init_zero_lookup_ge_None // in Hsome; last lia.
      eapply is_Some_None; eauto.
    - intros ?. rewrite init_zero_lookup_lt_zero //. eauto.
  Qed.

  Lemma init_state_wf:
    state_wf init_state.
  Proof. split_and!; apply wf_init_zero. Qed.

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

  Definition crash_fun := (fun s => {| mem_state := init_zero; disks_state := disks_state s|}).

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Read_Mem i => reads (lookup_mem i)
         | Write_Mem i v => puts (upd_mem i v)
         | Read_Disk id i => reads (lookup_disk id i)
         | Write_Disk id i v => puts (upd_disk id i v)
         | CAS i vold vnew => cas_rel i vold vnew
         | MaybeFailDisk => rel_or (puts (maybe_fail_disk d0))
                                     (puts (maybe_fail_disk d1))
         | Fail => error
         end;
       crash_step := puts crash_fun;
       finish_step := puts crash_fun |}.

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof. eexists; econstructor. Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof. inversion 1; congruence. Qed.

  Definition l : Layer Op :=
    {| Layer.OpState := State;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       finish_total := crash_total_ok;
       crash_non_err := crash_non_err_ok;
       finish_non_err := crash_non_err_ok;
       initP := fun s => s = init_state |}.
End TwoDisk.

Definition read_mem i := Call (TwoDisk.Read_Mem i).
Definition write_mem i v := Call (TwoDisk.Write_Mem i v).
Definition read_disk id i := Call (TwoDisk.Read_Disk id i).
Definition write_disk id i v := Call (TwoDisk.Write_Disk id i v).
Definition cas i vold vnew := Call (TwoDisk.CAS i vold vnew).
Definition assert (b: bool) := if b then (_ <- Ret (); Ret ())%proc else Call (TwoDisk.Fail).

Definition lock i : proc TwoDisk.Op unit :=
  Loop (fun (_ : unit) =>
          x <- cas i 0 1;
          Ret (if nat_eq_dec x 0 then
                  DoneWithOutcome tt
                else
                  ContinueOutcome tt)
       )%proc tt.
Definition unlock i : proc TwoDisk.Op unit := write_mem i 0.