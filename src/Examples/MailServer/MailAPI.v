From RecordUpdate Require Import RecordSet.
From stdpp Require gmap.
From stdpp Require Import fin_maps.

From Armada Require Export Lib.
From Armada Require Import Spec.SemanticsHelpers Spec.LockDefs.
From Armada.Goose Require Import Machine Heap Examples.MailServer.

From Armada.Helpers Require Import RecordZoom.

From Transitions Require Import Relations.

Module Mail.
  Section GoModel.
  Context `{model_wf:GoModelWf}.

  Implicit Types (uid:uint64).

  Inductive Op : Type -> Type :=
  | Open : Op unit
  | Pickup_Start uid : Op (list (string * list byte))
  | Pickup_End uid (msgs: list (string * list byte)) : Op (slice.t Message.t)
  | Deliver_Start uid (msg: slice.t byte) : Op unit
  | Deliver_End uid (msg: slice.t byte) : Op unit
  | Delete uid (msgID: string) : Op unit
  | Lock uid : Op unit
  | Unlock uid : Op unit
  | DataOp T (op: Data.Op T) : Op T
  .

  Inductive MailboxStatus :=
  | MPickingUp
  | MLocked
  | MUnlocked.

  Definition mailbox_lock_acquire (s: MailboxStatus) : option MailboxStatus :=
    match s with
    | MPickingUp => None
    | MLocked => None
    | MUnlocked => Some MPickingUp
    end.

  Definition mailbox_finish_pickup (s: MailboxStatus) : option MailboxStatus :=
    match s with
    | MPickingUp => Some MLocked
    | MLocked => None
    | MUnlocked => None
    end.

  Definition mailbox_lock_release (s: MailboxStatus) : option MailboxStatus :=
    match s with
    | MPickingUp => None
    | MLocked => Some MUnlocked
    | MUnlocked => None
    end.

  Record State : Type :=
    { heap: Data.State;
      messages: gmap.gmap uint64 (MailboxStatus * gmap.gmap string (list byte));
      open : bool;
    }.

  Global Instance etaState : Settable _ :=
    settable! Build_State <heap; messages; open>.

  Import RelationNotations.


  (* TODO: generalize these definitions in Filesys *)
  Definition lookup K `{countable.Countable K} V (proj:State -> gmap.gmap K V) (k:K)
    : relation State State V :=
    readSome (fun s => s.(proj) !! k).

  Definition createSlice V (data: List.list V) : relation State State (slice.t V) :=
    r <- such_that (fun s (r: ptr _) => Data.getAlloc r s.(heap) = None /\ r <> nullptr _);
    salloc <- such_that (fun _ (salloc : slice.t _ * List.list V) =>
                           let (sli, alloc) := salloc in
                           sli.(slice.ptr) = r ∧ Data.getSliceModel sli alloc = Some data);
    _ <- puts (set heap (set Data.allocs (updDyn (a:=Ptr.Heap V) r (Unlocked, snd salloc))));
    pure (fst salloc).

  Definition createMessages (msgs: list (string * list byte)) : list Message.t :=
    map (λ '(name, contents), Message.mk name (bytes_to_string contents)) msgs.

  Section OpWrappers.

    Definition pickup uid : proc Op (slice.t Message.t) :=
      (msgs <- Call (Pickup_Start uid);
       Call (Pickup_End uid msgs))%proc.

    Definition deliver uid msg : proc Op unit :=
      (_ <- Call (Deliver_Start uid msg);
       Call (Deliver_End uid msg))%proc.

  End OpWrappers.

  (* TODO: move this to Heap *)
  Definition readSlice T (p: slice.t T) : relation State State (list T) :=
    let! (s, alloc) <- readSome (fun s => Data.getAlloc p.(slice.ptr) s.(heap));
         _ <- readSome (fun _ => lock_available Reader s);
         (* TODO: need bounds checks *)
         pure (list.take p.(slice.length) (list.drop p.(slice.offset) alloc)).

  Definition readLockSlice T (p: slice.t T) : relation State State unit :=
    let! (s, alloc) <- readSome (fun s => Data.getAlloc p.(slice.ptr) s.(heap));
         s' <- readSome (fun _ => lock_acquire Reader s);
         _ <- readSome (fun _ => Data.getSliceModel p alloc);
         puts (set heap (set Data.allocs (updDyn (a:=Ptr.Heap T) p.(slice.ptr) (s', alloc)))).

  Definition readUnlockSlice T (p: slice.t T) : relation State State (list T) :=
    let! (s, alloc) <- readSome (fun s => Data.getAlloc p.(slice.ptr) s.(heap));
         s' <- readSome (fun _ => lock_release Reader s);
         _ <- puts (set heap (set Data.allocs (updDyn (a:=Ptr.Heap T) p.(slice.ptr) (s', alloc))));
         readSome (fun _ => Data.getSliceModel p alloc).

  Definition step_closed T (op: Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | Open =>
      _ <- puts (set open (λ _, true));
      puts (set messages (λ m, (λ inbox, (MUnlocked, snd inbox)) <$> m))
    | _ => error
    end.

  Definition step_open T (op: Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | Pickup_Start uid =>
      let! (s, msgs) <- lookup messages uid;
        match mailbox_lock_acquire s with
        | Some s =>
           _ <- puts (set messages <[uid := (s, msgs)]>);
           such_that (λ _ msgs', Permutation.Permutation msgs' (map_to_list msgs))
        | None =>
          none
        end
    | Pickup_End uid msgs =>
        let! (s, msgs') <- lookup messages uid;
        s <- Filesys.FS.unwrap (mailbox_finish_pickup s);
        _ <- puts (set messages <[uid := (s, msgs')]>);
        createSlice (createMessages msgs)
    | Deliver_Start uid msg => readLockSlice msg
    | Deliver_End uid msg =>
      let! (s, msgs) <- lookup messages uid;
      n <- such_that (fun _ (n: string) => msgs !! n = None);
      msg <- readUnlockSlice msg;
      puts (set messages <[ uid := (s, <[ n := msg ]> msgs) ]>)
    | Delete uid msg =>
      let! (s, msgs) <- lookup messages uid;
           match s with
           | MLocked =>
             _ <- Filesys.FS.unwrap (msgs !! msg);
               puts (set messages <[ uid := (s, delete msg msgs) ]>)
           | _ => error
           end
    | Lock uid =>
      let! (s, msgs) <- lookup messages uid;
           s <- Filesys.FS.unwrap (mailbox_lock_acquire s);
           puts (set messages <[uid := (s, msgs)]>)
    | Unlock uid =>
      let! (s, msgs) <- lookup messages uid;
           s <- Filesys.FS.unwrap (mailbox_lock_release s);
           puts (set messages <[uid := (s, msgs)]>)
    | DataOp op =>
      (* The MailServer does not involve map operations or little endian encoding,
         so we do not prove refinement for these operations. *)
      match op with
      | Data.NewMap _ => error
      | Data.MapLookup _ _ => error
      | Data.MapAlter _ _ _ _ => error
      | Data.MapStartIter _ => error
      | Data.MapEndIter _ => error
      | Data.Uint64Get _ _ => error
      | Data.Uint64Put _ _ _ => error
      |  _ => _zoom heap (Data.step op)
      end
    | Open => error
    end.

  Definition step T (op: Op T) : relation State State T :=
    i <- reads open;
    match i with
    | true => step_open op
    | false => step_closed op
    end.

  Definition crash_step : relation State State unit :=
    _ <- puts (set open (λ _, false));
    puts (set heap (λ _, ∅)).

  Definition finish_step : relation State State unit :=
    _ <- puts (set open (λ _, false));
    puts (set heap (λ _, ∅)).

  Definition sem : Dynamics Op State :=
    {| Proc.step := step;
       Proc.crash_step := crash_step;
       Proc.finish_step := finish_step; |}.

  Definition initP (s:State) :=
    s.(heap) = ∅ /\
    s.(open) = false /\
    (forall (uid: uint64),
        (uid < 100 -> s.(messages) !! uid = Some (MUnlocked, ∅)) /\
        (uid >= 100 -> s.(messages) !! uid = None)).

  Lemma crash_step_val:
    ∀ s1 : State, ∃ s2 : State, sem.(Proc.crash_step) s1 (Val s2 ()).
  Proof.
    intros s1.
    do 3 eexists; split; econstructor.
  Qed.

  Lemma finish_step_val:
    ∀ s1 : State, ∃ s2 : State, sem.(Proc.finish_step) s1 (Val s2 ()).
  Proof.
    intros s1.
    do 3 eexists; split; econstructor.
  Qed.

  Lemma crash_step_non_err:
    ∀ (s1 : State) (ret : Return State ()), sem.(Proc.crash_step) s1 ret → ret ≠ Err.
  Proof.
    intros s1 ret H.
    destruct ret; inversion H; eauto.
    repeat deex. inversion H1.
  Qed.

  Lemma finish_step_non_err:
    ∀ (s1 : State) (ret : Return State ()), sem.(Proc.finish_step) s1 ret → ret ≠ Err.
  Proof.
    intros s1 ret H.
    destruct ret; inversion H; eauto.
    repeat deex. inversion H1.
  Qed.

  Definition l : Layer Op.
    refine {| Layer.sem := sem;
              trace_proj := fun _ => nil;
              Layer.initP := initP;
           |}; intros; try reflexivity;
    eauto using crash_step_val, finish_step_val,
    crash_step_non_err, finish_step_non_err.
  Defined.

  End GoModel.
End Mail.
