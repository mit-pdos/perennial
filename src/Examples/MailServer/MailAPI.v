From RecordUpdate Require Import RecordSet.

From RecoveryRefinement Require Export Lib.
From RecoveryRefinement Require Import Spec.SemanticsHelpers Spec.LockDefs.
From RecoveryRefinement.Goose Require Import Machine Heap Examples.MailServer.

From RecoveryRefinement.Helpers Require Import RelationAlgebra RecordZoom.
From stdpp Require gmap.
From stdpp Require Import fin_maps.

Module Mail.
  Section GoModel.
  Context `{model_wf:GoModelWf}.

  Implicit Types (uid:uint64).

  Inductive Op : Type -> Type :=
  | Pickup uid : Op (list (string * list byte))
  | CreateMessages (msgs: list (string * list byte)) : Op (slice.t Message.t)
  | Deliver uid (msg: slice.t byte) : Op unit
  | Delete uid (msgID: string) : Op unit
  | Unlock uid : Op unit
  | DataOp T (op: Data.Op T) : Op T
  .

  Record State : Type :=
    { heap: Data.State;
      messages: gmap.gmap uint64 (LockStatus * gmap.gmap string (list byte)); }.

  Global Instance etaState : Settable _ :=
    settable! Build_State <heap; messages>.

  Import RelationNotations.


  (* TODO: generalize these definitions in Filesys *)
  Definition lookup K `{countable.Countable K} V (proj:State -> gmap.gmap K V) (k:K) : relation State State V :=
    readSome (fun s => s.(proj) !! k).

  Definition createSlice V (data: List.list V) : relation State State (slice.t V) :=
    r <- such_that (fun s (r: ptr _) => Data.getAlloc r s.(heap) = None /\ r <> nullptr _);
      _ <- puts (set heap (set Data.allocs (updDyn (a:=Ptr.Heap V) r (Unlocked, data))));
      pure {| slice.ptr := r;
              slice.offset := 0;
              slice.length := length data; |}.

  Fixpoint createMessages (msgs: list (string * list byte)) : relation State State (list Message.t) :=
    match msgs with
    | nil => pure nil
    | (name,msg)::msgs =>
      contents <- createSlice msg;
        messageData <- createMessages msgs;
        pure (Message.mk name contents::messageData)
    end.

  Section OpWrappers.

    Definition pickup uid : proc Op (slice.t Message.t) :=
      (msgs <- Call (Pickup uid);
       Call (CreateMessages msgs))%proc.

  End OpWrappers.

  (* TODO: move this to Heap *)
  Definition readSlice T (p: slice.t T) : relation State State (list T) :=
    let! (s, alloc) <- readSome (fun s => Data.getAlloc p.(slice.ptr) s.(heap));
         _ <- readSome (fun _ => lock_available Reader s);
         (* TODO: need bounds checks *)
         pure (list.take p.(slice.length) (list.drop p.(slice.offset) alloc)).

  Definition step T (op: Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | Pickup uid =>
      let! (s, msgs) <- lookup messages uid;
        match lock_acquire Writer s with
        | Some s =>
           _ <- puts (set messages <[uid := (s, msgs)]>);
           pure (map_to_list msgs)
        | None =>
          none
        end
    | CreateMessages msgs =>
        messageData <- createMessages msgs;
        createSlice messageData
    | Deliver uid msg =>
      let! (s, msgs) <- lookup messages uid;
        n <- such_that (fun _ (n: string) => msgs !! n = None);
        msg <- readSlice msg;
        puts (set messages <[ uid := (s, <[ n := msg ]> msgs) ]>)
    | Delete uid msg =>
      let! (s, msgs) <- lookup messages uid;
           match s with
           | Locked =>
             _ <- Filesys.FS.unwrap (msgs !! msg);
               puts (set messages <[ uid := (s, delete msg msgs) ]>)
           (* the lock will never be read locked, but for convenience we
              consider that an error as well *)
           | _ => error
           end
    | Unlock uid =>
      let! (s, msgs) <- lookup messages uid;
           s <- Filesys.FS.unwrap (lock_release Writer s);
           puts (set messages <[uid := (s, msgs)]>)
    | DataOp op => _zoom heap (Data.step op)
    end.

  Definition crash_step : relation State State unit := pure tt.
  Definition finish_step : relation State State unit := pure tt.

  Definition sem : Dynamics Op State :=
    {| Proc.step := step;
       Proc.crash_step := crash_step;
       Proc.finish_step := finish_step; |}.

  Definition initP (s:State) :=
    s.(heap) = ∅ /\
    (forall (uid: uint64),
        (uid < 100 -> s.(messages) !! uid = Some (Unlocked, ∅)) /\
        (uid >= 100 -> s.(messages) !! uid = None)).

  Definition l : Layer Op.
    refine {| Layer.sem := sem;
              trace_proj := fun _ => nil;
              Layer.initP := initP;
           |}; simpl; intros; auto.
    - eexists; econstructor.
    - eexists; econstructor.
    - inversion H; subst; congruence.
    - inversion H; subst; congruence.
  Defined.

  End GoModel.
End Mail.
