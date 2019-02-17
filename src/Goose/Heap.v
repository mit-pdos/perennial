From RecordUpdate Require Import RecordUpdate.

From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Spec.SemanticsHelpers.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.

From stdpp Require Import base.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.

Inductive LockMode := Reader | Writer.

Module Data.
  Inductive Op : Type -> Type :=
  | NewAlloc T (v:T) (len:uint64) : Op (ptr T)
  | PtrDeref T (p:ptr T) (off:uint64) : Op T
  | PtrStore T (p:ptr T) (off:uint64) (x:T) : Op unit

  | SliceAppend T (s:slice.t T) (x:T) : Op (slice.t T)
  | SliceAppendSlice T (s:slice.t T) (s':slice.t T) : Op (slice.t T)

  | NewMap V : Op (Map V)
  | MapAlter `(m:Map V) (k:uint64) (f:option V -> option V) : Op unit
  | MapLookup `(m:Map V) (k:uint64) : Op (option V)
  | MapStartIter `(m:Map V) : Op (list (uint64*V))
  | MapEndIter `(m:Map V) : Op unit

  | NewLock : Op LockRef
  | LockAcquire : LockRef -> LockMode -> Op unit
  | LockRelease : LockRef -> LockMode -> Op unit

  (* expose uint64 little endian encoding/decoding *)
  | Uint64Get : slice.t byte -> Op uint64
  | Uint64Put : slice.t byte -> uint64 -> Op unit

  | BytesToString : slice.t byte -> Op string
  | StringToBytes : string -> Op (slice.t byte)
  .

  Section OpWrappers.

    Context {Op'} {i:Injectable Op Op'}.
    Notation proc := (proc Op').
    Notation "'Call!' op" := (Call (inject op) : proc _) (at level 0, op at level 200).

    Definition newAlloc T v len :=
      Call! @NewAlloc T v len.

    Definition newPtr T {GoZero:HasGoZero T} : proc (ptr T) :=
      newAlloc (zeroValue T) 1.

    Definition newSlice T {GoZero:HasGoZero T} len : proc (slice.t T) :=
      Bind (newAlloc (zeroValue T) len)
           (fun p => Ret {| slice.ptr := p;
                         slice.length := len;
                         slice.offset := 0 |}).

    Definition ptrDeref T p off :=
      Call! @PtrDeref T p off.

    Definition readPtr T (p: ptr T) : proc T :=
      ptrDeref p 0.

    Definition sliceRead T (s: slice.t T) off : proc T :=
      ptrDeref s.(slice.ptr) (s.(slice.offset) + off).

    Definition ptrStore T p off x :=
      Call! @PtrStore T p off x.

    Definition writePtr T (p: ptr T) x :=
      ptrStore p 0 x.

    Definition sliceWrite T (s: slice.t T) off (x:T) : proc unit :=
      ptrStore s.(slice.ptr) (s.(slice.offset) + off) x.

    Definition sliceAppend T s x :=
      Call! @SliceAppend T s x.

    Definition sliceAppendSlice T s s' :=
      Call! @SliceAppendSlice T s s'.

    Definition newMap V := Call! NewMap V.

    Definition mapAlter V m k f := Call! @MapAlter V m k f.
    Definition mapLookup V m k := Call! @MapLookup V m k.
    Definition mapStartIter V m := Call! @MapStartIter V m.
    Definition mapEndIter V m := Call! @MapEndIter V m.

    Definition mapGet V {_:HasGoZero V} (m: Map V) k : proc (V * bool) :=
      Bind (mapLookup m k)
           (fun mv => match mv with
                   | Some v => Ret (v, true)
                   | None => Ret (zeroValue V, false)
                   end).

    Definition newLock := Call! NewLock.
    Definition lockAcquire l m := Call! LockAcquire l m.
    Definition lockRelease l m := Call! LockRelease l m.

    Definition uint64Get p := Call! Uint64Get p.
    Definition uint64Put p n := Call! Uint64Put p n.

    Definition bytesToString bs := Call! BytesToString bs.
    Definition stringToBytes s := Call! StringToBytes s.
  End OpWrappers.

  Definition hashtableM V := gmap.gmap uint64 V.

  Inductive LockStatus := Locked | ReadLocked (num:nat) | Unlocked.

  Definition ptrModel (code:Ptr.ty) : Type :=
    match code with
    | Ptr.Heap T => list T
    | Ptr.Map V => hashtableM V
    | Ptr.Lock => LockStatus
    end.

  Record State : Type :=
    mkState { allocs : DynMap Ptr.t ptrModel; }.

  Instance _eta : Settable _ :=
    mkSettable (constructor mkState <*> allocs)%set.

  Definition getAlloc (s:State) ty (p:Ptr.t ty) : option (ptrModel ty) :=
    getDyn s.(allocs) p.

  Definition updAllocs ty (p:Ptr.t ty) (x:ptrModel ty)
    : relation State State unit :=
    puts (set allocs (updDyn p x)).

  Import RelationNotations.

  Definition step T (op:Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | NewAlloc v len =>
      r <- such_that (fun s (r:ptr _) => getAlloc s r = None /\ r <> nullptr _);
        _ <- updAllocs r (List.repeat v len);
        pure r
    | PtrDeref p off =>
      alloc <- such_that (fun s alloc => getAlloc s p = Some alloc);
        x <- such_that (fun _ x => List.nth_error alloc off = Some x);
        pure x
    (* TODO: rest of the semantics *)
    | _ => error
    end.

  Global Instance empty_heap : Empty State := {| allocs := ∅ |}.

End Data.

Arguments Data.newPtr {Op' i} T {GoZero}.
Arguments Data.newSlice {Op' i} T {GoZero} len.
