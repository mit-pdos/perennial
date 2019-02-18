From RecordUpdate Require Import RecordUpdate.

From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Spec.SemanticsHelpers.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.

From Tactical Require Import ProofAutomation.

From stdpp Require Import base.

Import ProcNotations.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.

Inductive LockMode := Reader | Writer.

Module Data.
  Inductive Op : Type -> Type :=
  | NewAlloc T (v:T) (len:uint64) : Op (ptr T)
  | PtrDeref T (p:ptr T) (off:uint64) : Op T
  | PtrStore T (p:ptr T) (args:NonAtomicArgs (uint64 * T)) : Op unit

  | SliceAppend T (s:slice.t T) (x:T) : Op (slice.t T)
  | SliceAppendSlice T (s:slice.t T) (s':slice.t T) : Op (slice.t T)

  | NewMap V : Op (Map V)
  | MapAlter `(m:Map V) (args:NonAtomicArgs
                                (uint64 * (option V -> option V))) : Op unit
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
      (p <- newAlloc (zeroValue T) len;
         Ret {| slice.ptr := p;
                slice.length := len;
                slice.offset := 0 |})%proc.

    Definition ptrDeref T p off :=
      Call! @PtrDeref T p off.

    Definition readPtr T (p: ptr T) : proc T :=
      ptrDeref p 0.

    Definition sliceRead T (s: slice.t T) off : proc T :=
      ptrDeref s.(slice.ptr) (s.(slice.offset) + off).

    Definition ptrStore T p off x : proc _ :=
      (_ <- Call (inject (@PtrStore T p Begin));
         Call (inject (PtrStore p (FinishArgs (off, x)))))%proc.

    Definition writePtr T (p: ptr T) x :=
      ptrStore p 0 x.

    Definition sliceWrite T (s: slice.t T) off (x:T) : proc unit :=
      ptrStore s.(slice.ptr) (s.(slice.offset) + off) x.

    Definition sliceAppend T s x :=
      Call! @SliceAppend T s x.

    Definition sliceAppendSlice T s s' :=
      Call! @SliceAppendSlice T s s'.

    Definition newMap V := Call! NewMap V.

    Definition mapAlter V m (k: uint64) (f: option V -> option V) : proc _ :=
      (_ <- Call (inject (@MapAlter V m Begin));
        Call (inject (MapAlter m (FinishArgs (k, f)))))%proc.

    Definition mapLookup V m k := Call! @MapLookup V m k.

    Definition mapIter V (m: Map V) (body: uint64 -> V -> proc unit) : proc unit :=
      (kvs <- Call (inject (MapStartIter m));
         _ <- List.fold_right
           (fun '(k, v) p => Bind p (fun _ => body k v))
           (Ret tt) kvs;
         Call (inject (MapEndIter m)))%proc.

    Definition mapGet V {_:HasGoZero V} (m: Map V) k : proc (V * bool) :=
      (mv <- mapLookup m k;
        match mv with
        | Some v => Ret (v, true)
        | None => Ret (zeroValue V, false)
        end)%proc.

    Definition newLock := Call! NewLock.

    Definition lockAcquire l m := Call! LockAcquire l m.
    Definition lockRelease l m := Call! LockRelease l m.

    Definition uint64Get p := Call! Uint64Get p.
    Definition uint64Put p n := Call! Uint64Put p n.

    Definition bytesToString bs := Call! BytesToString bs.
    Definition stringToBytes s := Call! StringToBytes s.
  End OpWrappers.

  Inductive LockStatus := Locked | ReadLocked (num:nat) | Unlocked.

  (* We model a hashtable as if it had a lock, but the calls to acquire and
  release this lock never block but instead error on failure.

     I can't yet tell if this is a new idea, obvious, an old idea, or weird.
   *)
  Definition hashtableM V := (LockStatus * gmap.gmap uint64 V)%type.

  Definition ptrModel (code:Ptr.ty) : Type :=
    match code with
    | Ptr.Heap T =>
      (* note that for convenience we use a reader-writer LockStatus, but the
      way its used (only Writer acquires/releases) guarantees that it is always
      either Unlocked or Locked, never ReadLocked *)
      LockStatus * list T
    | Ptr.Map V => hashtableM V
    | Ptr.Lock => LockStatus
    end.

  Record State : Type :=
    mkState { allocs : DynMap Ptr.t ptrModel; }.

  Instance _eta : Settable _ :=
    mkSettable (constructor mkState <*> allocs)%set.

  Definition getAlloc ty (p:Ptr.t ty) (s:State) : option (ptrModel ty) :=
    getDyn s.(allocs) p.

  Definition updAllocs ty (p:Ptr.t ty) (x:ptrModel ty)
    : relation State State unit :=
    puts (set allocs (updDyn p x)).

  Import RelationNotations.

  (* returns [Some s'] when the lock should be acquired to status s', and None
  if the lock would block *)
  Definition lock_acquire (m:LockMode) (s:LockStatus) : option LockStatus :=
    match m, s with
    | Reader, ReadLocked n => Some (ReadLocked (S n))
    (* note that the number is one less than the number of readers, so that
       ReadLocked 0 means something *)
    | Reader, Unlocked => Some (ReadLocked 0)
    | Writer, Unlocked => Some Locked
    | _, _ => None
    end.

  (* returns [Some s'] when the lock should be released to status s', and None if this usage is an error *)
  Definition lock_release (m:LockMode) (s:LockStatus) : option LockStatus :=
    match m, s with
    | Reader, ReadLocked 0 => Some Unlocked
    | Reader, ReadLocked (S n) => Some (ReadLocked n)
    | Writer, Locked => Some Unlocked
    | _, _ => None
    end.

  (* lock_available reports whether acquiring and releasing the lock atomically
  would succeed; phrased as an option unit for compatibility with readSome *)
  Definition lock_available (m:LockMode) (s:LockStatus) : option unit :=
    match m, s with
    | Reader, ReadLocked _ => Some tt
    | _, Unlocked => Some tt
    | _, _ => None
    end.

  (* sanity check lock definitions: if you can acquire a lock, you can always
  release it the same way and get back to where you started *)
  Lemma lock_acquire_release m s :
    forall s', lock_acquire m s = Some s' ->
          lock_release m s' = Some s.
  Proof.
    destruct m, s; simpl; inversion 1; auto.
  Qed.

  (* sanity check lock_available *)
  Theorem lock_available_acquire_release m s :
    lock_available m s = Some tt <->
    (exists s', lock_acquire m s = Some s' /\
           lock_release m s' = Some s).
  Proof.
    destruct m, s; simpl; (intuition eauto); propositional; try congruence.
  Qed.

  Fixpoint list_nth_upd A (l: list A) (n: nat) (x: A) : option (list A) :=
    match n with
    | 0 => match l with
          | nil => None
          | x0::xs => Some (x::xs)
          end
    | S n' => match l with
             | nil => None
             | x0::xs => match list_nth_upd xs n' x with
                        | Some xs' => Some (x0::xs')
                        | None => None
                        end
             end
    end.

  Theorem list_nth_upd_length A (l: list A) n x l' :
    list_nth_upd l n x = Some l' ->
    length l = length l'.
  Proof.
    generalize dependent l.
    generalize dependent l'.
    induction n; simpl.
    - destruct l; simpl; inversion 1; subst.
      simpl; auto.
    - destruct l; simpl; inversion 1; subst.
      destruct_with_eqn (list_nth_upd l n x); try congruence.
      inv_clear H.
      simpl; eauto.
  Qed.

  Theorem list_nth_upd_get_nth A (l: list A) n x l' :
    list_nth_upd l n x = Some l' ->
    List.nth_error l' n = Some x.
  Proof.
    generalize dependent l.
    generalize dependent l'.
    induction n; simpl.
    - destruct l; simpl; inversion 1; subst; auto.
    - destruct l; simpl; inversion 1; subst.
      destruct_with_eqn (list_nth_upd l n x); try congruence.
      inv_clear H.
      eauto.
  Qed.

  Definition step T (op:Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | NewAlloc v len =>
      r <- such_that (fun s (r:ptr _) => getAlloc r s = None /\ r <> nullptr _);
        _ <- updAllocs r (Unlocked, List.repeat v len);
        pure r
    | PtrDeref p off =>
      let! (s, alloc) <- readSome (getAlloc p);
           _ <- readSome (fun _ => lock_available Reader s);
        x <- readSome (fun _ => List.nth_error alloc off);
        pure x
    | PtrStore p args =>
      let! (s, alloc) <- readSome (getAlloc p);
      match args with
      | Begin => s' <- readSome (fun _ => lock_acquire Writer s);
                  updAllocs p (s', alloc)
      | FinishArgs (off, x) => s' <- readSome (fun _ => lock_release Writer s);
                                alloc' <- readSome (fun _ => list_nth_upd alloc off x);
                                updAllocs p (s', alloc')
      end
    | NewMap V =>
      r <- such_that (fun s (r:Map _) => getAlloc r s = None /\ r <> nullptr _);
        _ <- updAllocs r (Unlocked, ∅);
          pure r
    | MapLookup r k =>
      let! (s, m) <- readSome (fun s => getDyn s.(allocs) r);
           _ <- readSome (fun _ => lock_available Reader s);
        pure (m !! k)
    | MapAlter r args =>
      let! (s, m) <- readSome (fun s => getDyn s.(allocs) r);
      match args with
      | Begin => s' <- readSome (fun _ => lock_acquire Writer s);
                  updAllocs r (s', m)
      | FinishArgs (k, f) => s' <- readSome (fun _ => lock_release Writer s);
                              updAllocs r (s', partial_alter f k m)
      end
    | MapStartIter r =>
      let! (s, m) <- readSome (fun s => getDyn s.(allocs) r);
           s' <- readSome (fun _ => lock_acquire Reader s);
           _ <- updAllocs r (s', m);
           (* TODO: allow any permutation *)
           pure (fin_maps.map_to_list m)
    | MapEndIter r =>
      let! (s, m) <- readSome (fun s => getDyn s.(allocs) r);
           s' <- readSome (fun _ => lock_release Reader s);
           _ <- updAllocs r (s', m);
           pure tt
    | NewLock =>
      r <- such_that (fun s (r:LockRef) => getAlloc r s = None /\ r <> nullptr _);
        _ <- updAllocs r Unlocked;
        pure r
    | LockAcquire r m =>
      v <- readSome (fun s => getDyn s.(allocs) r);
        match lock_acquire m v with
        | Some s' => updAllocs r s'
        | None =>
          (* disabled transition; will only become available when the lock
             is freed by its owner *)
          none
        end
    | LockRelease r m =>
      v <- readSome (fun s => getDyn s.(allocs) r);
        match lock_release m v with
        | Some s' => updAllocs r s'
        | None => error (* attempt to free the lock incorrectly *)
        end
    | _ => error
    end.

  Global Instance empty_heap : Empty State := {| allocs := ∅ |}.

End Data.

Arguments Data.newPtr {Op' i} T {GoZero}.
Arguments Data.newSlice {Op' i} T {GoZero} len.
