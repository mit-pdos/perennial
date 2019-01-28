From RecoveryRefinement Require Import Database.Base.

(** These are unit tests for the data structures, written in Coq to get proper
typechecking without a lot of unsafeCoerce.

Each function returns a proc (A*A), where the first elements is the actual value and the second is the expected. We run them all in database/test/DataStructureSpec.hs as hspec tests.
 *)

Local Open Scope proc.

Import UIntNotations.
Local Open Scope u64.

Notation spec A := ((A * A)%type) (only parsing).

Definition shouldReturn A (p: proc A) (expected:A) : proc (spec A) :=
  actual <- p;
    Ret (actual, expected).

Definition iorefRead bs : proc (spec ByteString) :=
  r <- Data.newIORef bs;
    shouldReturn (Data.readIORef r) bs.

Definition iorefWrite bs : proc (spec ByteString) :=
  r <- Data.newIORef bs;
    let new := BS.append bs bs in
    _ <- Data.writeIORef r new;
      shouldReturn (Data.readIORef r) new.

Definition arrayLength : proc (spec (uint64 * uint64)) :=
  r <- Data.newArray uint64;
    sz0 <- Data.arrayLength r;
    _ <- Data.arrayAppend r 1;
    _ <- Data.arrayAppend r 2;
    sz1 <- Data.arrayLength r;
    Ret ((sz0, sz1), (fromNum 0, fromNum 2)).

Definition arrayGet : proc (spec uint64) :=
  r <- Data.newArray uint64;
    _ <- Data.arrayAppend r 2;
    _ <- Data.arrayAppend r 3;
    shouldReturn (Data.arrayGet r 1) 3.

Definition hashtableLookup bs :
  proc (spec (option ByteString * option ByteString)) :=
  r <- Data.newHashTable ByteString;
    _ <- Data.hashTableAlter r 3 (fun _ => Some bs);
    x1 <- Data.hashTableLookup r 1;
    x2 <- Data.hashTableLookup r 3;
    Ret ((x1, x2), (None, Some bs)).

Definition hashtableIntLookup :
  proc (spec (option uint64 * option uint64)) :=
  r <- Data.newHashTable uint64;
    _ <- Data.hashTableAlter r 3 (fun _ => Some 4096);
    x1 <- Data.hashTableLookup r 1;
    x2 <- Data.hashTableLookup r 3;
    Ret ((x1, x2), (None, Some 4096)).

Definition hashtableReadAll :
  proc (spec (uint64 * uint64)) :=
  r <- Data.newHashTable uint64;
    _ <- Data.hashTableAlter r 2 (fun _ => Some (fromNum 5));
    a <- Data.hashTableReadAll r;
    e <- Data.arrayGet a 0;
    Ret (e, (fromNum 2, fromNum 5)).

(* this just shouldn't deadlock *)
Definition locking : proc (spec unit) :=
  l <- Data.newLock;
    _ <- Data.lockAcquire Reader l;
    _ <- Data.lockAcquire Reader l;
    _ <- Data.lockRelease Reader l;
    _ <- Data.lockRelease Reader l;
    _ <- Data.lockAcquire Writer l;
    _ <- Data.lockRelease Writer l;
    Ret (tt, tt).
