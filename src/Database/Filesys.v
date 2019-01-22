From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.

From RecordUpdate Require Import RecordSet.
Import ApplicativeNotations.

From Classes Require Import EqualDec.
Import EqualDecNotation.

From stdpp Require gmap.
From stdpp Require Import fin_maps.

From Coq Require Import String.

Definition Path := string.

Instance path_eqdec : EqualDec Path.
Proof.
  unfold Path.
  typeclasses eauto.
Defined.

Module FS.
  Implicit Types (p:Path) (fh:Fd) (bs:ByteString).

  (* the types of the arguments are determined by their, using the implicit
  types given above *)
  Inductive Op : Type -> Type :=
  | Open p : Op Fd
  | Close fh : Op unit
  | List : Op (list Path)
  | Size fh : Op uint64
  | ReadAt fh (off:uint64) (len:uint64) : Op ByteString
  | Create p : Op Fd
  | Append fh bs' : Op unit
  | Delete p : Op unit
  | Rename p1 p2 : Op bool (* returns false if the destination exists *)
  | Truncate p : Op unit
  | AtomicCreate p bs : Op unit
  .

  Definition open p : proc Op Fd := Call (Open p).
  Definition close fh := Call (Close fh).
  Definition list := Call (List).
  Definition size fh := Call (Size fh).
  Definition readAt fh off len := Call (ReadAt fh off len).
  Definition create p := Call (Create p).
  Definition append fh bs := Call (Append fh bs).
  Definition delete p := Call (Delete p).
  Definition truncate p := Call (Truncate p).
  Definition atomicCreate p bs := Call (AtomicCreate p bs).

  Inductive OpenMode := Read | Write.

  Record State :=
    mkState { files: gmap Path ByteString;
              fds: gmap Fd (Path * OpenMode); }.

  Instance _eta : Settable State :=
    mkSettable (constructor mkState <*> files <*> fds)%set.

  Definition readFd (fh: Fd) (m: OpenMode) : relation State State Path :=
    readSome (fun s => match s.(fds) !! fh with
                    | Some (p, m') => if m == m' then Some p else None
                    | _ => None
                    end).

  Import RelationNotations.

  Definition step T (op:Op T) : relation State State T :=
    (* NOTE: dependent match annotations improve error messages (the error
    message can now include the expected type T based on branch) *)
    match op in Op T return relation State State T with
    | Open p =>
      _ <- readSome (fun s => s.(files) !! p);
        fh <- such_that (fun s fh => s.(fds) !! fh = None);
        _ <- puts (set fds (insert fh (p, Read)));
        pure fh
    | Close fh =>
      puts (set fds (map_delete fh))
    | List =>
      reads (fun s => map fst (map_to_list s.(files)))
    | Size fh =>
        bs <- (p <- readFd fh Read;
                readSome (fun s => s.(files) !! p));
        pure (BS.length bs)
    | ReadAt fh off len =>
      p <- readFd fh Read;
        bs <- (p <- readFd fh Read;
                readSome (fun s => s.(files) !! p));
        pure (BS.take len (BS.drop off bs))
    | Create p =>
      _ <- readNone (fun s => s.(files) !! p);
        fh <- such_that (fun s fh => s.(fds) !! fh = None);
        _ <- puts (set files (insert p BS.empty));
        _ <- puts (set fds (insert fh (p, Write)));
        pure fh
    | Append fh bs' =>
      p <- readFd fh Write;
        bs <- readSome (fun s => s.(files) !! p);
        puts (set files (insert p (BS.append bs bs')))
    | Delete p =>
      (* Delete(p) fails if there is an open fh pointing to p - this is a safe
      approximation of real behavior, where the underlying inode for the file is
      retained as long as there are open files *)
      (_ <- such_that (fun s fh =>
                        exists m, s.(fds) !! fh = Some (p, m));
         error)
      (* delete's error case supercedes this succesful deletion case *)
      + (_ <- readSome (fun s => s.(files) !! p);
           puts (set files (map_delete p)))
    | Truncate p =>
      _ <- readSome (fun s => s.(files) !! p);
        puts (set files (insert p BS.empty))
    | Rename p1 p2 =>
      bs <- readSome (fun s => s.(files) !! p1);
        dst <- reads (fun s => s.(files) !! p2);
        match dst with
        | Some _ =>  pure false
        | None => _ <- puts (set files (map_delete p1));
                   _ <- puts (set files (insert p2 bs));
                   pure true
        end
    | AtomicCreate p bs =>
      _ <- readNone (fun s => s.(files) !! p);
        puts (set files (insert p bs))
    end.

End FS.
