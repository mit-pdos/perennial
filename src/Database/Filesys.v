From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.InjectOp.
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

  (* the types of the arguments are determined by their name, using the implicit
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
  | Rename p1 p2 : Op unit
  | Truncate p : Op unit
  | AtomicCreate p bs : Op unit

  (* Additional operations that seem to be required for the mail server. *)
  | Random : Op uint64
  | Link p1 p2 : Op bool
  .

  Section OpWrappers.

    Context {Op'} {i:Injectable Op Op'}.
    Notation proc := (proc Op').
    Notation "'Call!' op" := (Call (inject op)) (at level 0, op at level 200).
    Definition open p : proc _ := Call! Open p.
    Definition close fh : proc _ := Call! Close fh.
    Definition list : proc _ := Call! List.
    Definition size fh : proc _ := Call! Size fh.
    Definition readAt fh off len : proc _ := Call! ReadAt fh off len.
    Definition create p : proc _ := Call! Create p.
    Definition append fh bs : proc _ := Call! Append fh bs.
    Definition delete p : proc _ := Call! Delete p.
    Definition rename p1 p2 : proc _ := Call! Rename p1 p2.
    Definition truncate p : proc _ := Call! Truncate p.
    Definition atomicCreate p bs : proc _ := Call! AtomicCreate p bs.

    Definition random : proc _ := Call! Random.
    Definition link p1 p2 : proc _ := Call! Link p1 p2.

  End OpWrappers.

  Inductive OpenMode := Read | Write.

  Record State :=
    mkState { files: gmap Path ByteString;
              (* Mail server uses link+unlink so it would be nicer to have
               * an explicit model of inodes and hard links.
               *)
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
      (* Rename requires that the destination path not be open *)
      (_ <- such_that (fun s fh =>
                        exists m, s.(fds) !! fh = Some (p2, m));
         error)
      (* Rename always creates the destination directory - other behaviors
      require checks, which makes the operation non-atomic.

       Linux does have renameat2 for renaming without overwriting, presumably
       atomically, but it would be complicated to use, especially from
       Haskell. *)
      + (bs <- readSome (fun s => s.(files) !! p1);
           _ <- puts (set files (map_delete p1));
           puts (set files (insert p2 bs)))
    | AtomicCreate p bs =>
      _ <- readNone (fun s => s.(files) !! p);
        puts (set files (insert p bs))

    (* Mail server specific ops *)
    | Random =>
      r <- such_that (fun s r => True);
      pure r
    | Link p1 p2 =>
      (* XXX need hard link model state *)
      pure true
    end.

  Definition crash_step : relation State State unit :=
    puts (set fds (fun _ => ∅)).

End FS.
