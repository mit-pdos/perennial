From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.

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

  Inductive Op : Type -> Type :=
  | Open : Path -> Op Fd
  | Close : Fd -> Op unit
  | List : Op (list Path)
  | Size : Fd -> Op uint64
  (* readAt fh offset length *)
  | ReadAt : Fd -> uint64 -> uint64 -> Op ByteString
  | Create : Path -> Op Fd
  | Append : Fd -> ByteString -> Op unit
  | Delete : Path -> Op unit
  | Truncate : Fd -> Op unit
  | AtomicCreate : Path -> ByteString -> Op unit
  .

  Definition open (p:Path) : proc Op Fd := Call (Open p).
  Definition close fh := Call (Close fh).
  Definition list := Call (List).
  Definition size fh := Call (Size fh).
  Definition readAt fh off len := Call (ReadAt fh off len).
  Definition create p := Call (Create p).
  Definition append fh bs := Call (Append fh bs).
  Definition delete p := Call (Delete p).
  Definition truncate fh := Call (Truncate fh).
  Definition atomicCreate p bs := Call (AtomicCreate p bs).

  Inductive OpenMode := Read | Write.

  Record State :=
    { files: gmap Path ByteString;
      fds: gmap Fd (Path * OpenMode); }.

  Definition upd_files (f: _ -> _) (s:State) : State :=
    {| files := f s.(files);
       fds := s.(fds); |}.

  Definition upd_fds (f: _ -> _) (s:State) : State :=
    {| files := s.(files);
       fds := f s.(fds); |}.

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
        _ <- puts (upd_fds (insert fh (p, Read)));
        pure fh
    | Close fh =>
      puts (upd_fds (map_delete fh))
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
      fh <- such_that (fun s fh => s.(fds) !! fh = None);
        _ <- readNone (fun s => s.(files) !! p);
        _ <- puts (upd_files (insert p BS.empty));
        _ <- puts (upd_fds (insert fh (p, Write)));
        pure fh
    | Append fh bs' =>
      p <- readFd fh Write;
        bs <- readSome (fun s => s.(files) !! p);
        puts (upd_files (insert p (BS.append bs bs')))
    | Delete p =>
      (* Delete(p) fails if there is an open fh pointing to p - this is a safe
      approximation of real behavior, where the underlying inode for the file is
      retained as long as there are open files *)
      (_ <- such_that (fun s fh =>
                        exists m, s.(fds) !! fh = Some (p, m)); error)
      (* delete's error case supercedes this succesful deletion case *)
      + puts (upd_files (map_delete p))
    | Truncate fh =>
      p <- (p <- readFd fh Write;
             _ <- readSome (fun s => s.(files) !! p);
             pure p);
        puts (upd_files (insert p BS.empty))
    | AtomicCreate p bs =>
      _ <- readNone (fun s => s.(files) !! p);
        puts (upd_files (insert p bs))
    end.

End FS.
