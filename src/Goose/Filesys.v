From RecordUpdate Require Import RecordUpdate.
From Tactical Require Import ProofAutomation.

From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Spec.SemanticsHelpers.
From RecoveryRefinement Require Import Spec.LockDefs.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.
From RecoveryRefinement.Goose Require Import Heap.

From Classes Require Import EqualDec.
From stdpp Require gmap.
From stdpp Require Import fin_maps.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.

Import EqualDecNotation.

Module FS.
  Section GoModel.
  Context `{model_wf:GoModelWf}.
  Implicit Types (p:string) (fh:File) (bs:slice.t byte).

  (* the types of the arguments are determined by their name, using the implicit
  types given above *)
  Inductive Op : Type -> Type :=
  | Open p : Op File
  | Close fh : Op unit
  | List : Op (slice.t string)
  | Size fh : Op uint64
  | ReadAt fh (off:uint64) (len:uint64) : Op (slice.t byte)
  | Create p : Op File
  | Append fh bs' : Op unit
  | Delete p : Op unit
  | Rename p1 p2 : Op unit
  | Truncate p : Op unit
  | AtomicCreate p bs : Op unit
  | Link p1 p2 : Op bool
  .

  Section OpWrappers.

    Context {Op'} {i:Injectable Op Op'}.
    Notation proc := (proc Op').
    Notation "'Call!' op" := (Call (inject op) : proc _) (at level 0, op at level 200).
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
    Definition link p1 p2 := Call! Link p1 p2.

  End OpWrappers.

  Inductive OpenMode := Read | Write.

  Record State :=
    mkState { heap: Data.State;
              files: gmap.gmap string (List.list byte);
              fds: gmap.gmap File (string * OpenMode); }.

  Global Instance _eta : Settable State :=
    mkSettable (constructor mkState <*> heap <*> files <*> fds)%set.

  Definition readFd (fh: File) (m: OpenMode) : relation State State string :=
    readSome (fun s => match s.(fds) !! fh with
                    | Some (p, m') => if m == m' then Some p else None
                    | _ => None
                    end).

  Import RelationNotations.

  Definition step T (op:Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | Open p =>
      _ <- readSome (fun s => s.(files) !! p);
        fh <- such_that (fun s fh => s.(fds) !! fh = None);
        _ <- puts (set fds (insert fh (p, Read)));
        pure fh
    | Close fh =>
      puts (set fds (map_delete fh))
    | List =>
      (* TODO: this should be non-atomic *)
      l <- reads (fun s => map fst (map_to_list s.(files)));
        error
    | Size fh =>
        bs <- (p <- readFd fh Read;
                readSome (fun s => s.(files) !! p));
        pure (length bs)
    | ReadAt fh off len =>
      p <- readFd fh Read;
        bs <- (p <- readFd fh Read;
                readSome (fun s => s.(files) !! p));
        let read_bs := list.take len (list.drop off bs) in
        r <- such_that (fun s (r: ptr _) => Data.getAlloc r s.(heap) = None /\ r <> nullptr _);
          _ <- puts (set heap (set Data.allocs (updDyn (a:=Ptr.Heap byte) r (Unlocked, read_bs))));
          pure {| slice.ptr := r;
                  slice.offset := 0;
                  slice.length := length read_bs; |}
    | Create p =>
      _ <- readNone (fun s => s.(files) !! p);
        fh <- such_that (fun s fh => s.(fds) !! fh = None);
        _ <- puts (set files (insert p nil));
        _ <- puts (set fds (insert fh (p, Write)));
        pure fh
    | Append fh p' =>
      path <- readFd fh Write;
      let! (s, alloc) <- readSome (fun st => Data.getAlloc p'.(slice.ptr) st.(heap));
           bs' <- readSome (fun _ => Data.getSliceModel p' alloc);
           _ <- readSome (fun _ => lock_available Reader s);
           bs <- readSome (fun s => s.(files) !! path);
           puts (set files (insert path (bs ++ bs')))
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
        puts (set files (insert p nil))
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
    | AtomicCreate path p =>
      _ <- readNone (fun s => s.(files) !! path);
      let! (s, alloc) <- readSome (fun st => Data.getAlloc p.(slice.ptr) st.(heap));
           bs <- readSome (fun _ => Data.getSliceModel p alloc);
           _ <- readSome (fun _ => lock_available Reader s);
        puts (set files (insert path bs))
    (* TODO: figure out how to write link semantics *)
    | Link p1 p2 => error
    end.

  Definition crash_step : relation State State unit :=
    _ <- puts (set fds (fun _ => ∅));
      puts (set heap (fun _ => ∅)).

  Theorem crash_step_non_err s res :
      crash_step s res ->
      res <> Err.
  Proof.
    destruct res; eauto.
    unfold crash_step, puts; simpl; intros.
    (intuition auto); propositional; discriminate.
  Qed.

  Global Instance empty_fs : Empty State :=
    {| heap := ∅;
       files := ∅;
       fds := ∅; |}.

  End GoModel.
End FS.
