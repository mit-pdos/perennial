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
  Module path.
    Record t :=
      mk { dir: string;
           fname: string; }.
  End path.

  Section GoModel.
  Context `{model_wf:GoModelWf}.
  Implicit Types (dir p:string) (fh:File) (bs:slice.t byte).

  (* the types of the arguments are determined by their name, using the implicit
  types given above *)
  Inductive Op : Type -> Type :=
  | Open dir p : Op File
  | Close fh : Op unit
  | List dir (na: NonAtomicArgs unit) : Op (retT na (slice.t string))
  | Size fh : Op uint64
  | ReadAt fh (off:uint64) (len:uint64) : Op (slice.t byte)
  | Create dir p : Op File
  | Append fh bs' : Op unit
  | Delete dir p : Op unit
  | Rename dir1 p1 dir2 p2 : Op unit
  | Truncate dir p : Op unit
  | AtomicCreate dir p bs : Op unit
  | Link dir1 p1 dir2 p2 : Op bool
  .

  Section OpWrappers.

    Context {Op'} {i:Injectable Op Op'}.
    Notation proc := (proc Op').
    Notation "'Call!' op" := (Call (inject op) : proc _) (at level 0, op at level 200).
    Definition open dir p : proc _ := Call! Open dir p.
    Definition close fh : proc _ := Call! Close fh.
    Definition list dir : proc (slice.t string) :=
      Bind (Call (inject (List dir Begin)))
           (fun _ => Call (inject (List dir (FinishArgs tt)))).
    Definition size fh : proc _ := Call! Size fh.
    Definition readAt fh off len : proc _ := Call! ReadAt fh off len.
    Definition create dir p : proc _ := Call! Create dir p.
    Definition append fh bs : proc _ := Call! Append fh bs.
    Definition delete dir p : proc _ := Call! Delete dir p.
    Definition rename dir1 p1 dir2 p2 : proc _ := Call! Rename dir1 p1 dir2 p2.
    Definition truncate dir p : proc _ := Call! Truncate dir p.
    Definition atomicCreate dir p bs : proc _ := Call! AtomicCreate dir p bs.
    Definition link dir1 p1 dir2 p2 := Call! Link dir1 p1 dir2 p2.

  End OpWrappers.

  Inductive OpenMode := Read | Write.

  Global Instance path_countable : countable.Countable path.t.
  Proof.
    apply (countable.inj_countable'
            (fun '(path.mk dir fname) => (dir, fname))
            (fun '(dir, fname) => path.mk dir fname)).
    destruct x; simpl; auto.
  Qed.

  Record State :=
    mkState { heap: Data.State;
              dirs: gmap.gmap string LockStatus;
              files: gmap.gmap path.t (List.list byte);
              fds: gmap.gmap File (path.t * OpenMode); }.

  Global Instance _eta : Settable State :=
    settable! mkState <heap; dirs; files; fds>.

  Definition readFd (fh: File) (m: OpenMode) : relation State State path.t :=
    readSome (fun s => match s.(fds) !! fh with
                    | Some (p, m') => if m == m' then Some p else None
                    | _ => None
                    end).

  Import RelationNotations.

  Definition readDir (files: gmap.gmap path.t (List.list byte)) (dir0: string) : List.list string :=
    map_fold (fun '(path.mk dir _) _data ents =>
               if dir == dir0 then dir::ents else ents)
             [] files.

  Definition step T (op:Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | Open dir name =>
      let p := path.mk dir name in
      _ <- readSome (fun s => s.(files) !! p);
        fh <- such_that (fun s fh => s.(fds) !! fh = None);
        _ <- puts (set fds (insert fh (p, Read)));
        pure fh

    | Close fh =>
      puts (set fds (map_delete fh))

    | List dir na =>
      s <- readSome (fun s => s.(dirs) !! dir);
        match na return relation _ _ (retT na (slice.t string)) with
        | Begin =>
          s' <- readSome (fun _ => lock_acquire Reader s);
            puts (set dirs (insert dir s'))
        | FinishArgs _ =>
          s' <- readSome (fun _ => lock_release Reader s);
            _ <- puts (set dirs (insert dir s'));
            l <- reads (fun s => readDir s.(files) dir);
            r <- such_that (fun s (r: ptr _) => Data.getAlloc r s.(heap) = None /\ r <> nullptr _);
            _ <- puts (set heap (set Data.allocs (updDyn (a:=Ptr.Heap string) r (Unlocked, l))));
            pure {| slice.ptr := r;
                    slice.offset := 0;
                    slice.length := length l; |}
        end

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

    | Create dir name =>
      let p := path.mk dir name in
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

    | Delete dir name =>
      let p := path.mk dir name in
      (* Delete(p) fails if there is an open fh pointing to p - this is a safe
      approximation of real behavior, where the underlying inode for the file is
      retained as long as there are open files *)
      (_ <- such_that (fun s fh =>
                        exists m, s.(fds) !! fh = Some (p, m));
         error)
      (* delete's error case supercedes this succesful deletion case *)
      + (s <- readSome (fun s => s.(dirs) !! p.(path.dir));
         _ <- readSome (fun _ => lock_available Writer s);
       _ <- readSome (fun s => s.(files) !! p);
           puts (set files (map_delete p)))

    | Truncate dir name =>
      let p := path.mk dir name in
      _ <- readSome (fun s => s.(files) !! p);
        puts (set files (insert p nil))

    | Rename dir1 name1 dir2 name2 =>
      let p1 := path.mk dir1 name1 in
      let p2 := path.mk dir2 name2 in
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

    | AtomicCreate dir name p =>
      let path := path.mk dir name in
      _ <- readNone (fun s => s.(files) !! path);
      let! (s, alloc) <- readSome (fun st => Data.getAlloc p.(slice.ptr) st.(heap));
           bs <- readSome (fun _ => Data.getSliceModel p alloc);
           _ <- readSome (fun _ => lock_available Reader s);
        puts (set files (insert path bs))

    | Link dir1 name1 dir2 name2 =>
        let p1 := path.mk dir1 name1 in
        let p2 := path.mk dir2 name2 in
        bs <- readSome (fun s => s.(files) !! p1);
        (_ <- such_that (fun s fh =>
                         s.(fds) !! fh = Some (p1, Write)); error)
        + (mdest <- reads (fun s => s.(files) !! p2);
             match mdest with
             | Some _ =>
               (* model hardlink as copy since there's no way to modify a file
               after it's been created *)
               _ <- puts (set files (insert p2 bs)); pure true
             | None => pure false
             end)
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
       dirs := ∅;
       files := ∅;
       fds := ∅; |}.

  End GoModel.
End FS.
