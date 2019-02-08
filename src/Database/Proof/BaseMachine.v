From RecoveryRefinement Require Export CSL.WeakestPre.

From RecoveryRefinement Require Export Database.Base.

Set Implicit Arguments.

Class baseG (Σ: gFunctors) := BaseG {}.

Instance baseG_irisG `{baseG Σ} : irisG Op Base.l Σ.
Admitted.

Definition ioref_mapsto `{baseG Σ} {T} (r:IORef T) (x:T) : iProp Σ.
Admitted.

Definition hashtable_mapsto `{baseG Σ} {V}
           (r:HashTable V) (v:Data.hashtableM V) : iProp Σ.
Admitted.

Definition array_mapsto `{baseG Σ} {T}
           (r:Array T) (v: list T) : iProp Σ.
Admitted.

Definition path_mapsto `{baseG Σ} (p: Path) (bs: ByteString) : iProp Σ.
Admitted.

Definition fd_mapsto `{baseG Σ} (fh: Fd) (s:Path * FS.OpenMode) : iProp Σ.
Admitted.

Class GenericMapsTo `{baseG Σ} (Addr:Type) :=
  { ValTy : Type;
    generic_mapsto : Addr -> ValTy -> iProp Σ; }.

Instance ioref_gen_mapsto `{baseG Σ} T : GenericMapsTo (@IORef T)
  := {| generic_mapsto := ioref_mapsto; |}.
Instance hashtable_gen_mapsto `{baseG Σ} V : GenericMapsTo (@HashTable V)
  := {| generic_mapsto := hashtable_mapsto; |}.
Instance array_gen_mapsto `{baseG Σ} T : GenericMapsTo (@Array T)
  := {| generic_mapsto := array_mapsto; |}.
Instance path_gen_mapsto `{baseG Σ} : GenericMapsTo Path :=
  {| generic_mapsto := path_mapsto |}.
Instance fd_gen_mapsto `{baseG Σ} : GenericMapsTo Fd :=
  {| generic_mapsto := fd_mapsto |}.

Notation "l ↦ v" := (generic_mapsto l v)
                      (at level 20) : bi_scope.
