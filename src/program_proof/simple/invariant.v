From RecordUpdate Require Import RecordUpdate.

From Perennial.algebra Require Import liftable auth_map.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import disk_prelude.

From Goose.github_com.mit_pdos.go_nfsd Require Import simple.
From Perennial.program_proof Require Import obj.obj_proof marshal_proof addr_proof crash_lockmap_proof addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import jrnl.sep_jrnl_proof.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List range_set.
From Perennial.program_logic Require Import spec_assert.
From Perennial.goose_lang.lib Require Import slice.typed_slice into_val.
From Perennial.program_proof Require Import simple.spec.

Class simpleG Σ :=
  { simple_fs_stateG :> ghost_varG Σ (gmap u64 (list u8));
    simple_mapG :> mapG Σ u64 (list u8);
    simple_jrnlG :> jrnlG Σ;
    simple_lockmapG :> lockmapG Σ;
  }.

Definition simpleΣ :=
  #[ ghost_varΣ (gmap u64 (list u8));
   mapΣ u64 (list u8);
   jrnlΣ;
   lockmapΣ
  ].

#[global]
Instance subG_simpleΣ Σ : subG simpleΣ Σ → simpleG Σ.
Proof. solve_inG. Qed.

Section heap.
Context `{!heapGS Σ}.
Context `{!simpleG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Record simple_names := {
  simple_jrnl : jrnl_names;
  simple_jrnl_next : jrnl_names;
  simple_src : gname;
  simple_lockmapghs : list gname;
}.

Variable P : SimpleNFS.State -> iProp Σ.
Context `{Ptimeless : !forall σ, Timeless (P σ)}.

Definition LogSz : nat := 513.
Definition InodeSz : nat := 128.
Definition NumInodes : nat := 4096 / InodeSz.

Definition covered_inodes : gset u64 :=
  rangeSet 2 (NumInodes-2).

Definition no_overflows (src : SimpleNFS.State) : iProp Σ :=
  ([∗ map] _↦istate ∈ src, ⌜(length istate < 2^64)%Z⌝)%I.

Global Instance no_overflows_Persistent src : Persistent (no_overflows src).
Proof. refine _. Qed.

Definition is_source γ : iProp Σ :=
  ∃ (src: SimpleNFS.State),
    (* If we were doing a refinement proof, the top-level source_state would
     * own 1/2 of this [map_ctx] *)
    "Hsrcheap" ∷ map_ctx γ 1%Qp src ∗
    "%Hdom" ∷ ⌜dom src = covered_inodes⌝ ∗
    "#Hnooverflow" ∷ no_overflows src ∗
    "HP" ∷ P src.

Definition encodes_inode (len: u64) (blk: u64) data : Prop :=
  has_encoding data (EncUInt64 len :: EncUInt64 blk :: nil).

Definition inum2addr (inum : u64) := Build_addr LogSz (uint.nat inum * InodeSz * 8).
Definition blk2addr blk := Build_addr blk 0.

Definition is_inode_enc (inum: u64) (len: u64) (blk: u64) (pointsto: addr -> object -> iProp Σ) : iProp Σ :=
  ∃ (ibuf : defs.inode_buf),
    "%Hinode_encodes" ∷ ⌜ encodes_inode len blk (vec_to_list ibuf) ⌝ ∗
    "Hinode_enc_pointsto" ∷ pointsto (inum2addr inum) (existT _ (defs.bufInode ibuf)).

Definition is_inode_data (len : u64) (blk: u64) (contents: list u8) (pointsto: addr -> object -> iProp Σ) : iProp Σ :=
  ∃ (bbuf : Block),
    "%Hdiskdata" ∷ ⌜ firstn (length contents) (vec_to_list bbuf) = contents ⌝ ∗
    "%Hdisklen" ∷ ⌜ uint.Z len = length contents ⌝ ∗
    "Hdiskblk" ∷ pointsto (blk2addr blk) (existT _ (defs.bufBlock bbuf)).

Definition is_inode (inum: u64) (state: list u8) (pointsto: addr -> object -> iProp Σ) : iProp Σ :=
  ∃ (blk: u64),
    "Hinode_enc" ∷ is_inode_enc inum (length state) blk pointsto ∗
    "Hinode_data" ∷ is_inode_data (length state) blk state pointsto.

Definition is_inode_mem (l: loc) (inum: u64) (len: u64) (blk: u64) : iProp Σ :=
  "Hinum" ∷ l ↦[Inode :: "Inum"] #inum ∗
  "Hisize" ∷ l ↦[Inode :: "Size"] #len ∗
  "Hidata" ∷ l ↦[Inode :: "Data"] #blk.

Definition Njrnl := nroot .@ "jrnl".

Definition is_inode_stable γsrc γtxn (inum: u64) : iProp Σ :=
  ∃ (state: list u8),
    "Hinode_state" ∷ inum [[γsrc]]↦ state ∗
    "Hinode_disk" ∷ is_inode inum state (durable_pointsto_own γtxn).

Definition N := nroot .@ "simplenfs".

Definition is_fh (s : Slice.t) (fh : u64) : iProp Σ :=
  ∃ vs,
    "#Hfh_slice" ∷ readonly (own_slice_small s u8T (DfracOwn 1) vs) ∗
    "%Hfh_enc" ∷ ⌜ has_encoding vs (EncUInt64 fh :: nil) ⌝.

Definition is_fs γ (nfs: loc) dinit : iProp Σ :=
  ∃ (txn lm : loc),
    "#Hfs_txn" ∷ readonly (nfs ↦[Nfs :: "t"] #txn) ∗
    "#Hfs_lm" ∷ readonly (nfs ↦[Nfs :: "l"] #lm) ∗
    "#Histxn" ∷ is_txn txn γ.(simple_jrnl).(jrnl_txn_names) dinit ∗
    "#Hislm" ∷ is_lockMap lm γ.(simple_lockmapghs) covered_inodes
                                (is_inode_stable γ.(simple_src) γ.(simple_jrnl))
                                (λ a, C -∗ |={⊤}=> is_inode_stable γ.(simple_src) γ.(simple_jrnl_next) a) ∗
    "#Hsrc" ∷ inv N (is_source γ.(simple_src)) ∗
    "#Htxnsys" ∷ is_txn_system Njrnl γ.(simple_jrnl) ∗
    "#Htxncrash" ∷ txn_cinv Njrnl γ.(simple_jrnl) γ.(simple_jrnl_next).

Global Instance is_fs_persistent γ nfs dinit : Persistent (is_fs γ nfs dinit).
Proof. apply _. Qed.

End heap.
