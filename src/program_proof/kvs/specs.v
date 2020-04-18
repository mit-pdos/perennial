From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import kvs.
From Perennial.program_proof Require Import txn.specs buftxn.specs.
From Perennial.goose_lang.lib Require Import encoding.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import marshal_proof.

Module kvpair.
  Record t :=
    mk { key: u64;
         val: Block; }.
  Global Instance _eta: Settable _ := settable! mk <key; val>.
End kvpair.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!crashG Σ}.
Context `{!inG Σ (authR (optionUR (exclR boolO)))}.
Context `{!gen_heapPreG u64 disk.Block Σ}.
Context `{!gen_heapG u64 disk.Block Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Notation "l k↦ v" := (mapsto (L:=u64) (V:=disk.Block) l 1 v%V)
                            (at level 20, format "l  k↦ v") : bi_scope.
Notation "l k↦{ q } v" := (mapsto (L:=u64) (V:=disk.Block) l q v%V)
                            (at level 20, q at level 50, format "l  k↦{ q }  v") : bi_scope.

Fixpoint init_keys (keys: list u64) (sz: nat) : list u64 :=
match sz with
| O => keys
| S n => init_keys ((U64 (Z.of_nat n)) :: keys) n
end.

Fixpoint init_kvs (kvs: gmap u64 Block) (sz: nat) : gmap u64 Block :=
match sz with
| O => kvs
| S n => <[(U64 (Z.of_nat n)) := (inhabitant Block0)]> (init_kvs kvs n)
end.
Definition kvs_init_s sz : gmap u64 Block := init_kvs ∅ sz.

(*XXXway to generalize from wal/abstractions.v?*)
Definition kvpair_val (pair : u64*Slice.t): val :=
  (#(fst pair), (slice_val (snd pair), #()))%V.

(* Links a list of kvpairs to a slice *)
Definition kvpairs_slice (val_s: Slice.t) (pairs: list kvpair.t): iProp Σ :=
  ∃ bks, is_slice val_s (struct.t KVPair.S) 1 (kvpair_val <$> bks) ∗
   [∗ list] _ ↦ b_kvp;kvp ∈ bks;pairs, let '(kvpair.mk a b) := kvp in
                                     is_block (snd b_kvp) b ∗
                                              ⌜fst b_kvp = a⌝.

Definition kvpairs_match (s: gmap u64 Block) (pairs: list kvpair.t): iProp Σ :=
  [∗ list] kvp ∈ pairs, let '(kvpair.mk a b) := kvp in (⌜(s !! a = Some b)⌝)%I.

Definition is_kvs' (s: gmap u64 Block) (sz : nat) :=
  (∃ keys,
    ⌜keys = init_keys [] sz⌝ ∗
    [∗ list] k ∈ keys, (∃ v : Block, ⌜s !! k = Some v⌝ ∗ k k↦ v))%I.

Definition ptsto_kvs (kvsl: loc) (s : gmap u64 Block) (sz : nat): iProp Σ :=
  ( ∃ (l : loc) γ,
      kvsl↦[KVS.S :: "txn"] #l ∗
      kvsl ↦[KVS.S :: "sz"] #(U64 (Z.of_nat sz)) ∗
      is_txn l γ ∗
      is_kvs' s sz)%I.

Definition crashed_kvs s sz kvp_ls : iProp Σ :=
  is_kvs' s sz ∗ kvpairs_match s kvp_ls.

Definition ptsto_kvpair (l: loc) (pair: kvpair.t) : iProp Σ :=
      ∃ bs, (l↦[KVPair.S :: "Key"] #pair.(kvpair.key) ∗
      l ↦[KVPair.S :: "Val"] (slice_val bs) ∗
      is_block bs pair.(kvpair.val))%I.

Theorem wpc_MkKVS d (sz: nat) k E1 E2:
  {{{ True }}}
    MkKVS #d #(U64(Z.of_nat sz)) @ NotStuck; k; E1; E2
  {{{ kvsl, RET #kvsl; ptsto_kvs kvsl (kvs_init_s sz) sz}}}
  {{{ True }}}.
Proof.
Admitted.

Theorem wpc_KVS__Get kvsl s sz key v stk E:
  {{{ ptsto_kvs kvsl s sz ∗ ⌜s !! key = Some v⌝ }}}
    KVS__Get #kvsl #key @ stk; E (* Crashes don't matter to state here *)
  {{{(pairl: loc), RET #pairl;
     ptsto_kvs kvsl s sz ∗ ptsto_kvpair pairl (kvpair.mk key v)
  }}}.
Proof.
Admitted.

Theorem wpc_KVS__MultiPut kvsl s sz kvp_ls_before kvp_slice kvp_ls stk k E1 E2:
  {{{
       ptsto_kvs kvsl s sz
                 ∗ kvpairs_match s kvp_ls_before
                 ∗ kvpairs_slice kvp_slice kvp_ls
  }}}
    KVS__MultiPut #kvsl (slice_val kvp_slice) @ stk; k; E1; E2
  {{{ (ok: bool), RET #ok;
      ptsto_kvs kvsl s sz ∗ kvpairs_match s kvp_ls
  }}}
  {{{ crashed_kvs s sz kvp_ls ∨ crashed_kvs s sz kvp_ls_before }}}.
Proof.
Admitted.
End heap.
