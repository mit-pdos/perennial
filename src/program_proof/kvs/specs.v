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

Definition is_kvs (kvsl: loc) (s :gmap u64 Block) (sz : nat): iProp Σ :=
  ( ∃ (l : loc) (keys: list u64) γ,
      kvsl↦[KVS.S :: "txn"] #l ∗
      kvsl ↦[KVS.S :: "sz"] #(U64 (Z.of_nat sz)) ∗
      is_txn l γ ∗
      ⌜keys = init_keys [] sz⌝ ∗
      [∗ list] k ∈ keys, (∃ v : Block, ⌜s !! k = Some v⌝ ∗ k k↦ v))%I.

Definition is_block (s:Slice.t) (b:Block) :=
  is_slice_small s byteT 1 (Block_to_vals b).

Definition is_kvpair (l: loc) (key : u64) (b: Block) : iProp Σ :=
      ∃ bs, (l↦[KVPair.S :: "Key"] #key ∗
      l ↦[KVPair.S :: "Val"] (slice_val bs) ∗
      is_block bs b)%I.

Theorem wpc_MkKVS d (sz: nat) k E1 E2:
  {{{ True }}}
    MkKVS #d #(U64(Z.of_nat sz)) @ NotStuck; k; E1; E2
  {{{ kvsl, RET #kvsl; is_kvs kvsl (kvs_init_s sz) sz}}}
  {{{ True }}}.
Proof.
Admitted.

Theorem wpc_KVS__Get kvsl s sz key v stk E:
  {{{ is_kvs kvsl s sz ∗ ⌜s !! key = Some v⌝ }}}
    KVS__Get #kvsl #key @ stk; E (* Crashes don't matter to state here *)
  {{{ (pairl: loc), RET #pairl; (is_kvs kvsl s sz ∗ is_kvpair pairl key v)}}}.
Proof.
Admitted.

(*TODO put actually modifies *)
(*Would it just be easier to not deal with kvpairs?*)
Theorem wpc_KVS__MultiPut kvsl s kvpairsl stk k E1 E2:
  {{{ is_kvs kvsl s }}}
    KVS__MultiPut #kvsl #kvpairsl @ stk; k; E1; E2
  {{{ (ok: bool), RET #ok; (is_kvs kvsl s)}}}
  {{{ True }}}.
Proof.
Admitted.
End heap.
