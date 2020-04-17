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

Definition is_kvs (kvsl: loc) (s :gmap u64 disk.Block) : iProp Σ :=
  ( ∃ (l : loc) (sz: nat) (keys: list u64) γ,
      kvsl↦[KVS.S :: "txn"] #l ∗
      kvsl ↦[KVS.S :: "sz"] #(U64 (Z.of_nat sz)) ∗
      is_txn l γ ∗
      ⌜keys = init_keys [] sz⌝ ∗
      [∗ list] k ∈ keys, (∃ v : disk.Block, ⌜s !! k = Some v⌝ ∗ k k↦ v))%I.

Definition is_kvpair (l: loc) : iProp Σ :=
  (∃ (key : u64) (val: Slice.t),
      l↦[KVS.S :: "Key"] #key ∗
      l ↦[KVS.S :: "Val"] (slice_val val))%I.

(*Theorem wpc_MkKVS (d: disk.Disk) (sz: u64)
    MkKVS #d #sz @ NotStuck; k; E1; E2
  {{{ l (ok: bool), RET (#l, #ok); ⌜ int.nat sz > 0 → ok = true ⌝ ∗
      if ok then ptsto_log l [] ∗ ∃ (ml: loc), l ↦[Log.S :: "m"] #ml ∗ is_free_lock ml
      else 0 d↦∗ vs }}}
  {{{ 0 d↦∗ vs ∨ (∃ b b' vs', ⌜ vs = b :: vs' ⌝ ∗ 0 d↦∗ (b' :: vs') ) }}}.
Proof.
Qed.*)

(*Do I need stuck / E? What are those for?*)
Theorem wpc_KVS__Get kvsl s key stk E:
  {{{ is_kvs kvsl s }}}
    KVS__Get #kvsl key @ stk; E
  {{{ (pairl: loc), RET #pairl; (is_kvs kvsl s ∗ is_kvpair pairl)}}}.
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
