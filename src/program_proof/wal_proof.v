From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

(* defining the abstraction of the log, including internal abstractions *)

Module update.
  Record t :=
    { addr: u64;
      b: Block; }.
End update.

Definition disk := gmap u64 Block.

Module log_state.
  Record t :=
    mk { txn_disk: gmap u64 disk; }.
  Global Instance _eta: Settable _ := settable! mk <txn_disk>.
End log_state.

Instance gen_gmap_entry {Σ K} `{Countable K} {V} (m: gmap K V) :
  GenPred (K*V) Σ (fun _ '(k, v) => m !! k = Some v).
Proof.
  intros _ _.
  destruct (map_to_list m) as [|[k v] l] eqn:Hm; [ exact None | apply Some ].
  exists (k, v).
  apply elem_of_map_to_list.
  rewrite Hm.
  constructor.
Qed.

Existing Instance r_mbind.

Definition log_crash: transition log_state.t unit :=
  disks ← reads log_state.txn_disk;
  kv ← suchThat (fun _ '(k, v) => disks !! k = Some v);
  let '(pos, d) := kv in
  modify (set log_state.txn_disk (λ _, {[ pos := d ]}));;
  ret tt.

Instance Zgt_decide z1 z2 : Decision (z1 > z2).
Proof.
  hnf.
  destruct (decide (z2 < z1)); [ left | right ]; abstract lia.
Defined.

Definition latest_disk (s:log_state.t): u64*disk :=
  map_fold
    (fun k d '(k', d') =>
       if decide (int.val k > int.val k')
       then (k, d) else (k', d'))
    (U64 0, ∅) s.(log_state.txn_disk).

Definition log_read (a:u64): transition log_state.t Block :=
  d ← reads (snd ∘ latest_disk);
  match d !! a with
  | None => undefined
  | Some b => ret b
  end.

Definition apply_upds (upds: list (u64*Block)) (d: disk): disk :=
  fold_right (fun '(a, b) => <[a := b]>) d upds.

Definition log_mem_append (upds: list (u64*Block)): transition log_state.t unit :=
  txn_d ← reads latest_disk;
  let '(txn, d) := txn_d in
  new_txn ← suchThat (gen:=fun _ _ => None) (fun _ new_txn => int.val new_txn > int.val txn);
  modify (set log_state.txn_disk (<[new_txn:=apply_upds upds d]>)).

Definition remove_before (pos: u64) {V} (m: gmap u64 V) : gmap u64 V :=
  filter (fun '(x, _) => int.val x < int.val pos) m.

Definition log_flush (pos: u64): transition log_state.t unit :=
  txns ← reads log_state.txn_disk;
  _ ← unwrap (txns !! pos);
  modify (set log_state.txn_disk (remove_before pos)).

Section heap.
Context `{!heapG Σ}.
Existing Instance diskG0.
Implicit Types (Φ : val → iProp Σ).
Implicit Types (v:val) (z:Z).
Implicit Types (stk:stuckness) (E:coPset).

End heap.
