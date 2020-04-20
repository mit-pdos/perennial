From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude wal.abstraction wal.circ_proof disk_lib.

Implicit Types (txn_id:nat) (pos: u64).

Existing Instance r_mbind.
Existing Instance fallback_genPred.

Definition update_durable: transition log_state.t nat :=
  new_durable ← suchThat
              (λ s new_durable,
               (s.(log_state.durable_lb) ≤
                new_durable ≤
                length s.(log_state.txns))%nat);
modify (set log_state.durable_lb (λ _, new_durable));;
ret new_durable.

Definition update_installed: transition log_state.t nat :=
  new_installed ← suchThat
              (λ s new_installed,
                 (s.(log_state.installed_lb) ≤
                  new_installed ≤
                  s.(log_state.durable_lb))%nat);
  modify (set log_state.installed_lb (λ _, new_installed));;
  ret new_installed.

Definition log_crash : transition log_state.t unit :=
  crash_txn ← suchThat
            (λ s (crash_txn: nat),
               s.(log_state.durable_lb) ≤ crash_txn);
  modify (set log_state.txns (fun txns => take crash_txn txns));;
  modify (set log_state.durable_lb (fun _ => crash_txn));;
  ret tt.

Definition suchThatMax {Σ} (pred: Σ -> nat -> Prop) : transition Σ nat :=
  suchThat (λ s x, pred s x ∧ ∀ y, pred s y -> y ≤ x).

Definition is_txn (s: log_state.t) (txn_id: nat) (pos: u64): Prop :=
  fst <$> s.(log_state.txns) !! txn_id = Some pos.

Definition getTxnId (pos: u64) : transition log_state.t nat :=
  suchThatMax (fun s (txn_id: nat) => is_txn s txn_id pos).

Definition log_flush (pos:u64) : transition log_state.t unit :=
  txn_id ← getTxnId pos;
  new_durable ← suchThat
              (λ s (new_durable: nat),
                 (Nat.max s.(log_state.durable_lb) txn_id ≤ new_durable ≤ length s.(log_state.txns))%nat);
  modify (set log_state.durable_lb (λ _, (new_durable)));;
  ret tt.

Definition allocPos : transition log_state.t u64 :=
  suchThat (λ s (pos': u64),
            (∃ txn_id', is_txn s txn_id' pos') ∧
            (∀ (pos: u64) txn_id,
                is_txn s txn_id pos ->
                int.val pos' >= int.val pos)).

Definition log_mem_append (txn: list update.t): transition log_state.t u64 :=
  pos ← allocPos;
  modify (set log_state.txns (fun txns => txns ++ [(pos,txn)]));;
  ret pos.

Definition apply_upds (upds: list update.t) (d: disk): disk :=
  fold_left (fun d '(update.mk a b) => <[int.val a := b]> d) upds d.

Definition disk_at_txn_id (txn_id: nat) (s:log_state.t): disk :=
  apply_upds (txn_upds (take txn_id (log_state.txns s))) s.(log_state.d).

Definition updates_for_addr (a: u64) (l : list update.t) : list Block :=
  update.b <$> filter (λ u, u.(update.addr) = a) l.

Definition updates_since (txn_id: nat) (a: u64) (s : log_state.t) : list Block :=
  updates_for_addr a (txn_upds (drop txn_id (log_state.txns s))).

Fixpoint latest_update (base: Block) (upds: list Block) : Block :=
  match upds with
  | u :: upds' =>
    latest_update u upds'
  | nil => base
  end.

Definition last_disk (s:log_state.t): disk :=
  disk_at_txn_id (length (log_state.txns s)) s.

Definition no_updates_since σ a txn_id :=
  Forall (λ u, u.(update.addr) ≠ a)
         (txn_upds (drop txn_id (log_state.txns σ))).

Definition log_read_cache (a:u64): transition log_state.t (option Block) :=
  ok ← any bool;
  if (ok:bool)
  then d ← reads last_disk;
       match d !! int.val a with
       | None => undefined
       | Some b => ret (Some b)
       end
  else
    (* on miss, read makes [installed_to] precise enough so the caller can
    use [log_read_installed] and together get the current value at [a] *)
    update_durable;;
    update_installed;;
    suchThat (fun s (_:unit) =>
                no_updates_since s a s.(log_state.installed_lb));;
    ret None.

Definition installed_disk (s:log_state.t): disk :=
  disk_at_txn_id s.(log_state.installed_lb) s.

Definition log_read_installed (a:u64): transition log_state.t Block :=
  update_durable;;
  update_installed;;
  installed_txn_id ← suchThat (fun s txn_id =>
                                 s.(log_state.installed_lb) ≤
                                 txn_id ≤
                                 s.(log_state.durable_lb));
  d ← reads (disk_at_txn_id installed_txn_id);
  unwrap (d !! int.val a).


Section heap.
Context `{!heapG Σ}.
Implicit Types (v:val) (z:Z).

Context (N: namespace).
Context (P: log_state.t -> iProp Σ).

(* this will be the entire internal wal invariant - callers will not need to
unfold it *)
Definition is_wal (l: loc): iProp Σ := inv N (l ↦ #() ∗ ∃ σ, P σ).

Definition blocks_to_gmap (bs:list Block): disk.
  (* this is just annoying to write down *)
Admitted.

Theorem wp_new_wal bs :
  {{{ P (log_state.mk (blocks_to_gmap bs) [(U64 0, [])] 0 0) ∗ 0 d↦∗ bs }}}
    MkLog #()
  {{{ l, RET #l; is_wal l }}}.
Proof.
Admitted.

Theorem wp_Walog__MemAppend (Q: u64 -> iProp Σ) l bufs bs :
  {{{ is_wal l ∗
       updates_slice bufs bs ∗
       (∀ σ σ' pos,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_mem_append bs) σ σ' pos⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q pos))
   }}}
    Walog__MemAppend #l (slice_val bufs)
  {{{ pos (ok : bool), RET (#pos, #ok); if ok then Q pos else emp }}}.
Proof.
  iIntros (Φ) "(Hwal & Hupds & Hfupd) HΦ".
  wp_call.
  wp_apply wp_slice_len.
  wp_pures.
  wp_if_destruct.
  { wp_pures. iApply "HΦ". done. }

  wp_apply wp_ref_to; first val_ty.
  iIntros (txnloc) "Htxnloc".

  wp_apply wp_ref_to; first val_ty.
  iIntros (okloc) "Hokloc".

  (* XXX need a real is_wal *)
Admitted.

Theorem wp_Walog__ReadMem (Q: option Block -> iProp Σ) l a :
  {{{ is_wal l ∗
       (∀ σ σ' mb,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q mb))
   }}}
    Walog__ReadMem #l #a
  {{{ (ok:bool) bl, RET (slice_val bl, #ok); if ok
                                             then ∃ b, is_block bl b ∗ Q (Some b)
                                             else Q None}}}.
Proof.
  iIntros (Φ) "[Hwal Hfupd] HΦ".
  wp_call.

  (* XXX need a real is_wal *)
Admitted.

Theorem wp_Walog__ReadInstalled (Q: Block -> iProp Σ) l a :
  {{{ is_wal l ∗
       (∀ σ σ' b,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_read_installed a) σ σ' b⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q b))
   }}}
    Walog__ReadInstalled #l #a
  {{{ bl, RET slice_val bl; ∃ b, is_block bl b ∗ Q b}}}.
Proof.
  iIntros (Φ) "[Hwal Hfupd] HΦ".
  wp_call.

  (* XXX is this a valid block? *)
Admitted.

Theorem wp_Walog__Flush (Q: iProp Σ) l pos :
  {{{ is_wal l ∗
       (∀ σ σ' b,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_flush pos) σ σ' b⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q))
   }}}
    Walog__Flush #l #pos
  {{{ RET #(); Q}}}.
Proof.
  iIntros (Φ) "[Hwal Hfupd] HΦ".
  wp_call.

  wp_apply util_proof.wp_DPrintf.

  (* XXX need a real is_wal *)
Admitted.

End heap.
