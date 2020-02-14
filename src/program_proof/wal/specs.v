From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude wal.abstraction.

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
  kv ← suchThat (gen:=fun _ _ => None) (fun s '(k, v) => s.(log_state.txn_disk) !! k = Some v ∧ int.val k >= int.val s.(log_state.durable_to));
  let '(pos, d) := kv in
  modify (set log_state.txn_disk (λ _, {[ pos := d ]}) ∘
          set log_state.durable_to (λ _, pos) ∘
          set log_state.installed_to (λ _, pos));;
  ret tt.

Definition latest_disk (s:log_state.t): u64*disk :=
  map_fold
    (fun k d '(k', d') =>
       if decide (int.val k' < int.val k)
       then (k, d) else (k', d'))
    (U64 0, ∅) s.(log_state.txn_disk).

Definition get_txn_disk (pos:u64) : transition log_state.t disk :=
  reads ((.!! pos) ∘ log_state.txn_disk) ≫= unwrap.

Definition update_installed: transition log_state.t u64 :=
  new_installed ← suchThat (gen:=fun _ _ => None)
                (fun s pos => int.val s.(log_state.installed_to) <=
                            int.val pos <=
                            int.val s.(log_state.durable_to));
  modify (set log_state.installed_to (λ _, new_installed));;
  ret new_installed.

Definition log_read_cache (a:u64): transition log_state.t (option Block) :=
  ok ← suchThat (fun _ (b:bool) => True);
  if (ok:bool)
  then d ← reads (snd ∘ latest_disk);
       match d !! int.val a with
       | None => undefined
       | Some b => ret (Some b)
       end
  else (* this is really non-deterministic; it would be simpler if upfront we
          moved installed_to forward to a valid transaction and then made most
          of the remaining decisions deterministically. *)
    new_installed ← update_installed;
    install_d ← get_txn_disk new_installed;
    suchThat (gen:=fun _ _ => None)
             (fun s (_:unit) =>
                forall pos d, int.val s.(log_state.installed_to) < int.val pos ->
                         s.(log_state.txn_disk) !! pos = Some d ->
                         d !! int.val a = install_d !! int.val a);;
    ret None.

Definition log_read_installed (a:u64): transition log_state.t Block :=
  installed_to ← update_installed;
  install_d ← get_txn_disk installed_to;
  unwrap (install_d !! int.val a).

Definition log_read (a:u64): transition log_state.t Block :=
  d ← reads (snd ∘ latest_disk);
  match d !! int.val a with
  | None => undefined
  | Some b => ret b
  end.

Definition apply_upds (upds: list update.t) (d: disk): disk :=
  fold_right (fun '(update.mk a b) => <[int.val a := b]>) d upds.

Definition log_mem_append (upds: list update.t): transition log_state.t u64 :=
  txn_d ← reads latest_disk;
  let '(txn, d) := txn_d in
  (* Note that if the new position can be an earlier txn if every update is
  absorbed (as a special case, an empty list of updates is always fully
  absorbed). In that case what was previously a possible crash point is now
  gone. This is actually the case when it happens because that transaction was
  in memory. *)
  new_txn ← suchThat (gen:=fun _ _ => None) (fun _ new_txn => int.val new_txn >= int.val txn);
  modify (set log_state.txn_disk (<[new_txn:=apply_upds upds d]>));;
  ret new_txn.

Definition log_flush (pos: u64): transition log_state.t unit :=
  (* flush should be undefined when the position is invalid *)
  _ ← reads ((.!! pos) ∘ log_state.txn_disk) ≫= unwrap;
  modify (set log_state.durable_to (λ _, pos)).

Section heap.
Context `{!heapG Σ}.
Implicit Types (v:val) (z:Z).

Context (N: namespace).
Context (P: log_state.t -> iProp Σ).

(* this will be the entire internal wal invariant - callers will not need to
unfold it *)
Definition is_wal (l: loc): iProp Σ := inv N (l ↦ Free #()).

Definition blocks_to_gmap (bs:list Block): disk.
  (* this is just annoying to write down *)
Admitted.

Theorem wp_new_wal bs :
  {{{ P (log_state.mk {[U64 0 := blocks_to_gmap bs]} (U64 0) (U64 0)) ∗ 0 d↦∗ bs }}}
    MkLog #()
  {{{ l, RET #l; is_wal l }}}.
Proof.
Admitted.

Theorem wp_Walog__MemAppend (Q: u64 -> iProp Σ) l bufs bs :
  {{{ is_wal l ∗
       updates_slice bufs bs ∗
       (∀ σ σ' pos,
         ⌜relation.denote (log_mem_append bs) σ σ' pos⌝ ∗
          P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q pos)
   }}}
    Walog__MemAppend #l (slice_val bufs)
  {{{ pos, RET #pos; Q pos }}}.
Proof.
Admitted.

Theorem wp_Walog__ReadMem (Q: option Block -> iProp Σ) l a :
  {{{ is_wal l ∗
       (∀ σ σ' mb,
         ⌜relation.denote (log_read_cache a) σ σ' mb⌝ ∗
          P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q mb)
   }}}
    Walog__ReadMem #l #a
  {{{ (ok:bool) bl, RET (#ok, slice_val bl); if ok
                                             then ∃ b, is_block bl b ∗ Q (Some b)
                                             else Q None}}}.
Proof.
Admitted.

Theorem wp_Walog__ReadInstalled (Q: Block -> iProp Σ) l a :
  {{{ is_wal l ∗
       (∀ σ σ' b,
         ⌜relation.denote (log_read_installed a) σ σ' b⌝ ∗
          P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q b)
   }}}
    Walog__ReadInstalled #l #a
  {{{ (ok:bool) bl, RET (#ok, slice_val bl); ∃ b, is_block bl b ∗ Q b}}}.
Proof.
Admitted.

Theorem wp_Walog__Flush (Q: iProp Σ) l pos :
  {{{ is_wal l ∗
       (∀ σ σ' b,
           (* TODO: does this correctly account for undefined behavior? it seems
           like it's wrong since this proof gets to assume false when there's
           undefined behavior, whereas we'd somehow need the caller to establish
           preconditions at all intermediate points *)
         (⌜relation.denote (log_flush pos) σ σ' b⌝ ∗ P σ)
         ={⊤ ∖↑ N}=∗ P σ' ∗ Q)
   }}}
    Walog__Flush #l #pos
  {{{ RET #(); Q}}}.
Proof.
Admitted.

End heap.
