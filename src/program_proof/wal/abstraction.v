From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.program_proof Require Import proof_prelude.

Module update.
  Record t :=
    mk { addr: u64;
         b: Block; }.
  Global Instance _eta: Settable _ := settable! mk <addr; b>.
End update.

Definition disk := gmap Z Block.

Definition txn_upds (txns: list (u64 * list update.t)) : list update.t :=
  concat (snd <$> txns).

Module log_state.
  Record t :=
    mk {
        d: disk;
        txns: list (u64 * list update.t);
        (* installed_lb promises what will be read after a cache miss *)
        installed_to: nat;
        (* durable_lb promises what will be on-disk after a crash *)
        durable_to: nat;
      }.
  Global Instance _eta: Settable _ := settable! mk <d; txns; installed_to; durable_to>.

  Definition updates σ : list update.t := txn_upds σ.(txns).

  Definition valid_addrs (updates: list update.t) (d: disk) :=
    forall i u, updates !! i = Some u ->
           ∃ (b: Block), d !! (int.val u.(update.addr)) = Some b.

  Definition valid_log_state (s : t) :=
    valid_addrs (updates s) s.(d) ∧
    (* monotonicity of txnids  *)
    (forall (pos1 pos2: u64) (txn_id1 txn_id2: nat),
        txn_id1 < txn_id2 ->
        fst <$> s.(txns) !! txn_id1 = Some pos1 ->
        fst <$> s.(txns) !! txn_id2 = Some pos2 ->
        (* can get the same handle for two transactions due to absorption or
        empty transactions *)
        int.val pos1 ≤ int.val pos2) ∧
    s.(installed_to) ≤ s.(durable_to) ≤ length s.(txns).

End log_state.

Implicit Types (txn_id:nat) (pos: u64).

Existing Instance r_mbind.

Definition update_durable: transition log_state.t nat :=
  new_durable ← suchThat (gen:=fun _ _ => None)
              (fun s new_durable =>
                 (s.(log_state.durable_to) ≤ new_durable ≤ length s.(log_state.txns))%nat);
  modify (set log_state.durable_to (λ _, new_durable));;
  ret new_durable.

Definition update_installed: transition log_state.t nat :=
  new_installed ← suchThat (gen:=fun _ _ => None)
              (fun s new_installed =>
                 (s.(log_state.installed_to) ≤ new_installed ≤ s.(log_state.durable_to))%nat);
  modify (set log_state.installed_to (λ _, new_installed));;
  ret new_installed.

Definition crash : transition log_state.t unit :=
  crash_txn ← suchThat (gen:=fun _ _ => None)
            (fun s (crash_txn: nat) =>
               s.(log_state.durable_to) <= crash_txn);
  modify (set log_state.txns (fun txns => take crash_txn txns));;
  modify (set log_state.durable_to (fun _ => crash_txn));;
  ret tt.

Definition suchThatMax {Σ} (pred: Σ -> nat -> Prop) : transition Σ nat :=
  (* TODO: implement *)
  undefined.

Definition getTxnId (pos: u64) : transition log_state.t nat :=
  suchThatMax (fun s (txn_id: nat) => fst <$> s.(log_state.txns) !! txn_id = Some pos).

Definition flush (pos:u64) : transition log_state.t unit :=
  txn_id ← getTxnId pos;
  new_durable ← suchThat (gen:=fun _ _ => None)
              (fun s (new_durable: nat) =>
                 (Nat.max s.(log_state.durable_to) txn_id ≤ new_durable ≤ length s.(log_state.txns))%nat);
  modify (set log_state.durable_to (λ _, (new_durable)));;
  ret tt.

Definition allocPos : transition log_state.t u64 :=
  (* TODO: get the highest pos used *)
  highest ← ret (U64 0);
  suchThat (gen:=fun _ _ => None) (fun _ (pos': u64) => int.val pos' >= int.val highest).

Definition mem_append (txn: list update.t) :=
  pos ← allocPos;
  modify (set log_state.txns (fun txns => txns ++ [(pos,txn)])).

Definition apply_upds (upds: list update.t) (d: disk): disk :=
  fold_left (fun d '(update.mk a b) => <[int.val a := b]> d) upds d.

Definition disk_at_txn_id (txn_id: nat) (s:log_state.t): disk :=
  apply_upds (txn_upds $ take txn_id (log_state.txns s)) s.(log_state.d).

Definition updates_for_addr (a: u64) (l : list update.t) : list Block :=
  fmap update.b
  (filter (fun u => u.(update.addr) = a) l).

Definition updates_since (txn_id: nat) (a: u64) (s : log_state.t) : list Block :=
  updates_for_addr a (txn_upds $ drop txn_id (log_state.txns s)).

Fixpoint latest_update (base: Block) (upds: list Block) : Block :=
  match upds with
  | u :: upds' =>
    latest_update u upds'
  | nil => base
  end.

Definition last_disk (s:log_state.t): disk :=
  disk_at_txn_id (length (log_state.txns s)) s.

Definition no_updates_since σ a txn_id :=
  Forall (fun u => u.(update.addr) ≠ a)
         (txn_upds $ drop txn_id (log_state.txns σ)).

Definition log_read_cache (a:u64): transition log_state.t (option Block) :=
  ok ← suchThat (fun _ (b:bool) => True);
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
    suchThat (gen:=fun _ _ => None)
             (fun s (_:unit) =>
                no_updates_since s a s.(log_state.installed_to));;
    ret None.

Definition installed_disk (s:log_state.t): disk :=
  disk_at_txn_id s.(log_state.installed_to) s.

Definition log_read_installed (a:u64): transition log_state.t Block :=
  update_durable;;
  update_installed;;
  d ← reads installed_disk;
  unwrap (d !! int.val a).

Section heap.
Context `{!heapG Σ}.
Definition update_val (up:u64*Slice.t): val :=
  (#(fst up), (slice_val (snd up), #()))%V.

Theorem update_val_t u : val_ty (update_val u) (struct.t Update.S).
Proof.
  repeat constructor.
  destruct u; rewrite /blockT; val_ty.
Qed.

(* TODO: this should probably also have a fraction *)
Definition is_block (s:Slice.t) (b:Block) :=
  is_slice_small s byteT 1 (Block_to_vals b).

Definition updates_slice (bk_s: Slice.t) (bs: list update.t): iProp Σ :=
  ∃ bks, is_slice bk_s (struct.t Update.S) 1 (update_val <$> bks) ∗
   [∗ list] _ ↦ b_upd;upd ∈ bks;bs , let '(update.mk a b) := upd in
                                     is_block (snd b_upd) b ∗
                                     ⌜fst b_upd = a⌝.

Lemma updates_slice_len bk_s bs :
  updates_slice bk_s bs -∗ ⌜int.val bk_s.(Slice.sz) = length bs⌝.
Proof.
  iIntros "Hupds".
  iDestruct "Hupds" as (bks) "[Hbs Hbks]".
  iDestruct (is_slice_sz with "Hbs") as %Hbs_sz.
  iDestruct (big_sepL2_length with "Hbks") as %Hbks_len.
  rewrite fmap_length in Hbs_sz.
  iPureIntro.
  rewrite -Hbks_len.
  rewrite Hbs_sz.
  destruct bk_s; simpl.
  word.
Qed.

End heap.

Hint Resolve update_val_t : val_ty.
