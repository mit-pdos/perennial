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

Definition apply_upds (upds: list update.t) (d: disk): disk :=
  fold_right (fun '(update.mk a b) => <[int.val a := b]>) d upds.

Definition get_updates (s:log_state.t): list update.t :=
  s.(log_state.updates).

Definition disk_at_pos (pos: u64) (s:log_state.t): disk :=
  apply_upds (firstn (Z.to_nat (int.val pos)) s.(log_state.updates)) s.(log_state.disk).

Definition latest_disk (s:log_state.t): disk :=
  disk_at_pos (length s.(log_state.updates)) s.

Definition installed_disk (s:log_state.t): disk :=
  disk_at_pos s.(log_state.installed_to) s.

Definition logged_upds (s:log_state.t): list update.t :=
  firstn (Z.to_nat (int.val s.(log_state.durable_to))) s.(log_state.updates).

Definition inmem_upds (s:log_state.t): list update.t :=
  skipn (Z.to_nat (int.val s.(log_state.durable_to))) s.(log_state.updates).

Definition valid_log_state (s : log_state.t) :=
  int.val s.(log_state.installed_to) ≤ int.val s.(log_state.durable_to) ∧
  int.val (log_state.last_pos s) >= int.val s.(log_state.durable_to).

Lemma latest_disk_at_pos: forall σ,
    latest_disk σ = disk_at_pos (length σ.(log_state.updates)) σ.
Proof.
  intros.
  unfold latest_disk; eauto.
Qed.

Definition log_crash: transition log_state.t unit :=
  kv ← suchThat (gen:=fun _ _ => None) (fun s '(pos, d, upds) => s.(log_state.disk) = d ∧ int.val pos >= int.val s.(log_state.durable_to) ∧ upds = firstn (Z.to_nat (int.val pos)) s.(log_state.updates));
  let '(pos, d, upds) := kv in
  modify (set log_state.disk (λ _, d ) ∘
          set log_state.updates (λ _, upds) ∘
          set log_state.durable_to (λ _, pos) ∘
          set log_state.installed_to (λ _, pos));;
  ret tt.

Definition update_installed: transition log_state.t u64 :=
  new_installed ← suchThat (gen:=fun _ _ => None)
                (fun s pos => int.val s.(log_state.installed_to) <=
                            int.val pos <=
                            int.val s.(log_state.durable_to));
  modify (set log_state.installed_to (λ _, new_installed));;
  ret new_installed.

Definition update_durable: transition log_state.t u64 :=
  new_durable ← suchThat (gen:=fun _ _ => None)
                (fun s pos => int.val s.(log_state.durable_to) <=
                            int.val pos <= 
                            int.val (length s.(log_state.updates)));
  modify (set log_state.durable_to (λ _, new_durable));;
  ret new_durable.

Definition log_read_cache (a:u64): transition log_state.t (option Block) :=
  update_installed;;
  update_durable;;
  d ← reads latest_disk;
  match d !! int.val a with
  | None => undefined
  | Some b => ret (Some b)
  end.

Definition log_read_installed (a:u64): transition log_state.t Block :=
  update_installed;;
  update_durable;;
  d ← reads installed_disk;
  unwrap (d !! int.val a).

Fixpoint absorb_map upds m: gmap u64 Block :=
  match upds with
  | [] => m
  | upd :: upd0 => absorb_map upd0 (<[update.addr upd := update.b upd]> m)
  end.                   

(* XXX fit in log *)
Definition log_mem_append (upds: list update.t): transition log_state.t u64 :=
  update_durable;;
  logged ← reads logged_upds;
  inmem  ← reads inmem_upds;
  (* new are the updates after absorbing of inmem in upds; that is,
  replacing upds in inmem with upds if to the same address.  *)
  new ← suchThat (gen:=fun _ _ => None)
                 (fun s new => absorb_map new ∅ = absorb_map (inmem++upds) ∅);
  modify (set log_state.updates (λ _, logged++new));;
  ret (U64 (length (logged++new))).

Definition log_flush (pos: u64): transition log_state.t unit :=
  (* flush should be undefined when the position is invalid *)
  modify (set log_state.durable_to (λ _, pos)).

(*
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
  {{{ P (log_state.mk {[U64 0 := blocks_to_gmap bs]} (U64 0) (U64 0)) ∗ 0 d↦∗ bs }}}
    MkLog #()
  {{{ l, RET #l; is_wal l }}}.
Proof.
Admitted.

Theorem wp_Walog__MemAppend (Q: u64 -> iProp Σ) l bufs bs :
  {{{ is_wal l ∗
       updates_slice bufs bs ∗
       (∀ σ σ' pos,
         ⌜valid_log_state σ⌝ -∗
         ⌜relation.denote (log_mem_append bs) σ σ' pos⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q pos))
   }}}
    Walog__MemAppend #l (slice_val bufs)
  {{{ pos, RET (#pos, #true); Q pos }}}.
Proof.
Admitted.

Theorem wp_Walog__ReadMem (Q: option Block -> iProp Σ) l a :
  {{{ is_wal l ∗
       (∀ σ σ' mb,
         ⌜valid_log_state σ⌝ -∗
         ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q mb))
   }}}
    Walog__ReadMem #l #a
  {{{ (ok:bool) bl, RET (slice_val bl, #ok); if ok
                                             then ∃ b, is_block bl b ∗ Q (Some b)
                                             else Q None}}}.
Proof.
Admitted.

Theorem wp_Walog__ReadInstalled (Q: Block -> iProp Σ) l a :
  {{{ is_wal l ∗
       (∀ σ σ' b,
         ⌜valid_log_state σ⌝ -∗
         ⌜relation.denote (log_read_installed a) σ σ' b⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q b))
   }}}
    Walog__ReadInstalled #l #a
  {{{ (ok:bool) bl, RET (slice_val bl, #ok); ∃ b, is_block bl b ∗ Q b}}}.
Proof.
Admitted.

Theorem wp_Walog__Flush (Q: iProp Σ) l pos :
  {{{ is_wal l ∗
       (∀ σ σ' b,
         ⌜valid_log_state σ⌝ -∗
         ⌜relation.denote (log_flush pos) σ σ' b⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q))
   }}}
    Walog__Flush #l #pos
  {{{ RET #(); Q}}}.
Proof.
Admitted.

End heap.
*)

(*
Lemma latest_disk_durable s : valid_log_state s ->
  int.val s.(log_state.durable_to) ≤ int.val (fst (latest_disk s)).
Proof.
  destruct s.
  rewrite /valid_log_state /latest_disk /=.
  intros. destruct H.
Admitted.

Lemma latest_disk_pos s : valid_log_state s ->
  s.(log_state.txn_disk) !! (fst (latest_disk s)) = Some (snd (latest_disk s)).
Proof.
  unfold latest_disk.
  destruct s; simpl.
  intros.
  assert (∃ d, txn_disk !! durable_to = Some d).
  { destruct H; eauto. }
  clear H.
  revert H0.
  match goal with
  | |- context[map_fold ?f ?init ?m] =>
    eapply (map_fold_ind (fun acc m => (∃ d, m !! durable_to = Some d) -> m !! acc.1 = Some acc.2) f)
  end.
  { intros [d Heq]; simpl.
    rewrite lookup_empty in Heq; congruence. }
  intros x d m [k' d']; simpl; intros.
  destruct (decide (int.val k' < int.val x)); simpl.
  - rewrite lookup_insert //.
  - destruct (decide (x = k')) as [-> | ?].
    + rewrite lookup_insert //.
Admitted.

Lemma latest_disk_append s npos nd : valid_log_state s ->
  int.val npos >= int.val (fst (latest_disk s)) ->
  latest_disk (set log_state.txn_disk <[npos:=nd]> s) = (npos, nd).
Proof.
Admitted.

Definition get_txn_disk (pos:u64) : transition log_state.t disk :=
  reads ((.!! pos) ∘ log_state.txn_disk) ≫= unwrap.
 *)

(*
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
                forall pos d, int.val s.(log_state.installed_to) ≤ int.val pos ->
                         s.(log_state.txn_disk) !! pos = Some d ->
                         d !! int.val a = install_d !! int.val a);;
    ret None.
*)

(*
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
*)          

