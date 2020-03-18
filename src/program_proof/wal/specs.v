From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude wal.abstraction wal.circular_proof.

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

Definition last_disk (s:log_state.t): disk :=
  disk_at_pos (length s.(log_state.updates)) s.

Definition installed_disk (s:log_state.t): disk :=
  disk_at_pos s.(log_state.installed_to) s.

(* updates that have been logged or installed *)
Definition stable_upds (s:log_state.t): list update.t :=
  firstn (Z.to_nat (int.val s.(log_state.durable_to))) s.(log_state.updates).

(* updates in the on-disk log *)
Definition logged_upds (s:log_state.t): list update.t :=
  skipn (Z.to_nat (int.val s.(log_state.installed_to))) (stable_upds s).

(* update in the in-memory log *)
Definition inmem_upds (s:log_state.t): list update.t :=
  skipn (Z.to_nat (int.val s.(log_state.durable_to))) s.(log_state.updates).

Definition valid_addrs (updates: list update.t) (d: disk) :=
  forall i u, updates !! i = Some u -> ∃ (b: Block), d !! (int.val u.(update.addr)) = Some b.

Definition is_trans (trans: gmap u64 bool) pos :=
  trans !! pos = Some(true).

Definition valid_log_state (s : log_state.t) :=
  valid_addrs s.(log_state.updates) s.(log_state.disk) ∧
  is_trans s.(log_state.trans) s.(log_state.durable_to) ∧
  is_trans s.(log_state.trans) s.(log_state.installed_to) ∧
  int.val s.(log_state.installed_to) ≤ int.val s.(log_state.durable_to) ∧
  int.val (log_state.last_pos s) >= int.val s.(log_state.durable_to).

Lemma last_disk_at_pos: forall σ,
    last_disk σ = disk_at_pos (length σ.(log_state.updates)) σ.
Proof.
  intros.
  unfold last_disk; eauto.
Qed.

Lemma valid_installed: forall s,
    valid_log_state s ->
    int.val s.(log_state.installed_to) ≤ int.val (length s.(log_state.updates)).
Proof.
Admitted.

Definition log_crash: transition log_state.t unit :=
  kv ← suchThat (gen:=fun _ _ => None)
     (fun s '(pos, d, upds) => s.(log_state.disk) = d ∧
                            is_trans s.(log_state.trans) pos ∧
                            int.val pos >= int.val s.(log_state.durable_to) ∧
                            upds = firstn (Z.to_nat (int.val pos)) s.(log_state.updates));
  let '(pos, d, upds) := kv in
  modify (set log_state.disk (λ _, d ) ∘
          set log_state.updates (λ _, upds) ∘
          set log_state.durable_to (λ _, pos) ∘
          set log_state.installed_to (λ _, pos));;
  ret tt.

Definition update_installed: transition log_state.t u64 :=
  new_installed ← suchThat (gen:=fun _ _ => None)
                (fun s pos => is_trans s.(log_state.trans) pos ∧
                            int.val s.(log_state.installed_to) <=
                            int.val pos <=
                            int.val s.(log_state.durable_to));
  modify (set log_state.installed_to (λ _, new_installed));;
  ret new_installed.

Definition update_durable: transition log_state.t u64 :=
  new_durable ← suchThat (gen:=fun _ _ => None)
              (fun s pos =>  is_trans s.(log_state.trans) pos ∧
                          int.val s.(log_state.durable_to) <=
                          int.val pos <= 
                          int.val (length s.(log_state.updates)));
  modify (set log_state.durable_to (λ _, new_durable));;
  ret new_durable.

(* XXX is_trans pos? *)
Definition only_on_disk s (a: u64) :=
  forall pos b,
    int.val s.(log_state.installed_to) ≤ int.val pos ->
    (installed_disk s) !! (int.val a) = Some b ->
    (disk_at_pos pos s) !! (int.val a) = Some b.

Lemma only_on_disk_eq:
  forall s (a:u64) (b: Block),
    only_on_disk s a ->
    (last_disk s) !! (int.val a) = Some b ->
    (installed_disk s) !! (int.val a) = Some b.
Proof.
Admitted.

Lemma only_on_disk_last:
  forall s (a:u64) (b: Block),
    valid_log_state s ->
    only_on_disk s a ->
    (installed_disk s) !! (int.val a) = Some b ->
    (last_disk s) !! (int.val a) = Some b.
Proof.
  intros.
  unfold only_on_disk in *.
  destruct s eqn:sigma.
  specialize (H0 (length updates)).
  apply H0; simpl in *; eauto.
  unfold valid_log_state in *.
  intuition; simpl in *.
  unfold log_state.last_pos in H6; simpl in *.
  lia.
Qed.

Definition log_read_cache (a:u64): transition log_state.t (option Block) :=
  ok ← suchThat (fun _ (b:bool) => True);
  if (ok:bool)
  then d ← reads last_disk;
       match d !! int.val a with
       | None => undefined
       | Some b => ret (Some b)
       end
  else (* this is really non-deterministic; it would be simpler if upfront we
          moved installed_to forward to a valid transaction and then made most
          of the remaining decisions deterministically. *)
    update_installed;;
    suchThat (gen:=fun _ _ => None)
             (fun s (_:unit) => only_on_disk s a);;
    ret None.

Definition log_read_installed (a:u64): transition log_state.t Block :=
  update_installed;;
  d ← reads installed_disk;
  unwrap (d !! int.val a).

Fixpoint absorb_map upds m: gmap u64 Block :=
  match upds with
  | [] => m
  | upd :: upd0 => absorb_map upd0 (<[update.addr upd := update.b upd]> m)
  end.                   

Definition log_mem_append (upds: list update.t): transition log_state.t u64 :=
  logged ← reads logged_upds;
  assert (fun σ => length (logged ++ upds) <= circular_proof.LogSz);;
  inmem  ← reads inmem_upds;
  stable ← reads stable_upds;
  updates ← reads get_updates;
  (* new are the updates after absorbing of inmem in upds; that is,
  replacing upds in inmem with upds if to the same address.  *)
  new ← suchThat (gen:=fun _ _ => None)
                 (fun s new => absorb_map new ∅ = absorb_map (inmem++upds) ∅);
  modify (set log_state.updates (λ _, stable++new));;
  modify (set log_state.trans <[ U64 (length updates) := true]>);;
  ret (U64 (length (stable++new))).

Definition log_flush (pos: u64): transition log_state.t unit :=
  p  ← suchThat (gen:=fun _ _ => None)
     (fun s (p:u64) => is_trans  s.(log_state.trans) pos ∧ p = pos);
  modify (set log_state.durable_to (λ _, p)).

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
  {{{ P (log_state.mk (blocks_to_gmap bs) ([]) (∅) (U64 0) (U64 0)) ∗ 0 d↦∗ bs }}}
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



