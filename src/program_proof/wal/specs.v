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
  fold_left (fun d '(update.mk a b) => <[int.val a := b]> d) upds d.

Definition get_updates (s:log_state.t): list update.t :=
  s.(log_state.updates).

Definition disk_at_pos (pos: nat) (s:log_state.t): disk :=
  apply_upds (firstn pos s.(log_state.updates)) s.(log_state.disk).

Definition updates_since (pos: u64) (a: u64) (s : log_state.t) : list Block :=
  map update.b
  (filter (fun u => u.(update.addr) = a) (skipn (int.nat pos) s.(log_state.updates))).

Fixpoint latest_update (base: Block) (upds: list Block) : Block :=
  match upds with
  | u :: upds' =>
    latest_update u upds'
  | nil => base
  end.

Definition is_last_pos (m : gmap u64 Block) (pos : u64) : Prop :=
  ∀ (pos' : u64) b,
    m !! pos' = Some b -> word.ltu pos' pos ∨ pos' = pos.

Definition is_last_block (m : gmap u64 Block) (b : Block) : Prop :=
  ∃ pos,
    is_last_pos m pos ∧
    m !! pos = Some b.

Definition last_disk (s:log_state.t): disk :=
  disk_at_pos (length s.(log_state.updates)) s.

Definition installed_disk (s:log_state.t): disk :=
  disk_at_pos (int.nat s.(log_state.installed_to)) s.

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

Theorem valid_log_state_advance_installed_to σ pos :
  valid_log_state σ ->
  is_trans σ.(log_state.trans) pos ->
  int.val pos ≤ int.val σ.(log_state.durable_to) ->
  valid_log_state (set log_state.installed_to (λ _ : u64, pos) σ).
Proof.
  destruct σ.
  unfold valid_log_state; simpl.
  intuition.
Qed.

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

(*
(* XXX is_trans pos? *)
Definition only_on_disk s (a: u64) :=
  forall pos,
    int.val s.(log_state.installed_to) ≤ pos ->
    (disk_at_pos (Z.to_nat pos) s) !! (int.val a) = (installed_disk s) !! (int.val a).
*)

(*
Lemma only_on_disk_eq:
  forall s (a:u64) (b: Block),
    valid_log_state s ->
    only_on_disk s a ->
    (last_disk s) !! (int.val a) = Some b ->
    (installed_disk s) !! (int.val a) = Some b.
Proof.
  unfold only_on_disk.
  unfold last_disk, installed_disk.
  intros.
  specialize (H0 (length s.(log_state.updates))).
  rewrite <- H0; auto.
  apply valid_installed.
  auto.
Qed.

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
  rewrite H0; simpl in *; eauto.
  unfold valid_log_state in *.
  intuition; simpl in *.
  unfold log_state.last_pos in H6; simpl in *.
  lia.
Qed.
*)

Theorem apply_upds_cons disk u ul :
  apply_upds (u :: ul) disk =
  apply_upds ul (apply_upds [u] disk).
Proof.
  reflexivity.
Qed.

Theorem apply_upds_app : forall u1 u2 disk,
  apply_upds (u1 ++ u2) disk =
  apply_upds u2 (apply_upds u1 disk).
Proof.
  induction u1.
  - reflexivity.
  - simpl app.
    intros.
    rewrite apply_upds_cons.
    rewrite IHu1.
    reflexivity.
Qed.

Theorem updates_since_to_last_disk σ a (pos : u64) installed :
  disk_at_pos (int.nat pos) σ !! int.val a = Some installed ->
  int.val pos ≤ int.val σ.(log_state.installed_to) ->
  last_disk σ !! int.val a = Some (latest_update installed (updates_since pos a σ)).
Proof.
  destruct σ.
  unfold last_disk, updates_since, disk_at_pos.
  simpl.
  intros.
  rewrite firstn_all.
  rewrite <- (firstn_skipn (int.nat pos)) at 1.
  rewrite apply_upds_app.
  generalize dependent H.
  generalize (apply_upds (take (int.nat pos) updates) disk).
  intros.
  generalize (drop (int.nat pos) updates).
  intros.
  generalize dependent d.
  generalize dependent installed.
  induction l; simpl; intros.
  - auto.
  - destruct a0.
    rewrite filter_cons; simpl.
    destruct (decide (addr = a)); subst.
    + simpl.
      erewrite <- IHl.
      { reflexivity. }
      rewrite lookup_insert. auto.
    + erewrite <- IHl.
      { reflexivity. }
      rewrite lookup_insert_ne; auto.
      intro Hx. apply n. word.
Qed.

Theorem disk_at_pos_installed_to σ pos0 pos :
  disk_at_pos pos0 (@set _ _  log_state.installed_to
      (fun (_ : forall _ : u64, u64) (x2 : log_state.t) => x2) (λ _ : u64, pos) σ) =
  disk_at_pos pos0 σ.
Proof.
  reflexivity.
Qed.

Theorem last_disk_installed_to σ pos :
  last_disk (@set _ _  log_state.installed_to
      (fun (_ : forall _ : u64, u64) (x2 : log_state.t) => x2) (λ _ : u64, pos) σ) =
  last_disk σ.
Proof.
  reflexivity.
Qed.

Definition no_updates_since σ a (pos : u64) :=
  ∀ (pos' : u64) u,
    int.val pos < int.val pos' ->
    σ.(log_state.updates) !! int.nat pos' = Some u ->
    u.(update.addr) ≠ a.

Theorem no_updates_since_nil σ a (pos : u64) :
  no_updates_since σ a pos ->
  updates_since pos a σ = nil.
Proof.
  unfold no_updates_since, updates_since.
  intros.
Admitted.

Theorem no_updates_since_last_disk σ a (pos : u64) :
  no_updates_since σ a pos ->
  disk_at_pos (int.nat pos) σ !! int.val a = last_disk σ !! int.val a.
Proof.
Admitted.

Theorem updates_since_apply_upds σ a (pos diskpos : u64) installedb b :
  int.val pos ≤ int.val diskpos ->
  disk_at_pos (int.nat pos) σ !! int.val a = Some installedb ->
  disk_at_pos (int.nat diskpos) σ !! int.val a = Some b ->
  b ∈ installedb :: updates_since pos a σ.
Proof.
Admitted.

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
             (fun s (_:unit) =>
                no_updates_since s a s.(log_state.installed_to));;
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



