From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import Map.

From Perennial.goose_lang Require Import crash_modality.
From Perennial.algebra Require Import deletable_heap.

From Goose.github_com.mit_pdos.perennial_examples Require Import alloc.
From Perennial.program_logic Require Export na_crash_inv.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.examples Require Import alloc_addrset.

Inductive block_status :=
| block_free
| block_reserved
| block_used.

Instance block_status_eq_dec : EqDecision block_status.
Proof.
  intros e1 e2.
  destruct e1, e2;
  try (abstract (left; congruence));
  try (abstract (right; congruence)).
Qed.

Canonical Structure gset64O := leibnizO (gset u64).

Class allocG Σ :=
  { alloc_used_preG :> gen_heapPreG u64 block_status Σ;
    alloc_freeset :> inG Σ (ghostR gset64O);
 }.

(* state representation types (defined here since modules can't be in sections) *)
Module alloc.
  Definition t := gmap u64 block_status.

  Definition domain (σ: t) : gset u64 := dom (gset u64) σ.
  Definition free (σ: t) : gset u64 := dom (gset u64) (filter (λ x, x.2 = block_free) σ).
  Definition used (σ: t) : gset u64 := dom (gset u64) (filter (λ x, x.2 = block_used) σ).
  Definition unused (σ: t) : gset u64 := dom (gset u64) (filter (λ x, x.2 ≠ block_used) σ).

  Global Instance _witness : Inhabited t.
  Proof. econstructor. apply (∅: gmap u64 block_status). Defined.

  Lemma unused_used_disjoint σ :
    unused σ ## used σ.
  Proof.
    rewrite /unused /used.
    apply elem_of_disjoint => a H1 H2.
    apply elem_of_dom in H1 as [s1 [H1 Hs1]%map_filter_lookup_Some].
    apply elem_of_dom in H2 as [s2 [H2 Hs2]%map_filter_lookup_Some].
    congruence.
  Qed.

  Lemma unused_used_domain σ :
    unused σ ∪ used σ = domain σ.
  Proof.
    rewrite /unused /used /domain.
    apply gset_eq => a.
    rewrite elem_of_union.
    rewrite !elem_of_dom.
    split.
    - destruct 1.
      + destruct H as [s [H _]%map_filter_lookup_Some]; eauto.
      + destruct H as [s [H _]%map_filter_lookup_Some]; eauto.
    - intros.
      destruct H as [s H].
      destruct (decide (s = block_used)); [right | left]; exists s.
      + rewrite map_filter_lookup_Some; eauto.
      + rewrite map_filter_lookup_Some; eauto.
  Qed.
End alloc.

Definition alloc_post_crash (σ: alloc.t) : Prop :=
  alloc.free σ = alloc.unused σ.

Lemma alloc_post_crash_lookup_unused σ k:
  alloc_post_crash σ →
  k ∈ alloc.unused σ →
  σ !! k = Some block_free.
Proof.
  intros <-. rewrite elem_of_dom. intros (kv&Hlook).
  edestruct (map_filter_lookup_Some (λ x, x.2 = block_free) σ k kv) as (Hlook'&_).
  simpl in *; intuition; subst; auto.
Qed.

Lemma alloc_post_crash_lookup_not_reserved σ k:
  alloc_post_crash σ →
  ¬ (σ !! k = Some block_reserved).
Proof.
  intros Hcrash Hlook.
  assert (σ !! k = Some block_free); last by congruence.
  apply alloc_post_crash_lookup_unused; auto.
  rewrite /alloc.unused. rewrite elem_of_dom. eexists.
  rewrite map_filter_lookup_Some; split; eauto.
Qed.

Lemma alloc_post_crash_used σ :
  alloc_post_crash σ →
  alloc.free σ = alloc.domain σ ∖ alloc.used σ.
Proof.
  intros ->.
  pose proof (alloc.unused_used_domain σ).
  pose proof (alloc.unused_used_disjoint σ).
  set_solver.
Qed.

Section goose.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!allocG Σ}.
Context `{!crashG Σ}.
Context `{!stagedG Σ}.

Record alloc_names :=
  { alloc_status_name: gen_heapG u64 block_status Σ;
    alloc_free_name : gname;
  }.

Instance alloc_names_eta : Settable _ := settable! Build_alloc_names <alloc_status_name; alloc_free_name>.

Implicit Types (a: u64) (m: gmap u64 ()) (free: gset u64).

Context (P: alloc.t → iProp Σ).
Context (Ψ: u64 → iProp Σ).
Context (N: namespace).
Implicit Types (l:loc) (γ:alloc_names) (σ: alloc.t).

Definition Nlock := N.@"allocator".
Definition Ncrash := N.@"crash".
Definition Ninv := N.@"inv".

Definition allocator_inv γ (d: gset u64) : iProp Σ :=
  ∃ σ,
    "%Hdom" ∷ ⌜ dom _ σ = d ⌝ ∗
    "Hstatus" ∷ gen_heap_ctx (hG:=γ.(alloc_status_name)) σ ∗
    "Hfreeset_auth" ∷ own (γ.(alloc_free_name)) (● (Excl' (alloc.free σ))) ∗
    "HP" ∷ P σ
.

Definition block_cinv γ addr : iProp Σ :=
  Ψ addr ∨ mapsto (hG := alloc_status_name γ) addr 1 block_used.

Definition free_block γ n k : iProp Σ :=
  "Hcrashinv" ∷ (na_crash_inv Ncrash (LVL n) (Ψ k) (block_cinv γ k)) ∗
  "Hmapsto" ∷ (mapsto (hG := alloc_status_name γ) k 1 block_free).

Definition free_block_pending γ n k : iProp Σ :=
  (|C={⊤, ∅}_(LVL (S n))=> block_cinv γ k).

Definition reserved_block γ n k P : iProp Σ :=
  "Hcrashinv" ∷ (na_crash_inv Ncrash (LVL n) P (block_cinv γ k)) ∗
  "Hmapsto" ∷ (mapsto (hG := alloc_status_name γ) k 1 block_reserved) ∗
  "Halloc_inv" ∷ ∃ d, inv Ninv (allocator_inv γ d).

Definition reserved_block_in_prep γ (n: nat) k : iProp Σ :=
  "Hmapsto" ∷ (mapsto (hG := alloc_status_name γ) k 1 block_reserved) ∗
  "Halloc_inv" ∷ ∃ d, inv Ninv (allocator_inv γ d).

Definition used_block γ k : iProp Σ :=
  "Hmapsto" ∷ (mapsto (hG := alloc_status_name γ) k 1 block_used).

(*
Definition block_status_interp γ k st : iProp Σ :=
  match st with
  | block_free => free_block γ k
  | block_used => True
  | block_reserved => True
  end.
*)

Definition allocator_linv γ n (mref: loc) : iProp Σ :=
 ∃ (freeset: gset u64),
  "Hfreemap" ∷ is_addrset mref (freeset) ∗
  "Hblocks" ∷ ([∗ set] k ∈ freeset, free_block γ n k) ∗
  "Hfreeset_frag" ∷ own (γ.(alloc_free_name)) (◯ (Excl' freeset))
.

Definition is_allocator (l: loc) (d: gset u64) γ n : iProp Σ :=
  ∃ (lref mref: loc) (γlk: gname),
    "#m" ∷ readonly (l ↦[Allocator.S :: "m"] #lref) ∗
    "#free" ∷ readonly (l ↦[Allocator.S :: "free"] #mref) ∗
    "#His_lock" ∷ is_lock Nlock γlk #lref (allocator_linv γ n mref) ∗
    "#Halloc_inv" ∷ inv Ninv (allocator_inv γ d)
.

Definition is_allocator_mem_pre (l: loc) σ : iProp Σ :=
  ∃ (lref mref: loc) (γlk: gname),
    "%Hpostcrash" ∷ ⌜ alloc_post_crash σ ⌝ ∗
    "#m" ∷ readonly (l ↦[Allocator.S :: "m"] #lref) ∗
    "#free" ∷ readonly (l ↦[Allocator.S :: "free"] #mref) ∗
    "Hfreemap" ∷ is_addrset mref (alloc.free σ) ∗
    "Hfree_lock" ∷ is_free_lock γlk lref.

(* TODO: prove something useful for initializing from zero blocks *)

Lemma alloc_post_crash_free_used σ :
  alloc.free σ = alloc.domain σ ∖ alloc.used σ ↔
  alloc_post_crash σ.
Proof.
  clear.
  rewrite /alloc_post_crash.
  pose proof (alloc.unused_used_domain σ).
  pose proof (alloc.unused_used_disjoint σ).
  set_solver.
Qed.

Lemma elem_of_filter_dom {A B} `{Countable A} (P': A * B → Prop) `{∀ x, Decision (P' x)} (m: gmap A B) (x: A) :
  x ∈ dom (gset A) (filter P' m) ↔ (∃ (y: B), m !! x = Some y ∧ P' (x,y)).
Proof.
  split; intros.
  - apply elem_of_dom in H1 as [y [H1 Hy]%map_filter_lookup_Some];
      simpl in *; subst.
    exists y; eauto.
  - destruct H1 as [y [Hlookup HP]].
    apply elem_of_dom; eexists.
    apply map_filter_lookup_Some; eauto.
Qed.

Lemma alloc_post_crash_no_reserved σ :
  alloc_post_crash σ ↔
  dom (gset u64) (filter (λ '(_,s), s = block_reserved) σ) = ∅.
Proof.
  rewrite /alloc_post_crash.
  split; intros.
  - apply gset_elem_is_empty; intros.
    rewrite elem_of_filter_dom.
    destruct 1 as [y [? ->]].
    assert (x ∈ alloc.free σ).
    { rewrite H.
      rewrite /alloc.unused elem_of_filter_dom.
      eexists; eauto. }
    apply elem_of_filter_dom in H1 as [? [? Heq]]; simpl in Heq; congruence.
  - apply gset_eq; intros.
    rewrite /alloc.free /alloc.unused.
    rewrite !elem_of_filter_dom.
    split; intros.
    + destruct H0 as [? [? ?]]; simpl in *; eauto.
      exists x0; split; eauto.
      congruence.
    + destruct H0 as [? [? ?]]; simpl in *; eauto.
      exists x0; split; eauto.
      destruct x0; eauto; try congruence.
      cut (x ∈ (∅: gset u64)).
      { rewrite elem_of_empty; contradiction. }
      rewrite -H.
      apply elem_of_filter_dom.
      eauto.
Qed.

Definition new_alloc_state (start sz: Z) (used: gset u64): alloc.t :=
  gset_to_gmap block_used used ∪
  gset_to_gmap block_free (rangeSet start sz).

Lemma new_alloc_state_no_reserved start sz used :
  dom (gset u64) (filter (λ '(_, s), s = block_reserved)
                          (new_alloc_state start sz used)) = ∅.
Proof.
  clear.
  apply gset_elem_is_empty; intros x Helem.
  apply elem_of_dom in Helem as [s1 [Helem Hs1]%map_filter_lookup_Some];
    simpl in *; subst.
  apply lookup_union_Some_raw in Helem as [Helem | [? Helem]].
  - apply lookup_gset_to_gmap_Some in Helem.
    intuition congruence.
  - apply lookup_gset_to_gmap_Some in Helem.
    intuition congruence.
Qed.

Theorem new_alloc_state_properties start sz used :
  used ⊆ rangeSet start sz →
  let σ := new_alloc_state start sz used in
  alloc.domain σ = rangeSet start sz ∧
  alloc.free σ = alloc.domain σ ∖ alloc.used σ ∧
  alloc.used σ = used.
Proof.
  clear.
  intros.
  rewrite /alloc.domain.
  split_and!.
  - rewrite /new_alloc_state.
    rewrite dom_union_L.
    rewrite !dom_gset_to_gmap.
    set_solver.
  - apply alloc_post_crash_free_used.
    apply alloc_post_crash_no_reserved.
    apply new_alloc_state_no_reserved.
  - subst σ; rewrite /new_alloc_state /alloc.used.
    apply gset_eq; intros.
    rewrite elem_of_filter_dom /=.
    setoid_rewrite lookup_union_Some_raw.
    setoid_rewrite lookup_gset_to_gmap_Some.
    setoid_rewrite lookup_gset_to_gmap_None.
    split.
    + destruct 1 as [y [Hlookup ->]].
      intuition congruence.
    + intros.
      exists block_used; intuition eauto.
Qed.

(* TODO: remove σ and related assumptions, move those to the postcondition *)
Theorem wp_newAllocator σ mref (start sz: u64) (used: gset u64) :
  int.val start + int.val sz < 2^64 →
  alloc.domain σ = rangeSet (int.val start) (int.val sz) →
  alloc.free σ = alloc.domain σ ∖ alloc.used σ →
  alloc.used σ = used →
  {{{ is_addrset mref used  }}}
    New #start #sz #mref
  {{{ l, RET #l; is_allocator_mem_pre l σ }}}.
Proof using allocG0.
  iIntros (Hoverflow Hdom Husedeq ? Φ) "Hused HΦ"; subst used.
  wp_call.
  wp_apply wp_freeRange; first by auto.
  iIntros (mref') "Hfree".
  wp_pures.
  wp_apply (wp_mapRemove with "[$Hfree $Hused]"); iIntros "(Hfree & Hused)".
  wp_apply wp_new_free_lock.
  iIntros (γ1 lk) "Hlock".
  rewrite -wp_fupd.
  wp_apply wp_allocStruct; auto.
  iIntros (l) "Hallocator".
  iDestruct (struct_fields_split with "Hallocator") as "(m&free&_)".
  iMod (readonly_alloc_1 with "m") as "#m".
  iMod (readonly_alloc_1 with "free") as "#free".
  iModIntro.
  iApply ("HΦ" $! _).
  iExists _, _, _; iFrame "#".
  rewrite Husedeq Hdom. iFrame.
  iPureIntro.
  apply alloc_post_crash_free_used; auto.
Qed.

Context {Hitemcrash: ∀ x, IntoCrash (Ψ x) (λ _, Ψ x)}.
(*
Instance allocator_post_crash γ mref σ :
  IntoCrash (allocator_linv γ mref σ) (λ _, allocator_durable σ).
Proof.
  hnf; iNamed 1.
  by iFrame.
Qed.
*)

Global Instance is_allocator_Persistent l γ d n:
  Persistent (is_allocator l d γ n).
Proof. apply _. Qed.

Definition alloc_crash_cond' σ : iProp Σ :=
  [∗ set] k ∈ alloc.unused σ, Ψ k.

Definition alloc_crash_cond (d: gset u64) : iProp Σ :=
  ∃ σ, ⌜dom _ σ = d⌝ ∗ P σ ∗ [∗ set] k ∈ alloc.unused σ, Ψ k.

Theorem reserved_block_weaken γ n k R R' :
  □(R -∗ R') -∗
  reserved_block γ n k R -∗
  reserved_block γ n k R'.
Proof.
  iIntros "#HR'"; iNamed 1.
  iFrame. by iApply (na_crash_inv_weaken with "HR'").
Qed.

Lemma free_big_sepS_to_all σ (Φ: u64 → iProp Σ):
  ([∗ set] k ∈ alloc.free σ, Φ k) ⊣⊢
  [∗ map] k↦v ∈ σ, match v with block_free => Φ k | _ => True end.
Proof.
  rewrite -big_opM_dom big_sepM_filter.
  apply big_sepM_proper. intros ? []; eauto => //=;
  try (by rewrite decide_False);
  try (by rewrite decide_True).
Qed.

Lemma free_block_init γ n σ E:
  ↑Ncrash ⊆ E →
  alloc_post_crash σ →
  ([∗ set] k ∈ alloc.unused σ, Ψ k) -∗
  ([∗ map] k↦v ∈ σ, mapsto (hG := alloc_status_name γ) k 1 v) -∗
  |={E}=> ([∗ set] k ∈ dom (gset _) σ, free_block_pending γ n k) ∗
          ([∗ set] k ∈ alloc.free σ, free_block γ n k).
Proof.
  iIntros (Hin Hcrashed) "Hfree Hpts".
  rewrite -?Hcrashed.
  rewrite ?free_big_sepS_to_all.
  iCombine "Hpts Hfree" as "H".
  rewrite -big_opM_dom -?big_sepM_sep.
  iApply big_sepM_fupd. iApply (big_sepM_mono with "H").
  iIntros (k x Hlookup) "(Hmaps&HΨ)".
  destruct x.
  - (* TODO: should they all be in the same na_crash_inv? *)
    iMod (na_crash_inv_alloc Ncrash _ _ (block_cinv γ k) (Ψ k) with "[$] []") as
        "(Hbund&Hpend)".
    { auto. }
    { iIntros "!> !> H". iLeft. eauto. }
    iModIntro. iFrame. 
  - exfalso. eapply alloc_post_crash_lookup_not_reserved; eauto.
  - (* TODO: should they all be in the same na_crash_inv? *)
    iMod (na_crash_inv_alloc Ncrash _ _ (block_cinv γ k) (mapsto k 1 block_used) with "[$] []") as
        "(Hbund&Hpend)".
    { auto. }
    { iIntros "!> !> H". iRight. eauto. }
    iModIntro. iFrame.
Qed.

Theorem is_allocator_alloc n l σ :
  ([∗ set] k ∈ alloc.unused σ, Ψ k) -∗
  ▷ P σ -∗
  is_allocator_mem_pre l σ
  ={⊤}=∗
  ∃ γ, is_allocator l (alloc.domain σ) γ n ∗
  |C={⊤, ↑N}_(LVL (size (alloc.domain σ) + S (S n)))=> alloc_crash_cond (alloc.domain σ).
Proof.
  clear Hitemcrash.
  iIntros "Hunused HP". iNamed 1.
  iMod (gen_heap_strong_init σ) as (γheap Hpf) "(Hctx&Hpts)".
  iMod (ghost_var_alloc (alloc.free σ)) as (γfree) "(Hfree&Hfree_frag)".
  set (γ := {| alloc_status_name := γheap;
               alloc_free_name := γfree |}).

  iMod (inv_alloc Ninv _ (allocator_inv γ (alloc.domain σ)) with "[HP Hctx Hfree]") as "#Hinv".
  { iNext. iExists _. iFrame. eauto. }

  iMod (free_block_init γ n with "[$] [$]") as "(Hpending&Hblock)".
  { set_solver. }
  { eauto. }

  iDestruct (cfupd_big_sepS with "Hpending") as "Hpending".

  iMod (alloc_lock Nlock ⊤ _ _ (allocator_linv γ n mref)%I
          with "[$Hfree_lock] [Hfreemap Hblock Hfree_frag]") as "#Hlock".
  { iExists _; iFrame. }

  iDestruct (inv_cfupd1 _ ⊤ with "Hinv") as "-#Hallocinv".
  { set_solver. }

  iModIntro.
  iExists γ.
  iSplitR.
  { iExists _, _, _; iFrame "#". }
  iMod "Hallocinv" as "_".
  { pose proof (LVL_gt (size (alloc.domain σ) + S (S n))); lia. }
  iMod "Hpending" as "_".
  { change (size (dom _ σ)) with (size (alloc.domain σ)).
    replace (size (alloc.domain σ) + S (S n))%nat
            with (S (size (alloc.domain σ) + S n))%nat by lia.
    rewrite LVL_Sk.
    lia. }
  iModIntro. iNext.

  iIntros "Hset Hinner".
  iNamed "Hinner".
  iExists _. iFrame.
  fold (alloc.domain σ).
  rewrite /alloc.unused.
  rewrite -Hdom.
  iSplitR; first by auto.
  rewrite -?big_sepM_dom big_sepM_filter.
  iDestruct (big_sepM_mono_with_inv with "Hstatus Hset") as "(_&$)".
  iIntros (k x Hlookup) "(Hctx&Hfree)".
  iDestruct "Hfree" as "[HΨ|Hused]".
  - iFrame. destruct (decide _); eauto.
  - iDestruct (gen_heap_valid with "[$] Hused") as %Hlookup'.
    iFrame. rewrite decide_False //= => Heq. congruence.
Qed.

Lemma map_empty_difference `{Countable K} {V} (m: gmap K V) :
  ∅ ∖ m = ∅.
Proof.
  apply map_eq; intros.
  rewrite lookup_difference_None; eauto.
Qed.

Lemma set_empty_difference `{Countable K} (m: gset K) :
  ∅ ∖ m = ∅.
Proof.
  clear.
  set_solver.
Qed.

Theorem alloc_free_reserve σ new :
  alloc.free (<[new := block_reserved]> σ) =
  alloc.free σ ∖ {[new]}.
Proof.
  clear.
  rewrite /alloc.free /=.
  rewrite map_filter_insert_not_strong //=.
  rewrite map_filter_delete (dom_delete_L) //.
Qed.

Theorem alloc_free_free σ new :
  alloc.free (<[new := block_free]> σ) =
  alloc.free σ ∪ {[new]}.
Proof.
  clear.
  rewrite /alloc.free /=.
  rewrite map_filter_insert //= dom_insert_L. set_solver.
Qed.

Theorem reserved_not_in_alloc_free σ a :
  σ !! a = Some block_reserved →
  a ∉ alloc.free σ.
Proof.
  clear.
  rewrite /alloc.free /= => Hlook.
  rewrite elem_of_dom. intros (x&(His&Heq)%map_filter_lookup_Some).
  simpl in Heq. rewrite Heq Hlook in His. congruence.
Qed.

Theorem alloc_free_subset σ :
  alloc.free σ ⊆ dom _ σ.
Proof. by apply dom_map_filter_subseteq. Qed.

(*
Theorem alloc_free_use σ new :
  alloc.free (set alloc.used (union new) σ) =
  alloc.free σ ∖ new.
Proof.
  clear.
  rewrite /alloc.free /=.
  set_solver.
Qed.
*)

Theorem wpc_Reserve (Q: option u64 → iProp Σ) (Qc: iProp Σ) l dset γ n n' E1 E2:
  ↑N ⊆ E1 →
  ↑nroot.@"readonly" ⊆ E1 →
  (∀ o, Q o -∗ Qc) →
  {{{ is_allocator l dset γ n' ∗
     (∀ σ σ' ma,
          ⌜match ma with
           | Some a => a ∈ alloc.free σ ∧ σ' = <[a := block_reserved]> σ
           | None => σ' = σ ∧ alloc.free σ = ∅
           end⌝ -∗
          ▷ P σ ={E1 ∖ ↑N}=∗ ▷ P σ' ∗ Q ma) ∧
      Qc
  }}}
    Allocator__Reserve #l  @ NotStuck; n; E1; E2
  {{{ a (ok: bool), RET (#a, #ok);
      if ok then Q (Some a) ∗ reserved_block γ n' a (Ψ a)
      else Q None }}}
  {{{ Qc }}}.
Proof.
  clear.
  iIntros (Hsub0 Hsub2 HQ Φ Φc) "(Hinv&Hfupd) HΦ". iNamed "Hinv".
  assert ((↑Nlock : coPset) ⊆ E1) as Hsub1.
  { solve_ndisj. }
  rewrite /Allocator__Reserve.

  Ltac show_crash1 :=
    try crash_case; iDestruct "Hfupd" as "(_&$)".

  wpc_pures; first by show_crash1.
  iMod (readonly_load with "m") as (?) "m'".
  { assumption. }
  iMod (readonly_load with "free") as (?) "free'".
  { assumption. }



  wpc_bind (lock.acquire _).
  wpc_frame "Hfupd HΦ"; first by show_crash1.
  wp_loadField.
  wp_apply (acquire_spec' with "His_lock"); first assumption.
  iIntros "(His_locked & Hinner)"; iNamed "Hinner". iNamed 1.

  wpc_pures; first by show_crash1.
  wpc_bind (findKey _).
  wpc_frame "Hfupd HΦ"; first by show_crash1.
  wp_loadField.
  wp_apply (wp_findKey with "Hfreemap").
  iIntros (k ok) "[%Hk Hfreemap]".
  iNamed 1.


  wpc_pures; first by show_crash1.

  wpc_bind (impl.MapDelete _ _).
  wpc_frame "Hfupd HΦ"; first by show_crash1.
  wp_loadField.
  iDestruct "Hfreemap" as (m') "[Hfreemap %Hdom]".
  wp_apply (wp_MapDelete with "Hfreemap"); iIntros "Hfreemap".
  iNamed 1.


  iAssert (is_addrset mref (freeset ∖ {[k]})) with "[Hfreemap]" as "Hfreemap".
  { iExists _; iFrame.
    iPureIntro.
    rewrite /map_del.
    rewrite dom_delete_L.
    set_solver. }


  wpc_pure _ _; first by show_crash1.
  wpc_pure _ _; first by show_crash1.

  (* Linearization point here. *)
  wpc_bind (Skip).
  iApply wpc_atomic_no_mask; iSplit; first by show_crash1.
  iInv "Halloc_inv" as "H".
  wp_pures.


  destruct ok.

  - (* extract block *)

    iNamed "H".
    iDestruct (ghost_var_agree with "Hfreeset_auth [$]") as %Heq.
    iDestruct "Hfupd" as "(Hfupd&_)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hrestore_mask"; first solve_ndisj.
    iMod ("Hfupd" $! σ _ (Some k) with "[] [$]") as "(HP&HQ)".
    { iPureIntro; split; last by reflexivity. rewrite Heq. eauto. }
    iMod "Hrestore_mask" as "_".

    iDestruct (big_sepS_delete with "Hblocks") as "[Hbk Hblocks]"; eauto.
    iNamed "Hbk".

    iMod (gen_heap_update _ k _ block_reserved with "[$] [$]") as "(Hctx&Hmapsto)".
    iMod (ghost_var_update _ (alloc.free (<[k := block_reserved]>σ)) with "Hfreeset_auth [$]")
         as "(Hfreeset_auth&Hfreeset_frag)".

    iModIntro. iSplitL "HP Hfreeset_auth Hctx".
    { iNext. iExists _. iFrame. iPureIntro.
      rewrite dom_insert_L.
      assert (k ∈ dom (gset u64) σ).
      { rewrite -Heq in Hk. by apply alloc_free_subset. }
      set_solver.
    }
    iSplit.
    { iModIntro. crash_case. iApply HQ. iFrame. }
    iModIntro.
    Ltac show_crash2 HQ :=
      try crash_case; iApply HQ; iFrame.

    wpc_pures; first by show_crash2 HQ.

    wpc_frame "HΦ HQ"; first by show_crash2 HQ.
    wp_loadField.
    wp_apply (release_spec' with "[Hfreeset_frag Hblocks Hfreemap $His_locked $His_lock]"); first assumption.
    { iExists _; iFrame.
      rewrite alloc_free_reserve. rewrite Heq. eauto.
    }
    wp_pures.
    iNamed 1. iApply "HΦ"; iFrame.
    { iExists _. eauto. }
  - iNamed "H".
    iDestruct (ghost_var_agree with "Hfreeset_auth [$]") as %Heq.
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hrestore_mask"; first solve_ndisj.
    iDestruct "Hfupd" as "(Hfupd&_)".
    iMod ("Hfupd" $! σ _ None with "[] [$]") as "(HP&HQ)".
    { iPureIntro; split; first by reflexivity. congruence. }
    iMod "Hrestore_mask" as "_".

    iModIntro. iSplitL "HP Hfreeset_auth Hstatus".
    { iNext. iExists _. iFrame. iPureIntro. eauto. }
    iSplit.
    { iModIntro. crash_case. iApply HQ. iFrame. }
    iModIntro.
    wpc_pures; first by show_crash2 HQ.

    wpc_frame "HΦ HQ"; first by show_crash2 HQ.
    wp_loadField.
    wp_apply (release_spec' with "[Hfreeset_frag Hblocks Hfreemap $His_locked $His_lock]"); first assumption.
    { iExists _; iFrame. rewrite Hk set_empty_difference. iFrame. }
    wp_pures.
    iNamed 1. iApply "HΦ"; iFrame.
Qed.

Lemma block_cinv_free_pred γ a :
  Ψ a -∗ block_cinv γ a.
Proof.
  iIntros "HΨ".
  iLeft; auto.
Qed.

Lemma block_cinv_from_used γ a :
  used_block γ a -∗ block_cinv γ a.
Proof.
  rewrite /used_block /block_cinv.
  iIntros "Hused".
  iRight; auto.
Qed.

Lemma prepare_reserved_block_reuse R' E R n n' γ e a Φ Φc:
  (S n < n')%nat →
  language.to_val e = None →
  reserved_block γ n' a R -∗
  Φc ∧
  (R -∗
   reserved_block_in_prep γ n' a -∗
   WPC e @ LVL n; (⊤ ∖ ↑Ncrash); ∅ {{ λ v, (reserved_block γ n' a (R' v) -∗ Φc ∧ Φ v) ∗
                                           (R' v) ∗
                                           reserved_block_in_prep γ n' a ∗
                                           □ (R' v -∗ block_cinv γ a) }}
                                   {{ Φc ∗ ▷ block_cinv γ a }}) -∗
  WPC e @  (LVL (S n)); ⊤; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (??) "Hreserved H".
  iNamed "Hreserved".
  iDestruct "Halloc_inv" as (?) "#Hinv".
  iApply (wpc_na_crash_inv_open_modify (λ v, R' v) with "[$] [H Hmapsto]"); try iFrame; auto.
  iSplit.
  - iDestruct "H" as "($&_)".
  - iIntros "HR". iDestruct "H" as "(_&H)".
    iSpecialize ("H" with "[$] [Hmapsto]").
    { iFrame. iExists _. eauto. }
    iApply (wpc_strong_mono with "H"); eauto.
    iSplit.
    * iIntros (?) "(Hclose&HR&Hprep&Hcinv)". iModIntro. iFrame. iFrame "#".
      iIntros. iApply "Hclose". iSplitR "Hprep".
      ** by iFrame.
      ** iIntros. eauto.
    * iIntros. rewrite difference_diag_L. iApply step_fupdN_inner_later; eauto.
Qed.

Lemma prepare_reserved_block E1 E2 R n n' γ e a Φ Φc:
  ↑Ncrash ⊆ E1 →
  (S n < n')%nat →
  language.to_val e = None →
  reserved_block γ n' a R -∗
  Φc ∧
  (R -∗
   reserved_block_in_prep γ n' a -∗
   WPC e @ LVL n; (E1 ∖ ↑Ncrash); ∅ {{ λ v, (Φc ∧ Φ v) ∗ block_cinv γ a }}
                                   {{ Φc ∗ ▷ block_cinv γ a }}) -∗
  WPC e @  (LVL (S n)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (???) "Hreserved H".
  iNamed "Hreserved".
  iDestruct "Halloc_inv" as (?) "#Hinv".
  iApply (wpc_na_crash_inv_open_modify (λ v, block_cinv γ a) with "[$] [H Hmapsto]"); try iFrame; auto.
  iSplit.
  - iDestruct "H" as "($&_)".
  - iIntros "HR". iDestruct "H" as "(_&H)".
    iSpecialize ("H" with "[$] [Hmapsto]").
    { iFrame. iExists _. eauto. }
    iApply (wpc_strong_mono with "H"); eauto.
    iSplit.
    * iIntros (?) "(Hclose&Hcinv)". iModIntro. iFrame. iFrame "#".
      iSplitL "".
      ** eauto.
      ** eauto.
    * iIntros. rewrite difference_diag_L. iApply step_fupdN_inner_later; eauto.
Qed.

Lemma free_mark_used_non_free σ a:
  σ !! a ≠ Some block_free →
  alloc.free (<[a := block_used]> σ) = alloc.free σ.
Proof.
  intros Hneq. rewrite /alloc.free.
  rewrite map_filter_insert_not' //=.
  { intros []; subst; eauto. }
Qed.

Lemma dom_update_status σ a x x':
  σ !! a = Some x →
  dom (gset u64) (<[a := x']>σ) = dom (gset u64) σ.
Proof.
  intros Hlookup. rewrite dom_insert_L.
  cut (a ∈ dom (gset u64) σ).
  { set_solver+. }
  apply elem_of_dom; eauto.
Qed.

Lemma mark_used E γ n' a Q:
  ↑Ninv ⊆ E →
   reserved_block_in_prep γ n' a -∗
   (∀ σ, ⌜ σ !! a = Some block_reserved ⌝ -∗
         P σ ={E ∖ ↑ N}=∗ ▷ P (<[a := block_used]> σ) ∗ Q)
   ={E,E ∖ ↑Ninv, E}▷=∗ Q ∗ used_block γ a.
Proof.
  iIntros (?) "Hprep Hfupd".
  iNamed "Hprep".
  iDestruct "Halloc_inv" as (d) "#Hinv".
  iInv "Hinv" as "H" "Hclo".
  iModIntro. iNext. iNamed "H".
  iDestruct (gen_heap_valid with "[$] Hmapsto") as %Hlookup'.
  iMod (fupd_intro_mask' _ (E ∖ ↑N)) as "Hrestore_mask"; first solve_ndisj.
  iMod ("Hfupd" with "[//] [$]") as "(HP&HQ)".
  iMod "Hrestore_mask" as "_".
  iMod (gen_heap_update _ a _ block_used with "[$] [$]") as "(Hctx&Hmapsto)".
  iMod ("Hclo" with "[HP Hctx Hfreeset_auth]").
  { iNext. iExists _. iFrame "HP Hctx".
    rewrite (dom_update_status σ a block_reserved) //=.
    iFrame "%".
    rewrite (free_mark_used_non_free) //=.
    intros Heq; subst; eauto. rewrite Heq in Hlookup'. congruence.
  }
  iModIntro. iFrame.
Qed.

(*
Lemma gset_difference_difference `{Countable K} (A B C: gset K) :
  C ⊆ A →
  A ∖ (B ∖ C) = A ∖ B ∪ C.
Proof using.
  clear.
  intros.
  apply gset_eq; intros k.
  rewrite !elem_of_difference.
  intuition.
  - destruct (decide (k ∈ C)); set_solver.
  - set_solver.
  - set_solver.
Qed.

Theorem alloc_free_free σ new :
  new ⊆ σ.(alloc.domain) →
  alloc.free (set alloc.used (λ used, used ∖ new) σ) =
  alloc.free σ ∪ new.
Proof.
  intros Hsub.
  rewrite /alloc.free /=.
  rewrite gset_difference_difference //.
Qed.

Lemma alloc_used_valid γ a used :
  gen_heap_ctx (hG:=γ.(alloc_status_name)) (gset_to_gmap () used) -∗
  alloc_used γ a -∗
  ⌜a ∈ used⌝.
Proof.
  rewrite /alloc_used.
  iIntros "Hctx Hused".
  iDestruct (gen_heap_valid with "Hctx Hused") as %Hlookup.
  iPureIntro.
  apply lookup_gset_to_gmap_Some in Hlookup as [? _]; auto.
Qed.
*)

(** XXX: should probably make this a WPC in case the fupd requires a durable resource *)
Theorem wp_Free (Q: iProp Σ) E l d γ n' (a: u64) :
  ↑N ⊆ E →
  ↑nroot.@"readonly" ⊆ E →
  {{{ is_allocator l d γ n' ∗ reserved_block γ n' a (Ψ a) ∗
     (∀ σ, ⌜ σ !! a = Some block_reserved ⌝ -∗ ▷ P σ ={E ∖↑N}=∗ ▷ P (<[ a := block_free ]> σ) ∗ Q)
  }}}
    Allocator__Free #l #a @ E
  {{{ RET #(); Q }}}.
Proof.
  clear Hitemcrash.
  iIntros (Hsub1 Hsub3 Φ) "(Halloc&Hreserved&Hfupd) HΦ"; iNamed "Halloc".
  assert (↑Nlock ⊆ E) as Hsub2 by solve_ndisj.
  iMod (readonly_load with "m") as (?) "m'".
  { assumption. }
  iMod (readonly_load with "free") as (?) "free'".
  { assumption. }
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec' with "His_lock").
  { auto. }
  iIntros "(Hlocked&Hinv)"; iNamed "Hinv".
  wp_loadField.
  iDestruct "Hfreemap" as (m) "[Hfreemap %Hdom]".
  wp_apply (wp_MapInsert _ _ _ _ () with "Hfreemap"); first by auto.
  iIntros "Hfreemap".
  do 2 wp_pure _.
  wp_bind (Skip).

  iInv "Halloc_inv" as "H" "Hclo".
  wp_pure _.
  iNamed "H".
  iNamed "Hreserved".
  iDestruct (ghost_var_agree with "Hfreeset_auth [$]") as %Heq.
  iDestruct (gen_heap_valid with "[$] Hmapsto") as %Hlookup'.
  iMod (gen_heap_update _ a _ block_free with "[$] [$]") as "(Hctx&Hmapsto)".
  iMod (ghost_var_update _ (alloc.free (<[a := block_free]>σ)) with "Hfreeset_auth [$]")
    as "(Hfreeset_auth&Hfreeset_frag)".
  iMod (fupd_intro_mask' _ (E ∖ ↑N)) as "Hrestore_mask"; first solve_ndisj.
  iMod ("Hfupd" $! σ with "[%//] HP") as "[HP HQ]".
  iMod "Hrestore_mask" as "_".
  iMod ("Hclo" with "[HP Hctx Hfreeset_auth]").
  { iNext. iExists _. iFrame. erewrite dom_update_status; eauto. }
  iModIntro. wp_pures.
  iAssert (is_addrset mref (alloc.free (<[a := block_free]>σ))) with "[Hfreemap]" as "Hfreemap".
  { iExists _; iFrame.
    iPureIntro.
    rewrite /map_insert dom_insert_L alloc_free_free.
    set_solver. }
  wp_loadField.
  wp_apply (release_spec' with "[$His_lock $Hlocked Hmapsto Hfreemap Hcrashinv Hfreeset_frag Hblocks]").
  { auto. }
  {
    iExists _. iFrame "Hfreemap Hfreeset_frag".
    rewrite alloc_free_free.
    rewrite big_sepS_union; last first.
    { apply disjoint_singleton_r; auto. by apply reserved_not_in_alloc_free. }
    rewrite big_opS_singleton.
    rewrite Heq. iFrame.
  }
  iApply ("HΦ" with "[$]").
Qed.

End goose.
