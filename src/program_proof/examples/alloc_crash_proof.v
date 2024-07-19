From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import Map gset.

From Perennial.goose_lang Require Import crash_modality crash_borrow.
From Perennial.base_logic Require Import lib.ghost_map.

From Goose.github_com.mit_pdos.perennial_examples Require Import alloc.
From Perennial.program_logic Require Export ncinv.
From Perennial.program_proof.examples Require Import alloc_addrset.

Inductive block_status :=
| block_free
| block_reserved
| block_used.

#[global]
Instance block_status_eq_dec : EqDecision block_status.
Proof.
  intros e1 e2.
  destruct e1, e2;
  try (abstract (left; congruence));
  try (abstract (right; congruence)).
Qed.

Class allocG Σ :=
  { alloc_used_preG :> ghost_mapG Σ u64 block_status;
    alloc_freeset :> ghost_varG Σ (gset u64);
 }.

(* state representation types (defined here since modules can't be in sections) *)
Module alloc.
  Definition t := gmap u64 block_status.

  Definition domain (σ: t) : gset u64 := dom σ.
  Definition free (σ: t) : gset u64 := dom (filter (λ x, x.2 = block_free) σ).
  Definition used (σ: t) : gset u64 := dom (filter (λ x, x.2 = block_used) σ).
  Definition unused (σ: t) : gset u64 := dom (filter (λ x, x.2 ≠ block_used) σ).

  Global Instance _witness : Inhabited t.
  Proof. econstructor. apply (∅: gmap u64 block_status). Defined.

  Lemma unused_used_disjoint σ :
    unused σ ## used σ.
  Proof.
    rewrite /unused /used.
    apply elem_of_disjoint => a H1 H2.
    apply elem_of_dom in H1 as [s1 [H1 Hs1]%map_lookup_filter_Some].
    apply elem_of_dom in H2 as [s2 [H2 Hs2]%map_lookup_filter_Some].
    congruence.
  Qed.

  Lemma unused_used_domain σ :
    unused σ ∪ used σ = domain σ.
  Proof.
    rewrite /unused /used /domain.
    apply set_eq => a.
    rewrite elem_of_union.
    rewrite !elem_of_dom.
    split.
    - destruct 1.
      + destruct H as [s [H _]%map_lookup_filter_Some]; eauto.
      + destruct H as [s [H _]%map_lookup_filter_Some]; eauto.
    - intros.
      destruct H as [s H].
      destruct (decide (s = block_used)); [right | left]; exists s.
      + rewrite map_lookup_filter_Some; eauto.
      + rewrite map_lookup_filter_Some; eauto.
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
  edestruct (map_lookup_filter_Some (λ x, x.2 = block_free) σ k kv) as (Hlook'&_).
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
  rewrite map_lookup_filter_Some; split; eauto.
Qed.

Lemma alloc_used_reserve s u :
  u ∈ alloc.free s →
  alloc.used (<[u:=block_reserved]> s) =
  alloc.used s.
Proof.
  rewrite /alloc.free /alloc.used.
  intros Hufree.
  apply elem_of_dom in Hufree as [status Hufree].
  apply map_lookup_filter_Some in Hufree as [Hufree ?];
    simpl in *; subst.
  rewrite map_filter_insert_not' //= => status.
  rewrite Hufree=>[= <-] //.
Qed.

Lemma alloc_free_reserved s a :
  s !! a = Some block_reserved →
  alloc.used (<[a := block_free]> s) =
  alloc.used s.
Proof.
  rewrite /alloc.used.
  intros Hareserved.
  rewrite map_filter_insert_not' //= => status.
  rewrite Hareserved=>[= <-] //.
Qed.

Lemma alloc_used_insert s a :
  alloc.used (<[a := block_used]> s) = {[a]} ∪ alloc.used s.
Proof.
  rewrite /alloc.used.
  rewrite map_filter_insert_True //.
  set_solver.
Qed.

Section goose.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.
Context `{!heapGS Σ}.
Context `{!allocG Σ}.
Context `{!stagedG Σ}.

Record alloc_names :=
  { alloc_status_name: gname;
    alloc_free_name : gname;
  }.

Instance alloc_names_eta : Settable _ := settable! Build_alloc_names <alloc_status_name; alloc_free_name>.

Implicit Types (a: u64) (m: gmap u64 ()) (free: gset u64).

Context (P: alloc.t → iProp Σ).
Context (Ψ: u64 → iProp Σ).
Context (N: namespace).
Implicit Types (l:loc) (γ:alloc_names) (σ: alloc.t).

Definition Nlock := N.@"allocator".
Definition Ninv := N.@"inv".

Definition allocator_inv γ (d: gset u64) : iProp Σ :=
  ∃ σ,
    "%Hdom" ∷ ⌜ dom σ = d ⌝ ∗
    "Hstatus" ∷ ghost_map_auth γ.(alloc_status_name) 1 σ ∗
    "Hfreeset_auth" ∷ ghost_var (γ.(alloc_free_name)) (1/2) (alloc.free σ) ∗
    "HP" ∷ P σ
.

Definition block_cinv γ addr : iProp Σ :=
  Ψ addr ∨ addr ↪[alloc_status_name γ] block_used.

Definition free_block γ k : iProp Σ :=
  "Hcrashinv" ∷ (crash_borrow (Ψ k) (block_cinv γ k)) ∗
  "Hmapsto" ∷ (k ↪[alloc_status_name γ] block_free).

Definition free_block_pending γ k : iProp Σ :=
  (|C={⊤}=> block_cinv γ k).

Definition reserved_block γ k P : iProp Σ :=
  "Hcrashinv" ∷ (crash_borrow P (block_cinv γ k)) ∗
  "Hmapsto" ∷ (k ↪[alloc_status_name γ] block_reserved) ∗
  "Halloc_inv" ∷ ∃ d, ncinv Ninv (allocator_inv γ d).

Definition reserved_block_in_prep γ k : iProp Σ :=
  "Hmapsto" ∷ (k ↪[alloc_status_name γ] block_reserved) ∗
  "Halloc_inv" ∷ ∃ d, ncinv Ninv (allocator_inv γ d).

Definition used_block γ k : iProp Σ :=
  "Hmapsto" ∷ (k ↪[alloc_status_name γ] block_used).

Definition allocator_linv γ (mref: loc) : iProp Σ :=
 ∃ (freeset: gset u64),
  "Hfreemap" ∷ is_addrset mref (freeset) ∗
  "Hblocks" ∷ ([∗ set] k ∈ freeset, k ↪[alloc_status_name γ] block_free) ∗
  "Hborrows" ∷ crash_borrow ([∗ set] k ∈ freeset, Ψ k) ([∗ set] k ∈ freeset, block_cinv γ k) ∗
  "Hfreeset_frag" ∷ ghost_var (γ.(alloc_free_name)) (1/2) (freeset)
.

Definition is_allocator (l: loc) (d: gset u64) γ : iProp Σ :=
  ∃ (lref mref: loc),
    "#m" ∷ readonly (l ↦[Allocator :: "m"] #lref) ∗
    "#free" ∷ readonly (l ↦[Allocator :: "free"] #mref) ∗
    "#His_lock" ∷ is_lock Nlock #lref (allocator_linv γ mref) ∗
    "#Halloc_inv" ∷ ncinv Ninv (allocator_inv γ d)
.

Definition is_allocator_mem_pre (l: loc) σ : iProp Σ :=
  ∃ (lref mref: loc),
    "%Hpostcrash" ∷ ⌜ alloc_post_crash σ ⌝ ∗
    "#m" ∷ readonly (l ↦[Allocator :: "m"] #lref) ∗
    "#free" ∷ readonly (l ↦[Allocator :: "free"] #mref) ∗
    "Hfreemap" ∷ is_addrset mref (alloc.free σ) ∗
    "Hfree_lock" ∷ is_free_lock lref ∗
    "Hltok" ∷ pre_borrow.


Theorem is_allocator_pre_post_crash l σ :
  is_allocator_mem_pre l σ -∗ ⌜alloc_post_crash σ⌝.
Proof.
  iNamed 1; eauto.
Qed.

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
  x ∈ dom (filter P' m) ↔ (∃ (y: B), m !! x = Some y ∧ P' (x,y)).
Proof.
  split; intros.
  - apply elem_of_dom in H1 as [y [H1 Hy]%map_lookup_filter_Some];
      simpl in *; subst.
    exists y; eauto.
  - destruct H1 as [y [Hlookup HP]].
    apply elem_of_dom; eexists.
    apply map_lookup_filter_Some; eauto.
Qed.

Lemma alloc_post_crash_no_reserved σ :
  alloc_post_crash σ ↔
  dom (filter (λ '(_,s), s = block_reserved) σ) = ∅.
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
  - apply set_eq; intros.
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

(* this code is no longer used, but left here in case we need to construct an
allocator state from nothing (say for initialization) since it's a bit
complicated. *)
Section new_alloc_state.
Definition new_alloc_state (start sz: Z) (used: gset u64): alloc.t :=
  gset_to_gmap block_used used ∪
  gset_to_gmap block_free (rangeSet start sz).

Lemma new_alloc_state_no_reserved start sz used :
  dom (filter (λ '(_, s), s = block_reserved)
                          (new_alloc_state start sz used)) = ∅.
Proof.
  clear.
  apply gset_elem_is_empty; intros x Helem.
  apply elem_of_dom in Helem as [s1 [Helem Hs1]%map_lookup_filter_Some];
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
  alloc_post_crash σ ∧
  alloc.used σ = used ∧
  alloc.unused σ = rangeSet start sz ∖ used.
Proof.
  clear.
  intros.
  rewrite /alloc.domain /alloc_post_crash.
  assert (alloc.used σ = used).
  { subst σ; rewrite /new_alloc_state /alloc.used.
    apply set_eq; intros.
    rewrite elem_of_filter_dom /=.
    setoid_rewrite lookup_union_Some_raw.
    setoid_rewrite lookup_gset_to_gmap_Some.
    setoid_rewrite lookup_gset_to_gmap_None.
    split.
    - destruct 1 as [y [Hlookup ->]].
      intuition congruence.
    - intros.
      exists block_used; intuition eauto.
  }
  assert (alloc.domain σ = rangeSet start sz).
  { rewrite /alloc.domain /σ.
    rewrite /new_alloc_state.
    rewrite dom_union_L.
    rewrite !dom_gset_to_gmap.
    set_solver. }
  rewrite -H0.
  split_and!; auto.
  - apply alloc_post_crash_no_reserved.
    apply new_alloc_state_no_reserved.
  - pose proof (alloc.unused_used_disjoint σ).
    pose proof (alloc.unused_used_domain σ).
    rewrite -H1.
    set_solver.
Qed.
End new_alloc_state.

Theorem wp_newAllocator {mref} {start sz: u64} σ (used: gset u64) :
  uint.Z start + uint.Z sz < 2^64 →
  alloc.domain σ = rangeSet (uint.Z start) (uint.Z sz) →
  alloc.used σ = used →
  alloc_post_crash σ →
  {{{ is_addrset mref used  }}}
    New #start #sz #mref 
  {{{ l, RET #l; is_allocator_mem_pre l σ }}}.
Proof using allocG0.
  iIntros (Hoverflow Hdom Hused Hfree Φ) "Hused HΦ".
  iApply wp_crash_borrow_generate_pre; auto.
  wp_rec. wp_pures.
  wp_apply wp_freeRange; first by auto.
  iIntros (mref') "Hfree".
  wp_pures.
  wp_apply (wp_mapRemove with "[$Hfree $Hused]"); iIntros "(Hfree & Hused)".
  wp_apply wp_new_free_lock.
  iIntros (lk) "Hlock".
  rewrite -wp_fupd.
  wp_apply wp_allocStruct; auto.
  iIntros (l) "Hallocator".
  iDestruct (struct_fields_split with "Hallocator") as "(m&free&_)".
  iMod (readonly_alloc_1 with "m") as "#m".
  iMod (readonly_alloc_1 with "free") as "#free".
  iModIntro.
  iIntros "Htoks".
  iApply "HΦ".
  iExists _, _; iFrame "∗#".
  iSplitR; first auto.
  (*
  iSplitR "Htoks"; last first.
  { iDestruct "Htoks" as "($&$&$&$&_)". }
   *)
  iExactEq "Hfree".
  rewrite /named.
  f_equal.
  apply alloc_post_crash_free_used in Hfree.
  congruence.
Qed.

Context {Hitemcrash: ∀ x, IntoCrash (Ψ x) (λ _, Ψ x)}.

Global Instance is_allocator_Persistent l γ d:
  Persistent (is_allocator l d γ).
Proof. apply _. Qed.

Definition alloc_crash_cond' σ : iProp Σ :=
  [∗ set] k ∈ alloc.unused σ, Ψ k.

Definition alloc_crash_cond (d: gset u64) (post_crash: bool) : iProp Σ :=
  ∃ σ, "%Halloc_post_crash" ∷ ⌜if post_crash then alloc_post_crash σ else True⌝ ∗
       "%Halloc_dom" ∷ ⌜dom σ = d⌝ ∗
       "HPalloc" ∷ ▷ P σ ∗
       "Hunused" ∷ [∗ set] k ∈ alloc.unused σ, Ψ k.

Definition alloc_crash_cond_no_later (d: gset u64) (post_crash: bool) : iProp Σ :=
  ∃ σ, "%Halloc_post_crash" ∷ ⌜if post_crash then alloc_post_crash σ else True⌝ ∗
       "%Halloc_dom" ∷ ⌜dom σ = d⌝ ∗
       "HPalloc" ∷ P σ ∗
       "Hunused" ∷ [∗ set] k ∈ alloc.unused σ, Ψ k.

Lemma alloc_crash_cond_from_post_crash d :
  alloc_crash_cond d true -∗ alloc_crash_cond d false.
Proof.
  iNamed 1.
  iExists _; iFrame "∗%".
Qed.

Lemma alloc_crash_cond_strip_later `{∀ σ, Timeless (P σ)} d b :
  alloc_crash_cond d b ={⊤}=∗ alloc_crash_cond_no_later d b.
Proof.
  iNamed 1.
  iDestruct "HPalloc" as ">HPalloc".
  iExists _; by iFrame.
Qed.

Lemma alloc_crash_cond_no_later_from_post_crash d :
  alloc_crash_cond_no_later d true -∗ alloc_crash_cond_no_later d false.
Proof.
  iNamed 1.
  iExists _; iFrame "∗%".
Qed.

Definition revert_reserved (σ : alloc.t) : alloc.t :=
  (λ x, if decide (x = block_reserved) then block_free else x) <$> (σ: gmap u64 block_status).

Lemma alloc_post_crash_revert_reserved σ:
  alloc_post_crash (revert_reserved σ).
Proof.
  clear.
  rewrite /alloc_post_crash /revert_reserved /alloc.free /alloc.unused.
  rewrite !map_filter_fmap /= !dom_fmap_L.
  f_equal. apply map_filter_ext. intros i x. simpl. destruct x.
  - rewrite decide_False //; auto.
  - rewrite decide_True //; discriminate.
  - rewrite decide_False //; auto.
Qed.

Lemma unused_revert_reserved σ:
  alloc.unused (revert_reserved σ) = alloc.unused σ.
Proof.
  clear.
  rewrite /alloc.unused /revert_reserved.
  rewrite map_filter_fmap /= dom_fmap_L.
  f_equal. apply map_filter_ext. intros i x. simpl. destruct x.
  - rewrite decide_False //; auto.
  - rewrite decide_True //; discriminate.
  - rewrite decide_False //; auto.
Qed.

Lemma dom_revert_reserved σ:
 dom (revert_reserved σ) = dom σ.
Proof.
  clear.
  rewrite /revert_reserved dom_fmap_L //.
Qed.

Lemma used_revert_reserved (σ0: alloc.t):
  alloc.used (revert_reserved σ0) = alloc.used σ0.
Proof.
  clear.
  rewrite /alloc.used /revert_reserved.
  rewrite map_filter_fmap /= dom_fmap_L.
  f_equal. apply map_filter_ext. intros i x. simpl. destruct x.
  - rewrite decide_False //; auto.
  - rewrite decide_True //; discriminate.
  - rewrite decide_False //; auto.
Qed.

Lemma alloc_crash_cond_crash_true d E :
  (∀ σ, ▷ P σ ={E}=∗ ▷ P (revert_reserved σ)) -∗
  alloc_crash_cond d false ={E}=∗ alloc_crash_cond d true.
Proof.
  clear.
  iIntros "H".
  iNamed 1.
  iMod ("H" with "HPalloc"). iModIntro. iExists _. iFrame.
  rewrite unused_revert_reserved. iFrame.
  iPureIntro; split.
  - apply alloc_post_crash_revert_reserved.
  - rewrite dom_revert_reserved. auto.
Qed.

Lemma alloc_crash_cond_no_later_crash_true d E :
  (∀ σ, P σ ={E}=∗ P (revert_reserved σ)) -∗
  alloc_crash_cond_no_later d false ={E}=∗ alloc_crash_cond_no_later d true.
Proof.
  clear.
  iIntros "H".
  iNamed 1.
  iMod ("H" with "HPalloc"). iModIntro. iExists _. iFrame.
  rewrite unused_revert_reserved. iFrame.
  iPureIntro; split.
  - apply alloc_post_crash_revert_reserved.
  - rewrite dom_revert_reserved. auto.
Qed.

(* TODO: this is a more general property about filter *)
Lemma dom_filter_unfree σ :
  dom (filter (λ x : u64 * block_status, x.2 ≠ block_free) σ) = alloc.domain σ ∖ alloc.free σ.
Proof.
  clear.
  apply dom_filter_L.
  intros i. rewrite /alloc.domain/alloc.free.
  set_unfold. split.
  * intros (Hi&Hnin).
    apply elem_of_dom in Hi. destruct Hi as [x Hin].
    exists x. split; eauto. intros Hin'. eapply Hnin.
    apply elem_of_filter_dom; eauto.
  * intros (x&Hi&Hneq). split.
    ** apply elem_of_dom; eauto.
    ** intros Hdom. apply elem_of_filter_dom in Hdom as (?&?&Hfree). simpl in Hfree. congruence.
Qed.

Theorem reserved_block_weaken γ k R R' :
  □ (R -∗ R') -∗
  □ (R' -∗ block_cinv γ k) -∗
  reserved_block γ k R -∗
  reserved_block γ k R'.
Proof.
  iIntros "#HR' #Hwand"; iNamed 1.
  iFrame. iApply (crash_borrow_conseq with "[] [] [] Hcrashinv"); eauto.
Qed.

Lemma free_big_sepS_to_all σ (Φ: u64 → iProp Σ):
  ([∗ set] k ∈ alloc.free σ, Φ k) ⊣⊢
  [∗ map] k↦v ∈ σ, match v with block_free => Φ k | _ => True end.
Proof.
  rewrite -big_opM_dom big_sepM_filter'.
  apply big_sepM_proper. intros ? []; eauto => //=;
  try (by rewrite decide_False);
  try (by rewrite decide_True).
Qed.

Lemma alloc_post_crash_big_sepM_split_free σ (Φ : u64 → _ → iProp Σ):
  alloc_post_crash σ →
  ([∗ map] k↦v ∈σ, Φ k v) -∗
  ([∗ set] k ∈ alloc.free σ, Φ k block_free) ∗
  ([∗ set] k ∈ (alloc.domain σ ∖ alloc.free σ), Φ k block_used).
Proof.
  iIntros (Hcrashed) "Hpts".
  iDestruct (big_sepM_filter_split _ (λ x, x.2 = block_free) with "Hpts") as "(Hfree&Hnfree)".
  iSplitL "Hfree".
  { iApply big_sepM_dom. iApply (big_sepM_mono with "Hfree").
    iIntros (?? Hlookup).
    apply map_lookup_filter_Some in Hlookup as (?&Heq). simpl in Heq. subst.
    eauto. }
  iAssert ([∗ map] k↦x ∈ filter (λ x : u64 * block_status, x.2 ≠ block_free) σ, Φ k block_used)%I
           with "[Hnfree]" as "Hused".
  { iApply (big_sepM_mono with "Hnfree").
    iIntros (?? Hfilter) "H".
    apply map_lookup_filter_Some in Hfilter as (?&Heq).
    simpl in Heq. destruct x; try iFrame; try congruence.
    exfalso. eapply alloc_post_crash_lookup_not_reserved; eauto.
  }
  iDestruct (big_sepM_dom with "Hused") as "Hused".
  rewrite dom_filter_unfree. eauto.
Qed.

Lemma free_block_init γ σ E :
  alloc_post_crash σ →
  pre_borrow -∗
  ([∗ set] k ∈ alloc.unused σ, Ψ k) -∗
  ([∗ map] k↦v ∈ σ, k ↪[alloc_status_name γ] v) -∗
  |={E}=> init_cancel (([∗ set] k ∈ alloc.free σ, k ↪[alloc_status_name γ] block_free) ∗
                       crash_borrow ([∗ set] k ∈ alloc.free σ, Ψ k)
                                    ([∗ set] k ∈ alloc.free σ, block_cinv γ k))
                      ([∗ set] k ∈ dom σ, block_cinv γ k).
Proof.
  clear.
  iIntros (Hcrashed) "Hpre Hfree Hpts".
  rewrite -?Hcrashed.
  iModIntro.
  iDestruct (crash_borrow_init_cancel ([∗ set] k ∈ alloc.free σ, Ψ k)
                                      ([∗ set] k ∈ alloc.free σ, block_cinv γ k) with "Hpre Hfree []") as "H".
  { iIntros "!>". iApply big_sepS_mono.
    iIntros (??) "H"; by iLeft. }

  assert (dom σ = (alloc.domain σ ∖ alloc.free σ) ∪ alloc.free σ) as ->.
  { rewrite /alloc.domain difference_union_L.
    apply alloc_post_crash_free_used in Hcrashed.
    set_solver. }
  iDestruct (alloc_post_crash_big_sepM_split_free with "Hpts") as "(Hfree&Hused)".
  { auto. }
  iApply (init_cancel_wand with "H [Hfree]").
  { iIntros "$". eauto. }
  iIntros "H".
  iApply big_sepS_union.
  { set_solver+. }
  iFrame. iApply (big_sepS_mono with "Hused").
  { iIntros (??) "H". by iRight. }
Qed.

Theorem is_allocator_alloc l σ :
  ([∗ set] k ∈ alloc.unused σ, Ψ k) -∗
  ▷ P σ -∗
  is_allocator_mem_pre l σ
  ={⊤}=∗ init_cancel (∃ γ, is_allocator l (alloc.domain σ) γ)
                     (alloc_crash_cond (alloc.domain σ) false).
Proof.
  clear Hitemcrash.
  iIntros "Hunused HP". iNamed 1.
  iMod (ghost_map_alloc σ) as (γheap) "(Hctx&Hpts)".
  iMod (ghost_var_alloc (alloc.free σ)) as (γfree) "(Hfree&Hfree_frag)".
  set (γ := {| alloc_status_name := γheap;
               alloc_free_name := γfree |}).

  iMod (ncinv_alloc Ninv _ (allocator_inv γ (alloc.domain σ)) with "[HP Hctx Hfree]") as "(#Hinv&Hallocinv)".
  { iNext. iExists _. iFrame. eauto. }

  iMod (free_block_init γ with "[$] [$] [$]") as "Hic"; first done.
  iModIntro.
  iApply (init_cancel_fupd ⊤).
  iApply (init_cancel_cfupd ⊤).
  iApply (init_cancel_wand with "Hic [Hfreemap Hfree_lock Hfree_frag]").
  { iIntros "Hblock".
    iMod (alloc_lock Nlock ⊤ _ (allocator_linv γ mref)%I
            with "[$Hfree_lock] [Hfreemap Hblock Hfree_frag]") as "#Hlock".
    { iExists _; iFrame. }
    iModIntro.
    iExists γ.
    rewrite /is_allocator.
    { iExists _, _; iFrame "#". }
  }
  iMod (own_disc_fupd_elim with "Hallocinv") as "Hallocinv".
  iIntros "Hpending HC".
  iModIntro.
  iMod (fupd_mask_subseteq (↑Ninv)) as "Hclo".
  { set_solver+. }
  iMod ("Hallocinv" with "[$]") as "Hallocinner".
  iDestruct "Hallocinner" as (?) "(>%Hdom&>Hstatus&>?&HP)".
  iNamed.
  iMod "Hclo".
  iModIntro.
  rewrite /alloc_crash_cond.

  iExists _. iFrame.
  fold (alloc.domain σ).
  rewrite /alloc.unused.
  rewrite -Hdom.
  iSplitR; first by auto.
  rewrite /alloc.free.
  rewrite -?big_sepM_dom ?big_sepM_filter'.
  iDestruct (big_sepM_mono_with_inv with "Hstatus Hpending") as "(_&$)".
  iIntros (k x Hlookup) "(Hctx&Hfree)".
  rewrite /free_block_pending.
  iDestruct "Hfree" as "[HΨ|Hused]".
  - iFrame. destruct (decide _); eauto.
  - iDestruct (ghost_map_lookup with "[$] Hused") as %Hlookup'.
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
  rewrite map_filter_insert_False //=.
  rewrite map_filter_delete dom_delete_L //.
Qed.

Theorem alloc_free_free σ new :
  alloc.free (<[new := block_free]> σ) =
  alloc.free σ ∪ {[new]}.
Proof.
  clear.
  rewrite /alloc.free /=.
  rewrite map_filter_insert_True //= dom_insert_L. set_solver.
Qed.

Theorem reserved_not_in_alloc_free σ a :
  σ !! a = Some block_reserved →
  a ∉ alloc.free σ.
Proof.
  clear.
  rewrite /alloc.free /= => Hlook.
  rewrite elem_of_dom. intros (x&(His&Heq)%map_lookup_filter_Some).
  simpl in Heq. rewrite Heq Hlook in His. congruence.
Qed.

Theorem alloc_free_subset σ :
  alloc.free σ ⊆ dom σ.
Proof. by apply dom_filter_subseteq. Qed.

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
  Opaque crash_borrow.

Theorem wp_Reserve (Q: option u64 → iProp Σ) l dset γ E1:
  ↑N ⊆ E1 →
  {{{ is_allocator l dset γ ∗
     (∀ σ σ' ma,
          ⌜match ma with
           | Some a => a ∈ alloc.free σ ∧ σ' = <[a := block_reserved]> σ
           | None => σ' = σ ∧ alloc.free σ = ∅
           end⌝ -∗
          ▷ P σ ={E1 ∖ ↑N}=∗ ▷ P σ' ∗ Q ma)
  }}}
    Allocator__Reserve #l @ E1
  {{{ a (ok: bool), RET (#a, #ok);
      if ok then Q (Some a) ∗ reserved_block γ a (Ψ a)
      else Q None }}}.
Proof.
  clear.
  iIntros (Hsub0 Φ) "(Hinv&Hfupd) HΦ". iNamed "Hinv".
  assert ((↑Nlock : coPset) ⊆ E1) as Hsub1.
  { solve_ndisj. }
  rewrite /Allocator__Reserve.

  wp_pures.
  iMod (readonly_load with "m") as (?) "m'".
  iMod (readonly_load with "free") as (?) "free'".



  wp_bind (lock.acquire _).
  wp_loadField.
  wp_apply (acquire_spec' with "His_lock"); first assumption.
  iIntros "(His_locked & Hinner)"; iNamed "Hinner".

  wp_loadField.
  wp_apply (wp_findKey with "Hfreemap").
  iIntros (k ok) "[%Hk Hfreemap]".


  wp_loadField.
  iDestruct "Hfreemap" as (m') "[Hfreemap %Hdom]".
  wp_apply (wp_MapDelete with "Hfreemap"); iIntros "Hfreemap".


  iAssert (is_addrset mref (freeset ∖ {[k]})) with "[Hfreemap]" as "Hfreemap".
  { iExists _; iFrame.
    iPureIntro.
    rewrite /map_del.
    rewrite dom_delete_L.
    set_solver. }


  do 2 wp_pure.
  (* Linearization point here. *)
  wp_bind (Skip).
  destruct ok.

  - (* extract block *)
    iApply (wp_crash_borrow_split _ _ _ _ _  (Ψ k) ([∗ set] k0 ∈ freeset ∖ {[k]} , Ψ k0)
                                             (block_cinv γ k) ([∗ set] k0 ∈ freeset ∖ {[k]} , block_cinv γ k0)
              with "Hborrows").
    { auto. }
    { iNext. rewrite big_sepS_delete; auto. }
    { iIntros "!> !> H". iLeft. auto. }
    { iIntros "!> !> H". iApply (big_sepS_mono with "H").
      iIntros. by iLeft. }
    {  rewrite -big_sepS_delete //. eauto. }
    iDestruct (big_sepS_delete _ _ k with "Hblocks") as "(Hmapsto&Hblocks)".
    { eassumption. }

    iInv "Halloc_inv" as "H" "Hclo".
    wp_pures.
    iNamed "H".

    iDestruct (ghost_var_agree with "Hfreeset_auth [$]") as %<-.
    iMod (fupd_mask_subseteq (E1 ∖ ↑N)) as "Hrestore_mask"; first solve_ndisj.
    iMod ("Hfupd" $! σ _ (Some k) with "[] [$]") as "(HP&HQ)".
    { iPureIntro; split; last by reflexivity. eauto. }
    iMod "Hrestore_mask" as "_".

    iMod (ghost_map_update block_reserved with "[$] Hmapsto") as "(Hctx&Hmapsto)".
    iCombine "Hfreeset_frag Hfreeset_auth" as "Hfreeset".
    iMod (ghost_var_update (alloc.free (<[k := block_reserved]>σ)) with "[$]")
         as "(Hfreeset_auth&Hfreeset_frag)".
    iMod ("Hclo" with "[HP Hfreeset_auth Hctx]").
    { iNext. iExists _. iFrame. iPureIntro.
      rewrite dom_insert_L.
      assert (k ∈ dom σ).
      { by apply alloc_free_subset. }
      set_solver.
    }
    iModIntro.
    iIntros "(Hborrow&Hborrows)".
    wp_loadField.
    wp_apply (release_spec' with "[Hfreeset_frag Hblocks Hborrows Hfreemap $His_locked $His_lock]");
      first assumption.
    { iExists _; iFrame.
      rewrite alloc_free_reserve. eauto.
    }
    wp_pures.
    iApply "HΦ"; iFrame.

    iFrame.
    { iExists _. eauto. }
  -
    iInv "Halloc_inv" as "H".
    wp_pures.
    iNamed "H".
    iDestruct (ghost_var_agree with "Hfreeset_auth [$]") as %<-.
    iMod (fupd_mask_subseteq (E1 ∖ ↑N)) as "Hrestore_mask"; first solve_ndisj.
    iMod ("Hfupd" $! σ _ None with "[] [$]") as "(HP&HQ)".
    { iPureIntro; split; first by reflexivity. congruence. }
    iMod "Hrestore_mask" as "_".

    iModIntro. iSplitL "HP Hfreeset_auth Hstatus".
    { iNext. iExists _. iFrame. iPureIntro. eauto. }

    wp_loadField.
    wp_apply (release_spec' with "[Hfreeset_frag Hblocks Hborrows Hfreemap $His_locked $His_lock]");
      first assumption.
    { iExists _; iFrame. rewrite Hk set_empty_difference. iFrame. }
    wp_pures.
    iApply "HΦ"; by iFrame.
Qed.

(* NOTE: we used to have a proof of this (with nearly the same proof script as
above). This spec supports using durable resources for the fupd, preserving them
on crash. We don't need this feature for our examples, though. *)
Theorem wpc_Reserve (Q: option u64 → iProp Σ) (Qc: iProp Σ) l dset γ E1 :
  ↑N ⊆ E1 →
  □ (∀ o, Q o -∗ Qc) -∗
  {{{ is_allocator l dset γ ∗
     (∀ σ σ' ma,
          ⌜match ma with
           | Some a => a ∈ alloc.free σ ∧ σ' = <[a := block_reserved]> σ
           | None => σ' = σ ∧ alloc.free σ = ∅
           end⌝ -∗
          ▷ P σ ={E1 ∖ ↑N}=∗ ▷ P σ' ∗ Q ma) ∧
      Qc
  }}}
    Allocator__Reserve #l @ E1
  {{{ a (ok: bool), RET (#a, #ok);
      if ok then Q (Some a) ∗ reserved_block γ a (Ψ a)
      else Q None }}}
  {{{ Qc }}}.
Proof.
  iIntros (?) "#HQc".
  iIntros "!>" (Φ Φc) "[Halloc Hfupd] HΦ".
Abort.

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

Lemma prepare_reserved_block_reuse R' R γ e a Φ Φc :
  language.to_val e = None →
  reserved_block γ a R -∗
   Φc ∧
  (R -∗
   reserved_block_in_prep γ a -∗
   WPC e @ ⊤ {{ λ v, (reserved_block γ a (R' v) -∗ Φc ∧ Φ v) ∗
                                           (R' v) ∗
                                           reserved_block_in_prep γ a ∗
                                           □ (R' v -∗ block_cinv γ a) }}
                                   {{ Φc ∗ block_cinv γ a }}) -∗
  WPC e @ ⊤ {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hreserved H".
  iNamed "Hreserved".
  iDestruct "Halloc_inv" as (?) "#Hinv".
  iApply (wpc_crash_borrow_open_modify _ _ _ with "Hcrashinv [H Hmapsto]"); try iFrame; auto.
  iSplit.
  - iDestruct "H" as "($&_)".
  - iIntros "HR". iDestruct "H" as "(_&H)".
    iSpecialize ("H" with "[$] [Hmapsto]").
    { iFrame. iExists _. eauto. }
    iApply (wpc_strong_mono with "H"); eauto.
    iSplit.
    * iIntros (?) "(Hclose&HR&Hprep&#Hcinv)". iModIntro. iFrame. iFrame "#".
      iFrame "HR".
      iIntros. iApply "Hclose". iSplitR "Hprep".
      ** by iFrame.
      ** eauto.
    * eauto.
Qed.

Lemma prepare_reserved_block E1 R γ e a Φ Φc :
  language.to_val e = None →
  reserved_block γ a R -∗
  Φc ∧
  (R -∗
   reserved_block_in_prep γ a -∗
   WPC e @ E1 {{ λ v, (Φc ∧ Φ v) ∗ block_cinv γ a }} {{ Φc ∗ block_cinv γ a }}) -∗
  WPC e @  E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hreserved H".
  iNamed "Hreserved".
  iDestruct "Halloc_inv" as (?) "#Hinv".
  iApply (wpc_crash_borrow_open_modify  _ _ with "[$] [H Hmapsto]"); try iFrame; auto.
  iSplit.
  - iDestruct "H" as "($&_)".
  - iIntros "HR". iDestruct "H" as "(_&H)".
    iSpecialize ("H" with "[$] [Hmapsto]").
    { iFrame. iExists _. eauto. }
    iApply (wpc_strong_mono with "H"); eauto.
    iSplit.
    * iIntros (?) "(Hclose&Hcinv)". iModIntro.
      iExists (block_cinv γ a). iFrame.
      iSplitL "".
      ** eauto.
      ** eauto.
    * eauto.
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
  dom (<[a := x']>σ) = dom σ.
Proof.
  intros Hlookup. rewrite dom_insert_L.
  cut (a ∈ dom σ).
  { set_solver+. }
  apply elem_of_dom; eauto.
Qed.

Lemma mark_used' E γ a Q:
  ↑Ninv ⊆ E →
   reserved_block_in_prep γ a -∗
   (∀ σ, ⌜ σ !! a = Some block_reserved ⌝ -∗
         ▷ P σ -∗ |NC={E ∖ ↑ N}=> ▷ P (<[a := block_used]> σ) ∗ Q)
   -∗ |NC={E}=> Q ∗ used_block γ a.
Proof.
  iIntros (?) "Hprep Hfupd".
  iNamed "Hprep".
  iDestruct "Halloc_inv" as (d) "#Hinv".
  iInv "Hinv" as "H" "Hclo".
  rewrite /allocator_inv.
  iDestruct "H" as (?) "(>Hdom&>Hstatus&>Hauth&HP)".
  iNamed "Hdom". iNamed "Hstatus". iNamed "Hauth".
  iDestruct (ghost_map_lookup with "[$] Hmapsto") as %Hlookup'.
  iMod (ncfupd_mask_subseteq (E ∖ ↑N)) as "Hrestore_mask"; first solve_ndisj.
  iMod ("Hfupd" with "[//] [$]") as "(HP&HQ)".
  iMod "Hrestore_mask" as "_".
  iMod (ghost_map_update block_used with "[$] Hmapsto") as "(Hctx&Hmapsto)".
  iMod ("Hclo" with "[HP Hctx Hfreeset_auth]").
  { iNext. iExists _. iFrame "HP Hctx".
    rewrite (dom_update_status σ a block_reserved) //=.
    iFrame "%".
    rewrite (free_mark_used_non_free) //=.
    intros Heq; subst; eauto. rewrite Heq in Hlookup'. congruence.
  }
  iModIntro. by iFrame.
Qed.

Lemma mark_used E γ a Q:
  ↑Ninv ⊆ E →
   reserved_block_in_prep γ a -∗
   (∀ σ, ⌜ σ !! a = Some block_reserved ⌝ -∗
         P σ -∗ |NC={E ∖ ↑ N}=> ▷ P (<[a := block_used]> σ) ∗ Q)
   -∗ |NC={E, E ∖ ↑Ninv}=> ▷ |NC={E ∖ ↑Ninv, E}=> Q ∗ used_block γ a.
Proof.
  iIntros (?) "Hprep Hfupd".
  iNamed "Hprep".
  iDestruct "Halloc_inv" as (d) "#Hinv".
  iInv "Hinv" as "H" "Hclo".
  iModIntro. iNext. iNamed "H".
  iDestruct (ghost_map_lookup with "[$] Hmapsto") as %Hlookup'.
  iMod (ncfupd_mask_subseteq (E ∖ ↑N)) as "Hrestore_mask"; first solve_ndisj.
  iMod ("Hfupd" with "[//] [$]") as "(HP&HQ)".
  iMod "Hrestore_mask" as "_".
  iMod (ghost_map_update block_used with "[$] Hmapsto") as "(Hctx&Hmapsto)".
  iMod ("Hclo" with "[HP Hctx Hfreeset_auth]").
  { iNext. iExists _. iFrame "HP Hctx".
    rewrite (dom_update_status σ a block_reserved) //=.
    iFrame "%".
    rewrite (free_mark_used_non_free) //=.
    intros Heq; subst; eauto. rewrite Heq in Hlookup'. congruence.
  }
  iModIntro. by iFrame.
Qed.

(*
Lemma gset_difference_difference `{Countable K} (A B C: gset K) :
  C ⊆ A →
  A ∖ (B ∖ C) = A ∖ B ∪ C.
Proof using.
  clear.
  intros.
  apply set_eq; intros k.
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
  ghost_map_auth (γ.(alloc_status_name)) 1 (gset_to_gmap () used) -∗
  alloc_used γ a -∗
  ⌜a ∈ used⌝.
Proof.
  rewrite /alloc_used.
  iIntros "Hctx Hused".
  iDestruct (ghost_map_lookup with "Hctx Hused") as %Hlookup.
  iPureIntro.
  apply lookup_gset_to_gmap_Some in Hlookup as [? _]; auto.
Qed.
*)

(** XXX: should probably make this a WPC in case the fupd requires a durable resource *)
Theorem wp_Free (Q: iProp Σ) E l d γ (a: u64) :
  ↑N ⊆ E →
  {{{ is_allocator l d γ ∗ reserved_block γ a (Ψ a) ∗
     (∀ σ, ⌜ σ !! a = Some block_reserved ⌝ -∗ ▷ P σ -∗ |NC={E ∖↑N}=> ▷ P (<[ a := block_free ]> σ) ∗ Q)
  }}}
    Allocator__Free #l #a @ E
  {{{ RET #(); Q }}}.
Proof.
  clear Hitemcrash.
  iIntros (Hsub1 Φ) "(Halloc&Hreserved&Hfupd) HΦ".
  iNamed "Halloc".
  assert (↑Nlock ⊆ E) as Hsub2 by solve_ndisj.
  iMod (readonly_load with "m") as (?) "m'".
  iMod (readonly_load with "free") as (?) "free'".
  wp_rec. wp_pures.
  wp_loadField.
  wp_apply (acquire_spec' with "His_lock").
  { auto. }
  iIntros "(Hlocked&Hinv)"; iNamed "Hinv".
  wp_loadField.
  iDestruct "Hfreemap" as (m) "[Hfreemap %Hdom]".
  wp_apply (wp_MapInsert _ _ () with "Hfreemap"); first by auto.
  iIntros "Hfreemap".
  do 2 wp_pure.
  wp_bind (Skip).

  iInv "Halloc_inv" as "H" "Hclo".
  wp_pure.
  iNamed "H".
  (* TODO: iNamed doesn't work because reserved_block re-uses the name
  Halloc_inv from is_allocator *)
  iDestruct "Hreserved" as "(Hcrashinv&Hmapsto&Halloc_inv_block)".
  iDestruct (ghost_var_agree with "Hfreeset_auth [$]") as %<-.
  iDestruct (ghost_map_lookup with "[$] Hmapsto") as %Hlookup'.
  iMod (ghost_map_update block_free with "[$] Hmapsto") as "(Hctx&Hmapsto)".
  iCombine "Hfreeset_auth Hfreeset_frag" as "Hfreeset".
  iMod (ghost_var_update (alloc.free (<[a := block_free]>σ)) with "[$]")
    as "(Hfreeset_auth&Hfreeset_frag)".
  iMod (fupd_mask_subseteq (E ∖ ↑N)) as "Hrestore_mask"; first solve_ndisj.
  iMod ("Hfupd" $! σ with "[%//] HP") as "[HP HQ]".
  iMod "Hrestore_mask" as "_".
  iMod ("Hclo" with "[HP Hctx Hfreeset_auth]") as "_".
  { iNext. iExists _. iFrame. erewrite dom_update_status; eauto. }
  iModIntro. wp_pures.
  iAssert (is_addrset mref (alloc.free (<[a := block_free]>σ))) with "[Hfreemap]" as "Hfreemap".
  { iExists _; iFrame.
    iPureIntro.
    rewrite /map_insert dom_insert_L alloc_free_free.
    set_solver. }
  wp_bind (struct.loadF _ _ _).
  iApply (wp_crash_borrow_combine _ _ _
                                ([∗ set] k0 ∈ alloc.free (<[a := block_free]> σ), Ψ k0)%I
                                ([∗ set] k0 ∈ alloc.free (<[a := block_free]> σ), block_cinv γ k0)%I
            with "Hcrashinv Hborrows").
  { auto. }
  { iNext. iModIntro. iApply big_sepS_mono. iIntros (??) "H"; by iLeft. }
  { iNext.
    rewrite alloc_free_free. rewrite big_sepS_union; last first.
    { apply disjoint_singleton_r; auto. by apply reserved_not_in_alloc_free. }
    rewrite big_opS_singleton.
    iIntros "($&$)". }
  { iNext.
    rewrite alloc_free_free. rewrite big_sepS_union; last first.
    { apply disjoint_singleton_r; auto. by apply reserved_not_in_alloc_free. }
    rewrite big_opS_singleton.
    iIntros "($&$)". eauto. }
  wp_loadField.
  iIntros "Hborrows".
  wp_apply (release_spec' with "[$His_lock $Hlocked Hmapsto Hfreemap Hfreeset_frag Hblocks Hborrows]").
  { auto. }
  {
    iExists _. iFrame. 
    rewrite alloc_free_free.
    rewrite big_sepS_union; last first.
    { apply disjoint_singleton_r; auto. by apply reserved_not_in_alloc_free. }
    rewrite big_opS_singleton.
    iFrame.
  }
  wp_pures.
  iApply ("HΦ" with "[$]").
Qed.

End goose.

Section goose.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.
Context `{!heapGS Σ}.
Context `{!allocG Σ}.

Context (P: heapGS Σ → alloc.t → iProp Σ).
Context (Ψ: heapGS Σ → u64 → iProp Σ).

Instance allocator_crash_cond_stable d b :
  (∀ x, IntoCrash (▷ P _ x) (λ hG, ▷ P hG x)%I) →
  (∀ x, IntoCrash (Ψ _ x) (λ hG, Ψ hG x)) →
  IntoCrash (alloc_crash_cond (P _) (Ψ _) d b) (λ hG, alloc_crash_cond (P hG) (Ψ hG) d b).
Proof.
  intros.
  hnf; iNamed 1.
  iCrash.
  iExists _. iFrame. eauto.
Qed.

Instance allocator_crash_cond_no_later_stable d b :
  (∀ x, IntoCrash (P _ x) (λ hG, P hG x)%I) →
  (∀ x, IntoCrash (Ψ _ x) (λ hG, Ψ hG x)) →
  IntoCrash (alloc_crash_cond_no_later (P _) (Ψ _) d b) (λ hG, alloc_crash_cond_no_later (P hG) (Ψ hG) d b).
Proof.
  intros.
  hnf; iNamed 1.
  iCrash.
  iExists _. iFrame. eauto.
Qed.

End goose.
