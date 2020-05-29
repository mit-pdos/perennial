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

Class allocG Σ :=
  { alloc_used_preG :> gen_heapPreG u64 block_status Σ; }.

(* state representation types (defined here since modules can't be in sections) *)
Module alloc.
  Definition t := gmap u64 block_status.

  Definition free (σ: t) : gset u64 := dom (gset u64) (filter (λ x, x.2 = block_free) σ).
  Definition used (σ: t) : gset u64 := dom (gset u64) (filter (λ x, x.2 = block_used) σ).
  Definition unused (σ: t) : gset u64 := dom (gset u64) (filter (λ x, x.2 ≠ block_used) σ).

  Global Instance _witness : Inhabited t.
  Proof. econstructor. apply (∅: gmap u64 block_status). Defined.

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

Section goose.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!allocG Σ}.
Context `{!crashG Σ}.
Context `{!stagedG Σ}.

Let allocN := nroot.@"allocator".

Record alloc_names :=
  { alloc_used_name: gen_heapG u64 block_status Σ; }.

Instance alloc_names_eta : Settable _ := settable! Build_alloc_names <alloc_used_name>.

Implicit Types (a: u64) (m: gmap u64 ()) (free: gset u64).

Context (SIZE: nat).
Context (MAX: nat).
Context (P: alloc.t → iProp Σ).
Context (Ψ: u64 → iProp Σ).
Context (N: namespace).
Implicit Types (l:loc) (γ:alloc_names) (σ: alloc.t).


Definition Ncrash := N.@"crash".

(* crash_inv: either exists Ψ, etc. or block *)
Definition free_block_cinv γ addr : iProp Σ :=
  Ψ addr ∨ mapsto (hG := alloc_used_name γ) addr 1 block_used.

Definition free_block γ k : iProp Σ :=
  "Hcrashinv" ∷ (∃ Γ i, na_crash_bundle Γ Ncrash (LVL MAX) (Ψ k) i ∗ na_crash_val Γ (free_block_cinv γ k) i) ∗
  "Hmapsto" ∷ (mapsto (hG := alloc_used_name γ) k 1 block_free).

Definition free_block_pending γ k : iProp Σ :=
  (∃ Γ, na_crash_pending Γ Ncrash (LVL MAX) (free_block_cinv γ k)).

(*
Definition block_status_interp γ k st : iProp Σ :=
  match st with
  | block_free => free_block γ k
  | block_used => True
  | block_reserved => True
  end.
*)

Definition allocator_linv γ (mref: loc) : iProp Σ :=
 ∃ (freeset: gset u64),
  "Hfreemap" ∷ is_addrset mref (freeset) ∗
  "Hblocks" ∷ [∗ set] k ∈ freeset, free_block γ k
.

Definition allocator_inv γ : iProp Σ :=
  ∃ σ,
    "Hstatus" ∷ gen_heap_ctx (hG:=γ.(alloc_used_name)) σ ∗
    "HP" ∷ P σ.

Definition is_allocator (l: loc) γ : iProp Σ :=
  ∃ (lref mref: loc) (γlk: gname),
    "#m" ∷ readonly (l ↦[Allocator.S :: "m"] #lref) ∗
    "#free" ∷ readonly (l ↦[Allocator.S :: "free"] #mref) ∗
    "#His_lock" ∷ is_lock allocN γlk #lref (allocator_linv γ mref) ∗
    "#Halloc_inv" ∷ inv N (allocator_inv γ)
.

Definition is_allocator_pre γ freeset : iProp Σ :=
  "#Halloc_inv" ∷ inv N (allocator_inv γ) ∗
  "Hblocks" ∷ [∗ set] k ∈ freeset, free_block γ k.

Context {Hitemcrash: ∀ x, IntoCrash (Ψ x) (λ _, Ψ x)}.
(*
Instance allocator_post_crash γ mref σ :
  IntoCrash (allocator_linv γ mref σ) (λ _, allocator_durable σ).
Proof.
  hnf; iNamed 1.
  by iFrame.
Qed.
*)

Global Instance is_allocator_Persistent l γ :
  Persistent (is_allocator l γ).
Proof. apply _. Qed.

Definition alloc_crash_cond : iProp Σ :=
  ∃ σ, P σ ∗ [∗ set] k ∈ alloc.unused σ, Ψ k.

(*
Lemma mapsto_pts_to_free:
  [∗ map] i↦v ∈ σ, mapsto i 1 v -∗
  [∗ map] i↦v ∈ alloc.free σ, mapsto i 1 v -∗
*)
Set Nested Proofs Allowed.

Lemma free_big_sepS_to_all σ (Φ: u64 → iProp Σ):
  ([∗ set] k ∈ alloc.free σ, Φ k) ⊣⊢
  [∗ map] k↦v ∈ σ, match v with block_free => Φ k | _ => True end.
Proof.
  rewrite -big_opM_dom big_sepM_filter.
  apply big_sepM_proper. intros ? []; eauto => //=;
  try (by rewrite decide_False);
  try (by rewrite decide_True).
Qed.

Lemma free_block_init γ σ E:
  ↑Ncrash ⊆ E →
  alloc_post_crash σ →
  ([∗ set] k ∈ alloc.unused σ, Ψ k) -∗
  ([∗ map] k↦v ∈ σ, mapsto (hG := alloc_used_name γ) k 1 v) -∗
  |={E}=> ([∗ set] k ∈ dom (gset _) σ, free_block_pending γ k) ∗
          ([∗ set] k ∈ alloc.free σ, free_block γ k).
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
    iMod (na_crash_inv_init Ncrash (LVL MAX) E) as (Γ) "H".
    iMod (na_crash_inv_alloc _ _ _ _ (free_block_cinv γ k) (Ψ k) with "[$] [$] []") as
        (i) "(Hbund&Hval&Hpend)".
    { auto. }
    { iAlways. iIntros "H". iLeft. eauto. }
    iModIntro. iFrame. rewrite /free_block_pending.
    iSplitL "Hpend".
    { iExists _. iFrame. }
    iExists _, _. iFrame.
  - exfalso. eapply alloc_post_crash_lookup_not_reserved; eauto.
  - (* TODO: should they all be in the same na_crash_inv? *)
    iMod (na_crash_inv_init Ncrash (LVL MAX) E) as (Γ) "H".
    iMod (na_crash_inv_alloc _ _ _ _ (free_block_cinv γ k) (mapsto k 1 block_used) with "[$] [$] []") as
        (i) "(Hbund&Hval&Hpend)".
    { auto. }
    { iAlways. iIntros "H". iRight. eauto. }
    iModIntro. iFrame.
    iExists _. iFrame.
Qed.

Lemma allocator_crash_obligation e (Φ: val → iProp Σ) Φc Φc' E2 E2' k σ:
  E2 ⊆ E2' →
  ↑N ⊆ E2' ∖ E2 →
  alloc_post_crash σ →
  ([∗ set] k ∈ alloc.unused σ, Ψ k) -∗
  P σ -∗
  □ (alloc_crash_cond -∗ Φc -∗ Φc') -∗
  (∀ γ, is_allocator_pre γ (alloc.free σ) -∗ WPC e @ NotStuck; LVL k; ⊤; E2 {{ Φ }} {{ Φc }}) -∗
  |={⊤}=> WPC e @ NotStuck; (LVL (k + set_size (alloc.unused σ))); ⊤; E2' {{ Φ }} {{ Φc' }}%I.
Proof.
  iIntros (?? Hcrash) "Hstate HP #Hcrash1 HWP".
  iMod (gen_heap_strong_init σ) as (γheap Hpf) "(Hctx&Hpts)".
  set (γ := {| alloc_used_name := γheap |}).
  iMod (inv_alloc N _ (allocator_inv γ) with "[HP Hctx]") as "#Hinv".
  { iNext. iExists _. iFrame. }
  iMod (free_block_init γ with "[$] [$]").
  { set_solver+. }
  { eauto. }
Abort.


(* TODO: prove something useful for initializing from zero blocks *)


Theorem wp_newAllocator mref (start sz: u64) used :
  int.val start + int.val sz < 2^64 →
  {{{ is_addrset mref used ∗
      let σ0 := {| alloc.domain := rangeSet (int.val start) (int.val sz);
                   alloc.reserved := ∅;
                   alloc.used := used |} in
      ⌜alloc.wf σ0⌝ ∗ allocator_durable σ0 ∗ P σ0 }}}
    New #start #sz #mref
  {{{ l γ, RET #l; is_allocator l γ }}}.
Proof using allocG0.
  iIntros (Hoverflow Φ) "(Hused&%Hwf&Hblocks&HP) HΦ".
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
  iMod (gen_heap_init (gset_to_gmap () used)) as (γ2) "Husedctx".
  set (γ:={| alloc_lock_name := γ1; alloc_used_name := γ2 |}).
  iMod (alloc_lock allocN ⊤ _ _
                   (∃ σ, "Hlockinv" ∷ allocator_linv γ mref' σ ∗ "HP" ∷ P σ)%I
          with "[$Hlock] [-HΦ]") as "#Hlock".
  { iExists _; iFrame.
    rewrite /alloc.free /= difference_empty_L.
    iFrame "% ∗".
  }
  iModIntro.
  iApply ("HΦ" $! _ γ).
  iExists _, _; iFrame "#".
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
  alloc.free (set alloc.reserved (union new) σ) =
  alloc.free σ ∖ new.
Proof.
  clear.
  rewrite /alloc.free /=.
  set_solver.
Qed.

Theorem alloc_free_use σ new :
  alloc.free (set alloc.used (union new) σ) =
  alloc.free σ ∖ new.
Proof.
  clear.
  rewrite /alloc.free /=.
  set_solver.
Qed.

Theorem wp_Reserve (Q: option u64 → iProp Σ) l γ :
  {{{ is_allocator l γ ∗
     (∀ σ σ' ma,
          ⌜match ma with
           | Some a => a ∈ alloc.free σ ∧ σ' = set alloc.reserved ({[a]} ∪.) σ
           | None => σ' = σ
           end⌝ -∗
           ⌜alloc.wf σ⌝ -∗
          P σ ={⊤}=∗ P σ' ∗ Q ma)
  }}}
    Allocator__Reserve #l
  {{{ a (ok: bool), RET (#a, #ok);
      if ok then Q (Some a) ∗ Ψ a ∗ alloc_used γ a
      else Q None }}}.
Proof.
  clear.
  iIntros (Φ) "(Hinv&Hfupd) HΦ"; iNamed "Hinv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "His_lock").
  iIntros "(His_locked & Hinner)"; iNamed "Hinner".
  iNamed "Hlockinv".
  wp_loadField.
  wp_apply (wp_findKey with "Hfreemap").
  iIntros (k ok) "[%Hk Hfreemap]".
  wp_pures.
  wp_loadField.
  iDestruct "Hfreemap" as (m') "[Hfreemap %Hdom]".
  wp_apply (wp_MapDelete with "Hfreemap"); iIntros "Hfreemap".
  iAssert (is_addrset mref (alloc.free σ ∖ {[k]})) with "[Hfreemap]" as "Hfreemap".
  { iExists _; iFrame.
    iPureIntro.
    rewrite /map_del.
    rewrite dom_delete_L.
    set_solver. }
  iMod ("Hfupd" $! _ (if ok then _ else _) (if ok then Some k else None) with "[] [%//] HP") as "[HP HQ]".
  { destruct ok; simpl; auto. }
  wp_loadField.
  destruct ok.

  - (* extract block *)
    iNamed "Hdurable".
    iDestruct (big_sepS_delete with "Hblocks") as "[Hbk Hblocks]"; eauto.

    iMod (gen_heap_alloc _ k () with "Hallocated") as "[Hallocated His_used]".
    { apply lookup_gset_to_gmap_None.
      rewrite /alloc.free in Hk; set_solver. }

    wp_apply (release_spec with "[-HΦ HQ Hbk His_used $His_lock $His_locked]").
    { iExists _; iFrame.
      assert (alloc.wf (set alloc.reserved ({[k]} ∪.) σ)) as Hwf''.
      { rewrite /alloc.wf in Hwf |- *; set_solver. }
      iFrame "%".
      iSplitL "Hfreemap".
      - rewrite alloc_free_reserve; iFrame.
      - iSplitL "Hblocks".
        { rewrite alloc_free_reserve; iFrame. }
        simpl.
        rewrite -gset_to_gmap_union_singleton //. }
    wp_pures.
    iApply "HΦ"; iFrame.
  - wp_apply (release_spec with "[-HΦ HQ $His_lock $His_locked]").
    { iExists _; iFrame "∗ %".
      iExactEq "Hfreemap"; rewrite /named.
      f_equal.
      set_solver. }
    wp_pures.
    iApply "HΦ"; iFrame.
Qed.

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
  gen_heap_ctx (hG:=γ.(alloc_used_name)) (gset_to_gmap () used) -∗
  alloc_used γ a -∗
  ⌜a ∈ used⌝.
Proof.
  rewrite /alloc_used.
  iIntros "Hctx Hused".
  iDestruct (gen_heap_valid with "Hctx Hused") as %Hlookup.
  iPureIntro.
  apply lookup_gset_to_gmap_Some in Hlookup as [? _]; auto.
Qed.

(* TODO: upstream: https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/162 *)
Lemma gset_to_gmap_difference_singleton `{Countable K} {A} (x : A) i (Y: gset K) :
  gset_to_gmap x (Y ∖ {[i]}) = delete i (gset_to_gmap x Y).
Proof.
  apply map_eq; intros j; apply option_eq; intros y.
  rewrite lookup_delete_Some !lookup_gset_to_gmap_Some elem_of_difference
    elem_of_singleton; destruct (decide (i = j)); intuition.
Qed.

Theorem wp_Free (Q: iProp Σ) l γ (a: u64) :
  {{{ is_allocator l γ ∗ Ψ a ∗ alloc_used γ a ∗
     (∀ σ σ',
          ⌜σ' = set alloc.used (λ used, used ∖ {[a]}) σ⌝ -∗
          ⌜alloc.wf σ⌝ -∗
          P σ ={⊤}=∗ P σ' ∗ Q)
  }}}
    Allocator__Free #l #a
  {{{ RET #(); Q }}}.
Proof.
  clear Hitemcrash.
  iIntros (Φ) "(Halloc&Hb&Hused&Hfupd) HΦ"; iNamed "Halloc".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "His_lock").
  iIntros "(Hlocked&Hinv)"; iNamed "Hinv".
  iNamed "Hlockinv".
  wp_loadField.
  iDestruct "Hfreemap" as (m) "[Hfreemap %Hdom]".
  wp_apply (wp_MapInsert _ _ _ _ () with "Hfreemap"); first by auto.
  iIntros "Hfreemap".
  iAssert (is_addrset mref (alloc.free σ ∪ {[a]})) with "[Hfreemap]" as "Hfreemap".
  { iExists _; iFrame.
    iPureIntro.
    rewrite /map_insert dom_insert_L.
    set_solver. }
  wp_loadField.
  iMod ("Hfupd" $! σ with "[] [%//] HP") as "[HP HQ]".
  { iPureIntro.
    eauto. }
  iDestruct (alloc_used_valid with "Hallocated Hused") as %Hused.
  assert (a ∉ alloc.free σ) by set_solver.
  assert (a ∈ σ.(alloc.domain)) by set_solver.
  assert (alloc.wf (set alloc.used (λ used : gset u64, used ∖ {[a]}) σ)) as Hwf''.
  { set_solver. }
  iMod (gen_heap_delete with "[$Hallocated $Hused]") as "Hallocated".
  wp_apply (release_spec with "[$His_lock $Hlocked Hb Hdurable Hfreemap Hallocated HP]").
  { iNamed "Hdurable".
    iExists _; iFrame "HP".
    iFrame "%".
    rewrite alloc_free_free; last first.
    { apply elem_of_subseteq_singleton; auto. }
    iFrame "Hfreemap".
    rewrite big_sepS_union; last first.
    { apply disjoint_singleton_r; auto. }
    rewrite big_opS_singleton.
    iFrame "Hb Hblocks".
    iExactEq "Hallocated".
    rewrite /named.
    f_equal.
    simpl.
    rewrite -gset_to_gmap_difference_singleton //.
  }
  iApply ("HΦ" with "[$]").
Qed.

End goose.
