From iris.algebra Require Import auth frac agree gmap excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export language.
From iris.program_logic Require Import lifting.
From Perennial.algebra Require Export frac_count.
From Perennial.Helpers Require Export Transitions.
From Perennial.program_logic Require Export spec_assert language_ctx.
From Perennial.goose_lang Require Export lang.
From Perennial.goose_lang Require Import tactics notation lifting.

Set Default Proof Using "Type".

(* Wrapper around ffi_models and so on to avoid clashes between the ffi for
   the spec and the concrete *)

Class spec_ffi_model := { spec_ffi_model_field : ffi_model }.
Class spec_ext_op := { spec_ext_op_field : ext_op }.
Class spec_ext_semantics (H1: spec_ext_op) (H2: spec_ffi_model) :=
  { spec_ext_semantics_field : ext_semantics (spec_ext_op_field) (spec_ffi_model_field) }.
Class spec_ffi_interp (spec_ffi: spec_ffi_model) :=
  { spec_ffi_interp_field : ffi_interp (spec_ffi_model_field) }.

Section go_refinement.
Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{!spec_ffi_interp spec_ffi}.

Canonical Structure spec_lang : language :=
  @goose_lang (spec_ext_op_field) (spec_ffi_model_field) (spec_ext_semantics_field).
Canonical Structure spec_crash_lang : crash_semantics spec_lang :=
  @goose_crash_lang (spec_ext_op_field) (spec_ffi_model_field) (spec_ext_semantics_field).

Existing Instance spec_ffi_interp_field.
Existing Instance spec_ext_semantics_field.
Existing Instance spec_ext_op_field.
Existing Instance spec_ffi_model_field.


Class refinement_heapG Σ := refinement_HeapG {
  refinement_spec_ffiG : ffiG Σ;
  refinement_traceG :> traceG Σ;
  refinement_cfgG :> @cfgG spec_lang Σ;
  refinement_na_heapG :> na_heapG loc (@val spec_ext_op_field) Σ;
  refinement_frac_countG :> frac_countG Σ;
  refinement_crash_name : gname;
  (* TODO: do we need prophecies at the spec level? *)
  (*
  refinement_proph_mapG :> proph_mapG proph_id (val * val) Σ;
   *)
}.

Section go_spec_definitions.
Context {Σ: gFunctors}.
Context {hR: refinement_heapG Σ}.
Context `{invG Σ}.
Context `{crashG Σ}.

Definition refinement_ctok := staged_pending 1 (refinement_crash_name).

Definition spec_interp σ : iProp Σ :=
    (na_heap_ctx tls σ.(heap) ∗ (* proph_map_ctx κs σ.(used_proph_id) ∗ *) ffi_ctx refinement_spec_ffiG σ.(world)
      ∗ trace_auth σ.(trace) ∗ oracle_auth σ.(oracle) ∗ ⌜ null_non_alloc σ.(heap) ⌝ ∗ refinement_ctok)%I.

Definition spec_stateN := nroot .@ "source".@  "state".

(* TODO: these names are terrible *)
Definition spec_ctx : iProp Σ :=
  source_ctx (CS := spec_crash_lang) ∗ ncinv spec_stateN (∃ σ, source_state σ ∗ spec_interp σ)%I.
Definition spec_ctx' r ρ : iProp Σ :=
  source_ctx' (CS := spec_crash_lang) r ρ ∗ ncinv spec_stateN (∃ σ, source_state σ ∗ spec_interp σ)%I.

Definition spec_crash_ctx P : iProp Σ :=
  source_crash_ctx (CS := spec_crash_lang) refinement_ctok ∗
  □ (|C={↑spec_stateN}_0=> inv spec_stateN (P ∨ (∃ σ, source_state σ ∗ spec_interp σ)))%I.

Definition spec_crash_ctx' r ρ P : iProp Σ :=
  source_crash_ctx' (CS := spec_crash_lang) r ρ refinement_ctok ∗
  □ (|C={↑spec_stateN}_0=> inv spec_stateN (P ∨ (∃ σ, source_state σ ∗ spec_interp σ)))%I.

Global Instance spec_ctx_persistent : Persistent (spec_ctx).
Proof. apply _. Qed.

Global Instance spec_crash_ctx_persistent P : Persistent (spec_crash_ctx P).
Proof. apply _. Qed.

(** Override the notations so that scopes and coercions work out *)
Notation "l s↦{ q } v" := (heap_mapsto (hG := refinement_na_heapG) l q v%V)
  (at level 20, q at level 50, format "l  s↦{ q }  v") : bi_scope.
Notation "l s↦ v" :=
  (heap_mapsto (hG := refinement_na_heapG) l 1 v%V) (at level 20) : bi_scope.
Notation "l s↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  s↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Section go_ghost_step.

Lemma sN_inv_sub_minus_state E:
  nclose sN ⊆ E →
  nclose sN_inv ⊆ E ∖ ↑spec_stateN.
Proof.
  rewrite /sN_inv/sN/spec_stateN. intros Hsub.
  assert (nclose (nroot.@"source".@"base") ##
                 ↑nroot.@"source".@"state").
  { solve_ndisj. }
  assert (nclose (nroot.@"source".@"base") ⊆ E).
  { etransitivity; last eassumption. apply nclose_subseteq. }
  set_solver.
Qed.

Lemma spec_interp_null σ l:
  addr_base l = null →
  ▷ spec_interp σ -∗
  ▷ ⌜ heap σ !! l = None ⌝.
Proof.
  iIntros (Hl) "Hinterp !>".
  iDestruct "Hinterp" as "(_&_&?&?&H&_)".
  iDestruct "H" as %Hnonnull. iPureIntro.
  rewrite (addr_plus_off_decode l) Hl. eapply Hnonnull.
Qed.

Hint Resolve sN_inv_sub_minus_state : core.

Lemma ghost_output j K `{LanguageCtx _ K} E tr lit :
  nclose spec_stateN ⊆ E →
  nclose sN_inv ⊆ E →
  spec_ctx -∗
  trace_frag tr -∗
  j ⤇ K (Output (LitV lit)) -∗ |NC={E}=>
  j ⤇ K (LitV LitUnit) ∗ trace_frag (add_event (Out_ev lit) tr).
Proof.
  iIntros (??) "(#Hctx&#Hstate) Htr_frag Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&?&>Htr_auth&?)".
  iDestruct (trace_agree with "[$] [$]") as %?; subst.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { eapply head_prim_step_trans.
    rewrite /= /head_step /=.
    repeat (monad_simpl; simpl).
  }
  { solve_ndisj. }
  iMod (trace_update with "[$] [$]") as "(?&Htr_frag)".
  iMod ("Hclo" with "[-Hj Htr_frag]").
  { iNext. iExists _. iFrame. rewrite //=. }
  iFrame. eauto.
Qed.

Lemma ghost_input j K `{LanguageCtx _ K} E tr (sel: u64) Or :
  nclose spec_stateN ⊆ E →
  nclose sN_inv ⊆ E →
  spec_ctx -∗
  trace_frag tr -∗
  oracle_frag Or -∗
  j ⤇ K (Input (LitV (LitInt sel))) -∗ |NC={E}=>
  j ⤇ K (LitV (LitInt (Or tr sel))) ∗ trace_frag (add_event (In_ev sel (LitInt (Or tr sel))) tr) ∗
  oracle_frag Or.
Proof.
  iIntros (??) "(#Hctx&#Hstate) Htr_frag Hor_frag Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&?&>Htr_auth&>Hor_auth&?)".
  iDestruct (trace_agree with "[$] [$]") as %?; subst.
  iDestruct (oracle_agree with "[$] [$]") as %?; subst.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { eapply head_prim_step_trans.
    rewrite /= /head_step /=.
    repeat (monad_simpl; simpl).
  }
  { solve_ndisj. }
  iMod (trace_update with "[$] [$]") as "(?&Htr_frag)".
  iMod ("Hclo" with "[-Hj Htr_frag Hor_frag]").
  { iNext. iExists _. iFrame. rewrite //=. }
  iFrame. eauto.
Qed.

Lemma head_irreducible_not_atomically e σ :
  (∀ el e'', e ≠ Atomically el e'') →
  (∀ κ e' σ' efs, head_step e σ κ e' σ' efs → False) →
  head_irreducible e σ.
Proof.
  intros ? Hno_step.
  intros ???? Hstep%head_step_atomic_inv; [ | done ].
  eauto.
Qed.

Ltac head_irreducible :=
  apply head_irreducible_not_atomically;
  [ by inversion 1
  | rewrite /head_step /=; intros ???? Hstep;
    repeat match goal with
           | _ => progress (monad_inv; simpl in * )
           | H: context[unwrap ?mx], Hnone: ?mx = None |- _ =>
             rewrite -> Hnone in H; simpl in H
           end;
    auto
  ].

Lemma ghost_load_block_oob_stuck j K `{LanguageCtx _ K} E l n
  (Hoff: (addr_offset l < 0 ∨ n <= addr_offset l)%Z):
  nclose sN ⊆ E →
  spec_ctx -∗
  na_block_size (addr_base l) n →
  j ⤇ K (Load (Val $ LitV $ LitLoc l)) -∗ |NC={E}=> False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_block_size_oob_lookup with "Hσ Hl") as %Hnone; auto.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    subst. eauto.
  }
  solve_ndisj.
Qed.

Lemma ghost_load_write_stuck j K `{LanguageCtx _ K} E l q (v: val):
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st (WSt) l q v -∗
  j ⤇ K (Load (Val $ LitV $ LitLoc l)) -∗ |NC={E}=> False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_heap_write_lookup with "Hσ Hl") as %([]&?&Hlock); try inversion Hlock; subst.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    subst. eauto.
  }
  solve_ndisj.
Qed.

Lemma ghost_load_null_stuck j K `{LanguageCtx _ K} E l:
  addr_base l = null →
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (Load (Val $ LitV $ LitLoc l)) -∗ |NC={E}=> False.
Proof.
  iIntros (Hnull ?) "(#Hctx&#Hstate) Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct (spec_interp_null _ l with "Hinterp") as ">Hnone"; eauto.
  iDestruct "Hnone" as %Hnone.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    subst. eauto.
  }
  solve_ndisj.
Qed.

Lemma ghost_load_rd j K `{LanguageCtx _ K} E n l q (v: val):
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st (RSt n) l q v -∗
  j ⤇ K (Load (Val $ LitV $ LitLoc l)) -∗ |NC={E}=>
  na_heap_mapsto_st (RSt n) l q v ∗ j ⤇ K v.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_heap_read' with "Hσ Hl") as %([]&?&?&Hlock&Hle); try inversion Hlock; subst.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { eapply head_prim_step_trans.
    rewrite /= /head_step /=.
    repeat (monad_simpl; simpl).
  }
  { eauto. }
  iMod ("Hclo" with "[Hσ H Hrest]").
  { iNext. iExists _. iFrame. }
  iFrame. eauto.
Qed.

Lemma ghost_load j K `{LanguageCtx _ K} E l q v:
  nclose sN ⊆ E →
  spec_ctx -∗
  l s↦{q} v -∗
  j ⤇ K (Load (Val $ LitV $ LitLoc l)) -∗ |NC={E}=>
  l s↦{q} v ∗ j ⤇ K v.
Proof.
  iIntros (?) "Hspec Hl0 Hj".
  iDestruct (heap_mapsto_na_acc with "Hl0") as "(Hl&Hclo_l)".
  rewrite na_heap_mapsto_eq.
  iMod (ghost_load_rd with "Hspec [$] [$]") as "(?&$)"; eauto.
  iModIntro. iApply "Hclo_l". iFrame.
Qed.


Lemma ghost_cmpxchg_fail_rd j K `{LanguageCtx _ K} E l q n v' v1 v2:
  v' ≠ v1 → vals_compare_safe v' v1 →
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st (RSt n) l q v' -∗
  j ⤇ K (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) -∗ |NC={E}=>
  na_heap_mapsto_st (RSt n) l q v' ∗ j ⤇ K (PairV v' (LitV $ LitBool false)).
Proof.
  iIntros (???) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_heap_read' with "Hσ Hl") as %([]&?&?&Hlock&Hle); try inversion Hlock; subst.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { eapply head_prim_step_trans.
    rewrite /= /head_step /=.
    repeat (monad_simpl; simpl).
  }
  { eauto. }
  rewrite bool_decide_false //.
  iMod ("Hclo" with "[Hσ H Hrest]").
  { iNext. iExists _. iFrame. }
  simpl. iFrame. eauto.
Qed.

Lemma ghost_cmpxchg_fail j K `{LanguageCtx _ K} E l q v' v1 v2:
  v' ≠ v1 → vals_compare_safe v' v1 →
  nclose sN ⊆ E →
  spec_ctx -∗
  l s↦{q} v' -∗
  j ⤇ K (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) -∗ |NC={E}=>
  l s↦{q} v' ∗ j ⤇ K (PairV v' (LitV $ LitBool false)).
Proof.
  iIntros (???) "Hspec Hl0 Hj".
  iDestruct (heap_mapsto_na_acc with "Hl0") as "(Hl&Hclo_l)".
  rewrite na_heap_mapsto_eq.
  iMod (ghost_cmpxchg_fail_rd with "Hspec [$] [$]") as "(?&$)"; eauto.
  iModIntro. iApply "Hclo_l". iFrame.
Qed.

Lemma ghost_cmpxchg_suc j K `{LanguageCtx _ K} E l v' v1 v2:
  v' = v1 → vals_compare_safe v' v1 →
  nclose sN ⊆ E →
  spec_ctx -∗
  l s↦ v' -∗
  j ⤇ K (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) -∗ |NC={E}=>
  l s↦ v2 ∗ j ⤇ K (PairV v' (LitV $ LitBool true)).
Proof.
  iIntros (???) "(#Hctx&#Hstate) Hl0 Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (heap_mapsto_na_acc with "Hl0") as "(Hl&Hclo_l)".
  iDestruct (@na_heap_read_1 with "Hσ Hl") as %(lk&?&?Hlock).
  destruct lk; inversion Hlock; subst.
  iMod (na_heap_write _ _ _ (Reading 0) with "Hσ Hl") as "(Hσ&Hl)"; first done.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { eapply head_prim_step_trans.
    rewrite /= /head_step /=.
    repeat (monad_simpl; simpl).
  }
  { eauto. }
  rewrite bool_decide_true //.
  iMod ("Hclo" with "[Hσ H Hrest]").
  { iNext. iExists _. iFrame "H". simpl. iFrame; simpl. rewrite upd_equiv_null_non_alloc; eauto. }
  simpl. iFrame. iModIntro. iApply "Hclo_l"; eauto.
Qed.

Lemma ghost_cmpxchg_block_oob_stuck j K `{LanguageCtx _ K} E l (v1 v2: val) n
  (Hoff: (addr_offset l < 0 ∨ n <= addr_offset l)%Z):
  nclose sN ⊆ E →
  spec_ctx -∗
  na_block_size (addr_base l) n →
  j ⤇ K (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) -∗ |NC={E}=> False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_block_size_oob_lookup with "Hσ Hl") as %Hnone; auto.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e' ∨ of_val v1 = e' ∨ of_val v2 = e').
    { move: Heq. destruct Ki => //=; naive_solver congruence. }
    naive_solver.
  }
  solve_ndisj.
Qed.

Lemma ghost_cmpxchg_null_stuck j K `{LanguageCtx _ K} E l (v1 v2: val):
  addr_base l = null →
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) -∗ |NC={E}=> False.
Proof.
  iIntros (??) "(#Hctx&#Hstate) Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct (spec_interp_null _ l with "Hinterp") as ">Hnone"; eauto.
  iDestruct "Hnone" as %Hnone.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e' ∨ of_val v1 = e' ∨ of_val v2 = e').
    { move: Heq. destruct Ki => //=; naive_solver congruence. }
    naive_solver.
  }
  solve_ndisj.
Qed.

Lemma ghost_cmpxchg_suc_read_stuck j K `{LanguageCtx _ K} E l v v1 v2 n q:
  v = v1 →
  (0 < n)%nat →
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st (RSt n) l q v -∗
  j ⤇ K (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) -∗ |NC={E}=> False.
Proof.
  iIntros (???) "(#Hctx&#Hstate) Hlread Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_heap_read' with "Hσ Hlread") as %([]&x&?&Hlock&Hle); try inversion Hlock; subst.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
    destruct (decide (vals_compare_safe v1 v1)).
    ** destruct x; first by lia. monad_inv; eauto.
    ** monad_inv; eauto.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e' ∨ of_val v1 = e' ∨ of_val v2 = e').
    { move: Heq. destruct Ki => //=; naive_solver congruence. }
    naive_solver.
  }
  { eauto. }
Qed.

Lemma ghost_cmpxchg_write_stuck j K `{LanguageCtx _ K} E l v v1 v2 q:
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st (WSt) l q v -∗
  j ⤇ K (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) -∗ |NC={E}=> False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_heap_write_lookup with "Hσ Hl") as %([]&?&Hlock); try inversion Hlock; subst.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e' ∨ of_val v1 = e' ∨ of_val v2 = e').
    { move: Heq. destruct Ki => //=; naive_solver congruence. }
    naive_solver.
  }
  { eauto. }
Qed.

Lemma ghost_finish_store j K `{LanguageCtx _ K} E l (v' v: val) :
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st WSt l 1 v' -∗
  (∀ v', na_heap_mapsto (hG := refinement_na_heapG) l 1 v' -∗ l s↦ v') -∗
  j ⤇ K (FinishStore (Val $ LitV $ LitLoc l) v) -∗ |NC={E}=>
  l s↦ v ∗ j ⤇ K #().
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hlclo Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iMod (na_heap_write_finish_vs _ _ _ _ (Reading 0) with "Hl Hσ") as (lkw (?&Hlock)) "(Hσ&Hl)"; first done.
  destruct lkw; inversion Hlock; subst.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { eapply head_prim_step_trans.
    rewrite /= /head_step /=.
    repeat (monad_inv; simpl in *; monad_simpl).
    econstructor.
    - rewrite /is_Writing/ifThenElse. destruct (decide _).
      * econstructor. eauto.
      * exfalso; eauto.
    - repeat (monad_inv; simpl in *; monad_simpl).
  }
  { eauto. }
  iMod ("Hclo" with "[Hσ H Hrest]").
  { iNext. iExists _. iFrame "H". simpl. iFrame; simpl. rewrite upd_equiv_null_non_alloc; eauto. }
  simpl. iFrame. iModIntro. iApply "Hlclo"; eauto.
Qed.

Lemma ghost_prepare_write j K `{LanguageCtx _ K} E l v :
  nclose sN ⊆ E →
  spec_ctx -∗
  l s↦ v -∗
  j ⤇ K (PrepareWrite (Val $ LitV $ LitLoc l)) -∗ |NC={E}=>
  na_heap_mapsto_st WSt l 1 v ∗ (∀ v', na_heap_mapsto l 1 v' -∗ l s↦ v') ∗ j ⤇ K #().
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (heap_mapsto_na_acc with "Hl") as "[Hl Hl_rest]".
  iMod (na_heap_write_prepare _ _ _ _ Writing with "Hσ Hl") as (lk1 (Hlookup&Hlock)) "(Hσ&?)"; first done.
  destruct lk1; inversion Hlock; subst.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { eapply head_prim_step_trans.
    rewrite /= /head_step /=.
    repeat (monad_simpl; simpl).
  }
  { eauto. }
  iMod ("Hclo" with "[Hσ H Hrest]").
  { iNext. iExists _. iFrame "H". simpl. iFrame; simpl. rewrite upd_equiv_null_non_alloc; eauto. }
  by iFrame.
Qed.

Lemma ghost_prepare_write_read_stuck j K `{LanguageCtx _ K} E l v n q:
  (0 < n)%nat →
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st (RSt n) l q v -∗
  j ⤇ K (PrepareWrite (Val $ LitV $ LitLoc l)) -∗ |NC={E}=> False.
Proof.
  iIntros (??) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_heap_read' with "Hσ Hl") as %([]&x&?&Hlock&Hle); try inversion Hlock; subst.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
    destruct x; first by lia. simpl in *; monad_inv; auto.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    subst. eauto.
  }
  { eauto. }
Qed.

Lemma ghost_prepare_write_block_oob_stuck j K `{LanguageCtx _ K} E l n
  (Hoff: (addr_offset l < 0 ∨ n <= addr_offset l)%Z):
  nclose sN ⊆ E →
  spec_ctx -∗
  na_block_size (addr_base l) n →
  j ⤇ K (PrepareWrite (Val $ LitV $ LitLoc l)) -∗ |NC={E}=> False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_block_size_oob_lookup with "Hσ Hl") as %Hnone; auto.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    subst. eauto.
  }
  solve_ndisj.
Qed.

Lemma ghost_prepare_write_write_stuck j K `{LanguageCtx _ K} E l q (v: val):
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st (WSt) l q v -∗
  j ⤇ K (PrepareWrite (Val $ LitV $ LitLoc l)) -∗ |NC={E}=> False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_heap_write_lookup with "Hσ Hl") as %([]&?&Hlock); try inversion Hlock; subst.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    subst. eauto.
  }
  solve_ndisj.
Qed.

Lemma ghost_prepare_write_null_stuck j K `{LanguageCtx _ K} E l:
  addr_base l = null →
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (PrepareWrite (Val $ LitV $ LitLoc l)) -∗ |NC={E}=> False.
Proof.
  iIntros (Hnull ?) "(#Hctx&#Hstate) Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct (spec_interp_null _ l with "Hinterp") as ">Hnone"; eauto.
  iDestruct "Hnone" as %Hnone.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    subst. eauto.
  }
  solve_ndisj.
Qed.

Lemma ghost_finish_read j K `{LanguageCtx _ K} E l n q (v: val) :
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st (RSt (S n)) l q v -∗
  j ⤇ K (FinishRead (Val $ LitV $ LitLoc l)) -∗ |NC={E}=>
  na_heap_mapsto_st (RSt n) l q v ∗ j ⤇ K #().
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iMod (na_heap_read_finish_vs' _ (fun m => match m with | Reading (S n) => Reading n | _ => m end) with "Hl Hσ") as (lk1 n1 (Hlookup&Hlock)) "[Hσ Hl]".
  1: {
    intros lk lkn Hlk. destruct lk; inversion Hlk; subst.
    rewrite /= //.
  }
  destruct lk1; inversion Hlock; subst.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { eapply head_prim_step_trans.
    rewrite /= /head_step /=.
    repeat (monad_inv; simpl in *; monad_simpl).
  }
  { eauto. }
  iMod ("Hclo" with "[Hσ H Hrest]").
  { iNext. iExists _. iFrame "H". simpl. iFrame; simpl. rewrite upd_equiv_null_non_alloc; eauto. }
  simpl. by iFrame.
Qed.

Lemma ghost_start_read j K `{LanguageCtx _ K} E l n q (v: val) :
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st (RSt n) l q v -∗
  j ⤇ K (StartRead (Val $ LitV $ LitLoc l)) -∗ |NC={E}=>
  na_heap_mapsto_st (RSt (S n)) l q v ∗ j ⤇ K v.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iMod (na_heap_read_prepare' _ (fun m => match m with | Reading n => Reading (S n) | _ => m end) with "Hσ Hl") as (lk1 n1 (Hlookup&Hlock)) "[Hσ Hl]".
  1: {
    intros lk lkn Hlk. destruct lk; inversion Hlk; subst.
    rewrite /= //.
  }
  destruct lk1; inversion Hlock; subst.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { eapply head_prim_step_trans.
    rewrite /= /head_step /=.
    repeat (monad_simpl; simpl).
  }
  { eauto. }
  iMod ("Hclo" with "[Hσ H Hrest]").
  { iNext. iExists _. iFrame "H". simpl. iFrame; simpl. rewrite upd_equiv_null_non_alloc; eauto. }
  by iFrame.
Qed.

Lemma ghost_start_read_block_oob_stuck j K `{LanguageCtx _ K} E l n
  (Hoff: (addr_offset l < 0 ∨ n <= addr_offset l)%Z):
  nclose sN ⊆ E →
  spec_ctx -∗
  na_block_size (addr_base l) n →
  j ⤇ K (StartRead (Val $ LitV $ LitLoc l)) -∗ |NC={E}=> False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_block_size_oob_lookup with "Hσ Hl") as %Hnone; auto.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    subst. eauto.
  }
  solve_ndisj.
Qed.

Lemma ghost_start_read_write_stuck j K `{LanguageCtx _ K} E l q (v: val):
  nclose sN ⊆ E →
  spec_ctx -∗
  na_heap_mapsto_st (WSt) l q v -∗
  j ⤇ K (StartRead (Val $ LitV $ LitLoc l)) -∗ |NC={E}=> False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hl Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&Hrest)".
  iDestruct (@na_heap_write_lookup with "Hσ Hl") as %([]&?&Hlock); try inversion Hlock; subst.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    subst. eauto.
  }
  solve_ndisj.
Qed.

Lemma ghost_start_read_null_stuck j K `{LanguageCtx _ K} E l:
  addr_base l = null →
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (StartRead (Val $ LitV $ LitLoc l)) -∗ |NC={E}=> False.
Proof.
  iIntros (Hnull ?) "(#Hctx&#Hstate) Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iDestruct (spec_interp_null _ l with "Hinterp") as ">Hnone"; eauto.
  iDestruct "Hnone" as %Hnone.
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #l = e').
    { move: Heq. destruct Ki => //=; congruence. }
    subst. eauto.
  }
  solve_ndisj.
Qed.

Lemma ghost_allocN_non_pos_stuck j K `{LanguageCtx _ K} E v (n: u64) :
  ¬ (0 < int.Z n)%Z →
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (AllocN (Val $ LitV $ LitInt $ n) (Val v)) -∗ |NC={E}=> False.
Proof.
  iIntros (Hnonpos ?) "(#Hctx&#Hstate) Hj".
  iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
  iMod (ghost_step_stuck with "Hj Hctx H") as %[].
  {
  split; first done.
  apply prim_head_irreducible; auto.
  * head_irreducible.
  * intros Hval. apply ectxi_language_sub_redexes_are_values => Ki e' Heq.
    assert (of_val #n = e' ∨ of_val v = e').
    { move: Heq. destruct Ki => //=; naive_solver congruence. }
    naive_solver.
  }
  solve_ndisj.
Qed.

Definition spec_mapsto_vals_toks l q vs : iProp Σ :=
  ([∗ list] j↦vj ∈ vs, (l +ₗ j) s↦{q} vj ∗ meta_token (hG := refinement_na_heapG) (l +ₗ j) ⊤)%I.

Lemma ghost_allocN_seq_sized_meta j K `{LanguageCtx _ K} E v (n: u64) :
  (0 < length (flatten_struct v))%nat →
  (0 < int.Z n)%Z →
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (AllocN (Val $ LitV $ LitInt $ n) (Val v)) -∗ |NC={E}=>
  ∃ l : loc, j ⤇ K (#l) ∗
             ⌜ l ≠ null ∧ addr_offset l = 0%Z ⌝ ∗
             na_block_size (hG := refinement_na_heapG) l (int.nat n * length (flatten_struct v))%nat ∗
             [∗ list] i ∈ seq 0 (int.nat n),
             (spec_mapsto_vals_toks (l +ₗ (length (flatten_struct v) * Z.of_nat i)) 1
                               (flatten_struct v)).
Proof.
  iIntros (Hlen Hn Φ) "(#Hctx&Hstate) Hj".
  iInv "Hstate" as (σ) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&(Hrest1&Hrest2&Hrest3&Hrest4&Hrest5))".
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step_trans. simpl.
    econstructor; last (repeat econstructor).
    econstructor. { monad_simpl. }
    eexists _ (fresh_locs (dom (gset loc) _.(heap))); repeat econstructor.
      ** apply fresh_locs_non_null; lia.
      ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
  }
  { solve_ndisj. }
  set (l := fresh_locs (dom (gset loc) (heap _))).
  assert (isFresh σ l) as Hfresh.
  { apply fresh_locs_isFresh. }
  iMod (na_heap_alloc_list tls (heap _) l
                           (concat_replicate (int.nat n) (flatten_struct v))
                           (Reading O) with "Hσ")
    as "(Hσ & Hblock & Hl)".
  { rewrite concat_replicate_length. cut (0 < int.nat n)%nat; first by lia.
    lia. }
  { destruct Hfresh as (?&?). rewrite //=. }
  { destruct Hfresh as (H'&?); eauto. eapply H'. }
  { destruct Hfresh as (H'&?); eauto. destruct (H' 0) as (?&Hfresh).
    by rewrite (loc_add_0) in Hfresh.
  }
  { eauto. }
  iMod ("Hclo" with "[Hσ H Hrest1 Hrest2 Hrest3 Hrest4 Hrest5]").
  { iNext. iExists _. iFrame "H". iFrame.
    iDestruct "Hrest4" as %Hnon_null.
    iPureIntro. intros off.
    cut (∀ off x, heap (state_init_heap l x v σ) !! addr_plus_off null off =
                heap σ !! addr_plus_off null off).
    { intros ->. eauto. }
    intros.  rewrite /state_init_heap/ state_insert_list.
    rewrite lookup_union_r //.
    eapply heap_array_lookup_base_ne. erewrite isFresh_base; eauto.
    eapply isFresh_not_null; eauto.
  }
  iModIntro.
  iExists _. iFrame.
  unfold mapsto_vals.
  rewrite concat_replicate_length. iFrame.
  iDestruct (heap_seq_replicate_to_nested_mapsto l (flatten_struct v) (int.nat n)
                                                 (λ l v, l s↦ v ∗ meta_token l ⊤)%I
               with "[Hl]") as "Hl".
  {
    iApply (big_sepL_mono with "Hl").
    iIntros (l0 x Heq) "(Hli&$)".
    iApply (na_mapsto_to_heap with "Hli").
    destruct Hfresh as (H'&?). eapply H'.
  }
  iSplitL "".
  { iPureIntro; split; eauto using isFresh_not_null, isFresh_offset0. }
  iApply (big_sepL_mono with "Hl").
  iIntros (k0 ? _) "H".
  setoid_rewrite Z.mul_comm at 1.
  setoid_rewrite Z.mul_comm at 2.
  rewrite /spec_mapsto_vals_toks. eauto.
Qed.

End go_ghost_step.
End go_spec_definitions.

End go_refinement.

Notation "l s↦{ q } v" := (heap_mapsto (hG := refinement_na_heapG) l q v%V)
  (at level 20, q at level 50, format "l  s↦{ q }  v") : bi_scope.
Notation "l s↦ v" :=
  (heap_mapsto (hG := refinement_na_heapG) l 1 v%V) (at level 20) : bi_scope.
Notation "l s↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  s↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Section trace_inv.
Context {ext: ext_op}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ext_semantics ext ffi}.
Context `{!ffi_interp ffi}.
Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{!spec_ffi_interp spec_ffi}.
Context {Σ: gFunctors}.
Context {hG: heapG Σ}.
Context {hS: stagedG Σ}.
Context {hR: refinement_heapG Σ}.

Definition trace_inv : iProp Σ :=
  (∃ tr trs or ors, ⌜ tr = trs ⌝ ∗
                    ⌜ or = ors ⌝ ∗
                    trace_frag (hT := heapG_traceG) tr ∗
                    trace_frag (hT := refinement_traceG) trs ∗
                    oracle_frag (hT := heapG_traceG) or ∗
                    oracle_frag (hT := refinement_traceG) ors).

Definition spec_traceN := sN .@ "trace".

Definition trace_ctx : iProp Σ :=
  ncinv spec_traceN trace_inv.

End trace_inv.

Section resolution_test.
Context {ext: ext_op}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ext_semantics ext ffi}.
Context `{!ffi_interp ffi}.
Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{!spec_ffi_interp spec_ffi}.
Context {Σ: gFunctors}.
Context {hG: heapG Σ}.
Context {hS: stagedG Σ}.
Context {hR: refinement_heapG Σ}.
Set Printing Implicit.

Lemma test_resolution1 l v :
  l ↦ v -∗ (heap_mapsto (hG := heapG_na_heapG) l 1 (v)).
Proof using Type.
  iIntros "H". eauto.
Qed.

Lemma test_resolution2 l v :
  l s↦ v -∗ (heap_mapsto (hG := refinement_na_heapG) l 1 (v)).
Proof using Type.
  iIntros "H". eauto.
Qed.

Lemma test_resolution3 l v :
  l ↦ v -∗ (heap_mapsto l 1 (v)).
Proof using Type.
  iIntros "H". eauto.
Qed.

Lemma test_resolution4 l v :
  l s↦ v -∗ (heap_mapsto l 1 (v)).
Proof using Type.
  iIntros "H". eauto.
Qed.
Unset Printing Implicit.

End resolution_test.

Arguments refinement_spec_ffiG {spec_ext spec_ffi spec_ffi_semantics spec_ffi_interp0 Σ hRG} : rename.

Section tacs.
Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{!spec_ffi_interp spec_ffi}.
Existing Instance spec_ffi_interp_field.
Existing Instance spec_ext_semantics_field.
Existing Instance spec_ext_op_field.
Existing Instance spec_ffi_model_field.


Notation sexpr := (@expr (@spec_ext_op_field spec_ext)).

Lemma tac_refine_bind (K: sexpr → sexpr) `{LanguageCtx _ K} (K' : list (ectxi_language.ectx_item _)) (e e': sexpr):
  ectx_language.fill K' e' = e →
  (K e = (λ x, K (ectx_language.fill K' x)) e') ∧
  LanguageCtx (λ x, K (ectx_language.fill K' x)).
Proof. rewrite //=. intros ->. split; auto. apply comp_ctx; auto. apply ectx_lang_ctx. Qed.

Lemma tac_refine_bind' (K: sexpr → sexpr) {Hctx: LanguageCtx' (ext := @spec_ext_op_field _)
                                             (ffi := (spec_ffi_model_field))
                                             (ffi_semantics := (spec_ext_semantics_field))
                                             K} (K' : list (ectxi_language.ectx_item _)) (e e': sexpr):
  ectx_language.fill K' e' = e →
  (K e = (λ x, K (ectx_language.fill K' x)) e') ∧
  LanguageCtx' (λ x, K (ectx_language.fill K' x)).
Proof. rewrite //=. intros ->. split; auto. apply comp_ctx'; auto. apply ectx_lang_ctx'. Qed.

End tacs.

(* Some duplication here with reshape_expr that is used in wp... the need for the duplication is
   that the K returned by reshape_expr will be an ectx_item list for the *implementation* layer,
   not for the spec layer *)

Ltac refine_reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _                               => tac K e
    | App ?e (Val ?v)                 => add_item (@AppLCtx spec_ext_op_field v) K e
    | App ?e1 ?e2                     => add_item (@AppRCtx spec_ext_op_field e1) K e2
    | UnOp ?op ?e                     => add_item (@UnOpCtx spec_ext_op_field op) K e
    | BinOp ?op (Val ?v) ?e           => add_item (@BinOpRCtx spec_ext_op_field op v) K e
    | BinOp ?op ?e1 ?e2               => add_item (@BinOpLCtx spec_ext_op_field op e2) K e1
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) K e0
    | Pair (Val ?v) ?e                => add_item (PairRCtx v) K e
    | Pair ?e1 ?e2                    => add_item (PairLCtx e2) K e1
    | Fst ?e                          => add_item (@FstCtx spec_ext_op_field) K e
    | Snd ?e                          => add_item (@SndCtx spec_ext_op_field) K e
    | InjL ?e                         => add_item (@InjLCtx spec_ext_op_field) K e
    | InjR ?e                         => add_item (@InjRCtx spec_ext_op_field) K e
    | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) K e0
    | Primitive2 ?op (Val ?v) ?e      => add_item (@Primitive2RCtx spec_ext_op_field op v) K e
    | Primitive2 ?op ?e1 ?e2          => add_item (@Primitive2LCtx spec_ext_op_field op e2) K e1
    | Primitive1 ?op ?e               => add_item (@Primitive1Ctx spec_ext_op_field op) K e
    | ExternalOp ?op ?e               => add_item (@ExternalOpCtx spec_ext_op_field op) K e
    (* | Primitive3 ?op (Val ?v0) (Val ?v1) ?e2 => add_item (Primitive3RCtx op v0 v1) K e2
    | Primitive3 ?op (Val ?v0) ?e1 ?e2     => add_item (Primitive3MCtx op v0 e2) K e1
    | Primitive3 ?op ?e0 ?e1 ?e2           => add_item (Primitive3LCtx op e1 e2) K e0 *)
    | CmpXchg (Val ?v0) (Val ?v1) ?e2 => add_item (CmpXchgRCtx v0 v1) K e2
    | CmpXchg (Val ?v0) ?e1 ?e2       => add_item (CmpXchgMCtx v0 e2) K e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgLCtx e1 e2) K e0
    end
  with add_item Ki K e :=
    go (Ki :: K) e
  in
  go (@nil (@ectx_item spec_ext_op_field)) e.

Tactic Notation "spec_bind" open_constr(efoc) " as " ident(H) :=
  iStartProof;
  lazymatch goal with
  | |- context[ (?j ⤇ ?Kinit ?e)%I ] =>
    let H' := fresh H in
    refine_reshape_expr e ltac:(fun K' e' => unify e' efoc; destruct (tac_refine_bind Kinit K' e e') as (->&H'); [split; eauto|])
    || fail "spec_bind: cannot find" efoc "in" e
  end.

Section tacs_test.
Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{!spec_ffi_interp spec_ffi}.
Existing Instance spec_ffi_interp_field.
Existing Instance spec_ext_semantics_field.
Existing Instance spec_ext_op_field.
Existing Instance spec_ffi_model_field.

Context {Σ: gFunctors}.
Context {hG: heapG Σ}.
Context {hR: refinement_heapG Σ}.

Notation sexpr := (@expr (@spec_ext_op_field spec_ext)).

Lemma test j (K: sexpr → sexpr) `{LanguageCtx _ K} (e: sexpr):
  j ⤇ K (PrepareWrite e) -∗
  j ⤇ K (PrepareWrite e).
Proof. spec_bind e as Hctx. Abort.

End tacs_test.
