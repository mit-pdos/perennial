(* TODO: there should be a directory for this Go package. *)

From New.proof Require Export proof_prelude.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base.
From New.proof Require Import sync strings time.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

Class locked_stackG Σ :=
  {
    #[local] ls_var_inG :: ghost_varG Σ (list go_string);
  }.

Section locked_stack_proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

(* FIXME: duplication *)
#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

Context `{!locked_stackG Σ}.

Definition own_locked_stack γ (σ : list go_string) : iProp Σ :=
  ghost_var γ (1/2) σ.
#[global] Opaque own_locked_stack.
#[local] Transparent own_locked_stack.

Definition is_LockedStack s γ : iProp Σ :=
  "#Hmu" ∷ (is_Mutex (struct.field_ref_f chan_spec_raw_examples.LockedStack "mu" s)
              (∃ stack_sl (stack : list go_string),
                  "stack" ∷ s ↦s[chan_spec_raw_examples.LockedStack :: "stack"] stack_sl ∗
                  "Hstack_sl" ∷ stack_sl ↦* stack ∗
                  "Hstack_cap" ∷ own_slice_cap go_string stack_sl (DfracOwn 1) ∗
                  "Hstack_auth" ∷ ghost_var γ (1/2) stack
    )).

Lemma wp_NewLockedStack :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.NewLockedStack #()
  {{{ s γ, RET #s; is_LockedStack s γ ∗ own_locked_stack γ [] }}}.
Proof.
  wp_start. unshelve wp_apply wp_slice_make2; try tc_solve; first word.
  iIntros (stack_sl) "[stack_sl cap]". rewrite replicate_0.
  wp_auto. wp_alloc s as "Hs".
  iApply wp_fupd. wp_auto.
  iMod (ghost_var_alloc []) as (γ) "[Hstack_auth Hstack_frag]".
  iApply "HΦ". iDestruct (struct_fields_split with "Hs") as "H". iNamed "H".
  simpl. iMod (init_Mutex with "[$] [-Hstack_frag]") as "$"; by iFrame.
Qed.

End locked_stack_proof.
