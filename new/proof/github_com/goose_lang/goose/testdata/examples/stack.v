From New.proof Require Export proof_prelude.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base simple.
From New.proof Require Import sync strings time.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!ghost_varG Σ (list go_string)}.

(* TODO: don't duplicate these *)
#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

Definition own_stack (γ: gname) (q: Qp) (xs: list go_string): iProp Σ :=
  ghost_var γ q xs.
Definition stack_rep γ xs := own_stack γ (1/2) xs.

Let N := nroot.

Definition lock_inv l γ: iProp _ :=
    ∃ (stack_s: slice.t) (xs: list go_string),
    "Hxs" ∷ own_stack γ (1/4) xs ∗
    "stack" ∷ l ↦s[chan_spec_raw_examples.LockedStack :: "stack"] stack_s ∗
    "Hstack" ∷ stack_s ↦* (reverse xs) ∗
    "Hcap" ∷ own_slice_cap go_string stack_s (DfracOwn 1).

Definition is_stack (l: loc) γ : iProp Σ :=
  ∃ (mu_l: loc),
  "#Hinv" ∷ inv N (∃ xs, own_stack γ (1/4) xs) ∗
  "#Hlock" ∷ is_Mutex (struct.field_ref_f chan_spec_raw_examples.LockedStack "mu" l) (lock_inv l γ).

Lemma wp_LockedStack__Pop (l: loc) γ :
  ∀ (Φ: val → iProp Σ),
  is_pkg_init chan_spec_raw_examples -∗
  (is_stack l γ ∗ |={⊤,∅}=> ∃ xs, stack_rep γ xs ∗
                  match xs with
                  | [] => stack_rep γ xs -∗ |={∅,⊤}=> Φ (#"", #false)%V
                  | x :: xs' => stack_rep γ xs' -∗ |={∅,⊤}=> Φ (#x, #true)%V
                  end) -∗
  WP l @ (ptrT.id chan_spec_raw_examples.LockedStack.id) @ "Pop" #() {{ Φ }}.
Proof.
  iIntros (Φ) "#? [#Hstack Hau]".
  wp_method_call. wp_call. wp_auto.
  iNamed "Hstack".
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[locked I]". iNamed "I".
  wp_auto.
  wp_if_destruct.
  -
    (* TODO: use invariant to fire au *)
    wp_apply (wp_Mutex__Unlock with "[$Hlock $locked Hxs stack Hstack Hcap]").
    { iFrame. }
    admit.
  - iDestruct (own_slice_len with "Hstack") as %Hlen.
    list_elem (reverse xs) (sint.nat (slice.len_f stack_s) - 1)%nat as x_last.
    {
      rewrite length_reverse in Hlen.
      len.
    }
    wp_pure.
    { len. }
    wp_apply (wp_load_slice_elem with "[$Hstack]") as "Hstack".
    { len. }
    { replace (sint.nat (word.sub stack_s.(slice.len_f) (W64 1))) with (sint.nat stack_s.(slice.len_f) - 1)%nat; eauto.
      word. }
Admitted.

End proof.
