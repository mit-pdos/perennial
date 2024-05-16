From Perennial.goose_lang Require Import proof_automation.
From Perennial.goose_lang Require Import struct.struct.

Set Default Proof Using "Type".

Section wp.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Definition allocate_zero t : val :=
    λ: <>, ref (zero_val t).

  (* manual version of proof *)
  Lemma allocate_zero_spec t :
    has_zero t →
    {{{ True }}}
      allocate_zero t #()
    {{{ (l:loc), RET #l; l ↦[t] (zero_val t) }}}.
  Proof.
    iIntros (Hzero Φ) "_ HΦ".
    wp_call.
    wp_apply wp_ref_of_zero; first auto.
    iIntros (l) "Hl".
    iApply "HΦ".
    iAssumption.
  Qed.

  Lemma allocate_zero_spec_automated t :
    has_zero t →
    {{{ True }}}
      allocate_zero t #()
    {{{ (l:loc), RET #l; l ↦[t] (zero_val t) }}}.
  Proof.
    (* TODO: stopped working with Perennial typeclass *)
    iSteps.
    admit.
  Abort.

End wp.
