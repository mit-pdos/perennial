From Perennial.goose_lang Require Import proof_automation.
From Perennial.goose_lang Require Import struct.struct.
From Perennial.goose_lang Require Import typed_mem.

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
    iSteps.
  Qed.

  Lemma load_field l t v :
    {{{ l ↦[t] v }}}
      let: "x" := ![t] #l in Var "x"
    {{{ RET v; l ↦[t] v }}}.
  Proof.
    (* why is this not fully automated? *)
    iSteps.
    iIntros "!> !> !> !>".
    iSteps.
  Qed.

  Lemma load_readonly l d f v :
    {{{ readonly (l ↦[d :: f] v) }}}
      struct.loadF d f #l
    {{{ RET v; emp }}}.
  Proof.
    iSteps.
    (* TODO: gets stuck here rather than getting [∃ q, l ↦[d :: f]{q} v] from
    the [readonly]. I wonder if the existentials are confusing it? Need to   *)
    Fail iStep.
  Abort.

End wp.
