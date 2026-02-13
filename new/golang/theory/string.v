From New.golang.defn Require Export string.
Require Import New.proof.github_com.goose_lang.goose.model.strings.
From New.golang.theory Require Export exception loop proofmode slice.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.StringSemantics}.
Collection W := sem.

Lemma wp_string_to_bytes (s : go_string)
    `[!to ↓u go.SliceType elem_type] `[!elem_type ↓u go.byte] `[!from ↓u go.string] :
  {{{ True }}}
    Convert from to #s
  {{{ sl, RET #sl; sl ↦* s ∗ own_slice_cap w8 sl (DfracOwn 1) }}}.
Proof using W.
  pose proof (go.tagged_steps internal). wp_start. wp_auto.
  wp_apply wp_StringToByteSlice. done.
Qed.

Lemma wp_bytes_to_string sl (s : go_string) dq
    `[!from ↓u go.SliceType elem_type] `[!elem_type ↓u go.byte] `[!to ↓u go.string] :
  {{{ sl ↦*{dq} s }}}
    Convert from to #sl
  {{{ RET #s; sl ↦*{dq} s }}}.
Proof using W.
  pose proof (go.tagged_steps internal). wp_start. wp_auto.
  wp_apply (wp_ByteSliceToString with "[$]"). done.
Qed.

End proof.
