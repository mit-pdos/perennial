From New.proof Require Import proof_prelude.
From New.generatedproof Require Export strings.
From Perennial Require Import base.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : strings.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) strings := build_get_is_pkg_init_wf.

Lemma wp_asciiSpace_init :
  {{{ True }}}
    strings.asciiSpace'init #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop strings get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    strings.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init strings }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply wp_asciiSpace_init.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

(* Model for Go's unicode.IsSpace for ASCII-range bytes.
   Based on https://cs.opensource.google/go/go/+/refs/tags/go1.26.1:src/strings/strings.go;l=377 *)
Definition is_ascii_space (b : w8) : bool :=
  (word.eqb b (W8 9))  ||    (* \t  (0x09) *)
  (word.eqb b (W8 10)) ||    (* \n  (0x0A) *)
  (word.eqb b (W8 11)) ||    (* \v  (0x0B) *)
  (word.eqb b (W8 12)) ||    (* \f  (0x0C) *)
  (word.eqb b (W8 13)) ||    (* \r  (0x0D) *)
  (word.eqb b (W8 32))      (* space (0x20) *)
.

Fixpoint split_fields_aux (s : go_string) (w : option go_string) : list go_string :=
  match s with
  | [] => match w with None => [] | Some w => [w] end
  | x :: s => if is_ascii_space x then
              match w with
              | None => split_fields_aux s None
              | Some w => w :: split_fields_aux s None
              end
            else split_fields_aux s (Some (default [] w ++ [x]))
  end.
Definition split_fields (s : go_string) : list go_string := split_fields_aux s None.

(* FIXME: this is wrong (unsound) for strings with non-ascii runes. Simplest
   solution might be to add a precondition for the string to be all ascii. *)
Axiom wp_Fields :
  ∀ `{!strings.Assumptions} (s : go_string),
  {{{ is_pkg_init strings }}}
    @! strings.Fields #s
  {{{ sl,
      RET #sl;
      sl ↦* (split_fields s) ∗ own_slice_cap w8 sl (DfracOwn 1) }}}.

(* Test split_fields because it is part of the wp_Fields axiom. *)
Example split_fields_hello :
  split_fields "hello"%go = ["hello"%go].
Proof. vm_compute. reflexivity. Qed.

Example split_fields_leading_spaces :
  split_fields "   hello world"%go = ["hello"%go; "world"%go].
Proof. vm_compute. reflexivity. Qed.

Example split_fields_two_words :
  split_fields "hello world"%go = ["hello"%go; "world"%go].
Proof. vm_compute. reflexivity. Qed.

Example split_fields_empty :
  split_fields ""%go = [].
Proof. vm_compute. reflexivity. Qed.

Definition bs_tab : w8 := W8 9.
Definition bs_nl  : w8 := W8 10.
Definition bs_cr  : w8 := W8 13.
Definition bs_sp  : w8 := W8 32.

Definition hello_world_ws : go_string :=
  [bs_sp; bs_tab] ++ "hello"%go ++ [bs_nl] ++ "world"%go ++ [bs_cr; bs_sp].

Example split_fields_mixed_ws :
  split_fields hello_world_ws =
    ["hello"%go; "world"%go].
Proof. vm_compute. reflexivity. Qed.

Example split_fields_interp_string_literal :
  split_fields "  hello\tthere\ngeneral\rkenobi "%go
  = ["hello"%go; "there"%go; "general"%go; "kenobi"%go].
Proof. vm_compute. reflexivity. Qed.

(* Unit tests for wp_Fields, exercising the axiom via fields_spec *)
Example wp_Fields_mixed_ws :
  {{{ is_pkg_init strings }}}
    @! strings.Fields #("  hello\tthere\ngeneral\rkenobi "%go)
  {{{ sl,
      RET #sl;
      sl ↦* ["hello"%go; "there"%go; "general"%go; "kenobi"%go] ∗ own_slice_cap w8 sl (DfracOwn 1) }}}.
Proof.
  iIntros (Φ) "#Hinit HΦ".
  wp_apply (wp_Fields).
  iIntros (sl) "(Hsl & Hcap)".
  iApply "HΦ". iFrame.
Qed.

Example wp_Fields_two_words:
  {{{ is_pkg_init strings }}}
    @! strings.Fields #"hello world"%go
  {{{ sl,
      RET #sl;
      sl ↦* ["hello"%go; "world"%go] ∗
      own_slice_cap w8 sl (DfracOwn 1)
  }}}.
Proof.
  iIntros (Φ) "#Hinit HΦ".
  wp_apply (wp_Fields "hello world"%go).
  iIntros (sl) "(Hsl & Hcap)".
  iApply "HΦ". iFrame.
Qed.

End wps.
