From New.proof Require Import proof_prelude.
From New.proof Require Export std.
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

(* Pure model of strings.Fields:
   is_space_byte identifies ASCII whitespace bytes (space, \t, \n, \r);
   drop_while/take_while are helpers used to define split_fields_go,
   which models Go's strings.Fields splitting behavior.
   fields_spec ties the axiomatic WP to the pure model. *)
Definition is_space_byte (b : w8) : bool :=
  (word.eqb b (W8 32)) ||    (* space    *)
  (word.eqb b (W8 9))  ||    (* \t       *)
  (word.eqb b (W8 10)) ||    (* \n       *)
  (word.eqb b (W8 13)).      (* \r       *)

Fixpoint drop_while {A} (f : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' => if f x then drop_while f xs' else x :: xs'
  end.

Fixpoint take_while {A} (f : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' => if f x then x :: take_while f xs' else []
  end.

Fixpoint split_fields_go (fuel : nat) (s : go_string) : list go_string :=
  match fuel with
  | O => []
  | S fuel' =>
      let s' := drop_while is_space_byte s in
      match s' with
      | [] => []
      | _ =>
          let w := take_while (fun b => negb (is_space_byte b)) s' in
          let rest := drop_while (fun b => negb (is_space_byte b)) s' in
          w :: split_fields_go fuel' rest
      end
  end.

Definition fields_spec (s : go_string) (ss : list go_string) : Prop :=
  ss = split_fields_go (length s) s ∧ (length ss) < 2 ^ 64 .

Axiom wp_strings_Fields :
  ∀ `{!strings.Assumptions} (s : go_string),
  {{{ is_pkg_init strings }}}
    @! strings.Fields #s
  {{{ sl (ss : list go_string),
      RET #sl;
      sl ↦* ss ∗ ⌜ fields_spec s ss ⌝ ∗  own_slice_cap w8 sl (DfracOwn 1) }}}.

(* Unit tests for split_fields_go *)
Example split_fields_go_hello :
  split_fields_go (length "hello"%go) "hello"%go = ["hello"%go].
Proof. vm_compute. reflexivity. Qed.

Example split_fields_go_leading_spaces :
  split_fields_go (length "   hello world"%go) "   hello world"%go =
    ["hello"%go; "world"%go].
Proof. vm_compute. reflexivity. Qed.

Example split_fields_go_two_words :
  split_fields_go (length "hello world"%go) "hello world"%go =
    ["hello"%go; "world"%go].
Proof. vm_compute. reflexivity. Qed.

Example split_fields_go_empty :
  split_fields_go (length ""%go) ""%go = [].
Proof. vm_compute. reflexivity. Qed.

Definition bs_tab : w8 := W8 9.
Definition bs_nl  : w8 := W8 10.
Definition bs_cr  : w8 := W8 13.
Definition bs_sp  : w8 := W8 32.

Definition hello_world_ws : go_string :=
  [bs_sp; bs_tab] ++ "hello"%go ++ [bs_nl] ++ "world"%go ++ [bs_cr; bs_sp].

Example split_fields_go_mixed_ws :
  split_fields_go (length hello_world_ws) hello_world_ws =
    ["hello"%go; "world"%go].
Proof. vm_compute. reflexivity. Qed.

Example split_fields_go_interp_string_literal :
  split_fields_go (length "  hello\tthere\ngeneral\rkenobi "%go)
                  "  hello\tthere\ngeneral\rkenobi "%go
  = ["hello"%go; "there"%go; "general"%go; "kenobi"%go].
Proof. vm_compute. reflexivity. Qed.

(* Unit tests for wp_strings_Fields, exercising the axiom via fields_spec *)
Example wp_Fields_mixed_ws :
  {{{ is_pkg_init strings }}}
    @! strings.Fields #("  hello\tthere\ngeneral\rkenobi "%go)
  {{{ sl,
      RET #sl;
      sl ↦* ["hello"%go; "there"%go; "general"%go; "kenobi"%go] ∗ own_slice_cap w8 sl (DfracOwn 1) }}}.
Proof.
  iIntros (Φ) "#Hinit HΦ".
  wp_apply (wp_strings_Fields).
  iIntros (sl ss) "(Hsl & %Hspec & Hcap)".
  destruct Hspec as [Hss _].
  subst ss.
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
  wp_apply (wp_strings_Fields "hello world"%go).
  iIntros (sl ss) "(Hsl & %Hspec & Hcap)".
  destruct Hspec as [Hss _].
  subst ss.
  iApply "HΦ". iFrame.
Qed.

End wps.