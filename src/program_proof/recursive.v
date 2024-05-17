From Perennial.program_proof Require Import proof_prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition recur: val :=
  rec: "recur" "n" :=
    (if: "n" = #0
    then #0
    else "n" + ("recur" ("n" - #1))).

End code.

Section proof.
Context `{heapGS Σ, !ffi_semantics _ _, !ext_types _}.

Lemma wp_test (n : u64) :
  {{{
    True
  }}}
    recur #n
  {{{
    (x : u64), RET #x; True
  }}}.
Proof.
  rewrite /recur.
  iIntros (Φ) "_ HΦ".
  match goal with
  | |- context[RecV (BNamed "recur") _ ?body] => set (loop:=body)
  end.
  iLöb as "IH" forall (n Φ).
  wp_if_destruct.
  { by iApply "HΦ". }
  wp_bind (App _ _).
  wp_pure1.
  (*
    TODO: for some reason, this wipes out HΦ, not letting me Qed.
      iApply ("IH" with "[]").
    But constructing a trivially equivalent IH2 makes things work out.
  *)
  iAssert ((□
    ∀ (n0 : w64) (Φ0 : val → iPropI Σ),
      ⌜True⌝ -∗
      ▷ (∀ x : w64, True -∗ Φ0 #x) -∗
      WP (rec: "recur" "n" := loop)%V #n0 {{ v, Φ0 v }}
  )%I) as "#IH2".
  { iIntros (??) "!> _". iApply "IH". }
  iApply ("IH2" with "[]"); [done|].
  iIntros (?) "!> _".
  wp_pures.
  by iApply "HΦ".
Qed.
