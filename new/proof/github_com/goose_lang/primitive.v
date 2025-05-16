From New.proof Require Import proof_prelude.
Require Import New.code.github_com.goose_lang.primitive.
Require Import New.generatedproof.github_com.goose_lang.primitive.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

#[global]
Program Instance is_pkg_init_inst : IsPkgInit (PROP:=iProp Σ) primitive :=
  ltac2:(build_pkg_init ()).

Lemma wp_Assume (cond : bool) :
  {{{ is_pkg_init primitive }}}
    primitive@"Assume" #cond
  {{{ RET #(); ⌜ cond = true ⌝ }}}
.
Proof.
  wp_start as "#Hdef".
  destruct cond; wp_auto.
  - iApply ("HΦ" with "[//]").
  - iLöb as "IH". wp_auto.
    wp_apply ("IH" with "[$]").
Qed.

Lemma wp_RandomUint64 :
  {{{ is_pkg_init primitive }}}
    primitive@"RandomUint64" #()
  {{{ (x: w64), RET #x; True }}}
.
Proof.
  wp_start as "_".
  wp_apply wp_ArbitraryInt.
  iIntros (x).
  iApply "HΦ".
  done.
Qed.

Lemma wp_UInt64Get s q (x: u64) (vs: list w8) :
  take 8 vs = u64_le x →
  {{{ is_pkg_init primitive ∗ own_slice s q vs }}}
    primitive@"UInt64Get" #s
  {{{ RET #x; own_slice s q vs }}}.
Proof.
  intros Hx.
  wp_start as "Hs".
Admitted.

Lemma wp_UInt64Put s x (vs: list w8) :
  (length vs >= w64_bytes)%nat →
  {{{ is_pkg_init primitive ∗ own_slice s (DfracOwn 1) vs }}}
    primitive@"UInt64Put" #s #x
  {{{ RET #(); own_slice s (DfracOwn 1) (u64_le x ++ (drop w64_bytes vs)) }}}.
Proof.
  intros Hvs.
  wp_start as "Hs".
Admitted.

End wps.
