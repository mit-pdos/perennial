Require Export New.generatedproof.go_etcd_io.etcd.pkg.v3.idutil.
Require Export New.proof.proof_prelude.
From New.proof Require Import time math sync.atomic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit math := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit idutil := define_is_pkg_init True%I.

Definition is_Generator (g : loc) : iProp Σ :=
  ∃ (prefix : w64),
    "#prefix" ∷ g ↦s[idutil.Generator :: "prefix"]□ prefix ∗
    "#suffix" ∷ inv nroot (∃ (suffix : w64),
          struct.field_ref_f idutil.Generator "suffix" g ↦ suffix
      ) ∗
    "_" ∷ True.
#[global] Opaque is_Generator.
#[local] Transparent is_Generator.
Instance : ∀ s, Persistent (is_Generator s).
Proof. apply _. Qed.

Lemma wp_lowbit (x n : w64) :
  {{{ is_pkg_init idutil }}}
    @! idutil.lowbit #x #n
  {{{ (y : w64), RET #y; True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

Lemma wp_Generator__Next g :
  {{{ is_pkg_init idutil ∗ is_Generator g }}}
    g @ (ptrT.id idutil.Generator.id) @ "Next" #()
  {{{ (i : w64), RET #i; True }}}.
Proof.
  wp_start as "H". iNamedSuffix "H" "_g".
  wp_auto. wp_bind.
  wp_apply wp_AddUint64.
  iInv "suffix_g" as ">Hi" "Hclose".
  iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
  iNamed "Hi". iFrame. iIntros "Hi".
  iMod "Hmask". iMod ("Hclose" with "[$Hi]") as "_". iModIntro.
  wp_auto. wp_apply wp_lowbit as "%y _". iApply "HΦ". done.
Qed.

Lemma wp_NewGenerator (memberID : w16) (now : time.Time.t) :
  {{{ is_pkg_init idutil }}}
    @! idutil.NewGenerator #memberID #now
  {{{ RET #(); True }}}.
Proof.
  wp_start as "H". wp_auto.
Admitted.

End wps.
