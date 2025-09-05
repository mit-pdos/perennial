Require Export New.generatedproof.time.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit time := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf time := build_get_is_pkg_init_wf.

#[local]
Lemma wp_Time__sec (t : loc) (tv : time.Time.t) :
  {{{ is_pkg_init time ∗ t ↦ tv }}}
    t @ (ptrT.id time.Time.id) @ "sec" #()
  {{{ (x : w64), RET #x; t ↦ tv }}}.
Proof.
  wp_start. wp_auto. wp_if_destruct; wp_auto; by iApply "HΦ".
Qed.

#[local]
Lemma wp_Time__unixSec (t : loc) (tv : time.Time.t) :
  {{{ is_pkg_init time ∗ t ↦ tv }}}
    t @ (ptrT.id time.Time.id) @ "unixSec" #()
  {{{ (x : w64), RET #x; t ↦ tv }}}.
Proof.
  wp_start. wp_auto. wp_apply (wp_Time__sec with "[$]") as "% ?". by iApply "HΦ".
Qed.

#[local]
Lemma wp_Time__nsec (t : loc) (tv : time.Time.t) :
  {{{ is_pkg_init time ∗ t ↦ tv }}}
    t @ (ptrT.id time.Time.id) @ "nsec" #()
  {{{ (x : w32), RET #x; True }}}.
Proof.
  wp_start. wp_auto. by iApply "HΦ".
Qed.

#[local]
Lemma wp_Time__UnixNano (t : time.Time.t) :
  {{{ is_pkg_init time }}}
    t @ time.Time.id @ "UnixNano" #()
  {{{ (x : w64), RET #x; True }}}.
Proof.
  wp_start. wp_auto. wp_apply (wp_Time__unixSec with "[$]") as "% ?".
  wp_apply (wp_Time__nsec with "[$]") as "% ?". by iApply "HΦ".
Qed.

End wps.
