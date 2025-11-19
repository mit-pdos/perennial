From New.generatedproof Require Export time.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import logatom.chan_au_base protocol.simple.simple.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chan_au_base.chanG Σ time.Time.t}.

#[global] Instance : IsPkgInit time := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf time := build_get_is_pkg_init_wf.

#[local]
Lemma wp_Time__sec (t : loc) (tv : time.Time.t) :
  {{{ is_pkg_init time ∗ t ↦ tv }}}
    t @ (ptrT.id time.Time.id) @ "sec" #()
  {{{ (x : w64), RET #x; t ↦ tv }}}.
Proof.
  wp_start. wp_auto. wp_if_destruct; by iApply "HΦ".
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

Lemma wp_Time__UnixNano (t : time.Time.t) :
  {{{ is_pkg_init time }}}
    t @ time.Time.id @ "UnixNano" #()
  {{{ (x : w64), RET #x; True }}}.
Proof.
  wp_start. wp_auto. wp_apply (wp_Time__unixSec with "[$]") as "% ?".
  wp_apply (wp_Time__nsec with "[$]") as "% ?". by iApply "HΦ".
Qed.

Axiom wp_Now :
  {{{ is_pkg_init time }}}
    @! time.Now #()
  {{{ (t : time.Time.t), RET #t; True }}}.

Axiom wp_Time__Add : ∀ (t : time.Time.t) (d : time.Duration.t),
  {{{ is_pkg_init time }}}
    t @ time.Time.id @ "Add" #d
  {{{ (t : time.Time.t), RET #t; True }}}.

Lemma wp_arbitraryTime :
  {{{ True }}}
    time.arbitraryTime #()
  {{{ (t: time.Time.t), RET #t; True }}}.
Proof.
  wp_start.
  wp_call.
  change time.time.__Time with time.Time.
  wp_apply wp_ArbitraryInt as "%x".
  by iApply "HΦ".
Qed.

Lemma wp_After (d : time.Duration.t) :
  {{{ is_pkg_init time }}}
    @! time.After #d
  {{{ (ch: loc) γ, RET #ch; is_simple γ ch (λ (t: time.Time.t), True)%I }}}.
Proof.
  wp_start.
  change (time.time.__Time) with (time.Time).
  wp_apply chan.wp_make; first word.
  iIntros (ch γ) "(His & Hcap & Hown)".
  simpl.
  iMod (start_simple _ _ (λ t, True)%I
          with "[$His] [$Hown]") as (γsimple) "[_ #Hch]".
  wp_auto.
  wp_apply wp_fork.
  {
    wp_apply wp_arbitraryTime.
    iIntros (t) "_".
    wp_apply (wp_simple_send with "[$Hch]"). done.
  }
  iApply "HΦ".
  iFrame "#".
Qed.

Lemma wp_Sleep (d : time.Duration.t) :
  {{{ is_pkg_init time }}}
    @! time.Sleep #d
  {{{ RET #(); True }}}.
Proof. wp_start. by iApply "HΦ". Qed.

End wps.
