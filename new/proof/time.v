From New.proof Require Import proof_prelude.
From New.generatedproof Require Export time.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import logatom.chan_au_base idiom.handoff.handoff.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : time.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) time := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) time := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop time get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    time.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init time }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
Admitted.

Local Set Default Proof Using "All".

#[local]
Lemma wp_Time__sec (t : loc) (tv : time.Time.t) :
  {{{ is_pkg_init time ∗ t ↦ tv }}}
    t @! (go.PointerType time.Time) @! "sec" #()
  {{{ (x : w64), RET #x; t ↦ tv }}}.
Proof.
  wp_start. wp_auto. wp_if_destruct; by iApply "HΦ".
Qed.

#[local]
Lemma wp_Time__unixSec (t : loc) (tv : time.Time.t) :
  {{{ is_pkg_init time ∗ t ↦ tv }}}
    t @! (go.PointerType time.Time) @! "unixSec" #()
  {{{ (x : w64), RET #x; t ↦ tv }}}.
Proof.
  wp_start. wp_auto. wp_apply (wp_Time__sec with "[$]") as "% ?". by iApply "HΦ".
Qed.

#[local]
Lemma wp_Time__nsec (t : loc) (tv : time.Time.t) :
  {{{ is_pkg_init time ∗ t ↦ tv }}}
    t @! (go.PointerType time.Time) @! "nsec" #()
  {{{ (x : w32), RET #x; True }}}.
Proof.
  wp_start. wp_auto. by iApply "HΦ".
Qed.

Lemma wp_Time__UnixNano (t : time.Time.t) :
  {{{ is_pkg_init time }}}
    t @! time.Time @! "UnixNano" #()
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
    t @! time.Time @! "Add" #d
  {{{ (t : time.Time.t), RET #t; True }}}.

Lemma wp_arbitraryTime :
  {{{ True }}}
    time.arbitraryTime #()
  {{{ (t: time.Time.t), RET #t; True }}}.
Proof.
  wp_start. wp_apply wp_ArbitraryInt as "%x _". by iApply "HΦ".
Qed.

Lemma wp_After `{!chanG Σ time.Time.t} (d : time.Duration.t) :
  {{{ is_pkg_init time }}}
    @! time.After #d
  {{{ (ch: loc) γ, RET #ch; is_chan_handoff γ ch (λ (t: time.Time.t), True)%I }}}.
Proof.
  wp_start.
  wp_apply chan.wp_make; first word.
  iIntros (ch γ) "(His & Hcap & Hown)".
  simpl.
  iMod (start_handoff _ _ (λ t, True)%I
          with "[$His] [$Hown]") as (γhandoff) "[_ #Hch]".
  wp_auto.
  wp_apply wp_fork.
  {
    wp_apply wp_arbitraryTime.
    iIntros (t) "_".
    wp_apply (wp_handoff_send with "[$Hch]"). done.
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
