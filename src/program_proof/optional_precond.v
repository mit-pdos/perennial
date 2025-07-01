Require Import Goose.github_com.goose_lang.std.
Require Import Perennial.goose_lang.lib.atomic.impl.
Require Import Perennial.goose_lang.lib.atomic.atomic.
Require Import Perennial.program_proof.std_proof.
Require Import Perennial.program_proof.grove_prelude.
Require Import Perennial.algebra.mono_nat.

Section proof.

Context `{!heapGS Σ}.

Definition addr : loc.
Admitted.

Definition naddr : namespace := nroot .@ "addr".

Definition get : val :=
  λ: <>,
    atomic.LoadUint64 #addr.

Definition inner γ addr : iProp Σ :=
  ∃ (v: nat),
    "Haddr" ∷ addr ↦[uint64T] #v ∗
    "Hauth" ∷ mono_nat_auth_own γ (1/2)%Qp v.

Definition get_inv γ : iProp Σ :=
  inv naddr (inner γ addr).

Theorem wp_get {γ} E Q :
  {{{ get_inv γ ∗
      ∀ x, Q x ∨
        ( |={⊤ ∖ ↑naddr,E}=>
            ∃ x0, mono_nat_lb_own γ x0 ∗
              ( mono_nat_lb_own γ x0 -∗ ⌜ x0 ≤ x ⌝ -∗ |={E,⊤ ∖ ↑naddr}=> Q x ) ) ∨
        ( |={⊤ ∖ ↑naddr,E}=>
            ∃ x0, mono_nat_auth_own γ (1/2)%Qp x0 ∗
              ( mono_nat_auth_own γ (1/2)%Qp x0 -∗ ⌜ x0 = x ⌝ -∗ |={E,⊤ ∖ ↑naddr}=> Q x ) )
  }}}
    get #()
  {{{ x, RET #x;
      Q x ∗
      mono_nat_lb_own γ x
  }}}.
Proof.
  iIntros (Φ) "[#Hinv HQ] HΦ".
  wp_rec.
  iInv "Hinv" as ">H".
  iNamed "H".
  iDestruct (mono_nat_lb_own_get with "Hauth") as "#Hlb".
  wp_apply (wp_LoadUint64 with "Haddr").
  iIntros "Haddr".
  iDestruct ("HQ" $! v) as "[HQ | [HQ | HQ]]".
  - iModIntro.
    iSplitL "Haddr Hauth".
    { iFrame. }
    iApply "HΦ". iFrame. done.
  - iMod "HQ" as (x0) "[Hprelb HQ]".
    iDestruct (mono_nat_lb_own_valid with "Hauth Hprelb") as "%Hlb".
    iMod ("HQ" with "Hprelb []") as "HQ"; first by intuition eauto.
    iModIntro.
    iSplitL "Haddr Hauth".
    { iFrame. }
    iApply "HΦ". iFrame. done.
  - iMod "HQ" as (x0) "[Hpreauth HQ]".
    iDestruct (mono_nat_auth_own_agree with "Hauth Hpreauth") as "%Heq".
    iMod ("HQ" with "Hpreauth []") as "HQ"; first by intuition eauto.
    iModIntro.
    iSplitL "Haddr Hauth".
    { iFrame. }
    iApply "HΦ". iFrame. done.
Qed.

Theorem wp_get_pre_lb γ x0 :
  {{{ get_inv γ ∗
      mono_nat_lb_own γ x0
  }}}
    get #()
  {{{ x, RET #x;
      ⌜x0 ≤ x⌝ ∗
      mono_nat_lb_own γ x
  }}}.
Proof.
  iIntros (Φ) "[#Hinv #Hlb] HΦ".
  wp_apply (wp_get _ (λ x, ⌜x0 ≤ x⌝)%I with "[$Hinv Hlb]").
  { iIntros (x).
    iRight. iLeft.
    iModIntro.
    iFrame "Hlb".
    iIntros "Hlb2 %Hlb".
    done.
  }
  iIntros (x) "[%HQ #Hlb3]".
  iApply "HΦ". iFrame "#". done.
Qed.

Theorem wp_get_pre_auth γ x :
  {{{ get_inv γ ∗
      mono_nat_auth_own γ (1/2)%Qp x
  }}}
    get #()
  {{{ RET #x;
      mono_nat_lb_own γ x
  }}}.
Proof.
  iIntros (Φ) "[#Hinv Hauth] HΦ".
  wp_apply (wp_get _ (λ x0, ⌜x0 = x⌝)%I with "[$Hinv Hauth]").
  { iIntros (x0).
    iRight. iRight.
    iModIntro.
    iFrame "Hauth".
    iIntros "Hauth %Heq".
    done.
  }
  iIntros (x0) "[%HQ #Hlb]".
  subst.
  iApply "HΦ". iFrame "#".
Qed.

Theorem wp_get_nopre γ :
  {{{ get_inv γ
  }}}
    get #()
  {{{ x, RET #x;
      mono_nat_lb_own γ x
  }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ".
  wp_apply (wp_get ⊤ (λ x, True)%I with "[$Hinv]").
  { iIntros (x). iLeft. done. }
  iIntros (x) "[_ #Hlb3]".
  iApply "HΦ". iFrame "#".
Qed.

End proof.
