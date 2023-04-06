From Perennial.program_proof Require Import grove_prelude.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import auth dfrac_agree mono_list csum gset.
From iris.base_logic.lib Require Import mono_nat.

Section renewable_lease_protocol.

Class renewable_leaseG Σ :=
  {
    escrowG :> ghost_varG Σ () ;
    mono_natG :> mono_natG Σ ;
  }.

Context `{!gooseGlobalGS Σ}.
Context `{!renewable_leaseG Σ}.

Definition is_lease_valid_lb γl (t:u64) :=
  mono_nat_lb_own γl (int.nat t)
.

Definition own_lease_expiration γl (t:u64) :=
  mono_nat_auth_own γl (1/2) (int.nat t)
.

Definition is_lease N γl (R:iProp Σ) : iProp Σ :=
  ∃ γtok,
  inv N (∃ expirationTime, own_lease_expiration γl expirationTime ∗
         (R ∨ is_time_lb expirationTime ∗ (R ∨ ghost_var γtok 1 ())))
.

Definition post_lease N γl (R:iProp Σ) : iProp Σ :=
  ∀ expirationTime,
  own_lease_expiration γl expirationTime -∗
  is_time_lb expirationTime ={↑N}=∗
  ▷ R
.

Lemma lease_acc N e R γl t :
  int.nat t < int.nat e →
  is_lease_valid_lb γl e -∗
  is_lease N γl R -∗
  own_time t ={↑N,∅}=∗
  ▷ R ∗ (▷ R ={∅,↑N}=∗ own_time t)
.
Proof.
  iIntros (HnotExpired) "#Hlease_lb #Hlease Htime".
  iDestruct "Hlease" as (γtok) "#Hinv".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hexpiration Hi]".
  iDestruct (mono_nat_lb_own_valid with "Hexpiration Hlease_lb") as %[_ Hineq].
  iDestruct "Hi" as "[HR | [>Hbad _]]"; last first.
  {
    iDestruct (mono_nat_lb_own_valid with "Htime Hbad") as %[_ Hbad].
    exfalso. lia.
  }
  iFrame "HR".
  replace (↑N ∖ ↑N) with (∅:coPset) by set_solver.
  iModIntro.
  iIntros "HR".
  iFrame "Htime".
  iMod ("Hclose" with "[-]"); last done.
  iExists _; iFrame.
Qed.

Lemma lease_alloc e N R :
  R ={↑N}=∗
  ∃ γl,
  is_lease N γl R ∗
  post_lease N γl R ∗
  own_lease_expiration γl e
.
Proof.
  iIntros "HR".
  iMod (ghost_var_alloc ()) as (γtok) "Htok".
  iMod (mono_nat_own_alloc (int.nat e)) as (γl) "[Hexp _]".
  iDestruct "Hexp" as "[Hexp Hexp2]".
  iExists γl.
  iFrame "Hexp".
  iMod (inv_alloc with "[HR Hexp2]") as "#Hinv".
  2: {
    iSplitR "Htok".
    { iModIntro. iExists γtok. done. }
    iModIntro.
    iIntros (?) "Hexp Hlb".
    iInv "Hinv" as "Hi" "Hclose".
    iDestruct "Hi" as (?) "(>Hexp2 & Hi)".
    iDestruct (mono_nat_auth_own_agree with "Hexp Hexp2") as %[_ Hagree].
    assert (expirationTime = expirationTime0) by word.
    subst.
    iDestruct "Hi" as "[HR | (_ & [HR | >Hbad])]".
    {
      iFrame "HR". iMod ("Hclose" with "[-]"); last done.
      iExists _; iFrame.
      iRight. iFrame.
    }
    {
      iFrame. iMod ("Hclose" with "[-]"); last done.
      iExists _; iFrame.
      iRight. iFrame.
    }
    {
      iDestruct (ghost_var_valid_2 with "Hbad Htok") as %[Hbad _].
      exfalso.
      done.
    }
  }
  { iExists _. iFrame. }
Qed.

Lemma renew_lease e' γl e t N R :
  int.nat t < int.nat e →
  int.nat e <= int.nat e' →
  is_lease N γl R -∗
  own_lease_expiration γl e -∗
  own_time t ={↑N}=∗
  own_time t ∗ own_lease_expiration γl e'
.
Proof.
  intros ??.
  iIntros "#Hlease Hexp Htime".
  iDestruct "Hlease" as (γtok) "#Hinv".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hexp2 Hi]".
  iDestruct (mono_nat_auth_own_agree with "Hexp Hexp2") as %[_ Hagree].
  assert (expirationTime = e) by word.
  subst.
  iDestruct "Hi" as "[HR|[>Hbad _]]".
  2: {
    iDestruct (mono_nat_lb_own_valid with "Htime Hbad") as %[_ Hbad].
    exfalso. lia.
  }
  iCombine "Hexp Hexp2" as "Hexp".
  iMod (mono_nat_own_update with "Hexp") as "[Hexp _]".
  { instantiate (1:=int.nat e'). lia. }
  iDestruct "Hexp" as "[Hexp Hexp2]".
  iFrame.
  iMod ("Hclose" with "[-]"); last done.
  iExists _; iFrame.
Qed.

Lemma lease_get_lb γl e :
  own_lease_expiration γl e -∗
  is_lease_valid_lb γl e.
Proof. iApply mono_nat_lb_own_get. Qed.

End renewable_lease_protocol.
