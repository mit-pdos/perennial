From Perennial.program_proof Require Import grove_prelude.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import auth dfrac_agree mono_list csum gset.
From iris.base_logic.lib Require Import mono_nat.

Section renewable_lease_protocol.

Class renewable_leaseG Σ :=
  {
    #[global] escrowG :: ghost_varG Σ () ;
    #[global] mono_natG :: mono_natG Σ ;
  }.

Definition renewable_leaseΣ := #[ghost_varΣ () ; mono_natΣ ].

Global Instance subG_renewable_leaseΣ {Σ} : subG renewable_leaseΣ Σ → renewable_leaseG Σ.
Proof. intros. solve_inG. Qed.

Context `{!gooseGlobalGS Σ}.
Context `{!renewable_leaseG Σ}.

Definition is_lease_valid_lb γl (t:u64) :=
  mono_nat_lb_own γl (uint.nat t)
.

Definition own_lease_expiration γl (t:u64) :=
  mono_nat_auth_own γl (1/2) (uint.nat t)
.

Local Definition is_lease_inv N γl γtok R : iProp Σ :=
  inv N (∃ expirationTime, own_lease_expiration γl expirationTime ∗
         (R ∨ is_time_lb expirationTime ∗ ghost_var γtok 1 ()))
.

Definition is_lease N γl (R:iProp Σ) : iProp Σ :=
  ∃ γtok, is_lease_inv N γl γtok R
.

Definition post_lease N γl (R:iProp Σ) : iProp Σ :=
  ∃ γtok, ghost_var γtok 1 () ∗ is_lease_inv N γl γtok R.

Lemma lease_acc N e R γl t {E} :
  ↑N ⊆ E →
  uint.nat t < uint.nat e →
  is_lease_valid_lb γl e -∗
  is_lease N γl R -∗
  own_time t ={E,E∖↑N}=∗
  ▷ R ∗ (▷ R ={E∖↑N,E}=∗ own_time t)
.
Proof.
  iIntros (? HnotExpired) "#Hlease_lb #Hlease Htime".
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
  iMod (mono_nat_own_alloc (uint.nat e)) as (γl) "[Hexp _]".
  iDestruct "Hexp" as "[Hexp Hexp2]".
  iExists γl.
  iFrame "Hexp".
  iMod (inv_alloc with "[HR Hexp2]") as "#Hinv".
  2: {
    iSplitR "Htok".
    { iModIntro. iExists γtok. done. }
    iModIntro.
    iExists _; iFrame "∗#".
  }
  { iExists _. iFrame. }
Qed.

Lemma lease_renew e' γl e N R :
  uint.nat e <= uint.nat e' →
  own_lease_expiration γl e -∗
  post_lease N γl R
  ={↑N}=∗
  post_lease N γl R ∗
  own_lease_expiration γl e'
.
Proof.
  intros ?.
  iIntros "Hexp Hpost".
  iDestruct "Hpost" as (γtok) "[Htok #Hinv]".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hexp2 Hi]".
  iDestruct (mono_nat_auth_own_agree with "Hexp Hexp2") as %[_ Hagree].
  assert (expirationTime = e) by word.
  subst.
  iDestruct "Hi" as "[HR|>[_ Hbad2]]".
  2: {
    iCombine "Hbad2 Htok" gives %[? _].
    exfalso. done.
  }
  iCombine "Hexp Hexp2" as "Hexp".
  iMod (mono_nat_own_update with "Hexp") as "[Hexp _]".
  { instantiate (1:=uint.nat e'). lia. }
  iDestruct "Hexp" as "[Hexp Hexp2]".
  iFrame "Hexp2".
  iMod ("Hclose" with "[-Htok]"); by iFrame.
Qed.

Lemma lease_expire e N γl (R:iProp Σ) :
  own_lease_expiration γl e -∗
  post_lease N γl R -∗
  is_time_lb e ={↑N}=∗
  ▷ R
.
Proof.
  iIntros "Hexp Hpost Hlb".
  iDestruct "Hpost" as (?) "[Htok Hinv]".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "(>Hexp2 & Hi)".
  iDestruct (mono_nat_auth_own_agree with "Hexp Hexp2") as %[_ Hagree].
  assert (expirationTime = e) by word.
  subst.
  iDestruct "Hi" as "[HR |>[_ Hbad]]".
  {
    iFrame "HR". iMod ("Hclose" with "[-]"); last done.
    iExists _; iFrame.
    iRight. iFrame.
  }
  {
    iDestruct (ghost_var_valid_2 with "Hbad Htok") as %[Hbad _].
    exfalso.
    done.
  }
Qed.

Lemma post_lease_acc N R γl {E} :
  ↑N ⊆ E →
  post_lease N γl R ={E,E∖↑N}=∗
  ▷ R ∗ (▷ R ={E∖↑N,E}=∗ post_lease N γl R)
.
Proof.
  iIntros (?) "Hpost".
  iDestruct "Hpost" as (?) "[Htok #Hinv]".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hexpiration Hi]".
  iDestruct "Hi" as "[HR | [_ >Hbad]]"; last first.
  {
    iCombine "Htok Hbad" gives %[Hbad _].
    exfalso. done.
  }
  iFrame "HR".
  iModIntro.
  iIntros "HR".
  iExists _; iFrame "∗#".
  iMod ("Hclose" with "[-]"); last done.
  iExists _; iFrame.
Qed.

Lemma post_get_lease R N γl :
  post_lease N γl R -∗ is_lease N γl R.
Proof.
  iIntros "(% & ? & ?)". iExists _. iFrame.
Qed.

Lemma lease_get_lb γl e :
  own_lease_expiration γl e -∗
  is_lease_valid_lb γl e.
Proof. iApply mono_nat_lb_own_get. Qed.

Lemma lease_lb_mono γl e e' :
  uint.nat e' <= uint.nat e →
  is_lease_valid_lb γl e -∗
  is_lease_valid_lb γl e'.
Proof. intros. by iApply mono_nat_lb_own_le. Qed.

End renewable_lease_protocol.
