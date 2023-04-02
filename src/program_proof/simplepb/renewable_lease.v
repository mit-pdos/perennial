From Perennial.program_proof Require Import grove_prelude.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import auth dfrac_agree mono_list csum gset.
From Perennial.goose_lang.ffi Require Export grove_ffi_time_axiom.

Section renewable_lease_protocol.

Context `{!heapGS Σ}.
Context `{invGS Σ}.
Context `{γtime:gname}.
Context `{!ghost_varG Σ ()}.

Notation is_time_lb := (is_time_lb γtime).
Notation own_time := (own_time γtime).

Definition isLease N (expirationTime:u64) (R:iProp Σ) : iProp Σ :=
  ∃ γtok,
  inv N (R ∨ is_time_lb expirationTime ∗ (R ∨ ghost_var γtok 1 ())).

Definition postLease N (expirationTime:u64) (R:iProp Σ) : iProp Σ :=
  is_time_lb expirationTime ={↑N}=∗ ▷ R
.

Lemma lease_acc N e R t :
  int.nat t < int.nat e →
  isLease N e R -∗
  £ 1 -∗
  own_time t ={↑N,∅}=∗
  R ∗ (R ={∅,↑N}=∗ own_time t)
.
Proof.
  iIntros (HnotExpired) "#Hlease Hlc Htime".
  iDestruct "Hlease" as (γtok) "#Hinv".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iDestruct "Hi" as "[HR | [Hbad _]]"; last first.
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
  by iLeft.
Qed.

Lemma lease_alloc e N R :
  R ={↑N}=∗
  isLease N e R ∗
  postLease N e R
.
Proof.
  iIntros "HR".
  iMod (ghost_var_alloc ()) as (γtok) "Htok".
  iMod (inv_alloc with "[HR]") as "#Hinv".
  2: {
    iSplitR "Htok".
    { iModIntro. iExists γtok. done. }
    iModIntro.
    iIntros "Hlb".
    iInv "Hinv" as "Hi" "Hclose".
    iDestruct "Hi" as "[HR | (_ & [HR | >Hbad])]".
    {
      iFrame "HR". iMod ("Hclose" with "[-]"); last done.
      iRight. iFrame.
    }
    {
      iFrame. iMod ("Hclose" with "[-]"); last done.
      iRight. iFrame.
    }
    {
      iDestruct (ghost_var_valid_2 with "Hbad Htok") as %[Hbad _].
      exfalso.
      done.
    }
  }
  { by iLeft. }
Qed.

End renewable_lease_protocol.
