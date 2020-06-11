From iris.proofmode Require Import tactics.
From Perennial.Helpers Require NamedProps ProofCaching PropRestore.

(*+ Demo of Perennial's IPM extensions +*)

Section bi.
  Context {PROP: bi} {Haff: BiAffine PROP}.

  Context (P Q R: PROP).
  Context `{!Persistent Q}.

  (*! Brief previews: *)

  (** * first extension: named propositions *)
  Import Perennial.Helpers.NamedProps.

  Definition is_foo :=
    ("HP" ∷ P ∗
     "HR" ∷ R)%I.

  Theorem is_foo_read_P :
    is_foo -∗ P.
  Proof.
    iIntros "H".
    iNamed "H".
    iExact "HP".
  Qed.

  (* there are several problems this solves:
    - you're about to destruct a definition, but don't remember what's inside,
      so you have to print it to come up with the right intro pattern
    - the names used for a definition are repeated in every into pattern rather
      than colocated with the definition (where you can see what each conjunct
      is)
    - when you change a definition all intro patterns that reference it have to
      be updated, sometimes with an obscure change (eg, add a new name in the
      5th position)
  *)

  Definition is_bar :=
    ("#HQ" ∷ Q ∗
     "HR" ∷ R)%I.

  Theorem is_bar_read_Q :
    is_bar -∗ □Q.
  Proof.
    iNamed 1.
    iModIntro.
    iExact "HQ".
  Qed.

  (** * second extension: proof caching *)
  Import Perennial.Helpers.ProofCaching.

  (* note that repetition is primarily due to the structure of cache safety
  proofs; I'm not sure where else this problem would arise *)

  Theorem repetitive_proof :
    "HPR" ∷ (P -∗ R) -∗
    "HP" ∷ P -∗
    P ∧ ("HQ" ∷ Q -∗ P) ∧ ("HQ" ∷ Q -∗ R) ∧ R.
  Proof.
    iIntros "? ?"; iNamed.
    iCache P with "HP".
    { auto. }
    iCache R with "HP HPR".
    { iApply ("HPR" with "[$]"). }
    repeat iSplit.
    - iFromCache.
    - iNamed 1.
      iFromCache.
    - iNamed 1.
      iFromCache.
    - iFromCache.
  Qed.

  (** * third extension: restore destructed prop *)
  Import Perennial.Helpers.PropRestore.

  (* note that this isn't fully implemented *)

  (* here's the problem we're trying to solve: *)
  Theorem bar_acc_R_bad_proof :
    is_bar -∗ R ∗ (R -∗ is_bar).
  Proof.
    iNamed 1.
    (* I'm not trying to demonstrate proving the first part, that's fine *)
    iSplitL "HR"; first by iFrame.
    iIntros "HR".
    (* this is the annoying part: we can't just use [iFrame] because there are
    persistent facts, too (this can get much worse when there are existentials
    and pure facts, and the order of framing means [iFrame "% # ∗"] sometimes
    doesn't work but [iFrame "∗ # %]" does...) *)
    iFrame.
    iFrame "#".
  Qed.

  Theorem bar_acc_R :
    is_bar -∗ R ∗ (R -∗ is_bar).
  Proof.
    iIntros "H".
    iDestruct (restore_intro with "H") as "H".
    iDestruct "H" as "(?&?&H)"; iNamed.
    iDestruct (restore_elim with "H") as "#His_foo"; iClear "H".
    iFrame.
    iIntros "HP".
    (* this is entirely independent of the persistent facts in is_bar *)
    iApply "His_foo"; iFrame.
  Qed.

  (* The issue with the current implementation is that [iNamed "H"] where "H" is
     a Restore doesn't do the right thing. I think NamedProps needs some
     typeclass-based extension mechanism that PropRestore can implement. *)

End bi.
