From coqutil Require Import Z.bitblast.
Require Export New.generatedproof.go_etcd_io.etcd.pkg.v3.idutil.
Require Export New.proof.proof_prelude.
From New.proof Require Import time math sync.atomic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : idutil.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) idutil := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) idutil := build_get_is_pkg_init_wf.

(* FIXME: id.go says that the overflowing of cnt into timestamp is intentional
   "to extend the event window to 2^56". However, there are only 48 bits in the
   suffix, and the documentation is a typo from an older version of the code. *)
Definition is_Generator (g : loc) (R : w64 → iProp Σ) : iProp Σ :=
  ∃ (prefix : Z),
    "#prefix" ∷ g.[idutil.Generator.t, "prefix"] ↦□ (W64 (prefix * 2^48)) ∗
    "#Hinv" ∷
      inv nroot (∃ (init num_used : Z),
          "suffix" ∷ g.[idutil.Generator.t, "suffix"] ↦ W64 (init + num_used) ∗
          "HR" ∷ ([∗ list] i ∈ seqZ (init + num_used + 1) (2^48 - num_used),
                    R (W64 (prefix * 2^48 + i `mod` 2^48)))
      ) ∗
    "_" ∷ True.
#[global] Opaque is_Generator.
#[local] Transparent is_Generator.
#[global] Instance : ∀ s R, Persistent (is_Generator s R).
Proof. apply _. Qed.

(* Specialized to 48 low bits. *)
#[local]
Lemma wp_lowbit (x n : w64) :
  (* NOTE: need `0 < uint.Z n` because there's no guarantees about [word.sru]
     when the shift amount is the width. *)
  {{{ is_pkg_init idutil ∗ ⌜ 0 < uint.Z n < 64 ⌝ }}}
    @! idutil.lowbit #x #n
  {{{ RET #(W64 ((uint.Z x) `mod` 2^(uint.Z n))); True }}}.
Proof.
  wp_start as "%H". wp_auto.
  iSpecialize ("HΦ" with "[//]").
  iExactEq "HΦ". f_equal. f_equal.
  rewrite Automation.word.word_eq_iff_Z_eq.
  rewrite word.unsigned_and Automation.word.unsigned_sru'. 2:{ word. }
  repeat ereplace (uint.Z (W64 ?[a])) with (?a) by word.
  replace (uint.Z (word.sub (W64 _) _)) with (64 - uint.Z n)%Z by word.
  replace (_ `div` _) with (Z.ones (uint.Z n)).
  2:{
    change (uint.Z (W64 18446744073709551615)) with (Z.ones 64).
    Z.bitblast.
  }
  rewrite Z.land_ones //. word.
Qed.

Lemma wp_Generator__Next g R :
  {{{ is_pkg_init idutil ∗ is_Generator g R }}}
    g @! (go.PointerType idutil.Generator) @! "Next" #()
  {{{ (i : w64), RET #i; R i }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto_lc 1. wp_bind.
  wp_apply wp_AddUint64.
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamedSuffix "Hi" "_inv".
  iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
  iFrame. iIntros "!> suffix_inv".
  ereplace (word.add ?[a] ?[b]) with (W64 (init + (num_used + 1))) by word.
  rewrite seqZ_cons.
  2:{ admit. } (* TODO: requires knowing that there are fewer than 2^56 calls to [Next]. *)
  iDestruct "HR_inv" as "[HR HR_inv]".
  iMod "Hmask". iMod ("Hclose" with "[suffix_inv HR_inv]") as "_".
  {
    ereplace (Z.succ (?[a] + ?[b] + 1)) with (?a + (?b + 1) + 1) by word.
    ereplace (Z.pred (?[a] - ?[b])) with (?a - (?b + 1)) by word.
    iFrame.
  }
  iModIntro.
  wp_auto.
  unfold idutil.suffixLen.
  wp_apply wp_lowbit; first word.
  iApply "HΦ".
  iExactEq "HR". f_equal.
  rewrite Automation.word.word_eq_iff_Z_eq.
  rewrite word.unsigned_or.
  rewrite -Z.add_nocarry_lor.
  2:{
    Z.bitblast.
    destruct (decide (i < 48)).
    - apply andb_false_intro1.
      rewrite Z.testbit_mod_pow2 // Z.mul_pow2_bits_low //. lia.
    - apply andb_false_intro2.
      unfold idutil.suffixLen.
      ereplace (uint.Z (W64 ?[a])) with ?a by word.
      rewrite Z.testbit_mod_pow2 //.
      apply andb_false_intro1. word.
  }
  word.
Admitted. (* overflow *)

(* TODO: this is overly conservative. Really should only demand [R] for the
   range of IDs with future timestamps, since the old ones might've been used
   before a crash+restart. *)
Lemma wp_NewGenerator R (memberID : w16) (now : time.Time.t) :
  {{{
      is_pkg_init idutil ∗
      ([∗ list] i ∈ seqZ 0 (2^64), R (W64 i))
  }}}
    @! idutil.NewGenerator #memberID #now
  {{{ g, RET #g; is_Generator g R }}}.
Proof.
  wp_start as "HR". wp_auto.
  wp_method_call. wp_auto.
  wp_apply wp_Time__UnixNano as "%nowNano _".
  rewrite /idutil.tsLen /idutil.cntLen /idutil.suffixLen.
  wp_apply wp_lowbit; first word. wp_alloc g as "Hg".
  iApply wp_fupd. wp_auto. iApply "HΦ". iFrame "∗#".
  iStructNamedPrefix "Hg" "H". iPersist "Hprefix".
  iMod (inv_alloc with "[Hsuffix HR]") as "$".
  { iEval (simpl) in "Hsuffix". iExists _, 0. iNext.
    iSplitL "Hsuffix".
    { iApply to_named. iExactEq "Hsuffix". ereplace (?[a] + 0) with ?a by word.
      f_equal.
      instantiate (1:=(uint.Z ?[x])).
      setoid_rewrite (word.of_Z_unsigned ?x).
      done.
    }
    rewrite -big_sepS_list_to_set.
    2:{ apply NoDup_seqZ. }
    rewrite -big_sepS_list_to_set.
    2:{ apply NoDup_seqZ. }
    admit. (* TODO: use the given R to prove the invariant's Rs. *)
  }
  iModIntro. iApply to_named.
  iExactEq "Hprefix".
  f_equal. simpl. instantiate (1:=uint.Z memberID).
  word.
Admitted.

End wps.
