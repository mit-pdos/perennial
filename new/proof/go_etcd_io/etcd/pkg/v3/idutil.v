From coqutil Require Import Z.bitblast.
Require Export New.generatedproof.go_etcd_io.etcd.pkg.v3.idutil.
Require Export New.proof.proof_prelude.
From New.proof Require Import time math sync.atomic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit math := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit idutil := define_is_pkg_init True%I.

(* FIXME: id.go says that the overflowing of cnt into timestamp is intentional
   "to extend the event window to 2^56". However, I only count 48 bits. Is that
   a typo? *)
Definition is_Generator (g : loc) (R : w64 → iProp Σ) : iProp Σ :=
  ∃ (prefix : Z),
    "#prefix" ∷ g ↦s[idutil.Generator :: "prefix"]□ (W64 (prefix * 2^48)) ∗
    "#Hinv" ∷
      inv nroot (∃ (init num_used : Z),
          "suffix" ∷ struct.field_ref_f idutil.Generator "suffix" g ↦ W64 (init + num_used) ∗
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
Lemma wp_lowbit (x : w64) :
  {{{ is_pkg_init idutil }}}
    @! idutil.lowbit #x #(W64 48)
  {{{ RET #(W64 ((uint.Z x) `mod` 2^(uint.Z 48))); True }}}.
Proof.
  wp_start as "%H". wp_auto.
  iSpecialize ("HΦ" with "[//]").
  iExactEq "HΦ". f_equal. f_equal.
  rewrite Automation.word.word_eq_iff_Z_eq.
  rewrite word.unsigned_and Automation.word.unsigned_sru'. 2:{ word. }
  repeat ereplace (uint.Z (W64 ?[a])) with (?a) by word.
  replace (uint.Z (word.sub (W64 _) _)) with (64 - 48)%Z by word.
  replace (_ `div` _) with (Z.ones (uint.Z 48)).
  2:{ vm_compute Z.ones. unfold math.MaxUint64. word. }
  rewrite Z.land_ones //. word.
Qed.

Lemma wp_Generator__Next g R :
  {{{ is_pkg_init idutil ∗ is_Generator g R }}}
    g @ (ptrT.id idutil.Generator.id) @ "Next" #()
  {{{ (i : w64), RET #i; R i }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto_lc 1. wp_bind.
  wp_apply wp_AddUint64.
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamedSuffix "Hi" "_inv".
  iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
  iFrame. iIntros "suffix_inv".
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
  wp_apply wp_lowbit. iApply "HΦ".
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
  wp_apply wp_Time__UnixNano as "%nowNano _".
  (* FIXME: wp_lowbit should *at least* support `suffixLen` and `tsLen` *)
  (*
  wp_apply wp_lowbit. wp_alloc g as "Hg".
  iApply wp_fupd. wp_auto. iApply "HΦ". iFrame "∗#".
  iDestruct (struct_fields_split with "Hg") as "Hg". iNamed "Hg".
  iPersist "Hprefix". iFrame "#".
  iMod (inv_alloc with "[Hsuffix]") as "$"; last done.
  iFrame. *)
Admitted.

End wps.
