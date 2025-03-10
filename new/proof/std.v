From New.proof Require Import proof_prelude.
From New.code.github_com.goose_lang Require Import std.
Require Export New.generatedproof.github_com.goose_lang.std.
From New.proof Require Import primitive sync.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!std.GlobalAddrs}.

(** NOTE:
  The discipline followed by other proofs so far has been to define
  [is_initialized] to require [is_defined] of the current package, but the
  [is_initialized] of all the imported packages (as opposed to [primitive.is_defined],
  it would be [primitive.is_initialized]).

  A package's [is_initialized] predicate is meant to include not only the
  systematic [is_defined] predicate, but also custom logical facts written by
  the proof developer (e.g. some packages initialize global variables to hold a
  read-only error value that gets used by functions in the package).

  [is_initialized] is intended to cover the entire precondition relating to
  all package initialization (e.g. the [sync.is_defined ∗
  atomic.is_initialized] in [wp_JoinHandle__finish] below should be part of
  [is_initialized]).

  Another pattern in the other proofs is to include [is_initialized] in the
  predicate associated to every object in this package. E.g. [is_JoinHandle]
  could have [is_initialized] in it, so [wp_JoinHandle__finish] doesn't even need
  to mention [is_initialized]. Explicit [is_initialized] would only be needed
  for specs that don't have a package object in the precondition. This might not
  be that great, since it increases the "entropy" of specs (sometimes you write
  [is_initialized], and sometimes you don't).

  We should eventually make all the proofs follow the same discipline for
  initialization-related predicates, whether it's more like this proof or the
  other proofs. It would be even nicer if the framework could enforce the
  discipline somehow (e.g. maybe the imported packages' [is_initialized] gets
  automatically included here).
 *)
#[global]
Program Instance : IsPkgInit std :=
  ltac2:(build_pkg_init ()).
Final Obligation. apply _. Qed.

Lemma wp_Assert (cond : bool) :
  {{{ is_pkg_init std ∗ ⌜cond = true⌝ }}}
    func_call #std #"Assert" #cond
  {{{ RET #(); True }}}.
Proof.
  wp_start as "%". subst.
  wp_auto.
  by iApply "HΦ".
Qed.

Lemma wp_SumNoOverflow (x y : u64) :
  {{{ is_pkg_init std }}}
    func_call #std #"SumNoOverflow" #x #y
  {{{ RET #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)); True }}}.
Proof.
  wp_start as "_".
  wp_auto.
  iSpecialize ("HΦ" with "[$]").
  iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  pose proof (sum_overflow_check x y).
  word.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) :
  {{{ is_pkg_init std }}}
    func_call #std #"SumAssumeNoOverflow" #x #y
  {{{ RET #(word.add x y); ⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply wp_SumNoOverflow.
  wp_auto.
  wp_apply wp_Assume. rewrite bool_decide_eq_true.
  iIntros (?). wp_auto.
  iApply "HΦ". iPureIntro. done.
Qed.

Definition is_JoinHandle (l: loc) (P: iProp Σ): iProp _ :=
  ∃ (mu_l cond_l: loc),
  "#mu" ∷ l ↦s[std.JoinHandle :: "mu"]□ mu_l ∗
  "#cond" ∷ l ↦s[std.JoinHandle :: "cond"]□ cond_l ∗
  "#Hcond" ∷ is_Cond cond_l (interface.mk sync "Mutex'ptr"%go #mu_l) ∗
  "#Hlock" ∷ is_Mutex mu_l
     (∃ (done_b: bool),
         "done_b" ∷ l ↦s[std.JoinHandle :: "done"] done_b ∗
         "HP" ∷ if done_b then P else True)
.

Lemma wp_newJoinHandle (P: iProp Σ) :
  {{{ is_pkg_init std }}}
    func_call #std #"newJoinHandle" #()
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_alloc mu as "?".
  wp_auto.
  wp_apply (wp_NewCond with "[#]").
  iIntros (cond) "#His_cond".
  wp_auto.
  wp_alloc jh_l as "jh".
  iApply struct_fields_split in "jh". simpl. iNamed "jh".
  iMod (typed_pointsto_persist with "Hmu") as "Hmu".
  iMod (typed_pointsto_persist with "Hcond") as "Hcond".
  iMod (init_Mutex (∃ (done_b: bool),
         "done_b" ∷ jh_l ↦s[std.JoinHandle :: "done"] done_b ∗
         "HP" ∷ if done_b then P else True)
         with "[] [$] [Hdone]") as "Hlock".
  { iPkgInit. }
  { iNext.
    iFrame.
  }
  wp_auto.
  iApply "HΦ".
  rewrite /is_JoinHandle.
  iFrame "His_cond". iFrame.
Qed.

Lemma wp_JoinHandle__finish l (P: iProp Σ) :
  {{{ is_pkg_init std ∗ is_JoinHandle l P ∗ P }}}
    method_call #std #"JoinHandle'ptr" #"finish" #l #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[Hhandle P]".
  iNamed "Hhandle".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[locked Hinv]". iNamed "Hinv".
  wp_auto.
  wp_apply (wp_Cond__Signal with "[$Hcond]").
  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$Hlock $locked done_b P]").
  { iFrame "done_b P". }
  wp_auto.
  iApply "HΦ".
  done.
Qed.

Lemma wp_Spawn (P: iProp Σ) (f : func.t) :
  {{{ is_pkg_init std ∗
        (∀ Φ, ▷(P -∗ Φ #()) -∗ WP #f #() {{ Φ }}) }}}
  func_call #std #"Spawn" #f
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  wp_start as "Hwp".
  wp_auto.
  wp_apply (wp_newJoinHandle P).
  iIntros (l) "#Hhandle". wp_auto.
  iMod (typed_pointsto_persist with "[$]") as "#?".
  iMod (typed_pointsto_persist with "[$]") as "#?".
  wp_bind (Fork _).
  iApply (wp_fork with "[Hwp]").
  - iModIntro. wp_auto.
    (* NOTE: it's important not to do a pure reduction here since it would
    produce a substitution into the lambda *)
    wp_apply "Hwp".
    iIntros "HP".
    wp_auto.
    wp_apply (wp_JoinHandle__finish with "[$Hhandle $HP]").
    wp_auto.
    done.
  - iModIntro.
    wp_auto.
    iApply "HΦ".
    iFrame "#".
Qed.

Lemma wp_JoinHandle__Join l P :
  {{{ is_pkg_init std ∗ is_JoinHandle l P }}}
    method_call #std #"JoinHandle'ptr" #"Join" #l #()
  {{{ RET #(); P }}}.
Proof.
  wp_start as "Hjh". iNamed "Hjh".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[Hlocked Hlinv]". iNamed "Hlinv".
  wp_auto.

  iAssert (∃ (done_b: bool),
           "locked" ∷ own_Mutex mu_l ∗
           "done" ∷ l ↦s[std.JoinHandle::"done"] done_b ∗
           "HP" ∷ (if done_b then P else True))%I
          with "[$Hlocked $done_b $HP]" as "HI".
  wp_for. iNamed "HI". wp_auto.
  rewrite decide_True //.
  wp_auto.
  destruct done_b0; wp_auto.
  - iApply wp_for_post_break.
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $locked $done]").
    wp_auto. iApply "HΦ". done.
  - wp_apply (wp_Cond__Wait with "[$Hcond locked done HP]").
    { iSplit.
      - iApply (Mutex_is_Locker with "Hlock").
      - iFrame. }
    iIntros "[Hlocked Hlinv]". iNamed "Hlinv".
    wp_auto.
    iApply wp_for_post_do.
    wp_auto.
    iFrame.
Qed.

End wps.
