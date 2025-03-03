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
Definition is_initialized : iProp Σ :=
  "#?" ∷ std.is_defined ∗
  "#?" ∷ primitive.is_defined.

Lemma wp_Assert (cond : bool) :
  {{{ is_initialized ∗ ⌜cond = true⌝ }}}
    func_call #std.pkg_name' #"Assert" #cond
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[init %] HΦ". iNamed "init".
  subst.
  wp_func_call; wp_call; wp_pures.
  wp_alloc b_l as "b".
  wp_pures. wp_load. wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_SumNoOverflow (x y : u64) :
  {{{ is_initialized }}}
    func_call #std.pkg_name' #"SumNoOverflow" #x #y
  {{{ RET #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)); True }}}.
Proof.
  iIntros (Φ) "#Hi HΦ".
  iNamed "Hi".
  wp_func_call.
  wp_call.
  wp_alloc y_ptr as "Hy".
  wp_pures.
  wp_alloc x_ptr as "Hx".
  wp_pures. wp_load. wp_load. wp_load. wp_pures.
  iSpecialize ("HΦ" with "[$]").
  iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  pose proof (sum_overflow_check x y).
  destruct (decide (uint.Z x ≤ uint.Z (word.add x y))); intuition idtac.
  - word.
  - word.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) :
  {{{ is_initialized }}}
    func_call #std.pkg_name' #"SumAssumeNoOverflow" #x #y
  {{{ RET #(word.add x y); ⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ }}}.
Proof.
  iIntros "* #Hi HΦ". iNamed "Hi". wp_func_call. wp_call.
  wp_alloc y_ptr as "Hy".
  wp_pures.
  wp_alloc x_ptr as "Hx".
  wp_pures. wp_load. wp_pures. wp_load.
  wp_pures. wp_apply (wp_SumNoOverflow with "[$]").
  wp_pures.
  wp_apply (wp_Assume with "[$]").
  rewrite bool_decide_eq_true.
  iIntros (?). wp_pures. do 2 wp_load. wp_pures.
  iApply "HΦ". iPureIntro. done.
Qed.

Definition is_JoinHandle (l: loc) (P: iProp Σ): iProp _ :=
  ∃ (mu_l cond_l: loc),
  "#mu" ∷ l ↦s[std.JoinHandle :: "mu"]□ mu_l ∗
  "#cond" ∷ l ↦s[std.JoinHandle :: "cond"]□ cond_l ∗
  "#Hcond" ∷ is_Cond cond_l (interface.mk sync.pkg_name' "Mutex'ptr"%go #mu_l) ∗
  "#Hlock" ∷ is_Mutex mu_l
     (∃ (done_b: bool),
         "done_b" ∷ l ↦s[std.JoinHandle :: "done"] done_b ∗
         "HP" ∷ if done_b then P else True)
.

Lemma wp_newJoinHandle (P: iProp Σ) :
  {{{ is_initialized ∗ sync.is_initialized }}}
    func_call #std.pkg_name' #"newJoinHandle" #()
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  iIntros (Φ) "[#Hi #?] HΦ". iNamed "Hi". wp_func_call. wp_call.
  wp_alloc mu_l as "mu"; wp_pures.
  wp_alloc m as "m"; wp_pures.
  wp_store; wp_pures.
  wp_alloc cond_l as "cond"; repeat (wp_load || wp_pures).
  wp_apply (wp_NewCond with "[#]").
  { iFrame "#". }
  iIntros (cond) "#His_cond".
  repeat (wp_pures || wp_store || wp_load).
  iMod (typed_pointsto_persist with "mu") as "mu".
  iMod (typed_pointsto_persist with "cond") as "cond".
  wp_alloc jh_l as "jh".
  iApply struct_fields_split in "jh". simpl. iNamed "jh".
  iMod (typed_pointsto_persist with "Hmu") as "Hmu".
  iMod (typed_pointsto_persist with "Hcond") as "Hcond".
  iMod (init_Mutex (∃ (done_b: bool),
         "done_b" ∷ jh_l ↦s[std.JoinHandle :: "done"] done_b ∗
         "HP" ∷ if done_b then P else True)
         with "[//] m [Hdone]") as "Hlock".
  { iNext.
    iFrame.
  }
  wp_pures.
  iApply "HΦ".
  rewrite /is_JoinHandle.
  iFrame "His_cond". iFrame.
Qed.

Lemma wp_JoinHandle__finish l (P: iProp Σ) :
  {{{ is_initialized ∗ sync.is_defined ∗ atomic.is_initialized ∗ is_JoinHandle l P ∗ P }}}
    method_call #std.pkg_name' #"JoinHandle'ptr" #"finish" #l #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(#init & #? & #? & #Hhandle & P)". iNamed "init".
  iNamed "Hhandle".
  wp_method_call. wp_call.
  wp_alloc h_l as "h". repeat (wp_pures || wp_load).
  wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[locked Hinv]". iNamed "Hinv".
  repeat (wp_pures || wp_load || wp_store).
  wp_apply (wp_Cond__Signal with "[$Hcond]").
  { iFrame "#". }
  repeat (wp_pures || wp_load).
  wp_apply (wp_Mutex__Unlock with "[$Hlock $locked done_b P]").
  { iFrame "done_b P". }
  wp_pures.
  iApply "HΦ".
  done.
Qed.

Lemma wp_Spawn (P: iProp Σ) (f : func.t) :
  {{{ is_initialized ∗ sync.is_defined ∗ atomic.is_initialized ∗
        (∀ Φ, ▷(P -∗ Φ #()) -∗ WP #f #() {{ Φ }}) }}}
  func_call #std.pkg_name' #"Spawn" #f
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  iIntros (Φ) "(#init & #? & #? & Hwp) HΦ". iNamed "init".
  wp_func_call; wp_call.
  wp_alloc f_l as "f"; wp_pures.
  wp_alloc h_l as "h"; wp_pures.
  iMod (typed_pointsto_persist with "f") as "#f".
  wp_apply (wp_newJoinHandle P).
  { iFrame "#". }
  iIntros (l) "#Hhandle".
  repeat (wp_load || wp_store || wp_pures).
  iMod (typed_pointsto_persist with "h") as "#h".
  wp_bind (Fork _).
  iApply (wp_fork with "[Hwp]").
  - iModIntro. wp_pures. wp_load.
    (* NOTE: it's important not to do a pure reduction here since it would
    produce a substitution into the lambda *)
    wp_apply "Hwp".
    iIntros "HP".
    wp_pures. wp_load.
    wp_apply (wp_JoinHandle__finish with "[$Hhandle $HP]").
    { iFrame "#". }
    wp_pures.
    done.
  - iModIntro.
    repeat (wp_pures || wp_load).
    iApply "HΦ".
    iFrame "#".
Qed.

Lemma wp_JoinHandle__Join l P :
  {{{ is_initialized ∗ sync.is_defined ∗ is_JoinHandle l P }}}
    method_call #std.pkg_name' #"JoinHandle'ptr" #"Join" #l #()
  {{{ RET #(); P }}}.
Proof.
  iIntros (Φ) "(#init & #? & Hjh) HΦ". iNamed "init". iNamed "Hjh".
  wp_method_call. wp_call.
  wp_alloc h_l as "h"; wp_pures.
  repeat (wp_load || wp_pures).
  wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[Hlocked Hlinv]". iNamed "Hlinv".
  wp_pures.

  iAssert (∃ (done_b: bool),
           "locked" ∷ own_Mutex mu_l ∗
           "done" ∷ l ↦s[std.JoinHandle::"done"] done_b ∗
           "HP" ∷ (if done_b then P else True))%I
          with "[$Hlocked $done_b $HP]" as "HI".
  wp_for. iNamed "HI". wp_pures.
  rewrite decide_True //.
  repeat (wp_pures || wp_load).
  destruct done_b0; repeat (wp_pures || wp_load || wp_store).
  - iApply wp_for_post_break.
    repeat (wp_pures || wp_load || wp_store).
    wp_apply (wp_Mutex__Unlock with "[$Hlock $locked $done]").
    wp_pures. iApply "HΦ". done.
  - wp_apply (wp_Cond__Wait with "[$Hcond locked done HP]").
    { iSplit.
      - iApply (Mutex_is_Locker with "Hlock").
      - iFrame. }
    iIntros "[Hlocked Hlinv]". iNamed "Hlinv".
    wp_pures.
    iApply wp_for_post_do.
    repeat (wp_pures || wp_load || wp_store).
    iFrame.
Qed.

End wps.
