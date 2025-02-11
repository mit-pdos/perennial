From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Import weakestpre.

Require Export New.code.sync.
From New.proof Require Import proof_prelude.
From Perennial.algebra Require Import map.
Require Export New.generatedproof.sync.

From New.proof Require Import sync.atomic.

Set Default Proof Using "Type".

Class syncG Σ := {
    #[global] wg_tokG :: mapG Σ u64 unit;
    #[global] wg_totalG :: ghost_varG Σ u64
  }.

Definition syncΣ := #[mapΣ u64 unit ; ghost_varΣ u64].
Global Instance subG_syncΣ{Σ} : subG (syncΣ) Σ → (syncG Σ).
Proof. solve_inG. Qed.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Section proof.
Context `{!heapGS Σ} `{!syncG Σ}.
Context `{!goGlobalsGS Σ}.
Context `{sync.GlobalAddrs}.

Definition is_initialized : iProp Σ :=
  "#?" ∷ sync.is_defined ∗
  "#?" ∷ atomic.is_initialized
.

(** This means [m] is a valid mutex with invariant [R]. *)
Definition is_Mutex (m: loc) (R : iProp Σ) : iProp Σ :=
  "#Hi" ∷ is_initialized ∗
  "#Hinv" ∷ inv nroot (
        ∃ b : bool,
          (m ↦s[ sync.Mutex :: "state" ]{# 1/4} b) ∗
                  if b then True else
                    m ↦s[sync.Mutex :: "state"]{# 3/4} b ∗ R
        ).

(** This resource denotes ownership of the fact that the Mutex is currently
    locked. *)
Definition own_Mutex (m: loc) : iProp Σ := m ↦s[sync.Mutex :: "state"]{# 3/4} true.

Lemma own_Mutex_exclusive (m : loc) : own_Mutex m -∗ own_Mutex m -∗ False.
Proof.
  iIntros "H1 H2".
  iCombine "H1 H2" gives %[Hbad _].
  exfalso.
  rewrite go_type_size_unseal in Hbad. naive_solver.
  (* FIXME: don't want to unseal go_type_size_unseal *)
Qed.

Global Instance is_Mutex_ne m : NonExpansive (is_Mutex m).
Proof. solve_proper. Qed.

(** The main proofs. *)
Global Instance is_Mutex_persistent m R : Persistent (is_Mutex m R).
Proof. apply _. Qed.
Global Instance locked_timeless m : Timeless (own_Mutex m).
Proof. apply _. Qed.

Lemma struct_val_aux_cons decls f t fvs :
  (struct.val_aux (structT $ (f,t) :: decls) fvs) =
  (default (zero_val t) (alist_lookup_f f fvs), (struct.val_aux (structT decls) fvs))%V.
Proof. rewrite struct.val_aux_unseal //=. Qed.

Lemma struct_val_aux_nil fvs :
  (struct.val_aux (structT $ []) fvs) = #().
Proof. rewrite struct.val_aux_unseal //=. Qed.

Lemma flatten_struct_tt :
  flatten_struct (# ()%V) = [].
Proof. rewrite to_val_unseal //=. Qed.

Theorem init_Mutex R E m : is_initialized -∗ m ↦ (default_val Mutex.t) -∗ ▷ R ={E}=∗ is_Mutex m R.
Proof.
  iIntros "#Hi Hl HR".
  simpl.
  iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl".
  simpl.
  iFrame "#".
  iMod (inv_alloc nroot _ (_) with "[Hstate HR]") as "#?".
  2:{ by iFrame "#". }
  { iIntros "!>". iExists false. iFrame.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hstate".
    iDestruct "Hstate" as "[$$]".
  }
Qed.

Lemma wp_Mutex__Lock m R :
  {{{ is_Mutex m R }}}
    method_call #sync.pkg_name' #"Mutex'ptr" #"Lock" #m #()
  {{{ RET #(); own_Mutex m ∗ R }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H". iNamed "Hi".
  iLöb as "IH".
  wp_method_call. wp_call.
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv nroot as ([]) "[Hl HR]".
  - wp_bind (CmpXchg _ _ _).
    iApply (wp_typed_cmpxchg_fail (V:=bool) with "[$]").
    { done. }
    { naive_solver. }
    iNext.
    iIntros "Hl".
    iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
    wp_pures.
    by iApply "IH".
  - iDestruct "HR" as "[Hl2 HR]".
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    wp_bind (CmpXchg _ _ _).
    iApply (wp_typed_cmpxchg_suc (V:=bool) with "[$]").
    { constructor. }
    { done. }
    iNext. iIntros "Hl".
    iModIntro.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iSplitL "Hl1"; first (iNext; iExists true; eauto).
    rewrite /locked. wp_pures.
    iApply "HΦ".
    eauto with iFrame.
Qed.

(* this form is useful for defer statements *)
Lemma wp_Mutex__Unlock' m :
  {{{ is_initialized }}}
    method_call #sync.pkg_name' #"Mutex'ptr" #"Unlock" #m
  {{{ (f : func.t), RET #f;
      ∀ R,
    {{{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}} #f #() {{{ RET #(); True }}}
  }}}.
Proof.
  iIntros (Ψ) "#Hdef HΨ".
  iNamed "Hdef".
  wp_method_call. wp_call.
  iApply "HΨ". iIntros (R).
  iIntros (Φ) "!# (#His & Hlocked & HR) HΦ".
  iNamed "His".
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv nroot as (b) "[>Hl _]".

  unfold own_Mutex.
  iCombine "Hl Hlocked" gives %[_ [=]]. subst.
  iCombine "Hl Hlocked" as "Hl".
  rewrite Qp.quarter_three_quarter.
  iApply (wp_typed_cmpxchg_suc (V:=bool) with "[$]").
  { econstructor. }
  { econstructor. }
  iIntros "!# Hl".
  iModIntro.
  iSplitR "HΦ"; last by wp_pures; iApply "HΦ".
  iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
  iDestruct "Hl" as "[Hl1 Hl2]".
  iNext. iExists false. iFrame.
Qed.

Lemma wp_Mutex__Unlock m R :
  {{{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}}
    method_call #sync.pkg_name' #"Mutex'ptr" #"Unlock" #m #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hinv & Hlocked & HR) HΦ".
  wp_bind (method_call _ _ _ #m)%E.
  iNamed "Hinv".
  wp_apply (wp_Mutex__Unlock' with "[$]"). iIntros (?) "Hspec".
  wp_apply ("Hspec" with "[$Hinv $Hlocked $HR $Hi]").
  by iApply "HΦ".
Qed.

Definition is_Locker (i : interface.t) (P : iProp Σ) : iProp Σ :=
  "#H_Lock" ∷ ({{{ True }}} (interface.get #"Lock" #i) #() {{{ RET #(); P }}}) ∗
  "#H_Unlock" ∷ ({{{ P }}} (interface.get #"Unlock" #i) #() {{{ RET #(); True }}})
.

Global Instance is_Locker_persistent v P : Persistent (is_Locker v P) := _.

Lemma Mutex_is_Locker (m : loc) R :
  is_Mutex m R -∗
  is_Locker (interface.mk sync.pkg_name' "Mutex'ptr"%go #m) (own_Mutex m ∗ R).
Proof.
  iIntros "#[? ?]".
  iSplitL.
  - iIntros (?) "!# _ HΦ".
    wp_pures.
    by wp_apply (wp_Mutex__Lock with "[$]").
  - iIntros (?) "!# [? ?] HΦ".
    wp_pures.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "#∗". }
    by iApply "HΦ".
Qed.

(** This means [c] is a condvar with underyling Locker at address [m]. *)
Definition is_Cond (c : loc) (m : interface.t) : iProp Σ :=
  "#Hi" ∷ is_initialized ∗
  "#Hc" ∷ c ↦s[sync.Cond :: "L"]□ m.

Global Instance is_Cond_persistent c m : Persistent (is_Cond c m) := _.

Theorem wp_NewCond (m : interface.t) :
  {{{ is_initialized }}}
    func_call #sync.pkg_name' #"NewCond" #m
  {{{ (c: loc), RET #c; is_Cond c m }}}.
Proof.
  iIntros (Φ) "#Hdef HΦ". iNamed "Hdef".
  wp_func_call. wp_call. wp_apply wp_fupd.
  wp_alloc c as "Hc".
  wp_pures.
  iApply "HΦ".

  iDestruct (struct_fields_split with "Hc") as "Hl".
  iNamed "Hl".
  iMod (typed_pointsto_persist with "HL") as "$".
  iFrame "#". done.
Qed.

Theorem wp_Cond__Signal c lk :
  {{{ is_initialized ∗ is_Cond c lk }}}
    method_call #sync.pkg_name' #"Cond'ptr" #"Signal" #c #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#Hdef Hc] HΦ". iNamed "Hdef".
  wp_method_call. wp_call. iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    method_call #sync.pkg_name' #"Cond'ptr" #"Broadcast" #c #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hi".
  wp_method_call. wp_call. iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Locker m R ∗ R }}}
    method_call #sync.pkg_name' #"Cond'ptr" #"Wait" #c #()
  {{{ RET #(); R }}}.
Proof.
  iIntros (Φ) "(#Hcond & #Hlock & HR) HΦ".
  iNamed "Hcond". iNamed "Hi".
  wp_method_call. wp_call.
  iNamed "Hlock".
  wp_load.
  wp_apply ("H_Unlock" with "[$]").
  wp_pures.
  wp_load.
  wp_apply ("H_Lock" with "[$]").
  iIntros "HR".
  wp_pures.
  iApply "HΦ". done.
Qed.

Definition own_WaitGroup (wg : loc) (counter : w64) : iProp Σ :=
  ∃ (waiters : w32),
    "Hwg" ∷ own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg)
      (word.or (word.slu counter (W64 32)) (W64 (uint.Z waiters))) ∗
    "%HnoWaitersIfZero" ∷ ⌜ uint.Z (word.slu counter (W64 32)) = 0 → uint.Z waiters = 0 ⌝.

(* XXX: overflow?
  https://github.com/golang/go/issues/20687
  https://go-review.googlesource.com/c/go/+/140937/2/src/sync/waitgroup.go *)

Local Lemma wg_add_word_fact (counter delta : w64) (waiters : w32) :
  word.add (word.or (word.slu counter (W64 32)) (W64 (uint.Z waiters))) (word.slu delta (W64 32)) =
  word.or (word.slu (word.add counter delta) (W64 32)) (W64 (uint.Z waiters)).
Proof.
Admitted.

Lemma wp_WaitGroup__Add (wg : loc) (delta : w64) :
  ∀ Φ,
  is_initialized -∗
  (|={⊤,∅}=> ∃ oldc, own_WaitGroup wg oldc ∗
                    ⌜ uint.Z oldc > uint.Z delta ∧
                      uint.Z oldc + uint.Z delta < 2^31 ⌝ ∗
    (own_WaitGroup wg (word.add oldc delta) ={∅,⊤}=∗ Φ #())) -∗
  WP method_call #sync.pkg_name' #"WaitGroup'ptr" #"Add" #wg #delta {{ Φ }}.
Proof.
  iIntros (?) "#Hi HΦ". iNamed "Hi".
  wp_method_call. wp_call.
  wp_pures.
  wp_apply wp_with_defer.
  iIntros (?) "Hdefer".
  simpl subst.
  wp_pures.
  wp_alloc wg_ptr as "Hwg_ptr". wp_pures.
  wp_alloc delta_ptr as "Hdelta_ptr". wp_pures.
  rewrite -!default_val_eq_zero_val.
  wp_alloc state_ptr as "Hstate_ptr". wp_pures.
  wp_load. wp_pures.
  wp_load. wp_pures.
  wp_apply (wp_Uint64__Add with "[$]").
  iMod "HΦ" as (?) "(Hwg & %Hbounds & HΦ)".
  iNamed "Hwg".
  iModIntro.
  iExists _. iFrame.
  iIntros "Hwg".
  rewrite wg_add_word_fact.
  iMod ("HΦ" with "[Hwg]").
  {
    iExists waiters.
    iFrame. iPureIntro.

    (* FIXME: lemma *)
    clear -H HnoWaitersIfZero Hbounds.
    word_cleanup.
    Transparent w64_word_instance.
    intros Hz. apply HnoWaitersIfZero.
    simpl in *.
    replace (32 `mod` 2^64) with (32) in * by reflexivity.
    rewrite Z.shiftl_mul_pow2 // in Hz.
    Z.div_mod_to_equations; lia.
  }
  iModIntro.
  wp_pures.
  wp_store.
  wp_pures.
  wp_alloc v_ptr as "Hv_ptr". wp_pures.
  wp_load. wp_pures.
  wp_store. wp_pures.
  wp_alloc w_ptr as "Hw_ptr". wp_pures.
  wp_load. wp_pures.
  wp_store. wp_pures.
  wp_load. wp_pures.
  destruct bool_decide eqn:Hbad.
  {
    exfalso.
    rewrite bool_decide_eq_true in Hbad.
    (* FIXME: lemma+automation *)
    destruct Hbounds.
    word_cleanup.
    Transparent w64_word_instance.
    simpl in *.
    rewrite -!Z.land_ones //
      Z.land_lor_distr_l Z.shiftr_lor in Hbad.
    rewrite !Z.land_ones // in Hbad.
    replace (32 `mod` 2^64) with (32) in * by reflexivity.
    rewrite !Z.mod_mod // in Hbad.
    rewrite !Z.shiftl_mul_pow2 // in Hbad.
    rewrite !Z.shiftr_div_pow2 // in Hbad.
    clear HnoWaitersIfZero.
    replace ((uint.Z waiters `mod` 2 ^ 64) `div` 2 ^ 32) with (0) in Hbad.
    2:{
      clear.
      simpl in *.
      rewrite Z.div_small //.
      Z.div_mod_to_equations. word.
    }
    rewrite Z.lor_0_r in Hbad.
    rewrite (Z.mod_small (_ + _)) in Hbad; last lia.
    rewrite (Z.mod_small (_ * _)) in Hbad; last lia.
    rewrite Z.div_mul // in Hbad.
    rewrite (Z.mod_small (_ + _)) in Hbad; last lia.
    replace (32 - 1) with (31) in * by reflexivity.
    rewrite word.signed_of_Z
      word.swrap_as_div_mod in Hbad.
    replace (32 - 1) with (31) in * by reflexivity.
    rewrite (Z.mod_small (_ + _)) in Hbad; last lia.
    rewrite Z.div_small in Hbad; last lia.
    rewrite Z.mul_0_r in Hbad.
    rewrite Z.sub_0_r in Hbad.
    replace (sint.Z (W32 0)) with (0) in * by reflexivity.
    lia.
    Opaque w64_word_instance.
  }
  wp_pures.
  wp_load.
  wp_pures.
  wp_bind (if: _ then _ else do: #())%E.
  clear Hbad.
  iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[Hv_ptr Hdelta_ptr]").
  {
    destruct bool_decide.
    - wp_pures.
      iSplitR; first done.
      iNamedAccu.
    - wp_pures. wp_load.
      wp_pures.
      destruct bool_decide eqn:Heq1.
      + wp_pures. wp_load. wp_load. wp_pures.
        rewrite bool_decide_eq_true in Heq1.
        destruct bool_decide eqn:Heq2.
        * exfalso.
          {
            rewrite bool_decide_eq_true in Heq2.
            (* more word reasoning *)
            admit.
          }
        * wp_pures. iFrame. done.
      + wp_pures. iFrame. done.
  }
  iIntros (?) "[% H]". iNamed "H".
  subst.
  wp_pures.
  wp_load.
  wp_pures.
Admitted.

End proof.
End goose_lang.

Typeclasses Opaque is_Mutex own_Mutex
            is_Locker is_Cond.
