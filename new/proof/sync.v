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

Local Definition enc (low high : w32) : w64 :=
  word.or (word.slu (W64 (uint.Z high)) (W64 32)) (W64 (uint.Z low)).

Local Lemma enc_add_high (low high delta : w32) :
  word.add (enc low high) (word.slu (W64 (uint.Z delta)) (W64 32)) =
  enc low (word.add high delta).
Proof.
Admitted.

Local Lemma enc_get_high (low high : w32) :
  W32 (uint.Z (word.sru (enc low high) (W64 32))) = high.
Proof.
Admitted.

Local Lemma enc_get_low (low high : w32) :
  W32 (uint.Z (enc low high)) = low.
Proof.
Admitted.

Local Lemma enc_inj (low high low' high' : w32) :
  enc low high = enc low' high' →
  low = low' ∧ high = high'.
Proof.
  intros Heq.
  split.
  - erewrite <-(enc_get_low low high).
    rewrite Heq enc_get_low //.
  - erewrite <-(enc_get_high low high).
    rewrite Heq enc_get_high //.
Qed.


Local Lemma enc_0 :
  W64 0 = enc (W32 0) (W32 0).
Proof. reflexivity. Qed.

(* User must not do an Add() on a wg with (counter=0, waiters>0). *)

Context `{!ghost_varG Σ w32}.

Definition N : namespace. Admitted.

Definition Q (possible_waiters : nat) : iProp Σ. Admitted.
Definition R : iProp Σ. Admitted.

Definition S (unfinished_waiters : nat): iProp Σ. Admitted.
Definition T : iProp Σ. Admitted.

Local Definition is_WaitGroup_inv wg γcounter : iProp Σ :=
  inv N (∃ counter waiters unfinished_waiters,
  "Hptsto" ∷ own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter) ∗
  "Hptsto2" ∷ (
      if decide (counter = W32 0 ∧ waiters ≠ W32 0) then True
      else own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter)
    ) ∗
  "Hctr" ∷ ghost_var γcounter (1/2)%Qp counter ∗

  "Hunfinished" ∷ S unfinished_waiters ∗
  "Hunfinished_token" ∷  [∗] (replicate unfinished_waiters R) ∗

  "HR" ∷ ([∗] (replicate (uint.nat waiters) R)) ∗
  "%Hunfinished_zero" ∷ ⌜ unfinished_waiters > 0 → waiters = W32 0 ∧ counter = W32 0 ⌝
  )%I
.

(* Prepare to Wait() *)
Lemma step1 w :
  Q w ==∗ Q (1+w) ∗ R.
Admitted.

Lemma step2 :
  Q 0 ∗ R -∗ False.
Admitted.

Lemma step3 uw :
  S uw ==∗ S (1+uw) ∗ T.
Admitted.

Lemma step3_many uw :
  S 0 ==∗ S uw ∗ ([∗] replicate uw T).
Proof.
  iInduction uw as [] "IH".
  { iIntros "$". rewrite replicate_0. iModIntro. done. }
  iIntros "H0".
  simpl.
  iMod ("IH" with "[$]") as "[Huw $]".
  by iApply step3.
Qed.

Lemma step4 :
  S 0 ∗ T -∗ False.
Admitted.

Definition own_WaitGroup (wg : loc) (counter : w32) : iProp Σ :=
  ∃ γcounter,
    ghost_var γcounter (1/2)%Qp counter ∗
    is_WaitGroup_inv wg γcounter.

Local Lemma wg_delta_to_w32 (delta' : w32) (delta : w64) :
  delta' = (W32 (uint.Z delta)) →
  word.slu delta (W64 32) = word.slu (W64 (uint.Z delta')) (W64 32).
Proof.
Admitted.

Lemma atomic_Uint64_inj a b c a' b' c' :
  atomic.Uint64.mk a b c = atomic.Uint64.mk a' b' c' →
  c = c'.
Proof.
  inversion 1.
  done.
Qed.

(* XXX: overflow?
  https://github.com/golang/go/issues/20687
  https://go-review.googlesource.com/c/go/+/140937/2/src/sync/waitgroup.go *)

Lemma wp_WaitGroup__Add (wg : loc) (delta : w64) :
  let delta' := (W32 (uint.Z delta)) in
  ∀ Φ,
  is_initialized -∗
  (|={⊤,↑N}=>
     ∃ oldc,
       "Hwg" ∷ own_WaitGroup wg oldc ∗
       "%Hbounds" ∷ ⌜ 0 ≤ sint.Z oldc + sint.Z delta' < 2^31 ⌝ ∗
       "HQ" ∷ (⌜ oldc ≠ W32 0 ⌝ ∨ Q 0) ∗
       "HΦ" ∷ ((⌜ oldc ≠ W32 0 ⌝ ∨ Q 0) -∗ own_WaitGroup wg (word.add oldc delta') ={↑N,⊤}=∗ Φ #())
  ) -∗
  WP method_call #sync.pkg_name' #"WaitGroup'ptr" #"Add" #wg #delta {{ Φ }}.
Proof.
  intros delta'.
  iIntros (?) "#Hi HΦ". iNamed "Hi".
  wp_method_call. wp_call.
  wp_pures.
  wp_apply wp_with_defer.
  iIntros (?) "Hdefer".
  simpl subst.
  wp_alloc wg_ptr as "Hwg_ptr".
  wp_pure_lc "Hlc". wp_pures.
  wp_alloc delta_ptr as "Hdelta_ptr". wp_pures.
  rewrite -!default_val_eq_zero_val.
  wp_alloc state_ptr as "Hstate_ptr". wp_pures.
  wp_load. wp_pures.
  wp_load. wp_pures.

  wp_apply (wp_Uint64__Add with "[$]").
  iMod "HΦ".
  iNamed "HΦ".
  unfold own_WaitGroup.
  iDestruct "Hwg" as (?) "[Hctr_in #Hinv]".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi".
  rewrite difference_diag_L.
  iModIntro.
  iCombine "Hctr Hctr_in" as "Hctr" gives %[_ ->].
  destruct decide as [Hw|HnotInWakingState].
  {
    iExFalso.
    destruct Hw as [-> Hw].
    destruct (uint.nat waiters) eqn:Hx.
    { exfalso. apply Hw. word. }
    iDestruct "HR" as "[HR _]".
    iDestruct "HQ" as "[%|HQ]".
    { done. }
    iDestruct (step2 with "[$]") as %[].
  }
  iCombine "Hptsto Hptsto2" as "Hptsto".
  iExists _. iFrame.
  rewrite (wg_delta_to_w32 delta') // enc_add_high.
  iMod (ghost_var_update (word.add oldc delta') with "Hctr") as "[Hctr Hctr_in]".
  iIntros "Hwg".
  destruct unfinished_waiters.
  2:{
    iExFalso.
    specialize (Hunfinished_zero ltac:(done)).
    intuition. subst.
    iDestruct "HQ" as "[%|HQ]"; first done.
    rewrite replicate_S. iClear "HR".
    iDestruct "Hunfinished_token" as "[HR _]".
    iDestruct (step2 with "[$]") as %[].
  }
  destruct (decide (word.add oldc delta' = W32 0 ∧ waiters ≠ W32 0)) as [Hwake|HnoWake].
  2:{ (* not done, no need to wake waiters. *)
    iMod ("Hclose" with "[Hwg Hunfinished Hunfinished_token Hctr HR]").
    {
      iNext.
      iDestruct "Hwg" as "[Hwg Hwg2]".
      iExists _, _, O; iFrame "Hwg ∗".
      rewrite decide_False; last intuition.
      iFrame. done.
    }
    iMod ("HΦ" with "[$] [$]").
    iModIntro.
    wp_pures.
    wp_store.
    wp_pures.
    wp_alloc v_ptr as "Hv_ptr". wp_pures.
    wp_load. wp_pures.
    wp_store. wp_pures.
    rewrite enc_get_high.

    wp_alloc w_ptr as "Hw_ptr". wp_pures.
    wp_load. wp_pures.
    wp_store. wp_pures.
    rewrite enc_get_low.

    wp_load. wp_pures.
    destruct bool_decide eqn:Hbad.
    {
      exfalso.
      rewrite bool_decide_eq_true in Hbad.
      (* FIXME: word should do these. *)
      rewrite word.signed_add in Hbad.
      replace (sint.Z (W32 0)) with 0 in * by reflexivity.
      rewrite word.swrap_inrange in Hbad; lia.
    }
    wp_pures.
    wp_load.
    wp_pures.
    wp_bind (if: _ then _ else do: #())%E.
    clear Hbad.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[Hv_ptr Hdelta_ptr]").
    {
      destruct bool_decide eqn:Heq0.
      - wp_pures.
        iSplitR; first done.
        iNamedAccu.
      - rewrite bool_decide_eq_false in Heq0.
        wp_pures. wp_load.
        wp_pures.
        destruct bool_decide eqn:Heq1.
        + wp_pures. wp_load. wp_load. wp_pures.
          replace (W32 (uint.Z delta)) with delta' by reflexivity.
          rewrite bool_decide_eq_true in Heq1.
          destruct bool_decide eqn:Heq2.
          * exfalso. rewrite bool_decide_eq_true in Heq2.
            { (* FIXME: word. *)
              assert (sint.Z oldc = 0).
              {
                word_cleanup.
                rewrite word.signed_add /word.swrap in Heq2_signed.
                word.
              }
              apply Heq0. intuition. exfalso. apply H3.
              { apply word.signed_inj. rewrite H0 //. }
              word.
            }
          * wp_pures. iFrame. done.
        + wp_pures. iFrame. done.
    }
    iIntros (?) "[% H]". iNamed "H".
    subst.
    wp_pures.
    wp_load.
    wp_pures.
    destruct (bool_decide) eqn:Heq1.
    { (* no need to wake anyone up *) wp_pures. wp_load. wp_pures. iFrame. }
    rewrite bool_decide_eq_false in Heq1.
    wp_pures. wp_load. wp_pures.
    rewrite bool_decide_true.
    { (* no need to wake anyone up *) wp_pures. wp_load. wp_pures. iFrame. }
    apply not_and_l in HnoWake, HnotInWakingState.
    destruct HnoWake as [|].
    2:{ by apply dec_stable. }
    destruct HnotInWakingState as [|].
    2:{ by apply dec_stable. }
    apply Znot_gt_le in Heq1.
    exfalso.
    apply H0. clear H0. apply word.signed_inj.
    replace (sint.Z (W32 0)) with 0 in * by reflexivity.
    intuition.
    apply Z.le_antisymm.
    { word. }
    { word_cleanup.
      rewrite word.signed_add /word.swrap in H2 |- *.
      word. }
  }

  (* will have to wake *)
  iDestruct "Hwg" as "[Hwg Hwg2]".
  iMod ("Hclose" with "[Hwg2 Hunfinished Hunfinished_token Hctr HR]").
  {
    iNext.
    iExists _, _, O; iFrame "Hwg2 ∗".
    rewrite decide_True; last intuition.
    done.
  }
  iMod ("HΦ" with "[$] [$]").
  iModIntro.
  wp_pures.
  wp_store.
  wp_pures.
  wp_alloc v_ptr as "Hv_ptr". wp_pures.
  wp_load. wp_pures.
  wp_store. wp_pures.
  rewrite enc_get_high.

  wp_alloc w_ptr as "Hw_ptr". wp_pures.
  wp_load. wp_pures.
  wp_store. wp_pures.
  rewrite enc_get_low.

  wp_load. wp_pures.
  destruct bool_decide eqn:Hbad.
  {
    exfalso.
    rewrite bool_decide_eq_true in Hbad.
    (* FIXME: word should do these. *)
    rewrite word.signed_add in Hbad.
    replace (sint.Z (W32 0)) with 0 in * by reflexivity.
    rewrite word.swrap_inrange in Hbad; lia.
  }
  wp_pures.
  wp_load.
  wp_pures.
  wp_bind (if: _ then _ else do: #())%E.
  clear Hbad.
  iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[Hv_ptr Hdelta_ptr]").
  {
    destruct bool_decide eqn:Heq0.
    - wp_pures.
      iSplitR; first done.
      iNamedAccu.
    - rewrite bool_decide_eq_false in Heq0.
      wp_pures. wp_load.
      wp_pures.
      destruct bool_decide eqn:Heq1.
      + wp_pures. wp_load. wp_load. wp_pures.
        replace (W32 (uint.Z delta)) with delta' by reflexivity.
        rewrite bool_decide_eq_true in Heq1.
        destruct bool_decide eqn:Heq2.
        * exfalso. rewrite bool_decide_eq_true in Heq2.
          { (* FIXME: word. *)
            assert (sint.Z oldc = 0).
            {
              word_cleanup.
              rewrite word.signed_add /word.swrap in Heq2_signed.
              word.
            }
            apply Heq0. intuition. exfalso. apply H5.
            { apply word.signed_inj. rewrite H0 //. }
            word.
          }
        * wp_pures. iFrame. done.
      + wp_pures. iFrame. done.
  }
  iIntros (?) "[% H]". iNamed "H".
  subst.
  wp_pures.

  wp_load.
  wp_pures.
  rewrite bool_decide_false.
  2:{ intuition. word. }
  wp_pures. wp_load. wp_pures.
  rewrite bool_decide_false.
  2:{ intuition. }
  wp_pures.
  wp_load. wp_pures.
  wp_apply (wp_Uint64__Load with "[$]").
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hwg".
  iMod "Hmask" as "_".
  iModIntro.
  wp_load.
  wp_pures.
  rewrite bool_decide_true //.
  wp_pures.

  wp_load.
  wp_pure_lc "Hlc".
  wp_pures.

  (* want to get a bunch of unfinisheds. *)
  wp_apply (wp_Uint64__Store with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  clear Hunfinished_zero.
  iNamed "Hi".
  iClear "Hptsto2".
  iCombine "Hwg Hptsto"  gives %[_ Heq].
  apply atomic_Uint64_inj in Heq.
  apply enc_inj in Heq as [<- <-].
  iCombine "Hwg Hptsto" as "Hwg".
  iExists _. iFrame.
  iIntros "Hwg".
  iMod "Hmask" as "_".
  destruct unfinished_waiters.
  2:{
    exfalso.
    specialize (Hunfinished_zero ltac:(done)).
    intuition.
  }
  clear Hunfinished_zero.
  iClear "Hunfinished_token".
  iMod (step3_many (uint.nat waiters) with "Hunfinished") as "[Hunfinished Hunfinished_tokens]".
  rewrite enc_0.
  iDestruct "Hwg" as "[Hwg Hwg2]".
  destruct Hwake as [Hwake1 Hwake2].
  rewrite Hwake1.
  iMod ("Hclose" with "[Hwg Hwg2 Hunfinished HR Hctr]").
  {
    iNext. iExists _, _, (uint.nat waiters).
    iFrame. rewrite replicate_0.
    iSplitL; first by iApply big_sepL_nil.
    done.
  }
  iModIntro.
  wp_pures.
  (* call semrelease. *)
Admitted.

End proof.
End goose_lang.

Typeclasses Opaque is_Mutex own_Mutex
            is_Locker is_Cond.
