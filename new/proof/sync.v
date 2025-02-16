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


Context `{!ghost_varG Σ w32}.

Definition is_sema (x : loc) γ N : iProp Σ :=
  inv N (∃ (v : w32), x ↦ v ∗ ghost_var γ (1/2) v).

Definition own_sema γ (v : w32) : iProp Σ :=
  ghost_var γ (1/2) v.

Lemma wp_runtime_Semacquire (sema : loc) γ N :
  ∀ Φ,
  is_initialized ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (⌜ uint.nat v > 0 ⌝ → own_sema γ (word.sub v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP func_call #sync.pkg_name' #"runtime_Semacquire" #sema {{ Φ }}.
Proof.
  iIntros (?) "[#Hi #Hsem] HΦ". iNamed "Hi".
  wp_func_call. wp_call.
  wp_for. wp_pures.
  rewrite decide_True //.
  wp_pures.
  wp_bind (! _)%E.
  iInv "Hsem" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hs Hv]".
  unshelve iApply (wp_typed_Load with "[$Hs]"); try tc_solve.
  { done. }
  iNext.
  iIntros "Hs".
  iMod ("Hclose" with "[$]") as "_".
  iModIntro.
  wp_pures.
  destruct bool_decide eqn:Hnz.
  { (* keep looping *)
    wp_pures.
    iApply wp_for_post_continue.
    wp_pures. iFrame.
  }

  (* try to acquire *)
  rewrite bool_decide_eq_false in Hnz.
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv "Hsem" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hs Hv]".
  destruct (decide (v = v0)).
  {
    subst. iMod "HΦ" as (?) "[Hv2 HΦ]".
    iCombine "Hv Hv2" as "Hv" gives %[_ <-].
    iMod (ghost_var_update with "Hv") as "[Hv Hv2]".
    unshelve iApply (wp_typed_cmpxchg_suc with "[$]"); try tc_solve; try done.
    iNext. iIntros "Hs".
    iMod ("HΦ" with "[] [$]") as "HΦ".
    { iPureIntro.
      (* FIXME: word *)
      assert (uint.nat v0 ≠ O).
      { intros ?. apply Hnz. word. }
      word.
    }
    iModIntro.
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_pures.
    iApply wp_for_post_return.
    wp_pures. done.
  }
  { (* cmpxchg will fail *)
    unshelve iApply (wp_typed_cmpxchg_fail with "[$]"); try tc_solve.
    { done. }
    { naive_solver. }
    iNext. iIntros "Hs".
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_pures.
    iApply wp_for_post_do. wp_pures.
    iFrame.
  }
Qed.

Lemma wp_runtime_Semrelease (sema : loc) γ N (_u1 : bool) (_u2 : w64):
  ∀ Φ,
  is_initialized ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (own_sema γ (word.add v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP func_call #sync.pkg_name' #"runtime_Semrelease" #sema #_u1 #_u2 {{ Φ }}.
Proof.
Admitted.

Local Definition enc (low high : w32) : w64 :=
  word.or (word.slu (W64 (uint.Z high)) (W64 32)) (W64 (uint.Z low)).

Local Lemma word_or_shiftr (w1 w2 w3 : w64) :
  uint.Z w3 < 64 →
  word.sru (word.or w1 w2) w3 = (word.or (word.sru w1 w3) (word.sru w2 w3)).
Proof.
  intros. apply word.unsigned_inj.
  rewrite !word.unsigned_sru // !word.unsigned_or !word.unsigned_sru //.
  rewrite (wrap_small (Z.lor _ _)).
  2:{
    split.
    { apply Z.lor_nonneg. word. }
    rewrite Z.bounded_iff_bits_nonneg //.
    2:{ apply Z.lor_nonneg. word. }
    intros.
    rewrite Z.lor_spec.
    repeat (rewrite (Zmod_small_bits_high 64) //; last word).
  }
  rewrite Z.shiftr_lor.
  repeat (rewrite -> Z.shiftr_div_pow2 by word).
  rewrite (wrap_small (_ `div` _)).
  2:{
    split.
    { apply Z_div_nonneg_nonneg; word. }
    word.
  }
  rewrite (wrap_small (_ `div` _)).
  2:{
    split.
    { apply Z_div_nonneg_nonneg; word. }
    word.
  }
  word.
Qed.

Local Lemma enc_get_high (low high : w32) :
  W32 (uint.Z (word.sru (enc low high) (W64 32))) = high.
Proof.
  rewrite /enc.
  rewrite word_or_shiftr //.
  rewrite word.unsigned_or !word.unsigned_sru // word.unsigned_slu //.
  rewrite !Z.shiftr_div_pow2 //.
  replace (uint.Z (W64 32)) with 32 by done.
  replace (uint.Z (W64 (uint.Z low))) with (uint.Z low) by word.
  rewrite (Z.div_small (uint.Z low)).
  2:{ word. }
  rewrite (wrap_small 0) // Z.lor_0_r.
  rewrite Z.shiftl_mul_pow2 //.
  replace (uint.Z (W64 _)) with (uint.Z high) by word.
  rewrite -> (wrap_small (_ * _)) by word.
  word.
Qed.

Local Lemma enc_get_low (low high : w32) :
  W32 (uint.Z (enc low high)) = low.
Proof.
  rewrite /enc.
  apply word.unsigned_inj.
  rewrite word.unsigned_or word.unsigned_slu // unsigned_U32 /word.wrap.
  Import bitblast.
  word_cleanup.
  destruct H0 as [? H0].
  destruct H1 as [? H1].
  rewrite Z.bounded_iff_bits_nonneg // in H0.
  rewrite Z.bounded_iff_bits_nonneg // in H1.
  Z.bitblast; subst.
  - rewrite Z.testbit_neg_r //. lia.
  - rewrite H1 //.
  - rewrite H1 //.
Qed.

Local Lemma enc_add_high (low high delta : w32) :
  word.add (enc low high) (word.slu (W64 (uint.Z delta)) (W64 32)) =
  enc low (word.add high delta).
Proof.
  rewrite /enc.
  apply word.unsigned_inj.
  repeat (
      rewrite word.unsigned_add ||
      rewrite word.unsigned_or ||
      rewrite word.unsigned_slu //
    ).
  replace (uint.Z (W64 (uint.Z high))) with (uint.Z high) by word.
  replace (uint.Z (W64 (uint.Z low))) with (uint.Z low) by word.
  unfold word.wrap.
  rewrite !Z.shiftl_mul_pow2 //.
  rewrite -> !(Z.mod_small (uint.Z _ * 2^_)) by word.
  Search Z.shiftl Z.pow.
  rewrite -!Z.land_ones //.
  word_cleanup.
  unfold word.wrap.
  destruct H0 as [? Hbit0].
  destruct H1 as [? Hbit1].
  destruct H2 as [? Hbit2].
  rewrite Z.bounded_iff_bits_nonneg // in Hbit0.
  rewrite Z.bounded_iff_bits_nonneg // in Hbit1.
  rewrite Z.bounded_iff_bits_nonneg // in Hbit2.


  match goal with
  | [ |- context[Z.add ?a ?b] ] => pose proof (Z.add_carry_bits a b false)
  end.
  rewrite Z.add_0_r in H3.
  destruct H3 as (? & -> & H3).

  match goal with
  | [ |- context[Z.add ?a ?b] ] => pose proof (Z.add_carry_bits a b false)
  end.
  rewrite Z.add_0_r in H4.
  destruct H4 as (? & -> & H4).
  Z.bitblast; subst.
  - rewrite !andb_true_l !andb_true_r.
    rewrite !(Z.testbit_neg_r _ (i - 32)) // /=.
    rewrite xorb_false_r.
    destruct H3 as [Hx Hx0].
    enough (Z.testbit x i = false) .
    { rewrite H3. rewrite xorb_false //. }
    generalize dependent i.
    set (P:=(λ i, i < 64 → i - 32 < 32 → i - 32 < 0 → i - 32 < 64 → Z.testbit x i = false)).
    change (∀ i : Z, 0 ≤ i → P i).
    apply (Wf_Z.natlike_rec P); subst P.
    { simpl. intros. done. }
    simpl. intros.
    apply (f_equal (λ n, Z.testbit n (x1))) in Hx.
    revert Hx.
    rewrite -> Z.div2_bits by lia.
    Z.bitblast_core.
    subst.
    repeat rewrite -> (Z.testbit_neg_r _ (x1 - 32)) by lia.
    simpl. rewrite andb_false_r orb_false_r andb_true_r /=.
    rewrite H5 //; lia.
  - rewrite !andb_true_r andb_true_l.
    Search (Z.testbit _ _).
    rewrite
Qed.

Local Lemma enc_add_low (low high delta : w32) :
  word.add (enc low high) (W64 (uint.Z delta)) =
  enc (word.add low delta) high.
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

Definition own_WaitGroup_waiters (possible_waiters : w32) : iProp Σ. Admitted.
Definition own_WaitGroup_wait_token: iProp Σ. Admitted.

Definition own_zerostate_auth_half (unfinished_waiters : w32): iProp Σ. Admitted.
Definition own_zerostate_token : iProp Σ. Admitted.

Record WaitGroup_names := {
    counter_gn : gname ;
    sema_gn : gname
  }.

Definition N : namespace. Admitted.
Implicit Type γ : WaitGroup_names.

Local Definition is_WaitGroup_inv wg γ : iProp Σ :=
  inv (N.@"wg") (∃ counter waiters unfinished_waiters,
  "Hptsto" ∷ own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter) ∗
  "Hptsto2" ∷ (
      if decide (counter = W32 0 ∧ waiters ≠ W32 0) then True
      else own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter)
    ) ∗
  "Hctr" ∷ ghost_var γ.(counter_gn) (1/2)%Qp counter ∗

  "Hunfinished" ∷ own_zerostate_auth_half unfinished_waiters ∗
  "Hunfinished_token" ∷  [∗] (replicate (uint.nat unfinished_waiters) own_WaitGroup_wait_token) ∗

  "Htoks" ∷ ([∗] (replicate (uint.nat waiters) own_WaitGroup_wait_token)) ∗
  "%Hunfinished_zero" ∷ ⌜ unfinished_waiters ≠ W32 0 → waiters = W32 0 ∧ counter = W32 0 ⌝
  )%I.

Local Definition is_WaitGroup_sema_inv γ : iProp Σ :=
  inv (N.@"semInv") (∃ (unfinished_waiters sema : w32),
        "Hs" ∷ own_sema γ.(sema_gn) sema ∗
        "HT" ∷  [∗] (replicate (uint.nat sema) own_zerostate_token) ∗
        "HS" ∷ own_zerostate_auth_half unfinished_waiters
    ).

Local Definition is_WaitGroup wg γ : iProp Σ :=
  "#Hsem" ∷ is_sema (struct.field_ref_f sync.WaitGroup "sema" wg) γ.(sema_gn) (N.@"sema") ∗
  "#Hinv" ∷ is_WaitGroup_inv wg γ ∗
  "#HsemInv" ∷ is_WaitGroup_sema_inv γ.

(* Prepare to Wait() *)
Lemma alloc_wait_token (w : w32) :
  uint.Z (word.add w (W32 1)) = uint.Z w + 1 →
  own_WaitGroup_waiters w ==∗ own_WaitGroup_waiters (word.add w (W32 1)) ∗ own_WaitGroup_wait_token.
Admitted.

Lemma max_waiters (n : Z) :
  ([∗] replicate (Z.to_nat n) own_WaitGroup_wait_token) -∗
  ⌜ n < 2^32 ⌝.
Proof.
Admitted.

Lemma waiters_none_token_false :
  own_WaitGroup_waiters (W32 0) ∗ own_WaitGroup_wait_token -∗ False.
Admitted.

Lemma alloc_zerostate_token uw :
  uint.Z (word.add uw (W32 1)) = uint.Z uw + 1 →
  own_zerostate_auth_half uw ∗ own_zerostate_auth_half uw ==∗
  own_zerostate_auth_half (word.add uw (W32 1)) ∗ own_zerostate_auth_half (word.add uw (W32 1)) ∗
  own_zerostate_token.
Admitted.

Lemma alloc_many_zerostate_tokens uw :
  own_zerostate_auth_half (W32 0) -∗ own_zerostate_auth_half (W32 0) ==∗
  own_zerostate_auth_half uw ∗ own_zerostate_auth_half uw ∗ ([∗] replicate (uint.nat uw) own_zerostate_token).
Proof.
  assert (∃ n, n = (uint.nat uw)) as [n Heq].
  { by eexists. }
  iInduction n as [] "IH" forall (uw Heq).
  { rewrite -Heq.
    replace (uw) with (W32 0) by word.
    iIntros "$ $". rewrite replicate_0. iModIntro. done. }
  rewrite -Heq.
  iIntros "? ?".
  simpl.
  iMod ("IH" $! (word.sub uw (W32 1)) with "[] [$] [$]") as "(Huw & Huw' & ?)".
  { word. }
  replace (uint.nat (word.sub _ _)) with n by word.
  iFrame.
  iMod (alloc_zerostate_token with "[$]") as "(? & ? & $)".
  { word. }
  replace (word.add (word.sub _ _) _) with (uw) by ring.
  by iFrame.
Qed.

Lemma zerostate_empty_token_false :
  own_zerostate_auth_half (W32 0) -∗ own_zerostate_token -∗ False.
Admitted.

Lemma zerostate_tokens_bound w (n : nat) :
  own_zerostate_auth_half w -∗ [∗] replicate n own_zerostate_token -∗ ⌜ n ≤ uint.nat w ⌝.
Admitted.

Lemma delete_zerostate_token uw :
  own_zerostate_auth_half uw -∗ own_zerostate_auth_half uw -∗
  own_zerostate_token ==∗
  own_zerostate_auth_half (word.sub uw (W32 1)) ∗ own_zerostate_auth_half (word.sub uw (W32 1)).
Admitted.

Lemma own_zerostate_auth_half_agree uw uw' :
  own_zerostate_auth_half uw -∗ own_zerostate_auth_half uw' -∗ ⌜ uw = uw' ⌝.
Admitted.

Definition own_WaitGroup γ (counter : w32) : iProp Σ :=
  ghost_var γ.(counter_gn) (1/2)%Qp counter.

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

Lemma wp_WaitGroup__Add (wg : loc) (delta : w64) γ :
  let delta' := (W32 (uint.Z delta)) in
  ∀ Φ,
  is_initialized ∗ is_WaitGroup wg γ -∗
  (|={⊤,↑N}=>
     ∃ oldc,
       "Hwg" ∷ own_WaitGroup γ oldc ∗
       "%Hbounds" ∷ ⌜ 0 ≤ sint.Z oldc + sint.Z delta' < 2^31 ⌝ ∗
       "HnoWaiters" ∷ (⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters (W32 0)) ∗
       "HΦ" ∷ ((⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters (W32 0)) -∗
               own_WaitGroup γ (word.add oldc delta') ={↑N,⊤}=∗ Φ #())
  ) -∗
  WP method_call #sync.pkg_name' #"WaitGroup'ptr" #"Add" #wg #delta {{ Φ }}.
Proof.
  intros delta'.
  iIntros (?) "[#Hi #His] HΦ". iNamed "Hi".
  iNamed "His".
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
  wp_load. wp_pures. wp_load. wp_pures.

  wp_apply (wp_Uint64__Add with "[$]").
  iMod "HΦ".
  iNamed "HΦ".
  unfold own_WaitGroup.
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iCombine "Hctr Hwg" as "Hctr" gives %[_ ->].
  destruct decide as [Hw|HnotInWakingState].
  {
    iExFalso.
    destruct Hw as [-> Hw].
    destruct (uint.nat waiters) eqn:Hx.
    { exfalso. apply Hw. word. }
    iDestruct "Htoks" as "[Htok _]".
    iDestruct "HnoWaiters" as "[%|HnoWaiter]".
    { done. }
    iDestruct (waiters_none_token_false with "[$]") as %[].
  }
  iCombine "Hptsto Hptsto2" as "Hptsto".
  iExists _. iFrame.
  rewrite (wg_delta_to_w32 delta') // enc_add_high.
  iMod (ghost_var_update (word.add oldc delta') with "Hctr") as "[Hctr Hctr_in]".
  iIntros "Hwg".
  destruct (decide (unfinished_waiters = W32 0)).
  2:{
    iExFalso.
    destruct (Hunfinished_zero ltac:(done)) as [-> ->].
    subst.
    iDestruct "HnoWaiters" as "[%|HnoWaiters]"; first done.
    destruct (uint.nat unfinished_waiters) eqn:Hx.
    { exfalso. apply n. word. }
    rewrite replicate_S.
    iDestruct "Hunfinished_token" as "[Htok _]".
    iDestruct (waiters_none_token_false with "[$]") as %[].
  }
  subst.
  destruct (decide (word.add oldc delta' = W32 0 ∧ waiters ≠ W32 0)) as [Hwake|HnoWake].
  2:{ (* not done, no need to wake waiters. *)
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hwg Hunfinished Hunfinished_token Hctr Htoks]").
    {
      iNext.
      iDestruct "Hwg" as "[Hwg Hwg2]".
      iExists _, _, (W32 0); iFrame "Hwg ∗".
      rewrite decide_False; last intuition.
      iFrame. done.
    }
    iMod ("HΦ" with "[$] [$]").
    iModIntro.
    wp_pures. wp_store. wp_pures. wp_alloc v_ptr as "Hv_ptr". wp_pures.
    wp_load. wp_pures. wp_store. wp_pures. rewrite enc_get_high.

    wp_alloc w_ptr as "Hw_ptr". wp_pures. wp_load. wp_pures. wp_store.
    wp_pures. rewrite enc_get_low. wp_load. wp_pures.

    destruct bool_decide eqn:Hbad.
    {
      exfalso.
      rewrite bool_decide_eq_true in Hbad.
      (* FIXME: word should do these. *)
      rewrite word.signed_add in Hbad.
      replace (sint.Z (W32 0)) with 0 in * by reflexivity.
      rewrite word.swrap_inrange in Hbad; lia.
    }
    wp_pures. wp_load. wp_pures.
    wp_bind (if: _ then _ else do: #())%E.
    clear Hbad.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[Hv_ptr Hdelta_ptr]").
    {
      destruct bool_decide eqn:Heq0.
      - wp_pures.
        iSplitR; first done.
        iNamedAccu.
      - rewrite bool_decide_eq_false in Heq0.
        wp_pures. wp_load. wp_pures.
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
    wp_pures. wp_load. wp_pures.
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
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hwg2 Hunfinished Hunfinished_token Hctr Htoks]") as "_".
  {
    iNext.
    iExists _, _, (W32 0); iFrame "Hwg2 ∗".
    rewrite decide_True; last intuition.
    done.
  }
  iMod ("HΦ" with "[$] [$]").
  iModIntro.
  wp_pures. wp_store. wp_pures. wp_alloc v_ptr as "Hv_ptr". wp_pures.
  wp_load. wp_pures. wp_store. wp_pures. rewrite enc_get_high.

  wp_alloc w_ptr as "Hw_ptr". wp_pures. wp_load. wp_pures. wp_store.
  wp_pures. rewrite enc_get_low.

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
  wp_pures. wp_load. wp_pures.
  wp_bind (if: _ then _ else do: #())%E.
  clear Hbad.
  iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[Hv_ptr Hdelta_ptr]").
  {
    destruct bool_decide eqn:Heq0.
    - wp_pures.
      iSplitR; first done.
      iNamedAccu.
    - rewrite bool_decide_eq_false in Heq0.
      wp_pures. wp_load. wp_pures.
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
  wp_pures. wp_load. wp_pures.
  rewrite bool_decide_false.
  2:{ intuition. word. }
  wp_pures. wp_load. wp_pures.
  rewrite bool_decide_false.
  2:{ intuition. }
  wp_pures. wp_load. wp_pures.
  wp_apply (wp_Uint64__Load with "[$]").
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hwg".
  iMod "Hmask" as "_".
  iModIntro.
  wp_load. wp_pures.
  rewrite bool_decide_true //.
  wp_pure_lc "Hlc". wp_pure_lc "Hlc2". wp_pures.

  wp_load. wp_pures.

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
  destruct (uint.nat unfinished_waiters) eqn:Huf.
  2:{
    exfalso.
    specialize (Hunfinished_zero ltac:(word)).
    intuition.
  }
  clear Hunfinished_zero.
  iClear "Hunfinished_token".
  iInv "HsemInv" as "Hi" "Hclose2".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi".
  iDestruct (own_zerostate_auth_half_agree with "[$] [$]") as %->.
  replace (unfinished_waiters) with (W32 0) by word.
  iDestruct (zerostate_tokens_bound with "[$] [$]") as %Hs.
  replace (sema) with (W32 0) by word.
  clear Huf Hs unfinished_waiters.
  iMod (alloc_many_zerostate_tokens waiters with "[$] [$]") as "(Hunfinished & HS & Hunfinished_tokens)".
  iEval (rewrite enc_0) in "Hwg".
  iDestruct "Hwg" as "[Hwg Hwg2]".
  destruct Hwake as [Hwake1 Hwake2].
  rewrite Hwake1.
  iMod ("Hclose2" with "[HS Hs HT]") as "_".
  { iFrame. }
  iMod ("Hclose" with "[Hwg Hwg2 Hunfinished Htoks Hctr]") as "_".
  {
    iNext. iExists _, _, waiters.
    iFrame. rewrite replicate_0.
    iSplitL; first by iApply big_sepL_nil.
    done.
  }
  iModIntro.
  wp_pures.
  (* call semrelease. *)

  iAssert (
      ∃ (wrem : w32),
        "Hw_ptr" ∷ w_ptr ↦ wrem ∗
        "Hunfinished_tokens" ∷ [∗] replicate (uint.nat wrem) own_zerostate_token
    )%I with "[Hw_ptr Hunfinished_tokens]" as "HloopInv".
  { iFrame. }

  wp_for.
  iNamed "HloopInv".
  wp_pures. wp_load. wp_pures.
  destruct bool_decide eqn:Hwrem.
  { (* no more waiters to wake up. *)
    rewrite decide_False; last naive_solver.
    rewrite decide_True //.
    wp_pures. wp_load. wp_pures. iFrame.
  }

  (* wake up another waiter *)
  rewrite bool_decide_eq_false in Hwrem.
  rewrite decide_True //.
  wp_pures. wp_load. wp_pure_lc "Hlc". wp_pures.
  wp_apply (wp_runtime_Semrelease with "[$]").
  iInv "HsemInv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  clear sema.
  iNamed "Hi".
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _; iFrame "Hs".
  iIntros "Hs".
  iMod "Hmask" as "_".
  replace (uint.nat wrem)%nat with (1+(uint.nat (word.sub wrem (W32 1))))%nat.
  2:{
    (* FIXME: word *)
    apply w32_val_neq in Hwrem. word.
  }
  rewrite replicate_S.
  iDestruct "Hunfinished_tokens" as "[HTnew Hunfinished_tokens]".

  iMod ("Hclose" with "[Hs HT HTnew HS]").
  {
    iDestruct (zerostate_tokens_bound _ (S (uint.nat sema)) with "[$] [$]") as %Hs.
    iFrame "Hs ∗".
    replace (uint.nat (word.add sema (W32 1))) with (S (uint.nat sema))%nat by word.
    iFrame.
  }
  iModIntro.
  wp_pures.
  iApply wp_for_post_do.
  wp_pures. wp_load. wp_pures. wp_store. wp_pures.
  iFrame.
Qed.

Lemma wp_WaitGroup__Wait (wg : loc) (delta : w64) γ :
  ∀ Φ,
  is_initialized ∗ is_WaitGroup wg γ ∗ own_WaitGroup_wait_token -∗
  (|={⊤∖↑N, ∅}=>
     ∃ oldc,
       own_WaitGroup γ oldc ∗ (⌜ sint.Z oldc = 0 ⌝ → own_WaitGroup γ oldc ={∅,⊤∖↑N}=∗
                               own_WaitGroup_wait_token -∗ Φ #())
  ) -∗
  WP method_call #sync.pkg_name' #"WaitGroup'ptr" #"Wait" #wg #() {{ Φ }}.
Proof.
  iIntros (?) "(#Hinit & #Hwg & HR_in) HΦ".
  iNamed "Hinit". iNamed "Hwg".
  wp_method_call. wp_call.
  rewrite -!default_val_eq_zero_val.
  wp_alloc wg_ptr as "Hwg_ptr".
  wp_pures.
  wp_for.
  wp_pures.
  rewrite decide_True //.
  wp_pures.

  wp_alloc state_ptr as "Hstate_ptr".
  wp_pures. wp_load. wp_pure_lc "Hlc". wp_pures.
  wp_apply (wp_Uint64__Load with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi".
  destruct (decide (counter = W32 0)).
  { (* counter is zero, so can return. *)
    subst.

    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as (?) "[Hwg HΦ]".
    { solve_ndisj. }
    iModIntro.
    iCombine "Hwg Hctr" gives %[_ ->].
    iExists _.
    iFrame.
    iIntros "Hptsto".
    iMod ("HΦ" with "[//] [$]") as "HΦ".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hptsto Hptsto2 Htoks Hunfinished Hunfinished_token Hwg]").
    { by iFrame. }
    iModIntro.
    wp_pures. wp_store. wp_pures.
    wp_alloc v_ptr as "Hv_ptr". wp_pures.
    wp_load. wp_pures.
    rewrite enc_get_high. wp_store. wp_pures.
    wp_alloc w_ptr as "Hw_ptr". wp_pures.
    wp_load. wp_pures.
    rewrite enc_get_low. wp_store. wp_pures. wp_load. wp_pures.
    iApply wp_for_post_return.
    wp_pures.
    by iApply "HΦ".
  }
  (* actually go to sleep *)
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hptsto".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hptsto Hptsto2 Htoks Hunfinished Hunfinished_token Hctr]") as "_".
  { by iFrame. }
  iModIntro.
  wp_pures. wp_store. wp_pures.
  wp_alloc v_ptr as "Hv_ptr". wp_pures.
  wp_load. wp_pures.
  rewrite enc_get_high. wp_store. wp_pures.
  wp_alloc w_ptr as "Hw_ptr". wp_pures.
  wp_load. wp_pures.
  rewrite enc_get_low. wp_store. wp_pures. wp_load. wp_pures.
  rewrite bool_decide_false //.
  wp_pures. wp_load. wp_pures. wp_load. wp_pures.
  wp_load. wp_pure_lc "Hlc". wp_pures.
  replace (1%Z) with (uint.Z (W32 1)) by reflexivity.
  rewrite enc_add_low.
  wp_apply (wp_Uint64__CompareAndSwap with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi".
  setoid_rewrite bool_decide_decide.
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists (enc waiters0 counter0).
  destruct (decide (_ = _)) as [Heq|Hneq].
  {
    apply enc_inj in Heq as [-> ->].
    rewrite decide_False.
    2:{ naive_solver. }
    iCombine "Hptsto Hptsto2" as "$".
    iSplitR; first done.
    iIntros "[Hptsto Hptsto2]".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[HR_in Hptsto Hptsto2 Htoks Hunfinished Hunfinished_token Hctr]") as "_".
    {
      iNext. repeat iExists _. iFrame "Hptsto ∗".
      iCombine "HR_in Htoks" as "Htoks".
      iDestruct (max_waiters with "[Htoks]") as %Hmax.
      { instantiate (1:=1 + uint.Z waiters).
        rewrite Z2Nat.inj_add //.
        word.
      }
      replace (uint.nat (word.add waiters (W32 1))) with (1 + uint.nat waiters)%nat by word.
      simpl. iFrame.
      iSplitL.
      { by destruct decide. }
      iPureIntro.
      intros Hun. exfalso. naive_solver.
    }
    iModIntro.
    wp_pures.
    wp_load.
    wp_pure_lc "Hlc".
    wp_pures.

    clear n unfinished_waiters Hunfinished_zero unfinished_waiters0 Hunfinished_zero0.

    wp_apply (wp_runtime_Semacquire with "[$]").
    iInv "HsemInv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iNamed "Hi".
    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iExists _; iFrame "Hs".
    iIntros "%Hsem Hsema".
    destruct (uint.nat sema) eqn:Hsema.
    { exfalso. lia. }
    rewrite replicate_S /=.
    iDestruct "HT" as "[Htok HT]".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[HT HS Hsema]") as "_".
    {
      iNext. iFrame.
      replace (uint.nat (word.sub sema (W32 1))) with n by word.
      iFrame.
    }
    iModIntro.
    wp_pure_lc "Hlc". wp_pure_lc "Hlc2". wp_pures.
    wp_load. wp_pures.
    wp_apply (wp_Uint64__Load with "[$]").
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iClear "Hv_ptr Hw_ptr Hstate_ptr". clear v_ptr counter w_ptr waiters state_ptr.
    clear unfinished_waiters sema n Hsema Hsem.
    iNamed "Hi".
    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iExists _. iFrame "Hptsto".
    destruct (decide (unfinished_waiters = W32 0)).
    {
      subst.
      iDestruct (zerostate_empty_token_false with "[$] [$]") as %[].
    }
    specialize (Hunfinished_zero ltac:(done)) as [-> ->].
    iIntros "Hptsto".
    iMod "Hmask" as "_".

    (* now, deallocate Htok. *)
    iInv "HsemInv" as "Hi" "Hclose2".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iNamed "Hi".
    iDestruct (own_zerostate_auth_half_agree with "[$] [$]") as %->.
    iMod (delete_zerostate_token with "[$] [$] [$]") as "[Hunfinished HS]".
    destruct (uint.nat unfinished_waiters) eqn:Hbad.
    { exfalso. apply n. word. }
    rewrite replicate_S /=.
    iDestruct "Hunfinished_token" as "[HR Hunfinished_token]".
    iMod ("Hclose2" with "[$]") as "_".
    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as (?) "[Hwg HΦ]".
    { solve_ndisj. }
    iCombine "Hwg Hctr" gives %[_ ->].
    iMod ("HΦ" with "[//] [$Hwg]") as "HΦ".
    iMod "Hmask".
    iMod ("Hclose" with "[Hptsto Hptsto2 Htoks Hunfinished Hunfinished_token Hctr]") as "_".
    {
      iFrame.
      replace (uint.nat (word.sub _ _)) with n0 by word.
      iFrame. done.
    }
    iModIntro.
    wp_pures.
    iApply wp_for_post_return.
    wp_pures.
    iApply "HΦ". done.
  }
  {
    iFrame "Hptsto".
    iSplitR; first done.
    iIntros "Hptsto".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hptsto Hptsto2 Htoks Hunfinished Hunfinished_token Hctr]") as "_".
    { iFrame. done. }
    iModIntro. wp_pures.
    iApply wp_for_post_do.
    wp_pures.
    iFrame.
  }
Qed.

End proof.
End goose_lang.

Typeclasses Opaque is_Mutex own_Mutex
            is_Locker is_Cond.
