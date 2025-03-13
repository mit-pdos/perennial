From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants ghost_map.
From Perennial.program_logic Require Import weakestpre.

Require Export New.code.sync.
From New.proof Require Import proof_prelude.
Require Export New.generatedproof.sync.

From New.proof Require Import sync.atomic.

Set Default Proof Using "Type".

Class syncG Σ := {
    #[global] wg_tokG :: ghost_mapG Σ w32 unit;
    #[global] wg_totalG :: ghost_varG Σ w32
  }.

Definition syncΣ := #[ghost_mapΣ w32 unit ; ghost_varΣ w32].
Global Instance subG_syncΣ{Σ} : subG (syncΣ) Σ → (syncG Σ).
Proof. solve_inG. Qed.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Section proof.
Context `{!heapGS Σ} `{!syncG Σ}.
Context `{!goGlobalsGS Σ}.

#[global]
Program Instance race_pkg_is_init : IsPkgInit race :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

#[global]
Program Instance pkg_is_init : IsPkgInit sync :=
  ltac2:(build_pkg_init ()).
Final Obligation. apply _. Qed.

(** This means [m] is a valid mutex with invariant [R]. *)
Definition is_Mutex (m: loc) (R : iProp Σ) : iProp Σ :=
  "#Hi" ∷ is_pkg_init sync ∗
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

Theorem init_Mutex R E m : is_pkg_init sync -∗ m ↦ (default_val Mutex.t) -∗ ▷ R ={E}=∗ is_Mutex m R.
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
    method_call #sync #"Mutex'ptr" #"Lock" #m #()
  {{{ RET #(); own_Mutex m ∗ R }}}.
Proof.
  wp_start as "H". iNamed "H".
  iLöb as "IH".
  wp_method_call. wp_call.
  wp_bind (CmpXchg _ _ _).
  iInv nroot as ([]) "[Hl HR]".
  - wp_bind (CmpXchg _ _ _).
    iApply (wp_typed_cmpxchg_fail (V:=bool) with "[$]").
    { done. }
    { naive_solver. }
    iNext.
    iIntros "Hl".
    iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
    wp_auto.
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
    rewrite /locked. wp_auto.
    iApply "HΦ".
    eauto with iFrame.
Qed.

(* this form is useful for defer statements *)
Lemma wp_Mutex__Unlock' m :
  {{{ is_pkg_init sync }}}
    method_call #sync #"Mutex'ptr" #"Unlock" #m
  {{{ (f : func.t), RET #f;
      ∀ R,
    {{{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}} #f #() {{{ RET #(); True }}}
  }}}.
Proof.
  iIntros (Ψ) "#Hdef HΨ".
  wp_method_call. wp_call.
  iApply "HΨ". iIntros (R).
  wp_start as "(#His & Hlocked & HR)".
  iNamed "His".
  wp_auto.
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
  iSplitR "HΦ"; last by wp_auto; iApply "HΦ".
  iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
  iDestruct "Hl" as "[Hl1 Hl2]".
  iNext. iExists false. iFrame.
Qed.

Lemma wp_Mutex__Unlock m R :
  {{{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}}
    method_call #sync #"Mutex'ptr" #"Unlock" #m #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#Hinv & Hlocked & HR)".
  wp_bind (method_call _ _ _ #m)%E.
  iNamed "Hinv".
  wp_apply (wp_Mutex__Unlock' with "[$]") as "% Hspec".
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
  is_Locker (interface.mk sync "Mutex'ptr"%go #m) (own_Mutex m ∗ R).
Proof.
  iIntros "#[? ?]".
  iSplitL.
  - iIntros (?) "!# _ HΦ".
    wp_auto.
    by wp_apply (wp_Mutex__Lock with "[$]").
  - iIntros (?) "!# [? ?] HΦ".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "#∗". }
    by iApply "HΦ".
Qed.

(** This means [c] is a condvar with underyling Locker at address [m]. *)
Definition is_Cond (c : loc) (m : interface.t) : iProp Σ :=
  "#Hi" ∷ is_pkg_init sync ∗
  "#Hc" ∷ c ↦s[sync.Cond :: "L"]□ m.

Global Instance is_Cond_persistent c m : Persistent (is_Cond c m) := _.

Theorem wp_NewCond (m : interface.t) :
  {{{ is_pkg_init sync }}}
    func_call #sync #"NewCond" #m
  {{{ (c: loc), RET #c; is_Cond c m }}}.
Proof.
  wp_start as "_".
  wp_apply wp_fupd.
  wp_alloc c as "Hc".
  wp_auto.
  iApply "HΦ".

  iDestruct (struct_fields_split with "Hc") as "Hl".
  iNamed "Hl".
  iMod (typed_pointsto_persist with "HL") as "$".
  iFrame "#". done.
Qed.

Theorem wp_Cond__Signal c lk :
  {{{ is_Cond c lk }}}
    method_call #sync #"Cond'ptr" #"Signal" #c #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[#Hdef Hc]".
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Broadcast c lk :
  {{{ is_Cond c lk }}}
    method_call #sync #"Cond'ptr" #"Broadcast" #c #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "H"; iNamed "H".
  wp_method_call. wp_call. iApply ("HΦ" with "[//]").
Qed.

Theorem wp_Cond__Wait c m R :
  {{{ is_Cond c m ∗ is_Locker m R ∗ R }}}
    method_call #sync #"Cond'ptr" #"Wait" #c #()
  {{{ RET #(); R }}}.
Proof.
  wp_start as "(#Hcond & #Hlock & HR)".
  iNamed "Hcond".
  wp_method_call. wp_call.
  iNamed "Hlock".
  wp_auto.
  wp_apply ("H_Unlock" with "[$]").
  wp_apply ("H_Lock" with "[$]") as "?".
  iApply "HΦ". done.
Qed.

Definition is_sema (x : loc) γ N : iProp Σ :=
  inv N (∃ (v : w32), x ↦ v ∗ ghost_var γ (1/2) v).

Definition own_sema γ (v : w32) : iProp Σ :=
  ghost_var γ (1/2) v.

Lemma wp_runtime_Semacquire (sema : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (⌜ uint.nat v > 0 ⌝ → own_sema γ (word.sub v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP func_call #sync #"runtime_Semacquire" #sema {{ Φ }}.
Proof.
  wp_start as "#Hsem".
  wp_for.
  wp_bind (! _)%E.
  iInv "Hsem" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hs Hv]".
  unshelve iApply (wp_typed_Load with "[$Hs]"); try tc_solve.
  { done. }
  iNext.
  iIntros "Hs".
  iMod ("Hclose" with "[$]") as "_".
  iModIntro.
  wp_auto.
  destruct bool_decide eqn:Hnz.
  { (* keep looping *)
    wp_auto.
    wp_for_post.
    iFrame.
  }

  (* try to acquire *)
  rewrite bool_decide_eq_false in Hnz.
  wp_auto.
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
    wp_auto.
    wp_for_post.
    done.
  }
  { (* cmpxchg will fail *)
    unshelve iApply (wp_typed_cmpxchg_fail with "[$]"); try tc_solve.
    { done. }
    { naive_solver. }
    iNext. iIntros "Hs".
    iMod ("Hclose" with "[$]") as "_".
    iModIntro.
    wp_auto.
    wp_for_post.
    iFrame.
  }
Qed.

Lemma wp_runtime_SemacquireWaitGroup (sema : loc) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (⌜ uint.nat v > 0 ⌝ → own_sema γ (word.sub v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP func_call #sync #"runtime_SemacquireWaitGroup" #sema {{ Φ }}.
Proof.
  wp_start as "#Hsem".
  wp_apply (wp_runtime_Semacquire with "[$]").
  iFrame.
Qed.

Lemma wp_runtime_Semrelease (sema : loc) γ N (_u1 : bool) (_u2 : w64):
  ∀ Φ,
  is_pkg_init sync ∗ is_sema sema γ N -∗
  (|={⊤∖↑N,∅}=> ∃ v, own_sema γ v ∗ (own_sema γ (word.add v (W32 1)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP func_call #sync #"runtime_Semrelease" #sema #_u1 #_u2 {{ Φ }}.
Proof.
Admitted.

Local Definition enc (low high : w32) : w64 :=
  word.add (word.slu (W64 (uint.Z high)) (W64 32)) (W64 (uint.Z low)).

Local Ltac local_word :=
  try apply word.unsigned_inj;
  repeat try (
      rewrite !word.unsigned_sru // ||
      rewrite word.unsigned_add ||
      rewrite word.unsigned_slu // ||
      rewrite !Z.shiftr_div_pow2 // ||
      rewrite Z.shiftl_mul_pow2 //
    );
  word
.

Local Lemma enc_get_high (low high : w32) :
  W32 (uint.Z (word.sru (enc low high) (W64 32))) = high.
Proof.
  local_word.
Qed.

Local Lemma enc_get_low (low high : w32) :
  W32 (uint.Z (enc low high)) = low.
Proof.
  local_word.
Qed.

Local Lemma enc_add_high (low high delta : w32) :
  word.add (enc low high) (word.slu (W64 (uint.Z delta)) (W64 32)) =
  enc low (word.add high delta).
Proof.
  local_word.
Qed.

Local Lemma enc_add_low (low high delta : w32) :
  uint.Z (word.add low delta) = uint.Z low + uint.Z delta →
  word.add (enc low high) (W64 (uint.Z delta)) =
  enc (word.add low delta) high.
Proof.
  intros. local_word.
Qed.

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

Record WaitGroup_names := {
    counter_gn : gname ;
    sema_gn : gname ;
    waiter_gn : gname ;
    zerostate_gn : gname ;
  }.

Implicit Type γ : WaitGroup_names.

(* FIXME: opaque *)
Definition own_WaitGroup_waiters γ (possible_waiters : w32) : iProp Σ :=
  ∃ (m : gset w32),
  ghost_map_auth γ.(waiter_gn) 1 (gset_to_gmap () m) ∗
  (* XXX: this helps maintain that the max number of waiters is [2^32-1] instead of [2^32]. *)
  (W32 0) ↪[γ.(waiter_gn)]□ () ∗
  ⌜ size m = S (uint.nat possible_waiters) ⌝.

Definition own_WaitGroup_wait_token γ : iProp Σ :=
  ∃ k,
    k ↪[γ.(waiter_gn)] () ∗
    (W32 0) ↪[γ.(waiter_gn)]□ ().

Definition own_zerostate_auth_half γ (unfinished_waiters : w32): iProp Σ :=
  ∃ (m : gset w32),
  ghost_map_auth γ.(zerostate_gn) (1/2) (gset_to_gmap () m) ∗
  ⌜ size m = uint.nat unfinished_waiters ⌝.

Definition own_zerostate_token γ : iProp Σ :=
  ∃ k, k ↪[γ.(zerostate_gn)] ().

Local Definition is_WaitGroup_inv wg γ N : iProp Σ :=
  inv (N.@"wg") (∃ counter waiters unfinished_waiters,
  "Hptsto" ∷ own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter) ∗
  "Hptsto2" ∷ (
      if decide (counter = W32 0 ∧ waiters ≠ W32 0) then True
      else own_Uint64 (struct.field_ref_f sync.WaitGroup "state" wg) (DfracOwn (1/2)) (enc waiters counter)
    ) ∗
  "Hctr" ∷ ghost_var γ.(counter_gn) (1/2)%Qp counter ∗

  "Hunfinished" ∷ own_zerostate_auth_half γ unfinished_waiters ∗
  "Hunfinished_token" ∷  [∗] (replicate (uint.nat unfinished_waiters) (own_WaitGroup_wait_token γ)) ∗

  "Htoks" ∷ ([∗] (replicate (uint.nat waiters) (own_WaitGroup_wait_token γ))) ∗
  "%Hunfinished_zero" ∷ ⌜ unfinished_waiters ≠ W32 0 → waiters = W32 0 ∧ counter = W32 0 ⌝
  )%I.

Local Definition is_WaitGroup_sema_inv γ N : iProp Σ :=
  inv (N.@"semInv") (∃ (unfinished_waiters sema : w32),
        "Hs" ∷ own_sema γ.(sema_gn) sema ∗
        "HT" ∷  [∗] (replicate (uint.nat sema) (own_zerostate_token γ)) ∗
        "HS" ∷ own_zerostate_auth_half γ unfinished_waiters
    ).

Local Definition is_WaitGroup wg γ N : iProp Σ :=
  "#Hsem" ∷ is_sema (struct.field_ref_f sync.WaitGroup "sema" wg) γ.(sema_gn) (N.@"sema") ∗
  "#Hinv" ∷ is_WaitGroup_inv wg γ N ∗
  "#HsemInv" ∷ is_WaitGroup_sema_inv γ N.

Lemma size_fin_to_set_w32:
  size (fin_to_set w32 : gset w32) = (Z.to_nat (2^32 : Z)).
Proof.
  unfold fin_to_set.
  rewrite -> size_list_to_set by apply finite.NoDup_enum.
  replace (length (finite.enum _)) with (finite.card w32) by reflexivity.
  pose proof (finite.fin_card (Z.to_nat (2^32 : Z))) as <-.
  symmetry.
  set (f := λ (x : fin (Z.to_nat (2^32 : Z))), W32 (Z.of_nat (fin_to_nat x))).
  unshelve eapply (finite.bijective_card f).
  {
    intros ???. subst f.
    simpl in *.
    apply fin_to_nat_inj.
    pose proof (fin_to_nat_lt x).
    pose proof (fin_to_nat_lt y).
    intros.
    (* FIXME: word. *)
    word_cleanup.
    word.
  }
  {
    intros ?.
    subst f. simpl.
    unshelve eexists (nat_to_fin (p:=uint.nat y) _).
    2:{ rewrite fin_to_nat_to_fin. word. }
    word.
  }
Qed.

(* Prepare to Wait() *)
Lemma alloc_wait_token γ (w : w32) :
  uint.Z (word.add w (W32 1)) = uint.Z w + 1 →
  own_WaitGroup_waiters γ w ==∗ own_WaitGroup_waiters γ (word.add w (W32 1)) ∗ own_WaitGroup_wait_token γ.
Proof.
  intros.
  iIntros "(% & (H &#? & %))".
  unshelve epose proof (size_pos_elem_of (fin_to_set w32 ∖ m) _) as [new Helem].
  { rewrite -> size_difference by set_solver. rewrite size_fin_to_set_w32. word. }
  iMod (ghost_map_insert new () with "[$]") as "[? ?]".
  { rewrite lookup_gset_to_gmap_None. set_solver. }
  rewrite -gset_to_gmap_union_singleton.
  iFrame "∗#".
  iPureIntro. rewrite H.
  rewrite size_union //.
  2:{ set_solver. }
  rewrite size_singleton. word.
Qed.

Lemma max_waiters (n : Z) γ :
  ([∗] replicate (Z.to_nat n) (own_WaitGroup_wait_token γ)) -∗
  ⌜ n < 2^32 ⌝.
Proof.
  iIntros "H".
  destruct (Z.to_nat n) eqn:Hn.
  { word. }
  iAssert (∃ (m : gset w32 ), ⌜ size m = S (Z.to_nat n) ⌝ ∗
                              ([∗ set] k ∈ m, ∃ dq, k ↪[γ.(waiter_gn)]{dq} ())
          )%I with "[H]" as "(%m & %Heq & _)".
  2:{
    iPureIntro.
    assert (m ⊆ (fin_to_set w32)) as Hsz by set_solver.
    apply subseteq_size in Hsz.
    rewrite size_fin_to_set_w32 in Hsz.
    rewrite Heq /= in Hsz.
    word.
  }
  rewrite Hn. clear n Hn.
  rename n0 into n.
  iInduction n as [|].
  {
    iDestruct "H" as "[(% & ? & ?) _]".
    destruct (decide (k = W32 0)).
    { iExFalso. subst. iDestruct (ghost_map_elem_valid_2 with "[$] [$]") as %Hv. naive_solver. }
    iExists {[ k; W32 0 ]}.
    assert ({[k]} ## ({[W32 0]} : gset w32)) by set_solver.
    iSplitR.
    { iPureIntro. rewrite -> size_union by set_solver. rewrite !size_singleton //. }
    rewrite big_sepS_union // !big_sepS_singleton.
    iFrame.
  }
  { generalize (S n) as n'. intros. clear n. rename n' into n.
    rewrite replicate_S.
    iDestruct "H" as "[Helem H]".
    iDestruct ("IHn" with "[$]") as "(% & % & H)".
    iDestruct "Helem" as (?) "[? _]".
    destruct (decide (k ∈ m)).
    {
      iExFalso.
      iDestruct (big_sepS_elem_of_acc with "H") as "[H _]".
      { done. }
      iDestruct "H" as (?) "?".
      iDestruct (ghost_map_elem_valid_2 with "[$] [$]") as %[Hv _].
      apply dfrac_valid_own_r in Hv. done.
    }
    iExists ({[k]} ∪ m).
    rewrite -> size_union by set_solver.
    rewrite size_singleton. iSplitR.
    { word. }
    rewrite -> big_sepS_union by set_solver.
    iFrame. rewrite big_sepS_singleton. iFrame.
  }
Qed.

Lemma waiters_none_token_false γ :
  own_WaitGroup_waiters γ (W32 0) -∗ own_WaitGroup_wait_token γ -∗ False.
Proof.
  iIntros "(% & Hauth & Hptsto1 & %)".
  iIntros "(% & Hptsto2 & _)".
  iCombine "Hauth Hptsto1" gives %Hlookup1.
  iCombine "Hauth Hptsto2" gives %Hlookup2.
  destruct (decide (k = W32 0)).
  { subst. iDestruct (ghost_map_elem_valid_2 with "[$] [$]") as %[Hv _]. naive_solver. }
  rewrite !lookup_gset_to_gmap_Some in Hlookup1, Hlookup2.
  intuition.
  assert ({[W32 0 ; k]} ⊆ m) as Hsz.
  { set_solver. }
  apply subseteq_size in Hsz.
  rewrite -> size_union in Hsz by set_solver.
  rewrite !size_singleton in Hsz. word.
Qed.

Lemma alloc_zerostate_token uw γ :
  uint.Z (word.add uw (W32 1)) = uint.Z uw + 1 →
  own_zerostate_auth_half γ uw -∗ own_zerostate_auth_half γ uw ==∗
  own_zerostate_auth_half γ (word.add uw (W32 1)) ∗ own_zerostate_auth_half γ (word.add uw (W32 1)) ∗
  own_zerostate_token γ.
Proof.
  intros. iIntros "Ha1 Ha2".
  iDestruct "Ha1" as "(% & Ha1 & %)".
  iDestruct "Ha2" as "(% & Ha2 & %)".
  iCombine "Ha1 Ha2" gives %[_ Heq].
  apply (f_equal dom) in Heq.
  rewrite !dom_gset_to_gmap in Heq. subst.
  iCombine "Ha1 Ha2" as "Ha".
  unshelve epose proof (size_pos_elem_of (fin_to_set w32 ∖ m0) _) as [new Helem].
  { rewrite -> size_difference by set_solver. rewrite size_fin_to_set_w32. word. }
  iMod (ghost_map_insert new () with "Ha") as "[Ha ?]".
  { rewrite lookup_gset_to_gmap_None. set_solver. }
  iFrame.
  rewrite -gset_to_gmap_union_singleton.
  iDestruct "Ha" as "($ & $)". iPureIntro.
  apply and_wlog_r; last done.
  rewrite -> size_union by set_solver.
  rewrite size_singleton. word.
Qed.

Lemma alloc_many_zerostate_tokens uw γ :
  own_zerostate_auth_half γ (W32 0) -∗ own_zerostate_auth_half γ (W32 0) ==∗
  own_zerostate_auth_half γ uw ∗ own_zerostate_auth_half γ uw ∗ ([∗] replicate (uint.nat uw) (own_zerostate_token γ)).
Proof.
  assert (∃ n, n = (uint.nat uw)) as [n Heq].
  { by eexists. }
  iInduction n as [] forall (uw Heq).
  { rewrite -Heq.
    replace (uw) with (W32 0) by word.
    iIntros "$ $". rewrite replicate_0. iModIntro. done. }
  rewrite -Heq.
  iIntros "? ?".
  simpl.
  iMod ("IHn" $! (word.sub uw (W32 1)) with "[] [$] [$]") as "(Huw & Huw' & ?)".
  { word. }
  replace (uint.nat (word.sub _ _)) with n by word.
  iFrame.
  iMod (alloc_zerostate_token with "[$] [$]") as "(? & ? & $)".
  { word. }
  replace (word.add (word.sub _ _) _) with (uw) by ring.
  by iFrame.
Qed.

Lemma zerostate_empty_token_false γ :
  own_zerostate_auth_half γ (W32 0) -∗ own_zerostate_token γ -∗ False.
Proof.
  iIntros "(% & Ha1 & %) (% & Hp)".
  apply size_empty_inv in H.
  apply leibniz_equiv in H as ->.
  iCombine "Ha1 Hp" gives %Hbad. done.
Qed.

Lemma zerostate_tokens_bound (n : nat) w γ :
  own_zerostate_auth_half γ w -∗ [∗] replicate n (own_zerostate_token γ) -∗ ⌜ n ≤ uint.nat w ⌝.
Proof.
  iIntros "(% & Ha & %) H".
  iAssert (
      ∃ (x : gset w32),
        ⌜ size x = n ⌝ ∗
        ⌜ x ⊆ m ⌝ ∗
        ([∗ set] k ∈ x, k ↪[γ.(zerostate_gn)] ()) ∗
        ghost_map_auth γ.(zerostate_gn) (1 / 2) (gset_to_gmap ()%V m)
    )%I with "[-]" as "(% & % & %Hsz & _)".
  2:{ iPureIntro. subst. apply subseteq_size in Hsz. word. }
  iInduction n as [|].
  {
    iExists ∅. iSplitR; first done.
    iSplitR; first done. iFrame. done.
  }
  rewrite replicate_S.
  iDestruct "H" as "[Ht H]".
  iDestruct ("IHn" with "[$] [$]") as (?) "(% & % & H & Ha)".
  iDestruct "Ht" as "(% & Ht)".
  destruct (decide (k ∈ x)).
  {
    iDestruct (big_sepS_elem_of_acc with "H") as "[H _]".
    { eassumption. }
    iCombine "Ht H" gives %Hbad. exfalso. naive_solver.
  }
  iCombine "Ht Ha" gives %Hlookup.
  apply lookup_gset_to_gmap_Some in Hlookup as [? _].
  iExists ({[k]} ∪ x).
  iFrame.
  iSplitR.
  { iPureIntro. rewrite -> size_union by set_solver. rewrite size_singleton. word. }
  iSplitR.
  { iPureIntro. set_solver. }
  rewrite -> big_sepS_union by set_solver.
  iFrame. rewrite big_sepS_singleton. iFrame.
Qed.

Lemma delete_zerostate_token uw γ :
  own_zerostate_auth_half γ uw -∗ own_zerostate_auth_half γ uw -∗
  own_zerostate_token γ ==∗
  own_zerostate_auth_half γ (word.sub uw (W32 1)) ∗ own_zerostate_auth_half γ (word.sub uw (W32 1)).
Proof.
  iIntros "(% & Ha1 & %) (% & Ha2 & %) (% & Ht)".
  iCombine "Ha1 Ha2" gives %[_ Heq%(f_equal dom)].
  rewrite !dom_gset_to_gmap in Heq. subst.
  iCombine "Ha1 Ha2" as "Ha".
  iCombine "Ha Ht" gives %Hlookup.
  apply lookup_gset_to_gmap_Some in Hlookup as [Helem _].
  iMod (ghost_map_delete with "[$] [$]") as "H".
  iModIntro.
  rewrite -gset_to_gmap_difference_singleton.
  iDestruct "H" as "[$ $]".
  iPureIntro.
  apply and_wlog_r; last done.
  rewrite -> size_difference by set_solver.
  rewrite size_singleton.
  enough (size m0 ≠ O) by word.
  intros Hbad. apply size_empty_inv in Hbad.
  set_solver.
Qed.

Lemma own_zerostate_auth_half_agree uw uw' γ :
  own_zerostate_auth_half γ uw -∗ own_zerostate_auth_half γ uw' -∗ ⌜ uw = uw' ⌝.
Proof.
  iIntros "(% & ? & %) (% & ? & %)".
  iDestruct (ghost_map_auth_agree with "[$] [$]") as %Heq.
  apply (f_equal dom) in Heq.
  rewrite !dom_gset_to_gmap in Heq. subst. word.
Qed.

Definition own_WaitGroup γ (counter : w32) : iProp Σ :=
  ghost_var γ.(counter_gn) (1/2)%Qp counter.

Local Lemma wg_delta_to_w32 (delta' : w32) (delta : w64) :
  delta' = (W32 (uint.Z delta)) →
  word.slu delta (W64 32) = word.slu (W64 (uint.Z delta')) (W64 32).
Proof.
  intros ->. local_word.
Qed.

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

Lemma wp_WaitGroup__Add (wg : loc) (delta : w64) γ N :
  let delta' := (W32 (uint.Z delta)) in
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N -∗
  (|={⊤,↑N}=>
     ∃ oldc,
       "Hwg" ∷ own_WaitGroup γ oldc ∗
       "%Hbounds" ∷ ⌜ 0 ≤ sint.Z oldc + sint.Z delta' < 2^31 ⌝ ∗
       "HnoWaiters" ∷ (⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters γ (W32 0)) ∗
       "HΦ" ∷ ((⌜ oldc ≠ W32 0 ⌝ ∨ own_WaitGroup_waiters γ (W32 0)) -∗
               own_WaitGroup γ (word.add oldc delta') ={↑N,⊤}=∗ Φ #())
  ) -∗
  WP method_call #sync #"WaitGroup'ptr" #"Add" #wg #delta {{ Φ }}.
Proof.
  intros delta'.
  wp_start as "#His".
  wp_apply wp_with_defer as "%defer defer".
  simpl subst. wp_auto_lc 1.
  wp_apply wp_Uint64__Add.
  iMod "HΦ".
  iNamed "HΦ".
  unfold own_WaitGroup.
  iNamed "His".
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
    iDestruct (waiters_none_token_false with "[$] [$]") as %[].
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
    iDestruct (waiters_none_token_false with "[$] [$]") as %[].
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
    wp_auto.
    rewrite enc_get_high enc_get_low.

    destruct bool_decide eqn:Hbad.
    {
      exfalso.
      rewrite bool_decide_eq_true in Hbad.
      (* FIXME: word should do these. *)
      rewrite word.signed_add in Hbad.
      replace (sint.Z (W32 0)) with 0 in * by reflexivity.
      rewrite word.swrap_inrange in Hbad; lia.
    }
    wp_auto.
    wp_bind (if: _ then _ else do: #())%E.
    clear Hbad.
    iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[-]").
    {
      destruct bool_decide eqn:Heq0.
      - wp_auto.
        iSplitR; first done.
        iNamedAccu.
      - rewrite bool_decide_eq_false in Heq0.
        wp_auto.
        destruct bool_decide eqn:Heq1.
        + wp_auto.
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
              apply Heq0. intuition. exfalso. apply H2.
              { apply word.signed_inj. rewrite H //. }
              word.
            }
          * wp_auto. iFrame. done.
        + wp_auto. iFrame. done.
    }
    iIntros (?) "[% H]". iNamed "H".
    subst.
    wp_auto.
    destruct (bool_decide) eqn:Heq1.
    { (* no need to wake anyone up *) wp_auto. iFrame. }
    rewrite bool_decide_eq_false in Heq1.
    wp_auto.
    rewrite bool_decide_true.
    { (* no need to wake anyone up *) wp_auto. iFrame. }
    apply not_and_l in HnoWake, HnotInWakingState.
    destruct HnoWake as [|].
    2:{ by apply dec_stable. }
    destruct HnotInWakingState as [|].
    2:{ by apply dec_stable. }
    apply Znot_gt_le in Heq1.
    exfalso.
    apply H. clear H. apply word.signed_inj.
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
  wp_auto. rewrite enc_get_high enc_get_low.

  destruct bool_decide eqn:Hbad.
  {
    exfalso.
    rewrite bool_decide_eq_true in Hbad.
    (* FIXME: word should do these. *)
    rewrite word.signed_add in Hbad.
    replace (sint.Z (W32 0)) with 0 in * by reflexivity.
    rewrite word.swrap_inrange in Hbad; lia.
  }
  wp_auto.
  wp_bind (if: _ then _ else do: #())%E.
  clear Hbad.
  iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val #tt ⌝ ∗ _)%I with "[-]").
  {
    destruct bool_decide eqn:Heq0.
    - wp_auto.
      iSplitR; first done.
      iNamedAccu.
    - rewrite bool_decide_eq_false in Heq0.
      wp_auto.
      destruct bool_decide eqn:Heq1.
      + wp_auto.
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
            apply Heq0. intuition. exfalso. apply H4.
            { apply word.signed_inj. rewrite H //. }
            word.
          }
        * wp_auto. iFrame. done.
      + wp_auto. iFrame. done.
  }
  iIntros (?) "[% H]". iNamed "H".
  subst.
  wp_auto.
  rewrite bool_decide_false.
  2:{ intuition. word. }
  wp_auto.
  rewrite bool_decide_false.
  2:{ intuition. }
  wp_auto.
  wp_apply wp_Uint64__Load.
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hwg".
  iMod "Hmask" as "_".
  iModIntro.
  wp_auto.
  rewrite bool_decide_true //.
  wp_auto_lc 2.

  (* want to get a bunch of unfinisheds. *)
  wp_apply wp_Uint64__Store.
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
  wp_auto.
  (* call semrelease. *)

  iAssert (
      ∃ (wrem : w32),
        "w" ∷ w_ptr ↦ wrem ∗
        "Hunfinished_tokens" ∷ [∗] replicate (uint.nat wrem) (own_zerostate_token γ)
    )%I with "[$]" as "HloopInv".

  wp_for.
  iNamed "HloopInv".
  wp_auto.
  destruct bool_decide eqn:Hwrem.
  { (* no more waiters to wake up. *)
    rewrite decide_False; last naive_solver.
    rewrite decide_True //.
    wp_auto. iFrame.
  }

  (* wake up another waiter *)
  rewrite bool_decide_eq_false in Hwrem.
  rewrite decide_True //.
  wp_auto_lc 1.
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
    iDestruct (zerostate_tokens_bound (S (uint.nat sema)) with "[$] [$]") as %Hs.
    iFrame "Hs ∗".
    replace (uint.nat (word.add sema (W32 1))) with (S (uint.nat sema))%nat by word.
    iFrame.
  }
  iModIntro.
  wp_auto.
  wp_for_post.
  iFrame.
Qed.

Lemma wp_WaitGroup__Wait (wg : loc) (delta : w64) γ N :
  ∀ Φ,
  is_pkg_init sync ∗ is_WaitGroup wg γ N ∗ own_WaitGroup_wait_token γ -∗
  (|={⊤∖↑N, ∅}=>
     ∃ oldc,
       own_WaitGroup γ oldc ∗ (⌜ sint.Z oldc = 0 ⌝ → own_WaitGroup γ oldc ={∅,⊤∖↑N}=∗
                               own_WaitGroup_wait_token γ -∗ Φ #())
  ) -∗
  WP method_call #sync #"WaitGroup'ptr" #"Wait" #wg #() {{ Φ }}.
Proof.
  wp_start as "(#Hwg & HR_in)". iNamed "Hwg".
  wp_auto.
  wp_for_core. (* TODO: need to set later credits *)
  wp_auto_lc 1.
  rewrite decide_True //. wp_auto.
  wp_apply (wp_Uint64__Load).
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
    wp_auto. rewrite enc_get_high enc_get_low bool_decide_true //=.
    wp_auto.
    wp_for_post.
    by iApply "HΦ".
  }
  (* actually go to sleep *)
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _; iFrame.
  iIntros "Hptsto".
  iMod "Hmask" as "_".

  iDestruct (max_waiters (1 + uint.Z waiters) with "[-]") as %HwaitersLe.
  {
    rewrite -> Z2Nat.inj_add by word.
    iFrame.
  }
  iMod ("Hclose" with "[Hptsto Hptsto2 Htoks Hunfinished Hunfinished_token Hctr]") as "_".
  { by iFrame. }
  iModIntro.
  wp_auto.
  rewrite enc_get_high enc_get_low bool_decide_false //.
  wp_auto_lc 1.
  replace (1%Z) with (uint.Z (W32 1)) by reflexivity.
  rewrite -> enc_add_low by word.
  wp_apply (wp_Uint64__CompareAndSwap).
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
      iDestruct (max_waiters (1+uint.Z waiters) with "[Htoks]") as %Hmax.
      {
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
    wp_auto_lc 1.

    clear n unfinished_waiters Hunfinished_zero unfinished_waiters0 Hunfinished_zero0.

    wp_apply (wp_runtime_SemacquireWaitGroup with "[$]").
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
    wp_auto_lc 2.
    wp_apply (wp_Uint64__Load).
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iClear "v w state". clear v_ptr counter w_ptr waiters state_ptr HwaitersLe.
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
    wp_auto.
    wp_for_post.
    iApply "HΦ". done.
  }
  {
    iFrame "Hptsto".
    iSplitR; first done.
    iIntros "Hptsto".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hptsto Hptsto2 Htoks Hunfinished Hunfinished_token Hctr]") as "_".
    { iFrame. done. }
    iModIntro. wp_auto.
    wp_for_post.
    iFrame.
  }
Qed.

End proof.
End goose_lang.

Typeclasses Opaque is_Mutex own_Mutex
            is_Locker is_Cond.
