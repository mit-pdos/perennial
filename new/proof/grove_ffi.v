(** Iris specs for Grove FFI *)
From iris.bi.lib Require Import fixpoint.
From iris.base_logic.lib Require Import mono_nat saved_prop.
From Perennial.program_logic Require Export atomic_fupd.
From New.proof Require Export proof_prelude.
From Perennial.goose_lang.ffi.grove_ffi Require Export grove_ffi.
From New.code.github_com.mit_pdos.gokv Require Import grove_ffi.

Set Default Proof Using "Type".

(** * Specs for user-facing operations *)
Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  (* FIXME: figure out which of these clients need to set *)
  Set Printing Projections.
  Existing Instances grove_op grove_model grove_semantics grove_interp goose_groveGS goose_groveNodeGS.

  Context `{!heapGS Σ}.

  Lemma wp_Listen c_l s E :
    {{{ True }}}
      Listen #c_l @ s; E
    {{{ RET listen_socket c_l; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_call.
    rewrite to_val_unseal. by iApply wp_ListenOp.
  Qed.

  Lemma wp_Connect c_r s E :
    {{{ True }}}
      Connect #c_r @ s; E
    {{{ (err : bool) (c_l : chan),
        RET struct.val ConnectRet [
              "Err" ::= #err;
              "Connection" ::= if err then bad_socket else connection_socket c_l c_r
            ];
      if err then True else c_l c↦ ∅
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_call.
    wp_bind (ExternalOp _ _)%E. rewrite [in #c_r]to_val_unseal. iApply (wp_ConnectOp with "[//]").
    iNext. iIntros (err recv) "Hr". wp_pures.
    replace (LitV err) with #err.
    2:{ rewrite to_val_unseal //. }
    by iApply "HΦ".
  Qed.

  Lemma wp_Accept c_l s E :
    {{{ True }}}
      Accept (listen_socket c_l)  @ s; E
    {{{ (c_r : chan), RET connection_socket c_l c_r; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_call.
    by iApply wp_AcceptOp.
  Qed.

  Ltac inv_undefined :=
    match goal with
    | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
        destruct e; try (apply suchThat_false in H; contradiction)
    end.

  Local Ltac solve_atomic :=
    apply strongly_atomic_atomic, ectx_language_atomic;
                                  [ apply heap_base_atomic; cbn [relation.denote base_trans]; intros * H;
                                    repeat inv_undefined;
                                    try solve [ apply atomically_is_val in H; auto ]
                                  |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].
  Local Ltac solve_atomic2 :=
    solve_atomic;
    (* TODO(Joe): Cleanup *)
    repeat match goal with
           | [ h : context [to_val]  |- _ ] => rewrite !to_val_unseal in h
           | [ |- context [to_val] ] => rewrite !to_val_unseal
           | [ H: relation.denote _ ?s1 ?s2 ?v |- _ ] => inversion_clear H
           | _ => progress monad_inv
           | _ => case_match
           end; eauto.

  Local Lemma own_slice_to_pointsto_vals s dq (vs : list u8) :
    s ↦*{dq} vs -∗ pointsto_vals s.(slice.ptr_f) dq (data_vals vs).
  Proof.
    rewrite own_slice_unseal /own_slice_def /pointsto_vals.
    iIntros "(Hs & _ & _)". simpl.
    rewrite big_sepL_fmap.
    iApply (big_sepL_impl with "Hs").
    iModIntro. iIntros "* % Hp". rewrite go_type_size_unseal /= left_id.
    rewrite typed_pointsto_unseal /typed_pointsto_def to_val_unseal /=.
    iDestruct select (_) as "[Hp %Hty]". inversion Hty; subst.
    rewrite loc_add_0. iFrame.
  Qed.

  Local Lemma pointsto_vals_to_own_slice (p : loc) (cap : w64) (dq : dfrac) (d : list w8) :
    (length d) = uint.nat (length d) →
    (length d) ≤ uint.Z cap →
    pointsto_vals p dq (data_vals d) -∗
    (slice.mk p (length d) cap) ↦*{dq} d.
  Proof.
    intros Hoverflow Hcap.
    rewrite own_slice_unseal /own_slice_def /pointsto_vals.
    iIntros "Hl". simpl.
    iSplitL.
    2:{ iPureIntro. word. }
    rewrite big_sepL_fmap.
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros "* % Hp". rewrite go_type_size_unseal /= left_id.
    rewrite typed_pointsto_unseal /typed_pointsto_def.
    destruct (d !! k).
    2:{ exfalso. done. }
    simpl in *. inversion H; subst.
    rewrite to_val_unseal /= right_id loc_add_0.
    iFrame.
  Qed.

  Lemma wp_Send c_l c_r (s : slice.t) (data : list u8) (dq : dfrac) :
    ⊢ {{{ s ↦*{dq} data }}}
      <<< ∀∀ ms, c_r c↦ ms >>>
        Send (connection_socket c_l c_r) (slice.val s) @ ∅
      <<< ∃∃ (msg_sent : bool),
        c_r c↦ (if msg_sent then ms ∪ {[Message c_l data]} else ms)
      >>>
      {{{ (err : bool), RET #err; ⌜if err then True else msg_sent⌝ ∗
                                s ↦*{dq} data }}}.
  Proof.
    iIntros "!#" (Φ) "Hs HΦ".
    wp_call.
    destruct s.
    iDestruct (own_slice_len with "Hs") as "%Hlen".
    iDestruct (own_slice_wf with "Hs") as "%Hwf".
    rewrite difference_empty_L /=.
    iMod "HΦ" as (ms) "[Hc HΦ]".
    { solve_atomic2. }
    cbn in *.
    rewrite to_val_unseal.
    iApply (wp_SendOp with "[$Hc Hs]").
    { done. }
    { iApply (own_slice_to_pointsto_vals with "[$]"). }
    iNext. iIntros (err_early err_late) "[Hc Hl]".
    iApply ("HΦ" $! (negb err_early) with "[Hc]").
    { by destruct err_early. }
    iSplit.
    - iPureIntro. by destruct err_early, err_late.
    - iDestruct (pointsto_vals_to_own_slice with "Hl") as "H".
      { word. }
      2:{ iExactEq "H". repeat f_equal. word. }
      word.
  Qed.

  Lemma wp_Receive c_l c_r :
    ⊢ <<< ∀∀ ms, c_l c↦ ms >>>
        Receive (connection_socket c_l c_r) @ ∅
      <<< ∃∃ (err : bool) (data : list u8),
        c_l c↦ ms ∗ if err then True else ⌜Message c_r data ∈ ms⌝
      >>>
      {{{ s,
        RET struct.val ReceiveRet [
              "Err" ::= #err;
              "Data" ::= #s
            ];
          s ↦* data
      }}}.
  Proof.
    iIntros "!#" (Φ) "HΦ". wp_call.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iMod "HΦ" as (ms) "[Hc HΦ]".
    { solve_atomic2. }
    iApply (wp_RecvOp with "Hc").
    iIntros "!#" (err l len data) "(%Hm & Hc & Hl)".
    iMod ("HΦ" $! err data with "[Hc]") as "HΦ".
    { iFrame. destruct err; first done. iPureIntro. apply Hm. }
    iModIntro. wp_pures.
    destruct err.
    {
      rewrite to_val_unseal /= slice.val_unseal /slice.val_def to_val_unseal /=.
      iApply ("HΦ" $! (slice.mk _ _ _)). destruct Hm as (-> & -> & ->).
      iApply own_slice_empty. done. }
    destruct Hm as [Hin Hlen].
    rewrite to_val_unseal /= slice.val_unseal /slice.val_def to_val_unseal /=.
    iApply ("HΦ" $! (slice.mk _ _ _)).
    iDestruct (pointsto_vals_to_own_slice with "Hl") as "H".
    { word. }
    2:{ iExactEq "H". repeat f_equal. word. }
    word.
  Qed.

  Context `{!savedPropG Σ}.
  Context `{!inG Σ (exclR unitO)}.
  Definition Ncrash := nroot.
  Definition own_crash_concrete P Pc : iProp Σ :=
    ∃ γprop γtok,
    saved_prop_own γprop (DfracOwn (1/2)) P ∗
      inv Ncrash (∃ Q, saved_prop_own γprop (DfracOwn (1/2)) Q ∗ (Q ∧ Pc ∨ own γtok (Excl ()) ∗ C))
  .

  Definition own_crash_abstract_pre Pc (ρ : iProp Σ → iProp Σ) (P : iProp Σ) : iProp Σ :=
    £ 2 -∗ |NC={⊤,∅}=> P ∗ (∀ P', (P' -∗ Pc) -∗ P' -∗ |NC={∅,⊤}=> ρ P').

  Definition own_crash_abstract Pc P : iProp Σ :=
    bi_greatest_fixpoint (own_crash_abstract_pre Pc) P.

  Lemma own_crash_unfold P Pc :
    own_crash_abstract Pc P -∗
    own_crash_abstract_pre Pc (own_crash_abstract Pc) P.
  Proof.
    iIntros "H".
    rewrite /own_crash_abstract.
    erewrite greatest_fixpoint_unfold.
    2:{
      constructor.
      - intros. iIntros "#Himpl * H".
        rewrite /own_crash_abstract_pre.
        iIntros "Hlc".
        iMod ("H" with "Hlc") as "[$ H]". iModIntro.
        iIntros (?) "Hwand HP'".
        iApply "Himpl".
        iApply ("H" with "[$] [$]").
      - intros.
        solve_proper.
    }
    iIntros "Hlc".
    iMod ("H" with "Hlc") as "[$ H]".
    iIntros "!# * Hwand HP'".
    iApply ("H" with "[$] [$]").
  Qed.

  Lemma alloc_own_crash P Pc :
    P ∧ Pc ={⊤}=∗ own_crash_abstract Pc P ∗ |C={⊤}=> ▷ Pc.
  Proof using Type*.
    iIntros "HP".
    iMod (saved_prop_alloc P (DfracOwn 1)) as (γprop) "[Hprop Hprop2]"; first done.
    iMod (own_alloc (Excl ())) as (γtok) "Htok"; first done.
    iMod (inv_alloc Ncrash ⊤ (∃ Q, saved_prop_own γprop (DfracOwn (1/2)) Q ∗ (Q ∧ Pc ∨ own γtok (Excl ()) ∗ C)) with "[-Hprop Htok]") as "#Hinv".
    { iNext. iExists _; iFrame. }
    iSplitL "Hprop".
    {
      iModIntro.
      iApply (greatest_fixpoint_coiter _ (λ P, saved_prop_own γprop (DfracOwn (1/2)) P)%I).
      2:{ iFrame. }
      iIntros "!# * Hprop".
      iIntros "[Hlc Hlc2]".
      rewrite ncfupd_eq.
      iIntros (?) "HNC".
      iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "[$] Hi") as (?) "[Hprop2 Hi]".
      iDestruct (saved_prop_agree with "[$] [$]") as "#-#Hagree".
      iMod (lc_fupd_elim_later with "[$] Hagree") as "#Hagree".
      iRewrite -"Hagree".
      iDestruct "Hi" as "[Hi | [_ Hbad]]".
      2:{
        iDestruct (NC_C with "[$] [$]") as %?. done.
      }
      iLeft in "Hi". iFrame "Hi".
      iFrame.
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "Hmask".
      iFrame.
      iIntros (?) "Hwand HP'".
      iIntros (?) "$".
      iMod "Hmask".
      iMod (saved_prop_update_2 with "[$] [$]") as "[$ H]".
      { rewrite Qp.half_half //. }
      iMod ("Hclose" with "[-]"); last done.
      iNext.
      iExists _; iFrame.
      iLeft. iSplit.
      { iFrame. }
      iApply "Hwand". iFrame.
    }
    iModIntro.
    iIntros "C".
    iInv "Hinv" as "Hi" "Hclose".
    iDestruct "Hi" as (?) "[? [H|>[Hbad _]]]".
    2:{ iCombine "Htok Hbad" gives %Hbad. done. }
    iRight in "H".
    iFrame.
    iMod ("Hclose" with "[-]"); last done.
    iNext. iExists _; iFrame. iRight. iFrame.
  Qed.

  (* want:
     combine: own_crash P Pc -∗ own_crash Q Qc -∗
     own_crash (P ∗ Q) (Pc Qc)

     split: own_crash (P ∗ Q) (Pc ∗ Qc) -∗
     own_crash P Pc ∗ own_crash Q Qc
     if P -∗ |C={⊤}=> Pc and Q -∗ |C={⊤}=> Qc.
   *)

  (* FIXME: this is actually logically atomic because the model doesn't capture
     the fact that reads and writes are non-atomic w.r.t. concurrency.
     This avoids existentially quantifying c inside the fupd to require the
     caller to "know" the file contents before callin Read.
   *)
  Lemma wp_FileRead f dq c E Φ :
    ⊢ (|NC={E, ∅}=> f f↦{dq} c ∗ (f f↦{dq} c -∗ |NC={∅,E}=>
                                 ∀ s, s ↦* c -∗ Φ #s)) -∗
    WP FileRead #f @ E {{ Φ }}.
  Proof.
    iIntros "Hau".
    wp_call.
    wp_bind (ExternalOp _ _).
    iApply wp_ncatomic.
    { solve_atomic2. }
    iMod "Hau" as "[Hf Hau]".
    rewrite to_val_unseal /=.
    iModIntro.
    iApply (wp_FileReadOp with "Hf").
    iNext. iIntros "* [Hf Hs]".
    iMod ("Hau" with "Hf") as "HΦ".
    iModIntro.
    wp_pures.
    replace (LitV err) with (#err); last by rewrite to_val_unseal.
    destruct err.
    {
      wp_pures.
      wp_call.
      iClear "HΦ Hs".
      replace (LitV LitUnit) with (#()); last by rewrite to_val_unseal.
      iLöb as "IH".
      wp_pures.
      wp_apply "IH".
    }
    wp_pures.
    rewrite slice.val_unseal /slice.val_def to_val_unseal /=.
    iDestruct "Hs" as "[% Hl]".
    iDestruct (pointsto_vals_to_own_slice with "Hl") as "H".
    { word. }
    { instantiate (1:=len). word. }
    iApply ("HΦ" $! (slice.mk _ _ _)).
    iExactEq "H".
    repeat f_equal.
    word.
  Qed.

  Lemma wp_FileWrite f s dq old data E Φ :
    ⊢ s ↦*{dq} data -∗
    (|NC={E, ∅}=> f f↦ old ∗ (f f↦ data -∗ |NC={∅,E}=> s ↦*{dq} data -∗ Φ #()) ∧
                            (f f↦ old -∗ |NC={∅,E}=> True)
    ) -∗
    WP FileWrite #f (slice.val s) @ E {{ Φ }}.
  Proof.
    iIntros "Hs Hau".
    wp_call.
    wp_bind (ExternalOp _ _).
    rewrite to_val_unseal /=.
    iApply wp_ncatomic.
    { solve_atomic2. }
    iMod "Hau" as "[Hf Hau]".
    iModIntro.
    iDestruct (own_slice_len with "Hs") as %Hlen.
    iDestruct (own_slice_wf with "Hs") as %Hcap.
    iApply (wp_FileWriteOp with "[$Hf Hs]").
    { done. }
    { by iApply own_slice_to_pointsto_vals. }
    iNext. iIntros "* [Hf Hl]".
    replace (LitV err) with #err; last by rewrite to_val_unseal //.
    destruct err.
    - iMod ("Hau" with "[$]") as "HΦ".
      iModIntro. wp_pures.
      wp_pures.
      wp_call. iClear "HΦ Hl".
      replace (LitV LitUnit) with (#()); last by rewrite to_val_unseal.
      iLöb as "IH". wp_pures. wp_apply "IH".
    - iLeft in "Hau". iMod ("Hau" with "[$]") as "Hau".
      iModIntro. wp_pures. iApply "Hau".
      iDestruct (pointsto_vals_to_own_slice with "Hl") as "H".
      { word. }
      { instantiate (1:= s.(slice.cap_f)). word. }
      destruct s. iExactEq "H".
      simpl in *. repeat f_equal. word.
  Qed.

  Lemma wp_FileAppend f s dq old data E Φ :
    ⊢ s ↦*{dq} data -∗
    (|NC={E, ∅}=> f f↦ old ∗ (f f↦ (old ++ data) -∗ |NC={∅,E}=> s ↦*{dq} data -∗ Φ #()) ∧
                            (f f↦ old -∗ |NC={∅,E}=> True)
    ) -∗
    WP FileAppend #f (slice.val s) @ E {{ Φ }}.
  Proof.
    iIntros "Hs Hau".
    wp_call.
    wp_bind (ExternalOp _ _).
    iApply wp_ncatomic.
    { solve_atomic2. }
    iMod "Hau" as "[Hf Hau]".
    iModIntro.
    iDestruct (own_slice_len with "Hs") as %Hlen.
    iDestruct (own_slice_wf with "Hs") as %Hcap.
    rewrite to_val_unseal /=.
    iApply (wp_FileAppendOp with "[$Hf Hs]").
    { done. }
    { by iApply own_slice_to_pointsto_vals. }
    iNext. iIntros "* [Hf Hl]".
    replace (LitV err) with #err; last by rewrite to_val_unseal //.
    destruct err.
    - iMod ("Hau" with "[$]") as "HΦ".
      iModIntro. wp_pures.
      wp_pures.
      wp_call. iClear "HΦ Hl".
      replace (LitV LitUnit) with (#()); last by rewrite to_val_unseal.
      iLöb as "IH". wp_pures. wp_apply "IH".
    - iLeft in "Hau". iMod ("Hau" with "[$]") as "Hau".
      iModIntro. wp_pures. iApply "Hau".
      iDestruct (pointsto_vals_to_own_slice with "Hl") as "H".
      { word. }
      { instantiate (1:= s.(slice.cap_f)). word. }
      destruct s. iExactEq "H".
      simpl in *. repeat f_equal. word.
  Qed.

  Lemma wp_GetTSC :
  ⊢ <<< ∀∀ prev_time, tsc_lb prev_time >>>
      GetTSC #() @ ∅
    <<< ∃∃ (new_time: u64), ⌜prev_time ≤ uint.nat new_time⌝ ∗ tsc_lb (uint.nat new_time) >>>
    {{{ RET #new_time; True }}}.
  Proof.
    iIntros "!>" (Φ) "HAU". wp_call.
    rewrite difference_empty_L.
    iMod "HAU" as (prev_time) "[Hlb HΦ]".
    { solve_atomic2. }
    rewrite to_val_unseal /=.
    iApply (wp_GetTscOp with "Hlb").
    iNext. iIntros (new_time) "[%Hprev Hlb]".
    iMod ("HΦ" with "[Hlb]") as "HΦ".
    { eauto with iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma wp_GetTimeRange :
    ⊢ ∀ (Φ:goose_lang.val → iProp Σ),
    (∀ (l h t:u64), ⌜uint.nat t <= uint.nat h⌝ -∗ ⌜uint.nat l <= uint.nat t⌝ -∗
                    own_time t -∗ |NC={⊤}=> (own_time t ∗ Φ (#l, #h)%V)) -∗
  WP GetTimeRange #() {{ Φ }}.
  Proof.
    iIntros (?) "HΦ".
    wp_call. rewrite to_val_unseal /=. iApply (wp_GetTimeRangeOp with "HΦ").
  Qed.

  Lemma tsc_lb_0 :
    ⊢ |==> tsc_lb 0.
  Proof. iApply mono_nat_lb_own_0. Qed.

  Lemma tsc_lb_weaken t1 t2 :
    (t1 ≤ t2)%nat →
    tsc_lb t2 -∗ tsc_lb t1.
  Proof. intros. apply mono_nat_lb_own_le. done. Qed.
End grove.
