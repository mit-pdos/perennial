(** Iris specs for Grove FFI *)
From iris.base_logic.lib Require Import mono_nat.
From Perennial.program_logic Require Export atomic_fupd.
From New.proof Require Export proof_prelude.
From Perennial.goose_lang.ffi.grove_ffi Require Export grove_ffi.
From New.code.github_com.mit_pdos.gokv Require Import grove_ffi.
From Perennial.goose_lang Require Import control.

Set Default Proof Using "Type".

(** * Specs for user-facing operations *)
Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  (* FIXME: figure out which of these clients need to set *)
  Set Printing Projections.
  Existing Instances grove_op grove_model grove_semantics grove_interp goose_groveGS goose_groveNodeGS.
  Local Coercion Var' (s:string) : expr := Var s.

  Context `{!heapGS Σ}.

  Lemma wp_Listen c_l s E :
    {{{ True }}}
      Listen #(LitInt c_l) @ s; E
    {{{ RET listen_socket c_l; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_rec.
    wp_apply wp_ListenOp. by iApply "HΦ".
  Qed.

  Lemma wp_Connect c_r s E :
    {{{ True }}}
      Connect #(LitInt c_r) @ s; E
    {{{ (err : bool) (c_l : chan),
        RET struct.val ConnectRet [
              "Err" ::= #err;
              "Connection" ::= if err then bad_socket else connection_socket c_l c_r
            ];
      if err then True else c_l c↦ ∅
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_rec.
    wp_apply wp_ConnectOp.
    iIntros (err recv) "Hr". wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma wp_Accept c_l s E :
    {{{ True }}}
      Accept (listen_socket c_l)  @ s; E
    {{{ (c_r : chan), RET connection_socket c_l c_r; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_rec.
    wp_apply wp_AcceptOp. by iApply "HΦ".
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
           | [ H: relation.denote _ ?s1 ?s2 ?v |- _ ] => inversion_clear H
           | _ => progress monad_inv
           | _ => case_match
           end; eauto.

  Local Lemma own_slice_to_pointsto_vals s q vs :
    own_slice s byteT q vs -∗ pointsto_vals s.(slice.ptr_f) q vs.
  Proof.
    rewrite own_slice_unseal /own_slice_def /pointsto_vals.
    iIntros "(Hs & _ & _)". simpl.
    iApply (big_sepL_impl with "Hs").
    iModIntro. iIntros "* % Hp". rewrite go_type_size_unseal /= left_id.
    rewrite typed_pointsto_unseal /typed_pointsto_def.
    iDestruct select (_) as "[Hp %Hty]". inversion Hty; subst.
    simpl. rewrite right_id. rewrite loc_add_0. iFrame.
  Qed.

  Local Lemma pointsto_vals_to_own_slice (p : loc) (cap : w64) (q : dfrac) (d : list w8) :
    (length d) = uint.nat (length d) →
    (length d) ≤ uint.Z cap →
    pointsto_vals p q (data_vals d) -∗
    own_slice (slice.mk p (length d) cap) byteT q (data_vals d).
  Proof.
    intros Hoverflow Hcap.
    rewrite own_slice_unseal /own_slice_def /pointsto_vals.
    iIntros "Hl". simpl.
    iSplitL.
    2:{ iPureIntro. rewrite /data_vals fmap_length /=. word. }
    iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros "* % Hp". rewrite go_type_size_unseal /= left_id.
    rewrite typed_pointsto_unseal /typed_pointsto_def.
    rewrite /data_vals list_lookup_fmap /= in H.
    destruct (d !! k).
    2:{ exfalso. done. }
    simpl in *. inversion H; subst.
    iSplitL.
    2:{ iPureIntro. econstructor. }
    simpl. rewrite right_id. rewrite loc_add_0. iFrame.
  Qed.

  Lemma wp_Send c_l c_r (s : slice.t) (data : list u8) (q : dfrac) :
    ⊢ {{{ own_slice s byteT q (data_vals data) }}}
      <<< ∀∀ ms, c_r c↦ ms >>>
        Send (connection_socket c_l c_r) (slice.val s) @ ∅
      <<< ∃∃ (msg_sent : bool),
        c_r c↦ (if msg_sent then ms ∪ {[Message c_l data]} else ms)
      >>>
      {{{ (err : bool), RET #err; ⌜if err then True else msg_sent⌝ ∗
                                own_slice s byteT q (data_vals data) }}}.
  Proof.
    iIntros "!#" (Φ) "Hs HΦ". wp_rec. 
    destruct s. wp_pures.
    iDestruct (own_slice_sz with "Hs") as "%Hlen".
    iDestruct (own_slice_wf with "Hs") as "%Hwf".
    rewrite difference_empty_L.
    iMod "HΦ" as (ms) "[Hc HΦ]".
    { solve_atomic2. }
    cbn in *.
    rewrite /data_vals fmap_length in Hlen.
    wp_apply (wp_SendOp with "[$Hc Hs]").
    { done. }
    { iApply (own_slice_to_pointsto_vals with "[$]"). }
    iIntros (err_early err_late) "[Hc Hl]".
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
      {{{ (s : slice.t),
        RET struct.val ReceiveRet [
              "Err" ::= #err;
              "Data" ::= slice.val s
            ];
          own_slice s byteT (DfracOwn 1) (data_vals data)
      }}}.
  Proof.
    iIntros "!#" (Φ) "HΦ". wp_rec. wp_pures. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iMod "HΦ" as (ms) "[Hc HΦ]".
    { solve_atomic2. }
    wp_apply (wp_RecvOp with "Hc").
    iIntros (err l len data) "(%Hm & Hc & Hl)".
    iMod ("HΦ" $! err data with "[Hc]") as "HΦ".
    { iFrame. destruct err; first done. iPureIntro. apply Hm. }
    iModIntro. wp_pures.
    destruct err.
    { rewrite slice_val_fold. iApply ("HΦ" $! (slice.mk _ _ _)). simpl. destruct Hm as (-> & -> & ->).
      simpl.
      iApply own_slice_empty. done. }
    destruct Hm as [Hin Hlen].
    rewrite slice_val_fold.
    iApply ("HΦ" $! (slice.mk _ _ _)).
    iModIntro.
    iDestruct (pointsto_vals_to_own_slice with "Hl") as "H".
    { word. }
    2:{ iExactEq "H". repeat f_equal. word. }
    word.
  Qed.

  Lemma wpc_FileRead f dq c E :
    ⊢ {{{ f f↦{dq} c }}}
        FileRead #(str f) @ E
      {{{ (s : slice.t), RET slice.val s; f f↦{dq} c ∗ own_slice s byteT (DfracOwn 1) (data_vals c) }}}
      {{{ f f↦{dq} c }}}.
  Proof.
    iIntros "!#" (Φ Φc) "Hf HΦ". wpc_call; first done.
    iCache with "HΦ Hf". { iApply "HΦ". done. }
    wpc_bind (ExternalOp _ _).
    iApply wpc_atomic.
    { solve_atomic2. }
    iSplit.
    { iApply "HΦ". done. }
    wp_apply (wp_FileReadOp with "Hf").
    iIntros (err l len) "(Hf & Hl)".
    iSplit; last first.
    { iApply "HΦ". done. }
    iModIntro.
    destruct err.
    { wpc_pures.
      wpc_frame. wp_apply wp_Exit. iIntros "?". done. }
    iDestruct "Hl" as "[%Hl Hl]".
    wpc_pures.
    iDestruct "HΦ" as "[_ HΦ]".
    rewrite slice_val_fold.
    iApply ("HΦ" $! (slice.mk _ _ _)). iFrame. iModIntro.
    iDestruct (pointsto_vals_to_own_slice with "Hl") as "H".
    { word. }
    2:{ iExactEq "H". repeat f_equal. word. }
    word.
  Qed.

  Lemma wpc_FileWrite f s q old data E :
    ⊢ {{{ f f↦ old ∗ own_slice s byteT q (data_vals data) }}}
        FileWrite #(str f) (slice.val s) @ E
      {{{ RET #(); f f↦ data ∗ own_slice s byteT q (data_vals data) }}}
      {{{ f f↦ old ∨ f f↦ data }}}.
  Proof.
    iIntros "!#" (Φ Φc) "[Hf Hs] HΦ".
    wpc_call. { by iLeft. } { by iLeft. }
    iCache with "HΦ Hf". { iApply "HΦ". by iLeft. }
    (* Urgh so much manual work just calling a WP lemma... *)
    rewrite slice.val_unseal.
    wpc_pures.
    iDestruct (own_slice_sz with "Hs") as "%Hlen".
    iDestruct (own_slice_wf with "Hs") as "%Hwf".
    wpc_bind (ExternalOp _ _).
    iApply wpc_atomic.
    { solve_atomic2. }
    iSplit.
    { iApply "HΦ". by iLeft. }
    rewrite /data_vals fmap_length in Hlen.
    wp_apply (wp_FileWriteOp with "[$Hf Hs]"); [done..| |].
    { iApply own_slice_to_pointsto_vals. done. }
    iIntros (err) "[Hf Hs]".
    iSplit; last first.
    { iApply "HΦ". destruct err; by eauto. }
    iModIntro. destruct err.
    { wpc_pures. wpc_frame. wp_apply wp_Exit. iIntros "?". done. }
    wpc_pures.
    { iApply "HΦ". eauto. }
    iApply "HΦ". iFrame.
    iModIntro.
    destruct s. simpl in *.
    iDestruct (pointsto_vals_to_own_slice with "Hs") as "H".
    { word. }
    2:{ iExactEq "H". repeat f_equal. word. }
    word.
  Qed.

  Lemma wpc_FileAppend f s q old data E :
    ⊢ {{{ f f↦ old ∗ own_slice s byteT q (data_vals data) }}}
        FileAppend #(str f) (slice.val s) @ E
      {{{ RET #(); f f↦ (old ++ data) ∗ own_slice s byteT q (data_vals data) }}}
      {{{ f f↦ old ∨ f f↦ (old ++ data) }}}.
  Proof.
    iIntros "!#" (Φ Φc) "[Hf Hs] HΦ".
    wpc_call. { by iLeft. } { by iLeft. }
    iCache with "HΦ Hf". { iApply "HΦ". by iLeft. }
    (* Urgh so much manual work just calling a WP lemma... *)
    rewrite slice.val_unseal.
    wpc_pures.
    iDestruct (own_slice_sz with "Hs") as "%Hlen".
    iDestruct (own_slice_wf with "Hs") as "%Hwf".
    wpc_bind (ExternalOp _ _).
    iApply wpc_atomic.
    { solve_atomic2. }
    iSplit.
    { iApply "HΦ". by iLeft. }
    rewrite /data_vals fmap_length in Hlen.
    wp_apply (wp_FileAppendOp with "[$Hf Hs]"); [done..| |].
    { iApply own_slice_to_pointsto_vals. done. }
    iIntros (err) "[Hf Hs]".
    iSplit; last first.
    { iApply "HΦ". destruct err; eauto. }
    iModIntro. destruct err.
    { wpc_pures. wpc_frame. wp_apply wp_Exit. iIntros "?". done. }
    wpc_pures.
    { iApply "HΦ". eauto. }
    iApply "HΦ". iFrame. iModIntro.
    destruct s. simpl in *.
    iDestruct (pointsto_vals_to_own_slice with "Hs") as "H".
    { word. }
    2:{ iExactEq "H". repeat f_equal. word. }
    word.
  Qed.


  Lemma wp_GetTSC :
  ⊢ <<< ∀∀ prev_time, tsc_lb prev_time >>>
      GetTSC #() @ ∅
    <<< ∃∃ (new_time: u64), ⌜prev_time ≤ uint.nat new_time⌝ ∗ tsc_lb (uint.nat new_time) >>>
    {{{ RET #new_time; True }}}.
  Proof.
    iIntros "!>" (Φ) "HAU". wp_rec.
    rewrite difference_empty_L.
    iMod "HAU" as (prev_time) "[Hlb HΦ]".
    { solve_atomic2. }
    wp_apply (wp_GetTscOp with "Hlb").
    iIntros (new_time) "[%Hprev Hlb]".
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
    wp_rec. wp_pures. wp_apply (wp_GetTimeRangeOp with "HΦ").
  Qed.

  Lemma tsc_lb_0 :
    ⊢ |==> tsc_lb 0.
  Proof. iApply mono_nat_lb_own_0. Qed.

  Lemma tsc_lb_weaken t1 t2 :
    (t1 ≤ t2)%nat →
    tsc_lb t2 -∗ tsc_lb t1.
  Proof. intros. apply mono_nat_lb_own_le. done. Qed.
End grove.
