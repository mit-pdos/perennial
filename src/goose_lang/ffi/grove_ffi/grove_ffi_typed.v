(** Iris reasoning principles for Grove FFI *)
From stdpp Require Import gmap vector fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import gen_heap_names.
From iris.proofmode Require Import tactics.
From Perennial.base_logic Require Import ghost_map mono_nat.
From Perennial.program_logic Require Import ectx_lifting atomic.

From Perennial.Helpers Require Import CountableTactics Transitions Integers.
From Perennial.goose_lang Require Import lang lifting proofmode prelude
     slice.impl slice typed_slice typed_mem control.
From Perennial.goose_lang Require Import wpc_proofmode crash_modality.
From Perennial.goose_lang.ffi.grove_ffi Require Export grove_ffi typed_impl.
Import typed_impl.grove_ffi.

Set Default Proof Using "Type".

(** * Specs for user-facing operations *)
Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  (* FIXME: figure out which of these clients need to set *)
  Existing Instances grove_op grove_model grove_ty grove_semantics grove_interp goose_groveGS goose_groveNodeGS.
  Local Coercion Var' (s:string) : expr := Var s.

  Context `{!heapGS Σ}.

  Lemma wp_Listen c_l s E :
    {{{ True }}}
      Listen #(LitInt c_l) @ s; E
    {{{ RET listen_socket c_l; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_apply wp_ListenOp. by iApply "HΦ".
  Qed.

  Lemma wp_Connect c_r s E :
    {{{ True }}}
      Connect #(LitInt c_r) @ s; E
    {{{ (err : bool) (c_l : chan),
        RET struct.mk_f ConnectRet [
              "Err" ::= #err;
              "Connection" ::= if err then bad_socket else connection_socket c_l c_r
            ];
      if err then True else c_l c↦ ∅
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_apply wp_ConnectOp.
    iIntros (err recv) "Hr". wp_pures.
    by iApply ("HΦ" $! err). (* Wow, Coq is doing magic here *)
  Qed.

  Lemma wp_Accept c_l s E :
    {{{ True }}}
      Accept (listen_socket c_l)  @ s; E
    {{{ (c_r : chan), RET connection_socket c_l c_r; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
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

  (* FIXME move the next 2 lemmas some place more general *)

  Lemma own_slice_small_byte_pointsto_vals (s : Slice.t) (data : list u8) (q : dfrac) :
    own_slice_small s byteT q data -∗ pointsto_vals (Slice.ptr s) q (data_vals data).
  Proof.
    rewrite /own_slice_small /slice.own_slice_small.
    iIntros "[Hs _]". rewrite /array.array /pointsto_vals.
    change (list.untype data) with (data_vals data).
    iApply (big_sepL_impl with "Hs"). iIntros "!#" (i v Hv) "Hl".
    move: Hv. rewrite /data_vals list_lookup_fmap.
    intros (b & _ & ->)%fmap_Some_1.
    rewrite byte_pointsto_untype byte_offset_untype //.
  Qed.

  Lemma pointsto_vals_own_slice_small_byte (s : Slice.t) (data : list u8) (q : dfrac) :
    uint.Z s.(Slice.sz) ≤ uint.Z s.(Slice.cap) →
    length data = uint.nat (Slice.sz s) →
    pointsto_vals (Slice.ptr s) q (data_vals data) -∗
    own_slice_small s byteT q data.
  Proof.
    iIntros (? Hlen) "Hl". rewrite /own_slice_small /slice.own_slice_small. iSplit; last first.
    { iPureIntro. rewrite /list.untype fmap_length. auto. }
    rewrite /array.array /pointsto_vals.
    change (list.untype data) with (data_vals data).
    iApply (big_sepL_impl with "Hl"). iIntros "!#" (i v Hv) "Hl".
    move: Hv. rewrite /data_vals list_lookup_fmap.
    intros (b & _ & ->)%fmap_Some_1.
    rewrite byte_pointsto_untype byte_offset_untype //.
  Qed.

  Lemma wp_Send c_l c_r (s : Slice.t) (data : list u8) (q : dfrac) :
    ⊢ {{{ own_slice_small s byteT q data }}}
      <<< ∀∀ ms, c_r c↦ ms >>>
        Send (connection_socket c_l c_r) (slice_val s) @ ∅
      <<< ∃∃ (msg_sent : bool),
        c_r c↦ (if msg_sent then ms ∪ {[Message c_l data]} else ms)
      >>>
      {{{ (err : bool), RET #err; ⌜if err then True else msg_sent⌝ ∗
        own_slice_small s byteT q data }}}.
  Proof.
    iIntros "!#" (Φ) "Hs HΦ". wp_lam. wp_let.
    wp_apply wp_slice_ptr.
    wp_apply wp_slice_len.
    wp_pures.
    iDestruct (own_slice_small_sz with "Hs") as "%Hlen".
    iDestruct (own_slice_small_wf with "Hs") as "%Hwf".
    rewrite difference_empty_L.
    iMod "HΦ" as (ms) "[Hc HΦ]".
    { solve_atomic2. }
    wp_apply (wp_SendOp with "[$Hc Hs]"); [done..| |].
    { iApply own_slice_small_byte_pointsto_vals. done. }
    iIntros (err_early err_late) "[Hc Hl]".
    iApply ("HΦ" $! (negb err_early) with "[Hc]").
    { by destruct err_early. }
    iSplit.
    - iPureIntro. by destruct err_early, err_late.
    - iApply pointsto_vals_own_slice_small_byte; done.
  Qed.

  Lemma wp_Receive c_l c_r :
    ⊢ <<< ∀∀ ms, c_l c↦ ms >>>
        Receive (connection_socket c_l c_r) @ ∅
      <<< ∃∃ (err : bool) (data : list u8),
        c_l c↦ ms ∗ if err then True else ⌜Message c_r data ∈ ms⌝
      >>>
      {{{ (s : Slice.t),
        RET struct.mk_f ReceiveRet [
              "Err" ::= #err;
              "Data" ::= slice_val s
            ];
          own_slice s byteT (DfracOwn 1) data
      }}}.
  Proof.
    iIntros "!#" (Φ) "HΦ". wp_call. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iMod "HΦ" as (ms) "[Hc HΦ]".
    { solve_atomic2. }
    wp_apply (wp_RecvOp with "Hc").
    iIntros (err l len data) "(%Hm & Hc & Hl)".
    iMod ("HΦ" $! err data with "[Hc]") as "HΦ".
    { iFrame. destruct err; first done. iPureIntro. apply Hm. }
    iModIntro. wp_pures. iModIntro.
    destruct err.
    { iApply ("HΦ" $! (Slice.mk _ _ _)). simpl. destruct Hm as (-> & -> & ->).
      iApply own_slice_zero. }
    destruct Hm as [Hin Hlen].
    iApply ("HΦ" $! (Slice.mk _ _ _)).
    rewrite /own_slice.
    iSplitL.
    - iApply pointsto_vals_own_slice_small_byte; done.
    - iExists []. simpl. iSplit; first by eauto with lia.
      iApply array.array_nil. done.
  Qed.
Lemma wpc_FileRead f dq c E :
    ⊢ {{{ f f↦{dq} c }}}
        FileRead #(str f) @ E
      {{{ (s : Slice.t), RET slice_val s; f f↦{dq} c ∗ own_slice s byteT (DfracOwn 1) c }}}
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
    iApply ("HΦ" $! (Slice.mk _ _ _)). iFrame. iModIntro.
    rewrite /own_slice.
    iSplitL.
    - iApply pointsto_vals_own_slice_small_byte; done.
    - iExists []. simpl. iSplit; first by eauto with lia.
      iApply array.array_nil. done.
  Qed.

  Lemma wpc_FileWrite f s q old data E :
    ⊢ {{{ f f↦ old ∗ own_slice_small s byteT q data }}}
        FileWrite #(str f) (slice_val s) @ E
      {{{ RET #(); f f↦ data ∗ own_slice_small s byteT q data }}}
      {{{ f f↦ old ∨ f f↦ data }}}.
  Proof.
    iIntros "!#" (Φ Φc) "[Hf Hs] HΦ".
    wpc_call. { by iLeft. } { by iLeft. }
    iCache with "HΦ Hf". { iApply "HΦ". by iLeft. }
    (* Urgh so much manual work just calling a WP lemma... *)
    wpc_pures. wpc_bind (slice.ptr _). wpc_frame. wp_apply wp_slice_ptr. iNamed 1.
    wpc_pures. wpc_bind (slice.len _). wpc_frame. wp_apply wp_slice_len. iNamed 1.
    wpc_pures.
    iDestruct (own_slice_small_sz with "Hs") as "%Hlen".
    iDestruct (own_slice_small_wf with "Hs") as "%Hwf".
    wpc_bind (ExternalOp _ _).
    iApply wpc_atomic.
    { solve_atomic2. }
    iSplit.
    { iApply "HΦ". by iLeft. }
    wp_apply (wp_FileWriteOp with "[$Hf Hs]"); [done..| |].
    { iApply own_slice_small_byte_pointsto_vals. done. }
    iIntros (err) "[Hf Hs]".
    iSplit; last first.
    { iApply "HΦ". destruct err; by eauto. }
    iModIntro. destruct err.
    { wpc_pures. wpc_frame. wp_apply wp_Exit. iIntros "?". done. }
    wpc_pures.
    { iApply "HΦ". eauto. }
    iApply "HΦ". iFrame.
    iApply pointsto_vals_own_slice_small_byte; done.
  Qed.

  Lemma wpc_FileAppend f s q old data E :
    ⊢ {{{ f f↦ old ∗ own_slice_small s byteT q data }}}
        FileAppend #(str f) (slice_val s) @ E
      {{{ RET #(); f f↦ (old ++ data) ∗ own_slice_small s byteT q data }}}
      {{{ f f↦ old ∨ f f↦ (old ++ data) }}}.
  Proof.
    iIntros "!#" (Φ Φc) "[Hf Hs] HΦ".
    wpc_call. { by iLeft. } { by iLeft. }
    iCache with "HΦ Hf". { iApply "HΦ". by iLeft. }
    (* Urgh so much manual work just calling a WP lemma... *)
    wpc_pures. wpc_bind (slice.ptr _). wpc_frame. wp_apply wp_slice_ptr. iNamed 1.
    wpc_pures. wpc_bind (slice.len _). wpc_frame. wp_apply wp_slice_len. iNamed 1.
    wpc_pures.
    iDestruct (own_slice_small_sz with "Hs") as "%Hlen".
    iDestruct (own_slice_small_wf with "Hs") as "%Hwf".
    wpc_bind (ExternalOp _ _).
    iApply wpc_atomic.
    { solve_atomic2. }
    iSplit.
    { iApply "HΦ". by iLeft. }
    wp_apply (wp_FileAppendOp with "[$Hf Hs]"); [done..| |].
    { iApply own_slice_small_byte_pointsto_vals. done. }
    iIntros (err) "[Hf Hs]".
    iSplit; last first.
    { iApply "HΦ". destruct err; eauto. }
    iModIntro. destruct err.
    { wpc_pures. wpc_frame. wp_apply wp_Exit. iIntros "?". done. }
    wpc_pures.
    { iApply "HΦ". eauto. }
    iApply "HΦ". iFrame.
    iApply pointsto_vals_own_slice_small_byte; done.
  Qed.

  Lemma wp_GetTSC :
  ⊢ <<< ∀∀ prev_time, tsc_lb prev_time >>>
      GetTSC #() @ ∅
    <<< ∃∃ (new_time: u64), ⌜prev_time ≤ uint.nat new_time⌝ ∗ tsc_lb (uint.nat new_time) >>>
    {{{ RET #new_time; True }}}.
  Proof.
    iIntros "!>" (Φ) "HAU". wp_lam.
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
    wp_call. wp_apply (wp_GetTimeRangeOp with "HΦ").
  Qed.

  Lemma tsc_lb_0 :
    ⊢ |==> tsc_lb 0.
  Proof. iApply mono_nat_lb_own_0. Qed.

  Lemma tsc_lb_weaken t1 t2 :
    (t1 ≤ t2)%nat →
    tsc_lb t2 -∗ tsc_lb t1.
  Proof. intros. apply mono_nat_lb_own_le. done. Qed.
End grove.
