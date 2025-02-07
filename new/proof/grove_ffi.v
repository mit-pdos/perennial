(** Iris specs for Grove FFI *)
From iris.bi.lib Require Import fixpoint_mono.
From iris.base_logic.lib Require Import mono_nat saved_prop.
From Perennial.program_logic Require Export atomic_fupd.
From New.proof Require Export proof_prelude own_crash.
From Perennial.goose_lang.ffi.grove_ffi Require Export grove_ffi.
From New.code.github_com.mit_pdos.gokv Require Import grove_ffi.
Require Import New.generatedproof.github_com.mit_pdos.gokv.grove_ffi.

Set Default Proof Using "Type".

Module ConnectRet.
Record t :=
  mk {
      Err : bool;
      Connection : loc;
    }.
End ConnectRet.

Global Instance into_val_ConnectRet `{ffi_syntax} : IntoVal ConnectRet.t :=
  {|
    to_val_def :=
      λ v, struct.val_aux ConnectRet [
               "Err" ::= #v.(ConnectRet.Err);
               "Connection" ::= #v.(ConnectRet.Connection)
             ]%V
  |}.

Instance wp_struct_make_ConnectRet `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  err conn :
  PureWp True
  (struct.make ConnectRet (alist_val [("Err" ::= #err)%V; ("Connection" ::= #conn)%V]))
  #(ConnectRet.mk err conn).
Proof.
  rewrite [in #(_ : ConnectRet.t)]to_val_unseal.
  by apply wp_struct_make.
Qed.

Module ReceiveRet.
Record t :=
  mk {
      Err : bool;
      Data : slice.t;
    }.
End ReceiveRet.

Global Instance into_val_ReceiveRet `{ffi_syntax} : IntoVal ReceiveRet.t :=
  {|
    to_val_def :=
      λ v, struct.val_aux ReceiveRet [
               "Err" ::= #v.(ReceiveRet.Err);
               "Data" ::= #v.(ReceiveRet.Data)
             ]%V
  |}.

Instance wp_struct_make_ReceiveRet `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  err data :
  PureWp True
  (struct.make ReceiveRet (alist_val [("Err" ::= #err)%V; ("Data" ::= #data)%V]))
  #(ReceiveRet.mk err data).
Proof.
  rewrite [in #(_ : ReceiveRet.t)]to_val_unseal.
  by apply wp_struct_make.
Qed.

(** * Specs for user-facing operations *)
Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  (* FIXME: figure out which of these clients need to set *)
  Set Printing Projections.
  Existing Instances grove_op grove_model grove_semantics grove_interp goose_groveGS goose_groveNodeGS.

  Context `{!heapGS Σ}.
  Context `{!goGlobalsGS Σ}.

  Definition is_initialized :=
    grove_ffi.is_defined.

  Definition is_Listener (l : loc) (host : u64) : iProp Σ :=
    is_initialized ∗
    heap_pointsto l (DfracDiscarded) (listen_socket host).

  Global Instance is_Listener_persistent l host : Persistent (is_Listener l host) := _.

  Lemma wp_Listen host :
    {{{ is_initialized }}}
      func_call #grove_ffi.pkg_name' #"Listen" #host
    {{{ l, RET #l; is_Listener l host }}}.
  Proof.
    iIntros (Φ) "#Hdef HΦ". wp_func_call. wp_call.
    rewrite to_val_unseal. simpl. wp_bind (ExternalOp _ _).
    iApply wp_ListenOp; first done.
    iIntros "!# _".
    iApply wp_fupd.
    iApply wp_alloc_untyped; try done.
    iIntros "!> * Hl". iMod (heap_pointsto_persist with "[$]").
    iApply "HΦ". iModIntro.
    iFrame "∗#".
  Qed.

  Definition is_Connection (c : loc) (local remote : u64) : iProp Σ :=
    is_initialized ∗
    heap_pointsto c (DfracDiscarded) (connection_socket local remote).

  Global Instance is_Connection_persistent c local remote : Persistent (is_Connection c local remote) := _.

  Lemma wp_Connect remote :
    {{{ is_initialized }}}
      func_call #grove_ffi.pkg_name' #"Connect" #remote
    {{{ (err : bool) (local : chan) l,
        RET #(ConnectRet.mk err l);
        if err then True else is_Connection l local remote
    }}}.
  Proof.
    iIntros (Φ) "#Hdef HΦ".
    wp_func_call. wp_call.
    wp_bind (ExternalOp _ _)%E. rewrite [in #remote]to_val_unseal. iApply (wp_ConnectOp with "[//]").
    iNext. iIntros (err recv) "Hr". wp_pures.
    replace (LitV err) with #err.
    2:{ rewrite to_val_unseal //. }
    wp_bind (ref _)%E.
    destruct err.
    - iApply wp_alloc_untyped; try done.
      iIntros "!# * ?".
      replace (LitV l) with #l.
      2:{ rewrite to_val_unseal //. }
      wp_pures. by iApply "HΦ".
      Unshelve. done.
    - iApply wp_alloc_untyped; try done.
      iIntros "!# * ?".
      replace (LitV l) with #l.
      2:{ rewrite to_val_unseal //. }
      iMod (heap_pointsto_persist with "[$]").
      wp_pures. iApply "HΦ". iFrame "∗#".
  Qed.

  Lemma wp_Accept l local :
    {{{ is_Listener l local }}}
      func_call #grove_ffi.pkg_name' #"Accept" #l
    {{{ c remote, RET #c; is_Connection c local remote }}}.
  Proof.
    iIntros (Φ) "[#? ?] HΦ". wp_func_call. wp_call.
    wp_bind (! _)%E.
    rewrite [in #l]to_val_unseal.
    iApply (wp_load with "[$]").
    iIntros "!> ?".
    wp_bind (ExternalOp _ _).
    iApply wp_AcceptOp; try done.
    iNext. iIntros.
    iApply wp_fupd.
    iApply wp_alloc_untyped; try done.
    iNext. iIntros "* ?".
    iMod (heap_pointsto_persist with "[$]").
    replace (LitV l0) with #l0; last by rewrite to_val_unseal.
    iApply "HΦ". iModIntro. iFrame "∗#".
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
    2:{ word. }
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

  Lemma wp_Send c local remote (s : slice.t) (data : list u8) (dq : dfrac) :
    ⊢ {{{ s ↦*{dq} data ∗ is_Connection c local remote }}}
      <<< ∀∀ ms, remote c↦ ms >>>
        func_call #grove_ffi.pkg_name' #"Send" #c #s @ ∅
      <<< ∃∃ (msg_sent : bool),
        remote c↦ (if msg_sent then ms ∪ {[Message local data]} else ms)
      >>>
      {{{ (err : bool), RET #err; ⌜if err then True else msg_sent⌝ ∗
                                s ↦*{dq} data }}}.
  Proof.
    iIntros "!#" (Φ) "[Hs #[? ?]] HΦ".
    wp_func_call.
    wp_call.
    wp_bind (! _)%E.
    rewrite [in #c]to_val_unseal.
    iApply (wp_load with "[$]").
    iIntros "!> * #?".
    wp_pures.
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

  Lemma wp_Receive c local remote :
    ⊢ {{{ is_Connection c local remote }}}
      <<< ∀∀ ms, local c↦ ms >>>
        func_call #grove_ffi.pkg_name' #"Receive" #c @ ∅
      <<< ∃∃ (err : bool) (data : list u8),
        local c↦ ms ∗ if err then True else ⌜Message remote data ∈ ms⌝
      >>>
      {{{ s, RET #(ReceiveRet.mk err s); s ↦* data }}}.
  Proof.
    iIntros "!#" (Φ) "#[? ?] HΦ". wp_func_call. wp_call.
    wp_bind (! _)%E.
    rewrite [in #c]to_val_unseal.
    iApply (wp_load with "[$]").
    iIntros "!> * ?".
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iMod "HΦ" as (ms) "[Hc HΦ]".
    { solve_atomic2. }
    iApply (wp_RecvOp with "Hc").
    iIntros "!#" (err l len data) "(%Hm & Hc & Hl)".
    iMod ("HΦ" $! err data with "[Hc]") as "HΦ".
    { iFrame. destruct err; first done. iPureIntro. apply Hm. }
    iModIntro. wp_pures.

    replace (LitV err) with #err; last by rewrite to_val_unseal.
    replace (InjLV _) with #(slice.mk l len len).
    2:{ repeat rewrite to_val_unseal //=. }
    destruct err.
    {
      destruct Hm as (?&?&?); subst.
      wp_pures.
      iApply "HΦ".
      iApply own_slice_empty. done.
    }
    destruct Hm as [Hin Hlen].
    wp_pures.
    iApply ("HΦ" $! (slice.mk _ _ _)).
    iDestruct (pointsto_vals_to_own_slice with "Hl") as "H".
    { word. }
    2:{ iExactEq "H". repeat f_equal. word. }
    word.
  Qed.

  (* FIXME: this is actually logically atomic because the model doesn't capture
     the fact that reads and writes are non-atomic w.r.t. concurrency.
     This avoids existentially quantifying c inside the fupd to require the
     caller to "know" the file contents before callin Read.
   *)
  Lemma wp_FileRead f dq c Φ :
    ⊢ grove_ffi.is_defined -∗
      (|NC={⊤, ∅}=> f f↦{dq} c ∗ (f f↦{dq} c -∗ |NC={∅, ⊤}=>
                                 ∀ s, s ↦* c -∗ Φ #s)) -∗
    WP func_call #grove_ffi.pkg_name' #"FileRead" #f {{ Φ }}.
  Proof.
    iIntros "#Hdef Hau".
    wp_func_call. wp_call.
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
    rewrite to_val_unseal /=.
    iDestruct "Hs" as "[% Hl]".
    iDestruct (pointsto_vals_to_own_slice with "Hl") as "H".
    { word. }
    { instantiate (1:=len). word. }
    iApply ("HΦ" $! (slice.mk _ _ _)).
    iExactEq "H".
    repeat f_equal.
    word.
  Qed.

  Lemma wp_FileWrite f s dq old data Φ :
    ⊢ (grove_ffi.is_defined ∗
       s ↦*{dq} data) -∗
    (|NC={⊤, ∅}=> f f↦ old ∗ (f f↦ data -∗ |NC={∅,⊤}=> s ↦*{dq} data -∗ Φ #()) ∧
                            (f f↦ old -∗ |NC={∅,⊤}=> True)
    ) -∗
    WP func_call #grove_ffi.pkg_name' #"FileWrite" #f #s {{ Φ }}.
  Proof.
    iIntros "[#Hdef Hs] Hau".
    wp_func_call. wp_call.
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

  Lemma wp_FileAppend f s dq old data Φ :
    ⊢ (grove_ffi.is_defined ∗ s ↦*{dq} data) -∗
    (|NC={⊤, ∅}=> f f↦ old ∗ (f f↦ (old ++ data) -∗ |NC={∅, ⊤}=> s ↦*{dq} data -∗ Φ #()) ∧
                            (f f↦ old -∗ |NC={∅, ⊤}=> True)
    ) -∗
    WP func_call #grove_ffi.pkg_name' #"FileAppend" #f #s {{ Φ }}.
  Proof.
    iIntros "[#Hdef Hs] Hau".
    wp_func_call. wp_call.
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
  ⊢ {{{ grove_ffi.is_defined }}}
    <<< ∀∀ prev_time, tsc_lb prev_time >>>
      func_call #grove_ffi.pkg_name' #"GetTSC" #() @ ∅
    <<< ∃∃ (new_time: u64), ⌜prev_time ≤ uint.nat new_time⌝ ∗ tsc_lb (uint.nat new_time) >>>
    {{{ RET #new_time; True }}}.
  Proof.
    iIntros "!>" (Φ) "#Hdef HAU". wp_func_call. wp_call.
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
    grove_ffi.is_defined -∗
      (∀ (l h t:u64), ⌜uint.nat t <= uint.nat h⌝ -∗ ⌜uint.nat l <= uint.nat t⌝ -∗
                      own_time t -∗ |NC={⊤}=> (own_time t ∗ Φ (#l, #h)%V)) -∗
    WP func_call #grove_ffi.pkg_name' #"GetTimeRange" #() {{ Φ }}.
  Proof.
    iIntros (?) "#Hdef HΦ". wp_func_call.
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

Typeclasses Opaque is_Listener is_Connection.
