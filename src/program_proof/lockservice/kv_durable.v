From Coq.Structures Require Import OrdersTac.
From stdpp Require Import gmap.
From iris.algebra Require Import numbers.
From Perennial.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import disk_prelude.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.goose_lang.lib Require Import crash_lock.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map rpc_durable_proof.
From Perennial.program_proof Require Import disk_prelude marshal_proof.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section kv_durable_proof.
Context `{!heapG Σ, !kvserviceG Σ, stagedG Σ}.
Context `{!filesysG Σ}.

(* TODO: move to marshal_proof *)
Definition has_map_encoding (m:gmap u64 u64) (r:Rec) :=
  ∃ l,
  (int.Z (size m) = size m) ∧
  NoDup l.*1 ∧
  (list_to_map l) = m ∧
  r = [EncUInt64 (size m)] ++ (flat_map (λ u, [EncUInt64 u.1 ; EncUInt64 u.2]) l)
.

Definition EncMap_invariant enc_v (r:Rec) sz map_sz (original_remaining:Z) (mtodo mdone:gmap u64 u64) : iProp Σ :=
  ∃ (l:list (u64 * u64)) (remaining:Z),
    ⌜ NoDup l.*1 ⌝ ∗
    ⌜(list_to_map l) = mdone⌝ ∗
    ⌜8 * 2 * (size mtodo) ≤ remaining⌝ ∗
    ⌜remaining = original_remaining - 8 * 2 * (size mdone)⌝ ∗
    ⌜mtodo ##ₘ mdone ⌝ ∗
    is_enc enc_v sz (r ++ [EncUInt64 map_sz] ++ (flat_map (λ u, [EncUInt64 u.1 ; EncUInt64 u.2]) l )) remaining
.

Definition marshalledMapSize (m:gmap u64 u64) : nat := 8 + 8 * 2 * (size m).

Lemma wp_EncMap e mref m sz r remaining :
marshalledMapSize m <= remaining →
{{{
    "Hmap" ∷ is_map (V:=u64) mref m ∗
    "Henc" ∷ is_enc e sz r remaining
}}}
  EncMap e #mref
{{{
     rmap, RET #();
     ⌜has_map_encoding m rmap⌝ ∗
     is_map (V:=u64) mref m ∗
     is_enc e sz (r ++ rmap) (remaining - marshalledMapSize m)
}}}.
Proof using Type*.
  intros Hrem.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam. wp_pures.

  wp_apply (wp_MapLen with "Hmap").
  iIntros "[%Hsize Hmap]".
  unfold marshalledMapSize in Hrem.
  wp_apply (wp_Enc__PutInt with "Henc").
  { lia. }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_MapIter_2 _ _ _ _ (EncMap_invariant e r sz (size m) (remaining - 8)) with "Hmap [Henc] [] [HΦ]").
  {
    iExists [] . iExists (remaining-8). simpl. iFrame.
    iSplit.
    { iPureIntro. apply NoDup_nil_2. }
    iSplit; first done.
    iPureIntro. split; first by lia.
    replace (size ∅) with (0%nat).
    { split; first by lia. apply map_disjoint_empty_r. }
    symmetry. by apply map_size_empty_iff.
  }
  {
    clear Φ.
    iIntros (???? Φ) "!# [Hpre %Htodo] HΦ".
    wp_pures.
    iDestruct "Hpre" as (l rem' Hnodup Hl Hrem' Hremeq Hmdisjoint) "Henc".

    assert (size mtodo ≠ 0%nat).
    { apply map_size_non_empty_iff.
      destruct (bool_decide (mtodo = ∅)) as [|] eqn:X.
      { apply bool_decide_eq_true in X. rewrite X in Htodo. done. }
      { by apply bool_decide_eq_false in X. }
    }
    wp_apply (wp_Enc__PutInt with "Henc").
    {
      lia.
    }
    iIntros "Henc".
    wp_pures.

    wp_apply (wp_Enc__PutInt with "Henc").
    {
      lia.
    }
    iIntros "Henc".
    iApply "HΦ".
    iExists (l ++ [(k, v)]), (rem' - 8 - 8).
    iSplit.
    { iPureIntro.
      rewrite fmap_app.
      rewrite NoDup_app.
      split; first done.
      split.
      { intros.
        simpl.
        rewrite not_elem_of_cons.
        split; last apply not_elem_of_nil.
        destruct (decide (x = k)) as [->|]; last done.
        exfalso.
        apply elem_of_list_fmap_2 in H1 as [ [k0 v0] [Hk Hp]].
        simpl in Hk.
        eapply (elem_of_list_to_map_1 (M:=gmap _)) in Hnodup; eauto.
        replace (list_to_map l) with (mdone) in Hnodup by eauto.
        eapply map_disjoint_spec; eauto.
        by rewrite Hk.
      }
      { apply NoDup_cons_2.
        - apply not_elem_of_nil.
        - apply NoDup_nil_2.
      }
    }
    iSplit.
    { iPureIntro.
      rewrite -Hl.
      apply list_to_map_snoc.
      (* XXX: had to put the M there because typeclass resolution was not working well *)
      rewrite (not_elem_of_list_to_map (M:=(@gmap u64 u64_eq_dec u64_countable))).
      rewrite Hl.
      destruct (mdone !! k) eqn:Hcase; last done.
      exfalso; by eapply map_disjoint_spec.
    }
    iSplit.
    { replace (size (delete k mtodo)) with (pred (size mtodo)).
      { iPureIntro. lia. }
      { symmetry. apply map_size_delete_Some. eauto. }
    }
    rewrite flat_map_app.
    simpl.
    replace ([EncUInt64 k; EncUInt64 v]) with ([EncUInt64 k] ++ [EncUInt64 v]) by eauto.
    iFrame.
    rewrite -app_assoc.
    rewrite -app_assoc.
    iFrame.
    iPureIntro.

    destruct (mdone !! k) eqn:X.
    - exfalso. eapply map_disjoint_spec; eauto.
    - split.
      + rewrite map_size_insert_None; first lia. done.
      + apply map_disjoint_insert_r_2.
        { apply lookup_delete. }
        by apply map_disjoint_delete_l.
  }
  iIntros "[Hmap Henc]".
  iDestruct "Henc" as (l rem' Hnodup Hl _ ? ?) "Henc".
  iApply ("HΦ" $! (
              [EncUInt64 (size m)] ++
              flat_map (λ u : u64 * u64, [EncUInt64 u.1; EncUInt64 u.2]) l)
         ).
  iFrame "Hmap".
  unfold marshalledMapSize.
  replace (remaining - (8 + 8 * 2 * size m)%nat) with (rem') by lia.
  iFrame.
  iPureIntro.
  exists l.
  rewrite -u64_Z_through_nat.
  eauto.
Qed.

Definition DecMap_invariant dec_v i_ptr m (r:Rec) mref s q data : iProp Σ :=
  ∃ (l:list (u64 * u64)) (mdone:gmap u64 u64),
    ⌜NoDup l.*1⌝ ∗
    ⌜(list_to_map l) ##ₘ mdone⌝ ∗
    ⌜(list_to_map l) ∪ mdone = m⌝ ∗
    i_ptr ↦[uint64T] #(size mdone) ∗
    is_map mref mdone ∗
    is_dec dec_v ((flat_map (λ u, [EncUInt64 u.1 ; EncUInt64 u.2]) l) ++ r) s q data
.

(* FIXME: prove this *)
Lemma gmap_size_union (A B:gmap u64 u64) :
  A ##ₘ B → size (A ∪ B) = ((size A) + (size B))%nat.
Proof.
Admitted.

Lemma wp_DecMap dec_v m s r rmap data q :
  {{{
      "%Hmapencoded" ∷ ⌜has_map_encoding m rmap⌝ ∗
      "Hdec" ∷ is_dec dec_v (rmap ++ r) s q data
  }}}
    DecMap dec_v
  {{{
      mref, RET #mref;
      is_map mref m ∗
      is_dec dec_v r s q data
  }}}.
Proof.
  Opaque NewMap.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  destruct Hmapencoded as [l [Hsize [Hnodup [HlistMap Hmapencoded]]]].
  rewrite Hmapencoded.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_pures.
  wp_apply wp_NewMap.
  iIntros (mref) "Hmref".
  wp_pures.
  wp_apply (wp_ref_to); first eauto.
  iIntros (i_ptr) "Hi".

  iAssert (DecMap_invariant dec_v i_ptr m r mref s q data) with "[Hi Hmref Hdec]" as "HloopInv".
  {
    iExists l, ∅.
    iFrame.
    iSplit; first done.
    iSplitL "".
    { iPureIntro. eapply (map_disjoint_empty_r (M:=gmap _)). }
    by rewrite right_id.
  }
  wp_pures.

  wp_forBreak_cond.
  clear HlistMap Hnodup Hmapencoded l.
  iDestruct "HloopInv" as (l' mdone Hnodup Hdisj Hunion) "(Hi & Hmref & Hdec)".
  wp_load.
  wp_pures.
  wp_if_destruct.
  { (* Start of loop iteration *)
    wp_pures.
    destruct l'.
    { simpl in Heqb. exfalso.
      simpl in *. rewrite left_id in Hunion.
      rewrite Hunion in Heqb. lia. }
    destruct p as [k v].
    simpl.
    wp_apply (wp_Dec__GetInt with "Hdec").
    iIntros "Hdec".
    wp_apply (wp_Dec__GetInt with "Hdec").
    iIntros "Hdec".
    wp_pures.
    wp_apply (wp_MapInsert with "Hmref"); first done.
    iIntros "Hmref".
    wp_pures.
    wp_load.
    wp_store.
    iLeft.
    iSplitL ""; first done.
    iSplitL "HΦ"; first done.
    iExists l', _.
    iFrame "Hmref".
    iSplitL "".
    { by apply NoDup_cons in Hnodup as [??]. }
    assert ((list_to_map l' (M:=gmap _ _)) !! k = None) as Hnok.
    { apply NoDup_cons in Hnodup as [HkNotInL Hnodup].
        by apply not_elem_of_list_to_map_1. }
    iSplitL "".
    { iPureIntro. simpl in Hdisj.
      rewrite map_disjoint_insert_r.
      split; first done.
      eapply map_disjoint_weaken; eauto.
      simpl.
      apply insert_subseteq.
      done.
    }
    iSplitL "".
    { iPureIntro. simpl in Hunion.
      rewrite -insert_union_r; last done.
      rewrite insert_union_l.
      done.
    }
    rewrite (map_size_insert_None); last first.
    { eapply map_disjoint_Some_l; eauto.
      simpl. apply lookup_insert. }
    replace (word.add (size mdone) 1) with (int.Z (size mdone) + 1:u64) by word.
    rewrite Z_u64; last first.
    { split; first lia.
      word_cleanup.
      rewrite Hsize in H1.
      assert (size mdone ≤ size m)%nat.
      { rewrite -Hunion. eapply subseteq_size.
        (* TODO: Prove that A ⊆ A ∪ B *)
        admit. }
      lia.
    }
    replace (Z.of_nat (S (size mdone))) with (size mdone + 1)%Z by lia.
    iFrame.
  }
  iRight. iSplitL ""; first done.
  wp_pures.
  iApply "HΦ".
  destruct l'; last first.
  {
    exfalso.
    set (mtodo:=(list_to_map (p :: l'))) in *.
    rewrite -Hunion in Heqb.
    rewrite gmap_size_union in Heqb; eauto.
    assert (size mtodo > 0) by admit.
    admit. (* TODO: use the fact that mtodo ≠ ∅ *)
  }
  replace (m) with (mdone); last first.
  { simpl in Hunion. by rewrite left_id in Hunion. }
  iFrame.
Admitted.


Implicit Types (γ : kvservice_names).

Local Notation "k [[ γ ]]↦ '_'" := (∃ v, k [[γ]]↦ v)%I
(at level 20, format "k  [[ γ ]]↦ '_'") : bi_scope.

Record KVServerC :=
  {
  kvsM : gmap u64 u64;
  }.

Global Instance PutPre_disc γ args : Discretizable (Put_Pre γ args) := _.
Global Instance PutPre_timeless γ args : Timeless (Put_Pre γ args) := _.

Definition KVServer_core_own_durable server rpc_server : iProp Σ :=
  ∃ rlastSeq rlastReply rkvs data,
    "%" ∷ ⌜has_map_encoding server.(kvsM) rkvs⌝ ∗
    "%" ∷ ⌜has_map_encoding rpc_server.(lastSeqM) rlastSeq⌝ ∗
    "%" ∷ ⌜has_map_encoding rpc_server.(lastReplyM) rlastReply⌝ ∗
    "%" ∷ ⌜has_encoding data (rlastSeq ++ rlastReply ++ rkvs)⌝ ∗
    "Hkvdur" ∷ "kvdur" f↦ data
.

Definition KVServer_core_own_vol (srv:loc) kv_server : iProp Σ :=
  ∃ (kvs_ptr:loc),
  "HkvsOwn" ∷ srv ↦[KVServer.S :: "kvs"] #kvs_ptr ∗
  "HkvsMap" ∷ is_map (kvs_ptr) kv_server.(kvsM)
.

Definition KVServer_core_own_ghost γ kv_server : iProp Σ :=
  "Hkvctx" ∷ map_ctx γ.(ks_kvMapGN) 1 kv_server.(kvsM)
.

Definition RPCServer_own_vol (sv:loc) rpc_server : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc),
    "HlastSeqOwn" ∷ sv ↦[RPCServer.S :: "lastSeq"] #lastSeq_ptr
∗ "HlastReplyOwn" ∷ sv ↦[RPCServer.S :: "lastReply"] #lastReply_ptr
∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) rpc_server.(lastSeqM)
∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) rpc_server.(lastReplyM)
.

Definition RPCServer_own_ghost (sv:loc) γrpc rpc_server : iProp Σ :=
  "Hsrpc" ∷ RPCServer_own γrpc rpc_server.(lastSeqM) rpc_server.(lastReplyM) (* TODO: Probably should get better naming for this *)
.

Definition RPCServer_phys_own γrpc (sv:loc) rpc_server : iProp Σ :=
  "Hrpcvol" ∷ RPCServer_own_vol sv rpc_server ∗
  "Hrpcghost" ∷ RPCServer_own_ghost sv γrpc rpc_server
.

Instance durable_timeless kv_server rpc_server: Timeless (KVServer_core_own_durable kv_server rpc_server) := _.

Instance durable_disc kv_server rpc_server: Discretizable (KVServer_core_own_durable kv_server rpc_server) := _.

Definition own_kvclerk γ ck_ptr srv : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient cl_ptr γ.(ks_rpcGN).


Definition kv_core_mu srv γ : rpc_core_mu :=
  {|
  core_own_durable := λ server rpc_server, KVServer_core_own_durable server rpc_server;
  core_own_ghost := λ server, KVServer_core_own_ghost γ server;
  core_own_vol := λ server, KVServer_core_own_vol srv server
  |}.

Lemma wpc_put_core γ (srv:loc) args kvserver req :
{{{
     (kv_core_mu srv γ).(core_own_vol) kvserver ∗
     Put_Pre γ args
}}}
  KVServer__put_core #srv (into_val.to_val args) @ 36 ; ⊤
{{{
      kvserver' (r:u64) P', RET #r;
            (<disc> P') ∗
            KVServer_core_own_vol srv kvserver' ∗
            <disc> (P' -∗ Put_Pre γ args) ∗
            (* TODO: putting this here because need to be discretizable *)
            <disc> (P' -∗ KVServer_core_own_ghost γ kvserver ={⊤∖↑rpcRequestInvN req}=∗ Put_Post γ args r ∗ KVServer_core_own_ghost γ kvserver')
}}}
{{{
     Put_Pre γ args
}}}.
Proof.
  iIntros (Φ Φc) "[Hvol Hpre] HΦ".
  iCache with "Hpre HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. by iApply "HΦc". }
  wpc_call; first done.

  iCache with "Hpre HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. by iApply "HΦc". }

  wpc_pures.
  iNamed "Hvol".

  wpc_bind (struct.loadF _ _ _)%E.
  wpc_frame.
  wp_loadField.
  iNamed 1.

  wpc_bind (MapInsert _ _ _).
  wpc_frame.

  wp_apply (wp_MapInsert with "HkvsMap"); eauto; iIntros "HkvsMap".
  iNamed 1.
  wpc_pures.
  iDestruct "HΦ" as "[_ HΦ]".
  iApply ("HΦ" $! {| kvsM := <[args.(U64_1):=args.(U64_2)]> kvserver.(kvsM) |} _ (Put_Pre γ args)).
  iFrame.
  iSplitL "Hpre".
  {
    iModIntro. iFrame.
  }
  iSplitR "".
  { iExists _; iFrame. }
  iSplitL ""; first eauto.
  iModIntro.
  iIntros "Hpre Hghost".
  iDestruct "Hpre" as (v) "Hpre".
  iMod (map_update with "Hghost Hpre") as "[Hkvctx Hptsto]".
  iModIntro. iFrame.
Qed.

Lemma wpc_WriteDurableKVServer γ (srv rpc_srv:loc) server rpc_server server' rpc_server':
  readonly (srv ↦[lockservice.KVServer.S :: "sv"] #rpc_srv) -∗
  {{{
      "Hvol" ∷ (kv_core_mu srv γ).(core_own_vol) server' ∗
      "Hrpcvol" ∷ RPCServer_own_vol rpc_srv rpc_server' ∗
      "Hdurable" ∷ (kv_core_mu srv γ).(core_own_durable) server rpc_server
  }}}
    WriteDurableKVServer #srv @ 36 ; ⊤
  {{{
        RET #();
      (kv_core_mu srv γ).(core_own_vol) server' ∗
      RPCServer_own_vol rpc_srv rpc_server' ∗
      (kv_core_mu srv γ).(core_own_durable) server' rpc_server'
  }}}
  {{{
      (kv_core_mu srv γ).(core_own_durable) server rpc_server ∨
      (kv_core_mu srv γ).(core_own_durable) server' rpc_server'
  }}}.
Proof.
  iIntros "#Hsv".
  iIntros (Φ Φc) "!# Hpre HΦ".
  iNamed "Hpre".

  wpc_call.
  { by iLeft. }
  { eauto. }
  iCache with "Hdurable HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iApply "HΦc". by iLeft. }

  wp_pures.
  iNamed "Hvol".
  iNamed "Hrpcvol".

  wpc_loadField.

  (* Compute size of encoded data *)
  repeat (wpc_bind (struct.loadF _ _ _)%E;
  wpc_frame;
  wp_loadField;
  iNamed 1
  ).

  wpc_bind (MapLen _)%E.
  wpc_frame.
  wp_apply (wp_MapLen with "HlastSeqMap").
  iIntros "[%HlastSeqSize HlastSeqMap]".
  iNamed 1.

  wpc_pures.

  wpc_bind (struct.loadF _ _ _)%E.
  wpc_frame.
  wp_loadField.
  wp_loadField.
  iNamed 1.

  wpc_bind (MapLen _)%E.
  wpc_frame.
  (* TODO: this should be lastReplyMap, unless we can make sure that lastSeq and lastReply have the same size *)
  wp_apply (wp_MapLen with "HlastSeqMap").
  iIntros "[%_ HlastSeqMap]".
  iNamed 1.

  wpc_pures.
  wpc_bind (struct.loadF _ _ _)%E.
  wpc_frame.
  wp_loadField.
  iNamed 1.

  wpc_bind (MapLen _)%E.
  wpc_frame.
  wp_apply (wp_MapLen with "HkvsMap").
  iIntros "[%HkvsSize HkvsMap]".
  iNamed 1.

  wpc_pures.

  (* Done computing size of encoder *)

  (* FIXME: add necessary overflow guards in code *)
  replace (word.add (word.add (word.add (word.mul (word.mul 8 2)
                (size rpc_server'.(lastSeqM)))
            (word.mul 2 (size rpc_server'.(lastSeqM))))
                              (word.mul 2 (size server'.(kvsM)))) 3) with
      (U64 (8 * 2 * ((size rpc_server'.(lastSeqM)) + (size rpc_server'.(lastSeqM)) + (size server.(kvsM)) + 3))); last first.
  {
    admit.
  }

  wpc_bind (marshal.NewEnc _)%E.
  wpc_frame.
  wp_apply (wp_new_enc).
  iIntros (enc_v) "Henc".
  iNamed 1.

  replace (int.Z (U64 (_))) with
      ((8 * 2 * ((size rpc_server'.(lastSeqM)) + (size rpc_server'.(lastSeqM)) + (size server.(kvsM))+ 3))); last first.
  { (* want to know that the entire expression has not overflowed *) admit. }


  wpc_pures.

  wpc_bind (struct.loadF _ _ _)%E.
  wpc_frame.
  wp_loadField.
  wp_loadField.
  iNamed 1.

  wpc_bind (EncMap _ _)%E.
  wpc_frame.
  wp_apply (wp_EncMap with "[$Henc $HlastSeqMap]").
  { unfold marshalledMapSize. Lia.lia. }
  iIntros (rlastSeqMap) "(%HrlastSeqMap & HlastSeqMap & Henc)".
  iNamed 1.

  wpc_pures.
  wpc_bind (struct.loadF _ _ _)%E.
  wpc_frame.
  wp_loadField.
  wp_loadField.
  iNamed 1.

  wpc_bind (EncMap _ _)%E.
  wpc_frame.
  assert (size rpc_server'.(lastReplyM) = size rpc_server'.(lastSeqM)) by admit.
  wp_apply (wp_EncMap with "[$Henc $HlastReplyMap]").
  { unfold marshalledMapSize.
    Lia.lia. }
  iIntros (rlastReplyMap) "(%HrlastReplyMap & HlastReplyMap & Henc)".
  iNamed 1.

  wpc_pures.

  wpc_bind (struct.loadF _ _ _)%E. wpc_frame. wp_loadField.
  iNamed 1.

  wpc_bind (EncMap _ _)%E.
  wpc_frame.
  wp_apply (wp_EncMap with "[$Henc $HkvsMap]").
  { unfold marshalledMapSize.
    rewrite H0.
    admit. (* FIXME: size was incorrectly rewritten above *)
  }
  iIntros (rkvsMap) "(%HrkvsMap & HkvsMap & Henc)".
  iNamed 1.
  wpc_pures.

  wpc_bind (marshal.Enc__Finish _)%E.
  wpc_frame.
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s data) "(%Hencoding & %Hlength & Hslice)".
  iNamed 1.
  iNamed "Hdurable".

  wpc_bind (Write _ _)%E.
  iApply (wpc_Write with "[$Hslice $Hkvdur]"); eauto.

  rewrite -app_assoc in Hencoding.
  iSplit.
  {
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iIntros "Hkvdur".
    iApply "HΦc".
    iDestruct "Hkvdur" as "[Hkvdur|Hkvdur]".
    - iLeft. iExists _, _, _, data0. eauto.
    - iRight. iExists rlastSeqMap, rlastReplyMap, rkvsMap, data. eauto.
  }
  iNext.
  iIntros "[Hkvdur Hslice]".
  wpc_pures.
  {
    iDestruct "HΦ" as "[HΦc _]". iModIntro. iApply "HΦc".
    iRight. iExists rlastSeqMap, rlastReplyMap, rkvsMap, data. eauto.
  }
  iDestruct "HΦ" as "[_ HΦ]".
  iApply "HΦ".
  iSplitL "HkvsOwn HkvsMap".
  { iExists _. iFrame. }
  iSplitL "HlastSeqOwn HlastReplyOwn HlastSeqMap HlastReplyMap".
  { iExists _, _. iFrame. }
  iExists rlastSeqMap, rlastReplyMap, rkvsMap, data. eauto.
Admitted.

Definition is_kvserver γ (srv:loc) : iProp Σ :=
  ∃ (rpc_srv:loc),
  "#Hsv" ∷ readonly (srv ↦[KVServer.S :: "sv"] #rpc_srv) ∗
  "#His_server" ∷ is_server KVServerC (kv_core_mu srv γ) rpc_srv γ.(ks_rpcGN).


Lemma KVServer__Put_spec srv γ :
is_kvserver γ srv -∗
{{{
    True
}}}
    KVServer__Put #srv
{{{ (f:goose_lang.val), RET f;
        ∀ args req, is_rpcHandler f γ.(ks_rpcGN) args req (Put_Pre γ args) (Put_Post γ args)
}}}.
Proof.
  iNamed 1.
  iIntros (Φ) "!# Hpre HΦ".
  wp_lam.
  wp_pures.
  iApply "HΦ".
  iIntros (args req).
  iApply is_rpcHandler_eta. simpl.
  iIntros "!#" (_ _).
  wp_pures.
  wp_loadField.
  clear Φ.
  iApply (RPCServer__HandleRequest_is_rpcHandler KVServerC); last by eauto.
  {
    iIntros (server) "!#". iIntros (Φ Φc) "Hpre HΦ".
    iNamed "Hpre".
    iMod "Hpre".
    wpc_pures.
    {
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro.
      by iApply "HΦc".
    }

    iApply (wpc_put_core γ with "[$Hpre $Hvol]").
    iSplit.
    {
      by iDestruct "HΦ" as "[HΦc _]".
    }
    iNext.
    iDestruct "HΦ" as "[_ HΦ]".
    iFrame.
    (* TODO: match up the core postcondition *)
    admit.
  }
  {
    iIntros (server rpc_server server' rpc_server') "!#".
    iIntros (Φ Φc) "Hpre HΦ".
    wpc_pures.
    {
      iDestruct "Hpre" as "(_ & _ & Hdur)". (* Requires own_durable to be discretizable *)
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro.
      iApply "HΦc".
      by iLeft.
    }
    wpc_apply (wpc_WriteDurableKVServer with "Hsv Hpre").
    iSplit.
    {
      by iDestruct "HΦ" as "[HΦc _]".
    }
    iNext. by iDestruct "HΦ" as "[_ HΦ]".
  }
  {
    iFrame "#".
  }
Admitted.

End kv_durable_proof.
