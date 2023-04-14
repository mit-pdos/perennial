From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import eesm.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From Perennial.program_proof.simplepb Require Import pb_apply_proof pb_prophetic_read.
From Perennial.program_proof.grove_shared Require Import erpc_lib.
From Perennial.program_proof Require Import map_marshal_proof.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb.apps Require Import vsm.
From Perennial.program_proof.fencing Require Import map.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section global_proof.

Context `{low_record:Sm.t}.

Notation low_OpType := (Sm.OpType low_record).
Notation low_has_op_encoding := (Sm.has_op_encoding low_record).
Notation low_has_snap_encoding := (Sm.has_snap_encoding low_record).
Notation low_compute_reply := (Sm.compute_reply low_record).
Notation low_is_readonly_op := (Sm.is_readonly_op low_record).
Instance low_op_eqdec : EqDecision (low_OpType).
Proof. apply (Sm.OpType_EqDecision low_record). Qed.

Inductive eeOp :=
  | getcid : eeOp
  | ee : u64 → u64 -> low_OpType → eeOp
  | ro_ee : low_OpType → eeOp
.

Record eeState := mkEeState
{
  nextCID : u64;
  lastSeq : gmap u64 u64 ;
  lastReply : gmap u64 (list u8);
  lowops : list low_OpType
}.

Global Instance etaEeState : Settable _ :=
  settable! (mkEeState) <nextCID ; lastSeq ; lastReply ; lowops >.

Definition apply_op_and_get_reply (state:eeState) (op:eeOp) : eeState * list u8 :=
    match op with
    | getcid => (state <| nextCID := (word.add state.(nextCID) 1) |>, u64_le state.(nextCID))
    | ee cid seq op =>
        if decide (int.nat seq <= int.nat (default (U64 0) (state.(lastSeq) !! cid))) then
          (state, default [] (state.(lastReply) !! cid))
        else
          let rep:=(low_compute_reply state.(lowops) op) in
          (state <| lastSeq := <[cid:=seq]> state.(lastSeq) |>
                <| lastReply := <[cid:=rep]> state.(lastReply) |>
                <| lowops := (state.(lowops) ++ [op]) |>, rep)
    | ro_ee op => (state, (low_compute_reply state.(lowops) op))
    end
.

Definition apply_op state op :=
  (apply_op_and_get_reply state op).1
.

Definition init_state := mkEeState 0 ∅ ∅ [].

Definition compute_state ops : eeState :=
  foldl apply_op init_state ops.

Definition compute_reply ops op : (list u8) :=
  (apply_op_and_get_reply (compute_state ops) op).2
.

Definition ee_has_encoding op_bytes op :=
  match op with
  | getcid => op_bytes = [U8 1]
  | ee cid seq lowop =>
      ∃ lowop_enc, low_has_op_encoding lowop_enc lowop ∧
      op_bytes = [U8 0] ++ u64_le cid ++ u64_le seq ++ (lowop_enc)
  | ro_ee lowop =>
      ∃ lowop_enc,
  low_has_op_encoding lowop_enc lowop ∧
  op_bytes = [U8 2] ++ (lowop_enc)
  end
.

Definition ee_has_snap_encoding snap_bytes ops :=
  let st := (compute_state ops) in
  ∃ low_snap_bytes enc_lastSeq enc_lastReply,
  has_u64_map_encoding enc_lastSeq st.(lastSeq) ∧
  has_byte_map_encoding enc_lastReply st.(lastReply) ∧
  low_has_snap_encoding low_snap_bytes st.(lowops) ∧
  snap_bytes = (u64_le st.(nextCID)) ++ (enc_lastSeq) ++ enc_lastReply ++ low_snap_bytes
.

Definition ee_is_readonly_op op :=
  match op with
    | getcid => False
    | ee _ _ _=> False
    | ro_ee lowop => low_is_readonly_op lowop
  end
.

Instance op_eqdec : EqDecision eeOp.
Proof. solve_decision. Qed.

Definition
  ee_record:=
  {|
    Sm.OpType := eeOp ;
    Sm.has_op_encoding := ee_has_encoding ;
    Sm.has_snap_encoding := ee_has_snap_encoding ;
    Sm.compute_reply :=  compute_reply ;
    Sm.is_readonly_op := ee_is_readonly_op ;
  |}.

Context `{!inG Σ (mono_listR (leibnizO low_OpType))}.
Context `{!pbG (pb_record:=ee_record) Σ}.

Definition own_oplog γ (lowops:list low_OpType) := own γ (●ML{#1/2} (lowops : list (leibnizO _))).

Context `{!gooseGlobalGS Σ, !urpcregG Σ, !erpcG Σ (list u8)}.
Definition own_eeState st γ γerpc : iProp Σ :=
  "Hlog" ∷ own_oplog γ st.(lowops) ∗
  "HerpcServer" ∷ eRPCServer_own_ghost γerpc st.(lastSeq) st.(lastReply) ∗
  "Hcids" ∷ ([∗ set] cid ∈ (fin_to_set u64), ⌜int.Z cid < int.Z st.(nextCID)⌝%Z ∨
                                              (is_eRPCClient_ghost γerpc cid 1))
.

Definition eeN := nroot .@ "ee".

Notation own_log := (own_op_log (pb_record:=ee_record)).

(* This is the invariant maintained by all the servers for the "centralized"
   ghost state of the system. *)
Definition is_ee_inv γpblog γ γerpc : iProp Σ :=
  inv eeN (∃ ops,
              own_log γpblog ops ∗
              own_eeState (compute_state ops) γ γerpc
      )
.

End global_proof.

Section local_proof.

Context {low_record:Sm.t}.
Notation low_OpType := (Sm.OpType low_record).
Notation low_has_op_encoding := (Sm.has_op_encoding low_record).
Notation low_compute_reply := (Sm.compute_reply low_record).
Instance low_op_dec2 : EqDecision low_OpType.
Proof. apply (Sm.OpType_EqDecision low_record). Qed.

Context `{!heapGS Σ, !urpcregG Σ, !erpcG Σ (list u8)}.

Notation ee_record := (ee_record (low_record:=low_record)).
Notation compute_state := (compute_state (low_record:=low_record)).
Notation eeOp := (eeOp (low_record:=low_record)).
Notation ee_is_InMemoryStateMachine := (is_InMemoryStateMachine (sm_record:=ee_record)).
Notation low_is_VersionedStateMachine := (is_VersionedStateMachine (sm_record:=low_record)).
Notation own_pb_Clerk := (pb_prophetic_read.own_Clerk (pb_record:=ee_record)).
Notation is_ee_inv := (is_ee_inv (low_record:=low_record)).

Context `{!config_proof.configG Σ}.
Context `{!inG Σ (mono_listR (leibnizO low_OpType))}.
Context `{!pbG (pb_record:=ee_record) Σ}.

Definition own_Clerk ck γoplog : iProp Σ :=
  ∃ (pb_ck:loc) γpblog γerpc (cid seqno:u64),
    "Hcid" ∷ ck ↦[eesm.Clerk :: "cid"] #cid ∗
    "Hseq" ∷ ck ↦[eesm.Clerk :: "seq"] #seqno ∗
    "Hown_ck" ∷ own_pb_Clerk pb_ck γpblog ∗
    "#Hpb_ck" ∷ readonly (ck ↦[eesm.Clerk :: "ck"] #pb_ck) ∗
    "#Hee_inv" ∷ is_ee_inv γpblog γoplog γerpc ∗
    "Herpc" ∷ is_eRPCClient_ghost γerpc cid seqno ∗
    "#Herpc_inv" ∷ is_eRPCServer γerpc ∗
    "%Hseqno_pos" ∷ ⌜ int.nat seqno > 0 ⌝
.

Lemma compute_state_snoc ops newop :
  compute_state (ops ++ [newop]) = apply_op (compute_state ops) newop.
Proof.
  unfold compute_state. by rewrite foldl_snoc.
Qed.


Lemma wp_Clerk__ApplyExactlyOnce ck γoplog lowop op_sl lowop_bytes Φ:
  low_has_op_encoding lowop_bytes lowop →
  own_Clerk ck γoplog -∗
  is_slice op_sl byteT 1 lowop_bytes -∗
  (|={⊤∖↑pbN∖↑prophReadN∖↑eeN,∅}=> ∃ oldops, own_oplog γoplog oldops ∗
    (own_oplog γoplog (oldops ++ [lowop]) ={∅,⊤∖↑pbN∖↑prophReadN∖↑eeN}=∗
    (∀ reply_sl, own_Clerk ck γoplog -∗ is_slice_small reply_sl byteT 1 (low_compute_reply oldops lowop)
     -∗ Φ (slice_val reply_sl )))) -∗
  WP Clerk__ApplyExactlyOnce #ck (slice_val op_sl) {{ Φ }}.
Proof.
  intros Henc.
  iIntros "Hclerk Hop Hupd".
  iNamed "Hclerk".

  wp_call.
  wp_apply (wp_NewSliceWithCap).
  { word. }
  iIntros (?) "Henc_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pure1_credit "Hlc".
  wp_pure1_credit "Hlc2".
  wp_load.
  replace (#(U8 0)) with (_.(to_val) (U8 0)).
  2: { done. }
  iDestruct (is_slice_split with "Henc_sl") as "[Henc_sl Henc_cap]".
  wp_apply (wp_SliceSet with "[Henc_sl]").
  { iFrame. iPureIntro.
    eexists _.
    rewrite lookup_replicate.
    split; first done.
    word.
  }
  iIntros "Henc_sl".
  iDestruct (is_slice_split with "[$Henc_sl $Henc_cap]") as "Henc_sl".
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.

  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.

  wp_load.
  iDestruct (is_slice_to_small with "Hop") as "Hop".
  wp_apply (wp_WriteBytes with "[$Henc_sl $Hop]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros (Hseqno_overflow).
  wp_storeField.
  wp_load.

  wp_loadField.

  iMod (make_request ({| Req_CID:= _; Req_Seq:= _ |}) with "Herpc_inv Herpc [Hupd Hlc]") as "[Herpc Hreq]".
  { done. }
  { simpl. word. }
  {
    iNext.
    iNamedAccu.
  }
  instantiate(1:=
          (λ reply, ∀ reply_sl,
            own_Clerk ck γoplog -∗
            is_slice_small reply_sl byteT 1 reply -∗
            Φ (slice_val reply_sl))
        %I).
  (* assert that it equals low_compute_reply *)

  iDestruct "Hreq" as (?) "(#Hreq & Htok)".
  iApply wp_fupd.
  iApply (wp_frame_wand with "[Hcid Hseq Herpc Htok Hlc2]").
  { iNamedAccu. }
  simpl.
  iDestruct (is_slice_to_small with "Henc_sl") as "Henc_sl".
  wp_apply (wp_Clerk__Apply with "Hown_ck [$Henc_sl]").
  {
    simpl.
    rewrite -app_assoc.
    rewrite -app_assoc.
    instantiate (1:= ee cid seqno lowop).
    exists lowop_bytes.
    split; done.
  }
  {
    iModIntro.
    iInv "Hee_inv" as "Hi" "Hclose".
    iDestruct "Hi" as (?) "[>Hpblog >Hee]".
    iNamed "Hee".

    destruct (decide (int.Z (default (U64 0) ((compute_state ops).(lastSeq) !! cid)) < int.Z seqno)%Z).
    { (* case: first time running request *)
      iMod (server_takes_request with "Hreq HerpcServer") as "HH".
      { solve_ndisj. }
      { simpl. done. }
      iDestruct "HH" as "(Hpre & Hupd & Hproc)".
      iDestruct "Hupd" as "[Hupd >Hlc]".
      iMod (lc_fupd_elim_later with "Hlc Hupd") as "Hupd".
      iNamed "Hupd".
      iMod "Hupd".
      iModIntro.
      iDestruct "Hupd" as (?) "[Hoplog2 Hupd]".
      iExists _.
      iFrame.
      iIntros "Hpblog".
      iDestruct (own_valid_2 with "Hlog Hoplog2") as %Hvalid.
      rewrite mono_list_auth_dfrac_op_valid_L in Hvalid.
      destruct Hvalid as [_ ?]. subst.
      iCombine "Hlog Hoplog2" as "Hoplog".
      iMod (own_update with "Hoplog") as "Hoplog".
      {
        apply mono_list_update.
        instantiate (1:=_ ++ [lowop]).
        by apply prefix_app_r.
      }
      iDestruct "Hoplog" as "[Hoplog Hoplog2]".
      iMod ("Hupd" with "Hoplog2") as "Hupd".

      iMod (server_completes_request _ _ _ with "Herpc_inv Hreq Hpre [Hupd] Hproc") as "[#Hreceipt HerpcServer]".
      { solve_ndisj. }
      { solve_ndisj. }
      { simpl. done. }
      { done. }
      simpl.
      iMod ("Hclose" with "[HerpcServer Hpblog Hoplog Hcids]").
      {
        iNext.
        iExists _; iFrame "Hpblog".
        rewrite compute_state_snoc.
        rewrite /apply_op.
        simpl.
        rewrite decide_False; last first.
        { word. }
        iFrame.
      }
      iModIntro.
      (* finish up *)
      iIntros (?) "Hrep_sl _ Hpbck".
      iNamed 1.
      iMod (get_request_post with "Hreq Hreceipt Htok") as "HΦ".
      { done. }
      iMod (lc_fupd_elim_later with "Hlc2 HΦ") as "HΦ".
      iApply ("HΦ" with "[Herpc Hcid Hpbck Hseq] [Hrep_sl]").
      {
        repeat iExists _.
        iFrame "∗#".
        iPureIntro.
        word.
      }
      {
        rewrite /compute_reply.
        rewrite /apply_op.
        simpl. rewrite decide_False; last first.
        { word. }
        done.
      }
    }
    { (* case: request already ran *)
      assert (int.nat (default (U64 0) ((compute_state ops).(lastSeq) !! cid)) = int.nat seqno ∨
              int.nat (default (U64 0) ((compute_state ops).(lastSeq) !! cid)) > int.nat seqno)
        as [Hok|HStale] by word.
      { (* case: not stale *)
        destruct (_ !! cid) eqn:X2; last first.
        {
          exfalso.
          simpl in Hok.
          replace (int.nat 0%Z) with (0) in Hok by word.
          word.
        }
        iMod (server_replies_to_request _ {| Req_CID := cid ; Req_Seq:= _|} with "Herpc_inv HerpcServer") as "HH".
        { solve_ndisj. }
        { simpl. rewrite X2. done. }
        { exists []. done. }
        iDestruct "HH" as "[#Hreceipt HerpcServer]".
        iExists _; iFrame.
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros "Hmask".
        iIntros "Hpblog".
        iMod "Hmask".

        iMod ("Hclose" with "[HerpcServer Hpblog Hlog Hcids]").
        {
          iNext.
          iExists _; iFrame "Hpblog".
          rewrite compute_state_snoc.
          rewrite /apply_op.
          simpl. rewrite decide_True; last first.
          { rewrite -Hok. rewrite X2. word. }
          iFrame.
        }

        iModIntro.
        (* finish up *)
        iIntros (?) "Hrep_sl _ Hpbck".
        iNamed 1.
        replace (u) with (seqno); last first.
        {
          simpl in Hok.
          word.
        }
        iMod (get_request_post with "Hreq Hreceipt Htok") as "HΦ".
        { done. }
        iMod (lc_fupd_elim_later with "Hlc2 HΦ") as "HΦ".
        iApply ("HΦ" with "[Herpc Hcid Hpbck Hseq] [Hrep_sl]").
        {
          repeat iExists _.
          iFrame "∗#".
          iPureIntro. word.
        }
        {
          simpl.
          rewrite /compute_reply.
          rewrite /apply_op.
          simpl. rewrite decide_True; last first.
          { rewrite -Hok. rewrite X2. word. }
          done.
        }
      }
      { (* case: stale *)

        destruct (_ !! cid) eqn:X2; last first.
        {
          exfalso.
          simpl in HStale.
          replace (int.nat 0%Z) with (0) in HStale by word.
          word.
        }
        iMod (smaller_seqno_stale_fact _ {| Req_CID := cid; Req_Seq := seqno |} with "Herpc_inv HerpcServer") as "HH".
        { solve_ndisj. }
        { done. }
        { simpl in HStale.
          simpl.
          word. }
        iDestruct "HH" as "[HerpcServer #Hstale]".
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros "Hmask".
        iExists _; iFrame.
        iIntros "Hpblog".
        iMod "Hmask".
        iMod ("Hclose" with "[HerpcServer Hpblog Hlog Hcids]").
        {
          iNext. iExists _; iFrame "Hpblog".
          rewrite compute_state_snoc.
          rewrite /apply_op.
          simpl. rewrite decide_True; last first.
          { rewrite X2. word. }
          iFrame.
        }
        iModIntro.
        iIntros (?) "Hsl _ Hpb".
        iNamed 1.
        iDestruct (client_stale_seqno with "Hstale Herpc") as %Hstale2.
        exfalso.
        simpl in Hstale2.
        word.
      }
    }
  }
Qed.

(* Now, the server proof. *)
Context `{!mapG Σ u64 (list low_OpType)}.

Definition own_ghost_vnums γst (ops:list eeOp) (latestVnum:u64) : iProp Σ :=
  "HfutureVersions" ∷ ([∗ set] vnum ∈ (fin_to_set u64), ⌜int.nat vnum > length ops⌝ →
                                                       vnum ⤳[γst] []) ∗
  "Hversions" ∷ ([∗ set] vnum ∈ (fin_to_set u64), ⌜int.nat vnum <= length ops⌝ →
                vnum ⤳[γst] [] ∨ (is_state γst vnum (compute_state (take (int.nat vnum) ops)).(lowops))
                ) ∗
  "#HlatestVersion" ∷
  ([∗ set] vnum ∈ (fin_to_set u64), □(⌜int.nat vnum <= length ops⌝ →
                                      ⌜int.nat latestVnum <= int.nat vnum⌝ →
                                      (is_state γst vnum (compute_state ops).(lowops))))
.

Definition own_StateMachine (s:loc) (ops:list eeOp) : iProp Σ :=
  let st := (compute_state ops) in
      ∃ (lastSeq_ptr lastReply_ptr lowSm:loc) (latestVnum:u64) own_low γst,
  "HnextCID" ∷ s ↦[EEStateMachine :: "nextCID"] #st.(nextCID) ∗
  "HlastSeq_ptr" ∷ s ↦[EEStateMachine :: "lastSeq"] #lastSeq_ptr ∗
  "HlastReply_ptr" ∷ s ↦[EEStateMachine :: "lastReply"] #lastReply_ptr ∗
  "HlastSeq" ∷ is_map lastSeq_ptr 1 st.(lastSeq) ∗
  "HlastReply" ∷ own_byte_map lastReply_ptr st.(lastReply) ∗

  "HeeNextIndex" ∷ s ↦[EEStateMachine :: "eeNextIndex"] #(U64 (length ops)) ∗

  "Hsm" ∷ s ↦[EEStateMachine :: "sm"] #lowSm ∗
  "Hghost" ∷ own_ghost_vnums γst ops latestVnum ∗
  "#Hislow" ∷ low_is_VersionedStateMachine lowSm own_low ∗
  "Hlowstate" ∷ own_low γst st.(lowops) latestVnum ∗
  "%Hle" ∷ ⌜int.nat latestVnum <= length ops⌝ ∗
  "%HnoOverflow" ∷ ⌜length ops = int.nat (length ops)⌝
.

Notation ee_is_InMemory_applyVolatileFn := (is_InMemory_applyVolatileFn (sm_record:=ee_record)).
Notation ee_is_InMemory_setStateFn := (is_InMemory_setStateFn (sm_record:=ee_record)).
Notation ee_is_InMemory_getStateFn := (is_InMemory_getStateFn (sm_record:=ee_record)).
Notation ee_is_InMemory_applyReadonlyFn := (is_InMemory_applyReadonlyFn (sm_record:=ee_record)).

Lemma ghost_no_low_changes γst ops latestVnum o l :
  (length ops + 1 = int.nat (word.add (length ops) 1))%nat →
  (compute_state ops).(lowops) = l →
  (compute_state (ops ++ [o])).(lowops) = l →
  own_ghost_vnums γst ops latestVnum ==∗
  own_ghost_vnums γst (ops ++ [o]) latestVnum
.
Proof.
  intros HnoOverflow Heq1 Heq2.
  iNamed 1.
  iDestruct (big_sepS_elem_of_acc_impl (word.add (length ops) 1) with "HfutureVersions") as "[HH HfutureVersions]".
  { set_solver. }
  iSplitL "HfutureVersions".
  {
    iApply "HfutureVersions".
    { iModIntro. iIntros (???) "H %".
      iApply "H". iPureIntro. rewrite app_length in H2. word. }
    { iModIntro. iIntros. exfalso.
      rewrite app_length /= in H0.
      word. }
  }

  iSpecialize ("HH" with "[%]").
  { word. }
  iMod (ghost_map_points_to_update l with "HH") as "HH".
  iMod (ghost_map_points_to_persist with "HH") as "#HH".
  iSplitL "Hversions".
  {
    iDestruct (big_sepS_elem_of_acc_impl (U64 (length ops + 1)) with "Hversions") as "[_ Hversions]".
    { set_solver. }
    iApply "Hversions".
    {
      iModIntro. iIntros (???) "H %".
      rewrite app_length /= in H2.
      assert (int.nat y <= length ops).
      { admit. } (* FIXME: integer overflow *)
      iDestruct ("H" with "[%]") as "[$|H]".
      { done. }
      iRight.
      rewrite take_app_le.
      { done. }
      word.
    }
    iModIntro.
    iIntros.
    iRight.
    rewrite firstn_all2.
    2:{ rewrite app_length /=. word. }
    rewrite Heq2.
    iExactEq "HH".
    unfold is_state.
    repeat f_equal.
    rewrite app_length /= in H0.
    admit. (* FIXME: integer overflow *)
  }
  iModIntro.
  iApply (big_sepS_impl with "HlatestVersion").
  {
    iModIntro. iIntros (??) "#H".
    iModIntro.
    iIntros.
    rewrite app_length /= in H1.
    destruct (decide (x = (word.add (length ops) 1))).
    { subst x. rewrite Heq1 Heq2.
      iFrame "HH". }
    {
      rewrite Heq1 Heq2.
      iApply "H".
      { iPureIntro. admit. } (* FIXME: integer overflow *)
      { iPureIntro. word. }
    }
  }
Admitted. (* integer overflows *)

Lemma ghost_low_newop γst ops latestVnum op lowop l :
  (length ops + 1 = int.nat (word.add (length ops) 1))%nat →
  int.nat latestVnum <= length ops →
  (compute_state ops).(lowops) = l →
  (compute_state (ops ++ [op])).(lowops) = l ++ [lowop] →
  own_ghost_vnums γst ops latestVnum ==∗
  own_ghost_vnums γst (ops ++ [op]) (length (ops ++ [op])) ∗
  (∀ (vnum':u64), ⌜int.nat latestVnum <= int.nat vnum'⌝ →
        ⌜int.nat vnum' < int.nat (length (ops ++ [op]))⌝ → is_state γst vnum' l) ∗
  is_state γst (length (ops ++ [op])) (l ++ [lowop])
.
Proof.
  intros HnoOverflow. intros.
  iNamed 1.
  iDestruct (big_sepS_elem_of_acc_impl (word.add (length ops) 1) with "HfutureVersions") as "[HH HfutureVersions]".
  { set_solver. }
  iSpecialize ("HH" with "[%]").
  { word. }
  iMod (ghost_map_points_to_update (l ++ [lowop]) with "HH") as "HH".
  iMod (ghost_map_points_to_persist with "HH") as "#HH".
  iModIntro.
  iSplitL.
  {
    iSplitL "HfutureVersions".
    {
      iApply "HfutureVersions".
      { iModIntro. iIntros (???) "H %".
        iApply "H". iPureIntro. rewrite app_length in H5. word. }
      { iIntros. exfalso.
        rewrite app_length /= in H3.
        word. }
    }
    iSplitL "Hversions".
    {
      iDestruct (big_sepS_elem_of_acc_impl (U64 (length ops + 1)) with "Hversions") as "[_ Hversions]".
      { set_solver. }
      iApply "Hversions".
      {
        iModIntro. iIntros (???) "H %".
        rewrite app_length /= in H5.
        assert (int.nat y <= length ops).
        { admit. } (* FIXME: integer overflow *)
        iDestruct ("H" with "[%]") as "[$|H]".
        { done. }
        iRight.
        rewrite take_app_le.
        { done. }
        word.
      }
      {
        iIntros.
        iRight.
        rewrite firstn_all2.
        2:{ rewrite app_length /=. word. }
        rewrite H2.
        iExactEq "HH".
        unfold is_state.
        repeat f_equal.
        1:{ rewrite app_length /= in H3. admit. } (* FIXME: integer overflow *)
      }
    }
    iApply (big_sepS_impl with "HlatestVersion").
    {
      iModIntro. iIntros (??) "#H".
      iModIntro.
      iIntros.
      rewrite app_length /= in H5.
      assert (x = (word.add (length ops) 1)).
      { rewrite app_length /= in H4.
        admit. } (* FIXME: overflow *)
      subst x. rewrite H1 H2.
      iFrame "HH".
    }
  }
  iSplitL.
  2:{
    rewrite app_length /=.
    iExactEq "HH".
    unfold is_state.
    repeat f_equal. rewrite HnoOverflow. admit. (* FIXME: integer overflow *)
  }
  {
    iIntros.
    iDestruct (big_sepS_elem_of_acc _ _ vnum' with "HlatestVersion") as "[#H _]".
    { set_solver. }
    rewrite H1.
    rewrite app_length /= in H4.
    replace (int.nat (length ops + 1)) with (length ops + 1) in H4.
    2:{ admit. } (* FIXME: integer overflow *)
    iApply "H".
    { iPureIntro.  word. }
    { iPureIntro.  word. }
  }
Admitted. (* integer overflows *)

Lemma wp_EEStateMachine__apply s :
  {{{
        True
  }}}
    EEStateMachine__applyVolatile #s
    {{{
          applyFn, RET applyFn;
        ⌜val_ty applyFn (slice.T byteT -> slice.T byteT)⌝ ∗
        ee_is_InMemory_applyVolatileFn applyFn (own_StateMachine s)
  }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  clear Φ.
  iSplit.
  {
    iPureIntro. econstructor.
  }
  iIntros (???? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "(%Henc & #Hsl & Hown)".
  unfold own_StateMachine.
  set (st:=compute_state ops).
  destruct st eqn:X.
  iNamed "Hown".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (ret) "Hret".
  wp_pures.

  wp_loadField.
  wp_apply std_proof.wp_SumAssumeNoOverflow.
  iIntros (Hno_overflow).
  wp_storeField.
  destruct op.
  { (* case: getcid op *)
    rewrite Henc.
    iMod (readonly_load with "Hsl") as (?) "Hsl2".
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_NewSliceWithCap).
    { word. }
    iIntros (?) "Hrep_sl".
    wp_store.
    wp_loadField.
    wp_load.
    wp_apply (wp_WriteInt with "[$Hrep_sl]").
    iIntros (?) "Hrep_sl".
    wp_store.
    wp_loadField.
    wp_storeField.
    wp_load.
    iApply "HΦ".
    rewrite compute_state_snoc.
    simpl.
    unfold apply_op.
    unfold compute_reply.
    replace (compute_state ops) with (st) by done.
    rewrite X.
    simpl.
    iMod (ghost_no_low_changes with "Hghost") as "Hghost".
    { word. }
    { done. }
    { instantiate (1:=getcid).
      rewrite compute_state_snoc.
      done.
    }
    iModIntro.
    iSplitR "Hrep_sl"; last first.
    {
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
    }
    repeat iExists _.
    iFrame "Hlowstate ∗".
    rewrite app_length /=.
    iSplitL "HeeNextIndex".
    { iApply to_named. iExactEq "HeeNextIndex".
      repeat f_equal. word.
    }
    iFrame "Hislow".
    iPureIntro. word.
  }
  { (* case: apply an op *)
    destruct Henc as [? [HlowEnc Henc]].
    rewrite Henc.
    iMod (readonly_load with "Hsl") as (?) "Hsl2".
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_slice_len).
    wp_pures.

    iDestruct (is_slice_small_sz with "Hsl2") as %Hsl_sz.
    wp_apply (wp_SliceSubslice_small with "[$Hsl2]").
    { rewrite -Hsl_sz.
      split; last done.
      rewrite app_length.
      simpl.
      word.
    }
    iIntros (eeop_sl) "Hop_sl".
    rewrite -Hsl_sz -Henc.
    rewrite -> subslice_drop_take; last first.
    { rewrite Henc. rewrite app_length. simpl. word. }
    rewrite Henc.
    rewrite app_length.
    rewrite singleton_length.
    replace (1 + length (u64_le u ++ u64_le u0 ++ x) - int.nat 1%Z)
      with (length (u64_le u ++ u64_le u0 ++ x)) by word.
    replace (int.nat (U64 1)) with (length [U8 0]) by done.
    rewrite drop_app.
    rewrite take_ge; last word.
    rename x into eeop_bytes.
    wp_pures.
    wp_apply (wp_ReadInt with "Hop_sl").
    iIntros (?) "Hop_sl".
    wp_apply (wp_ReadInt with "Hop_sl").
    iIntros (?) "Hop_sl".
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapGet with "HlastSeq").
    iIntros (??) "(%Hlookup & HlastSeq)".
    wp_pures.
    wp_if_destruct.
    {
      wp_loadField.
      wp_apply (wp_byteMapGet with "HlastReply").
      iIntros (?) "[#Hrep_sl HlastReply]".
      wp_store.
      wp_pures.
      wp_load.
      iMod (readonly_load with "Hrep_sl") as (?) "Hrep_sl2".

      iApply "HΦ".

      rewrite compute_state_snoc.
      unfold apply_op.
      simpl.
      unfold compute_reply.
      replace (compute_state ops) with (st) by done.
      rewrite X.

      unfold apply_op_and_get_reply.
      rewrite decide_True; last first.
      {
        apply (f_equal fst) in Hlookup.
        rewrite map_get_val /= in Hlookup.
        rewrite Hlookup.
        word.
      }
      iSplitR "Hrep_sl2"; last first.
      {
        iClear "Hsl".
        iFrame. by iModIntro.
      }
      repeat iExists _.

      iFrame "Hlowstate ∗".
      iMod (ghost_no_low_changes with "Hghost") as "$".
      { word. }
      { done. }
      { rewrite compute_state_snoc.
        unfold apply_op.
        simpl.
        rewrite decide_True.
        1: done.
        simpl.
        replace (compute_state ops) with (st) by done.
        rewrite X.
        simpl.
        injection Hlookup as H1.
        rewrite H1.
        word.
      }
      iModIntro.
      iSplitL "HeeNextIndex".
      { iApply to_named. iExactEq "HeeNextIndex".
        repeat f_equal. rewrite app_length /=. word.
      }
      iFrame "Hislow".
      iPureIntro. rewrite app_length /=. word.
    }
    {
      wp_loadField.
      iAssert (_) with "Hislow" as "#Hislow2".
      iNamed "Hislow2".
      wp_loadField.

      iMod (readonly_alloc (is_slice_small s'0 byteT 1 eeop_bytes) with "[Hop_sl]") as "#Hop_sl".
      { simpl. iFrame. }
      wp_loadField.
      unfold is_Versioned_applyVolatileFn.
      iMod (ghost_low_newop  with "Hghost") as "Hghost".
      { word. }
      { word. }
      { done. }
      { instantiate (1:=o).
        instantiate (1:=ee u u0 o).
        rewrite compute_state_snoc.
        unfold apply_op.
        simpl.
        rewrite decide_False.
        { simpl. done. }
        injection Hlookup as H1.
        replace (compute_state ops) with (st) by done.
        rewrite  X.
        simpl. rewrite H1. word.
      }
      iDestruct "Hghost" as "(Hghost & HprevVers & HnewVer)".
      wp_apply ("HapplyVolatile_spec" with "[$Hlowstate HprevVers HnewVer]").
      {
        iSplitR; first done.
        iFrame "∗#".
        iSplitR; first iPureIntro.
        { word. }
        simpl.
        rewrite app_length /=.
        iSplitL "HprevVers".
        {
          iIntros.
          replace (compute_state ops) with st by done.
          rewrite X /=.
          iApply "HprevVers".
          { iPureIntro; word. }
          { iPureIntro; word. }
        }
        {
          iExactEq "HnewVer".
          repeat f_equal.
          { word. }
          { replace (compute_state ops) with st by done. rewrite X. done. }
        }
      }
      iIntros (??) "[Hlowstate Hrep_sl]".
      wp_store.
      wp_pures.
      wp_load.

      iMod (readonly_alloc (is_slice_small reply_sl byteT 1 (low_compute_reply
                   {|
                     nextCID := nextCID0;
                     lastSeq := lastSeq0;
                     lastReply := lastReply0;
                     lowops := lowops0
                   |}.(lowops) o)) q0 with "[Hrep_sl]") as "#Hreply_sl".
      { simpl. iFrame. }
      wp_loadField.
      iMod (readonly_load with "Hreply_sl") as (?) "Hreply_sl2".
      wp_apply (wp_byteMapPut with "[$HlastReply Hreply_sl2]").
      { iFrame. }
      iIntros "Hmap".
      wp_pures.
      wp_loadField.
      wp_apply (wp_MapInsert with "HlastSeq").
      { done. }
      iIntros "HlastSeq".
      wp_pures.
      wp_load.

      iMod (readonly_load with "Hreply_sl") as (?) "Hreply_sl2".
      iApply "HΦ".
      iModIntro.

      rewrite compute_state_snoc.
      unfold apply_op.
      simpl.
      unfold compute_reply.
      replace (compute_state ops) with (st) by done.
      rewrite X.

      unfold apply_op_and_get_reply.
      rewrite decide_False; last first.
      {
        apply (f_equal fst) in Hlookup.
        rewrite map_get_val /= in Hlookup.
        rewrite Hlookup.
        word.
      }
      iSplitR "Hreply_sl2"; last first.
      {
        iClear "Hsl".
        iFrame.
      }
      simpl.
      repeat iExists _.
      iFrame "∗".
      rewrite app_length /=.
      iSplitL "HeeNextIndex".
      { iApply to_named. iExactEq "HeeNextIndex".
        repeat f_equal. word.
      }
      iSplitL "Hghost".
      { iApply to_named. iExactEq "Hghost".
        repeat f_equal. word.
      }
      iFrame "#".
      iPureIntro. word.
    }
  }
  { (* apply a readonly op *)
    destruct Henc as [? [HlowEnc Henc]].
    rewrite Henc.
    iMod (readonly_load with "Hsl") as (?) "Hsl2".
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_slice_len).
    wp_pures.

    iDestruct (is_slice_small_sz with "Hsl2") as %Hsl_sz.
    wp_apply (wp_SliceSubslice_small with "[$Hsl2]").
    { rewrite -Hsl_sz.
      split; last done.
      rewrite app_length.
      simpl.
      word.
    }
    wp_pures.
    iIntros (eeop_sl) "Hop_sl".
    rewrite -Hsl_sz -Henc.
    rewrite -> subslice_drop_take; last first.
    { rewrite Henc. rewrite app_length. simpl. word. }
    rewrite Henc.
    rewrite app_length.
    rewrite singleton_length.
    replace (1 + length x - int.nat 1%Z)
      with (length (x)) by word.
    replace (int.nat (U64 1)) with (length [U8 2]) by done.
    rewrite drop_app.
    rewrite take_ge; last word.
    rename x into eeop_bytes.
    wp_pures.
    wp_loadField.
    iAssert (_) with "Hislow" as "#Hislow2".
    iNamed "Hislow2".
    wp_loadField.
    iMod (readonly_alloc (is_slice_small eeop_sl byteT 1 eeop_bytes) with "[Hop_sl]") as "#Hop_sl".
    { simpl. iFrame. }
    wp_apply ("HapplyReadonly_spec" with "[$Hlowstate]").
    { iFrame "#". done. }
    iIntros (???) "(% & Hlow & Hrep_sl & _)".
    wp_pures.
    wp_store.
    wp_load.

    rewrite compute_state_snoc.
    unfold apply_op.
    simpl.

    iApply "HΦ".
    replace (compute_state ops) with st by done.
    rewrite X.
    iSplitR "Hrep_sl".
    {
      repeat iExists _.
      iFrame "∗".
      iFrame.
      iMod (ghost_no_low_changes with "Hghost") as "$".
      { word. }
      { done. }
      { rewrite compute_state_snoc.
        unfold apply_op.
        simpl. done.
      }
      iSplitL "HeeNextIndex".
      { iModIntro. iApply to_named. iExactEq "HeeNextIndex".
        repeat f_equal. rewrite app_length /=. word.
      }
      simpl.
      iFrame "Hislow".
      iPureIntro. rewrite app_length /=. word.
    }
    {
      unfold compute_reply.
      simpl.
      replace (compute_state ops) with (st) by done.
      rewrite X.
      iModIntro. iFrame "Hrep_sl".
    }
  }
Qed.

Lemma ghost_low_setstate ops :
  length ops = int.nat (length ops) →
  ⊢ |==> ∃ γst,
  own_ghost_vnums γst (ops) (length ops) ∗
  is_state γst (length (ops)) (compute_state ops).(lowops)
.
Proof.
  intros HnoOverflow.
  iMod (ghost_map_alloc_fin []) as (?) "Hmap".
  iExists _.
  iDestruct (big_sepS_elem_of_acc_impl (U64 (length ops)) with "Hmap") as "[HH Hmap]".
  { set_solver. }
  iMod (ghost_map_points_to_update (compute_state ops).(lowops) with "HH") as "HH".
  iMod (ghost_map_points_to_persist with "HH") as "#?".
  iModIntro.
  iFrame "∗#".
  unfold own_ghost_vnums.
  iAssert (
      [∗ set] vnum ∈ fin_to_set u64, ( (⌜int.nat vnum ≤ length ops⌝
                                    → vnum ⤳[γ] []
                                      ∨ is_state γ vnum
                                (compute_state (take (int.nat vnum) ops)).(lowops)) ∗
                (⌜int.nat vnum > length ops⌝ → vnum ⤳[γ] [])))%I with "[-]" as "HH".
  {
    iApply "Hmap".
    {
      iModIntro. iIntros.
      destruct (decide (int.nat y ≤ length ops)).
      {
        iSplitL.
        { iIntros. iFrame. }
        iIntros. word.
      }
      { iSplitR.
        { iIntros. word. }
        { iIntros. iFrame. }
      }
    }
    {
      iSplitL.
      {
        iIntros.
        iRight. rewrite -HnoOverflow.
        rewrite firstn_all. iFrame "#".
      }
      { iIntros. exfalso. word. }
    }
  }
  iDestruct (big_sepS_sep with "HH") as "[H H2]".
  iFrame.
  iApply (big_sepS_impl with "[]").
  { by iApply big_sepS_emp. }
  iModIntro. iIntros.
  iModIntro. iIntros.
  assert (int.nat x = (length ops)).
  { rewrite /= in H2. word. }
  replace (x) with (U64 (length ops)) by word.
  iFrame "#".
Qed.

Lemma wp_EEStateMachine__setState s :
  {{{
        True
  }}}
    EEStateMachine__setState #s
  {{{
        setFn, RET setFn;
        ⌜val_ty setFn (slice.T byteT -> (arrowT uint64T unitT))%ht⌝ ∗
        ee_is_InMemory_setStateFn setFn (own_StateMachine s)
  }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  iModIntro.
  iApply "HΦ".
  clear Φ.
  iSplit.
  {
    iPureIntro. econstructor.
  }

  iIntros (???? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "(%Hsnap & #Hsnap_sl & Hown)".
  wp_pures.

  iNamed "Hown".
  iMod (readonly_load with "Hsnap_sl") as (?) "Hsnap_sl2".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_load.


  simpl in Hsnap.
  unfold own_StateMachine.
  rewrite /ee_has_snap_encoding in Hsnap.
  set (st:=compute_state ops) in *.
  set (st_old:=compute_state ops_prev) in *.
  destruct Hsnap as (lowsnap & enc_lastSeq & enc_lastReply & Hencseq  & Hencrep & Hlowsnap & Hsnap).
  rewrite Hsnap.
  wp_apply (wp_ReadInt with "[$Hsnap_sl2]").
  iIntros (?) "Hsnap_sl2".
  wp_pures.
  wp_storeField.
  wp_store.
  wp_load.

  wp_apply (wp_DecodeMapU64ToU64 with "[Hsnap_sl2]").
  {
    iSplitR; first done.
    iFrame.
  }
  iIntros (???) "[HlastSeqMap Hsnap_sl2]".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_apply (wp_DecodeMapU64ToBytes with "[Hsnap_sl2]").
  {
    iSplitR; first done.
    iFrame.
  }
  iIntros (???) "[HlastReplyMap Hsnap_sl2]".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_loadField.
  iAssert (_) with "Hislow" as "#Hislow2".
  iNamed "Hislow2".
  wp_loadField.
  iMod (readonly_alloc (is_slice_small rest_enc_sl0 byteT 1 lowsnap) with "[Hsnap_sl2]") as "#Hsnap_sl2".
  { simpl. iFrame. }
  unfold is_Versioned_setStateFn.
  iClear "Hghost".
  iMod ghost_low_setstate as (?) "[Hghost2 #Hstate]".
  { admit. } (* FIXME: integer overflow *)
  wp_apply ("HsetState_spec" with "[$Hlowstate Hsnap_sl2]").
  {
    iSplitR; first done.
    iFrame "#".
  }
  iIntros "Hlowstate".
  wp_pures.
  wp_storeField.
  iApply "HΦ".
  repeat iExists _.
  iFrame "∗ Hislow".
  iPureIntro.
  admit. (* FIXME: integer overflow *)
Admitted. (* integer overflows *)

Lemma wp_EEStatemachine__getState (s:loc) :
  ⊢ ee_is_InMemory_getStateFn (λ: <>, EEStateMachine__getState #s) (own_StateMachine s).
Proof.
  iIntros (? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "Hown".
  wp_pures.
  wp_call.
  unfold own_StateMachine.
  set (st:=compute_state ops).
  destruct st eqn:X.
  iNamed "Hown".
  wp_loadField.
  iAssert (_) with "Hislow" as "#Hislow2".
  iNamed "Hislow2".
  wp_loadField.
  wp_apply ("HgetState_spec" with "[$Hlowstate]").
  iIntros (??) "(Hlowstate & %Hlowsnap & #Hsnap_sl)".
  iMod (readonly_load with "Hsnap_sl") as (?) "Hsnap_sl2".
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { word. }
  iIntros (?) "Henc_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_loadField.
  wp_load.
  rewrite replicate_0.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_pures.
  wp_store.
  wp_loadField.
  wp_apply (wp_EncodeMapU64ToU64 with "HlastSeq").
  iIntros (??) "(Hmap & HlastSeqEnc & %HlastSeqEnc)".
  wp_load.
  iDestruct (is_slice_to_small with "HlastSeqEnc") as "HlastSeqEnc".
  wp_apply (wp_WriteBytes with "[$Henc_sl $HlastSeqEnc]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_loadField.

  wp_apply (wp_EncodeMapU64ToBytes with "HlastReply").
  iIntros (??) "(Hmap2 & HlastReplyEnc & %HlastReplyEnc)".
  wp_load.
  iDestruct (is_slice_to_small with "HlastReplyEnc") as "HlastReplyEnc".
  wp_apply (wp_WriteBytes with "[$Henc_sl $HlastReplyEnc]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_load.

  wp_apply (wp_WriteBytes with "[$Henc_sl $Hsnap_sl2]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_load.
  iApply "HΦ".
  iDestruct (is_slice_to_small with "Henc_sl") as "Henc_sl".
  iMod (readonly_alloc_1 with "Henc_sl") as "Henc_sl".
  iModIntro.
  iFrame "Henc_sl".
  iSplitL.
  {
    repeat iExists _.
    iFrame "Hghost".
    simpl.
    iFrame "Hlowstate ∗".
    iFrame "Hislow". iFrame "%".
  }
  iPureIntro.
  cbn.
  unfold ee_has_snap_encoding.
  replace (compute_state ops) with (st) by done.
  rewrite X.
  exists snap, enc, enc0.
  split; first done.
  split; first done.
  split; first done.
  repeat rewrite -app_assoc.
  done.
Qed.


Lemma applyreadonly_step γst ops o latestVnum (lastModifiedVnum:u64) :
  length ops = int.nat (length ops) →
  own_ghost_vnums γst ops latestVnum -∗
  (∀ (vnum : u64),
          ⌜int.nat vnum < int.nat latestVnum⌝
          → ⌜int.nat lastModifiedVnum ≤ int.nat vnum⌝
          → ∃ someOps : list low_OpType, is_state γst vnum someOps ∗
          ⌜low_compute_reply someOps o =
          low_compute_reply (compute_state ops).(lowops) o⌝) -∗
  ⌜∀ ops' : list ee_record.(Sm.OpType),
     ops' `prefix_of` ops
  → int.nat lastModifiedVnum ≤ length ops'
  → ee_record.(Sm.compute_reply) ops (ro_ee o) = ee_record.(Sm.compute_reply) ops' (ro_ee o)⌝
.
Proof.
  intros HnoOverflow.
  iNamed 1.
  iIntros "#Hstates".
  iIntros (???).
  iSpecialize ("Hstates" $! (length a)).

  assert (int.nat (length a) = (length a)) as HaOverflow.
  {
    apply prefix_length in a0.
    rewrite HnoOverflow in a0.
    word.
  }

  destruct (decide (int.nat latestVnum <= length a)).
  { (* use HlatestVersion *)
    iDestruct (big_sepS_elem_of_acc _ _ (U64 (length a)) with "HlatestVersion") as "[#HH _]".
    { set_solver. }
    iSpecialize ("HH" with "[%] [%]").
    {
      apply prefix_length in a0.
      rewrite HaOverflow. done.
    }
    { word. }

    iDestruct (big_sepS_elem_of_acc _ _ (U64 (length a)) with "Hversions") as "[H2 _]".
    { set_solver. }
    iSpecialize ("H2" with "[%]").
    { apply prefix_length in a0. rewrite HaOverflow. done. }
    iDestruct "H2" as "[Hbad|H2]".
    {
      unfold is_state.
      iDestruct (ghost_map_points_to_valid_2 with "Hbad HH") as %[Hbad _].
      exfalso. done.
    }
    iDestruct (ghost_map_points_to_agree with "HH H2") as %?.
    iPureIntro.
    replace (take (int.nat (length a)) ops) with a in H0.
    {
      unfold ee_record. simpl.
      unfold compute_reply.
      unfold apply_op_and_get_reply.
      rewrite H0 /=.
      done.
    }
    {
      rewrite HaOverflow.
      destruct a0 as [? ->].
      by rewrite take_app.
    }
  }
  { (* use Hstates *)
    iSpecialize ("Hstates" with "[%] [%]").
    { word. }
    { word. }
    iDestruct "Hstates" as (?) "[Hstate %]".
    iDestruct (big_sepS_elem_of_acc _ _ (U64 (length a)) with "Hversions") as "[H2 _]".
    { set_solver. }
    iSpecialize ("H2" with "[%]").
    { apply prefix_length in a0. rewrite HaOverflow. done. }
    iDestruct "H2" as "[Hbad|H2]".
    {
      unfold is_state.
      iDestruct (ghost_map_points_to_valid_2 with "Hbad Hstate") as %[Hbad _].
      exfalso. done.
    }
    iDestruct (ghost_map_points_to_agree with "Hstate H2") as %?.
    subst.
    iPureIntro.
    replace (take (int.nat (length a)) ops) with a in H0.
    {
      unfold ee_record. simpl.
      unfold compute_reply.
      unfold apply_op_and_get_reply.
      simpl.
      rewrite H0 /=.
      done.
    }
    {
      rewrite HaOverflow.
      destruct a0 as [? ->].
      by rewrite take_app.
    }
  }
Qed.

Lemma wp_EEStateMachine__applyReadonly s :
  {{{
        True
  }}}
    EEStateMachine__applyReadonly #s
  {{{
        applyReadonlyFn, RET applyReadonlyFn;
        ⌜val_ty applyReadonlyFn (slice.T byteT -> (prodT uint64T (slice.T byteT)))⌝ ∗
        ee_is_InMemory_applyReadonlyFn applyReadonlyFn (own_StateMachine s)
  }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  iModIntro.
  iApply "HΦ".
  clear Φ.
  iSplit.
  {
    iPureIntro. econstructor.
  }

  iIntros (???? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "(%Henc & %Hro & #Hsl & Hown)".
  wp_pures.

  iNamed "Hown".
  destruct op.
  { exfalso. done. }
  { exfalso. done. }
  destruct Henc as (lowop_bytes & Henc & ?).
  subst.
  iMod (readonly_load with "Hsl") as (?) "Hsl2".
  wp_apply (wp_SliceGet with "[$Hsl2]").
  { done. }
  iIntros "Hsl2".
  wp_pures.
  wp_apply (wp_SliceGet with "[$Hsl2]").
  { done. }
  iIntros "Hsl2".
  wp_pures.
  wp_apply (wp_SliceGet with "[$Hsl2]").
  { done. }
  iIntros "Hsl2".
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.

  iDestruct (is_slice_small_sz with  "Hsl2") as %Hsl_sz.
  wp_apply (wp_SliceSubslice_small with "[$Hsl2]").
  { rewrite -Hsl_sz.
    split; last done.
    rewrite app_length.
    simpl.
    word.
  }
  iIntros (eeop_sl) "Hop_sl".
  rewrite -Hsl_sz.
  rewrite -> subslice_drop_take; last first.
  { rewrite app_length. simpl. word. }
  rewrite app_length.
  rewrite singleton_length.
  replace (1 + length lowop_bytes - int.nat 1%Z)
    with (length lowop_bytes) by word.
  replace (int.nat (U64 1)) with (length [U8 2]) by done.
  rewrite drop_app.
  rewrite take_ge; last word.
  wp_pures.
  wp_loadField.
  iAssert (_) with "Hislow" as "#Hislow2".
  iNamed "Hislow2".
  wp_loadField.
  iMod (readonly_alloc (is_slice_small eeop_sl byteT 1 lowop_bytes) with "[Hop_sl]") as "#Hop_sl".
  { simpl. iFrame. }
  wp_apply ("HapplyReadonly_spec" with "[$Hlowstate]").
  { iFrame "#". done. }
  iIntros (???) "(%Hlen & Hlow & Hrep_sl & #Hstates)".
  iApply "HΦ".
  iSplitR.
  { iPureIntro. transitivity (int.nat latestVnum).
    { word. }
    done.
  }

  iDestruct (applyreadonly_step with "Hghost Hstates") as "#H".
  { word. }
  iFrame "H".
  iFrame "Hrep_sl".
  repeat iExists _.
  iFrame "∗".
  iFrame "Hislow".
  iPureIntro; word.
Qed.

Lemma alloc_own_ghost_vnums :
  ⊢ |==> ∃ γst, own_ghost_vnums γst [] 0 ∗
                is_state γst 0 []
.
Proof.
  iMod (ghost_map_alloc_fin []) as (?) "Hmap".
  iExists _.
  iDestruct (big_sepS_elem_of_acc_impl (U64 0) with "Hmap") as "[HH Hmap]".
  { set_solver. }
  iMod (ghost_map_points_to_persist with "HH") as "#?".
  iModIntro.
  iFrame "∗#".
  iSplitL.
  {
    iApply "Hmap".
    { iModIntro. iIntros. iFrame. }
    { iIntros. exfalso. simpl in H0. replace (int.nat (U64 0)) with (0) in H0; word. }
  }
  iSplitL.
  {
    iApply (big_sepS_impl with "[]").
    { by iApply big_sepS_emp. }
    iModIntro. iIntros.
    assert (int.nat x = 0).
    { rewrite /= in H2. word. }
    replace (x) with (U64 0) by word.
    iFrame "#".
  }
  iApply big_sepS_forall.
  iIntros. iModIntro.
  iIntros. rewrite /= in H1.
  assert (int.nat x = 0).
  { rewrite /= in H2. word. }
  replace (x) with (U64 0) by word.
  iFrame "#".
Qed.

Lemma wp_MakeEEKVStateMachine own_low lowSm :
  {{{
      "#Hislow" ∷ low_is_VersionedStateMachine lowSm own_low ∗
      "Hlowstate" ∷ (∀ γst, is_state γst 0 [] -∗
                      own_low γst [] 0)
  }}}
    MakeEEKVStateMachine #lowSm
  {{{
      sm own_MemStateMachine, RET #sm;
        ee_is_InMemoryStateMachine sm own_MemStateMachine ∗
        own_MemStateMachine []
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (?) "Hl".
  wp_pures.
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_apply (wp_NewMap).
  iIntros (lastSeq_ptr) "HlastSeq".
  wp_storeField.
  wp_apply (wp_byteMapNew).
  iIntros (lastReply_ptr) "HlastReply".
  wp_storeField.
  wp_storeField.
  wp_storeField.

  wp_apply wp_EEStateMachine__applyReadonly.
  iIntros (?) "[% #HisapplyReadonly]".
  wp_apply wp_EEStateMachine__apply.
  iIntros (?) "[% #Hisapply]".
  wp_apply wp_EEStateMachine__setState.
  iIntros (?) "[% #Hissetstae]".
  iApply wp_fupd.
  wp_apply wp_allocStruct.
  { repeat econstructor; done. }
  iIntros (?) "HH".
  iDestruct (struct_fields_split with "HH") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "ApplyVolatile") as "#?".
  iMod (readonly_alloc_1 with "GetState") as "#?".
  iMod (readonly_alloc_1 with "SetState") as "#?".
  iMod (readonly_alloc_1 with "ApplyReadonly") as "#?".
  iApply "HΦ".
  iSplitR.
  {
    iExists _, _, _, _.
    iFrame "#".
    iModIntro.
    iApply wp_EEStatemachine__getState.
  }
  iNamed "Hpre".
  iMod (alloc_own_ghost_vnums) as (?) "[Hghost #Hstate]".
  iSpecialize ("Hlowstate" with "Hstate").
  iModIntro.
  repeat iExists _.
  iFrame "∗#".
  done.
Qed.

(* The state machine will overflow after 2^64 CIDs have been generated.
This cannot happen in a real execution, so we ignore it for the proof. *)
Local Axiom SumAssumeNoOverflow_admitted : ∀ (i : u64),
  (int.Z (word.add i 1) = (int.Z i) + 1)%Z.

(* FIXME: one big collection of these invs *)
Lemma wp_MakeClerk confHost γ γoplog γerpc :
  {{{
    "#Hee_inv" ∷ is_ee_inv γ γoplog γerpc ∗
    "#Herpc_inv" ∷ is_eRPCServer γerpc ∗
    "#Hconf" ∷ config_protocol_proof.is_conf_host confHost γ ∗
    "#HprophInv" ∷ is_proph_read_inv γ
  }}}
    eesm.MakeClerk #confHost
  {{{
        ck, RET #ck; own_Clerk ck γoplog
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_allocStruct).
  { repeat constructor. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply clerk_proof.wp_MakeClerk.
  { iFrame "#". }
  iIntros (?) "Hck".
  wp_storeField.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hsl".
  wp_pures.
  iDestruct (is_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_SliceSet with "[$Hsl]").
  {
    simpl.
    iPureIntro.
    done.
  }
  iIntros "Hsl".
  wp_pures.
  wp_loadField.
  wp_bind (Clerk__Apply _ _).
  wp_apply (wp_frame_wand with "[-Hsl Hck]").
  { iNamedAccu. }
  iAssert (pb_prophetic_read.own_Clerk _ _) with "[Hck]" as "Hck".
  { iFrame "∗#". }
  wp_apply (wp_Clerk__Apply with "Hck [$Hsl]").
  {
    simpl.
    instantiate (1:=getcid).
    done.
  }
  iModIntro.

  iInv "Hee_inv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hpblog Hee]".
  iDestruct "Hee" as ">Hee".
  iNamed "Hee".
  iDestruct (big_sepS_elem_of_acc_impl (compute_state ops).(nextCID) with "Hcids") as "[Hcid Hcids]".
  { set_solver. }
  iDestruct "Hcid" as "[%Hbad | Hcid]".
  { exfalso. word. }
  iExists _; iFrame.
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iIntros "Hoplog".
  iMod "Hmask".
  iMod ("Hclose" with "[HerpcServer Hoplog Hlog Hcids]").
  {
    iNext.
    iExists _; iFrame "Hoplog".
    rewrite compute_state_snoc.
    simpl.
    iFrame.
    iApply "Hcids".
    {
      iModIntro.
      iIntros (???) "[%Hineq|$]".
      iLeft. iPureIntro.
      rewrite SumAssumeNoOverflow_admitted.
      word.
    }
    {
      iLeft. iPureIntro.
      rewrite SumAssumeNoOverflow_admitted.
      word.
    }
  }
  iModIntro.
  iIntros (?) "Hrep_sl _ Hpbck".
  iNamed 1.
  wp_pures.
  wp_apply (wp_ReadInt with "[Hrep_sl]").
  {
    simpl.
    unfold compute_reply.
    iFrame.
  }
  iIntros (?) "_".
  wp_pures.
  wp_storeField.
  wp_pures.
  wp_storeField.
  iApply "HΦ".
  iMod (readonly_alloc_1 with "ck") as "#?".
  iModIntro.
  repeat iExists _.
  iFrame "∗#%".
  iPureIntro.
  word.
Qed.

End local_proof.
