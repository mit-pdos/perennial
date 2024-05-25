From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.vrsm.storage Require Import proof.
From Perennial.program_proof.vrsm Require Import replica.definitions replica.apply_proof clerk.clerk_proof.
From Perennial.program_proof.grove_shared Require Import erpc_lib.
From Perennial.program_proof Require Import map_marshal_proof.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial Require Import exactlyonce.vsm log.
From Perennial.algebra Require Import map.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Goose.github_com.mit_pdos.gokv.vrsm.apps Require Import exactlyonce.

Section global_proof.

Context `{low_record:Sm.t}.

Notation low_OpType := (@Sm.OpType low_record).
Notation low_has_op_encoding := (@Sm.has_op_encoding low_record).
Notation low_has_snap_encoding := (@Sm.has_snap_encoding low_record).
Notation low_compute_reply := (@Sm.compute_reply low_record).
Notation low_is_readonly_op := (@Sm.is_readonly_op low_record).
Instance low_op_eqdec : EqDecision (low_OpType).
Proof. apply (@Sm.OpType_EqDecision low_record). Qed.

Inductive EOp :=
  | getcid : EOp
  | eop : u64 → u64 -> low_OpType → EOp
  | ro_eop : low_OpType → EOp
.

Record EState := mkEState
{
  nextCID : u64;
  lastSeq : gmap u64 u64 ;
  lastReply : gmap u64 (list u8);
  lowops : list low_OpType
}.

Global Instance etaEState : Settable _ :=
  settable! (mkEState) <nextCID ; lastSeq ; lastReply ; lowops >.

Definition apply_op_and_get_reply (state:EState) (op:EOp) : EState * list u8 :=
    match op with
    | getcid => (state <| nextCID := (word.add state.(nextCID) 1) |>, u64_le state.(nextCID))
    | eop cid seq op =>
        if decide (uint.nat seq <= uint.nat (default (W64 0) (state.(lastSeq) !! cid))) then
          (state, default [] (state.(lastReply) !! cid))
        else
          let rep:=(low_compute_reply state.(lowops) op) in
          (state <| lastSeq := <[cid:=seq]> state.(lastSeq) |>
                <| lastReply := <[cid:=rep]> state.(lastReply) |>
                <| lowops := (state.(lowops) ++ [op]) |>, rep)
    | ro_eop op => (state, (low_compute_reply state.(lowops) op))
    end
.

Definition apply_op state op :=
  (apply_op_and_get_reply state op).1
.

Definition init_state := mkEState 0 ∅ ∅ [].

Definition compute_state ops : EState :=
  foldl apply_op init_state ops.

Definition compute_reply ops op : (list u8) :=
  (apply_op_and_get_reply (compute_state ops) op).2
.

Definition esm_has_encoding op_bytes op :=
  match op with
  | getcid => op_bytes = [W8 1]
  | eop cid seq lowop =>
      ∃ lowop_enc, low_has_op_encoding lowop_enc lowop ∧
      op_bytes = [W8 0] ++ u64_le cid ++ u64_le seq ++ (lowop_enc)
  | ro_eop lowop =>
      ∃ lowop_enc,
  low_has_op_encoding lowop_enc lowop ∧
  low_is_readonly_op lowop ∧
  op_bytes = [W8 2] ++ (lowop_enc)
  end
.

Definition esm_has_snap_encoding snap_bytes ops :=
  let st := (compute_state ops) in
  ∃ low_snap_bytes enc_lastSeq enc_lastReply,
  has_u64_map_encoding enc_lastSeq st.(lastSeq) ∧
  has_byte_map_encoding enc_lastReply st.(lastReply) ∧
  low_has_snap_encoding low_snap_bytes st.(lowops) ∧
  snap_bytes = (u64_le st.(nextCID)) ++ (enc_lastSeq) ++ enc_lastReply ++ low_snap_bytes
.

Definition esm_is_readonly_op op :=
  match op with
    | getcid => False
    | eop _ _ _=> False
    | ro_eop lowop => low_is_readonly_op lowop
  end
.

(* TODO: could strengthen this to export the lower-level postcond's *)
Definition esm_apply_postcond ops op :=
  match op with
    | getcid => (uint.Z (word.add (compute_state ops).(nextCID) 1) =
                 (uint.Z (compute_state ops).(nextCID)) + 1)%Z
    | _ => True
  end
.

Instance op_eqdec : EqDecision EOp.
Proof. solve_decision. Qed.

Program Definition
  esm_record:=
  {|
    Sm.OpType := EOp ;
    Sm.has_op_encoding := esm_has_encoding ;
    Sm.has_snap_encoding := esm_has_snap_encoding ;
    Sm.compute_reply :=  compute_reply ;
    Sm.is_readonly_op := esm_is_readonly_op ;
    Sm.apply_postcond := esm_apply_postcond ;
  |}.
Obligation 1.
intros. rewrite /esm_apply_postcond /=.
destruct o; apply _.
Qed.

Context `{!inG Σ (mono_listR (leibnizO low_OpType))}.

Context `{!gooseGlobalGS Σ, !urpcregG Σ, !erpcG Σ (list u8)}.
Definition own_esm st γ γerpc : iProp Σ :=
  "Hlog" ∷ own_log γ st.(lowops) ∗
  "HerpcServer" ∷ eRPCServer_own_ghost γerpc st.(lastSeq) st.(lastReply) ∗
  "Hcids" ∷ ([∗ set] cid ∈ (fin_to_set u64), ⌜uint.Z cid < uint.Z st.(nextCID)⌝%Z ∨
                                              (is_eRPCClient_ghost γerpc cid 1))
.

Definition esmN := nroot .@ "esm".

(* This is the invariant maintained by all the servers for the "centralized"
   ghost state of the system. *)
Context {initconf:list u64}.
Local Instance esmParams : pbParams.t := pbParams.mk initconf (esm_record).
Context `{!pbG (pb_record:=esmParams.(pbParams.pb_record)) Σ}.
Definition is_esm_inv γpb γlog γerpc : iProp Σ :=
  inv esmN (∃ ops,
               own_op_log γpb ops ∗
               own_esm (compute_state ops) γlog γerpc
       )
.

Lemma alloc_esm γpb :
  own_op_log γpb [] ={⊤}=∗
  ∃ γlog γerpc,
  is_esm_inv γpb γlog γerpc ∗
  is_eRPCServer γerpc ∗
  own_log γlog ([]:list low_OpType)
.
Proof.
  iIntros "Hpblog".
  iMod (own_alloc (●ML [])) as (γlog) "[Hlog Hlog2]".
  { apply mono_list_auth_valid. }
  iExists γlog.
  iFrame "Hlog".
  iMod (make_rpc_server) as (γerpc) "(#? & Herpc & Hcids)".
  { set_solver. } iExists γerpc. iFrame "#".
  iMod (inv_alloc with "[-]") as "$"; last done.
  iExists []; iFrame. iNext.
  iApply (big_sepS_impl with "Hcids").
  iModIntro. iIntros. iFrame.
Qed.

End global_proof.

Section local_proof.

Context {low_record:Sm.t}.
Notation low_OpType := (@Sm.OpType low_record).
Notation low_has_op_encoding := (@Sm.has_op_encoding low_record).
Notation low_is_readonly_op := (@Sm.is_readonly_op low_record).
Notation low_compute_reply := (@Sm.compute_reply low_record).
Instance low_op_dec2 : EqDecision low_OpType.
Proof. apply (@Sm.OpType_EqDecision low_record). Qed.

Context `{!heapGS Σ, !urpcregG Σ, !erpcG Σ (list u8)}.

Notation esm_record := (esm_record (low_record:=low_record)).
Notation compute_state := (compute_state (low_record:=low_record)).
Notation EOp := (EOp (low_record:=low_record)).
Notation esm_is_InMemoryStateMachine := (is_InMemoryStateMachine (sm_record:=esm_record)).
Notation low_is_VersionedStateMachine := (is_VersionedStateMachine (sm_record:=low_record)).
Notation own_pb_Clerk := clerk_proof.own_Clerk.
Notation is_esm_inv := (is_esm_inv (low_record:=low_record)).

Context `{!inG Σ (mono_listR (leibnizO low_OpType))}.
Context {initconf:list u64}.
(* FIXME: can this second copy of the instance be avoided? *)
(* Existing Instance esmParams. *)
Local Instance esmParams2 : pbParams.t := esmParams (low_record:=low_record) (initconf:=initconf).

Context `{!pbG (pb_record:=esmParams2.(pbParams.pb_record)) Σ}.
Context `{!vsmG (sm_record:=low_record) Σ}.

Definition own_Clerk ck γoplog : iProp Σ :=
  ∃ (pb_ck:loc) γpb γerpc (cid seqno:u64),
    "Hcid" ∷ ck ↦[exactlyonce.Clerk :: "cid"] #cid ∗
    "Hseq" ∷ ck ↦[exactlyonce.Clerk :: "seq"] #seqno ∗
    "Hown_ck" ∷ own_pb_Clerk pb_ck γpb ∗
    "#Hpb_ck" ∷ readonly (ck ↦[exactlyonce.Clerk :: "ck"] #pb_ck) ∗
    "#Hee_inv" ∷ is_esm_inv γpb γoplog γerpc ∗
    "Herpc" ∷ is_eRPCClient_ghost γerpc cid seqno ∗
    "#Herpc_inv" ∷ is_eRPCServer γerpc ∗
    "%Hseqno_pos" ∷ ⌜ uint.nat seqno > 0 ⌝
.

Lemma compute_state_snoc ops newop :
  compute_state (ops ++ [newop]) = apply_op (compute_state ops) newop.
Proof.
  unfold compute_state. by rewrite foldl_snoc.
Qed.

Lemma wp_Clerk__ApplyExactlyOnce ck γoplog lowop op_sl lowop_bytes Φ:
  low_has_op_encoding lowop_bytes lowop →
  own_Clerk ck γoplog -∗
  own_slice op_sl byteT (DfracOwn 1) lowop_bytes -∗
  (|={⊤∖↑pbN∖↑prophReadN∖↑esmN,∅}=> ∃ oldops, own_log γoplog oldops ∗
    (own_log γoplog (oldops ++ [lowop]) ={∅,⊤∖↑pbN∖↑prophReadN∖↑esmN}=∗
    (∀ reply_sl, own_Clerk ck γoplog -∗ own_slice_small reply_sl byteT (DfracOwn 1) (low_compute_reply oldops lowop)
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
  replace (#(W8 0)) with (_.(to_val) (W8 0)).
  2: { done. }
  iDestruct (own_slice_split with "Henc_sl") as "[Henc_sl Henc_cap]".
  wp_apply (wp_SliceSet with "[Henc_sl]").
  { iFrame. iPureIntro.
    eexists _.
    rewrite lookup_replicate.
    split; first done.
    word.
  }
  iIntros "Henc_sl".
  iDestruct (own_slice_split with "[$Henc_sl $Henc_cap]") as "Henc_sl".
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
  iDestruct (own_slice_to_small with "Hop") as "Hop".
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
            own_slice_small reply_sl byteT (DfracOwn 1) reply -∗
            Φ (slice_val reply_sl))
        %I).
  (* assert that it equals low_compute_reply *)

  iDestruct "Hreq" as (?) "(#Hreq & Htok)".
  iApply wp_fupd.
  iApply (wp_frame_wand with "[Hcid Hseq Herpc Htok Hlc2]").
  { iNamedAccu. }
  simpl.
  iDestruct (own_slice_to_small with "Henc_sl") as "Henc_sl".
  wp_apply (wp_Clerk__Apply with "Hown_ck [$Henc_sl]").
  {
    simpl.
    rewrite -app_assoc.
    rewrite -app_assoc.
    instantiate (1:= eop cid seqno lowop).
    exists lowop_bytes.
    split; done.
  }
  {
    iModIntro.
    iInv "Hee_inv" as "Hi" "Hclose".
    iDestruct "Hi" as (?) "[>Hpblog >Hee]".
    iNamed "Hee".

    destruct (decide (uint.Z (default (W64 0) ((compute_state ops).(lastSeq) !! cid)) < uint.Z seqno)%Z).
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
      iIntros "_ Hpblog".
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
      assert (uint.nat (default (W64 0) ((compute_state ops).(lastSeq) !! cid)) = uint.nat seqno ∨
              uint.nat (default (W64 0) ((compute_state ops).(lastSeq) !! cid)) > uint.nat seqno)
        as [Hok|HStale] by word.
      { (* case: not stale *)
        destruct (_ !! cid) eqn:X2; last first.
        {
          exfalso.
          simpl in Hok.
          replace (uint.nat 0%Z) with (0) in Hok by word.
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
        iIntros "_ Hpblog".
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
        replace (w) with (seqno); last first.
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
          replace (uint.nat 0%Z) with (0) in HStale by word.
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
        iIntros "_ Hpblog".
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

Lemma wp_Clerk__ApplyReadonly ck γoplog lowop op_sl lowop_bytes Φ:
  low_is_readonly_op lowop →
  low_has_op_encoding lowop_bytes lowop →
  own_Clerk ck γoplog -∗
  own_slice op_sl byteT (DfracOwn 1) lowop_bytes -∗
  (|={⊤∖↑pbN∖↑prophReadN∖↑esmN,∅}=> ∃ oldops, own_log γoplog oldops ∗
    (own_log γoplog (oldops) ={∅,⊤∖↑pbN∖↑prophReadN∖↑esmN}=∗
    (∀ reply_sl, own_Clerk ck γoplog -∗ own_slice_small reply_sl byteT (DfracOwn 1) (low_compute_reply oldops lowop)
     -∗ Φ (slice_val reply_sl )))) -∗
  WP Clerk__ApplyReadonly #ck (slice_val op_sl) {{ Φ }}.
Proof.
  intros Hro Henc.
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
  replace (#(W8 2)) with (_.(to_val) (W8 2)).
  2: { done. }
  iDestruct (own_slice_split with "Henc_sl") as "[Henc_sl Henc_cap]".
  wp_apply (wp_SliceSet with "[Henc_sl]").
  { iFrame. iPureIntro.
    eexists _.
    rewrite lookup_replicate.
    split; first done.
    word.
  }
  iIntros "Henc_sl".
  iDestruct (own_slice_split with "[$Henc_sl $Henc_cap]") as "Henc_sl".

  wp_load.
  iDestruct (own_slice_to_small with "Hop") as "Hop".
  wp_apply (wp_WriteBytes with "[$Henc_sl $Hop]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_load.
  wp_loadField.

  iDestruct (own_slice_to_small with "Henc_sl") as "Henc_sl".
  wp_apply (wp_Clerk__ApplyReadonly with "Hown_ck [$Henc_sl]").
  {
    instantiate (1:= ro_eop lowop).
    by rewrite /esm_record /esm_is_readonly_op /=.
  }
  {
    rewrite /esm_record /=.
    eexists _; split; done.
  }

  iInv "Hee_inv" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hpblog Hee]".
  iNamed "Hee".
  iMod "Hupd" as (?) "[Hlog2 Hupd]".
  iDestruct (own_valid_2 with "Hlog Hlog2") as %Hvalid.
  apply mono_list_auth_dfrac_op_valid_L in Hvalid.
  destruct Hvalid as [_ ?]; subst.
  iModIntro. iExists _; iFrame.
  iIntros "Hpblog".
  iMod ("Hupd" with "[$]") as "Hupd".
  iMod ("Hclose" with "[Hpblog HerpcServer Hlog2 Hcids]").
  { iExists _; iFrame. }
  iModIntro.
  iIntros (?) "Hsl Hsl2 Hck".
  iApply ("Hupd" with "[-Hsl]").
  { repeat iExists _; iFrame "∗#%". }
  iFrame.
Qed.

(* Now, the server proof. *)
Definition own_ghost_vnums γst (ops:list EOp) (latestVnum:u64) : iProp Σ :=
  "HfutureVersions" ∷ ([∗ set] vnum ∈ (fin_to_set u64), ⌜uint.nat vnum > length ops⌝ →
                                                       vnum ⤳[γst] []) ∗
  "Hversions" ∷ ([∗ set] vnum ∈ (fin_to_set u64), ⌜uint.nat vnum <= length ops⌝ →
                vnum ⤳[γst] [] ∨ (is_state γst vnum (compute_state (take (uint.nat vnum) ops)).(lowops))
                ) ∗
  "#HlatestVersion" ∷
  ([∗ set] vnum ∈ (fin_to_set u64), □(⌜uint.nat vnum <= length ops⌝ →
                                      ⌜uint.nat latestVnum <= uint.nat vnum⌝ →
                                      (is_state γst vnum (compute_state ops).(lowops))))
.

Definition own_StateMachine (s:loc) (ops:list EOp) : iProp Σ :=
  let st := (compute_state ops) in
      ∃ (lastSeq_ptr lastReply_ptr lowSm:loc) (latestVnum:u64) own_low γst,
  "HnextCID" ∷ s ↦[eStateMachine:: "nextCID"] #st.(nextCID) ∗
  "HlastSeq_ptr" ∷ s ↦[eStateMachine :: "lastSeq"] #lastSeq_ptr ∗
  "HlastReply_ptr" ∷ s ↦[eStateMachine :: "lastReply"] #lastReply_ptr ∗
  "HlastSeq" ∷ own_map lastSeq_ptr (DfracOwn 1) st.(lastSeq) ∗
  "HlastReply" ∷ own_byte_map lastReply_ptr st.(lastReply) ∗

  "HesmNextIndex" ∷ s ↦[eStateMachine :: "esmNextIndex"] #(W64 (length ops)) ∗

  "Hsm" ∷ s ↦[eStateMachine :: "sm"] #lowSm ∗
  "Hghost" ∷ own_ghost_vnums γst ops latestVnum ∗
  "#Hislow" ∷ low_is_VersionedStateMachine lowSm own_low ∗
  "Hlowstate" ∷ own_low γst st.(lowops) latestVnum ∗
  "%Hle" ∷ ⌜uint.nat latestVnum <= length ops⌝ ∗
  "%HnoOverflow" ∷ ⌜length ops = uint.nat (length ops)⌝
.

Notation esm_is_InMemory_applyVolatileFn := (is_InMemory_applyVolatileFn (sm_record:=esm_record)).
Notation esm_is_InMemory_setStateFn := (is_InMemory_setStateFn (sm_record:=esm_record)).
Notation esm_is_InMemory_getStateFn := (is_InMemory_getStateFn (sm_record:=esm_record)).
Notation esm_is_InMemory_applyReadonlyFn := (is_InMemory_applyReadonlyFn (sm_record:=esm_record)).

Lemma u64_plus_1_le_no_overflow (y: u64) (n : nat) :
  n + 1 = uint.nat (word.add n 1) →
  W64 (n + 1)%Z ≠ y →
  uint.nat y ≤ n + 1 →
  uint.nat y ≤ n.
Proof.
  intros ? Hplus_1_neq Hle.
  cut (uint.nat y ≠ n + 1); first by lia.
  intros Heq.
  apply Hplus_1_neq.
  word.
Qed.

Lemma ghost_no_low_changes γst ops latestVnum o l :
  (length ops + 1 = uint.nat (word.add (length ops) 1))%nat →
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
      iApply "H". iPureIntro. rewrite app_length in H1. word. }
    { iModIntro. iIntros. exfalso.
      rewrite app_length /= in H.
      word. }
  }

  iSpecialize ("HH" with "[%]").
  { word. }
  iMod (ghost_map_points_to_update l with "HH") as "HH".
  iMod (ghost_map_points_to_persist with "HH") as "#HH".
  iSplitL "Hversions".
  {
    iDestruct (big_sepS_elem_of_acc_impl (W64 (length ops + 1)) with "Hversions") as "[_ Hversions]".
    { set_solver. }
    iApply "Hversions".
    {
      iModIntro. iIntros (???) "H %".
      rewrite app_length /= in H1.
      assert (uint.nat y <= length ops).
      { apply u64_plus_1_le_no_overflow; auto. }
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
    rewrite app_length /= in H.
    replace (Z.of_nat (length ops) + 1)%Z with (Z.of_nat (length ops + 1)) by
      lia.
    rewrite HnoOverflow.
    rewrite u64_Z_through_nat u64_Z //.
  }
  iModIntro.
  iApply (big_sepS_impl with "HlatestVersion").
  {
    iModIntro. iIntros (??) "#H".
    iModIntro.
    iIntros.
    rewrite app_length /= in H0.
    destruct (decide (x = (word.add (length ops) 1))).
    { subst x. rewrite Heq1 Heq2.
      iFrame "HH". }
    {
      rewrite Heq1 Heq2.
      iApply "H".
      { iPureIntro. apply u64_plus_1_le_no_overflow; auto.
        replace (Z.of_nat (length ops) + 1)%Z with (Z.of_nat (length ops + 1)) by
          lia.
        rewrite HnoOverflow.
        rewrite u64_Z_through_nat u64_Z //.
      }
      { iPureIntro. word. }
    }
  }
Qed.

Instance int_nat_u64_inj: Inj eq eq (fun z : u64 => Z.to_nat (uint.Z z)).
Proof.
  intros u1 u2 Heq.
  apply: int_Z_inj.
  apply Z2Nat.inj; auto using encoding.unsigned_64_nonneg.
Qed.

Lemma ghost_low_newop γst ops latestVnum op lowop l :
  (length ops + 1 = uint.nat (word.add (length ops) 1))%nat →
  uint.nat latestVnum <= length ops →
  (compute_state ops).(lowops) = l →
  (compute_state (ops ++ [op])).(lowops) = l ++ [lowop] →
  own_ghost_vnums γst ops latestVnum ==∗
  own_ghost_vnums γst (ops ++ [op]) (length (ops ++ [op])) ∗
  (∀ (vnum':u64), ⌜uint.nat latestVnum <= uint.nat vnum'⌝ →
        ⌜uint.nat vnum' < uint.nat (length (ops ++ [op]))⌝ → is_state γst vnum' l) ∗
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
        iApply "H". iPureIntro. rewrite app_length in H4. word. }
      { iIntros. exfalso.
        rewrite app_length /= in H2.
        word. }
    }
    iSplitL "Hversions".
    {
      iDestruct (big_sepS_elem_of_acc_impl (W64 (length ops + 1)) with "Hversions") as "[_ Hversions]".
      { set_solver. }
      iApply "Hversions".
      {
        iModIntro. iIntros (???) "H %".
        rewrite app_length /= in H4.
        assert (uint.nat y <= length ops).
        { apply u64_plus_1_le_no_overflow; auto. }
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
        rewrite H1.
        iExactEq "HH".
        unfold is_state.
        repeat f_equal.
        1:{ rewrite app_length /= in H2.
            replace (Z.of_nat (length ops) + 1)%Z with (Z.of_nat (length ops + 1)) by
              lia.
            rewrite HnoOverflow.
            rewrite u64_Z_through_nat u64_Z //.
        }
      }
    }
    iApply (big_sepS_impl with "HlatestVersion").
    {
      iModIntro. iIntros (??) "#H".
      iModIntro.
      iIntros.
      rewrite app_length /= in H4.
      assert (x = (word.add (length ops) 1)).
      { rewrite app_length /= in H3.
        apply int_nat_u64_inj.
        rewrite HnoOverflow in H4.
        rewrite u64_Z_through_nat in H4.
        rewrite u64_Z in H4.
        word.
      }
      subst x. rewrite H0 H1.
      iFrame "HH".
    }
  }
  iSplitL.
  2:{
    rewrite app_length /=.
    iExactEq "HH".
    unfold is_state.
    repeat f_equal. rewrite HnoOverflow.
    rewrite u64_Z_through_nat.
    rewrite u64_Z //.
  }
  {
    iIntros.
    iDestruct (big_sepS_elem_of_acc _ _ vnum' with "HlatestVersion") as "[#H _]".
    { set_solver. }
    rewrite H0.
    rewrite app_length /= in H3.
    replace (uint.nat (length ops + 1)) with (length ops + 1) in H3.
    2:{
      rewrite word.unsigned_add in HnoOverflow.
      rewrite HnoOverflow.
      f_equal.
      symmetry.
      rewrite unsigned_U64.
      rewrite Z2Nat.id; last by lia.
      rewrite encoding.word_wrap_wrap; auto; lia.
    }
    iApply "H".
    { iPureIntro.  word. }
    { iPureIntro.  word. }
  }
Qed.

Lemma wp_eStateMachine__apply s :
  {{{
        True
  }}}
    eStateMachine__applyVolatile #s
  {{{
          applyFn, RET applyFn;
        ⌜val_ty applyFn (slice.T byteT -> slice.T byteT)⌝ ∗
        esm_is_InMemory_applyVolatileFn applyFn (own_StateMachine s)
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
    wp_apply std_proof.wp_SumAssumeNoOverflow.
    iIntros (HnoOverflow2).
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
    iSplitR.
    { iPureIntro. simpl in *. word. }
    iSplitR "Hrep_sl"; last first.
    {
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
    }
    repeat iExists _.
    iFrame "Hlowstate ∗".
    rewrite app_length /=.
    iSplitL "HesmNextIndex".
    { iApply to_named. iExactEq "HesmNextIndex".
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

    iDestruct (own_slice_small_sz with "Hsl2") as %Hsl_sz.
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
    replace (1 + length (u64_le w ++ u64_le w0 ++ x) - uint.nat 1%Z)
      with (length (u64_le w ++ u64_le w0 ++ x)) by word.
    replace (uint.nat (W64 1)) with (length [W8 0]) by done.
    rewrite drop_app_length.
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
      simpl.
      iSplitR; first done.
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
      iSplitL "HesmNextIndex".
      { iApply to_named. iExactEq "HesmNextIndex".
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

      iMod (readonly_alloc (own_slice_small s'0 byteT (DfracOwn 1) eeop_bytes) with "[Hop_sl]") as "#Hop_sl".
      { simpl. iFrame. }
      wp_loadField.
      unfold is_Versioned_applyVolatileFn.
      iMod (ghost_low_newop  with "Hghost") as "Hghost".
      { word. }
      { word. }
      { done. }
      { instantiate (1:=o).
        instantiate (1:=eop w w0 o).
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

      iMod (readonly_alloc (own_slice_small reply_sl byteT (DfracOwn 1) (low_compute_reply
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
      simpl.
      iSplitR; first done.
      iSplitR "Hreply_sl2"; last first.
      {
        iClear "Hsl".
        iFrame.
      }
      simpl.
      repeat iExists _.
      iFrame "∗".
      rewrite app_length /=.
      iSplitL "HesmNextIndex".
      { iApply to_named. iExactEq "HesmNextIndex".
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
    destruct Henc as [? (HlowEnc & Hro & Henc)].
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

    iDestruct (own_slice_small_sz with "Hsl2") as %Hsl_sz.
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
    replace (1 + length x - uint.nat 1%Z)
      with (length (x)) by word.
    replace (uint.nat (W64 1)) with (length [W8 2]) by done.
    rewrite drop_app_length.
    rewrite take_ge; last word.
    rename x into eeop_bytes.
    wp_pures.
    wp_loadField.
    iAssert (_) with "Hislow" as "#Hislow2".
    iNamed "Hislow2".
    wp_loadField.
    iMod (readonly_alloc (own_slice_small eeop_sl byteT (DfracOwn 1) eeop_bytes) with "[Hop_sl]") as "#Hop_sl".
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
    iSplitR; first by iPureIntro.
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
      iSplitL "HesmNextIndex".
      { iModIntro. iApply to_named. iExactEq "HesmNextIndex".
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
  length ops = uint.nat (length ops) →
  ⊢ |==> ∃ γst,
  own_ghost_vnums γst (ops) (length ops) ∗
  is_state γst (length (ops)) (compute_state ops).(lowops)
.
Proof.
  intros HnoOverflow.
  iMod (ghost_map_alloc_fin []) as (?) "Hmap".
  iExists _.
  iDestruct (big_sepS_elem_of_acc_impl (W64 (length ops)) with "Hmap") as "[HH Hmap]".
  { set_solver. }
  iMod (ghost_map_points_to_update (compute_state ops).(lowops) with "HH") as "HH".
  iMod (ghost_map_points_to_persist with "HH") as "#?".
  iModIntro.
  iFrame "∗#".
  unfold own_ghost_vnums.
  iAssert (
      [∗ set] vnum ∈ fin_to_set u64, ( (⌜uint.nat vnum ≤ length ops⌝
                                    → vnum ⤳[γ] []
                                      ∨ is_state γ vnum
                                (compute_state (take (uint.nat vnum) ops)).(lowops)) ∗
                (⌜uint.nat vnum > length ops⌝ → vnum ⤳[γ] [])))%I with "[-]" as "HH".
  {
    iApply "Hmap".
    {
      iModIntro. iIntros.
      destruct (decide (uint.nat y ≤ length ops)).
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
  assert (uint.nat x = (length ops)).
  { rewrite /= in H2. word. }
  replace (x) with (W64 (length ops)) by word.
  iFrame "#".
Qed.

Lemma wp_eStateMachine__setState s :
  {{{
        True
  }}}
    eStateMachine__setState #s
  {{{
        setFn, RET setFn;
        ⌜val_ty setFn (slice.T byteT -> (arrowT uint64T unitT))%ht⌝ ∗
        esm_is_InMemory_setStateFn setFn (own_StateMachine s)
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

  iIntros (????? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "(%Hsnap & %HnextIndex & #Hsnap_sl & Hown)".
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
  rewrite /esm_has_snap_encoding in Hsnap.
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
  iMod (readonly_alloc (own_slice_small rest_enc_sl0 byteT (DfracOwn 1) lowsnap) with "[Hsnap_sl2]") as "#Hsnap_sl2".
  { simpl. iFrame. }
  unfold is_Versioned_setStateFn.
  iClear "Hghost".
  assert (nextIndex = length ops) by word; subst.
  assert (Hlen: length ops = uint.nat (length ops)).
  { word. }
  iMod (ghost_low_setstate _) as (?) "[Hghost2 #Hstate]"; first done.
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
  iPureIntro. split; last auto.
  rewrite -Hlen. reflexivity.
Qed.

Lemma wp_eStatemachine__getState (s:loc) :
  ⊢ esm_is_InMemory_getStateFn (λ: <>, eStateMachine__getState #s) (own_StateMachine s).
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
  iDestruct (own_slice_to_small with "HlastSeqEnc") as "HlastSeqEnc".
  wp_apply (wp_WriteBytes with "[$Henc_sl $HlastSeqEnc]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_loadField.

  wp_apply (wp_EncodeMapU64ToBytes with "HlastReply").
  iIntros (??) "(Hmap2 & HlastReplyEnc & %HlastReplyEnc)".
  wp_load.
  iDestruct (own_slice_to_small with "HlastReplyEnc") as "HlastReplyEnc".
  wp_apply (wp_WriteBytes with "[$Henc_sl $HlastReplyEnc]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_load.

  wp_apply (wp_WriteBytes with "[$Henc_sl $Hsnap_sl2]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_load.
  iApply "HΦ".
  iDestruct (own_slice_to_small with "Henc_sl") as "Henc_sl".
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
  unfold esm_has_snap_encoding.
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
  length ops = uint.nat (length ops) →
  own_ghost_vnums γst ops latestVnum -∗
  (∀ (vnum : u64),
          ⌜uint.nat vnum < uint.nat latestVnum⌝
          → ⌜uint.nat lastModifiedVnum ≤ uint.nat vnum⌝
          → ∃ someOps : list low_OpType, is_state γst vnum someOps ∗
          ⌜low_compute_reply someOps o =
          low_compute_reply (compute_state ops).(lowops) o⌝) -∗
  ⌜∀ ops' : list esm_record.(Sm.OpType),
     ops' `prefix_of` ops
  → uint.nat lastModifiedVnum ≤ length ops'
  → esm_record.(Sm.compute_reply) ops (ro_eop o) = esm_record.(Sm.compute_reply) ops' (ro_eop o)⌝
.
Proof.
  intros HnoOverflow.
  iNamed 1.
  iIntros "#Hstates".
  iIntros (???).
  iSpecialize ("Hstates" $! (length a)).

  assert (uint.nat (length a) = (length a)) as HaOverflow.
  {
    apply prefix_length in a0.
    rewrite HnoOverflow in a0.
    word.
  }

  destruct (decide (uint.nat latestVnum <= length a)).
  { (* use HlatestVersion *)
    iDestruct (big_sepS_elem_of_acc _ _ (W64 (length a)) with "HlatestVersion") as "[#HH _]".
    { set_solver. }
    iSpecialize ("HH" with "[%] [%]").
    {
      apply prefix_length in a0.
      rewrite HaOverflow. done.
    }
    { word. }

    iDestruct (big_sepS_elem_of_acc _ _ (W64 (length a)) with "Hversions") as "[H2 _]".
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
    replace (take (uint.nat (length a)) ops) with a in H.
    {
      unfold esm_record. simpl.
      unfold compute_reply.
      unfold apply_op_and_get_reply.
      rewrite H /=.
      done.
    }
    {
      rewrite HaOverflow.
      destruct a0 as [? ->].
      by rewrite take_app_length.
    }
  }
  { (* use Hstates *)
    iSpecialize ("Hstates" with "[%] [%]").
    { word. }
    { word. }
    iDestruct "Hstates" as (?) "[Hstate %]".
    iDestruct (big_sepS_elem_of_acc _ _ (W64 (length a)) with "Hversions") as "[H2 _]".
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
    replace (take (uint.nat (length a)) ops) with a in H.
    {
      unfold esm_record. simpl.
      unfold compute_reply.
      unfold apply_op_and_get_reply.
      simpl.
      rewrite H /=.
      done.
    }
    {
      rewrite HaOverflow.
      destruct a0 as [? ->].
      by rewrite take_app_length.
    }
  }
Qed.

Lemma wp_eStateMachine__applyReadonly s :
  {{{
        True
  }}}
    eStateMachine__applyReadonly #s
  {{{
        applyReadonlyFn, RET applyReadonlyFn;
        ⌜val_ty applyReadonlyFn (slice.T byteT -> (prodT uint64T (slice.T byteT)))⌝ ∗
        esm_is_InMemory_applyReadonlyFn applyReadonlyFn (own_StateMachine s)
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
  destruct Henc as (lowop_bytes & ? & Henc & ?).
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

  iDestruct (own_slice_small_sz with  "Hsl2") as %Hsl_sz.
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
  replace (1 + length lowop_bytes - uint.nat 1%Z)
    with (length lowop_bytes) by word.
  replace (uint.nat (W64 1)) with (length [W8 2]) by done.
  rewrite drop_app_length.
  rewrite take_ge; last word.
  wp_pures.
  wp_loadField.
  iAssert (_) with "Hislow" as "#Hislow2".
  iNamed "Hislow2".
  wp_loadField.
  iMod (readonly_alloc (own_slice_small eeop_sl byteT (DfracOwn 1) lowop_bytes) with "[Hop_sl]") as "#Hop_sl".
  { simpl. iFrame. }
  wp_apply ("HapplyReadonly_spec" with "[$Hlowstate]").
  { iFrame "#". rewrite /esm_record /= in Hro. iPureIntro; split; done. }
  iIntros (???) "(%Hlen & Hlow & Hrep_sl & #Hstates)".
  iApply "HΦ".
  iSplitR.
  { iPureIntro. transitivity (uint.nat latestVnum).
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
  iDestruct (big_sepS_elem_of_acc_impl (W64 0) with "Hmap") as "[HH Hmap]".
  { set_solver. }
  iMod (ghost_map_points_to_persist with "HH") as "#?".
  iModIntro.
  iFrame "∗#".
  iSplitL.
  {
    iApply "Hmap".
    { iModIntro. iIntros. iFrame. }
    { iIntros. exfalso. simpl in H. replace (uint.nat (W64 0)) with (0) in H; word. }
  }
  iSplitL.
  {
    iApply (big_sepS_impl with "[]").
    { by iApply big_sepS_emp. }
    iModIntro. iIntros.
    assert (uint.nat x = 0).
    { rewrite /= in H1. word. }
    replace (x) with (W64 0) by word.
    iFrame "#".
  }
  iApply big_sepS_forall.
  iIntros. iModIntro.
  iIntros. rewrite /= in H1.
  assert (uint.nat x = 0).
  { rewrite /= in H0. word. }
  replace (x) with (W64 0) by word.
  iFrame "#".
Qed.

Lemma wp_MakeExactlyOnceStateMachine own_low lowSm :
  {{{
      "#Hislow" ∷ low_is_VersionedStateMachine lowSm own_low ∗
      "Hlowstate" ∷ (∀ γst, is_state γst 0 [] -∗
                      own_low γst [] 0)
  }}}
    MakeExactlyOnceStateMachine #lowSm
  {{{
      sm own_MemStateMachine, RET #sm;
        esm_is_InMemoryStateMachine sm own_MemStateMachine ∗
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
  wp_apply (wp_NewMap u64).
  iIntros (lastSeq_ptr) "HlastSeq".
  wp_storeField.
  wp_apply (wp_byteMapNew).
  iIntros (lastReply_ptr) "HlastReply".
  wp_storeField.
  wp_storeField.
  wp_storeField.

  wp_apply wp_eStateMachine__applyReadonly.
  iIntros (?) "[% #HisapplyReadonly]".
  wp_apply wp_eStateMachine__apply.
  iIntros (?) "[% #Hisapply]".
  wp_apply wp_eStateMachine__setState.
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
    iApply wp_eStatemachine__getState.
  }
  iNamed "Hpre".
  iMod (alloc_own_ghost_vnums) as (?) "[Hghost #Hstate]".
  iSpecialize ("Hlowstate" with "Hstate").
  iModIntro.
  repeat iExists _.
  iFrame "∗#".
  done.
Qed.

Lemma wp_MakeClerk configHosts_sl configHosts γ γoplog γerpc :
  {{{
    "#HconfSl" ∷ readonly (own_slice_small configHosts_sl uint64T (DfracOwn 1) configHosts) ∗
    "#Hconf" ∷ config_protocol_proof.is_pb_config_hosts configHosts γ ∗
    "#Hesm_inv" ∷ is_esm_inv γ γoplog γerpc ∗
    "#Herpc_inv" ∷ is_eRPCServer γerpc
  }}}
    exactlyonce.MakeClerk (slice_val configHosts_sl)
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
  { iFrame "#%". }
  iIntros (?) "Hck".
  wp_storeField.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hsl".
  wp_pures.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
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
  wp_apply (wp_Clerk__Apply with "Hck [$Hsl]").
  {
    simpl.
    instantiate (1:=getcid).
    done.
  }
  iModIntro.

  iInv "Hesm_inv" as "Hi" "Hclose".
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
  iIntros "%Hpost Hoplog".
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
      rewrite /esm_record /= in Hpost.
      rewrite /apply_op /=.
      word.
    }
    {
      iLeft. iPureIntro.
      rewrite /esm_record /= in Hpost.
      rewrite /apply_op /=.
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
