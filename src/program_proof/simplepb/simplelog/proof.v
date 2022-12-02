From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export simplelog.
From Perennial.program_proof Require Import marshal_stateless_proof.
From coqutil.Datatypes Require Import List.
From Perennial.goose_lang Require Import crash_borrow.

From Perennial.program_proof.aof Require Import proof.

Section proof.

(* State machine definition *)
Record SMRecord :=
  {
    sm_OpType:Type ;
    sm_has_op_encoding : list u8 → sm_OpType → Prop ;
    sm_has_snap_encoding: list u8 → (list sm_OpType) → Prop ;
    sm_has_op_encoding_injective : ∀ o1 o2 l, sm_has_op_encoding l o1 → sm_has_op_encoding l o2 → o1 = o2 ;
    sm_compute_reply : list sm_OpType → sm_OpType → list u8 ;
  }.

Context {sm_record:SMRecord}.
Notation OpType := (sm_OpType sm_record).
Notation has_op_encoding := (sm_has_op_encoding sm_record).
Notation has_snap_encoding := (sm_has_snap_encoding sm_record).
Notation has_op_encoding_injective := (sm_has_op_encoding_injective sm_record).
Notation compute_reply := (sm_compute_reply sm_record).

Context `{!heapGS Σ}.
Context `{!aofG Σ}.

(* Want to prove *)

Definition file_encodes_state (data:list u8) (epoch:u64) (ops: list OpType) (sealed:bool): Prop.
Admitted.

Lemma file_encodes_state_inj data e ops s e' ops' s':
  file_encodes_state data e ops s →
  file_encodes_state data e' ops' s' →
  e = e' ∧
  ops = ops' ∧
  s = s'.
Proof.
Admitted.

Lemma file_encodes_state_append op op_bytes data epoch ops :
  has_op_encoding op_bytes op →
  file_encodes_state data epoch ops false →
  file_encodes_state (data ++ (u64_le (length op_bytes)) ++ op_bytes) epoch (ops++[op]) false
.
Proof.
Admitted.

Lemma file_encodes_state_snapshot snap ops epoch :
  has_snap_encoding snap ops →
  file_encodes_state ((u64_le (length snap) ++ snap) ++ u64_le epoch ++ u64_le (length ops))
    epoch ops false
.
Proof.
Admitted.

Implicit Types (P:u64 → list OpType → bool → iProp Σ).

Definition file_inv P (contents:list u8) : iProp Σ :=
  ∃ epoch ops sealed,
  ⌜file_encodes_state contents epoch ops sealed⌝ ∗
  P epoch ops sealed
.

Implicit Types own_InMemoryStateMachine : list OpType → iProp Σ.

Definition is_InMemory_applyVolatileFn (applyVolatileFn:val) own_InMemoryStateMachine : iProp Σ :=
  ∀ ops op op_sl op_bytes,
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        own_InMemoryStateMachine ops
  }}}
    applyVolatileFn (slice_val op_sl)
  {{{
        reply_sl q, RET (slice_val reply_sl);
        own_InMemoryStateMachine (ops ++ [op]) ∗
        is_slice_small reply_sl byteT q (compute_reply ops op)
  }}}
.

Definition is_InMemory_setStateFn (setStateFn:val) own_InMemoryStateMachine : iProp Σ :=
  ∀ ops_prev ops snap snap_sl,
  {{{
        ⌜has_snap_encoding snap ops⌝ ∗
        readonly (is_slice_small snap_sl byteT 1 snap) ∗
        own_InMemoryStateMachine ops_prev
  }}}
    setStateFn (slice_val snap_sl)
  {{{
        RET #(); own_InMemoryStateMachine ops
  }}}
.

Definition is_InMemoryStateMachine (sm:loc) own_InMemoryStateMachine : iProp Σ :=
  ∃ applyVolatileFn setStateFn,
  "#HapplyVolatile" ∷ readonly (sm ↦[InMemoryStateMachine :: "ApplyVolatile"] applyVolatileFn) ∗
  "#HapplyVolatile_spec" ∷ is_InMemory_applyVolatileFn applyVolatileFn own_InMemoryStateMachine ∗
  "#HsetState" ∷ readonly (sm ↦[InMemoryStateMachine :: "SetState"] setStateFn) ∗
  "#HsetState_spec" ∷ is_InMemory_setStateFn setStateFn own_InMemoryStateMachine
.

Definition own_StateMachine (s:loc) (epoch:u64) (ops:list OpType) (sealed:bool) P : iProp Σ :=
  ∃ (fname:string) (aof_ptr:loc) γaof (logsize:u64) (smMem_ptr:loc) data
    own_InMemoryStateMachine,
    "Hfname" ∷ s ↦[StateMachine :: "fname"] #(LitString fname) ∗
    "HlogFile" ∷ s ↦[StateMachine :: "logFile"] #aof_ptr ∗
    "HsmMem" ∷ s ↦[StateMachine :: "smMem"] #smMem_ptr ∗
    "HnextIndex" ∷ s ↦[StateMachine :: "nextIndex"] #(U64 (length ops)) ∗
    "Hlogsize" ∷ s ↦[StateMachine :: "logsize"] #logsize ∗
    "Hepoch" ∷ s ↦[StateMachine :: "epoch"] #epoch ∗
    "Hsealed" ∷ s ↦[StateMachine :: "sealed"] #sealed ∗

    "Haof" ∷ aof_log_own γaof data ∗
    "#His_aof" ∷ is_aof aof_ptr γaof fname (file_inv P) ∗
    "%Henc" ∷ ⌜file_encodes_state data epoch ops sealed⌝ ∗
    "Hmemstate" ∷ own_InMemoryStateMachine ops ∗
    "#HisMemSm" ∷ is_InMemoryStateMachine smMem_ptr own_InMemoryStateMachine
    (* "HsmMem" ∷ *)
.

Lemma StateMachine__apply s Q (op:OpType) (op_bytes:list u8) op_sl epoch ops P :
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        (P epoch ops false ={⊤}=∗ P epoch (ops ++ [op]) false ∗ Q) ∗
        own_StateMachine s epoch ops false P
  }}}
    StateMachine__apply #s (slice_val op_sl)
  {{{
        reply_sl q (waitFn:goose_lang.val),
        RET (slice_val reply_sl, waitFn);
        is_slice_small reply_sl byteT q (compute_reply ops op) ∗
        own_StateMachine s epoch (ops ++ [op]) false P ∗
        (∀ Ψ, (Q -∗ Ψ #()) -∗ WP waitFn #() {{ Ψ }})
  }}}
.
Proof.
  iIntros (Φ) "(%HopEnc & #Hop_sl & Hupd & Hown) HΦ".
  wp_lam.
  wp_pures.

  iNamed "Hown".

  (* first, apply the operation in memory and to compute the reply *)
  iAssert (_) with "HisMemSm" as "#HisMemSm2".
  iNamed "HisMemSm2".
  wp_loadField.
  wp_loadField.
  wp_apply ("HapplyVolatile_spec" with "[$Hmemstate]").
  {
    iFrame "#".
    done.
  }
  iIntros (??) "[Hmemstate Hreply_sl]".
  wp_pures.

  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_storeField.

  wp_loadField.
  wp_if_destruct.
  {
    admit. (* TODO: get rid of this panic *)
  }

  (* make opWithLen *)
  iMod (readonly_load with "Hop_sl") as (?) "Hop_sl2".
  iDestruct (is_slice_small_sz with "Hop_sl2") as %Hop_sz.
  wp_apply (wp_slice_len).
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "HopWithLen_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (opWithLen_sl_ptr) "HopWithLen".
  wp_pures.
  wp_apply wp_slice_len.
  wp_load.
  wp_apply (wp_WriteInt with "[$HopWithLen_sl]").
  iIntros (opWithLen_sl) "HopWithLen_sl".
  wp_store.
  wp_load.
  wp_apply (wp_WriteBytes with "[$HopWithLen_sl $Hop_sl2]").
  rename opWithLen_sl into opWithLen_sl_old.
  iIntros (opWithLen_sl) "[HopWithLen_sl _]".
  wp_store.

  (* start append on logfile *)
  wp_load.
  wp_loadField.

  iDestruct (is_slice_to_small with "HopWithLen_sl") as "HopWithLen_sl".

  (* simplify marshalled opWithLen list *)
  replace (int.nat 0) with (0%nat) by word.
  rewrite replicate_0.
  rewrite app_nil_l.
  replace (op_sl.(Slice.sz)) with (U64 (length op_bytes)); last first.
  { word. }

  wp_apply (wp_AppendOnlyFile__Append with "His_aof [$Haof $HopWithLen_sl Hupd]").
  { rewrite app_length. rewrite u64_le_length. word. }
  { admit. } (* TODO: list size overflow *)
  {
    instantiate (1:=Q).
    iIntros "Hi".
    iDestruct "Hi" as (???) "[%Henc2 HP]".
    pose proof (file_encodes_state_inj _ _ _ _ _ _ _ Henc2 Henc) as [-> [-> ->]].
    iMod ("Hupd" with "HP") as "[HP $]".
    iModIntro.
    iExists _, (ops ++ [op]), _.
    iFrame "HP".
    iPureIntro.
    by apply file_encodes_state_append.
  }
  iIntros (l) "[Haof HupdQ]".
  wp_pures.
  wp_loadField.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
  iSplitR "HupdQ".
  {
    iExists _, _, _, _, _, _, _.
    iFrame "∗#".
    iSplitL; last first.
    { iPureIntro. by apply file_encodes_state_append. }
    iApply to_named.
    iExactEq "HnextIndex".
    repeat f_equal.
    rewrite app_length.
    simpl.
    admit. (* TODO: show that the length of the ops list does not overflow *)
  }
  iIntros (Ψ) "HΨ".
  wp_call.
  wp_apply (wp_AppendOnlyFile__WaitAppend with "[$His_aof]").
  iIntros "Haof_len".
  iMod ("HupdQ" with "Haof_len") as "HQ".
  wp_pures.
  iModIntro.
  iApply "HΨ".
  iFrame.
Admitted.

Opaque crash_borrow.
Lemma wp_SetStateAndUnseal s (set_state_fn:val) P ops_prev (epoch_prev:u64) sealed_prev ops epoch (snap:list u8) snap_sl Q :
  {{{
        ⌜has_snap_encoding snap ops⌝ ∗
        readonly (is_slice_small snap_sl byteT 1 snap) ∗
        (P epoch_prev ops_prev sealed_prev ={⊤}=∗ P epoch ops false ∗ Q) ∗
        own_StateMachine s epoch_prev ops_prev sealed_prev P
  }}}
    StateMachine__setStateAndUnseal #s (slice_val snap_sl) #(U64 (length ops)) #epoch
  {{{
        RET #();
        own_StateMachine s epoch ops false P ∗ Q
  }}}
.
Proof.
  iIntros (Φ) "(%HsnapEnc & #Hsnap_sl & Hupd & Hown) HΦ".
  wp_lam.
  wp_pures.
  iNamed "Hown".

  wp_storeField.
  wp_storeField.
  wp_storeField.

  iAssert (_) with "HisMemSm" as "#HisMemSm2".
  iNamed "HisMemSm2".
  wp_loadField.
  wp_loadField.
  wp_apply ("HsetState_spec" with "[$Hsnap_sl $Hmemstate]").
  { done. }
  iIntros "Hmemstate".

  wp_pures.

  (* XXX: this could be a separate lemma *)
  wp_lam.
  wp_pures.

  (* create contents of brand new file *)

  wp_apply (wp_slice_len).
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }

  iIntros (?) "Henc_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_load.
  wp_apply (wp_WriteInt with "[$Henc_sl]").
  iIntros (enc_sl) "Henc_sl".
  wp_pures.
  wp_store.

  wp_load.
  iMod (readonly_load with "Hsnap_sl") as (?) "Hsnap_sl2".
  iDestruct (is_slice_small_sz with "Hsnap_sl2") as "%Hsnap_sz".
  wp_apply (wp_WriteBytes with "[$Henc_sl $Hsnap_sl2]").
  iIntros (enc_sl2) "[Henc_sl _]".
  wp_store.

  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "[$Henc_sl]").
  iIntros (enc_sl3) "Henc_sl".
  wp_pures.
  wp_store.

  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "[$Henc_sl]").
  iIntros (enc_sl4) "Henc_sl".
  wp_pures.
  wp_store.

  replace (int.nat 0) with (0%nat) by word.
  rewrite replicate_0.
  rewrite app_nil_l.
  replace (snap_sl.(Slice.sz)) with (U64 (length snap)); last first.
  { word. }

  wp_loadField.
  wp_pures.

  wp_loadField.

  wp_apply (wp_AppendOnlyFile__Close with "His_aof [$Haof]").
  iIntros "Hfile".
  wp_pures.

  wp_load.
  wp_loadField.

  wp_bind (FileWrite _ _).
  iApply (wpc_wp _ _ _ _ True).

  wpc_apply (wpc_crash_borrow_open_modify with "Hfile").
  { done. }
  iSplit; first done.
  iIntros "[Hfile Hinv]".
  iDestruct (is_slice_to_small with "Henc_sl") as "Henc_sl".
  iApply wpc_fupd.
  wpc_apply (wpc_FileWrite with "[$Hfile $Henc_sl]").
  iSplit.
  { (* case: crash; *)
    iIntros "[Hbefore|Hafter]".
    {
      iSplitR; first done.
      iModIntro; iExists _; iFrame.
    }
    { (* fire update; this is the same as the reasoning in the non-crash case *)
      iSplitR; first done.

      iDestruct "Hinv" as (???) "[%Henc2 HP]".
      pose proof (file_encodes_state_inj _ _ _ _ _ _ _ Henc2 Henc) as [-> [-> ->]].
      iMod ("Hupd" with "HP") as "[HP _]".
      iModIntro. iExists _; iFrame.
      iExists _, _, _; iFrame "HP".
      iPureIntro.
      rewrite -app_assoc.
      by apply file_encodes_state_snapshot.
    }
  }
  iNext.
  iIntros "[Hfile _]".
  iExists _.

  (* update file_inv *)
  iDestruct "Hinv" as (???) "[%Henc2 HP]".
  pose proof (file_encodes_state_inj _ _ _ _ _ _ _ Henc2 Henc) as [-> [-> ->]].
  iMod ("Hupd" with "HP") as "[HP HQ]".
  iModIntro.
  rewrite -app_assoc.
  set (newdata:=(u64_le (length snap) ++ snap) ++ u64_le epoch ++ u64_le (length ops)).
  iAssert (file_inv P newdata) with "[HP]" as "HP".
  {
    iExists _, _, _; iFrame "HP".
    iPureIntro.
    unfold newdata.
    rewrite -app_assoc.
    by apply file_encodes_state_snapshot.
  }
  iSplitL "Hfile HP".
  { iAccu. }
  iSplit.
  {
    iModIntro.
    iIntros "[Hfile HP]".
    iModIntro. iExists _; iFrame.
  }
  iIntros "Hfile".
  iSplit; first done.
  wp_pures.
  wp_loadField.

  wp_apply (wp_CreateAppendOnlyFile _ _ (file_inv P) with "[$Hfile]").
  iClear "His_aof".
  iIntros (new_aof_ptr γaof2) "[His_aof Haof]".
  wp_storeField.
  wp_pures.
  iApply "HΦ".
  iFrame "HQ".
  iModIntro.
  iExists fname, new_aof_ptr, γaof2, _, _, newdata, own_InMemoryStateMachine.
  iFrame "∗".
  iFrame "#".
  iPureIntro.
  unfold newdata.
  rewrite -app_assoc.
  by apply file_encodes_state_snapshot.
Qed.

End proof.
