From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.
From coqutil.Datatypes Require Import List.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.algebra Require Import mlist map.
From Perennial.program_proof.aof Require Import proof.
From Perennial.program_proof.vrsm.replica Require Import start_proof definitions.
From Goose.github_com.mit_pdos.gokv.vrsm Require Export storage.

Section global_proof.

Context {sm_record:Sm.t}.
Import Sm.
Instance e : EqDecision OpType := OpType_EqDecision.

Class simplelogG Σ := SimplelogG {
  simplelog_fmlistG :> fmlistG ((list OpType) * bool) Σ;
  simplelog_propose_fmlistG :> fmlistG OpType Σ;
  simplelog_aofG :> aofG Σ ;
  simplelog_pbG :> pbG Σ ;
}.

Definition simplelogΣ := #[
  fmlistΣ (list (OpType) * bool) ;
  fmlistΣ OpType ;
  aofΣ ;
  pbΣ
].

Global Instance subG_simplelogΣ {Σ} : subG simplelogΣ Σ → simplelogG Σ.
Proof. solve_inG. Qed.

Context `{!gooseGlobalGS Σ}.
Context `{!simplelogG Σ}.

(* Want to prove *)

Definition file_encodes_state (data:list u8) (epoch:u64) (ops: list OpType) (sealed:bool): Prop :=
  ∃ snap_ops snap (rest_ops:list OpType) (rest_ops_bytes:list (list u8)) sealed_bytes,
    ops = snap_ops ++ rest_ops ∧
    has_snap_encoding snap snap_ops ∧
    sealed_bytes = match sealed with false => [] | true => [W8 0] end /\
    length rest_ops = length rest_ops_bytes ∧
    (∀ (i:nat), i < length rest_ops →
          ∃ op op_len_bytes op_bytes,
            rest_ops !! i = Some op ∧
              rest_ops_bytes !! i = Some (op_len_bytes ++ op_bytes) ∧
              has_op_encoding op_bytes op /\
              op_len_bytes = u64_le (length op_bytes)
    ) ∧

    (length ops < 2^64)%Z ∧
    data = (u64_le (length snap)) ++ snap ++ (u64_le epoch) ++ (u64_le (length snap_ops)) ++
                         (concat rest_ops_bytes) ++ sealed_bytes
.

Lemma file_encodes_state_nonempty data epoch ops sealed :
  file_encodes_state data epoch ops sealed → length data > 0.
Proof.
  destruct 1 as (snap_ops&snap&rest_ops&rest_ops_bytes&sealed_bytes&Heq&Henc&Hsealed&Hlen&Henc'&?&Hdata).
  rewrite Hdata. rewrite ?app_length.
  rewrite u64_le_length; lia.
Qed.

Lemma file_encodes_state_append op op_bytes data epoch ops :
  (length ops + 1 < 2 ^ 64)%Z →
  has_op_encoding op_bytes op →
  file_encodes_state data epoch ops false →
  file_encodes_state (data ++ (u64_le (length op_bytes)) ++ op_bytes) epoch (ops++[op]) false
.
Proof.
  rewrite /file_encodes_state.
  intros Hoverflow Hop_enc Hf_enc.
  destruct Hf_enc as (snap_ops&snap&rest_ops&rest_ops_bytes&sealed_bytes&Heq_ops&Hsnaop_enc&Hsealed&Hlen&Hrest&?&Heq_data).
  do 3 eexists.
  exists (rest_ops_bytes ++ [u64_le (length op_bytes) ++ op_bytes]).
  exists [].
  split_and!.
  { rewrite Heq_ops. rewrite -app_assoc. f_equal. }
  { eauto. }
  { auto. }
  { rewrite ?app_length /=; lia. }
  { intros i Hlt.
    rewrite ?app_length /= in Hlt.
    destruct (decide (i = length rest_ops)); last first.
    { edestruct (Hrest i) as (op'&op_len_bytes'&op_bytes'&Hlookup1&Hlookup2&Henc'&Hlenenc'); eauto.
      { lia. }
      do 3 eexists; split_and!; eauto.
      { rewrite lookup_app_l; auto; lia. }
      { rewrite lookup_app_l; auto; lia. }
    }
    {
      subst. exists op, (u64_le (length op_bytes)), op_bytes. split_and!; eauto.
      { rewrite lookup_app_r ?list_lookup_singleton; auto. rewrite Nat.sub_diag //. }
      { rewrite lookup_app_r ?list_lookup_singleton; auto; try lia.
        rewrite Hlen. rewrite Nat.sub_diag //. }
    }
  }
  { rewrite ?app_length /=. lia. }
  { rewrite Heq_data. rewrite -?app_assoc.
    rewrite Hsealed.
    rewrite ?concat_app -?app_assoc. do 4 f_equal.
    rewrite /concat app_nil_r // app_nil_r //.
  }
Qed.

Lemma file_encodes_state_snapshot snap ops epoch :
  (length ops < 2 ^ 64)%Z →
  has_snap_encoding snap ops →
  file_encodes_state ((u64_le (length snap) ++ snap) ++ u64_le epoch ++ u64_le (length ops))
    epoch ops false
.
Proof.
  rewrite /file_encodes_state.
  intros Henc.
  exists ops, snap, [], [], [].
  rewrite ?app_nil_r. split_and!; auto.
  { simpl. intros. lia. }
Qed.

Lemma file_encodes_state_seal data ops epoch :
  file_encodes_state data epoch ops false →
  file_encodes_state (data ++ [W8 0]) epoch ops true
.
Proof.
  destruct 1 as
    (snap_ops&snap&rest_ops&rest_ops_bytes&sealed_bytes&Heq_ops&Hsnaop_enc&Hsealed&Hlen&Hrest&?&Heq_data).
  exists snap_ops, snap, rest_ops, rest_ops_bytes, [W8 0].
  split_and!; eauto.
  rewrite Heq_data Hsealed. rewrite -?app_assoc app_nil_l //.
Qed.

Implicit Types (P:u64 → list OpType → bool → iProp Σ).

Definition file_crash P (contents:list u8) : iProp Σ :=
  ⌜contents = []⌝ ∗ P 0 [] false
  ∨
  ∃ epoch ops sealed,
    ⌜file_encodes_state contents epoch ops sealed⌝ ∗
    P epoch ops sealed
.

End global_proof.

Section sm_defn.

Context {sm_record:Sm.t}.
Import Sm.

Context `{!heapGS Σ}.
Implicit Types own_InMemoryStateMachine : list OpType → iProp Σ.
Definition is_InMemory_applyVolatileFn (applyVolatileFn:val) own_InMemoryStateMachine : iProp Σ :=
  ∀ ops op op_sl op_bytes,
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        readonly (own_slice_small op_sl byteT (DfracOwn 1) op_bytes) ∗
        own_InMemoryStateMachine ops
  }}}
    applyVolatileFn (slice_val op_sl)
  {{{
        reply_sl q, RET (slice_val reply_sl);
        ⌜apply_postcond  ops op⌝ ∗
        own_InMemoryStateMachine (ops ++ [op]) ∗
        own_slice_small reply_sl byteT (DfracOwn q) (compute_reply ops op)
  }}}
.

Definition is_InMemory_setStateFn (setStateFn:val) own_InMemoryStateMachine : iProp Σ :=
  ∀ ops_prev ops snap snap_sl (nextIndex:u64),
  {{{
        ⌜has_snap_encoding snap ops⌝ ∗
        ⌜uint.nat nextIndex = length ops⌝ ∗
        readonly (own_slice_small snap_sl byteT (DfracOwn 1) snap) ∗
        own_InMemoryStateMachine ops_prev
  }}}
    setStateFn (slice_val snap_sl) #nextIndex
  {{{
        RET #(); own_InMemoryStateMachine ops
  }}}
.

Definition is_InMemory_getStateFn (getStateFn:val) own_InMemoryStateMachine : iProp Σ :=
  ∀ ops,
  {{{
        own_InMemoryStateMachine ops
  }}}
    getStateFn #()
  {{{
        snap snap_sl, RET (slice_val snap_sl); own_InMemoryStateMachine ops ∗
        ⌜has_snap_encoding snap ops⌝ ∗
        readonly (own_slice_small snap_sl byteT (DfracOwn 1) snap)
  }}}
.

Definition is_InMemory_applyReadonlyFn (applyReadonlyFn:val) own_InMemoryStateMachine : iProp Σ :=
  ∀ ops op op_sl op_bytes,
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        ⌜is_readonly_op op⌝ ∗
        readonly (own_slice_small op_sl byteT (DfracOwn 1) op_bytes) ∗
        own_InMemoryStateMachine ops
  }}}
    applyReadonlyFn (slice_val op_sl)
  {{{
        reply_sl q (lastModifiedIndex:u64),
        RET (#lastModifiedIndex, slice_val reply_sl);
        ⌜uint.nat lastModifiedIndex <= length ops ⌝ ∗
        ⌜∀ ops', prefix ops' ops → uint.nat lastModifiedIndex <= length ops' →
               (compute_reply ops op = compute_reply ops' op)⌝ ∗
        own_InMemoryStateMachine ops ∗
        own_slice_small reply_sl byteT (DfracOwn q) (compute_reply ops op)
  }}}
.

Definition is_InMemoryStateMachine (sm:loc) own_InMemoryStateMachine : iProp Σ :=
  ∃ applyVolatileFn setStateFn getStateFn applyReadonlyFn,
  "#HapplyVolatile" ∷ readonly (sm ↦[InMemoryStateMachine :: "ApplyVolatile"] applyVolatileFn) ∗
  "#HapplyVolatile_spec" ∷ is_InMemory_applyVolatileFn applyVolatileFn own_InMemoryStateMachine ∗

  "#HsetState" ∷ readonly (sm ↦[InMemoryStateMachine :: "SetState"] setStateFn) ∗
  "#HsetState_spec" ∷ is_InMemory_setStateFn setStateFn own_InMemoryStateMachine ∗

  "#HgetState" ∷ readonly (sm ↦[InMemoryStateMachine :: "GetState"] getStateFn) ∗
  "#HgetState_spec" ∷ is_InMemory_getStateFn getStateFn own_InMemoryStateMachine ∗

  "#HapplyReadonly" ∷ readonly (sm ↦[InMemoryStateMachine :: "ApplyReadonly"] applyReadonlyFn) ∗
  "#HapplyReadonly_spec" ∷ is_InMemory_applyReadonlyFn applyReadonlyFn own_InMemoryStateMachine
.

End sm_defn.

Section local_proof.

Context `{!heapGS Σ}.

Context {params:pbParams.t}.
Import pbParams.
Import Sm.

Record simplelog_names :=
{
  (* file_encodes_state is not injective, so we use this state to
     remember that "for the 5th append, the (epoch, ops, sealed) was X".
     For each possible length, there's a potential read-only proposal.
   *)
  sl_state : gname;
  proposed_gn: gname;
}.

Context `{!simplelogG Σ}.

Definition file_inv γ P epoch (contents:list u8) : iProp Σ :=
  ∃ ops sealed,
  ⌜file_encodes_state contents epoch ops sealed⌝ ∗
  P epoch ops sealed ∗
  fmlist_idx γ.(sl_state) (length contents) (ops, sealed) ∗
  fmlist_lb γ.(proposed_gn) ops
.

Definition own_StateMachine (s:loc) (epoch:u64) (ops:list OpType) (sealed:bool) P : iProp Σ :=
  ∃ (fname:string) (aof_ptr:loc) γ γaof (logsize:u64) (smMem_ptr:loc) data
    own_InMemoryStateMachine (allstates:list (list OpType * bool)),
    "Hfname" ∷ s ↦[StateMachine :: "fname"] #(LitString fname) ∗
    "HlogFile" ∷ s ↦[StateMachine :: "logFile"] #aof_ptr ∗
    "HsmMem" ∷ s ↦[StateMachine :: "smMem"] #smMem_ptr ∗
    "HnextIndex" ∷ s ↦[StateMachine :: "nextIndex"] #(W64 (length ops)) ∗
    "Hlogsize" ∷ s ↦[StateMachine :: "logsize"] #logsize ∗
    "Hepoch" ∷ s ↦[StateMachine :: "epoch"] #epoch ∗
    "Hsealed" ∷ s ↦[StateMachine :: "sealed"] #sealed ∗
    "#Hdurlb" ∷ □(if sealed then aof_durable_lb γaof data else True) ∗

    "Haof" ∷ aof_log_own γaof data ∗
    "#His_aof" ∷ is_aof pbAofN aof_ptr γaof fname (file_inv γ P epoch) (file_crash P) ∗
    "%Henc" ∷ ⌜file_encodes_state data epoch ops sealed⌝ ∗
    "Hmemstate" ∷ own_InMemoryStateMachine ops ∗
    "#HisMemSm" ∷ is_InMemoryStateMachine smMem_ptr own_InMemoryStateMachine ∗

    "%Hopssafe" ∷ ⌜length ops = uint.nat (length ops)⌝ ∗

    "#Hcur_state_var" ∷ fmlist_idx γ.(sl_state) (length data) (ops, sealed) ∗
    "Hallstates" ∷ fmlist γ.(sl_state) (DfracOwn 1) allstates ∗
    "%Hallstates_len" ∷ ⌜length allstates = (length data + 1)%nat⌝ ∗
    "Hops_proposed" ∷ fmlist γ.(proposed_gn) (DfracOwn 1) ops
.

Lemma wp_StateMachine__apply s Q (op:OpType) (op_bytes:list u8) op_sl epoch ops P :
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        readonly (own_slice_small op_sl byteT (DfracOwn 1) op_bytes) ∗
        (⌜apply_postcond ops op⌝ -∗ P epoch ops false
         ={⊤∖↑pbAofN}=∗ P epoch (ops ++ [op]) false ∗ Q) ∗
        own_StateMachine s epoch ops false P
  }}}
    StateMachine__apply #s (slice_val op_sl)
  {{{
        reply_sl q (waitFn:goose_lang.val),
        RET (slice_val reply_sl, waitFn);
        ⌜apply_postcond ops op⌝ ∗
        own_slice_small reply_sl byteT q (compute_reply ops op) ∗
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
  iIntros (??) "(%Hpost & Hmemstate & Hreply_sl)".
  wp_pures.

  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros (HnextIndexOverflow).

  wp_storeField.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_storeField.

  (* make opWithLen *)
  iMod (readonly_load with "Hop_sl") as (?) "Hop_sl2".
  iDestruct (own_slice_small_sz with "Hop_sl2") as %Hop_sz.
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

  iDestruct (own_slice_to_small with "HopWithLen_sl") as "HopWithLen_sl".

  (* simplify marshalled opWithLen list *)
  replace (uint.nat 0) with (0%nat) by word.
  rewrite replicate_0.
  rewrite app_nil_l.
  replace (op_sl.(Slice.sz)) with (W64 (length op_bytes)); last first.
  { word. }

  set (newsuffix:=u64_le (length op_bytes) ++ op_bytes).
  set (newdata:=data ++ newsuffix).

  (* make proposal *)
  iMod (fmlist_update with "Hops_proposed") as "[Hops_proposed #Hprop_lb]".
  {
    instantiate (1:=ops ++ [op]).
    apply prefix_app_r.
    done.
  }
  iMod (fmlist_update with "Hallstates") as "[Hallstates Hallstates_lb]".
  {
    instantiate (1:=allstates ++ (replicate (length newsuffix) (ops ++ [op], false))).
    apply prefix_app_r.
    done.
  }

  iDestruct (fmlist_lb_to_idx _ _ (length newdata) with "Hallstates_lb") as "#Hcurstate".
  {
    unfold newdata.
    rewrite app_length.
    assert (1 <= length newsuffix).
    {
      unfold newsuffix.
      rewrite app_length.
      rewrite u64_le_length.
      word.
    }
    rewrite lookup_app_r; last first.
    { word. }
    rewrite Hallstates_len.
    replace (length data + length newsuffix - (length data + 1))%nat with
      (length newsuffix - 1)%nat by word.
    apply lookup_replicate.
    split; last lia.
    done.
  }

  iDestruct (own_slice_small_sz with "HopWithLen_sl") as %HopWithLen_sz.
  wp_apply (wp_AppendOnlyFile__Append with "His_aof [$Haof $HopWithLen_sl Hupd]").
  { rewrite app_length. rewrite u64_le_length. word. }
  {
    unfold list_safe_size.
    word.
  }
  {
    instantiate (1:=Q).
    iIntros "Hi".
    iDestruct "Hi" as (??) "(%Henc2 & HP & #Hghost2 & _)".
    iDestruct (fmlist_idx_agree_1 with "Hcur_state_var Hghost2") as "%Heq".
    replace (ops0) with (ops) by naive_solver.
    replace (sealed) with (false) by naive_solver.

    iMod ("Hupd" with "[//] HP") as "[HP $]".
    iModIntro.
    iExists (ops ++ [op]), _.
    iFrame "HP".
    rewrite app_length.
    rewrite app_length.
    rewrite u64_le_length.
    iFrame "#".
    iPureIntro.
    apply file_encodes_state_append; auto.
    word.
  }
  iIntros (l) "[Haof HupdQ]".
  wp_pures.
  wp_loadField.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame "Hreply_sl".
  iSplitR; first done.
  iSplitR "HupdQ".
  {
    iExists fname, _, γ, _, _, _, _, _.
    iExists _.
    iFrame "HisMemSm ∗#".
    repeat rewrite app_length. rewrite u64_le_length.
    iFrame "∗#".
    iSplitL; last first.
    { iPureIntro.
      split.
      { apply file_encodes_state_append; auto. word. }
      { rewrite Hallstates_len.
        rewrite replicate_length.
        simpl.
        word. }
    }
    iApply to_named.
    iExactEq "HnextIndex".
    repeat f_equal.
    simpl.
    word.
  }
  iIntros (Ψ) "HΨ".
  wp_call.
  wp_apply (wp_AppendOnlyFile__WaitAppend with "[$His_aof]").
  iIntros "Haof_len".
  iMod ("HupdQ" with "Haof_len") as "[HQ _]".
  wp_pures.
  iModIntro.
  iApply "HΨ".
  iFrame.
Qed.

Lemma wp_setStateAndUnseal s P ops_prev (epoch_prev:u64) sealed_prev ops epoch (snap:list u8) snap_sl Q
      (nextIndex:u64)
  :
  {{{
        ⌜ (length ops < 2 ^ 64)%Z ⌝ ∗
        ⌜has_snap_encoding snap ops⌝ ∗
        ⌜uint.nat nextIndex = length ops⌝ ∗
        readonly (own_slice_small snap_sl byteT (DfracOwn 1) snap) ∗
        (P epoch_prev ops_prev sealed_prev ={⊤}=∗ P epoch ops false ∗ Q) ∗
        own_StateMachine s epoch_prev ops_prev sealed_prev P
  }}}
    StateMachine__setStateAndUnseal #s (slice_val snap_sl) #nextIndex #epoch
  {{{
        RET #();
        own_StateMachine s epoch ops false P ∗ Q
  }}}
.
Proof.
  iIntros (Φ) "(%HsnapLen & %HsnapEnc & %HnextIndex & #Hsnap_sl & Hupd & Hown) HΦ".
  assert (nextIndex = W64 (length ops)) by word; subst.
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
  unfold is_InMemory_setStateFn.
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
  iDestruct (own_slice_small_sz with "Hsnap_sl2") as "%Hsnap_sz".
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

  replace (uint.nat 0) with (0%nat) by word.
  rewrite replicate_0.
  rewrite app_nil_l.
  replace (snap_sl.(Slice.sz)) with (W64 (length snap)); last first.
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
  iDestruct (own_slice_to_small with "Henc_sl") as "Henc_sl".
  iApply wpc_fupd.
  iDestruct (own_slice_small_sz with "Henc_sl") as %Henc_sz.
  wpc_apply (wpc_FileWrite with "[$Hfile $Henc_sl]").
  iSplit.
  { (* case: crash; *)
    iIntros "[Hbefore|Hafter]".
    {
      iSplitR; first done.
      iModIntro; iExists _; iFrame.
      iDestruct "Hinv" as (??) "[H1 [H2 H3]]".
      iRight.
      iExists _,_,_; iFrame.
    }
    { (* fire update; this is the same as the reasoning in the non-crash case *)
      iSplitR; first done.

      iDestruct "Hinv" as (??) "(%Henc2 & HP & #Hghost2 & _)".
      iDestruct (fmlist_idx_agree_1 with "Hcur_state_var Hghost2") as "%Heq".
      replace (ops0) with (ops_prev) by naive_solver.
      replace (sealed) with (sealed_prev) by naive_solver.

      (* Want to change the gname for the γ variable that tracks
         proposals we've made so far, since we're going to make a new aof. This
         means γ can't show up in the crash condition. So, we need aof to have a
         different P in the crash condition and in the current resources. *)
      iMod ("Hupd" with "HP") as "[HP _]".
      iModIntro. iExists _; iFrame.
      iRight.
      iExists _, _, _; iFrame "HP".
      iPureIntro.
      rewrite -app_assoc.
      by apply file_encodes_state_snapshot.
    }
  }
  iNext.
  iIntros "[Hfile _]".

  iClear "Hallstates Hops_proposed".
  iMod (fmlist_alloc ([]: list (list OpType * bool))) as (γcur_state2) "Hallstates".
  iMod (fmlist_alloc ([] : list OpType)) as (γproposed2) "Hops_proposed".
  set (γ2:={| sl_state := γcur_state2 ; proposed_gn := γproposed2|} ).

  (* update file_inv *)

  iDestruct "Hinv" as (??) "(%Henc2 & HP & #Hghost2 & _)".
  iDestruct (fmlist_idx_agree_1 with "Hcur_state_var Hghost2") as "%Heq".
  replace (ops0) with (ops_prev) by naive_solver.
  replace (sealed) with (sealed_prev) by naive_solver.

  iMod ("Hupd" with "HP") as "[HP HQ]".

  rewrite -app_assoc.
  set (newdata:=(u64_le (length snap) ++ snap) ++ u64_le epoch ++ u64_le (length ops)).
  (* set new allstates *)

  iMod (fmlist_update with "Hallstates") as "[Hallstates Hallstates_lb]".
  {
    instantiate (1:=(replicate (length newdata + 1) (ops, false))).
    apply prefix_nil.
  }

  iMod (fmlist_update with "Hops_proposed") as "[Hops_proposed #Hprop_lb]".
  {
    instantiate (1:=ops).
    apply prefix_nil.
  }

  iDestruct (fmlist_lb_to_idx _ _ (length newdata) with "Hallstates_lb") as "#Hcurstate".
  {
    unfold newdata.
    rewrite app_length.
    apply lookup_replicate.
    split; last lia.
    done.
  }

  iAssert (file_inv γ2 P epoch newdata) with "[HP]" as "HP".
  {
    iExists _, _; iFrame "HP #".
    iPureIntro.
    unfold newdata.
    rewrite -app_assoc.
    by apply file_encodes_state_snapshot.
  }
  iModIntro.
  iExists _.
  iSplitL "Hfile HP".
  { iAccu. }
  iSplit.
  {
    iModIntro.
    iIntros "[Hfile HP]".
    iModIntro. iExists _; iFrame "Hfile".
    iDestruct "HP" as (??) "[H1 [H2 H3]]".
    iRight.
    iExists _,_,_; iFrame.
  }
  iIntros "Hfile".
  iSplit; first done.
  wp_pures.
  wp_loadField.

  wp_apply (wp_CreateAppendOnlyFile pbAofN _ _ (file_inv γ2 P epoch) (file_crash P) with "[] [$Hfile]").
  {
    iModIntro. iIntros (?) "Hinv".
    iDestruct "Hinv" as (??) "[H1 [H2 H3]]".
    iRight.
    iExists _,_,_; iFrame.
    by iModIntro.
  }
  iClear "His_aof".
  iIntros (new_aof_ptr γaof2) "(His_aof & Haof & #HdurableLb)".
  wp_storeField.
  wp_pures.
  iApply "HΦ".
  iSplitR "HQ"; last done.
  iModIntro.
  iExists fname, new_aof_ptr, γ2, γaof2, _, _, newdata, own_InMemoryStateMachine.
  iExists _.
  iFrame "∗".
  iFrame "#".
  iSplitR; first done.
  iSplitR.
  {
    iPureIntro.
    unfold newdata.
    rewrite -app_assoc.
    by apply file_encodes_state_snapshot.
  }
  iPureIntro.
  unfold newdata.
  rewrite replicate_length.
  split.
  { word. }
  word.
Qed.

Lemma wp_getStateAndSeal s P epoch ops sealed Q :
  {{{
        own_StateMachine s epoch ops sealed P ∗
        (P epoch ops sealed ={⊤∖↑pbAofN}=∗ P epoch ops true ∗ Q)
  }}}
    StateMachine__getStateAndSeal #s
  {{{
        snap_sl snap,
        RET (slice_val snap_sl);
        readonly (own_slice_small snap_sl byteT (DfracOwn 1) snap) ∗
        ⌜has_snap_encoding snap ops⌝ ∗
        own_StateMachine s epoch ops true P ∗
        Q
  }}}.
Proof.
  iIntros (Φ) "(Hown & Hupd) HΦ".
  wp_lam.
  wp_pures.

  iNamed "Hown".
  wp_loadField.

  wp_pures.
  wp_if_destruct.
  { (* case: not sealed previously *)
    wp_storeField.
    wp_apply (wp_NewSlice).
    iIntros (seal_sl) "Hseal_sl".
    wp_loadField.
    iDestruct (own_slice_to_small with "Hseal_sl") as "Hseal_sl".

    iMod (fmlist_update with "Hallstates") as "[Hallstates Hallstates_lb]".
    {
      instantiate (1:=(allstates ++ [(ops, true)])).
      apply prefix_app_r.
      done.
    }

    iDestruct (fmlist_lb_to_idx _ _ (length (data ++ [W8 0])) with "Hallstates_lb") as "#Hcurstate".
    {
      rewrite app_length.
      simpl.
      rewrite lookup_app_r; last first.
      { word. }
      rewrite Hallstates_len.
      rewrite Nat.sub_diag.
      done.
    }

    wp_apply (wp_AppendOnlyFile__Append with "His_aof [$Haof $Hseal_sl Hupd]").
    { by compute. }
    { by compute. }
    {
      iIntros "Hinv".
      instantiate (1:=Q).

      iDestruct "Hinv" as (??) "(%Henc2 & HP & #Hghost2 & #?)".
      iDestruct (fmlist_idx_agree_1 with "Hcur_state_var Hghost2") as "%Heq".
      replace (ops0) with (ops) by naive_solver.
      replace (sealed) with (false) by naive_solver.

      iMod ("Hupd" with "HP") as "[HP $]".
      iModIntro.
      iExists _, _.
      iFrame "HP".
      iFrame "#".
      iPureIntro.
      by apply file_encodes_state_seal.
    }
    iIntros (l) "[Haof HupdQ]".
    wp_pures.
    wp_loadField.
    wp_apply (wp_AppendOnlyFile__WaitAppend with "His_aof").
    iIntros "Hl".
    iMod ("HupdQ" with "Hl") as "[HQ #Hlb]".

    wp_pures.
    wp_loadField.
    iAssert (_) with "HisMemSm" as "#HisMemSm2".
    iNamed "HisMemSm2".
    wp_loadField.
    wp_apply ("HgetState_spec" with "[$Hmemstate]").
    iIntros (??) "(Hmemstate & %HencSnap & #Hsnap_sl)".
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iSplitR; first done.
    iSplitR; first done.
    iSplitR "HQ"; last done.

    iExists fname, aof_ptr, γ, γaof, _, _, _, _.
    iExists _.
    iFrame "∗#".
    iSplitR.
    {
      iPureIntro.
      by apply file_encodes_state_seal.
    }
    iPureIntro.
    rewrite app_length.
    rewrite app_length.
    rewrite replicate_length.
    simpl.
    word.
  }
  {
    wp_pures.
    wp_loadField.
    iAssert (_) with "HisMemSm" as "#HisMemSm2".
    iNamed "HisMemSm2".
    wp_loadField.
    wp_apply ("HgetState_spec" with "[$Hmemstate]").
    iIntros (??) "(Hmemstate & %HencSnap & #Hsnap_sl)".
    wp_pure1_credit "Hlc".
    wp_pures.
    iApply "HΦ".
    iSplitR; first done.

    iDestruct (accessP with "His_aof Hdurlb Haof") as "HH".
    iMod "HH".
    iDestruct "HH" as (?) "(%HdurPrefix & %HotherPrefix & HP & HcloseP)".
    replace (durableData) with (data); last first.
    {
      apply list_prefix_eq; first done.
      apply prefix_length; done.
    }
    iMod (lc_fupd_elim_later with "Hlc HP") as "HP".
    unfold file_inv.
    iDestruct "HP" as (?? HdurPrefixEnc) "(HP & #Hcurstate2 & #?)".

    iDestruct (fmlist_idx_agree_1 with "Hcur_state_var Hcurstate2") as "%Heq".
    replace (ops0) with (ops) by naive_solver.
    replace (sealed) with (true) by naive_solver.

    iMod ("Hupd" with "HP") as "[HP HQ]".
    iMod ("HcloseP" with "[HP]").
    {
      iNext.
      iExists _, _.
      iFrame "∗#%".
    }
    iModIntro.
    iSplitR; first done.
    iSplitR "HQ"; last done.

    iExists fname, aof_ptr, γ, γaof, _, _, _, _.
    iExists _.
    iFrame "∗#".
    done.
  }
Qed.

Lemma wp_StateMachine__applyReadonly s (op:OpType) (op_bytes:list u8) op_sl epoch ops sealed P :
  {{{
        ⌜has_op_encoding op_bytes op⌝ ∗
        ⌜is_readonly_op op⌝ ∗
        readonly (own_slice_small op_sl byteT (DfracOwn 1) op_bytes) ∗
        own_StateMachine s epoch ops sealed P
  }}}
    StateMachine__applyReadonly #s (slice_val op_sl)
  {{{
        reply_sl q (lastModifiedIndex : u64), RET (#lastModifiedIndex, slice_val reply_sl);
        ⌜uint.nat lastModifiedIndex ≤ length ops⌝ ∗
        ⌜∀ ops' : list OpType,
            ops' `prefix_of` ops
            → uint.nat lastModifiedIndex ≤ length ops' → compute_reply ops op = compute_reply ops' op⌝ ∗
        own_slice_small reply_sl byteT q (compute_reply ops op) ∗
        own_StateMachine s epoch ops sealed P
  }}}
.
Proof.
  iIntros (Φ) "(% & % & #? & Hstate) HΦ".
  wp_lam.
  iNamed "Hstate".
  wp_pures.
  iAssert (_) with "HisMemSm" as "#HisMemSm2".
  iNamed "HisMemSm2".
  wp_loadField.
  wp_loadField.
  wp_apply ("HapplyReadonly_spec" with "[$Hmemstate]").
  { iSplitR; first done. iSplitR; first done. iFrame "#". }
  iIntros (???) "(% & % & Hmemstate & Hreply)".
  iApply "HΦ". iFrame "Hreply".
  iSplitR; first done.
  iSplitR; first done.
  repeat iExists _; iFrame "∗ HisMemSm #%".
Qed.

Lemma wp_recoverStateMachine data P fname smMem own_InMemoryStateMachine Q :
  {{{
       "Hfile_ctx" ∷ crash_borrow (fname f↦ data ∗ file_crash P data)
                    (|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ file_crash P data') ∗
       "#HisMemSm" ∷ is_InMemoryStateMachine (sm_record:=pb_record) smMem own_InMemoryStateMachine ∗
       "Hmemstate" ∷ own_InMemoryStateMachine [] ∗
       "Hinit_upd" ∷ (∀ epoch ops sealed, P epoch ops sealed -∗ □ Q epoch ops sealed )
  }}}
    recoverStateMachine #smMem #(LitString fname)
  {{{
        s epoch ops sealed, RET #s; own_StateMachine s epoch ops sealed P ∗ Q epoch ops sealed
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_pures.

  wp_apply (wp_allocStruct).
  { repeat econstructor. }

  iIntros (s) "Hs".
  wp_pures.
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".

  wp_loadField.

  wp_bind (FileRead _).
  iApply wpc_wp.
  instantiate (1:=True%I).
  wpc_apply (wpc_crash_borrow_open_modify with "Hfile_ctx").
  { done. }
  iSplit; first done.
  iIntros "[Hfile Hfilecrash]".
  iDestruct "Hfilecrash" as "[Hempty|Hnonempty]".
  { (* case: empty *)
    iDestruct "Hempty" as "[%HdataEmpty HP]".
    iMod (fmlist_alloc (replicate (1) ([], false))) as (γsl_state) "Hallstates".
    iMod (fmlist_alloc ([]:list OpType)) as (γproposed) "Hops_proposed".
    set (γ:={| sl_state := γsl_state ; proposed_gn := γproposed |} ).
    iMod (fmlist_get_lb with "Hallstates") as "[Hallstates #Hlb]".
    iMod (fmlist_get_lb with "Hops_proposed") as "[Hops_proposed #Hprop_lb]".
    iDestruct (fmlist_lb_to_idx _ _ (length data) with "Hlb") as "#Hcurstate".
    {
      apply lookup_replicate.
      rewrite HdataEmpty.
      split; last (simpl; lia).
      done.
    }

    wpc_apply (wpc_FileRead with "[$Hfile]").
    iSplit.
    { (* case: crash while reading *)
      iIntros "Hfile".
      iSplitR; first done.
      iModIntro.
      iExists _; iFrame.
      iNext.
      iLeft.
      iFrame "∗%".
    }
    (* otherwise, no crash and we keep going *)
    iNext.
    iIntros (data_sl) "[Hfile Hdata_sl]".
    iExists (fname f↦data ∗ P 0 [] false)%I.
    iSplitL "Hfile HP".
    {
      iFrame.
    }
    iSplit.
    {
      iModIntro.
      iIntros "[? Hinv]".
      iModIntro.
      iExists _; iFrame.
      iNext.
      iLeft.
      iFrame "∗%".
    }
    iIntros "Hfile_ctx".
    iSplit; first done.

    wp_apply (wp_ref_to).
    { done. }
    iIntros (enc_ptr) "Henc".
    wp_pures.
    wp_load.

    iDestruct (own_slice_sz with "Hdata_sl") as %Hdata_sz.
    wp_apply (wp_slice_len).
    wp_pures.
    wp_if_destruct.
    2:{ (* bad case *)
      exfalso.
      rewrite HdataEmpty /= in Hdata_sz.
      replace (data_sl.(Slice.sz)) with (W64 0) in * by word.
      done.
    }

    iAssert (_) with "HisMemSm" as "#HisMemSm2".
    iNamed "HisMemSm2".
    wp_loadField.
    wp_apply ("HgetState_spec" with "[$Hmemstate]").
    iIntros (??) "(Hmemstate & %Hsnapenc & #Hsnap_sl)".
    wp_pures.
    iMod (readonly_load with "Hsnap_sl") as (?) "Hsnap_sl2".
    iDestruct (own_slice_small_sz with "Hsnap_sl2") as %Hsnap_sz.
    wp_apply (wp_slice_len).
    wp_apply (wp_NewSliceWithCap).
    { apply encoding.unsigned_64_nonneg. }
    iIntros (?) "Henc_sl".
    wp_apply (wp_ref_to).
    { done. }
    iIntros (initialContents_ptr) "HinitialContents".
    wp_pures.
    wp_apply (wp_slice_len).
    wp_load.
    wp_apply (wp_WriteInt with "Henc_sl").
    iIntros (enc_sl) "Henc_sl".
    wp_store.
    wp_load.
    wp_apply (wp_WriteBytes with "[$Henc_sl $Hsnap_sl2]").
    iIntros (enc_sl2) "[Henc_sl _]".
    rewrite replicate_0.
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "Henc_sl").
    iIntros (enc_sl3) "Henc_sl".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "Henc_sl").
    iIntros (enc_sl4) "Henc_sl".
    wp_store.
    wp_load.

    wp_loadField.

    iDestruct (own_slice_to_small with "Henc_sl") as "Henc_sl".
    wp_bind (FileWrite _ _).
    iApply (wpc_wp).
    instantiate (1:=True%I).
    wpc_apply (wpc_crash_borrow_open_modify with "Hfile_ctx").
    { done. }
    iSplit; first done.
    iIntros "[Hfile HP]".
    iApply wpc_fupd.
    wpc_apply (wpc_FileWrite with "[$Hfile $Henc_sl]").
    iSplit.
    { (* case: crash while writing *)
      iIntros "[Hbefore|Hafter]".
      {
        iSplitR; first done.
        iModIntro.
        iExists _.
        iFrame.
        iNext.
        iLeft.
        iFrame. done.
      }
      {
        iSplitR; first done.
        iModIntro.
        iExists _.
        iFrame.
        iNext.
        iRight.
        iPureIntro.
        replace (snap_sl.(Slice.sz)) with (W64 (length snap)); last first.
        { word. }
        rewrite app_nil_l.
        rewrite -app_assoc.
        unshelve (epose proof (file_encodes_state_snapshot snap [] 0 _ Hsnapenc)  as H; done).
        simpl. lia.
      }
    }
    iNext.
    iIntros "[Hfile _]".

    set (n:=(length (((([] ++ u64_le snap_sl.(Slice.sz)) ++ snap) ++ u64_le 0%Z) ++ u64_le 0%Z))).
    iMod (fmlist_update with "Hallstates") as "[Hallstates Hallstates_lb]".
    {
      instantiate (1:=((replicate (n+1) ([]:list OpType, false)))).
      rewrite replicate_S.
      simpl.
      apply prefix_cons.
      apply prefix_nil.
    }

    iDestruct (fmlist_lb_to_idx _ _ n with "Hallstates_lb") as "#Hcurstate2".
    {
      apply lookup_replicate.
      split; last lia.
      done.
    }

    iDestruct ("Hinit_upd" with "HP") as "#HQ".
    iModIntro.
    evar (c:list u8).
    iExists (fname f↦ ?c ∗ file_inv γ P 0 ?c)%I.
    iSplitL "Hfile HP".
    {
      iFrame "Hfile".
      iExists _, _.
      iFrame "∗#".
      iPureIntro.

      replace (snap_sl.(Slice.sz)) with (W64 (length snap)); last first.
      { word. }
      rewrite app_nil_l.
      rewrite -app_assoc.
      unshelve (epose proof (file_encodes_state_snapshot snap [] 0 _ Hsnapenc)  as H; done).
      simpl; lia.
    }
    iSplit.
    {
      iModIntro.
      iIntros "[Hfile Hinv]".
      iModIntro.
      iExists _.
      iFrame "Hfile".
      iNext.
      iRight.
      iDestruct "Hinv" as (??) "[H1 [H2 _]]".
      iExists _, _, _.
      iFrame.
    }
    iIntros "Hfile_ctx".
    iSplit; first done.
    wp_pures.
    wp_apply (wp_CreateAppendOnlyFile with "[] [$Hfile_ctx]").
    {
      iModIntro.
      iIntros (?) "Hinv".
      iModIntro.
      iNext.
      iDestruct "Hinv" as (??) "(H1 & H2 & _)".
      iRight. iExists _, _, _.
      iFrame.
    }
    iIntros (aof_ptr γaof) "(His_aof & Haof & #Hdurablelb)".
    wp_storeField.

    iApply "HΦ".
    iModIntro.
    iFrame "HQ".
    repeat iExists _.
    iFrame "∗#%".
    iSplitR; first done.
    iSplitR; first iPureIntro.
    {
      replace (snap_sl.(Slice.sz)) with (W64 (length snap)); last first.
      { word. }
      rewrite app_nil_l.
      rewrite -app_assoc.
      unshelve (epose proof (file_encodes_state_snapshot snap [] 0 _ Hsnapenc)  as H; done).
      simpl; lia.
    }
    iSplitL; first done.
    iPureIntro.
    rewrite replicate_length.
    unfold n.
    done.
  }

  (* case: file is non-empty, so we have to recovery from it *)
  iDestruct "Hnonempty" as (???) "[%Henc HP]".

  iMod (fmlist_alloc (replicate (length data + 1) (ops, sealed))) as (γsl_state) "Hallstates".
  iMod (fmlist_alloc ops) as (γproposed) "Hops_proposed".
  set (γ:={| sl_state := γsl_state ; proposed_gn := γproposed |} ).

  iMod (fmlist_get_lb with "Hallstates") as "[Hallstates #Hlb]".
  iMod (fmlist_get_lb with "Hops_proposed") as "[Hops_proposed #Hprop_lb]".
  iDestruct (fmlist_lb_to_idx _ _ (length data) with "Hlb") as "#Hcurstate".
  {
    apply lookup_replicate.
    split; last lia.
    done.
  }

  wpc_apply (wpc_FileRead with "[$Hfile]").
  iSplit.
  { (* case: crash while reading *)
    iIntros "Hfile".
    iSplitR; first done.
    iModIntro.
    iExists _; iFrame.
    iNext.
    iRight.
    iExists _, _, _; iFrame "∗%".
  }
  (* otherwise, no crash and we keep going *)
  iDestruct ("Hinit_upd" with "HP") as "#HQ".
  iNext.
  iIntros (data_sl) "[Hfile Hdata_sl]".
  iExists (fname f↦data ∗ file_inv γ P epoch data)%I.
  iSplitL "Hfile HP".
  {
    iFrame "∗#%".
  }
  iSplit.
  {
    iModIntro.
    iIntros "[Hfile Hinv]".
    iModIntro.
    iExists _; iFrame "Hfile".
    iNext.
    iDestruct "Hinv" as (??) "(H1 & H2 & _)".
    iRight.
    iExists _, _, _.
    iFrame.
  }
  iIntros "Hfile_ctx".
  iSplit; first done.

  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_load.

  iDestruct (own_slice_sz with "Hdata_sl") as %Hdata_sz.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_if_destruct.
  { (* bad case *)
    exfalso.
    apply file_encodes_state_nonempty in Henc.
    rewrite Heqb in Hdata_sz.
    assert (length data = 0%nat) by done.
    word.
  }

  wp_apply (wp_CreateAppendOnlyFile with "[] [$Hfile_ctx]").
  {
    iModIntro.
    iIntros (?) "Hinv".
    iModIntro.
    iNext.
    iDestruct "Hinv" as (??) "(H1 & H2 & _)".
    iRight.
    iExists _, _, _.
    iFrame.
  }
  iIntros (aof_ptr γaof) "(His_aof & Haof & #Hdurablelb)".
  wp_storeField.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (snapLen_ptr) "HsnapLen".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (snap_ptr) "Hsnap".
  wp_pures.
  wp_load.
  iDestruct (own_slice_to_small with "Hdata_sl") as "Hdata_sl".
  pose proof Henc as Henc2.
  destruct Henc as (snap_ops & snap & rest_ops & rest_ops_bytes & sealed_bytes & Henc).
  destruct Henc as (Hops & Hsnap_enc & Hsealedbytes & Hrest_ops_len & Henc).
  destruct Henc as (Hop_bytes & Hops_len & HdataEnc).
  rewrite HdataEnc.

  wp_apply (wp_ReadInt with "[$Hdata_sl]").
  iIntros (data_sl2) "Hdata_sl".
  wp_pures.
  wp_store.
  wp_store.
  wp_load.
  wp_load.
  iDestruct "Hdata_sl" as "[Hdata_sl Hdata_sl2]".

  assert (uint.nat (length snap) = length snap) as HsnapNoOverflow.
  { rewrite HdataEnc in Hdata_sz. rewrite ?app_length in Hdata_sz. word. }
  wp_apply (wp_SliceSubslice_small with "Hdata_sl").
  {
    rewrite app_length.
    split.
    { word. }
    { word. }
  }
  iIntros (snap_sl) "Hsnap_sl".
  rewrite -> subslice_drop_take by word.
  rewrite drop_0.
  rewrite Nat.sub_0_r.
  replace (uint.nat (length snap)) with (length snap).
  rewrite take_app_length.
  wp_store.

  wp_load.
  wp_apply (wp_slice_len).
  wp_pures.
  iDestruct (own_slice_small_sz with "Hdata_sl2") as %Hdata_sl2_sz.
  wp_load.
  wp_load.

  wp_apply (wp_SliceSubslice_small with "Hdata_sl2").
  {
    rewrite -Hdata_sl2_sz.
    split.
    {
      rewrite app_length.
      word.
    }
    { word. }
  }
  iIntros (data_sl3) "Hdata_sl".

  rewrite -Hdata_sl2_sz.
  rewrite -> subslice_drop_take; last first.
  {
    rewrite app_length; word.
  }
  replace (uint.nat (length snap)) with (length snap).
  rewrite drop_app_length.
  iEval (rewrite app_length) in "Hdata_sl".
  replace (length snap +
                     length
                       (u64_le epoch ++
                        u64_le (length snap_ops) ++ concat rest_ops_bytes ++ sealed_bytes) - length snap)%nat with (
                     length
                       (u64_le epoch ++
                        u64_le (length snap_ops) ++ concat rest_ops_bytes ++ sealed_bytes))
    by word.
  rewrite take_ge; last first.
  {
    done.
  }
  wp_store.

  wp_load.

  wp_apply (wp_ReadInt with "Hdata_sl").
  iIntros (data_sl4) "Hdata_sl".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_apply (wp_ReadInt with "Hdata_sl").
  iIntros (data_sl5) "Hdata_sl".
  wp_pures.
  wp_storeField.
  wp_store.

  iMod (readonly_alloc (own_slice_small snap_sl byteT (DfracOwn 1) snap) with "[Hsnap_sl]") as "#Hsnap_sl".
  {
    simpl.
    iFrame.
  }

  iAssert (_) with "HisMemSm" as "#HisMemSm2".
  iNamed "HisMemSm2".
  wp_loadField.
  wp_load.
  wp_loadField.
  wp_loadField.
  wp_apply ("HsetState_spec" with "[$Hmemstate $Hsnap_sl]").
  { iPureIntro; split; try done.
    subst. rewrite app_length in Hops_len. word.
  }
  iIntros "Hmemstate".
  wp_pures.

  (* loop invariant *)
  iAssert (
      ∃ rest_ops_sl (numOpsApplied:nat) q,
      "Henc" ∷ enc_ptr ↦[slice.T byteT] (slice_val rest_ops_sl) ∗
      "Hdata_sl" ∷ own_slice_small rest_ops_sl byteT (DfracOwn q) (concat (drop numOpsApplied rest_ops_bytes) ++ sealed_bytes) ∗
      "Hmemstate" ∷ own_InMemoryStateMachine (snap_ops ++ (take numOpsApplied rest_ops)) ∗
      "HnextIndex" ∷ s ↦[StateMachine :: "nextIndex"] #(length snap_ops + numOpsApplied)%nat ∗
      "%HnumOpsApplied_le" ∷ ⌜numOpsApplied <= length rest_ops⌝
    )%I with "[Henc Hdata_sl Hmemstate nextIndex]" as "HH".
  {
    iExists _, 0%nat, _.
    iFrame.
    rewrite take_0.
    rewrite app_nil_r.
    rewrite Nat.add_0_r.
    iFrame.
    iPureIntro.
    word.
  }

  wp_forBreak.
  iNamed "HH".
  wp_pures.

  wp_load.
  iDestruct (own_slice_small_sz with "Hdata_sl") as %Hrest_data_sz.
  wp_apply (wp_slice_len).
  wp_if_destruct.
  { (* there's enough bytes to make up an entire operation *)
    wp_apply (wp_ref_of_zero).
    { done. }
    iIntros (opLen) "HopLen".
    wp_pures.
    wp_load.

    destruct (drop numOpsApplied rest_ops_bytes) as [ | nextOp_bytes new_rest_ops_bytes] eqn:X.
    {
      exfalso.
      simpl in Hrest_data_sz.
      assert (1 < length sealed_bytes) by word.
      rewrite Hsealedbytes /= in H.
      destruct sealed.
      { simpl in H. lia. }
      { simpl in H. lia. }
    }
    assert (length rest_ops_bytes <= numOpsApplied ∨ numOpsApplied < length rest_ops) as [Hbad | HappliedLength] by word.
    {
      exfalso.
      rewrite -X in Hrest_data_sz.
      assert (length rest_ops_bytes ≤ numOpsApplied)%nat by word.
      rewrite drop_ge /= in Hrest_data_sz; last done.
      assert (1 < length sealed_bytes) by word.
      rewrite Hsealedbytes in H0.
      destruct sealed.
      { simpl in H0; lia. }
      { simpl in H0; lia. }
    }

    specialize (Hop_bytes numOpsApplied HappliedLength).
    destruct Hop_bytes as (op & op_len_bytes & op_bytes & Hop_bytes).
    destruct Hop_bytes as (Hrest_ops_lookup & Hrest_ops_bytes_lookup & Henc & Hoplenbytes).

    replace (nextOp_bytes) with (u64_le (length op_bytes) ++ op_bytes); last first.
    {
      erewrite drop_S  in X; eauto.
      inversion X; subst; auto.
    }
    iEval (rewrite concat_cons) in "Hdata_sl".
    rewrite -app_assoc.
    rewrite -app_assoc.
    wp_apply (wp_ReadInt with "[$Hdata_sl]").
    iIntros (rest_ops_sl2) "Hdata_sl".
    wp_pures.
    wp_store.
    wp_store.
    wp_load.
    wp_load.

    (* split the slice into two parts; copy/pasted from above *)
    iDestruct "Hdata_sl" as "[Hdata_sl Hdata_sl2]".
    assert (uint.nat (length op_bytes) = length op_bytes).
    { apply (take_drop_middle) in Hrest_ops_bytes_lookup.
      rewrite -Hrest_ops_bytes_lookup ?concat_app in HdataEnc.
      rewrite HdataEnc in Hdata_sz. clear -Hdata_sz. rewrite ?app_length in Hdata_sz.
      word.
    }
    wp_apply (wp_SliceSubslice_small with "Hdata_sl").
    {
      rewrite app_length.
      split.
      { word. }
      { word. }
    }
    iIntros (op_sl) "Hop_sl".
    rewrite -> subslice_drop_take by word.
    rewrite drop_0.
    rewrite Nat.sub_0_r.
    replace (uint.nat (length op_bytes)) with (length op_bytes).
    rewrite take_app_length.

    wp_pures.
    wp_load.
    wp_apply (wp_slice_len).
    wp_pures.
    wp_load.
    wp_load.

    clear Hdata_sl2_sz.
    iDestruct (own_slice_small_sz with "Hdata_sl2") as %Hdata_sl2_sz.
    wp_apply (wp_SliceSubslice_small with "Hdata_sl2").
    {
      rewrite -Hdata_sl2_sz.
      split.
      {
        rewrite app_length.
        word.
      }
      { word. }
    }
    iIntros (rest_ops_sl3) "Hdata_sl".
    wp_store.
    wp_loadField.
    wp_loadField.

    rewrite -Hdata_sl2_sz.
    rewrite -> subslice_drop_take; last first.
    {
      rewrite app_length; word.
    }
    replace (uint.nat (length op_bytes)) with (length op_bytes).
    rewrite drop_app_length.
    iEval (rewrite app_length) in "Hdata_sl".
    replace ((length op_bytes + length (concat new_rest_ops_bytes ++ sealed_bytes) -
                     length op_bytes))%nat with
      (length (concat new_rest_ops_bytes ++ sealed_bytes)) by word.
    iEval (rewrite take_ge) in "Hdata_sl"; last first.
    (* done splitting slices into two parts *)

    iMod (readonly_alloc (own_slice_small op_sl byteT (DfracOwn 1) op_bytes) with "[Hop_sl]") as "#Hop_sl".
    {
      simpl.
      iFrame.
    }
    wp_apply ("HapplyVolatile_spec" with "[$Hmemstate $Hop_sl]").
    { done. }
    iIntros (? ?) "(_ & Hmemstate & _)".
    wp_pures.
    wp_loadField.
    wp_apply (std_proof.wp_SumAssumeNoOverflow).
    iIntros (HnextIndexOverflow).
    wp_storeField.
    iModIntro.
    iLeft.
    iSplitR; first done.
    iFrame "Hsnap HsnapLen Haof HΦ fname logFile logsize sealed epoch smMem His_aof Hallstates Hops_proposed".
    iExists _, (numOpsApplied + 1)%nat, (q/2)%Qp.
    iFrame.
    iSplitL "Hdata_sl".
    {
      iApply to_named.
      iExactEq "Hdata_sl".
      f_equal.
      f_equal.
      rewrite -drop_drop.
      rewrite X.
      rewrite skipn_cons.
      rewrite drop_0.
      done.
    }
    iSplitL "Hmemstate".
    {
      iApply to_named.
      iExactEq "Hmemstate".
      f_equal.
      rewrite -app_assoc.
      f_equal.
      rewrite (take_more); last first.
      { word. }
      f_equal.
      apply list_eq.
      intros.
      destruct i.
      {
        simpl.
        rewrite lookup_take; last lia.
        rewrite lookup_drop.
        rewrite Nat.add_0_r.
        done.
      }
      {
        simpl.
        rewrite lookup_take_ge; last lia.
        done.
      }
    }
    iSplitL "HnextIndex".
    {
      iApply to_named.
      iExactEq "HnextIndex".

      repeat f_equal.
      apply word.unsigned_inj; auto.
      rewrite ?word.unsigned_add /=.
      rewrite -[a in a = _]unsigned_U64.
      f_equal.
      replace (Z.of_nat (length snap_ops + (numOpsApplied + 1)))%Z with
        (Z.of_nat (length snap_ops + numOpsApplied) + uint.Z (W64 1))%Z; last first.
      { replace (uint.Z 1%Z) with 1%Z.
        { clear. f_equal. lia. }
        rewrite //=.
      }
      clear.
      remember (Z.of_nat (length snap_ops + numOpsApplied)) as x.
      { rewrite /W64.
        rewrite ?word.ring_morph_add. f_equal.
        rewrite word.of_Z_unsigned. auto.
      }
    }
    iPureIntro.
    word.
  }
  (* done with loop *)
  assert (numOpsApplied = length rest_ops_bytes ∨ numOpsApplied < length rest_ops) as [ | Hbad] by word.
  2:{
    exfalso.
    assert (length (drop numOpsApplied rest_ops_bytes) > 0).
    { rewrite drop_length. lia. }
    edestruct (Hop_bytes (numOpsApplied)) as (op&op_len_bytes&op_bytes&Hlookup1&Hlookup2&Henc&Hlen_bytes).
    { lia. }
    erewrite drop_S in Hrest_data_sz; eauto.
    rewrite /= ?app_length in Hrest_data_sz.
    rewrite Hlen_bytes u64_le_length in Hrest_data_sz.
    assert (uint.nat (rest_ops_sl.(Slice.sz)) <= 1).
    { word. }
    lia.
  }

  iDestruct (own_slice_small_sz with "Hdata_sl") as %Hdata_sl_sz.
  iRight.
  iModIntro.
  iSplitR; first done.
  wp_pures.
  wp_load.
  wp_apply (wp_slice_len).
  wp_if_destruct.
  { (* sealed = true *)
    wp_storeField.
    destruct sealed.
    2:{
      exfalso.
      rewrite List.skipn_all /= ?Hsealedbytes /= in Hdata_sl_sz; last by lia.
      word.
    }
    iApply "HΦ".
    iModIntro.
    iSplitL.
    {
      iClear "HQ".
      repeat iExists _.
      iSplitL "fname".
      { iFrame. }
      iFrame "∗".
      iFrame "#".
      rewrite take_ge; last word.
      iEval (rewrite H) in "HnextIndex".
      rewrite -Hrest_ops_len.
      iSplitL "HnextIndex".
      { repeat rewrite app_length. iFrame. }
      iSplitR.
      {
        iPureIntro.
        rewrite -HdataEnc.
        rewrite -Hops.
        done.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite -Hops.
        word.
      }
      rewrite -Hops.
      iFrame "∗#".
      rewrite replicate_length.
      iPureIntro.
      done.
    }
    { iExactEq "HQ".
      subst.
      repeat f_equal.
      rewrite firstn_all2.
      { done. }
      { word. }
    }
  }
  (* sealed = false *)
  wp_pures.
  destruct sealed.
  {
    exfalso.
    assert (uint.nat rest_ops_sl.(Slice.sz) = 0%nat).
    { assert (uint.Z 0 = 0%Z) as Heq_Z0 by auto.
      rewrite Heq_Z0 in Heqb1. word.
    }
    rewrite -Hdata_sl_sz in H0.
    rewrite app_length in H0.
    rewrite Hsealedbytes /= in H0.
    word.
  }

  iModIntro.
  iApply "HΦ".
  iSplitL.
  {
    repeat iExists _.
    iClear "HQ".
    iFrame "∗". iFrame "#".
    rewrite take_ge; last word.
    iEval (rewrite H) in "HnextIndex".
    rewrite -Hrest_ops_len.
    iSplitL "HnextIndex".
    { repeat rewrite app_length. iFrame. }
    iSplitR; first done.
    iSplitR.
    {
      iPureIntro.
      rewrite -HdataEnc.
      rewrite -Hops.
      done.
    }
    iSplitR.
    {
      iPureIntro.
      rewrite -Hops.
      word.
    }
    rewrite -Hops.
    iFrame "∗#".
    rewrite replicate_length.
    iPureIntro.
    done.
  }
  { iExactEq "HQ".
    subst.
    repeat f_equal.
    rewrite firstn_all2.
    { done. }
    { word. }
  }
Qed.

Lemma simplelog_accessP s P :
  ⊢ accessP_fact (own_StateMachine s) P
.
Proof.
  iModIntro.
  iIntros "Hlc" (????) "Hupd".
  iIntros "Hown".
  iNamed "Hown".
  iMod (accessP_weak with "His_aof Haof") as "HH".
  iDestruct "HH" as (?) "(_ & Hinv & Hclose)".
  iMod (lc_fupd_elim_later with "Hlc Hinv") as "Hinv".
  iDestruct "Hinv" as (??) "(% & HP & #? & #?)".
  iDestruct (fmlist_agree_2 with "Hops_proposed [$]") as %?.
  iMod ("Hupd" with "[//] HP") as "[HP Φ]".
  iMod ("Hclose" with "[HP]").
  {
    iNext. iExists _, _. iFrame "∗#%".
  }
  iModIntro.
  (* FIXME: without this unfold, iFrame takes forever..? *)
  unfold own_StateMachine, named.
  iFrame "HisMemSm Φ".

  iExists fname, _, γ, _, _, _, _.
  iFrame "∗#%".
Qed.

Definition simplelog_P γ γsrv := file_crash (own_Server_ghost_f γ γsrv).

Definition simplelog_pre γ γsrv fname :=
  (|C={⊤}=> ∃ data, fname f↦ data ∗ ▷ simplelog_P γ γsrv data)%I.

Lemma wp_MakePbServer smMem own_InMemoryStateMachine fname γ data γsrv confHosts confHosts_sl me :
  let P := (own_Server_ghost_f γ γsrv) in
  {{{
       "#Hinvs" ∷ is_pb_host me γ γsrv ∗
       "#HisConfHost" ∷ config_protocol_proof.is_pb_config_hosts confHosts γ ∗
       "#Hconf_sl" ∷ readonly (own_slice_small confHosts_sl uint64T (DfracOwn 1) confHosts) ∗
       "Hfile_ctx" ∷ crash_borrow (fname f↦ data ∗ file_crash P data)
                    (|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ file_crash P data') ∗
       "#HisMemSm" ∷ is_InMemoryStateMachine (sm_record:=pb_record) smMem own_InMemoryStateMachine ∗
       "Hmemstate" ∷ own_InMemoryStateMachine []
  }}}
    MakePbServer #smMem #(LitString fname) (slice_val confHosts_sl)
  {{{
        s, RET #s; is_Server s γ γsrv
  }}}
.
Proof.
  iIntros (?).
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".

  wp_lam.
  wp_apply (wp_recoverStateMachine with "[-HΦ]").
  { iFrame "∗#".
    iIntros (???) "HP".
    subst.
    iNamed "HP".
    iDestruct (ghost_get_accepted_lb with "Hghost") as "#H".
    iModIntro.
    instantiate (1:=(λ epoch ops _, ∃ opsfull, ⌜ops = get_rwops opsfull⌝ ∗ is_accepted_lb γsrv.(r_pb) epoch opsfull)%I).
    simpl.
    iExists _; iFrame "#%".
  }
  iIntros (????) "[Hsm HQ]".
  wp_pures.
  iDestruct "HQ" as (?) "[% #Hacc_lb]".
  subst.

  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (sm) "HpbSm".
  iDestruct (struct_fields_split with "HpbSm") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "StartApply") as "#HstartApply".
  iMod (readonly_alloc_1 with "GetStateAndSeal") as "#HgetState".
  iMod (readonly_alloc_1 with "SetStateAndUnseal") as "#HsetState".
  iMod (readonly_alloc_1 with "ApplyReadonly") as "#HapplyReadonly".

  iNamed "Hsm".
  wp_loadField.
  wp_loadField.
  wp_loadField.

  iAssert (own_StateMachine s epoch (get_rwops opsfull) sealed P) with "[-HΦ]" as "Hsm".
  {
    repeat iExists _.
    iFrame "∗#%".
  }

  wp_apply (wp_MakeServer _ (own_StateMachine s)  with "[$Hsm]").
  {
    iFrame "#%".
    iSplitL; last first.
    {
      iPureIntro.
      destruct Henc as (?&?&?&?&?&?). word.
    }
    iExists _, _, _, _. unfold named.
    rewrite -simplelog_accessP.
    iFrame "#".
    iSplitL.
    { (* apply spec *)
      clear Φ.
      iIntros (?????? Φ) "!#".
      iIntros "(%HopEncoding & #Hop_sl & Hupd & Hsm) HΦ".
      wp_lam.
      wp_apply (wp_StateMachine__apply with "[$Hsm $Hop_sl Hupd]").
      {
        iFrame "%".
        instantiate (1:=Q).
        iIntros "H1 H2".
        iMod ("Hupd" with "H1 H2").
        iModIntro. iFrame.
      }
      iFrame.
    }
    iSplitL.
    { (* set state spec *)
      clear Φ.
      iIntros (???????? Φ) "!#".
      iIntros "(%HsnapLen & %HopEncoding & #Hop_sl & Hupd & Hsm) HΦ".
      wp_lam.
      wp_pures.
      wp_apply (wp_setStateAndUnseal with "[$Hsm $Hop_sl Hupd]").
      {
        iFrame "%".
        iSplitR.
        { iPureIntro. word. }
        iIntros "H1".
        instantiate (1:=Q).
        iMod (fupd_mask_subseteq _) as "Hmask".
        2:{ iMod ("Hupd" with "H1"). iMod "Hmask". iModIntro. iFrame. }
        solve_ndisj.
      }
      iIntros.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame.
    }
    iSplitL.
    { (* get state spec *)
      clear Φ.
      iIntros (???? Φ) "!#".
      iIntros "(Hsm & Hupd) HΦ".
      wp_lam.
      wp_pures.
      wp_apply (wp_getStateAndSeal with "[$Hsm Hupd]").
      {
        iFrame "%".
        instantiate (1:=Q).
        iIntros "H1".
        iMod ("Hupd" with "H1").
        iModIntro. iFrame.
      }
      iIntros.
      iApply "HΦ".
      iFrame.
    }
    iSplitL.
    {
      clear Φ.
      iIntros (?????? Φ) "!#".
      iIntros "(%Hop_enc & #Hop_sl & Hsm)  HΦ".
      wp_lam.
      wp_pures.
      wp_apply (wp_StateMachine__applyReadonly with "[$Hsm]").
      { iFrame "#%". }
      iIntros.
      iApply "HΦ".
      iFrame.
    }
    {
      done.
    }
  }
  done.
Qed.

End local_proof.
