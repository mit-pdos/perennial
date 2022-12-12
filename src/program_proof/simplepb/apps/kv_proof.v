From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import kv64.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From Perennial.program_proof.simplepb Require Import pb_apply_proof clerk_proof.
From Perennial.program_proof Require Import map_marshal_proof.
From Perennial.program_proof.aof Require Import proof.
From Perennial.program_proof.simplepb Require Import config_proof.
From Perennial.program_proof.simplepb Require Import pb_init_proof.

Section global_proof.

Inductive kv64Op :=
  | putOp : u64 → list u8 → kv64Op
  | getOp : u64 → kv64Op
.

Definition apply_op (state:gmap u64 (list u8)) (op:kv64Op) :=
  match op with
    | getOp _ => state
    | putOp k v => <[k:=v]> state
  end
.

Definition compute_state ops : gmap u64 (list u8) :=
  foldl apply_op ∅ ops.

Definition compute_reply ops op : (list u8) :=
  match op with
    | getOp k => default [] ((compute_state ops) !! k)
    | putOp k v => []
  end
.

Definition encode_op op : list u8 :=
  match op with
    | getOp k => [U8 1] ++ u64_le k
    | putOp k v => [U8 0] ++ u64_le k ++ v
  end
.

Instance op_eqdec : EqDecision kv64Op.
Proof. solve_decision. Qed.

Definition kv_record : PBRecord :=
  {|
    pb_OpType := kv64Op ;
    pb_has_op_encoding := λ op_bytes op, encode_op op = op_bytes ;
    pb_has_snap_encoding := λ snap_bytes ops, has_byte_map_encoding snap_bytes (compute_state ops) ;
    pb_compute_reply :=  compute_reply ;
  |}.

Notation OpType := (pb_OpType kv_record).
Notation has_op_encoding := (pb_has_op_encoding kv_record).
(* Notation compute_reply := (pb_compute_reply pb_record). *)
Notation pbG := (pbG (pb_record:=kv_record)).
Notation is_ApplyFn := (is_ApplyFn (pb_record:=kv_record)).
Notation is_pb_host := (is_pb_host (pb_record:=kv_record)).

Class kv64G Σ := Kv64G {
  kv64_simplelogG :> simplelogG (sm_record:=kv_record) Σ ;
  kv64_ghostMapG :> ghost_mapG Σ u64 (list u8) ;
  kv64_configG :> configG Σ
}.
Definition kv64Σ := #[simplelogΣ (sm_record:=kv_record); configΣ; ghost_mapΣ u64 (list u8)].
Global Instance subG_kv64Σ {Σ} : subG kv64Σ Σ → kv64G Σ.
Proof. intros. solve_inG. Qed.

Context `{!gooseGlobalGS Σ}.
Context `{!kv64G Σ}.

Definition own_kvs (γkv:gname) ops : iProp Σ :=
  ghost_map_auth γkv 1 (compute_state ops)
.

Definition stateN := nroot .@ "state".

Definition kv_inv γ γkv : iProp Σ :=
  inv stateN ( ∃ ops, own_log γ ops ∗ own_kvs γkv ops).

Definition own_kv_server_pre_init γsrv := own_server_pre γsrv.
Definition is_kv_server_pre_init_witness γsrv : iProp Σ :=
  is_accepted_lb γsrv (U64 0) [] ∗ is_epoch_lb γsrv (U64 0).

Lemma kv_server_pre_initialize :
  ⊢ |==> ∃ γsrv,
      own_kv_server_pre_init γsrv ∗ is_kv_server_pre_init_witness γsrv
.
Proof.
  iMod (pb_ghost_server_pre_init) as (γsrv) "HH".
  iModIntro.
  iExists _; iFrame.
Qed.

Lemma kv_system_init confγs :
  length confγs > 0 →
  (∀ γsrv, ⌜γsrv ∈ confγs⌝ → is_kv_server_pre_init_witness γsrv)
           ={⊤}=∗
  ∃ γsys γlog γkv ,
    pb_init_config γsys confγs ∗
    is_inv γlog γsys ∗
    sys_inv γsys ∗
    kv_inv γlog γkv ∗
    is_proposal_lb γsys (U64 0) [] ∗
    is_proposal_facts γsys (U64 0) []
.
Proof.
  intros ?.
  iIntros "#Hpre".
  iMod (pb_system_init confγs with "[Hpre]") as (γsys) "(#Hsys & Hghost & Hpb_init)".
  { done. }
  {
    iIntros.
    iApply "Hpre".
    done.
  }
  iExists γsys.
  iMod (pb_init_log with "Hghost") as (γlog) "[Hlog #Hisinv]".
  iExists γlog.
  iMod (ghost_map_alloc ∅) as (γkv) "[Hkvs Hkvptsto]".
  iExists _.
  iFrame "#".
  iMod (inv_alloc with "[Hkvs Hlog]") as "$".
  { iNext. iExists _; iFrame. }
  by iFrame.
Qed.

Lemma kv_server_pre_init :
  ⊢ |==> ∃ γsrv,
      own_kv_server_pre_init γsrv ∗ is_kv_server_pre_init_witness γsrv
.
Proof.
  iMod (pb_ghost_server_pre_init) as (γsrv) "HH".
  iModIntro.
  iExists _; iFrame.
Qed.

Definition kv_ptsto γkv (k:u64) (v:list u8): iProp Σ :=
  k ↪[γkv] v.

End global_proof.

Section local_proof.

Notation OpType := (pb_OpType kv_record).
Notation has_op_encoding := (pb_has_op_encoding kv_record).
(* Notation compute_reply := (pb_compute_reply pb_record). *)
Notation pbG := (pbG (pb_record:=kv_record)).
Notation is_ApplyFn := (is_ApplyFn (pb_record:=kv_record)).
Notation is_pb_host := (is_pb_host (pb_record:=kv_record)).


Context `{!heapGS Σ}.
Context `{!kv64G Σ}.

Lemma wp_EncodePutArgs (args_ptr:loc) (key:u64) val val_sl :
  {{{
      "Hargs_key" ∷ args_ptr ↦[kv64.PutArgs :: "Key"] #key ∗
      "Hargs_val" ∷ args_ptr ↦[kv64.PutArgs :: "Val"] (slice_val val_sl) ∗
      "Hargs_val_sl" ∷ is_slice_small val_sl byteT 1 (val)
  }}}
    kv64.EncodePutArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_op_encoding enc (putOp key val)⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Proof.
  iIntros (Φ) "H1 HΦ".
  iNamed "H1".
  wp_call.
  wp_apply (wp_NewSliceWithCap (V:=u8)).
  { done. }
  iIntros (ptr) "Hbuf".
  wp_apply wp_ref_to; first by val_ty. iIntros (l) "Hl".
  wp_load.
  iDestruct (is_slice_small_acc with "Hbuf") as "[Hbuf Hbufclose]".
  wp_apply (wp_SliceSet with "[$Hbuf]").
  { iPureIntro. done. }
  iEval simpl.
  change (<[int.nat 0%Z:=U8 0]> (replicate (int.nat 1%Z) (U8 0))) with [U8 0].
  iIntros "Hbuf". iDestruct ("Hbufclose" with "Hbuf") as "Hbuf".
  wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "Hbuf"). iIntros (sl) "Hbuf". wp_store. clear ptr.
  wp_loadField. wp_load.
  wp_apply (wp_WriteBytes with "[$Hbuf $Hargs_val_sl]").
  iIntros (sl') "[Hbuf _]". (* FIXME we are throwing away the args_val_sl here? *)
  wp_store. clear sl.
  wp_load.
  iApply "HΦ". iModIntro. iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_EncodeGetArgs (key:u64) :
  {{{
        True
  }}}
    kv64.EncodeGetArgs #key
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_op_encoding enc (getOp key)⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Proof.
  iIntros (Φ) "H1 HΦ".
  iNamed "H1".
  wp_call.
  wp_apply (wp_NewSliceWithCap (V:=u8)).
  { done. }
  iIntros (ptr) "Hbuf".
  wp_apply wp_ref_to; first by val_ty. iIntros (l) "Hl".
  wp_load.
  iDestruct (is_slice_small_acc with "Hbuf") as "[Hbuf Hbufclose]".
  wp_apply (wp_SliceSet with "[$Hbuf]").
  { iPureIntro. done. }
  iEval simpl.
  change (<[int.nat 0%Z:=U8 1]> (replicate (int.nat 1%Z) (U8 0))) with [U8 1].
  iIntros "Hbuf". iDestruct ("Hbufclose" with "Hbuf") as "Hbuf".
  wp_load.
  wp_apply (wp_WriteInt with "Hbuf"). iIntros (sl) "Hbuf". wp_store. clear ptr.
  wp_load.
  iApply "HΦ". iModIntro. iFrame.
  iPureIntro.
  done.
Qed.

Definition own_Clerk ck γkv : iProp Σ :=
  ∃ (pb_ck:loc) γlog γsys,
    "Hown_ck" ∷ own_Clerk pb_ck γsys ∗
    "#Hpb_ck" ∷ readonly (ck ↦[kv64.Clerk :: "cl"] #pb_ck) ∗
    "#His_inv" ∷ is_inv γlog γsys ∗
    "#Hkvinv" ∷ kv_inv γlog γkv
.

Lemma wp_Clerk__Put ck γkv key val_sl value Φ:
  own_Clerk ck γkv -∗
  is_slice val_sl byteT 1 value -∗
  □(|={⊤∖↑pbN,↑stateN}=> ∃ old_value, kv_ptsto γkv key old_value ∗
    (kv_ptsto γkv key (value) ={↑stateN,⊤∖↑pbN}=∗
    (own_Clerk ck γkv -∗ Φ #()))) -∗
  WP Clerk__Put #ck #key (slice_val val_sl) {{ Φ }}.
Proof.
  iIntros "Hck Hval_sl #Hupd".
  wp_call.
  wp_pures.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
  iIntros (args) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  iDestruct (is_slice_to_small with "Hval_sl") as "Hval_sl".
  wp_apply (wp_EncodePutArgs with "[$Key $Val $Hval_sl]").
  iIntros (putEncoded put_sl) "[%Henc Henc_sl]".
  wp_loadField.

  wp_apply (wp_Clerk__Apply with "Hown_ck His_inv Henc_sl").
  { done. }

  (* make this a separate lemma? *)
  iModIntro.
  iMod "Hupd".

  iInv "Hkvinv" as ">Hown" "Hclose".
  replace (↑_∖_) with (∅:coPset); last set_solver.
  iModIntro.

  iDestruct "Hown" as (?) "[Hlog Hkvs]".
  iDestruct ("Hupd") as (?) "[Hkvptsto Hkvclose]".
  iExists _; iFrame "Hlog".
  iIntros "Hlog".

  iMod (ghost_map_update (value) with "Hkvs Hkvptsto") as "[Hkvs Hkvptsto]".

  iMod ("Hclose" with "[Hlog Hkvs]") as "_".
  {
    iExists _; iFrame.
    iNext.
    unfold own_kvs.
    unfold compute_state.
    rewrite foldl_snoc.
    simpl.
    iFrame.
  }
  iMod ("Hkvclose" with "Hkvptsto") as "HH".
  iModIntro.
  iIntros (?) "Hsl Hck".
  wp_pures.
  iApply "HH".
  iExists _, _, _.
  iFrame "∗#".
  iModIntro.
  done.
Qed.

Definition own_KVState (s:loc) (ops:list OpType) : iProp Σ :=
  ∃ (kvs_loc:loc),
  "Hkvs" ∷ s ↦[KVState :: "kvs"] #kvs_loc ∗
  "Hkvs_map" ∷ own_byte_map kvs_loc (compute_state ops)
.

Lemma wp_KVState__apply s :
  {{{
        True
  }}}
    KVState__apply #s
  {{{
        applyFn, RET applyFn;
        ⌜val_ty applyFn (slice.T byteT -> slice.T byteT)⌝ ∗
        is_InMemory_applyVolatileFn applyFn (own_KVState s)
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
  iNamed "Hown".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (ret) "Hret".
  wp_pures.
  wp_apply (wp_slice_len).
  iMod (readonly_load with "Hsl") as (?) "Hsl2".
  iDestruct (is_slice_small_sz with "Hsl2") as %Hsl_sz.
  destruct op.
  { (* case: put op *)
    rewrite -Henc.
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_SliceSubslice_small with "[$Hsl2]").
    { rewrite -Hsl_sz.
      rewrite -Henc.
      split; last done.
      rewrite app_length.
      simpl.
      word.
    }
    iIntros (putOp_sl) "Hop_sl".
    rewrite -Hsl_sz -Henc.
    rewrite -> subslice_drop_take; last first.
    { rewrite app_length. simpl. word. }
    rewrite app_length.
    rewrite singleton_length.
    unfold encode_op.
    replace (1 + length (u64_le u ++ l) - int.nat 1%Z) with (length (u64_le u ++ l)) by word.
    replace (int.nat (U64 1)) with (length [U8 0]) by done.
    rewrite drop_app.
    rewrite take_ge; last word.

    (* TODO: separate lemma *)
    wp_call.
    wp_apply (wp_ref_to).
    { done. }
    iIntros (enc_ptr) "Henc".
    wp_pures.
    wp_apply (wp_allocStruct).
    { Transparent slice.T. repeat econstructor. Opaque slice.T. }
    iIntros (args_ptr) "Hargs".
    iDestruct (struct_fields_split with "Hargs") as "HH".
    iNamed "HH".
    wp_pures.
    wp_load.
    wp_apply (wp_ReadInt with "[$Hop_sl]").
    iIntros (val_sl) "Hval_sl".
    wp_pures.
    wp_storeField.
    wp_storeField.
    (* TODO: end of separate lemma? *)

    wp_call.
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_byteMapPut with "[$Hkvs_map $Hval_sl]").
    iIntros "Hkvs_map".
    wp_pures.
    wp_apply (wp_NewSlice).
    iIntros (rep_sl) "Hrep_sl".
    wp_store.
    wp_load.
    iApply "HΦ".
    iModIntro.
    iSplitL "Hkvs Hkvs_map".
    {
      iExists _; iFrame.
      unfold compute_state.
      rewrite foldl_snoc.
      done.
    }
    simpl.
    iDestruct (is_slice_to_small with "Hrep_sl") as "$".
  }
  { (* case: get op *)
    wp_pures.
    rewrite -Henc.
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.

    wp_apply (wp_SliceSubslice_small with "[$Hsl2]").
    { rewrite -Hsl_sz.
      rewrite -Henc.
      split; last done.
      rewrite app_length.
      simpl.
      word.
    }
    iIntros (getOp_sl) "Hop_sl".
    rewrite -Hsl_sz -Henc.
    rewrite -> subslice_drop_take; last first.
    { rewrite app_length. simpl. word. }
    rewrite app_length.
    rewrite singleton_length.
    unfold encode_op.
    replace (1 + length (u64_le u) - int.nat 1%Z) with (length (u64_le u)) by word.
    replace (int.nat (U64 1)) with (length [U8 1]) by done.
    rewrite drop_app.
    rewrite take_ge; last word.

    (* TODO: separate lemma *)
    wp_call.
    wp_pures.
    wp_apply (wp_ReadInt with "Hop_sl").
    iIntros (?) "_".
    wp_pures.
    (* end separate lemma *)

    (* TODO: separate lemma *)
    wp_call.
    wp_loadField.
    wp_apply (wp_byteMapGet with "Hkvs_map").
    iIntros (rep_sl) "[#Hrep_sl Hkvs_map]".
    iMod (readonly_load with "Hrep_sl") as (?) "Hrep_sl2".
    wp_store.
    wp_load.
    iApply "HΦ".
    iModIntro.
    iFrame.
    iExists _ ; iFrame.
    unfold compute_state.
    rewrite foldl_snoc.
    done.
  }
Qed.

Lemma wp_KVState__setState s :
  {{{
        True
  }}}
    KVState__setState #s
  {{{
        setFn, RET setFn;
        ⌜val_ty setFn (slice.T byteT -> unitT)⌝ ∗
        is_InMemory_setStateFn setFn (own_KVState s)
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
  wp_apply (wp_DecodeMapU64ToBytes with "[Hsnap_sl2]").
  {
    rewrite /kv_record.(pb_has_snap_encoding) /= in Hsnap.
    iSplitR; first done.
    iApply to_named.
    iExactEq "Hsnap_sl2".
    f_equal.
    instantiate (1:=[]).
    rewrite app_nil_r.
    done.
  }
  iIntros (?? mptr) "(Hmap & _)".
  wp_pures.
  wp_storeField.
  wp_pures.
  iApply "HΦ".
  iModIntro. iExists _; iFrame.
Qed.

Lemma wp_KVState__getState (s:loc) :
  ⊢ is_InMemory_getStateFn (λ: <>, KVState__getState #s) (own_KVState s).
Proof.
  iIntros (? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "Hown".
  wp_pures.
  wp_call.
  iNamed "Hown".
  wp_loadField.
  iApply wp_fupd.
  wp_apply (wp_EncodeMapU64ToBytes with "Hkvs_map").
  iIntros (??) "(Hmap & Henc & %Henc)".
  iDestruct (is_slice_to_small with "Henc") as "Henc_sl".
  iMod (readonly_alloc_1 with "Henc_sl") as "#Henc_sl".
  iApply "HΦ".
  iModIntro.
  iFrame "#".
  iSplitL; last done.
  iExists _; iFrame.
Qed.

Notation is_InMemoryStateMachine := (is_InMemoryStateMachine (sm_record:=kv_record)).

Lemma wp_MakeKVStateMachine :
  {{{
        True
  }}}
    MakeKVStateMachine #()
  {{{
      sm own_MemStateMachine, RET #sm;
        is_InMemoryStateMachine sm own_MemStateMachine ∗
        own_MemStateMachine []
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_call.

  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
  iIntros (s) "Hs".
  iDestruct (struct_fields_split with "Hs") as "Hs".
  iNamed "Hs".
  wp_pures.
  wp_apply (wp_byteMapNew).
  iIntros (?) "Hmap".
  wp_storeField.
  wp_apply (wp_KVState__apply).
  iIntros (?) "[% #His_apply]".
  wp_apply (wp_KVState__setState).
  iIntros (?) "[% #His_setstate]".
  iApply wp_fupd.
  wp_apply (wp_allocStruct).
  {
    repeat econstructor; done.
  }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "ApplyVolatile") as "#Happly".
  iMod (readonly_alloc_1 with "GetState") as "#Hgetstate".
  iMod (readonly_alloc_1 with "SetState") as "#HsetState".
  iApply "HΦ".
  iSplitR "kvs Hmap".
  {
    iExists _, _, _.
    iModIntro.
    iFrame "#".
    iApply wp_KVState__getState.
  }
  iModIntro.
  iExists _.
  iFrame.
Qed.

Lemma wp_Start fname host γsys γsrv data :
  {{{
      "#Hhost" ∷ is_pb_host host γsys γsrv ∗
      "#Hinv" ∷ sys_inv γsys ∗
      "Hfile_ctx" ∷ crash_borrow (fname f↦ data ∗ file_crash (own_Server_ghost γsys γsrv) data)
                    (|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ file_crash (own_Server_ghost γsys γsrv) data')
  }}}
    Start #(LitString fname) #host
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_MakeKVStateMachine).
  iIntros (??) "[#HisSmMem Hmemstate]".
  wp_apply (wp_MakePbServer with "Hinv [$HisSmMem $Hmemstate $Hfile_ctx]").
  iIntros (?) "#Hsrv".
  wp_pures.
  wp_apply (pb_start_proof.wp_Server__Serve with "[$]").
  wp_pures.
  by iApply "HΦ".
Qed.

End local_proof.

Section local_init_proof.

Context `{!gooseGlobalGS Σ}.
Context `{!gooseLocalGS Σ}.
Context `{!kv64G Σ}.

Lemma kv_server_init fname γsys γsrv :
  fname f↦ [] -∗
  is_sys_init_witness γsys -∗
  own_kv_server_pre_init γsrv ={⊤}=∗
  fname f↦ [] ∗
  file_crash (own_Server_ghost γsys γsrv) [].
Proof.
  iIntros "Hfile #Hwit Hpre".
  iFrame "Hfile".
  iDestruct (pb_server_init with "Hwit Hpre") as "HH".
  iLeft.
  iFrame.
  done.
Qed.

End local_init_proof.
