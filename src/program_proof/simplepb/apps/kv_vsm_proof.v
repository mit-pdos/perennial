From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import kv.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From iris.algebra Require Import mono_list.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From Perennial.program_proof Require Import map_string_marshal_proof.
From Perennial.program_proof.aof Require Import proof.
From Perennial.program_proof.simplepb Require Import config_proof.
From Perennial.program_proof.simplepb.apps Require Import vsm log.
From Perennial.program_proof.fencing Require Import map.

Section defns.

Inductive kvOp :=
  | putOp : string → string → kvOp
  | getOp : string → kvOp
.

Definition apply_op (state:gmap string string) (op:kvOp) :=
  match op with
    | getOp _ => state
    | putOp k v => <[k:=v]> state
  end
.

Definition compute_state ops : gmap string string :=
  foldl apply_op ∅ ops.

Definition compute_reply ops op : list u8 :=
  match op with
    | getOp k => string_to_bytes (default "" ((compute_state ops) !! k))
    | putOp k v => []
  end
.

Definition encode_op op : list u8 :=
  match op with
    | putOp k v => [U8 0] ++ u64_le (length (string_to_bytes k)) ++
                         string_to_bytes k ++ string_to_bytes v
    | getOp k => [U8 1] ++ string_to_bytes k
  end
.

Definition is_readonly_op (op:kvOp) :=
  match op with
    | getOp _ => True
    | _ => False
  end
.

Instance op_eqdec : EqDecision kvOp.
Proof. solve_decision. Qed.

Definition kv_record : Sm.t :=
  {|
    Sm.OpType := kvOp ;
    Sm.has_op_encoding := λ op_bytes op, encode_op op = op_bytes ;
    Sm.has_snap_encoding := λ snap_bytes ops, has_string_map_encoding snap_bytes (compute_state ops) ;
    Sm.compute_reply :=  compute_reply ;
    Sm.is_readonly_op :=  is_readonly_op ;
    Sm.apply_postcond :=  λ ops op, True ;
  |}.

End defns.

Section local_proof.

Notation OpType := (Sm.OpType kv_record).
Notation has_op_encoding := (Sm.has_op_encoding kv_record).
(* Notation compute_reply := (pb_compute_reply pb_record). *)
Notation pbG := (pbG (pb_record:=kv_record)).
Notation is_ApplyFn := (is_ApplyFn (pb_record:=kv_record)).
Notation is_pb_host := (is_pb_host (pb_record:=kv_record)).

Context `{!heapGS Σ}.

Lemma wp_encodePutArgs (args_ptr:loc) (key val:string) :
  {{{
      "Hargs_key" ∷ args_ptr ↦[kv.PutArgs :: "Key"] #(str key) ∗
      "Hargs_val" ∷ args_ptr ↦[kv.PutArgs :: "Val"] #(str val)
  }}}
    kv.encodePutArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜ has_op_encoding enc (putOp key val)⌝ ∗
        own_slice enc_sl byteT 1 enc
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
  iDestruct (own_slice_small_acc with "Hbuf") as "[Hbuf Hbufclose]".
  wp_apply (wp_SliceSet with "[$Hbuf]").
  { iPureIntro. done. }
  iEval simpl.
  change (<[int.nat 0%Z:=U8 0]> (replicate (int.nat 1%Z) (U8 0))) with [U8 0].
  iIntros "Hbuf". iDestruct ("Hbufclose" with "Hbuf") as "Hbuf".
  wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "Hbuf"). iIntros (sl) "Hbuf". wp_store. clear ptr.
  wp_loadField.
  wp_apply wp_StringToBytes.
  iIntros (?) "Hsl".
  wp_load.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_WriteBytes with "[$Hbuf $Hsl]").
  iIntros (sl') "[Hbuf _]".
  wp_store. clear sl.
  wp_loadField.
  wp_apply wp_StringToBytes.
  iIntros (?) "Hsl".
  wp_load.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_WriteBytes with "[$Hbuf $Hsl]").
  iIntros (?) "[Hbuf _]".
  wp_store. clear sl.
  wp_load.
  iApply "HΦ". iModIntro. iFrame.
  iPureIntro.
  by rewrite string_bytes_length.
Qed.

Lemma wp_decodePutArgs enc_sl enc q (key val:string) :
  {{{
        "%Henc" ∷ ⌜has_op_encoding enc (putOp key val)⌝ ∗
        "Hsl" ∷ own_slice_small enc_sl byteT q enc
  }}}
    kv.decodePutArgs (slice_val enc_sl)
  {{{
        (args_ptr:loc), RET #args_ptr;
        "Hargs_key" ∷ args_ptr ↦[kv.PutArgs :: "Key"] #(str key) ∗
        "Hargs_val" ∷ args_ptr ↦[kv.PutArgs :: "Val"] #(str val)
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iNamed "Hpre".
  wp_call.

  (* IDEA: maybe get rid of redundancy in slice length by having the slice object be
     (own_slice_small byteT slptr cap l)
     (slice_val sl_ptr lst).
     So instead of an arbitrary `enc_sl`, we should really have `Slice.mk
     enc_ptr (length enc) enc_cap`, but written more compactly.
   *)
  iDestruct (own_slice_small_sz with "Hsl") as %Hsl_sz.
  cbn in Henc.
  subst.
  wp_apply wp_SliceSkip.
  { cbn in Hsl_sz. word. }
  iDestruct (slice_small_split _ 1 with "Hsl") as "[_ Hsl]".
  { cbn. word. }
  rewrite skipn_cons drop_0.
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
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (?) "Hl".
  wp_load.
  wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (kv_sl) "Hkv_sl".
  wp_pures. wp_store. wp_store. wp_load. wp_load.
  iDestruct (own_slice_small_wf with "Hkv_sl") as %Hkv_wf.
  iDestruct (own_slice_small_sz with "Hkv_sl") as %Hkv_sz.
  simpl in Hsl_sz. rewrite app_length in Hkv_sz.
  wp_apply wp_SliceTake.
  { word. }
  iDestruct (slice_small_split with "Hkv_sl") as "[Hk Hv]".
  { shelve. }
  replace (int.nat (length (string_to_bytes key))) with (length (string_to_bytes key)) by word.
  Unshelve.
  2:{ rewrite app_length. word. }
  wp_apply (wp_StringFromBytes with "[$Hk]").
  iIntros "Hk".
  rewrite take_app.
  wp_storeField.
  rewrite drop_app.
  wp_load.
  wp_load.
  wp_apply wp_SliceSkip.
  { word. }
  wp_apply (wp_StringFromBytes with "[$Hv]").
  iIntros "Hv".
  do 2 rewrite string_to_bytes_inj.
  wp_storeField.
  iModIntro. iApply "HΦ".
  iFrame.
Qed.

Lemma wp_encodeGetArgs (key:string) :
  {{{
        True
  }}}
    kv.encodeGetArgs #(str key)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_op_encoding enc (getOp key)⌝ ∗
        own_slice enc_sl byteT 1 enc
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
  iDestruct (own_slice_small_acc with "Hbuf") as "[Hbuf Hbufclose]".
  wp_apply (wp_SliceSet with "[$Hbuf]").
  { iPureIntro. done. }
  iEval simpl.
  change (<[int.nat 0%Z:=U8 1]> (replicate (int.nat 1%Z) (U8 0))) with [U8 1].
  iIntros "Hbuf". iDestruct ("Hbufclose" with "Hbuf") as "Hbuf".
  wp_apply wp_StringToBytes.
  iIntros (?) "Hsl".
  wp_load.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_WriteBytes with "[$Hbuf $Hsl]").
  iIntros (?) "[Hbuf _]". wp_store. clear ptr.
  wp_load.
  iApply "HΦ". iModIntro. iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_decodeGetArgs enc_sl enc q (key:string) :
  {{{
        "%Henc" ∷ ⌜has_op_encoding enc (getOp key)⌝ ∗
        "Hsl" ∷ own_slice_small enc_sl byteT q enc
  }}}
    kv.decodeGetArgs (slice_val enc_sl)
  {{{
        RET #(str key); True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iNamed "Hpre".
  wp_call.
  cbn in Henc. subst.
  iDestruct (own_slice_small_sz with "Hsl") as %Hsl_sz.
  wp_apply wp_SliceSkip.
  { simpl in Hsl_sz. word. }
  iDestruct (slice_small_split _ 1 with "Hsl") as "[_ Hsl]".
  { simpl. word. }
  rewrite skipn_cons drop_0.
  wp_apply (wp_StringFromBytes with "[$]").
  iIntros "_".
  wp_pures.
  rewrite string_to_bytes_inj.
  by iApply "HΦ".
Qed.

Notation is_state := (is_state (sm_record:=kv_record)).

Context `{!vsmG (sm_record:=kv_record) Σ}.

Definition own_KVState (s:loc) γst (ops:list OpType) (latestVnum:u64) : iProp Σ :=
  ∃ (kvs_loc vnums_loc:loc) (vnumsM:gmap string u64) (minVnum:u64),
  "Hkvs" ∷ s ↦[KVState :: "kvs"] #kvs_loc ∗
  "Hvnums" ∷ s ↦[KVState :: "vnums"] #vnums_loc ∗
  "HminVnum" ∷ s ↦[KVState :: "minVnum"] #minVnum ∗
  "Hkvs_map" ∷ own_map kvs_loc 1 (compute_state ops) ∗
  "Hvnums_map" ∷ own_map vnums_loc 1 vnumsM ∗
  "#Hst" ∷ □ (∀ (k:string),
              (∀ (vnum':u64), ⌜int.nat vnum' <= int.nat latestVnum⌝ →
                             ⌜int.nat (default minVnum (vnumsM !! k)) <= int.nat vnum'⌝ →
              ∃ someOps, is_state γst vnum' someOps ∗
                      ⌜compute_reply someOps (getOp k) = compute_reply ops (getOp k)⌝)) ∗
  "%Hle" ∷ ⌜∀ (k:string), int.nat (default minVnum (vnumsM !! k)) <= int.nat latestVnum⌝
.

Implicit Type own_VersionedStateMachine : gname → (list OpType) → u64 → iProp Σ.

Lemma wp_KVState__apply s :
  {{{
        True
  }}}
    KVState__apply #s
  {{{
        applyFn, RET applyFn;
        ⌜val_ty applyFn (slice.T byteT -> (arrowT uint64T (slice.T byteT)))⌝ ∗
        is_Versioned_applyVolatileFn applyFn (own_KVState s)
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
  iIntros (??????? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "(%Henc & %Hvnum & #Hsl & Hown & #Hintermediate)".
  iNamed "Hown".
  wp_pures.
  iMod (readonly_load with "Hsl") as (?) "Hsl2".
  destruct op.
  { (* case: put op *)
    rewrite -Henc.
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_decodePutArgs with "[$Hsl2 //]").
    iIntros (?). iNamed 1.
    wp_pures.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapInsert with "[$]").
    { done. }
    iIntros "Hvnums_map".

    wp_pures.
    wp_call.
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapInsert_to_val with "[$Hkvs_map]").
    iIntros "Hkvs_map".
    wp_pures.

    wp_apply wp_NewSlice.
    iIntros (?) "Hnil".

    iApply "HΦ".
    iSplitL "Hkvs Hkvs_map Hvnums HminVnum Hvnums_map".
    {
      repeat iExists _; iFrame.
      unfold compute_state.
      rewrite foldl_snoc.
      iFrame.
      iSplitL.
      {
        iModIntro.
        iIntros.
        rewrite /typed_map.map_insert /= in H0.
        destruct (decide (k = s0)).
        { subst. rewrite lookup_insert /= in H0.
          replace (vnum) with (vnum') by word.
          iExists _. by iDestruct "Hintermediate" as "[_ $]".
        }
        assert (compute_reply (ops ++ [putOp s0 s1]) (getOp k) =
                  compute_reply (ops) (getOp k)) as Heq; last setoid_rewrite Heq.
        {
          rewrite /compute_reply /compute_state.
          rewrite foldl_snoc /=.
          by rewrite lookup_insert_ne.
        }
        rewrite lookup_insert_ne in H0; last done.
        destruct (decide (int.nat vnum' <= int.nat latestVnum)).
        { by iApply "Hst". }
        destruct (decide (int.nat vnum' = int.nat vnum)).
        { replace (vnum') with (vnum) by word.
          iExists _.
          iDestruct "Hintermediate" as "[_ $]".
          iPureIntro.
          by rewrite /compute_reply /compute_state foldl_snoc /= lookup_insert_ne.
        }
        {
          iDestruct "Hintermediate" as "[Hint _]".
          iSpecialize ("Hint" $! vnum' with "[%] [%]").
          { word. }
          { word. }
          iExists _. by iFrame "Hint".
        }
      }
      {
        iPureIntro. intros.
        destruct (decide (k = s0)).
        { subst.
          by rewrite /typed_map.map_insert lookup_insert /=.
        }
        {
          rewrite /typed_map.map_insert lookup_insert_ne /=; last done.
          transitivity (int.nat latestVnum).
          { apply Hle. }
          word.
        }
      }
    }
    simpl.
    rewrite replicate_0.
    iDestruct (own_slice_to_small with "Hnil") as "$".
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
    wp_apply (wp_decodeGetArgs with "[$Hsl2 //]").

    wp_loadField.
    wp_apply (wp_MapInsert with "[$]").
    { done. }
    iIntros "Hvnums_map".
    wp_pures.

    (* TODO: separate lemma *)
    wp_call.
    wp_loadField.
    wp_apply (wp_MapGet with "[$Hkvs_map]").
    iIntros (??) "[%Hlookup Hkvs_map]".
    wp_pures.
    wp_apply wp_StringToBytes.
    iIntros (?) "Hrep_sl".

    iApply "HΦ".
    iSplitL "Hkvs Hkvs_map Hvnums HminVnum Hvnums_map".
    {
      repeat iExists _; iFrame.
      unfold compute_state.
      rewrite foldl_snoc.
      iFrame.
      iSplitL.
      2: {
        iPureIntro. intros.
        destruct (decide (k = s0)).
        { subst.
          by rewrite /typed_map.map_insert lookup_insert /=. }
        { rewrite /typed_map.map_insert lookup_insert_ne /=; last done.
          transitivity (int.nat latestVnum).
          { apply Hle. }
          word. }
      }
      iModIntro.
      iIntros.
      rewrite /typed_map.map_insert /= in H0.
      destruct (decide (k = s0)).
      { subst. rewrite lookup_insert /= in H0.
        replace (vnum) with (vnum') by word.
        iExists _. by iDestruct "Hintermediate" as "[_ $]".
      }
      eassert (compute_reply (ops ++ [_]) (getOp k) =
                compute_reply (ops) (getOp k)) as Heq; last setoid_rewrite Heq.
      {
        rewrite /compute_reply /compute_state.
        rewrite foldl_snoc /=. done.
      }
      rewrite lookup_insert_ne in H0; last done.
      destruct (decide (int.nat vnum' <= int.nat latestVnum)).
      { by iApply "Hst". }
      destruct (decide (int.nat vnum' = int.nat vnum)).
      { replace (vnum') with (vnum) by word.
        iExists _.
        iDestruct "Hintermediate" as "[_ $]".
        iPureIntro.
        by rewrite /compute_reply /compute_state foldl_snoc /=.
      }
      {
        iDestruct "Hintermediate" as "[Hint _]".
        iSpecialize ("Hint" $! vnum' with "[%] [%]").
        { word. }
        { word. }
        iExists _. by iFrame "Hint".
      }
    }
    injection Hlookup as <- <-.
    iDestruct (own_slice_to_small with "Hrep_sl") as "$".
  }
Qed.

Lemma wp_KVState__applyReadonly s :
  {{{
        True
  }}}
    KVState__applyReadonly #s
  {{{
        applyReadonlyFn, RET applyReadonlyFn;
        ⌜val_ty applyReadonlyFn (slice.T byteT -> (prodT uint64T (slice.T byteT)))⌝ ∗
        is_Versioned_applyReadonlyFn applyReadonlyFn (own_KVState s)
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
  iIntros (?????? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "(%Hro & %Henc & #Hsl & Hown)".
  wp_pures.
  destruct op.
  { by exfalso. }
  rewrite /kv_record /= in Henc.
  rewrite <- Henc.
  iMod (readonly_load with "Hsl") as (?) "Hsl2".
  wp_apply (wp_SliceGet with "[$Hsl2]").
  { done. }
  iIntros "Hsl2".
  wp_pures.
  wp_apply (wp_decodeGetArgs with "[$Hsl2 //]").
  iNamed "Hown".
  wp_pures.
  wp_call.
  wp_loadField.
  wp_apply (wp_MapGet with "Hkvs_map").
  iIntros (??) "[%Hkv_lookup Hkvs_map]".
  wp_pures.
  wp_apply wp_StringToBytes.
  iIntros (?) "Hrep_sl".
  wp_loadField.
  wp_apply (wp_MapGet with "Hvnums_map").
  iIntros (??) "(%Hlookup & Hvnums_map)".
  wp_pures.
  wp_if_destruct.
  {
    wp_pures. iApply "HΦ". iModIntro.
    apply map_get_true in Hlookup.
    pose proof (Hle s0) as Hle2.
    rewrite Hlookup /= in Hle2.
    iSplitR. { iPureIntro. word. }
    injection Hkv_lookup as <- ?.
    iDestruct (own_slice_to_small with "Hrep_sl") as "$".
    rewrite /kv_record /compute_reply /compute_state /=.
    iSplitL.
    { repeat iExists _; iFrame "∗#%". }
    iSpecialize ("Hst" $! s0).
    rewrite Hlookup /=.
    iModIntro. iIntros.
    iApply "Hst".
    { iPureIntro. word. }
    { iPureIntro. word. }
  }
  {
    wp_loadField. wp_pures. iApply "HΦ". iModIntro.
    apply map_get_false in Hlookup as [Hlookup Hv].
    subst.
    pose proof (Hle s0) as Hle2.
    rewrite Hlookup /= in Hle2.
    iSplitR. { iPureIntro. word. }
    injection Hkv_lookup as <- ?.
    iDestruct (own_slice_to_small with "Hrep_sl") as "$".
    rewrite /kv_record /compute_reply /compute_state /=.
    iSplitL.
    { repeat iExists _; iFrame "∗#%". }
    iSpecialize ("Hst" $! s0).
    rewrite Hlookup /=.
    iModIntro. iIntros.
    iApply "Hst".
    { iPureIntro. word. }
    { iPureIntro. word. }
  }
Qed.

Lemma wp_KVState__setState s :
  {{{
        True
  }}}
    KVState__setState #s
  {{{
        setFn, RET setFn;
        ⌜val_ty setFn ((slice.T byteT) -> (arrowT uint64T unitT))%ht⌝ ∗
        is_Versioned_setStateFn setFn (own_KVState s)
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

  iIntros (???????? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "(%Hsnap & #Hsnap_sl & Hown & #HstNew)".
  wp_pures.

  iNamed "Hown".
  iMod (readonly_load with "Hsnap_sl") as (?) "Hsnap_sl2".
  wp_storeField.
  wp_apply (wp_NewMap string).
  iClear "Hvnums_map".
  iIntros (?) "Hvnums_map".
  wp_storeField.
  wp_apply (wp_DecodeStringMap with "[Hsnap_sl2]").
  {
    rewrite /kv_record.(Sm.has_snap_encoding) /= in Hsnap.
    iSplitR; first done.
    iApply to_named.
    iExactEq "Hsnap_sl2".
    f_equal.
    instantiate (1:=[]).
    rewrite app_nil_r.
    done.
  }
  iIntros (mptr) "Hmap".
  wp_storeField.
  iApply "HΦ".
  iModIntro. repeat iExists _; iFrame.
  iSplitR.
  { iModIntro. iIntros.
    assert (int.nat vnum' = int.nat vnum).
    { rewrite lookup_empty /= in H0. word. }
    replace (vnum) with vnum' by word.
    by iExists _; iFrame "HstNew". }
  iPureIntro. intros. rewrite lookup_empty /=. word.
Qed.

Lemma wp_KVState__getState (s:loc) :
  ⊢ is_Versioned_getStateFn (λ: <>, KVState__getState #s) (own_KVState s).
Proof.
  iIntros (??? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "Hown".
  wp_pures.
  wp_call.
  iNamed "Hown".
  wp_loadField.
  iApply wp_fupd.
  wp_apply (wp_EncodeStringMap with "Hkvs_map").
  iIntros (??) "(Hmap & Henc & %Henc)".
  iDestruct (own_slice_to_small with "Henc") as "Henc_sl".
  iMod (readonly_alloc_1 with "Henc_sl") as "#Henc_sl".
  iApply "HΦ".
  iModIntro.
  iFrame "#".
  iSplitL; last done.
  repeat iExists _; iFrame "∗#%".
Qed.

Notation is_InMemoryStateMachine := (is_InMemoryStateMachine (sm_record:=kv_record)).

Lemma wp_makeVersionedStateMachine :
  {{{
        True
  }}}
    makeVersionedStateMachine #()
  {{{
      sm own_MemStateMachine, RET #sm;
        is_VersionedStateMachine sm own_MemStateMachine ∗
        (∀ γst, is_state γst (U64 0) [] -∗ own_MemStateMachine γst [] (U64 0))
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
  wp_apply (wp_NewMap string).
  iIntros (?) "Hmap".
  wp_storeField.
  wp_apply (wp_NewMap string).
  iIntros (?) "Hvnums_map".
  wp_storeField.
  wp_apply (wp_KVState__apply).
  iIntros (?) "[% #His_apply]".
  wp_apply (wp_KVState__applyReadonly).
  iIntros (?) "[% #His_applyReadonly]".
  wp_apply (wp_KVState__setState).
  iIntros (?) "[% #His_setstate]".
  iApply wp_fupd.
  wp_apply (wp_allocStruct).
  {
    repeat econstructor; try done.
  }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "ApplyVolatile") as "#Happly".
  iMod (readonly_alloc_1 with "ApplyReadonly") as "#HapplyReadonly".
  iMod (readonly_alloc_1 with "GetState") as "#Hgetstate".
  iMod (readonly_alloc_1 with "SetState") as "#HsetState".
  iApply "HΦ".
  iSplitR.
  {
    repeat iExists _. iModIntro.
    iFrame "#". iApply wp_KVState__getState.
  }
  iModIntro.
  iIntros (?) "#?".
  repeat iExists _; iFrame.
  iSplitL.
  { iModIntro. iIntros. rewrite lookup_empty /= in H3.
    replace (int.nat (U64 0)) with (0) in * by word.
    assert (int.nat vnum' = int.nat 0) by word.
    replace (vnum') with (U64 0) by word.
    iExists _; by iFrame "#".
  }
  iPureIntro. intros. rewrite lookup_empty /= //.
Qed.

End local_proof.
