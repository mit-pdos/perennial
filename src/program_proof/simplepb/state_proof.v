From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Import state.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_apply_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From Perennial.goose_lang Require Import crash_borrow.

Section state_proof.
Context `{!heapGS Σ}.

Definition compute_state ops : (gmap u64 (list u8)) :=
  foldl (λ m' op, <[op.1 := (default [] (m' !! op.1)) ++ op.2 ]>m') ∅ ops.

Program Definition pb_record : PBRecord :=
  {|
    pb_OpType := (u64 * list u8) ;
    pb_has_op_encoding := λ op_bytes op, (u64_le op.1 ++ op.2) = op_bytes ;
    pb_has_snap_encoding := λ snap_bytes ops , True ;
    pb_compute_reply :=  λ ops op, default [] ((compute_state ops) !! op.1) ;
  |}.
Obligation 1.
Admitted.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_op_encoding_injective := (pb_has_op_encoding_injective pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).
Notation is_ApplyFn := (is_ApplyFn (pb_record:=pb_record)).

Implicit Type σ : list (list u8).

Context `{!pbG Σ}.
Context `{!ghost_mapG Σ u64 (list u8)}.

Definition own_kvs (γkv:gname) ops : iProp Σ :=
  ghost_map_auth γkv 1 (compute_state ops)
.

Definition stateN := nroot .@ "state".

Definition sys_inv γ γkv : iProp Σ :=
  inv stateN ( ∃ ops, own_log γ ops ∗ own_kvs γkv ops).

Definition kv_ptsto γkv (k:u64) (v:list u8): iProp Σ :=
  k ↪[γkv] v.

Definition is_Clerk γ ck : iProp Σ :=
  ∃ (pb_ck:loc) γsys γsrv,
    "#Hpb_ck" ∷ readonly (ck ↦[state.Clerk :: "cl"] #pb_ck) ∗
    "#His_ck" ∷ is_Clerk pb_ck γsys γsrv ∗
    "#His_inv" ∷ is_inv γ γsys
.

Context `{!urpc_proof.urpcregG Σ}.
Context `{!stagedG Σ}.

Lemma wp_Clerk__FetchAndAppend ck γ γkv key val_sl value Φ:
  sys_inv γ γkv -∗
  is_Clerk γ ck -∗
  is_slice val_sl byteT 1 value -∗
  □((|={⊤∖↑pbN,↑stateN}=> ∃ old_value, kv_ptsto γkv key old_value ∗
    (kv_ptsto γkv key (old_value ++ value) ={↑stateN,⊤∖↑pbN}=∗
    (∀ reply_sl, is_slice_small reply_sl byteT 1 old_value -∗
      Φ (#(U64 0), slice_val reply_sl)%V ))) ∗
  (∀ (err:u64) unused_sl, ⌜err ≠ 0⌝ -∗ Φ (#err, (slice_val unused_sl))%V ))-∗
  WP state.Clerk__FetchAndAppend #ck #key (slice_val val_sl) {{ Φ }}.
Proof.
  iIntros "#Hinv #Hck Hval_sl #Hupd".
  wp_call.
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (op) "Hop_sl".
  set op_sl:=(Slice.mk _ _ _).
  wp_apply (wp_ref_to).
  { done. }
  replace (int.nat 0%Z) with (0%nat) by word.
  simpl.
  iIntros (op_ptr) "Hop_ptr".
  wp_pures.
  wp_load.
  wp_apply (wp_WriteInt with "Hop_sl").
  iIntros (op_sl') "Hop_sl".
  wp_store.
  clear op_sl.
  simpl.

  wp_load.
  wp_apply (wp_WriteBytes with "[$Hop_sl Hval_sl]").
  {
    iDestruct (is_slice_to_small with "Hval_sl") as "$".
  }
  iIntros (op_sl) "[Hop_sl Hval_sl]".
  wp_store.
  clear op_sl'.
  wp_load.
  iNamed "Hck".
  wp_loadField.

  wp_apply (wp_Clerk__Apply with "[] [] Hop_sl").
  { instantiate (1:=(key,value)). done. }
  { iFrame "#". }
  { iFrame "#". }
  iModIntro.
  iSplitL.
  { (* case: successful response *)
    iLeft in "Hupd".
    iMod "Hupd".
    iInv "Hinv" as ">Hown" "Hclose".
    replace (↑_∖_) with (∅:coPset); last set_solver.
    iModIntro.

    iDestruct "Hupd" as (?) "[Hkvptsto Hupd]".
    iDestruct "Hown" as (?) "[Hown Hkvs]".
    iExists _.
    iFrame.

    iIntros "Hghost".
    iDestruct (ghost_map_lookup with "Hkvs Hkvptsto") as %Hold_value.
    iMod (ghost_map_update (old_value ++ value) with "Hkvs Hkvptsto") as "[Hkvs Hkvptsto]".

    iMod ("Hclose" with "[Hghost Hkvs]") as "_".
    {
      iNext.
      iExists _; iFrame "Hghost".
      iExactEq "Hkvs".
      unfold own_kvs.
      f_equal.
      unfold compute_state.

      rewrite foldl_snoc.
      simpl.
      f_equal.
      rewrite Hold_value.
      simpl.
      done.
    }
    iMod ("Hupd" with "Hkvptsto") as "Hupd".
    iModIntro.
    iIntros (reply_sl) "Hreply_sl".
    iApply "Hupd".
    iFrame.
    iExactEq "Hreply_sl".
    f_equal.
    unfold compute_reply.
    simpl.
    rewrite Hold_value.
    done.
  }
  {
    iIntros.
    iRight in "Hupd".
    iApply "Hupd".
    done.
  }
Qed.

Definition own_byte_map (mptr:loc) (m:gmap u64 (list u8)): iProp Σ :=
  ∃ (kvs_sl:gmap u64 Slice.t),
    "Hkvs_map" ∷ is_map mptr 1 kvs_sl ∗
    "#Hkvs_slices" ∷ (∀ (k:u64), readonly (is_slice_small (default Slice.nil (kvs_sl !! k))
                                                          byteT
                                                          1
                                                          (default [] (m !! k))
                                                          )
                     ) ∗
    "Hkvs_slices_caps" ∷ ([∗ set] k ∈ (fin_to_set u64),
                           is_slice_cap (default Slice.nil (kvs_sl !! k)) byteT)
.

Lemma wp_byteMapGet mptr m (k:u64) :
  {{{ own_byte_map mptr m }}}
    Fst (MapGet #mptr #k)
  {{{
        sl, RET (slice_val sl);
        readonly (is_slice_small sl byteT 1 (default [] (m !! k))) ∗
        own_byte_map mptr m
  }}}
.
Proof.
  iIntros (Φ) "Hmap HΦ".
  iNamed "Hmap".
  wp_apply (wp_MapGet with "Hkvs_map").
  iIntros (sl ok) "[%Hlookup Hkvs_map]".
  wp_pures.
  iApply "HΦ".
  iSplitR "Hkvs_map Hkvs_slices_caps"; last first.
  { iExists _. eauto with iFrame. }
  iModIntro.
  iSpecialize ("Hkvs_slices" $! k).
  rewrite /map_get in Hlookup.
  apply (f_equal fst) in Hlookup.
  simpl in Hlookup.
  rewrite Hlookup.
  iFrame "#".
Qed.

Lemma wp_SliceAppendSlice {V:Type} `{!into_val.IntoVal V} ty sl1 (l1:list V) sl2 l2 q1 q2 :
{{{
    is_slice_small sl1 ty q1 l1 ∗
    is_slice_small sl2 ty q2 l2 ∗
    is_slice_cap sl1 ty
}}}
  SliceAppendSlice ty (slice_val sl1) (slice_val sl2)
{{{
    sl, RET (slice_val sl);
      is_slice_small sl2 ty q2 l2 ∗
      is_slice_small sl ty q1 (l1 ++ l2) ∗
      is_slice_cap sl ty
}}}
.
Proof.
Admitted.

Lemma wp_byteMapAppend mptr m (k:u64) sl (v:list u8) q :
{{{
      own_byte_map mptr m ∗
      is_slice_small sl byteT q v
}}}
  (SliceAppendSlice byteT (Fst (MapGet #mptr #k)) (slice_val sl))
{{{ sl, RET (slice_val sl);
    ∀ Ψ,
    (own_byte_map mptr (<[k := (default [] (m !! k)) ++ v]> m) -∗ Ψ #()) -∗
    WP MapInsert #mptr #k (slice_val sl) {{ Ψ }}
}}}
.
Proof.
  iIntros (Φ) "[Hmap Hsl] HΦ".
  iNamed "Hmap".
  wp_apply (wp_MapGet with "Hkvs_map").
  iIntros (sl1 ok) "[%Hlookup Hkvs_map]".
  wp_pures.
  iDestruct (big_sepS_delete _ _ k with "Hkvs_slices_caps") as "[Hcap Hkvs_slices_caps]".
  { set_solver. }
  rewrite /map_get /= in Hlookup.
  apply (f_equal fst) in Hlookup.
  simpl in Hlookup.
  rewrite Hlookup.
  iAssert (_) with "Hkvs_slices" as "#Hsl1".
  iSpecialize ("Hsl1" $! k).
  rewrite Hlookup.
  iMod (readonly_load with "Hsl1") as (?) "Hsl11".
  wp_apply (wp_SliceAppendSlice with "[$Hsl11 $Hsl $Hcap]").
  iIntros (new_sl) "(_ & Hnew_sl & Hcap)".
  iApply "HΦ".
  clear Φ.
  iIntros (Φ) "HΦ".
  iMod (readonly_alloc _ (H:=is_slice_small_as_mapsto _ _ _) with "Hnew_sl") as "#Hnew_sl".
  wp_apply (wp_MapInsert with "Hkvs_map").
  { done. }
  iIntros "Hkvs_map".
  iApply "HΦ".
  iExists _.
  iFrame "Hkvs_map".
  rewrite /typed_map.map_insert.
  iSplitR "Hcap Hkvs_slices_caps".
  {
    iIntros (?).
    destruct (decide (k0 = k)).
    {
      rewrite e.
      repeat rewrite lookup_insert.
      simpl.
      done.
    }
    {
      rewrite lookup_insert_ne; last done.
      rewrite lookup_insert_ne; last done.
      iApply "Hkvs_slices".
    }
  }
  {
    iApply (big_sepS_delete _ _ k).
    { set_solver. }
    rewrite lookup_insert /=.
    iFrame "Hcap".
    iApply (big_sepS_impl with "Hkvs_slices_caps").
    {
      iModIntro.
      iIntros.
      rewrite lookup_insert_ne; last set_solver.
      done.
    }
  }
Qed.

Definition has_byte_map_encoding (enc:list u8) (m:gmap u64 (list u8)) : Prop.
Admitted.

Lemma wp_decodeKvs enc_sl enc m q :
  {{{
        ⌜has_byte_map_encoding enc m⌝ ∗
        is_slice_small enc_sl byteT q enc
  }}}
    decodeKvs (slice_val enc_sl)
  {{{
        (mptr:loc), RET #mptr; own_byte_map mptr m
  }}}.
Proof.
Admitted.

Lemma wp_encodeKvs mptr m :
  {{{
        own_byte_map mptr m
  }}}
    encodeKvs #mptr
  {{{
        enc_sl enc, RET (slice_val enc_sl);
        ⌜has_byte_map_encoding enc m⌝ ∗
        is_slice enc_sl byteT 1 enc ∗
        own_byte_map mptr m
  }}}.
Proof.
Admitted.

Record KVStateC :=
mkKVStateC {
  kv_epoch:u64 ;
  kv_sealed:bool;
  kv_ops:list OpType;
}.

Context `{!filesysG Σ}.

Definition has_kvstate_encoding (enc:list u8) (st:KVStateC) : Prop :=
  ∃ enc_kvs,
  has_byte_map_encoding enc_kvs (compute_state st.(kv_ops)) ∧
  enc = (u64_le st.(kv_epoch)) ++ (u64_le (length st.(kv_ops))) ++ (u64_le (if st.(kv_sealed) then 1 else 0))
                       ++ enc_kvs
.

Definition crash_cond fname P : iProp Σ :=
  |={⊤}=> ∃ enc_kvstate st,
    ⌜has_kvstate_encoding enc_kvstate st⌝ ∗
    fname f↦ enc_kvstate ∗
    P st.

Definition own_KVState_vol (k:loc) st: iProp Σ :=
  ∃ (kvs_ptr:loc),
    "Hkvs" ∷ k ↦[KVState :: "kvs"] #kvs_ptr ∗
    "Hepoch" ∷ k ↦[KVState :: "epoch"] #st.(kv_epoch) ∗
    "HnextIndex" ∷ k ↦[KVState :: "nextIndex"] #(U64 (length st.(kv_ops))) ∗
    "Hsealed" ∷ k ↦[KVState :: "sealed"] #st.(kv_sealed) ∗
    "Hmap" ∷ own_byte_map kvs_ptr (compute_state st.(kv_ops))
.

Definition own_KVState_dur fname st P : iProp Σ :=
    (* durable resources *)
    "Hdur" ∷ crash_borrow
               (∃ enc_kvstate,
                   ⌜has_kvstate_encoding enc_kvstate st⌝ ∗
                    fname f↦ enc_kvstate ∗ P st)
               (crash_cond fname P)
.

Lemma wp_KVState__getState s st :
  {{{
        "Hvol" ∷ own_KVState_vol s st
  }}}
    KVState__getState #s
  {{{
       enc_sl enc, RET (slice_val enc_sl);
        ⌜has_kvstate_encoding enc st⌝ ∗
        is_slice enc_sl byteT 1 enc ∗
        own_KVState_vol s st
  }}}
.
Proof.
Admitted.

Lemma wp_KVState__MakeDurable s old_st st fname P Q :
  {{{
        "#Hfname" ∷ readonly (s ↦[KVState :: "filename"] #(LitString fname)) ∗
        "Hvol" ∷ own_KVState_vol s st ∗
        "Hdur" ∷ own_KVState_dur fname old_st P ∗
        "Hupd" ∷ (P old_st ={⊤}=∗ P st ∗ Q)
  }}}
    KVState__MakeDurable #s
  {{{
       RET #();
        own_KVState_vol s st ∗
        own_KVState_dur fname st P ∗
        Q
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_KVState__getState with "Hvol").
  iIntros (??) "(%Henc & Henc_sl & Hvol)".
  wp_loadField.

  (* open crash_borrow *)
  wp_bind (Write #_ _).
  iApply (wpc_wp _ _ _ _ True).

  wpc_apply (wpc_crash_borrow_open_modify with "Hdur").
  { done. }
  iSplit; first done.
  iIntros "HP".
  iDestruct "HP" as (?) "(%Hold_enc & Hfile & HP)".

  iApply wpc_fupd.
  wpc_apply (wpc_Write with "[$Hfile $Henc_sl]").
  iSplit.
  { (* if a crash happens during the atomic write *)
    iIntros "[Hfile|Hfile]".
    {
      iSplit; first done.
      iModIntro.
      iExists _, _.
      iFrame "∗%".
    }
    {
      iSplit; first done.
      iMod ("Hupd" with "HP") as "[HP HQ]".
      iModIntro.

      iExists _, _.
      iFrame "∗%".
    }
  }
  iNext.
  iIntros "[Hfile Henc_sl]".
  iMod ("Hupd" with "HP") as "[HP HQ]".
  iModIntro.
  iExists (_).
  iSplitL "HP Hfile"; last first.
  {
    iSplitL ""; last first.
    {
      iIntros "Hdur".
      iSplit; first done.
      wp_pures.
      iApply "HΦ".
      iFrame "Hvol".
      iFrame "Hdur".
      iFrame "HQ".
      done.
    }
    (* prove the crash condition is still met*)
    iModIntro.
    iIntros "H".
    iDestruct "H" as (?) "H".
    iExists _,_.
    by iFrame.
  }
  (* prove the new resources *)
  iExists _; iFrame.
  done.
Qed.

Definition own_KVState_StateMachine (k:loc) epoch ops sealed P : iProp Σ :=
  let st := mkKVStateC epoch sealed ops in
  ∃ fname,
  "#Hfname" ∷ readonly (k ↦[KVState :: "filename"] #(LitString fname)) ∗
  "Hvol " ∷ own_KVState_vol k st ∗
  "Hdur" ∷ own_KVState_dur fname st (λ st, P st.(kv_epoch) st.(kv_ops) st.(kv_sealed))
.

Lemma wp_KVState__Apply s P :
  {{{
        True
  }}}
    KVState__Apply #s
  {{{
       applyFn, RET applyFn;
        is_ApplyFn (own_KVState_StateMachine s) applyFn P
  }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  iModIntro.
  iApply "HΦ".
  clear Φ.

  unfold is_ApplyFn.
  iIntros (???????) "!# Hpre HΦ".
  wp_pures.

  iDestruct "Hpre" as "(%Henc & #Hop_sl & Hupd & Hstate)".
  iNamed "Hstate".
  iDestruct (from_named with "Hvol") as "Hvol".
  rewrite -Henc.

  iMod (readonly_load with "Hop_sl") as (?) "Hop_sl1".
  wp_apply (wp_ReadInt with "Hop_sl1").
  iIntros (?) "Hop_sl1".
  wp_pures.

  iNamed "Hvol".
  wp_loadField.
  wp_apply (wp_byteMapGet with "Hmap").
  iIntros (vsl) "[#Hvsl Hmap]".
  wp_pures.

  Opaque u64_le.
  simpl.
  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros "%Hno_overflow".
  wp_storeField.
  wp_loadField.

  wp_apply (wp_byteMapAppend with "[$Hmap $Hop_sl1]").
  iIntros (?) "Hmap".
  simpl.
  wp_loadField.
  wp_apply "Hmap".
  iIntros "Hmap".
  wp_pures.
  wp_apply (wp_KVState__MakeDurable with "[$Hfname Hkvs Hepoch HnextIndex Hsealed Hmap Hupd $Hdur]").
  {
    simpl.
    instantiate (2:=mkKVStateC _ _ _).
    simpl.
    iFrame "Hupd".

    iExists _; iFrame.
    simpl.
    rewrite app_length /=.
    iSplitL "HnextIndex".
    {
      iApply to_named.
      iExactEq "HnextIndex".
      f_equal.
      f_equal.
      replace (int.Z 1) with (1) in * by word.
      assert (int.Z (Z.of_nat (length σ)) = Z.of_nat (length σ)) as H2.
      { admit. }
      rewrite H2 in Hno_overflow.
      admit. (* FIXME: nextIndex overflow *)
    }
    iApply to_named.
    iExactEq "Hmap".
    f_equal.
    unfold compute_state.
    rewrite foldl_snoc.
    done.
  }
  iIntros "(Hvol & Hdur & HQ)".
  wp_pures.
  iMod (readonly_load with "Hvsl") as (?) "Hvsl2".
  iApply "HΦ".
  iFrame "HQ".
  iFrame "Hvsl2".
  iModIntro.
  iExists _.
  iFrame "∗#".
Admitted. (* FIXME: just overflow reasoning left *)

End state_proof.
