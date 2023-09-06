From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import kv.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb Require Import pb_definitions config_proof.
From Perennial.program_proof.simplepb Require Import pb_apply_proof clerk_proof.
From Perennial.program_proof.grove_shared Require Import erpc_lib.
From Perennial.program_proof Require Import map_marshal_proof.
From iris.algebra Require Import dfrac_agree mono_list.

From Perennial.program_proof.simplepb.apps Require Import vsm esm_proof kv_vsm_proof log.

Class kvG Σ := KvG {
  kv_ghostMapG :> ghost_mapG Σ string string ;
  kv_logG :> inG Σ (mono_listR (leibnizO kvOp)) ;
  kv_vsmG :> vsmG (sm_record:=kv_record) Σ ;
}.
Definition kvΣ := #[configΣ; ghost_mapΣ string string;
                      GFunctor (mono_listR (leibnizO kvOp));
                      vsmΣ (sm_record:=kv_record)
   ].
Global Instance subG_kvΣ {Σ} : subG kvΣ Σ → kvG Σ.
Proof. intros. solve_inG. Qed.

Definition ekv_record := (esm_record (low_record:=kv_record)).
Class ekvG Σ :=
  {
    ekv_erpcG :> erpcG Σ (list u8) ;
    ekv_simplelogG :> simplelogG (sm_record:=ekv_record) Σ;
    ekv_kvG :> kvG Σ ;
  }.

Definition ekvΣ := #[erpcΣ (list u8); simplelogΣ (sm_record:=ekv_record);
                     kvΣ].
Global Instance subG_ekvΣ {Σ} : subG ekvΣ Σ → ekvG Σ.
Proof. intros. solve_inG. Qed.

Section global_proof.


Context `{!gooseGlobalGS Σ}.
Context `{!ekvG Σ}.

(* The abstract state applies the operation to an all-nil map,
   so that each key already exists from the start. This is consisent with
   [getOp] doing [default []]. *)
Definition own_kvs (γkv:gname) ops : iProp Σ :=
  ∃ allocatedKeys,
  ghost_map_auth γkv 1 (compute_state ops ∪ gset_to_gmap "" allocatedKeys)
.

Definition stateN := nroot .@ "state".

Definition kv_inv γlog γkv : iProp Σ :=
  inv stateN ( ∃ ops, own_log γlog ops ∗ own_kvs γkv ops).

Definition kv_ptsto γkv (k v : string) : iProp Σ :=
  k ↪[γkv] v.

Lemma alloc_kv γlog allocated :
  own_log γlog [] ={⊤}=∗
  ∃ γkv ,
  kv_inv γlog γkv ∗
  [∗ set] k ∈ allocated, kv_ptsto γkv k ""
.
Proof.
  iIntros "Hlog".
  iMod (ghost_map_alloc (gset_to_gmap "" allocated)) as (γkv) "[Hkvs Hkvptsto]".
  iExists _.
  iMod (inv_alloc with "[Hkvs Hlog]") as "$".
  { iNext. iExists _; iFrame. rewrite /own_kvs /compute_state /=.
    iExists _. rewrite left_id_L. done. }
  replace allocated with (dom (gset_to_gmap "" allocated)) at 2.
  2:{ rewrite dom_gset_to_gmap. done. }
  iApply big_sepM_dom. iApply (big_sepM_impl with "Hkvptsto").
  iIntros "!# %k %x".
  rewrite lookup_gset_to_gmap_Some.
  iIntros ([_ <-]). auto.
Qed.

(* These are the client-side invs *)
Definition is_ekv_invs γpb γkv : iProp Σ :=
  ∃ γlog γerpc,
  is_esm_inv (low_record:=kv_record) γpb γlog γerpc ∗
  is_eRPCServer γerpc ∗
  kv_inv γlog γkv
.

Definition is_kv_config confHost γkv : iProp Σ :=
  ∃ γpb γerpc γlog,
    "#Hee_inv" ∷ is_esm_inv (low_record:=kv_record) γpb γlog γerpc ∗
    "#Herpc_inv" ∷ is_eRPCServer γerpc ∗
    "#Hkv_inv" ∷ kv_inv γlog γkv ∗
    "#Hconf" ∷ is_pb_sys_host confHost γpb
.

Lemma alloc_ekv γpb allocated :
  own_op_log γpb [] ={⊤}=∗
  ∃ γkv ,
  is_ekv_invs γpb γkv ∗
  [∗ set] k ∈ allocated, kv_ptsto γkv k ""
.
Proof.
  iIntros "Hoplog".
  iMod (alloc_esm with "[$]") as (??) "(#? & #? & ?)".
  iMod (alloc_kv with "[$]") as (?) "(#? & Hkvs)".
  iExists _. iFrame.
  iModIntro. repeat iExists _; iFrame "#".
Qed.

End global_proof.

Section local_proof.

Context `{!heapGS Σ}.
Context `{!ekvG Σ}.

Lemma wp_Start fname (confHost host:chan) γsys γsrv data :
  {{{
      "#Hhost" ∷ is_pb_host (pb_record:=ekv_record) host γsys γsrv ∗
      "#HconfHost" ∷ config_protocol_proof.is_pb_config_host confHost γsys ∗
      "Hfile_ctx" ∷ crash_borrow (fname f↦ data ∗ file_crash (own_Server_ghost_f γsys γsrv) data)
                  (|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ file_crash (own_Server_ghost_f γsys γsrv) data') ∗

      "#Hinvs" ∷ is_pb_system_invs γsys
  }}}
    Start #(LitString fname) #(host:u64) #(confHost:u64)
  {{{
        RET #(); True
  }}}
.
Proof using Type*.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_makeVersionedStateMachine).
  iIntros (??) "[#His1 Hown]".
  wp_apply (wp_MakeExactlyOnceStateMachine with "[Hown]").
  {
    iFrame.
    iFrame "His1".
  }
  iIntros (??) "[#His2 Hown]".
  wp_apply (wp_MakePbServer (sm_record:=ekv_record) with "[$Hown $Hfile_ctx]").
  { iFrame "#". }
  iIntros (?) "His".
  wp_pures.
  wp_apply (pb_start_proof.wp_Server__Serve with "[$]").
  wp_pures.
  by iApply "HΦ".
Qed.

Definition own_Clerk ck γkv : iProp Σ :=
  ∃ (eeCk:loc) γlog,
    "Hcl" ∷ ck ↦[kv.Clerk :: "cl"] #eeCk ∗
    "#Hkvinv" ∷ kv_inv γlog γkv ∗
    "Hownck" ∷ esm_proof.own_Clerk (low_record:=kv_record) eeCk γlog
.

Lemma wp_MakeClerk γkv confHost :
  {{{
      is_kv_config confHost γkv
  }}}
    kv.MakeClerk #confHost
  {{{
        ck, RET #ck; own_Clerk ck γkv
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (esm_proof.wp_MakeClerk with "[]").
  { iFrame "#". }
  iIntros (?) "Hck".
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl".
  iApply "HΦ".
  repeat iExists _.
  iFrame "∗#".
Qed.

Lemma wp_Clerk__Put ck γkv key value :
⊢ {{{ own_Clerk ck γkv }}}
  <<< ∀∀ old_value, kv_ptsto γkv key old_value >>>
    Clerk__Put #ck #(str key) #(str value) @ (↑pbN ∪ ↑prophReadN ∪ ↑esmN ∪ ↑stateN)
  <<< kv_ptsto γkv key value >>>
  {{{ RET #(); own_Clerk ck γkv }}}.
Proof.
  iIntros "%Φ !# Hck Hupd".
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
  iIntros (args) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_apply (wp_encodePutArgs with "[$Key $Val]").
  iIntros (putEncoded put_sl) "[%Henc Henc_sl]".
  wp_loadField.
  wp_apply (wp_Clerk__ApplyExactlyOnce with "Hownck Henc_sl").
  { done. }
  iInv "Hkvinv" as ">Hown" "Hclose".

  (* make this a separate lemma? *)
  iMod (fupd_mask_subseteq _) as "Hmaskclose".
  2: iMod "Hupd".
  1:{ eauto 20 with ndisj. } (* FIXME: increase search depth on solve_ndisj? *)

  iModIntro.
  iDestruct "Hown" as (?) "[Hlog Hkvs]".
  iDestruct ("Hupd") as (?) "[Hkvptsto Hkvclose]".

  rewrite /kv_record /=.
  iExists _; iFrame.
  iIntros "Hlog".

  iNamed "Hkvs".
  iMod (ghost_map_update (value) with "Hkvs Hkvptsto") as "[Hkvs Hkvptsto]".

  iMod ("Hkvclose" with "Hkvptsto") as "HH".
  iMod "Hmaskclose" as "_".
  iMod ("Hclose" with "[Hlog Hkvs]") as "_".
  {
    iExists _; iFrame.
    iNext.
    unfold own_kvs.
    unfold compute_state.
    rewrite foldl_snoc.
    simpl. rewrite insert_union_l.
    iExists _.
    iFrame.
  }
  iModIntro.
  iIntros (?) "Hsl Hck".
  wp_pures.
  iApply "HH".
  iModIntro.
  repeat iExists _.
  iFrame "∗#".
Qed.

Lemma wp_Clerk__Get ck γkv key :
⊢ {{{ own_Clerk ck γkv }}}
  <<< ∀∀ value, kv_ptsto γkv key value >>>
    Clerk__Get #ck #(str key) @ (↑pbN ∪ ↑prophReadN ∪ ↑esmN ∪ ↑stateN)
  <<< kv_ptsto γkv key value >>>
  {{{ RET #(str value); own_Clerk ck γkv }}}.
Proof.
  iIntros "%Φ !# Hck Hupd".
  wp_lam.
  wp_pures.
  iNamed "Hck".
  wp_apply (wp_encodeGetArgs with "[//]").
  iIntros (getEncoded get_sl) "[%Henc Henc_sl]".
  wp_loadField.
  wp_apply (wp_Clerk__ApplyReadonly with "Hownck Henc_sl").
  { instantiate (1:=getOp key). done. }
  { done. }
  iInv "Hkvinv" as ">Hown" "Hclose".

  (* make this a separate lemma? *)
  iMod (fupd_mask_subseteq _) as "Hmaskclose".
  2: iMod "Hupd".
  1:{ eauto 20 with ndisj. }

  iModIntro.

  iDestruct "Hown" as (?) "[Hlog Hkvs]".
  iDestruct ("Hupd") as (?) "[Hkvptsto Hkvclose]".
  iExists _; iFrame "Hlog".
  iIntros "Hlog".

  iNamed "Hkvs".
  iDestruct (ghost_map_lookup with "[$] [$]") as %Hlook.

  iMod ("Hkvclose" with "Hkvptsto") as "HΦ".
  iMod "Hmaskclose" as "_".
  iMod ("Hclose" with "[Hlog Hkvs]") as "_".
  { iExists _; iFrame. iExists _; iFrame. }
  iModIntro.
  iIntros (?) "Hck Hsl".
  wp_apply (wp_StringFromBytes with "[$]").
  iIntros "_".
  simpl. rewrite string_to_bytes_inj /=.
  rewrite lookup_union in Hlook.
  destruct (compute_state ops !! key) as [x|]; simpl.
  - simpl in Hlook. rewrite union_Some_l in Hlook.
    injection Hlook as <-.
    iApply "HΦ". repeat iExists _. iFrame "∗#".
  -
    rewrite left_id lookup_gset_to_gmap_Some in Hlook.
    destruct Hlook as [? ?]; subst.
    iApply "HΦ". repeat iExists _. iFrame "∗#".
Qed.

Local Lemma helper (m:gmap string string) s k v d :
  (m ∪ gset_to_gmap d s) !! k = Some v →
  default d (m !! k) = v.
Proof.
  rewrite lookup_union.
  destruct (m !! k).
  { rewrite union_Some_l. naive_solver. }
  { rewrite option_union_left_id lookup_gset_to_gmap_Some. naive_solver. }
Qed.

Lemma wp_Clerk__CondPut ck γkv key expect val :
⊢ {{{ own_Clerk ck γkv }}}
  <<< ∀∀ old_value, kv_ptsto γkv key old_value >>>
    Clerk__CondPut #ck #(str key) #(str expect) #(str val) @ (↑pbN ∪ ↑prophReadN ∪ ↑esmN ∪ ↑stateN)
  <<< kv_ptsto γkv key (if bool_decide (expect = old_value) then val else old_value) >>>
  {{{ RET #(str (if bool_decide (expect = old_value) then "ok" else "")); own_Clerk ck γkv }}}.
Proof.
  iIntros "%Φ !# Hck Hupd".
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
  iIntros (args) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_apply (wp_encodeCondPutArgs with "[$Key $Expect $Val]").
  iIntros (putEncoded put_sl) "[%Henc Henc_sl]".
  wp_loadField.
  wp_apply (wp_Clerk__ApplyExactlyOnce with "Hownck Henc_sl").
  { done. }
  iInv "Hkvinv" as ">Hown" "Hclose".

  (* make this a separate lemma? *)
  iMod (fupd_mask_subseteq _) as "Hmaskclose".
  2: iMod "Hupd".
  1:{ eauto 20 with ndisj. } (* FIXME: increase search depth on solve_ndisj? *)

  iModIntro.
  iDestruct "Hown" as (?) "[Hlog Hkvs]".
  iDestruct ("Hupd") as (?) "[Hkvptsto Hkvclose]".

  rewrite /kv_record /=.
  iExists _; iFrame.
  iIntros "Hlog".

  iNamed "Hkvs".
  iDestruct (ghost_map_lookup with "[$] [$]") as %Hlook.
  iMod (ghost_map_update _ with "Hkvs Hkvptsto") as "[Hkvs Hkvptsto]".

  pose proof Hlook as Heq.
  apply helper in Heq. subst.
  iMod ("Hkvclose" with "Hkvptsto") as "HH".
  iMod "Hmaskclose" as "_".
  iMod ("Hclose" with "[Hlog Hkvs]") as "_".
  {
    iExists _; iFrame.
    iNext.
    unfold own_kvs.
    unfold compute_state.
    rewrite foldl_snoc.
    simpl. rewrite insert_union_l.
    destruct (decide _).
    {
      subst.
      rewrite /compute_state.
      rewrite bool_decide_true.
      2:{ done. }
      iExists _; iFrame.
    }
    {
      rewrite bool_decide_false.
      2:{ naive_solver. }
      iExists _.
      subst.
      rewrite -insert_union_l.
      rewrite insert_id.
      2:{ done. }
      iFrame.
    }
  }
  iModIntro.
  iIntros (?) "Hck Hsl".
  wp_apply (wp_StringFromBytes with "[$Hsl]").
  iIntros "_".
  wp_pures.
  destruct (decide _).
  { subst. rewrite bool_decide_true; last done. iApply "HH". repeat iExists _; iFrame "∗#". }
  { subst. rewrite bool_decide_false; last done. iApply "HH". repeat iExists _; iFrame "∗#". }
Qed.

End local_proof.
