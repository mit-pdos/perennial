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

Context {conf_host_names:list config_proof.config_server_names}.
Context {initconf:list u64}.
Local Instance esmParams : pbParams.t := pbParams.mk conf_host_names initconf (ekv_record).

Class ekvG Σ :=
  {
    ekv_erpcG :> erpcG Σ (list u8) ;
    ekv_simplelogG :> simplelogG Σ;
    ekv_kvG :> kvG Σ ;
  }.

Definition ekvΣ := #[erpcΣ (list u8); simplelogΣ; kvΣ].
Global Instance subG_ekvΣ {Σ} : subG ekvΣ Σ → ekvG Σ.
Proof. intros. solve_inG. Qed.

Record kv_names :=
  {
    pb_gn : simplepb_system_names ;
    log_gn : gname ;
    kv_gn : gname ;
  }
.

Implicit Types γ : kv_names.

Section global_proof.

Context `{!gooseGlobalGS Σ}.
Context `{!ekvG Σ}.

(* The abstract state applies the operation to an all-nil map,
   so that each key already exists from the start. This is consisent with
   [getOp] doing [default []]. *)
Definition own_kvs γ ops : iProp Σ :=
  ∃ allocatedKeys,
  ghost_map_auth γ.(kv_gn) 1 (compute_state ops ∪ gset_to_gmap "" allocatedKeys)
.

Definition stateN := nroot .@ "state".

Definition kv_inv γlog γ : iProp Σ :=
  inv stateN ( ∃ ops, own_log γlog ops ∗ own_kvs γ ops).

Definition kv_ptsto γ (k v : string) : iProp Σ :=
  k ↪[γ.(kv_gn)] v.

(* FIXME: this should not expose own_log. Want to directly allocate KV system
   and servers in one shot, without manually doing pb underneath. *)

Definition is_kv_config_hosts confHosts γ : iProp Σ :=
  ∃ γerpc γlog,
    "#Hee_inv" ∷ is_esm_inv (low_record:=kv_record) γ.(pb_gn) γlog γerpc ∗
    "#Herpc_inv" ∷ is_eRPCServer γerpc ∗
    "#Hkv_inv" ∷ kv_inv γlog γ ∗
    "#Hinvs" ∷ is_pb_system_invs γ.(pb_gn) ∗
    "#Hconf" ∷ is_pb_sys_hosts confHosts γ.(pb_gn) ∗
    "%Hnonempty" ∷ ⌜0 < length confHosts⌝
.

Definition is_kv_server_host host γ γsrv : iProp Σ :=
  is_pb_host host γ.(pb_gn) γsrv.

(*
Lemma alloc_kv_system γsrvs :
  length γsrvs > 0 →
  (∀ γsrv, ⌜γsrv ∈ γsrvs⌝ → is_accepted_lb γsrv.(r_pb) (U64 0) [] ∗ is_epoch_lb γsrv.(r_pb) 0)
  ={⊤}=∗ ∃ γ,
  is_kv_inv γ ∗
  [∗ set] k ∈ allocated, kv_ptsto γ k ""
.
  is_pb_system_invs γ ∗
  own_op_log γ [] ∗
  (∀ γsrv, ⌜γsrv ∈ γsrvs⌝ → is_pb_sys_init_witness γ γsrv) ∗
  pb_init_for_config γ.(s_pb) (r_pb <$> γsrvs) ∗
  primary_init_for_config γ.(s_prim) ∗
  is_proph_read_inv γ
.

Lemma alloc_kv γlog allocated :
  own_log γlog [] ={⊤}=∗
  ∃ γ ,
  kv_inv γlog γ ∗
  [∗ set] k ∈ allocated, kv_ptsto γ k ""
.
Proof.
  iIntros "Hlog".
  iMod (ghost_map_alloc (gset_to_gmap "" allocated)) as (γkv) "[Hkvs Hkvptsto]".
  iExists {| |}.
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
 *)

End global_proof.

Section local_proof.

Context `{!heapGS Σ}.
Context `{!ekvG Σ}.

Definition kv_crash_resources γ γsrv data : iProp Σ := file_crash (own_Server_ghost_f γ.(pb_gn) γsrv) data.

Lemma wp_Start fname configHosts_sl configHosts (host:chan) γ γsrv data :
  {{{
      "#HconfSl" ∷ readonly (own_slice_small configHosts_sl uint64T 1 configHosts) ∗
      "#Hconf" ∷ is_kv_config_hosts configHosts γ ∗
      "#Hhost" ∷ is_kv_server_host host γ γsrv ∗
      "Hfile_ctx" ∷ crash_borrow (fname f↦ data ∗ kv_crash_resources γ γsrv data)
                  (|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ kv_crash_resources γ γsrv data')
  }}}
    Start #(LitString fname) #(host:u64) (slice_val configHosts_sl)
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
  iNamed "Hconf". iNamed "Hconf".
  wp_apply (wp_MakePbServer with "[Hown Hfile_ctx]").
  {
    iDestruct "Hconf" as "[Hconf ?]".
    iFrame "Hinvs". iFrame "HconfSl Hconf". iFrame "%".
    iFrame "His2 ∗".
  }
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

Lemma wp_MakeClerk γkv configHosts configHosts_sl :
  {{{
      "#HconfSl" ∷ readonly (own_slice_small configHosts_sl uint64T 1 configHosts) ∗
      "#Hhost" ∷ is_kv_config_hosts configHosts γkv
  }}}
    kv.MakeClerk (slice_val configHosts_sl)
  {{{
        ck, RET #ck; own_Clerk ck γkv
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  iNamed "Hhost".
  wp_apply (esm_proof.wp_MakeClerk with "[]").
  { iFrame "#%". }
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
