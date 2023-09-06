From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import closed.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi_adequacy.
From Perennial.program_logic Require dist_lang.

From Perennial.program_proof.bank Require Import bank_proof.
From Perennial.program_proof.simplepb Require Import pb_init_proof pb_definitions.
From Perennial.program_proof.simplepb Require Import kv_proof.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb.apps Require Import clerkpool_proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.goose_lang Require Import crash_borrow crash_modality.

Section closed_wpcs.

Context `{!heapGS Σ}.
Context `{!ekvG Σ}.

Definition dconfigHost : u64 := 10.
Definition lconfigHost : u64 := 110.
Lemma wpc_kv_replica_main γsys γsrv Φc fname me configHost :
  ((∃ data' : list u8, fname f↦data' ∗ ▷ file_crash (own_Server_ghost_f γsys γsrv) data') -∗
    Φc) -∗
  config_protocol_proof.is_pb_config_host configHost γsys -∗
  is_pb_host me γsys γsrv -∗
  is_pb_system_invs γsys -∗
  (∃ data : list u8, fname f↦data ∗ file_crash (own_Server_ghost_f γsys γsrv) data) -∗
  WPC kv_replica_main #(LitString fname) #me #configHost @ ⊤
  {{ _, True }}
  {{ Φc }}
.
Proof.
  (* TODO: all the invs *)
  iIntros "HΦc #HconfHost #Hpbhost #Hinvs Hpre".
  iNamed "Hinvs".
  iDestruct "Hpre" as (?) "[Hfile Hcrash]".

  unfold kv_replica_main.
  wpc_call.
  { iApply "HΦc". iExists _. iFrame. }

  iCache with "HΦc Hfile Hcrash".
  { iApply "HΦc". iExists _. iFrame. }
  wpc_bind (Primitive2 _ _ _).
  wpc_frame.
  iApply wp_crash_borrow_generate_pre.
  { done. }
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (?) "Hl".
  iIntros "Hpreborrow".
  iNamed 1.
  wpc_pures.
  wpc_bind (store_ty _ _).
  wpc_frame.
  wp_store.
  iModIntro.
  iNamed 1.

  iApply wpc_cfupd.
  wpc_apply (wpc_crash_borrow_inits with "Hpreborrow [Hfile Hcrash] []").
  { iAccu. }
  {
    iModIntro.
    instantiate (1:=(|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ file_crash (own_Server_ghost_f γsys γsrv) data')).
    iIntros "[H1 H2]".
    iModIntro.
    iExists _.
    iFrame.
  }
  iIntros "Hfile_ctx".
  wpc_apply (wpc_crash_mono _ _ _ _ _ (True%I) with "[HΦc]").
  { iIntros "_".
    iIntros "H".
    iMod "H".
    iModIntro.
    iApply "HΦc".
    done. }
  iApply wp_wpc.
  wp_pures.

  wp_apply (wp_Start with "[Hfile_ctx]").
  {
    iFrame "∗#".
  }
  wp_pures.
  done.
Qed.

Context `{!bankG Σ}.
Lemma wp_makeBankClerk γlk kvptsto :
  {{{
       is_bank "init" γlk kvptsto {[ "a1"; "a2" ]}
  }}}
    makeBankClerk #()
  {{{
        γ (b:loc), RET #b; own_bank_clerk γ b {[ "a1" ; "a2" ]}
  }}}
.
Proof.
  iIntros (?) "Hpre HΦ".
  wp_lam.
Admitted.

Lemma wp_config_main γconf {Σ} {HKV: ekvG Σ} {HG} {HL}:
  let hG := {| goose_globalGS := HG; goose_localGS := HL |} in
  "HconfInit" ∷ makeConfigServer_pre γconf [U64 1; U64 2] ∗
  "#Hhost" ∷ is_config_host configHost γconf -∗
  WP config_main #() {{ _, True }}
.
Proof.
  intros ?.
  iNamed 1.
  wp_call.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hsl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (servers_ptr) "Hservers".
  wp_pures.

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  wp_apply (wp_SliceAppend with "Hsl").
  iIntros (?) "Hsl".
  wp_apply (wp_StoreAt with "[$Hservers]").
  { done. }
  iIntros "Hservers".

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  wp_apply (wp_SliceAppend with "Hsl").
  iIntros (?) "Hsl".
  wp_apply (wp_StoreAt with "[$Hservers]").
  { done. }
  iIntros "Hservers".

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  rewrite replicate_0.
  simpl.
  wp_apply (config_proof.wp_MakeServer with "[$HconfInit $Hsl]").
  iIntros (?) "#Hissrv".
  wp_apply (wp_Server__Serve with "[$]").
  {
    iFrame "Hissrv".
  }
  wp_pures.
  done.
Qed.

End closed_wpcs.

End closed_wpcs.
