From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import closed.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi_adequacy.
From Perennial.program_logic Require dist_lang.

From Perennial.program_proof.bank Require Export bank_proof.
From Perennial.program_proof.lock Require Export lock_proof.
From Perennial.program_proof.simplepb Require Import pb_init_proof pb_definitions.
From Perennial.program_proof.simplepb Require Import kv_proof.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb.apps Require Import clerkpool_proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.goose_lang Require Import crash_borrow crash_modality.

Section closed_wpcs.

Context `{!heapGS Σ}.
Context `{!ekvG Σ}.

Lemma wpc_kv_replica_main γsys γsrv Φc fname me configHost :
  ((∃ data' : list u8, fname f↦data' ∗ ▷ file_crash (own_Server_ghost_f γsys γsrv) data') -∗
    Φc) -∗
  config_protocol_proof.is_pb_config_hosts [configHost] γsys -∗
  clerk_proof.is_proph_read_inv γsys -∗
  is_pb_host me γsys γsrv -∗
  is_pb_system_invs γsys -∗
  (∃ data : list u8, fname f↦data ∗ file_crash (own_Server_ghost_f γsys γsrv) data) -∗
  WPC kv_replica_main #(LitString fname) #me #configHost @ ⊤
  {{ _, True }}
  {{ Φc }}
.
Proof.
  (* TODO: all the invs *)
  iIntros "HΦc #HconfHost #Hproph #Hpbhost #Hinvs Hpre".
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
  wp_apply wp_NewSlice.
  iIntros (?) "Hsl".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (?) "HconfigHosts".
  wp_pures.
  wp_load. wp_apply (wp_SliceAppend with "[$]").
  iIntros (?) "Hsl".
  wp_store. wp_load.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  iMod (readonly_alloc_1 with "Hsl") as "#Hsl".

  wp_apply (wp_Start with "[$Hfile_ctx]").
  {
    iFrame "#". iPureIntro. simpl. rewrite app_length /=. word.
  }
  wp_pures.
  done.
Qed.


Definition dconfigHost : u64 := (U64 11).
Definition dconfigHostPaxos : u64 := (U64 12).
Definition dr1Host: u64 := (U64 1).
Definition dr2Host: u64 := (U64 2).

Definition lconfigHost : u64 := (U64 111).
Definition lconfigHostPaxos : u64 := (U64 112).
Definition lr1Host: u64 := (U64 101).
Definition lr2Host: u64 := (U64 102).

Lemma wp_mk_dconfig_hosts :
  {{{ True }}}
    mk_dconfig_hosts #()
  {{{ sl, RET (slice_val sl); readonly (own_slice_small sl uint64T 1 [ dconfigHost ]) }}}
.
  iIntros (?) "_ HΦ".
  wp_lam. wp_apply (wp_NewSlice).
  iIntros (?) "Hsl". wp_apply wp_ref_to; first by val_ty.
  iIntros (?) "Hptr". wp_pures. wp_load.
  iApply wp_fupd. wp_apply (wp_SliceAppend with "[$]").
  iIntros (?) "Hsl". iApply "HΦ".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  iMod (readonly_alloc_1 with "Hsl") as "$". done.
Qed.

Lemma wp_mk_lconfig_hosts :
  {{{ True }}}
    mk_lconfig_hosts #()
  {{{ sl, RET (slice_val sl); readonly (own_slice_small sl uint64T 1 [ lconfigHost ]) }}}
.
  iIntros (?) "_ HΦ".
  wp_lam. wp_apply (wp_NewSlice).
  iIntros (?) "Hsl". wp_apply wp_ref_to; first by val_ty.
  iIntros (?) "Hptr". wp_pures. wp_load.
  iApply wp_fupd. wp_apply (wp_SliceAppend with "[$]").
  iIntros (?) "Hsl". iApply "HΦ".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  iMod (readonly_alloc_1 with "Hsl") as "$". done.
Qed.

Context `{!bankG Σ}.
Lemma wp_makeBankClerk γlk γkv :
  {{{
        "#Hhost1" ∷ is_kv_config_hosts [dconfigHost] γkv ∗
        "#Hhost2" ∷ is_kv_config_hosts [lconfigHost] γlk ∗
        "#Hbank" ∷ is_bank "init" (Build_lock_names (kv_ptsto γlk)) (kv_ptsto γkv) {[ "a1"; "a2" ]}
  }}}
    makeBankClerk #()
  {{{
        (b:loc), RET #b; own_bank_clerk b {[ "a1" ; "a2" ]}
  }}}
.
Proof.
  iIntros (?) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_apply wp_mk_dconfig_hosts.
  iIntros (?) "#Hdsl".

  wp_apply (wp_MakeKv with "[$Hhost1]").
  { iFrame "#". done. }
  iIntros (?) "#Hkv".
  wp_pures.

  wp_apply wp_mk_lconfig_hosts.
  iIntros (?) "#Hlsl".
  wp_apply (wp_MakeKv with "[$Hhost2]").
  { iFrame "#". done. }
  iIntros (?) "Hlock_kv".
  wp_apply (wp_MakeLockClerk lockN with "[Hlock_kv]").
  {
    instantiate (3:=(Build_lock_names (kv_ptsto γlk))).
    iFrame. iPureIntro. solve_ndisj.
  }
  iIntros (?) "#Hlck".
  wp_pures.
  wp_apply (wp_MakeBankClerk with "[]").
  { iFrame "#". done. }
  iIntros (?) "Hb".
  iApply "HΦ".
  iFrame.
Qed.

Definition bank_pre : iProp Σ :=
  ∃ γkv γlk,
  "#Hhost1" ∷ is_kv_config_hosts [dconfigHost] γkv ∗
  "#Hhost2" ∷ is_kv_config_hosts [lconfigHost] γlk ∗
  "#Hbank" ∷ is_bank "init" (Build_lock_names (kv_ptsto γlk)) (kv_ptsto γkv) {[ "a1"; "a2" ]}
.

Lemma wp_bank_transferer_main :
  {{{
        bank_pre
  }}}
    bank_transferer_main #()
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (?) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_apply (wp_makeBankClerk with "[$]").
  iIntros (?) "Hck".
  wp_pures.
  wp_forBreak.
  wp_pures.
  wp_apply (Bank__SimpleTransfer_spec with "[$]").
  iIntros "Hck".
  wp_pures.
  iModIntro. iLeft. iFrame. done.
Qed.

Lemma wp_bank_auditor_main :
  {{{
        bank_pre
  }}}
    bank_auditor_main #()
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (?) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_apply (wp_makeBankClerk with "[$]").
  iIntros (?) "Hck".
  wp_pures.
  wp_forBreak.
  wp_pures.
  wp_apply (Bank__SimpleAudit_spec with "[$]").
  iIntros "Hck".
  wp_pures.
  iModIntro. iLeft. iFrame. done.
Qed.

End closed_wpcs.
