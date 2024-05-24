From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Export reconnectclient.
From Perennial.program_proof.grove_shared Require Export urpc_proof.

Section proof.

Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.

Definition own_ReconnectingClient ck host : iProp Σ :=
  ∃ (valid:bool) (urpcCl:loc),
  "Hvalid" ∷ ck ↦[ReconnectingClient :: "valid"] #valid ∗
  "HurpcCl" ∷ ck ↦[ReconnectingClient :: "urpcCl"] #urpcCl ∗
  "#Hcl" ∷ □(if valid then is_uRPCClient urpcCl host else True)
.

Definition reconnectN := nroot .@ "reconnect".

Definition is_ReconnectingClient ck (host:u64) : iProp Σ :=
  ∃ mu,
    "#Haddr" ∷ readonly (ck ↦[ReconnectingClient :: "addr"] #host) ∗
    "#Hmu" ∷ readonly (ck ↦[ReconnectingClient :: "mu"] mu) ∗
    "#HmuInv" ∷ is_lock reconnectN mu (own_ReconnectingClient ck host)
.

Lemma wp_getClient ck host :
  {{{
       is_ReconnectingClient ck host
  }}}
   ReconnectingClient__getClient #ck
  {{{
       (err: u64) urpcCl, RET (#err, #urpcCl); if (decide (err = 0)) then is_uRPCClient urpcCl host else True
  }}}
.
Proof.
  iIntros (Φ) "#His HΦ".
  iNamed "His".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* there's already a client there *)
    wp_loadField.
    wp_loadField.
    wp_apply (release_spec with "[- HΦ]").
    { iFrame "HmuInv ∗ #". }
    wp_pures. by iApply "HΦ".
  }

  (* else make a new one *)
  wp_loadField.
  wp_apply (release_spec with "[- HΦ]").
  { iFrame "HmuInv ∗".
    repeat iExists _.
    iFrame "∗#".
  }
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  wp_pures.
  iIntros (newRpcCl) "HnewRpcCl".
  wp_pures.

  iAssert (∃ (cl_ptr:loc), "HnewRpcCl" ∷ newRpcCl ↦[ptrT] #cl_ptr)%I with "[HnewRpcCl]" as "HH".
  { iExists _; iFrame. }
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (err_ptr) "Herr".
  wp_pures.
  wp_loadField.
  wp_apply (wp_TryMakeClient).
  iIntros (??) "Hnewcl".
  wp_pures.
  wp_store.
  iNamed "HH".
  wp_store.
  wp_load.

  wp_apply (wp_If_join emp).
  { iSplit.
    - iIntros. wp_apply wp_Sleep. done.
    - iIntros. wp_pures. done.
  }
  iIntros "_".

  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".

  wp_load.
  iClear "Hcl".
  iNamed "Hown".
  wp_if_destruct.
  - destruct (decide _); last by exfalso.
    wp_load.
    wp_storeField.
    wp_storeField.
    wp_loadField.
    iDestruct "Hnewcl" as "#Hnewcl".
    wp_apply (release_spec with "[- HΦ HnewRpcCl Herr]").
    { iFrame "HmuInv ∗ #". }

    wp_load.
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame "#".
  - wp_loadField.
    wp_apply (release_spec with "[- HΦ HnewRpcCl Herr]").
    { iFrame "HmuInv ∗ #". }

    wp_load.
    wp_load.
    wp_pures.
    iApply "HΦ".
    destruct (decide _).
    { exfalso. congruence. }
    done.
Qed.

Lemma wp_ReconnectingClient__Call2 γsmap q (cl_ptr:loc) (rpcid:u64) (host:u64) req rep_out_ptr
      (timeout_ms : u64) dummy_sl_val (reqData:list u8) Spec Φ :
  is_ReconnectingClient cl_ptr host -∗
  is_urpc_spec_pred γsmap host rpcid Spec -∗
  own_slice_small req byteT q reqData -∗
  rep_out_ptr ↦[slice.T byteT] dummy_sl_val -∗
  □(▷ Spec reqData (λ reply,
       own_slice_small req byteT q reqData -∗
        ∀ rep_sl,
          rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) -∗
          own_slice_small rep_sl byteT (DfracOwn 1) reply -∗
          Φ #0)
  ) -∗
  (
   ∀ (err:u64), ⌜err ≠ 0⌝ →
                own_slice_small req byteT q reqData -∗
                rep_out_ptr ↦[slice.T byteT] dummy_sl_val -∗ Φ #err
  ) -∗
  WP ReconnectingClient__Call #cl_ptr #rpcid (slice_val req) #rep_out_ptr #timeout_ms {{ Φ }}.
Proof.
  iIntros "#Hre #? Hsl Hrep #? HΦerr".
  iIntros.
  wp_call.
  wp_apply (wp_getClient with "[$]").
  iIntros (??) "Hcl".
  wp_pures.

  wp_if_destruct.
  { destruct (decide _).
    { exfalso. congruence. }
    iApply ("HΦerr" with "[] Hsl Hrep").
    done.
  }

  destruct (decide _); last by exfalso.
  iDestruct "Hcl" as "#Hcl".
  wp_apply (wp_Client__Call_pred with "[Hsl Hrep]").
  { iFrame "∗#". }
  iIntros (?) "(Hsl & HΦ)".
  wp_pures.
  wp_if_destruct.
  {
    iNamed "Hre".
    wp_loadField.
    wp_apply (acquire_spec with "HmuInv").
    iIntros "[Hlocked Hown]".

    iClear "Hcl".
    clear urpcCl.
    iNamed "Hown".
    wp_pures.
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[Hlocked Hvalid HurpcCl]").
    {
      iFrame "HmuInv Hlocked".
      iNext. repeat iExists _.
      iFrame "∗#".
      done.
    }
    wp_pures.
    rewrite Heqb.
    iModIntro.
    destruct err.
    {
     iApply ("HΦerr" with "[] Hsl [-]").
     { done. }
     { iFrame. }
    }
    {
      exfalso. done.
    }
  }
  wp_pures.
  destruct err.
  {
   iApply ("HΦerr" with "[] Hsl").
   { iPureIntro. simpl. by destruct c. }
   iFrame.
   done.
  }
  {
   simpl.
   iDestruct "HΦ" as (??) "(Hrep & Hsl2 & HΦ)".
   iApply ("HΦ" with "Hsl Hrep").
   iFrame.
   done.
  }
Qed.

Lemma wp_MakeReconnectingClient (srv:u64):
  {{{
       True
  }}}
    MakeReconnectingClient #srv
  {{{
       (cl_ptr:loc), RET #cl_ptr; is_ReconnectingClient cl_ptr srv
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (?) "HmuInv".
  wp_storeField.
  wp_storeField.
  wp_storeField.
  iApply "HΦ".
  iMod (readonly_alloc_1 with "mu") as "#Hmu".
  iMod (readonly_alloc_1 with "addr") as "#Haddr".
  iExists _.
  iFrame "#".
  iMod (alloc_lock with "HmuInv [-]") as "$"; last done.
  iNext.
  repeat iExists _.
  iFrame "∗#".
  done.
Qed.

End proof.
