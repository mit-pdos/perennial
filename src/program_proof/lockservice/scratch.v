From Perennial.program_proof.lockservice Require Import lockservice_nocrash.
From Perennial.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import proof_prelude.
From stdpp Require Import gmap.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.Helpers Require Import NamedProps.
From iris.algebra Require Import numbers.

Section lockservice_proof.
Context `{!heapG Σ}.
Context `{!mapG Σ u64 bool}.
Context `{!mapG Σ u64 unit}.
Context `{!ghost_varG Σ bool}.

Definition Nclient := nroot .@ "client".
Definition Nserver := nroot .@ "server".
Parameter (P : iProp Σ).
Instance tp : Timeless P. Admitted.

Definition server_inner γi γp γc : iProp Σ :=
  ∃ (issued : gmap u64 unit) (processed : gmap u64 bool) (claimed : gmap u64 bool) (locked : bool),
    "Hissued" ∷ ([∗ map] _ ↦ _; _ ∈ issued; processed, True) ∗
    "Hprocessed" ∷ ([∗ map] _ ↦ proc; claim ∈ processed; claimed, ⌜proc = false \/ claim = true⌝ ∨ P) ∗
    "Hctxi" ∷ map_ctx γi 1 issued ∗
    "Hctxp" ∷ map_ctx γp 1 processed ∗
    "Hctxc" ∷ map_ctx γc 1 claimed ∗
    "Hprocro" ∷ ([∗ map] reqid ↦ proc ∈ processed, reqid [[γp]]↦ false ∨ reqid [[γp]]↦ro true) ∗
    "Havail" ∷ (⌜locked=true⌝ ∨ P).

Definition client_req_inner γi γc returned reqid : iProp Σ :=
  "#Hissue" ∷ reqid [[γi]]↦ro () ∗
  "Hreply" ∷ ( ghost_var returned (1/2) false ∗ reqid [[γc]]↦ false ∨
               ghost_var returned (1/2) false ∗ reqid [[γc]]↦ro true ∗ P ∨
               ghost_var returned (1/2) true ∗ reqid [[γc]]↦ro true ).

Definition request_token γi reqid : iProp Σ :=
  "Hreq_tok" ∷ reqid [[γi]]↦ro ().

Definition response_token γp reqid acquired : iProp Σ :=
  "Hresp_tok" ∷ ⌜acquired=false⌝ ∨ reqid [[γp]]↦ro true.

Theorem client_allocates_reqid γi γp γc reqid :
  inv Nserver (server_inner γi γp γc)
  ={⊤}=∗
  ∃ returned,
    inv Nclient (client_req_inner γi γc returned reqid) ∗
    ghost_var returned (1/2) false.
Proof.
  iIntros "#H".
  iInv "H" as ">Hinner" "Hclose".
  iNamed "Hinner".
  destruct (issued !! reqid) eqn:Hissue.
  { (* Need some kind of assumption that this reqid has not been used yet. *)
    admit.
  }

  iDestruct (big_sepM2_lookup_1_none with "Hissued") as %Hproc; eauto.
  iDestruct (big_sepM2_lookup_1_none with "Hprocessed") as %Hclaim; eauto.

  iMod (map_alloc_ro _ tt with "Hctxi") as "[Hctxi #Hissue]"; eauto.
  iMod (map_alloc _ false with "Hctxp") as "[Hctxp Hproc]"; eauto.
  iMod (map_alloc _ false with "Hctxc") as "[Hctxc Hclaim]"; eauto.

  iDestruct (big_sepM2_insert _ _ _ _ tt false with "[$Hissued]") as "Hissued"; eauto.
  iDestruct (big_sepM2_insert _ _ _ _ false false with "[$Hprocessed]") as "Hprocessed"; eauto.
  iDestruct (big_sepM_insert with "[$Hprocro $Hproc]") as "Hprocro"; eauto.

  iMod (ghost_var_alloc false) as (returned) "[Hret1 Hret2]".

  iMod ("Hclose" with "[-Hclaim Hret1 Hret2]") as "_".
  { iExists _, _, _, _. iFrame. }

  iMod (inv_alloc with "[Hclaim Hret1]") as "Hc".
  2: { iModIntro. iExists returned. iFrame. }

  iFrame "#".
  iLeft. iFrame.
Admitted.

Theorem client_generates_request γi γc returned reqid :
  inv Nclient (client_req_inner γi γc returned reqid)
  ={⊤}=∗
  request_token γi reqid.
Proof.
  iIntros "#H".
  iInv "H" as ">Hinner" "Hclose".
  iNamed "Hinner".
  iFrame "Hissue".
  iApply "Hclose".
  iFrame. iFrame "#".
Qed.

Theorem server_processes_request γi γp γc reqid :
  inv Nserver (server_inner γi γp γc) -∗
  request_token γi reqid
  ={⊤}=∗
  ∃ acquired, response_token γp reqid acquired.
Proof.
  iIntros "#H #Hreq".
  iInv "H" as ">Hinner" "Hclose".
  iNamed "Hinner".
  iDestruct (map_valid with "Hctxi Hreq") as %Hreq.
  iDestruct (big_sepM2_lookup_1_some with "Hissued") as (proc) "%"; eauto.
  destruct proc.
  - iDestruct (big_sepM_lookup_acc with "Hprocro") as "[Hdupreply Hprocro]"; eauto.
    iDestruct "Hdupreply" as "[Hdupreply|#Hdupreply]".
    { iDestruct (map_valid with "Hctxp Hdupreply") as "%". congruence. }
    iFrame "Hdupreply".
    iDestruct ("Hprocro" with "[$Hdupreply]") as "Hprocro".
    iExists true.
    iApply "Hclose". iExists _, _, _, _. iFrame.
  - destruct locked.
    + iExists false.
      iMod ("Hclose" with "[-]") as "_".
      { iExists _, _, _, _. iFrame. }
      iModIntro. iLeft. done.
    + iDestruct (big_sepM2_delete with "Hissued") as "[_ Hissued]"; eauto.
      iDestruct (big_sepM2_insert_delete with "[$Hissued]") as "Hissued".
      iDestruct (big_sepM2_lookup_1_some with "Hprocessed") as (claim) "%"; eauto.
      iDestruct (big_sepM2_delete with "Hprocessed") as "[_ Hprocessed]"; eauto.
      iDestruct (big_sepM2_insert_delete with "[$Hprocessed Havail]") as "Hprocessed".
      { iDestruct "Havail" as "[%|Havail]"; first by congruence. iFrame. }
      iDestruct (big_sepM_insert_acc with "Hprocro") as "[Hproc Hprocro]"; eauto.
      iDestruct "Hproc" as "[Hproc|Hproc]".
      2: { iDestruct (map_valid with "Hctxp Hproc") as "%". congruence. }
      iMod (map_update _ _ true with "Hctxp Hproc") as "[Hctxp Hproc]".
      iMod (map_freeze with "Hctxp Hproc") as "[Hctxp #Hproc]".
      iDestruct ("Hprocro" with "[$Hproc]") as "Hprocro".
      iExists true. iFrame "Hproc".
      iApply "Hclose". iExists _, _, _, true. iFrame.
      rewrite insert_id; eauto. rewrite insert_id; eauto. iFrame.
      iLeft. done.
Qed.

Theorem client_accepts_reply γi γp γc returned reqid :
  ghost_var returned (1/2) false -∗
  inv Nserver (server_inner γi γp γc) -∗
  inv Nclient (client_req_inner γi γc returned reqid) -∗
  response_token γp reqid true
  ={⊤}=∗
  P.
Proof.
  iIntros "Hret #Hs #Hc #Htok".
  iInv "Hc" as ">Hinner_c" "Hclose_c".
  iNamed "Hinner_c".
  iDestruct "Hreply" as "[Hnotclaimed|Hclaimed]".
  2: {
    iDestruct "Hclaimed" as "[(Hret2 & Hclaim & HP)|(Hret2 & HP)]".
    2: { iDestruct (ghost_var_agree with "Hret Hret2") as %Heq. congruence. }
    iCombine "Hret Hret2" as "Hret".
    iMod (ghost_var_update true with "Hret") as "[Hret1 Hret2]".
    iFrame.
    iApply "Hclose_c". iFrame "#". iRight. iRight. iFrame.
  }

  iDestruct "Hnotclaimed" as "[Hret2 Hnotclaimed]".

  iInv "Hs" as ">Hinner_s" "Hclose_s".
  iNamed "Hinner_s".
  iDestruct (map_valid with "Hctxc Hnotclaimed") as %Hnotclaimed.

  iMod (map_update _ _ true with "Hctxc Hnotclaimed") as "[Hctxc Hclaimed]".
  iMod (map_freeze with "Hctxc Hclaimed") as "[Hctxc #Hclaimed]".

  iDestruct (map_ro_valid with "Hctxp [Htok]") as %Hproc.
  { iDestruct "Htok" as "[%|Htok]"; first by congruence. iFrame "Htok". }

  iDestruct (big_sepM2_delete with "Hprocessed") as "[Hproc Hprocessed]"; eauto.
  iDestruct "Hproc" as "[%|Hproc]"; first by intuition congruence.

  iDestruct (big_sepM2_insert_delete _ _ _ _ true true with "[$Hprocessed]") as "Hprocessed".
  { iLeft. iRight. done. }

  iCombine "Hret Hret2" as "Hret".
  iMod (ghost_var_update true with "Hret") as "[Hret Hret2]".

  iMod ("Hclose_s" with "[-Hclose_c Hproc Hret Hret2]") as "_".
  { iExists _, _, _, _. iFrame.
    rewrite insert_id; eauto. iFrame. }

  iFrame.
  iMod ("Hclose_c" with "[-]") as "_".
  { iFrame "#". iFrame. }

  done.
Qed.

End lockservice_proof.
