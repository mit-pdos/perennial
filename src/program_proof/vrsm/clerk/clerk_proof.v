From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.vrsm Require Export clerk.
From Perennial Require Import clerk.clerk_int_proof vrsm.proph_proof.
From iris.algebra Require Import mono_list.

(** This library layers exactly-once read operations on top of clerk_int_proof, which
   has duplicated reads. *)

Section clerk_proof.
Context `{!heapGS Σ}.
Context {params:pbParams.t}.
Import pbParams.
Import Sm.

Context `{!pbG Σ}.

Record proph_req_names :=
{
  op_gn:gname;
  finish_gn:gname;
}.

Definition own_Clerk ck γ : iProp Σ :=
  is_proph_read_inv γ ∗ own_int_Clerk ck γ.

Local Lemma wp_Clerk__ApplyReadonly2' γ ck op_sl op (op_bytes:list u8) (Φ:val → iProp Σ) :
is_readonly_op op →
has_op_encoding op_bytes op →
own_Clerk ck γ -∗
own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
  □(∀ opsToGet, |={⊤∖↑pbN∖↑prophReadLogN,∅}=>
     ((∃ ops, own_op_log γ ops ∗
       (⌜ops = opsToGet⌝ → own_op_log γ ops ={∅,⊤∖↑pbN∖↑prophReadLogN}=∗
       □(∀ reply_sl, own_slice_small reply_sl byteT (DfracOwn 1) (compute_reply ops op) -∗
                    own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
                    own_Clerk ck γ -∗ Φ (slice_val reply_sl)%V)))) ∨
       (True ={∅,⊤∖↑pbN∖↑prophReadLogN}=∗
       □(∀ reply_sl, own_slice_small reply_sl byteT (DfracOwn 1) (compute_reply opsToGet op) -∗
                  own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
                  own_Clerk ck γ -∗ Φ (slice_val reply_sl)%V)))
 -∗
WP clerk.Clerk__ApplyRo2 #ck (slice_val op_sl) {{ Φ }}.
Proof.
  iIntros (??) "[#Hinv Hck] ? #Hupd".
  wp_apply (wp_Clerk__ApplyReadonly_int with "[$] [$] [-]"); try done.
  iModIntro.
  iInv "Hinv" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hoplog Hintlog]".
  iMod (fupd_mask_subseteq (⊤∖↑pbN∖↑prophReadLogN)) as "Hmask".
  { solve_ndisj. }
  iSpecialize ("Hupd" $! σ).
  iMod "Hupd" as "[Hupd|Htriv]".
  {
    iDestruct "Hupd" as (?) "[Hoplog2 Hupd]".
    iDestruct (own_valid_2 with "Hoplog Hoplog2") as %Hvalid.
    assert (σ = ops); last subst.
    { rewrite mono_list_auth_dfrac_op_valid_L in Hvalid. by destruct Hvalid. }
    iModIntro.
    iExists _; iFrame.
    iIntros "Hintlog2".
    iMod ("Hupd" with "[//] [$]") as "#Hupd".
    iMod "Hmask". iMod ("Hclose" with "[Hintlog2 Hoplog]").
    { iExists _; iFrame. }
    iModIntro. iModIntro.
    iIntros.
    iApply ("Hupd" with "[$] [$] [$]").
  }
  {
    iModIntro.
    iExists _.
    iFrame.
    iIntros "Hintlog".
    iMod ("Htriv" with "[$]") as "#Hupd".
    iMod "Hmask". iMod ("Hclose" with "[Hintlog Hoplog]").
    { iExists _; iFrame. }
    iModIntro. iIntros. iModIntro.
    iIntros.
    iApply ("Hupd" with "[$] [$] [$]").
  }
Qed.

Implicit Types γreq : proph_req_names.

Definition operation_incomplete γreq : iProp Σ := own γreq.(op_gn) (DfracOwn 1).
Definition operation_receipt γreq : iProp Σ := own γreq.(op_gn) (DfracDiscarded).

Lemma complete_operation γreq :
  operation_incomplete γreq ==∗ operation_receipt γreq.
Proof.
  iIntros "H1".
  iApply (own_update with "H1").
  apply (cmra_update_exclusive).
  done.
Qed.

Definition result_claimed γreq : iProp Σ := own γreq.(finish_gn) (DfracDiscarded).
Definition result_unclaimed γreq : iProp Σ := own γreq.(finish_gn) (DfracOwn 1).

Definition read_fupd γ readOp (Q:list u8 → iProp Σ) : iProp Σ :=
£ 1 ∗ (|={⊤∖↑pbN∖↑prophReadN,∅}=> ∃ ops, own_op_log γ ops ∗
  (own_op_log γ ops ={∅,⊤∖↑pbN∖↑prophReadN}=∗ Q (compute_reply ops readOp))).

Definition prophReadReqN := prophReadN .@ "req".
Definition prophetic_read_inv prophV γ γreq readOp Φ : iProp Σ :=
  inv prophReadReqN (
        (*
          XXX: This invariant is a bit ad-hoc. A more principled approach would be to
          give the server a fraction of the ghost resources for the "state" of
          this protocol at the beginning of time, and for this invariant to have
          only a fraction of it.
        *)
  operation_incomplete γreq ∗ read_fupd γ readOp Φ ∨
  operation_receipt γreq ∗ ((Φ prophV) ∨ result_claimed γreq))
.

Lemma wp_Clerk__ApplyReadonly γ ck op_sl op (op_bytes:list u8) (Φ:val → iProp Σ) :
is_readonly_op op →
has_op_encoding op_bytes op →
own_Clerk ck γ -∗
own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
((|={⊤∖↑pbN∖↑prophReadN,∅}=> ∃ ops, own_op_log γ ops ∗
  (own_op_log γ ops ={∅,⊤∖↑pbN∖↑prophReadN}=∗
     (∀ reply_sl, own_slice_small reply_sl byteT (DfracOwn 1) (compute_reply ops op) -∗
                  own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
                  own_Clerk ck γ -∗ Φ (slice_val reply_sl)%V)))) -∗
WP clerk.Clerk__ApplyRo #ck (slice_val op_sl) {{ Φ }}.
Proof.
  iIntros (??) "Hck Hsl Hupd".
  wp_call.
  wp_apply (wp_NewProphBytes).
  iIntros (??) "Hproph".
  wp_pure1_credit "Hlc".
  iAssert (|={⊤}=> ∃ γreq, result_unclaimed γreq ∗ prophetic_read_inv b γ γreq _
  (λ reply, ∀ reply_sl : Slice.t,
             own_slice_small reply_sl byteT (DfracOwn 1) reply -∗
             own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗ own_Clerk ck γ -∗ Φ (slice_val reply_sl))
          )%I with "[Hupd Hlc]" as ">H".
  {
    iMod (own_alloc (DfracOwn 1)) as (γop) "Hop".
    { done. }
    iMod (own_alloc (DfracOwn 1)) as (γfinish) "Hfinish".
    { done. }
    iExists {| op_gn := γop ; finish_gn := γfinish |}.
    iFrame. iMod (inv_alloc with "[-]") as "$"; last done.
    iNext. iLeft. iFrame "Hop ∗".
  }
  iDestruct "H" as (?) "[Hfinish #Hinv]".
  wp_pures.
  wp_bind (Clerk__ApplyRo2 _ _).
  wp_apply (wp_frame_wand with "[Hproph Hfinish]").
  { iNamedAccu. }
  wp_apply (wp_Clerk__ApplyReadonly2' with "Hck Hsl []"); try done.
  iModIntro.
  iInv "Hinv" as "Hi" "Hclose".
  iIntros (?).
  iDestruct "Hi" as "[Hnotdone|Hdone]".
  2:{ (* case: one of the low-level uRPC requests already fired the fupd before. *)
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iRight.
    iIntros "_". iMod "Hmask".
    iDestruct "Hdone" as "[#>Hreceipt ?]".
    iMod ("Hclose" with "[-]").
    { iRight. iFrame "∗#". }
    iModIntro.
    iModIntro.
    iIntros (?) "Hrep_sl Hop_sl Hck".
    iNamed 1.
    wp_pures.
    wp_apply (wp_ResolveBytes with "[$Hproph $Hrep_sl]").
    iIntros "[% ?]".
    subst.
    wp_pure1_credit "Hlc".
    wp_pures.
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
    iDestruct "Hi" as "[[Hbad _]| Hi]".
    { iDestruct (own_valid_2 with "Hbad Hreceipt") as %?.
      exfalso. done. }
    iDestruct "Hi" as "[_ [HΦ | Hbad]]".
    2:{
      iDestruct (own_valid_2 with "Hbad Hfinish") as %?.
      exfalso. done. }
    iMod (own_update with "Hfinish") as "Hfinish".
    { apply dfrac_discard_update. }
    iMod ("Hclose" with "[Hfinish]").
    { iRight. iFrame "#". iRight. iFrame. }
    iModIntro.
    iApply ("HΦ" with "[$] [$] [$]").
  }
  { (* other case: we get to fire the fupd! *)
    destruct (decide (compute_reply x op = b)) eqn:X.
    {
      subst.
      iDestruct "Hnotdone" as "[>Hinc Hfupd]".
      iLeft.
      iDestruct "Hfupd" as "[>Hlc Hfupd]".
      iMod (lc_fupd_elim_later with "Hlc Hfupd") as "Hfupd".
      iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "Hfupd" as "Hupd".
      { solve_ndisj. }
      iDestruct "Hupd" as (?) "[Hlog Hupd]".
      iModIntro. iExists _; iFrame.
      iIntros "% Hlog"; subst.
      iMod ("Hupd" with "Hlog") as "HQ".
      iMod (complete_operation with "Hinc") as "#Hreceipt".
      iMod "Hmask".
      iMod ("Hclose" with "[HQ]").
      { iRight. iFrame "#". iLeft. iNext. iFrame "HQ". }
      iModIntro.
      iModIntro.
      iIntros (?) "Hrep_sl ? ?". iNamed 1.
      wp_pures.
      wp_apply (wp_ResolveBytes with "[$Hrep_sl $Hproph]").
      iIntros "[% ?]".
      wp_pure1_credit "Hlc".
      wp_pures.
      iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
      iDestruct "Hi" as "[[Hbad _]| Hi]".
      { iDestruct (own_valid_2 with "Hbad Hreceipt") as %?.
        exfalso. done. }
      iDestruct "Hi" as "[_ [HΦ | Hbad]]".
      2:{
        iDestruct (own_valid_2 with "Hbad Hfinish") as %?.
        exfalso. done. }
      iMod (own_update with "Hfinish") as "Hfinish".
      { apply dfrac_discard_update. }
      iMod ("Hclose" with "[Hfinish]").
      { iRight. iFrame "#". iRight. iFrame. }
      iModIntro.
      iApply ("HΦ" with "[$] [$] [$]").
    }
    {
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "Hmask".
      iRight.
      iIntros "_". iMod "Hmask".
      iMod ("Hclose" with "[-]").
      { iFrame "∗#". }
      iModIntro.
      iModIntro.
      iIntros (?) "Hrep_sl Hop_sl Hck".
      iNamed 1.
      wp_pures.
      wp_apply (wp_ResolveBytes with "[$Hproph $Hrep_sl]").
      iIntros "[% ?]".
      subst. by exfalso.
    }
  }
Qed.

Lemma wp_Clerk__Apply γ ck op_sl op (op_bytes:list u8) (Φ:val → iProp Σ) :
has_op_encoding op_bytes op →
own_Clerk ck γ -∗
own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
□((|={⊤∖↑pbN∖↑prophReadN,∅}=> ∃ ops, own_op_log γ ops ∗
  (⌜apply_postcond ops op⌝ -∗ own_op_log γ (ops ++ [op]) ={∅,⊤∖↑pbN∖↑prophReadN}=∗
     (∀ reply_sl, own_slice_small reply_sl byteT (DfracOwn 1) (compute_reply ops op) -∗
                  own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
                  own_Clerk ck γ -∗ Φ (slice_val reply_sl)%V)))) -∗
WP clerk.Clerk__Apply #ck (slice_val op_sl) {{ Φ }}.
Proof.
  iIntros (?) "[#Hinv Hck] ? #Hupd".
  wp_apply (wp_Clerk__Apply_int with "[$] [$] [-]"); try done.
  iModIntro.
  iInv "Hinv" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hoplog Hintlog]".
  iMod (fupd_mask_subseteq (⊤∖↑pbN∖↑prophReadN)) as "Hmask".
  { solve_ndisj. }
  iMod "Hupd".
  iDestruct "Hupd" as (?) "[Hoplog2 Hupd]".
  iDestruct (own_valid_2 with "Hoplog Hoplog2") as %Hvalid.
  assert (σ = ops); last subst.
  { rewrite mono_list_auth_dfrac_op_valid_L in Hvalid. by destruct Hvalid. }
  iModIntro.
  iExists _; iFrame.
  iIntros "H Hintlog2".
  iCombine "Hoplog Hoplog2" as "Hoplog".
  iMod (own_update with "Hoplog") as "Hoplog".
  { apply mono_list_update. instantiate (1:=ops ++ [op]). by apply prefix_app_r. }
  iDestruct "Hoplog" as "[Hoplog Hoplog2]".
  iMod ("Hupd" with "H [$]") as "Hupd".
  iMod "Hmask". iMod ("Hclose" with "[Hintlog2 Hoplog]").
  { iExists _; iFrame. }
  iModIntro.
  iIntros.
  iApply ("Hupd" with "[$] [$] [$]").
Qed.

Lemma wp_MakeClerk γ configHosts configHosts_sl :
  {{{
        "#HconfSl" ∷ readonly (own_slice_small configHosts_sl uint64T (DfracOwn 1) configHosts) ∗
        "#Hconf" ∷ is_pb_config_hosts configHosts γ
  }}}
    Make (slice_val configHosts_sl)
  {{{
        (ck:loc), RET #ck; own_Clerk ck γ
  }}}
.
Proof.
  iIntros (?) "#H HΦ".
  iNamed "H".
  wp_apply (wp_MakeClerk_int with "[]").
  { iFrame "#%". }
  iIntros (?) "?". iApply "HΦ".
  iNamed "Hconf".
  iFrame "∗#".
Qed.

End clerk_proof.
