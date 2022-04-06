From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import ctr.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export urpc_lib urpc_proof urpc_spec.
From Perennial.program_proof Require Export marshal_proof.
From iris.algebra Require Import cmra.
From iris.base_logic Require Export mono_nat.
From Perennial.goose_lang Require Import proph.
From Perennial.goose_lang Require Import prelude ffi.grove_exit_axiom.

From Perennial.program_proof.fencing Require Export map.

Section ctr_definitions.

Context `{!gooseGlobalGS Σ}.
Context `{!heapGS Σ}.

Record ctr_names :=
{
  epoch_gn : gname ;
  epoch_token_gn : gname ;
  val_gn : gname ;
  urpc_gn : server_chan_gnames ;
}.

Implicit Type γ : ctr_names.

Class ctrG Σ :=
  { mnat_inG:> mono_natG Σ;
    val_inG:> mapG Σ u64 u64;
    unused_tok_inG:> mapG Σ u64 bool
  }.

Context `{!ctrG Σ}.

Definition own_latest_epoch γ (e:u64) (q:Qp) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) q (int.nat e).

Definition is_latest_epoch_lb γ (e:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (int.nat e).

Definition own_unused_epoch γ (e:u64) : iProp Σ :=
  e ⤳[γ.(epoch_token_gn)] false.

Definition own_val γ (e:u64) (v:u64) (q:Qp): iProp Σ :=
  e ⤳[γ.(val_gn)]{# q } v ∗
  e ⤳[γ.(epoch_token_gn)]□ true.

(* If someone has own_val, that means the ctr sever saw that epoch number, which
   means the own_unused_epoch was given up. *)
Lemma unused_own_val_false γ e v q :
  own_unused_epoch γ e -∗ own_val γ e v q -∗ False.
Proof.
Admitted.

Lemma own_val_combine γ e v1 q1 v2 q2 :
  own_val γ e v1 q1 -∗ own_val γ e v2 q2 -∗ own_val γ e v1 (q1 + q2) ∗ ⌜v1 = v2⌝.
Proof.
Admitted.

Lemma own_val_split γ e v q1 q2 :
  own_val γ e v (q1 + q2) -∗ own_val γ e v q1 ∗ own_val γ e v q2.
Proof.
Admitted.
End ctr_definitions.

Module ctr.
Section ctr_proof.
Context `{!ctrG Σ}.
Context `{!heapGS Σ}.
Implicit Type γ:ctr_names.

Definition own_Server γ (s:loc) : iProp Σ :=
  ∃ (v latestEpoch:u64),
  "Hv" ∷ s ↦[Server :: "v"] #v ∗
  "HlatestEpoch" ∷ s ↦[Server :: "lastEpoch"] #latestEpoch ∗
  "HghostLatestEpoch" ∷ own_latest_epoch γ latestEpoch (1/2) ∗
  "HghostV" ∷ own_val γ latestEpoch v (1/2)
.

Definition ctrN := nroot .@ "ctr".

Definition is_Server γ (s:loc) : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock ctrN mu (own_Server γ s)
.

Definition GetPre γ pv e Φ : iProp Σ :=
  ∃ (repV:u64),
  proph_once pv repV ∗
  (|={⊤,∅}=> ∃ latestEpoch, if decide (int.Z latestEpoch < int.Z e)%Z then
      own_latest_epoch γ latestEpoch (1/2)%Qp ∗
      own_unused_epoch γ e ∗
                            (∀ v, own_val γ e v (1/2)%Qp ∗
                                           own_val γ latestEpoch v (1/2)%Qp ∗
                                           own_latest_epoch γ e (1/2)%Qp
                                           ={∅,⊤}=∗ Φ #v)
   else if decide (int.Z latestEpoch = int.Z e) then
    ∃ v, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
     own_val γ e v (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ∗ own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ Φ #v)
   else
     True).

Definition has_GetReply_encoding (l:list u8) (err v:u64) :=
  has_encoding l [EncUInt64 err; EncUInt64 v].

Program Definition Get_spec γ :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∃ (pv pe:proph_id) (repV:u64) e,
  proph_once pv repV ∗
  ⌜has_encoding reqData [EncUInt64 e]⌝ ∗
  (|={⊤,∅}=> ∃ latestEpoch, if decide (int.Z latestEpoch < int.Z e)%Z then
      own_latest_epoch γ latestEpoch (1/2)%Qp ∗
      own_unused_epoch γ e ∗
                            (∀ v, own_val γ e v (1/2)%Qp ∗
                                           own_val γ latestEpoch v (1/2)%Qp ∗
                                           own_latest_epoch γ e (1/2)%Qp
                                  ={∅,⊤}=∗ (∀ l, ⌜has_GetReply_encoding l 0 v⌝ -∗ proph_once pv v -∗ Φ l))
   else if decide (int.Z latestEpoch = int.Z e) then
    ∃ v, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
     own_val γ e v (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ∗ own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ (∀ l, ⌜has_GetReply_encoding l 0 v⌝ -∗ proph_once pv v -∗ Φ l))
   else
     (* FIXME: in this case, the server returns *)
      (∀ l, ⌜has_GetReply_encoding l 1 0⌝ -∗ proph_once pe true -∗ Φ l)
     ))%I.
Next Obligation.
  solve_proper.
Defined.

Context `{!rpcregG Σ}.

Definition is_host (host:u64) γ : iProp Σ :=
  handler_spec γ.(urpc_gn) host (U64 0) (Get_spec γ) ∗
  handlers_dom γ.(urpc_gn) {[ (U64 0) ]}
.

Definition own_Clerk γ (ck:loc) : iProp Σ :=
  ∃ (cl:loc) host,
  "#Hcl" ∷ readonly (ck ↦[Clerk :: "cl"] #cl) ∗
  "#Hcl_own" ∷ is_RPCClient cl host ∗
  "#Hhost" ∷ is_host host γ
.

Lemma wp_Clerk__Get γ ck (e:u64) :
  ∀ Φ,
  own_Clerk γ ck -∗
  (|={⊤,∅}=> ∃ latestEpoch, if decide (int.Z latestEpoch < int.Z e)%Z then
      own_latest_epoch γ latestEpoch (1/2)%Qp ∗
      own_unused_epoch γ e ∗
                            (∀ v, own_val γ e v (1/2)%Qp ∗
                                           own_val γ latestEpoch v (1/2)%Qp ∗
                                           own_latest_epoch γ e (1/2)%Qp
                                           ={∅,⊤}=∗ (own_Clerk γ ck -∗ Φ #v))
   else if decide (int.Z latestEpoch = int.Z e) then
    ∃ v, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
     own_val γ e v (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ∗ own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ (own_Clerk γ ck -∗ Φ #v))
   else
     True) -∗
    WP Clerk__Get #ck #e {{ Φ }}.
Proof.
  iIntros (Φ) "Hck Hupd".
  wp_lam.
  wp_pures.
  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { done. }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (req_sl reqData) "(%Hreq_enc & %Hreq_len & Hreq_sl)".
  wp_pures.
  wp_apply (wp_NewProph_once (T:=u64)).
  iIntros (valProph v) "Hprophv".
  wp_apply (wp_NewProph_once (T:=bool)).
  iIntros (errProph err) "Hprophe".
  wp_pures.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  wp_apply (wp_Client__Call _ _ _ _ _ _ _ _ _ _
                          (λ (l:list u8), ∃ v e, ⌜has_GetReply_encoding l e v⌝ ∗
                                  if (decide (int.Z e = 0)) then
                                    (own_Clerk γ ck -∗ Φ #v) ∗ proph_once valProph v
                                  else
                                    proph_once errProph true)%I
             with "[$Hreq_sl $Hrep $Hcl_own Hupd Hprophv Hprophe]").
  {
    iDestruct "Hhost" as "[$ _]".
    iAssert (□ proph_once valProph v)%I with "[Hprophv]" as "Hprophv".
    { admit. } (* FIXME: this is false; we're gonna need another piece of ghost state that matches the value of the prophecy, but is persistent *)
    iAssert (□ proph_once errProph e)%I with "[Hprophe]" as "Hprophe".
    { admit. }
    iDestruct "Hprophv" as "#Hprophv".
    iDestruct "Hprophe" as "#Hprophe".
    do 2 iModIntro.
    iAssert
      (|={⊤,∅}=> ∃ latestEpoch, if decide (int.Z latestEpoch < int.Z e)%Z then
      own_latest_epoch γ latestEpoch (1/2)%Qp ∗
      own_unused_epoch γ e ∗
                            (∀ v, own_val γ e v (1/2)%Qp ∗
                                           own_val γ latestEpoch v (1/2)%Qp ∗
                                           own_latest_epoch γ e (1/2)%Qp
                                           ={∅,⊤}=∗ (own_Clerk γ ck -∗ Φ #v))
   else if decide (int.Z latestEpoch = int.Z e) then
    ∃ v, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
     own_val γ e v (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ∗ own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ (own_Clerk γ ck -∗ Φ #v))
   else
     True)%I with "[]" as "Hupd".
    { admit. } (* FIXME: will need to put this or the reply in escrow *)
    simpl.
    iExists valProph,errProph,_,_; iFrame "Hprophv".
    iSplitL ""; first done.
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (latestEpoch) "Hupd".
    iExists latestEpoch.
    destruct (decide (int.Z latestEpoch < int.Z e)%Z).
    {
      iDestruct "Hupd" as "($ & $ & Hupd)".
      iIntros (val) "Hpre".
      iDestruct ("Hupd" with "Hpre") as "Hupd".
      iMod "Hupd".
      iModIntro.
      iIntros.
      iExists _,_.
      iSplitL ""; first done.
      setoid_rewrite decide_True; last done.
      iFrame "Hupd".
      iFrame.
    }
    { (* similar to above *)
      admit.
    }
  }

  iIntros (errCode) "(_ & Hreq_sl & Hpost)".
  (* will be able to show that errCode = None iff err = false by prophecy.Resolve *)

  wp_pures.
  destruct errCode.
  { (* case: error *)
    rewrite bool_decide_false; last first.
    { by destruct c. }
    wp_pures.
    wp_apply (wp_Exit).
    by iIntros.
  (* FIXME: I don't know if I need to prophesize about the error code; if
     there's an error, we just exit, and the caller finds out nothing *)
  }
  (* case: no error *)
  wp_pures.
  iNamed "Hpost".
  iDestruct "Hpost" as "(Hrep & Hrep_sl & Hpost)".
  wp_load.
  clear v.
  clear err.
  iDestruct "Hpost" as (v err) "(%Hrep_enc & Hpost)".

  (* TODO: move this to a different lemma *)
  wp_lam.
  iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_small".
  wp_apply (wp_new_dec with "[$Hrep_small]").
  { done. }
  iIntros (dec) "Hdec".
  wp_pures.
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (r) "Hr".
  iDestruct (struct_fields_split with "Hr") as "HH".
  iNamed "HH".
  simpl.
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_storeField.
  wp_pures.
  (* TODO: move the above to a different lemma *)
Admitted.

Lemma wp_Server__Get γ s (e:u64) (rep:loc) (dummy_err dummy_val:u64) :
  is_Server γ s -∗
  {{{
        "Hrep_error" ∷ rep ↦[GetReply :: "err"] #dummy_err ∗
        "Hrep_val" ∷ rep ↦[GetReply :: "val"] #dummy_val
  }}}
    Server__Get #s #e #rep
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros "#His_srv !#" (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_pures.
  iNamed "His_srv".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.

  wp_storeField.
  wp_loadField.
  wp_pures.

  wp_if_destruct.
  {
    wp_loadField.
    admit.
  }
Admitted.


(* NOTE: consider lt_eq_lt_dec: ∀ n m : nat, {n < m} + {n = m} + {m < n} *)

Lemma wp_Clerk__Put γ ck (e v:u64) :
  ∀ Φ,
  own_Clerk γ ck -∗
  (|={⊤,∅}=> ∃ latestEpoch, if decide (int.Z latestEpoch < int.Z e)%Z then
      own_latest_epoch γ latestEpoch (1/2)%Qp ∗
      own_unused_epoch γ e ∗
                            (own_val γ e v (1/2)%Qp ∗
                             (∃ oldv, own_val γ latestEpoch oldv (1/2)%Qp) ∗
                                           own_latest_epoch γ e (1/2)%Qp
                                           ={∅,⊤}=∗ (own_Clerk γ ck -∗ Φ #()))
   else if decide (int.Z latestEpoch = int.Z e) then
    ∃ oldv, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
     own_val γ e oldv (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ∗ own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ (own_Clerk γ ck -∗ Φ #()))
   else
     True) -∗
    WP Clerk__Put #ck #v #e {{ Φ }}.
Proof.
Admitted.

Lemma wp_MakeClerk host γ :
  (* is_host host γ *)
  {{{
      True
  }}}
    MakeClerk #host
  {{{
      (ck:loc), RET #ck; own_Clerk γ ck
  }}}.
Proof.
Admitted.

End ctr_proof.
End ctr.
