From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import ctr.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export urpc_lib urpc_proof urpc_spec.
From Perennial.program_proof Require Export marshal_proof.
From iris.algebra Require Import cmra.
From iris.base_logic Require Export mono_nat.
From Perennial.goose_lang Require Import proph.

From Perennial.program_proof.fencing Require Export map.

Section ctr_definitions.

Context `{!gooseGlobalGS Σ}.
Context `{!heapGS Σ}.

Record ctr_names :=
{
  epoch_gn : gname ;
  epoch_token_gn : gname ;
  val_gn : gname ;
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

Program Definition GetSpec γ :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∃ (pv:proph_id) (repV:u64) e,
  proph_once pv repV ∗
  ⌜has_encoding reqData [EncUInt64 e]⌝ ∗
  (|={⊤,∅}=> ∃ latestEpoch, if decide (int.Z latestEpoch < int.Z e)%Z then
      own_latest_epoch γ latestEpoch (1/2)%Qp ∗
      own_unused_epoch γ e ∗
                            (∀ v, own_val γ e v (1/2)%Qp ∗
                                           own_val γ latestEpoch v (1/2)%Qp ∗
                                           own_latest_epoch γ e (1/2)%Qp
                                  ={∅,⊤}=∗ (∀ l, ⌜has_encoding l [EncUInt64 v]⌝ -∗ proph_once pv v -∗ Φ l))
   else if decide (int.Z latestEpoch = int.Z e) then
    ∃ v, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
     own_val γ e v (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ∗ own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ (∀ l, ⌜has_encoding l [EncUInt64 v]⌝ -∗ proph_once pv v -∗ Φ l))
   else
     True))%I.
Next Obligation.
  solve_proper.
Defined.

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


Definition own_Clerk γ (ck:loc) : iProp Σ.
Admitted.

(* NOTE: consider lt_eq_lt_dec: ∀ n m : nat, {n < m} + {n = m} + {m < n} *)
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
Admitted.

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
