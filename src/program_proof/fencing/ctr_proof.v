From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import ctr.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.grove_shared Require Export erpc_lib urpc_proof urpc_spec.
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
    unused_tok_inG:> mapG Σ u64 bool;
    tok_inG :> inG Σ (dfracR)
  }.

Context `{!ctrG Σ}.

Definition own_latest_epoch γ (e:u64) (q:Qp) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) q (int.nat e).

Definition is_latest_epoch_lb γ (e:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (int.nat e).

Definition is_latest_epoch_lb_strict γ (e:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (int.nat e + 1).

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

Lemma own_latest_epoch_combine γ e1 e2 q1 q2 :
  own_latest_epoch γ e1 (q1) -∗ own_latest_epoch γ e2 q2 -∗ own_latest_epoch γ e1 (q1 + q2) ∗ ⌜e1 = e2⌝.
Proof.
Admitted.

Lemma own_latest_epoch_update e γ eold :
  own_latest_epoch γ eold 1 ==∗ own_latest_epoch γ e 1.
Proof.
Admitted.

Lemma own_latest_epoch_get_lb γ e q :
  own_latest_epoch γ e q -∗ is_latest_epoch_lb γ e.
Proof.
Admitted.

Lemma own_latest_epoch_with_lb γ e e' q :
  own_latest_epoch γ e q -∗ is_latest_epoch_lb γ e' -∗ ⌜int.Z e' ≤ int.Z e⌝.
Proof.
Admitted.

End ctr_definitions.

Module ctr.
Section ctr_proof.
Context `{!ctrG Σ}.
Context `{!heapGS Σ}.
Implicit Type γ:ctr_names.

Definition ctrN := nroot .@ "ctr".

Definition unused_epoch_inv γ : iProp Σ :=
  inv ctrN (
        [∗ set] e ∈ (fin_to_set u64), own_unused_epoch γ e ∨ own_val γ e 0 1
      ).

Lemma activate_unused_epoch v γ e:
  unused_epoch_inv γ -∗ own_unused_epoch γ e ={↑ctrN}=∗ own_val γ e v 1.
Proof.
Admitted.

Definition own_Server γ (s:loc) : iProp Σ :=
  ∃ (v latestEpoch:u64),
  "Hv" ∷ s ↦[Server :: "v"] #v ∗
  "HlatestEpoch" ∷ s ↦[Server :: "lastEpoch"] #latestEpoch ∗
  "HghostLatestEpoch" ∷ own_latest_epoch γ latestEpoch (1/2) ∗
  "HghostV" ∷ own_val γ latestEpoch v (1/2)
.

Definition is_Server γ (s:loc) : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock ctrN mu (own_Server γ s) ∗
  "#HunusedInv" ∷ unused_epoch_inv γ
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

(* FIXME: why is it normal to do |={⊤ ∖ mask, ∅}=> rather than |={⊤, mask}=> ? *)
(* Doing {T ∖ ctrN, ∅} means that I have to open up the invariant with ctrN
   before firing this fupd. On the other hand, if it's {T, ctrN}, I can
   optionally open the invariant after firing the fupd *)
Definition EnterNewEpoch_spec γ (e:u64) (Φ:iProp Σ) : iProp Σ :=
|={⊤, ↑ctrN}=> ∃ latestEpoch, if decide (int.Z latestEpoch < int.Z e)%Z then
    own_latest_epoch γ latestEpoch (1/2)%Qp ∗
    own_unused_epoch γ e ∗ (∀ v, own_val γ e v (1/2)%Qp -∗
                                 own_val γ latestEpoch v (1/2)%Qp -∗
                                 own_latest_epoch γ e (1/2)%Qp ={↑ctrN,⊤}=∗ Φ)
else (* XXX: it might seem like the server shouldn't need any resources in this case. *)
  (own_latest_epoch γ latestEpoch (1/2)%Qp ∗
   (own_latest_epoch γ latestEpoch (1/2)%Qp ={↑ctrN, ⊤}=∗ Φ))
.

Lemma EnterNewEpoch_spec_wand γ e Φ1 Φ2 :
  (Φ1 -∗ Φ2) -∗
  EnterNewEpoch_spec γ e Φ1 -∗
  EnterNewEpoch_spec γ e Φ2
.
Proof.
  iIntros "Hwand Hupd".
  rewrite /EnterNewEpoch_spec.
  iMod "Hupd".
  iDestruct "Hupd" as (?) "Hupd".
  iExists latestEpoch.
  destruct (decide (_)).
  {
    iModIntro.
    iDestruct "Hupd" as "($ & $ & Hupd)".
    iIntros (v) "H1 H2 H3".
    iApply "Hwand".
    iMod ("Hupd" $! v with "H1 H2 H3") as "$".
    done.
  }
  {
    iModIntro.
    iDestruct "Hupd" as "[$ Hupd]".
    iIntros "H1".
    iApply "Hwand".
    by iApply "Hupd".
  }
Qed.

Definition Get_core_spec γ (e:u64) (Φ:u64 → iProp Σ) : iProp Σ :=
  |={∅}=> ∃ v, own_val γ e v (1/2)%Qp ∗ (* XXX: have a ∅ here because this runs inside of a larger atomic step *)
    (own_val γ e v (1/2)%Qp ={∅}=∗ (Φ v))
.

Lemma Get_core_spec_wand γ e Φ1 Φ2 :
  (∀ x, Φ1 x -∗ Φ2 x) -∗
  Get_core_spec γ e Φ1 -∗
  Get_core_spec γ e Φ2
.
Proof.
  iIntros "Hwand Hupd".
  rewrite /Get_core_spec.
  iMod "Hupd".
  iModIntro.
  iDestruct "Hupd" as (v) "Hupd".
  iExists v.
  iDestruct "Hupd" as "[$ Hupd]".
  iIntros "H1".
  iApply "Hwand".
  iApply "Hupd".
  iFrame.
Qed.

Definition Get_server_spec γ (e:u64) (Φ:u64 → u64 → iProp Σ) : iProp Σ :=
|={⊤,∅}=> ∃ latestEpoch, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
  if decide (int.Z latestEpoch = int.Z e)%Z then
    Get_core_spec γ e (λ v, own_latest_epoch γ e (1/2) ={∅,⊤}=∗ Φ 0 v)
  else
    (own_latest_epoch γ latestEpoch (1/2)%Qp ={∅,⊤}=∗ (∀ dummy_val, Φ 1 dummy_val))
.

(*
SpecMonad T := (T → iProp Σ) → iProp Σ = Hom(Hom(T, P), P)
Sort of a "double dual". Covariant because Hom(-, P) is contravariant.

1. Functoriality:
Let f: A → B. Then,
SpecMonad(f) : SpecMonad(A) → SpecMonad(B) is given by
  (ma: (A → iProp Σ) → iProp Σ ) ↦ (λ (fb:B → iProp Σ), (ma (λ a, fb(f(a)))))

2. Unit transformation.
η : 1_C → SpecMonad

η_T : T → Hom(Hom(T, P), P) given by
η_T : (a:T)  →  (λ (fa:T → iProp Σ), fa a)

3. Multiplication transformation.

μ : SpecMonad ∘ SpecMonad → SpecMonad

μ_T: SpecMonad(SpecMonad(T)) → SpecMonad(t)

μ_T : (f: Hom(Hom(Hom(Hom(T, P), P), P), P)) ↦
(λ (fa:T → P), f (λ (g:((T → P) → P) → P), g (λ (h:(T → P) → P), h fa)))

Definition SpecMonad_mul (T:Type) :
  ((((T → iProp Σ) → iProp Σ) → iProp Σ) → iProp Σ) → ((T → iProp Σ) → iProp Σ)
  :=
  λ f, (λ fa, f (λ g, g (λ h, h fa)  ))....

That's a bit complicated. Maybe easier to see via adjunctions?
*)


(* Via adjunctions.
Let F : C → C^{op} be the functor F(T) = (T → iProp Σ) = Hom(T,P).
Let G : C^{op} → C be the same.
Let's show that F and G are adjoint:

NTS: ∀ X Y, Hom_op(Hom(Y,P), X) ≅ Hom(Y, Hom(X,P))
But this is obvious:
Hom_op(Hom(Y,P), X) ≅ Hom(X, Hom(Y,P)) ≅ Hom(Y, Hom(X,P)).
Have to think about naturality a bit.

Given f : (Y → P) → X, take
  λ y x, f (λ y', )

ε: F∘G → 1_{C^op}
η: 1_C → G∘F

We already defined η above.
Let's define
ε_A : Hom_op(F(G(A), A)
ε_A : Hom(A, F(G(A)),
so we can define ε_A = η_A, by flipping arrows.

The multiplication map for G∘F can be given by

SpecMonad² = G ∘ F ∘ G ∘ F → G ∘ (1_{C^op}) ∘ F = SpecMonad
by using ε in the middle.
*)

(* Via bind.
  β : SpecMonad(A) → (a → SpecMonad(B)) → SpecMonad(B)

  β:(sa: (A → P) → P) ↦ (λ (f:a → SpecMonad(B)), (λ (fb:b → P), sa (λ a, ((f a) fb) )  ))
*)

(* NOTE: some reference about this kind of pretty general monad construction:
 "On Double Dual Monads" https://www.mscand.dk/article/download/10995/9016 *)

(* TODO: this is pretty monadic *)
Program Definition Get_spec γ :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∃ (repV:u64) e,
    ⌜has_encoding reqData [EncUInt64 e]⌝ ∗ EnterNewEpoch_spec γ e (
       Get_server_spec γ e (λ v err, (∀ l, ⌜has_GetReply_encoding l err v⌝ -∗ Φ l))
     ))%I
.
Next Obligation.
  rewrite /EnterNewEpoch_spec /Get_server_spec /Get_core_spec.
  solve_proper.
Defined.

Definition getN := nroot .@ "ctr.get".

Record get_req_names :=
{
  op_gn:gname;
  finish_gn:gname;
}.

Implicit Types γreq : get_req_names.

Definition operation_incomplete γreq : iProp Σ := own γreq.(op_gn) (DfracOwn 1).
Definition operation_receipt γreq : iProp Σ := own γreq.(op_gn) (DfracDiscarded).

Definition result_claimed γreq : iProp Σ := own γreq.(finish_gn) (DfracOwn 1).

Definition Get_req_inv prophV e γ γreq Φ : iProp Σ :=
  inv getN (
        (* The server doesn't actually need quite this powerful of a fupd for
           Get_server_spec.  It only needs a fupd that can be fired specifically
           on the input prophV, but it's convenient to just reuse the more
           powerful spec definition.
         *)
    operation_incomplete γreq ∗ (
     (EnterNewEpoch_spec γ e (Get_server_spec γ e (λ err v, if decide (err = 0) then Φ v else True)%I) ) ∨
     (Get_server_spec γ e (λ err v, if decide (err = 0) then Φ v else True)%I)
    ) ∨
    operation_receipt γreq ∗ ((Φ prophV) ∨ result_claimed γreq) )
.

Program Definition Get_proph_spec γ :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∃ (prophV e:u64) γreq Φclient,
    ⌜has_encoding reqData [EncUInt64 e]⌝ ∗
    (Get_req_inv prophV e γ γreq Φclient) ∗
    (∀ l err v, ⌜has_GetReply_encoding l err v⌝ -∗
      (if (decide (err = 0)) then operation_receipt γreq else True) -∗ Φ l)
  )%I
.
Next Obligation.
  rewrite /Get_req_inv /EnterNewEpoch_spec /Get_server_spec /Get_core_spec.
  solve_proper.
Defined.

Context `{!urpcregG Σ}.

Definition is_host (host:u64) γ : iProp Σ :=
  handler_spec γ.(urpc_gn) host (U64 0) (Get_proph_spec γ) ∗
  handlers_dom γ.(urpc_gn) {[ (U64 0) ]}
.

Definition own_Clerk γ (ck:loc) : iProp Σ :=
  ∃ (cl:loc) host,
  "#Hcl" ∷ readonly (ck ↦[Clerk :: "cl"] #cl) ∗
  "#Hcl_own" ∷ is_uRPCClient cl host ∗
  "#Hhost" ∷ is_host host γ
.

Lemma wp_Clerk__Get γ ck (e:u64) :
  ∀ Φ,
  own_Clerk γ ck -∗
  EnterNewEpoch_spec γ e (
    |={⊤,∅}=> ∃ latestEpoch, own_latest_epoch γ latestEpoch (1 / 2) ∗
    (if decide (int.Z latestEpoch = int.Z e)
        then Get_core_spec γ e (λ v : u64, own_latest_epoch γ e (1 / 2) ={∅,⊤}=∗ Φ #v)
        else
         own_latest_epoch γ latestEpoch (1 / 2) ={∅,⊤}=∗ True) (* Get_server_spec
         actually has an obligation here; here, we'll exit if the epoch is
         stale, so the client doesn't need to prove anything about this case *)
  )%I
   -∗
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
  iIntros (prophValID prophVal) "Hprophv".
  wp_pures.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  iDestruct (is_slice_to_small with "Hreq_sl") as "Hreq_sl".

  iMod (own_alloc (DfracOwn 1)) as (γreq_op_gn) "HreqTok".
  { done. }
  iMod (own_alloc (DfracOwn 1)) as (γreq_finish_gn) "HfinishTok".
  { done. }
  set (γreq:={| op_gn:=γreq_op_gn ; finish_gn := γreq_finish_gn |}).
  (* Put the EnterNewEpoch into an invariant now, os we  *)
  iAssert (|={⊤}=> Get_req_inv prophVal e γ γreq (λ v, Φ #v))%I
               with "[Hupd HreqTok]" as ">#HgetInv".
  {
    rewrite /Get_req_inv.
    iMod (inv_alloc getN  with "[Hupd HreqTok]") as "$"; last done.
    iNext.
    iLeft.
    iFrame "HreqTok".
    (* Have f(P) in ctx. Want to prove f(Q). Want to know that it's enough to
       show that P -∗ Q. Basically, want to insist that a spec is covariant
       in its Φ argument (or maybe it's contravariant?). *)
    iLeft.
    iApply (EnterNewEpoch_spec_wand with "[] Hupd").
    iIntros "Hupd".
    rewrite /Get_server_spec.
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (?) "Hupd".
    iExists latestEpoch.
    iDestruct "Hupd" as "[$ Hupd]".

    destruct (decide (int.Z latestEpoch = int.Z e)).
    {
      rewrite /Get_core_spec.
      iMod "Hupd".
      iModIntro.
      iDestruct "Hupd" as (?) "[H1 Hupd]".
      iExists _; iFrame "H1".
      iIntros "H1".
      iMod ("Hupd" with "H1") as "Hupd".
      iModIntro.

      iIntros "H1".
      iMod ("Hupd" with "H1") as "Hupd".
      iModIntro.
      iFrame "Hupd".
    }
    {
      iIntros "H1".
      iMod ("Hupd" with "H1") as "Hupd".
      iModIntro.
      iIntros.
      iFrame.
    }
  }

  wp_apply (wp_Client__Call _ _ _ _ _ _ _ _ _ _
                          (λ (l:list u8), ∃ v e, ⌜has_GetReply_encoding l e v⌝ ∗
                                  if (decide (e = (U64 0))) then
                                    operation_receipt _
                                  else
                                    True)%I
             with "[] [$Hreq_sl $Hrep $Hcl_own HgetInv]").
  { iDestruct "Hhost" as "[$ _]". }
  {
    iModIntro.
    iNext.
    rewrite /Get_proph_spec.
    iExists _, _, _, _.
    iSplitL ""; first done.
    iFrame "HgetInv".

    iIntros (l err v HrepEnc) "Hpost".
    iExists _, _. iSplitL ""; first done.
    destruct (decide (err = 0)).
    {
      iFrame "Hpost".
    }
    {
      done.
    }
  }

  iIntros (errCode) "(_ & Hreq_sl & Hpost)".

  wp_pures.
  destruct errCode.
  { (* case: error *)
    rewrite bool_decide_false; last first.
    { by destruct c. }
    wp_pures.
    wp_apply (wp_Exit).
    iIntros.
    by exfalso.
  }
  wp_pures.
  iNamed "Hpost".
  iDestruct "Hpost" as "(Hrep & Hrep_sl & Hpost)".
  wp_load.
  iDestruct "Hpost" as (v err) "(%Hrep_enc & Hpost)".

  (* TODO: move this to a different lemma *)
  wp_lam.
  wp_apply (wp_new_dec with "Hrep_sl").
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

  wp_loadField.
  destruct (decide (int.Z err = 0)).
  { (* no error *)
    replace (err) with (U64 0) by word.
    wp_pures.

    wp_pures.
    wp_loadField.
    wp_apply (wp_ResolveProph_once (T:=u64) with "[$Hprophv]").
    { done. }
    iIntros "%HprophMatches".
    (* XXX: some later hacking. Open the invariant here so we can strip off a later from the Φ. *)
    iApply fupd_wp.

    (* Open HgetInv and use receipt to get Φ. *)
    iInv "HgetInv" as "Hi" "Hclose".
    iDestruct "Hi" as "[[>Hbad _] | Hgood]".
    {
      iDestruct (own_valid_2 with "Hpost Hbad") as %Hbad.
      exfalso.
      done.
    }
    iDestruct "Hgood" as "[_ [Hgood | >Hbad]]"; last first.
    { (* result can't be claimed from invariant because we have HfinishTok *)
      iDestruct (own_valid_2 with "HfinishTok Hbad") as %Hbad.
      exfalso.
      done.
    }

    (* XXX: I still don't know what setoid_rewrite does *)
    erewrite decide_True; last done.
    iDestruct "Hpost" as "#Hpost".
    iMod ("Hclose" with "[HfinishTok]") as "_".
    {
      iNext.
      iRight.
      iFrame "#".
      iRight.
      iFrame.
    }
    iModIntro.
    wp_pures.
    wp_loadField.
    rewrite HprophMatches.
    iFrame.
  }
  { (* error; we'll exit in this case *)
    wp_pures.
    rewrite bool_decide_false; last first.
    { naive_solver. }
    simpl.

    wp_pures.
    wp_apply (wp_Exit).
    by iIntros.
  }
Qed.

Lemma wp_Server__Get γ s (e:u64) (rep:loc) (dummy_err dummy_val:u64) (prophV:u64) γreq Post Φclient :
  is_Server γ s -∗
  {{{
        "Hrep_error" ∷ rep ↦[GetReply :: "err"] #dummy_err ∗
        "Hrep_val" ∷ rep ↦[GetReply :: "val"] #dummy_val ∗

        "#HgetSpec" ∷ (Get_req_inv prophV e γ γreq Φclient) ∗
        "Hpost" ∷ (∀ (err v:u64), (if (decide (err = 0)) then operation_receipt γreq else True) -∗ Post err v)
  }}}
    Server__Get #s #e #rep
  {{{
        (err v:u64), RET #();
        "Hrep_error" ∷ rep ↦[GetReply :: "err"] #err ∗
        "Hrep_val" ∷ rep ↦[GetReply :: "val"] #v ∗
        "Hpost" ∷ Post err v
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
  wp_bind (BinOp _ _ _).

  (* XXX: have to fire the fupd here so that we can bind around a pure step to
     easily strip off later. Ideally, we would've opened the inv after
     wp_if_destruct on whether the epoch number is stale. *)
  iInv "HgetSpec" as "Hi" "Hclose".
  wp_pures.
  wp_apply wp_value. (* FIXME: why do I have to do this manually? *)

  destruct (bool_decide (int.Z e < int.Z latestEpoch)) as [] eqn:Hineq.
  { (* case: Request epoch number is stale *)
    iMod ("Hclose" with "[$Hi]").
    iModIntro.
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[$HmuInv $Hlocked Hv HlatestEpoch HghostLatestEpoch HghostV]").
    {
      iNext.
      iExists _, _.
      iFrame.
    }
    wp_pures.
    wp_storeField.
    iModIntro.
    iApply "HΦ".
    iFrame.
    by iApply "Hpost".
  }
  (*
  iApply (wp_later_tok_pure_step).
  {
    naive_solver.
  }
  iIntros "[HlaterTok _]". *)
  { (* case: epoch number is not stale. *)
    (* Use EnterNewEpoch spec regardless of whether the prophecy matches the current value *)
    rewrite bool_decide_eq_false in Hineq.
    iDestruct "Hi" as "[Hi | Hbad]"; last first.
    { admit. } (* FIXME: have is_latest_epoch_lb here *)
    iDestruct "Hi" as "[_ [Hgood | Hbad]]"; last first.
    { admit. } (* FIXME: have is_latest_epoch_lb here *)
    iEval (rewrite /EnterNewEpoch_spec) in "Hgood".
    (* FIXME: Need to have the fupd mask exclude ↑getN in addition to ↑ctrN *)
    (*
    iMod "Hgood".


    wp_storeField.
    wp_loadField.
    simpl.

    iAssert (|={⊤}=> "HgetSpec" ∷ Get_server_spec γ e Post ∗
                    "HghostLatestEpoch" ∷ own_latest_epoch γ e (1/2) ∗
                    "HghostV" ∷ own_val γ e v (1/2) ∗
                    "#Hlatest_lb" ∷ is_latest_epoch_lb γ e
            )%I with "[HgetSpec HghostLatestEpoch HghostV]" as "HH".
    { (* doing iAssert so that the two cases of EnterNewEpoch get merged *)
      iMod "HgetSpec".
      iDestruct "HgetSpec" as (clientLatestEpoch) "HgetSpec".
      destruct (decide (int.Z clientLatestEpoch < int.Z e)) as [Hineq|Hineq].
      { (* first time seeing epoch number *)
        iDestruct "HgetSpec" as "(HclientLatest & Hunused & HgetSpec)".
        iMod (activate_unused_epoch v with "HunusedInv Hunused") as "HghostV2".
        iEval (rewrite -Qp_half_half) in "HghostV2".
        iDestruct (own_val_split with "HghostV2") as "[HghostV21 HghostV22]".
        iSpecialize ("HgetSpec" $! v with "HghostV21").
        iDestruct (own_latest_epoch_combine with "HghostLatestEpoch HclientLatest") as "[Hlatest %HepochEq]".
        iEval (rewrite Qp_half_half) in "Hlatest".
        iMod (own_latest_epoch_update e with "Hlatest") as "Hlatest".
        iEval (rewrite -Qp_half_half) in "Hlatest".
        iDestruct "Hlatest" as "[Hlatest Hlatest2]".
        rewrite HepochEq.
        iDestruct (own_latest_epoch_get_lb with "Hlatest") as "#Hlb".
        iSpecialize ("HgetSpec" with "HghostV Hlatest").
        iMod "HgetSpec".
        iModIntro.
        iFrame "∗#".
      }
      { (* have seen epoch number before *)
        iDestruct "HgetSpec" as "[HclientLatest HgetSpec]".
        iDestruct (own_latest_epoch_combine with "HclientLatest HghostLatestEpoch") as "[Hlatest %HepochEq]".
        iDestruct "Hlatest" as "[Hlatest Hlatest2]".
        iSpecialize ("HgetSpec" with "Hlatest2").
        iMod "HgetSpec".
        iModIntro.
        rewrite HepochEq in Hineq |- *.
        replace (e) with (latestEpoch) by word.
        iDestruct (own_latest_epoch_get_lb with "Hlatest") as "#Hlb".
        iFrame "∗#".
      }
    }
    iMod "HH".
    iNamed "HH".
    iModIntro.

    (* GetAtEpoch *)
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_loadField.

    iApply fupd_wp.
    iMod "HgetSpec".
    {
      iDestruct "HgetSpec" as (clientLatest) "[HclientLatest HgetSpec]".
      destruct (decide (int.Z clientLatest = int.Z e)) as [Heq|Heq].
      { (* epoch number is not stale *)
        unfold Get_core_spec.
        iMod "HgetSpec".
        iDestruct "HgetSpec" as (v2) "[Hval HgetSpec]".
        iDestruct (own_val_combine with "Hval HghostV") as "[HghostV %Hveq]".
        rewrite Hveq.
        iDestruct (own_val_split with "HghostV") as "[Hval HghostV]".
        iMod ("HgetSpec" with "Hval") as "HgetSpec".
        replace (clientLatest) with (e) by word.
        iMod ("HgetSpec" with "HclientLatest") as "HPost".
        iModIntro.

        wp_apply (release_spec with "[$HmuInv $Hlocked Hv HlatestEpoch HghostLatestEpoch HghostV]").
        {
          iNext. iExists _, _. iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame.
      }
      { (* epoch number is stale; this is impossible at this point, because we checked for staleness earlier *)
        iDestruct (own_latest_epoch_combine with "HclientLatest HghostLatestEpoch") as "[Hlatest %HepochEq]".
        exfalso.
        naive_solver.
      }
    }
  }
*)
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
