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
    unused_tok_inG:> mapG Σ u64 bool
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

Definition EnterNewEpoch_spec γ (e:u64) (Φ:iProp Σ) : iProp Σ :=
|={⊤,∅}=> ∃ latestEpoch, if decide (int.Z latestEpoch < int.Z e)%Z then
    own_latest_epoch γ latestEpoch (1/2)%Qp ∗
    own_unused_epoch γ e ∗ (∀ v, own_val γ e v (1/2)%Qp -∗
                                 own_val γ latestEpoch v (1/2)%Qp -∗
                                 own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ Φ)
else (* XXX: it might seem like the server shouldn't need any resources in this case. *)
  (own_latest_epoch γ latestEpoch (1/2)%Qp ∗
   (own_latest_epoch γ latestEpoch (1/2)%Qp ={∅,⊤}=∗ Φ))
.

(* In this spec:
   If the server can prove to the client that latestEpoch < e, then the client
   needs to give back to the server the own_latest_epoch and own_unused_epoch
   under a view-shift and the client will get back own_val of the new epoch, and
   the previous latest epoch.

   I think this might not be strictly TaDa.
 *)
Definition EnterNewEpoch_spec' γ (e:u64) (Φ:iProp Σ) : iProp Σ :=
∀ latestEpoch, own_latest_epoch γ latestEpoch (1/2)%Qp -∗
if decide (int.Z latestEpoch < int.Z e)%Z then
  |={⊤, ∅}=> own_latest_epoch γ latestEpoch (1)%Qp ∗ own_unused_epoch γ e ∗
            (∀ v, own_val γ e v (1/2)%Qp -∗
                  own_val γ latestEpoch v (1/2)%Qp -∗
                  own_latest_epoch γ e (1/2)%Qp ={∅,⊤}=∗ Φ)
else
  Φ
.

Definition Get_core_spec γ (e:u64) (Φ:u64 → iProp Σ) : iProp Σ :=
  |={⊤, ∅}=> ∃ v, own_val γ e v (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ={∅,⊤}=∗ (Φ v))
.

Definition Get_server_spec γ (e:u64) (Φ:u64 → u64 → iProp Σ) : iProp Σ :=
|={⊤,∅}=> ∃ latestEpoch, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
  if decide (int.Z latestEpoch = int.Z e)%Z then
    Get_core_spec γ e (λ v, Φ 0 v)
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
  (∃ (pv pe:proph_id) (repV:u64) e,
    ⌜has_encoding reqData [EncUInt64 e]⌝ ∗ EnterNewEpoch_spec γ e (
       Get_server_spec γ e (λ v err, (∀ l, ⌜has_GetReply_encoding l err v⌝ -∗ Φ l))
     ))%I
.
Next Obligation.
  rewrite /EnterNewEpoch_spec /Get_server_spec /Get_core_spec.
  solve_proper.
Defined.

Context `{!urpcregG Σ}.

Definition is_host (host:u64) γ : iProp Σ :=
  handler_spec γ.(urpc_gn) host (U64 0) (Get_spec γ) ∗
  handlers_dom γ.(urpc_gn) {[ (U64 0) ]}
.

Definition own_Clerk γ (ck:loc) : iProp Σ :=
  ∃ (cl:loc) host,
  "#Hcl" ∷ readonly (ck ↦[Clerk :: "cl"] #cl) ∗
  "#Hcl_own" ∷ is_uRPCClient cl host ∗
  "#Hhost" ∷ is_host host γ
.

Lemma wp_Server__Get γ s (e:u64) (rep:loc) (dummy_err dummy_val:u64) Post :
  is_Server γ s -∗
  {{{
        "Hrep_error" ∷ rep ↦[GetReply :: "err"] #dummy_err ∗
        "Hrep_val" ∷ rep ↦[GetReply :: "val"] #dummy_val ∗

      "HgetSpec" ∷ EnterNewEpoch_spec γ e (Get_server_spec γ e Post)
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
  wp_pures.

  wp_if_destruct.
  { (* case: Stale epoch number *)
    wp_loadField.
    (* First reason about EnterNewEpoch() *)
    unfold EnterNewEpoch_spec.
    iApply fupd_wp.
    iMod "HgetSpec".
    iDestruct "HgetSpec" as (clientLatestEpoch) "HgetSpec".
    destruct (decide (int.Z clientLatestEpoch < int.Z e)) as [Hineq|Hineq].
    { (* TODO(proof): contradiction because clientLatestEpoch == latestEpoch *)
      exfalso.
      admit.
    }
    (* e ≤ latestEpoch, so getSpec doesn't need own_unused_val *)
    iDestruct "HgetSpec" as "[Hlatest2 HgetSpec]". (* TODO: why bother with own_latest_epoch in this case? *)
    iMod ("HgetSpec" with "Hlatest2") as "HgetSpec".

    (* Now for the GetAtEpoch() *)
    unfold Get_server_spec.
    iMod "HgetSpec".
    clear Hineq clientLatestEpoch.
    iDestruct "HgetSpec" as (clientLatestEpoch) "[Hlatest2 HgetSpec]".

    destruct (decide (int.Z clientLatestEpoch = int.Z e)).
    { (* TODO(proof): contradiction; we know that latestEpoch > e, and clientLatestEpoch = latestEpoch. *)
      exfalso.
      admit.
    }
    iMod ("HgetSpec" with "Hlatest2") as "Hpost".
    iModIntro.

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
    iApply "Hpost".
  }
  { (* case: epoch number is not stale. *)
    admit.
  }
Admitted.

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
  wp_apply (wp_NewProph_once (T:=bool)).
  iIntros (errProph err) "Hprophe".
  wp_apply (wp_NewProph_once (T:=u64)).
  iIntros (valProph v) "Hprophv".
  wp_pures.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  iDestruct (is_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_apply (wp_Client__Call _ _ _ _ _ _ _ _ _ _
                          (λ (l:list u8), ∃ v e, ⌜has_GetReply_encoding l e v⌝ ∗
                                  if (decide (int.Z e = 0)) then
                                    (own_Clerk γ ck -∗ Φ #v) ∗ proph_once valProph v
                                  else
                                    proph_once errProph true)%I
             with "[] [$Hreq_sl $Hrep $Hcl_own Hupd Hprophv Hprophe]").
  { iDestruct "Hhost" as "[$ _]". }
  {
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
    (*
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
  {
    (* no error *)
    replace (err) with (U64 0) by word.
    wp_pures.
    rewrite bool_decide_true; last done.
    simpl.

    (* maybe we don't need this *)
    wp_apply (wp_ResolveProph_once (T:=bool) with "[]").
    { admit. }
    { admit. }
    iIntros (_).

    wp_pures.
    wp_loadField.
    wp_pures.
    iDestruct "Hpost" as "[Hpost Hprophv]".
    wp_loadField.
    wp_apply (wp_ResolveProph_once (T:=u64) with "[$Hprophv]").
    { done. }
  } *)
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
