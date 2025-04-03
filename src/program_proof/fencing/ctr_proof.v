From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import ctr.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.grove_shared Require Export erpc_lib urpc_proof urpc_spec erpc_proof.
From Perennial.program_proof Require Export marshal_proof.
From iris.algebra Require Import cmra.
From iris.base_logic Require Export mono_nat.
From Perennial.goose_lang Require Import proph.
From Perennial.goose_lang Require Import prelude.

From Perennial.algebra Require Export map.

Section ctr_definitions.

Context `{!gooseGlobalGS Σ}.
Context `{!heapGS Σ}.

Record ctr_names :=
{
  epoch_gn : gname ;
  epoch_token_gn : gname ;
  val_gn : gname ;
  urpc_gn : server_chan_gnames ;
  erpc_gn : erpc_names
}.

Implicit Type γ : ctr_names.

Class ctrG Σ :=
  { #[global] mnat_inG :: mono_natG Σ;
    #[global] val_inG :: mapG Σ u64 u64;
    #[global] unused_tok_inG :: mapG Σ u64 bool;
    #[global] tok_inG :: inG Σ (dfracR)
  }.

Context `{!ctrG Σ}.

Definition own_latest_epoch γ (e:u64) (q:Qp) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) q (uint.nat e).

Definition is_latest_epoch_lb γ (e:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (uint.nat e).

Definition is_latest_epoch_lb_strict γ (e:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (uint.nat e + 1).

Definition own_unused_epoch γ (e:u64) : iProp Σ :=
  e ⤳[γ.(epoch_token_gn)] false.

Definition own_val γ (e:u64) (v:u64) (q:Qp): iProp Σ :=
  e ⤳[γ.(val_gn)]{# q } v ∗
  e ⤳[γ.(epoch_token_gn)]□ true.

Lemma own_val_combine γ e v1 q1 v2 q2 :
  own_val γ e v1 q1 -∗ own_val γ e v2 q2 -∗ own_val γ e v1 (q1 + q2) ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "H1 H2".
  unfold own_val.
  iDestruct "H1" as "[H1 #Hepoch]".
  iDestruct "H2" as "[H2 _]".
  iDestruct (ghost_map_points_to_combine with "H1 H2") as "[$ $]".
  iFrame "#".
Qed.

Lemma own_val_split γ e v q1 q2 :
  own_val γ e v (q1 + q2) -∗ own_val γ e v q1 ∗ own_val γ e v q2.
Proof.
  iIntros "[H1 #Hepoch]".
  iDestruct "H1" as "[H1 H2]".
  iFrame "∗#".
Qed.

Lemma own_val_update v' γ e v:
  own_val γ e v 1 ==∗ own_val γ e v' 1.
Proof.
  iIntros "H1".
  iDestruct "H1" as "[H1 $]".
  iMod (ghost_map_points_to_update with "H1") as "$".
  done.
Qed.

Lemma own_latest_epoch_combine γ e1 e2 q1 q2 :
  own_latest_epoch γ e1 (q1) -∗ own_latest_epoch γ e2 q2 -∗ own_latest_epoch γ e1 (q1 + q2) ∗ ⌜e1 = e2⌝.
Proof.
  iIntros "H1 H2".
  unfold own_latest_epoch.
  iDestruct (mono_nat_auth_own_agree with "H1 H2") as %Hvalid.
  replace (e1) with (e2) by word.
  iCombine "H1 H2" as "H1".
  iFrame.
  done.
Qed.

Lemma own_latest_epoch_split γ e q1 q2 :
  own_latest_epoch γ e (q1 + q2) -∗ own_latest_epoch γ e (q1) ∗ own_latest_epoch γ e q2.
Proof.
  iIntros "H1".
  iDestruct "H1" as "[$ $]".
Qed.

Lemma own_latest_epoch_update e γ eold :
  uint.nat eold ≤ uint.nat e →
  own_latest_epoch γ eold 1 ==∗ own_latest_epoch γ e 1.
Proof.
  intros Hineq.
  iIntros "H1".
  iMod (mono_nat_own_update with "H1") as "[$ _]".
  { word. }
  done.
Qed.

Lemma own_latest_epoch_get_lb γ e q :
  own_latest_epoch γ e q -∗ is_latest_epoch_lb γ e.
Proof.
  iIntros "H1".
  by iApply (mono_nat_lb_own_get).
Qed.

Lemma own_latest_epoch_with_lb γ e e' q :
  own_latest_epoch γ e q -∗ is_latest_epoch_lb γ e' -∗ ⌜uint.Z e' ≤ uint.Z e⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (mono_nat_lb_own_valid with "H1 H2") as "[_ %Hineq]".
  iPureIntro.
  word.
Qed.

End ctr_definitions.

Module ctr.
Section ctr_proof.
Context `{!ctrG Σ}.
Context `{!heapGS Σ}.
Implicit Type γ:ctr_names.

Definition unusedN := nroot .@ "unused".

Definition unused_epoch_inv γ : iProp Σ :=
  inv unusedN (
        [∗ set] e ∈ (fin_to_set u64), own_unused_epoch γ e ∨ own_val γ e 0 1
      ).

(* If someone has own_val, that means the ctr sever saw that epoch number, which
   means the own_unused_epoch was given up. *)
Lemma unused_own_val_false γ e v (q:Qp) :
  unused_epoch_inv γ -∗ own_unused_epoch γ e -∗ own_val γ e v q ={↑unusedN}=∗ False.
Proof.
  iIntros "#Hinv Hunused Hval".
  iInv "Hinv" as ">Hi" "Hclose".
  iDestruct (big_sepS_elem_of_acc _ _ e with "Hi") as "[Helem HbigSepClose]".
  { set_solver. }
  iDestruct "Helem" as "[Hunused2|Hval2]".
  {
    unfold own_unused_epoch.
    iDestruct (ghost_map_points_to_valid_2 with "Hunused Hunused2") as "%Hvalid".
    exfalso.
    naive_solver.
  }
  iDestruct "Hval" as "[Hval _]".
  iDestruct "Hval2" as "[Hval2 _]".
  iDestruct (ghost_map_points_to_valid_2 with "Hval Hval2") as "%Hvalid".
  exfalso.
  destruct Hvalid as [Hbad _].
  rewrite dfrac_op_own in Hbad.
  rewrite dfrac_valid_own in Hbad.
  assert (1 < q + 1)%Qp.
  { apply Qp.lt_add_r. }
  apply (Qp.lt_le_trans _ _ _ H) in Hbad.
  clear H.
  by exfalso. (* Why does "by" work but not anything else I tried? E.g.
                 naive_solver, done, eauto. *)
Qed.

Lemma activate_unused_epoch v γ e:
  unused_epoch_inv γ -∗ own_unused_epoch γ e ={↑unusedN}=∗ own_val γ e v 1.
Proof.
  iIntros "#Hinv Hunused".
  iInv "Hinv" as ">Hi" "Hclose".
  iDestruct (big_sepS_elem_of_acc _ _ e with "Hi") as "[Helem Hi]".
  { set_solver. }
  iDestruct "Helem" as "[Hbad|Hval]".
  {
    iDestruct (ghost_map_points_to_valid_2 with "Hunused Hbad") as "%Hvalid".
    exfalso.
    naive_solver.
  }
  iSpecialize ("Hi" with "[$Hunused]").
  iMod ("Hclose" with "Hi").
  iApply (own_val_update with "Hval").
Qed.

Definition own_Server γ (s:loc) : iProp Σ :=
  ∃ (v latestEpoch:u64),
  "Hv" ∷ s ↦[Server :: "v"] #v ∗
  "HlatestEpoch" ∷ s ↦[Server :: "lastEpoch"] #latestEpoch ∗
  "HghostLatestEpoch" ∷ own_latest_epoch γ latestEpoch (1/2) ∗
  "HghostV" ∷ own_val γ latestEpoch v (1/2)
.

Context `{!erpcG Σ}.

Definition is_Server γ (s:loc) : iProp Σ :=
  ∃ mu (es:loc),
  "#Hmu" ∷ readonly (s ↦[Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock unusedN mu (own_Server γ s) ∗
  "#HunusedInv" ∷ unused_epoch_inv γ ∗
  "#He" ∷ readonly (s ↦[Server :: "e"] #es) ∗
  "#Hes" ∷ is_erpc_server γ.(erpc_gn) es
.

Definition has_GetReply_encoding (l:list u8) (err v:u64) :=
  has_encoding l [EncUInt64 err; EncUInt64 v].

(* FIXME: why is it normal to do |={⊤ ∖ mask, ∅}=> rather than |={⊤, mask}=> ? *)
(* Doing {T ∖ unusedN, ∅} means that I have to open up the invariant with unusedN
   before firing this fupd. On the other hand, if it's {T, unusedN}, I can
   optionally open the invariant after firing the fupd *)

Definition getN := nroot .@ "ctr.get".

(* put getN and unusedN etc. as sub-namespaces of one big namespaces *)
Definition EnterNewEpoch_spec γ (e:u64) (Φ:iProp Σ) : iProp Σ :=
|={⊤∖↑getN, ↑unusedN}=> ∃ latestEpoch, if decide (uint.Z latestEpoch < uint.Z e)%Z then
    own_latest_epoch γ latestEpoch (1/2)%Qp ∗
    own_unused_epoch γ e ∗ (∀ v, own_val γ e v (1/2)%Qp -∗
                                 own_val γ latestEpoch v (1/2)%Qp -∗
                                 own_latest_epoch γ e (1/2)%Qp ={↑unusedN,⊤∖↑getN}=∗ Φ)
else
  (own_latest_epoch γ latestEpoch (1/2)%Qp ∗
   (own_latest_epoch γ latestEpoch (1/2)%Qp ={↑unusedN, ⊤∖↑getN}=∗ Φ))
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

(** The spec for the "core" of a Get operation. This is what's run after the epoch
    number check succeeds.
*)
Definition Get_core_spec γ (e:u64) (Φ:u64 → iProp Σ) : iProp Σ :=
  (* XXX: have a ∅ here because this runs inside of a larger atomic step, so
     invariants will already have been opened *)
  |={∅}=> ∃ v, own_val γ e v (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ={∅}=∗ (Φ v))
    (* XXX: no need for fupds here *)
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

(** This is a "fenced" Get. It checks if the requests's epoch number is current,
    then runs the core operation if so, and does nothing if not.
*)
Definition Get_server_spec γ (e:u64) (Φ:u64 → u64 → iProp Σ) : iProp Σ :=
|={⊤∖↑getN,∅}=> ∃ latestEpoch, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
  if decide (uint.Z latestEpoch = uint.Z e)%Z then
    Get_core_spec γ e (λ v, own_latest_epoch γ e (1/2) ={∅,⊤∖↑getN}=∗ Φ 0 v)
  else
    (own_latest_epoch γ latestEpoch (1/2)%Qp ={∅,⊤∖↑getN}=∗ (∀ dummy_val, Φ 1 dummy_val))
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

Program Definition Get_spec γ :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∃ e,
    ⌜has_encoding reqData [EncUInt64 e]⌝ ∗ EnterNewEpoch_spec γ e (
       Get_server_spec γ e (λ v err, (∀ l, ⌜has_GetReply_encoding l err v⌝ -∗ Φ l))
     ))%I
.
Next Obligation.
  rewrite /EnterNewEpoch_spec /Get_server_spec /Get_core_spec.
  solve_proper.
Defined.

Record get_req_names :=
{
  op_gn:gname;
  ne_gn:gname;
  finish_gn:gname;
}.

Implicit Types γreq : get_req_names.

Definition operation_incomplete γreq : iProp Σ := own γreq.(op_gn) (DfracOwn 1).
Definition operation_receipt γreq : iProp Σ := own γreq.(op_gn) (DfracDiscarded).

Definition new_epoch_incomplete γreq : iProp Σ := own γreq.(ne_gn) (DfracOwn 1).
Definition new_epoch_receipt γreq : iProp Σ := own γreq.(ne_gn) (DfracDiscarded).

Lemma complete_operation γreq :
  operation_incomplete γreq ==∗ operation_receipt γreq.
Proof.
  iIntros "H1".
  iApply (own_update with "H1").
  apply (cmra_update_exclusive).
  done.
Qed.

Lemma complete_newepoch_operation γreq :
  new_epoch_incomplete γreq ==∗ new_epoch_receipt γreq.
Proof.
  iIntros "H1".
  iApply (own_update with "H1").
  apply (cmra_update_exclusive).
  done.
Qed.

Definition result_claimed γreq : iProp Σ := own γreq.(finish_gn) (DfracOwn 1).

Definition Get_req_inv prophV e γ γreq Φ : iProp Σ :=
  inv getN (
        (* The server doesn't actually need quite this powerful of a fupd for
           Get_server_spec.  It only needs a fupd that can be fired specifically
           on the input prophV, but it's convenient to just reuse the more
           powerful spec definition.
         *)
        (*
          XXX: This invariant is a bit ad-hoc. A more principled approach would be to
          give the server a fraction of the ghost resources for the "state" of
          this protocol at the beginning of time, and for this invariant to have
          only a fraction of it.
        *)
    operation_incomplete γreq ∗ (
     (new_epoch_incomplete γreq ∗ EnterNewEpoch_spec γ e (Get_server_spec γ e (λ err v, if decide (err = 0) then Φ v else True)%I) ) ∨
     (new_epoch_receipt γreq ∗ is_latest_epoch_lb γ e ∗ Get_server_spec γ e (λ err v, if decide (err = 0) then Φ v else True)%I)
    ) ∨
    is_latest_epoch_lb γ e ∗ new_epoch_receipt γreq  ∗ operation_receipt γreq ∗ ((Φ prophV) ∨ result_claimed γreq) )
.

Program Definition Get_proph_spec γ :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∃ (prophV e:u64) γreq Φclient,
    ⌜has_encoding reqData [EncUInt64 e]⌝ ∗
    (Get_req_inv prophV e γ γreq Φclient) ∗
    (∀ (err v:u64), (if (decide (err = (W64 0) ∧ v = prophV)) then operation_receipt γreq else True) -∗
                  (∀ l, ⌜has_GetReply_encoding l err v⌝ -∗ Φ l))
  )%I
.
Next Obligation.
  rewrite /Get_req_inv /EnterNewEpoch_spec /Get_server_spec /Get_core_spec.
  solve_proper.
Defined.

Definition Put_core_spec γ (e v:u64) (Φ:iProp Σ) : iProp Σ :=
  (* XXX: have a ∅ here because this runs inside of a larger atomic step, so
     invariants will already have been opened *)
  |={∅}=> ∃ vold, own_val γ e vold (1/2)%Qp ∗
    (own_val γ e v (1/2)%Qp ={∅}=∗ Φ)
.

Definition Put_server_spec γ (e v:u64) (Φ:u64 → iProp Σ) : iProp Σ :=
|={⊤,∅}=> ∃ latestEpoch, own_latest_epoch γ latestEpoch (1/2)%Qp ∗
  if decide (uint.Z latestEpoch = uint.Z e)%Z then
    Put_core_spec γ e v (own_latest_epoch γ e (1/2) ={∅,⊤}=∗ Φ 0)
  else
    (own_latest_epoch γ latestEpoch (1/2)%Qp ={∅,⊤}=∗ Φ 1)
.

Definition has_PutReply_encoding (l:list u8) (err:u64) :=
  has_encoding l [EncUInt64 err].

Program Definition Put_spec γ :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∃ e v,
    ⌜has_encoding reqData [EncUInt64 v ; EncUInt64 e]⌝ ∗ EnterNewEpoch_spec γ e (
       Put_server_spec γ e v (λ err, (∀ l, ⌜has_PutReply_encoding l err⌝ -∗ Φ l))
     ))%I
.
Next Obligation.
  rewrite /EnterNewEpoch_spec /Put_server_spec /Put_core_spec.
  solve_proper.
Defined.

Definition Put_spec_erpc γ : eRPCSpec :=
  {|
    espec_ty := (list u8 → iProp Σ);
    espec_Pre := λ Φ reqData, Put_spec γ reqData Φ;
    espec_Post := λ Φ reqData retData, (Φ retData);
  |}.

Context `{!urpcregG Σ}.

Program Definition GetFreshCID_spec γ :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∀ cid l, erpc_make_client_pre γ.(erpc_gn) cid -∗ ⌜has_encoding l [EncUInt64 cid]⌝ -∗ Φ l)%I
.
Next Obligation.
  rewrite /EnterNewEpoch_spec /Put_server_spec /Put_core_spec.
  solve_proper.
Defined.

Definition is_host (host:u64) γ : iProp Σ :=
  is_urpc_spec_pred γ.(urpc_gn) host (W64 0) (Get_proph_spec γ) ∗
  is_erpc_spec γ.(urpc_gn) γ.(erpc_gn) host (W64 1) (Put_spec_erpc γ) ∗
  is_urpc_spec_pred γ.(urpc_gn) host (W64 2) (GetFreshCID_spec γ) ∗
  is_urpc_dom γ.(urpc_gn) {[ (W64 0) ; (W64 1) ; (W64 2)]}
.

Definition own_Clerk γ (ck:loc) : iProp Σ :=
  ∃ (cl ecl:loc) host,
  "#Hcl" ∷ readonly (ck ↦[Clerk :: "cl"] #cl) ∗
  "#Hcl_is" ∷ is_uRPCClient cl host ∗
  "#Hhost" ∷ is_host host γ ∗
  "#He" ∷ readonly (ck ↦[Clerk :: "e"] #ecl) ∗
  "Hecl_own" ∷ own_erpc_client γ.(erpc_gn) ecl
.

Lemma wp_Clerk__Get γ ck (e:u64) :
  ∀ Φ,
  own_Clerk γ ck -∗
  EnterNewEpoch_spec γ e (
    |={⊤∖↑getN,∅}=> ∃ latestEpoch, own_latest_epoch γ latestEpoch (1 / 2) ∗
    (if decide (uint.Z latestEpoch = uint.Z e)
        then Get_core_spec γ e (λ v : u64, own_latest_epoch γ e (1 / 2) ={∅,⊤∖↑getN}=∗ (own_Clerk γ ck -∗ Φ #v))
        else
         own_latest_epoch γ latestEpoch (1 / 2) ={∅,⊤∖↑getN}=∗ True) (* Get_server_spec
         actually has an obligation here; here, we'll exit if the epoch is
         stale, so the client doesn't need to prove anything about this case *)
  )%I
   -∗
   WP Clerk__Get #ck #e {{ Φ }}.
Proof.
  iIntros (Φ) "Hck Hupd".
  wp_rec.
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
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".

  iMod (own_alloc (DfracOwn 1)) as (γreq_op_gn) "HreqTok".
  { done. }
  iMod (own_alloc (DfracOwn 1)) as (γreq_ne_gn) "HneTok".
  { done. }
  iMod (own_alloc (DfracOwn 1)) as (γreq_finish_gn) "HfinishTok".
  { done. }
  set (γreq:={| op_gn:=γreq_op_gn ; ne_gn:=γreq_ne_gn ; finish_gn := γreq_finish_gn |}).
  (* Put the EnterNewEpoch into an invariant now, os we  *)
  iAssert (|={⊤}=> Get_req_inv prophVal e γ γreq (λ v, Φ #v))%I
               with "[Hupd HneTok HreqTok Hecl_own]" as ">#HgetInv".
  {
    rewrite /Get_req_inv.
    iMod (inv_alloc getN  with "[Hupd HneTok HreqTok Hecl_own]") as "$"; last done.
    iNext.
    iLeft.
    iFrame "HreqTok".
    (* Have f(P) in ctx. Want to prove f(Q). Want to know that it's enough to
       show that P -∗ Q. Basically, want to insist that a spec is covariant
       in its Φ argument (or maybe it's contravariant?). *)
    iLeft.
    iFrame.
    iApply (EnterNewEpoch_spec_wand with "[Hecl_own] Hupd").
    iIntros "Hupd".
    rewrite /Get_server_spec.
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (?) "Hupd".
    iExists latestEpoch.
    iDestruct "Hupd" as "[$ Hupd]".

    destruct (decide (uint.Z latestEpoch = uint.Z e)).
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
      iSpecialize ("Hupd" with "[Hecl_own ]").
      { iExists _, _, _. iFrame "Hecl_own He Hcl Hcl_is Hhost". }
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

  wp_apply (wp_Client__Call_pred _ _ _ _ _ _ _ _ _ _
                          (λ (l:list u8), ∃ v e, ⌜has_GetReply_encoding l e v⌝ ∗
                                  if (decide (e = (W64 0) ∧ v = prophVal)) then
                                    operation_receipt _
                                  else
                                    True)%I
             with "[$Hreq_sl $Hrep Hcl_is HgetInv]").
  { iFrame "Hcl_is". iDestruct "Hhost" as "[$ _]".
    iModIntro.
    iNext.
    rewrite /Get_proph_spec.
    iExists _, _, _, _.
    iSplitL ""; first done.
    iFrame "HgetInv".

    iIntros (err v) "Hpost".
    iIntros (l) "%HrepEnc".
    iExists _, _. iSplitL ""; first done.
    destruct (decide (_)).
    {
      iFrame "Hpost".
    }
    {
      done.
    }
  }

  iIntros (errCode) "(Hreq_sl & Hpost)".

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
  wp_rec.
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
  destruct (decide (uint.Z err = 0)).
  { (* no error *)
    replace (err) with (W64 0) by word.
    wp_pures.

    wp_pures.
    wp_loadField.
    wp_apply (wp_ResolveProph_once (T:=u64) with "[$Hprophv]").
    { done. }
    iIntros "%HprophMatches".
    (* XXX: some later hacking. Open the invariant here so we can strip off a later from the Φ. *)
    iApply fupd_wp.
    rewrite (decide_True); last done.
    iDestruct "Hpost" as "#Hpost".

    (* Open HgetInv and use receipt to get Φ. *)
    iInv "HgetInv" as "Hi" "Hclose".
    iDestruct "Hi" as "[[>Hbad _] | Hgood]".
    {
      iDestruct (own_valid_2 with "Hpost Hbad") as %Hbad.
      exfalso.
      done.
    }
    iDestruct "Hgood" as "(#HlatestEpoch & #HneComplete & _ & [Hgood | >Hbad])"; last first.
    { (* result can't be claimed from invariant because we have HfinishTok *)
      iDestruct (own_valid_2 with "HfinishTok Hbad") as %Hbad.
      exfalso.
      done.
    }

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
        "Hpost" ∷ (∀ (err v:u64), (if (decide (err = 0 ∧ v = prophV)) then operation_receipt γreq else True) -∗ Post err v)
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
  wp_rec.
  wp_pures.
  iNamed "His_srv".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "HmuInv").
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

  destruct (bool_decide (uint.Z e < uint.Z latestEpoch)) as [] eqn:Hineq.
  { (* case: Request epoch number is stale *)
    iMod ("Hclose" with "[$Hi]").
    iModIntro.
    wp_pures.
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$HmuInv $Hlocked Hv HlatestEpoch HghostLatestEpoch HghostV]").
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
  { (* case: epoch number is not stale. *)

    iAssert (|={⊤∖↑getN,⊤}=> "HghostLatestEpoch" ∷ own_latest_epoch γ e (1/2) ∗
                                                "HghostV" ∷ own_val γ e v (1/2) ∗
                                                "#HneComplete" ∷ new_epoch_receipt γreq
            (* "#Hlatest_lb" ∷ is_latest_epoch_lb γ e *)
            )%I with "[Hi Hclose HgetSpec HghostLatestEpoch HghostV]" as "HH".
    {
      (* Use EnterNewEpoch spec regardless of whether the prophecy matches the current value *)
      rewrite bool_decide_eq_false in Hineq.
      iDestruct "Hi" as "[Hi | Hi]"; last first.
      { (* the request was already run previously, and we already have a receipt that the latestEpoch >= e *)
        iDestruct "Hi" as "[#HlatestLb [#Hreceipt HΦclient]]".
        iDestruct (own_latest_epoch_with_lb with "HghostLatestEpoch HlatestLb") as "%Hineq2".
        replace (latestEpoch) with (e); last first.
        { word. }
        iMod ("Hclose" with "[HΦclient]").
        {
          iNext.
          iRight.
          iFrame "∗#".
        }
        iModIntro.
        iFrame "∗#".
      }
      iDestruct "Hi" as "[HopIncomplete [[HneIncomplete Hgood] | Hi]]"; last first.
      { (* the request was run previously, but the Get fupd wasn't fired
           previously (because the prophecy must not have matched last time). *)
        iDestruct "Hi" as "(#HnewComplete & #Hlb & Hupd)".
        iDestruct (own_latest_epoch_with_lb with "HghostLatestEpoch Hlb") as "%Hineq2".
        replace (latestEpoch) with (e) by word.
        iFrame "∗#".
        iMod ("Hclose" with "[-]"); last done.
        iNext.
        iLeft.
        iFrame.
        iRight.
        iFrame "∗#".
      }
      iEval (rewrite /EnterNewEpoch_spec) in "Hgood".
      iMod "Hgood".

      (* FIXME: currently, we require |={⊤, ↑unusedN}=> from the client fupd.
       It seems enough to require |={⊤∖↑unusedN, ∅}=>, which should be strictly
       stronger than above. fupd_mask_frame_r can help prove that.
       *)
      iDestruct "Hgood" as (?) "Hupd".
      iMod (complete_newepoch_operation with "HneIncomplete") as "#HneComplete".
      destruct (decide (uint.Z latestEpoch0 < uint.Z e)).
      { (* first time seeing the number e *)
        iDestruct "Hupd" as "(Hlatest2 & Hunused & Hupd)".
        iDestruct (own_latest_epoch_combine with "HghostLatestEpoch Hlatest2") as "[Hlatest %Heq]".
        rewrite Heq.
        rewrite (Qp.half_half).
        iMod (own_latest_epoch_update e with "Hlatest") as "Hlatest".
        { word. }
        iEval (rewrite -Qp.half_half) in "Hlatest".
        iDestruct (own_latest_epoch_split with "Hlatest") as "[Hlatest Hlatest2]".
        iMod (activate_unused_epoch v with "HunusedInv Hunused") as "HghostV2".
        iEval (rewrite -Qp.half_half) in "HghostV2".
        iDestruct (own_val_split with "HghostV2") as "[HghostV21 HghostV22]".
        iSpecialize ("Hupd" $! v with "HghostV22 HghostV Hlatest2").
        iMod "Hupd".
        iDestruct (own_latest_epoch_get_lb with "Hlatest") as "#HlatestLb".
        iMod ("Hclose" with "[HopIncomplete Hupd]") as "_".
        {
          iNext.
          iLeft.
          iFrame "HopIncomplete".
          iRight.
          iFrame "∗#".
        }
        iModIntro.
        iFrame "∗#".
      }
      { (* e ≤ own_latestEpoch *)
        iDestruct "Hupd" as "[Hlatest2 Hupd]".
        iDestruct (own_latest_epoch_combine with "HghostLatestEpoch Hlatest2") as "[Hlatest %Heq]".
        iDestruct (own_latest_epoch_split with "Hlatest") as "[Hlatest1 Hlatest2]".
        rewrite -Heq.
        replace (latestEpoch) with (e); last first.
        {
          rewrite -Heq in n.
          word.
        }
        iDestruct (own_latest_epoch_get_lb with "Hlatest2") as "#HlatestLb".
        iMod ("Hupd" with "Hlatest1") as "Hupd".
        iMod ("Hclose" with "[Hupd HopIncomplete]") as "_".
        {
          iNext.
          iLeft.
          iFrame "∗#".
          iRight.
          iFrame "∗#".
        }
        iModIntro.
        iFrame "∗#".
      }
    }

    iMod "HH".
    iNamed "HH".
    iModIntro.

    (* Done with EnterNewEpoch part of the proof; now, just worry about GetAtEpoch *)

    wp_pures.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_bind (Skip).

    iInv "HgetSpec" as "Hi" "Hclose".
    wp_pures.
    wp_apply (wp_value).

    iDestruct "Hi" as "[Hi | HalreadyDone]"; last first.
    { (* case: someone already fired the client fupd and the receipt is sitting in the invariant *)
      iDestruct "HalreadyDone" as "(#Hlb & #HneReceipt & #Hreceipt & HΦclient)".
      iMod ("Hclose" with "[HΦclient]").
      {
        iNext.
        iRight.
        iFrame "∗#".
      }
      iModIntro.
      wp_pures.
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlocked $HmuInv Hv HlatestEpoch HghostV HghostLatestEpoch]").
      {
        iNext.
        iExists _, _.
        iFrame.
      }
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iFrame.
      iApply "Hpost".
      destruct (decide (_)); iFrame "#".
      done.
    }
    { (* case: the operation hasn't been run before, so we might run it now *)
      iDestruct "Hi" as "[Hincomplete [Hbad | Hupd]]".
      {
        iDestruct "Hbad" as "[Hbad _]".
        iDestruct (own_valid_2 with "HneComplete Hbad") as %Hbad.
        exfalso.
        done.
      }
      destruct (decide (v = prophV)) as [HprophMatches|HprophWrong].
      { (* case: prophecized value matches physical one; we have to run the fupd in this case *)
        iDestruct "Hupd" as "(#HneReceipt & #Hlb & Hupd)".
        iMod "Hupd".
        clear Hineq latestEpoch.
        iDestruct "Hupd" as (latestEpoch) "[Hlatest2 Hupd]".
        iDestruct (own_latest_epoch_combine with "HghostLatestEpoch Hlatest2") as "[Hlatest %Heq]".
        destruct (decide (uint.Z latestEpoch = uint.Z e)); last first.
        { (* contradictory: we know for sure that own_latest_epoch e *)
          exfalso.
          naive_solver.
        }
        iMod "Hupd".
        iDestruct "Hupd" as (v2) "[Hval2 Hupd]".
        iDestruct (own_val_combine with "HghostV Hval2") as "[Hval %HvEq]".
        rewrite -HvEq.
        iDestruct (own_val_split with "Hval") as "[Hval Hval2]".
        iMod ("Hupd" with "Hval2") as "Hupd".
        rewrite Heq.
        iDestruct (own_latest_epoch_split with "Hlatest") as "[Hlatest Hlatest2]".
        iMod ("Hupd" with "Hlatest2") as "Hupd".
        iMod (complete_operation with "Hincomplete") as "#Hreceipt".
        rewrite HprophMatches.
        iMod ("Hclose" with "[Hupd]").
        {
          iNext.
          iRight.
          iFrame "#".
          iLeft.
          iFrame.
        }
        iModIntro.
        wp_pures.
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlocked $HmuInv Hv HlatestEpoch Hval Hlatest]").
        {
          iNext.
          iExists _, _.
          iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame.
        iApply "Hpost".
        destruct (decide _); iFrame "#".
        done.
      }
      { (* case: prophecized value doesn't match physical one; we don't have to do anything in this case *)
        iMod ("Hclose" with "[Hincomplete Hupd]").
        {
          iNext.
          iLeft.
          iFrame.
        }
        iModIntro.
        wp_pures.
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlocked $HmuInv Hv HlatestEpoch HghostV HghostLatestEpoch]").
        {
          iNext.
          iExists _, _.
          iFrame.
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame.
        iApply "Hpost".
        rewrite decide_False; first done.
        naive_solver.
      }
    }
  }
Qed.

Lemma Put_core_spec_wand γ (e v:u64) (Φ Φ':iProp Σ) :
  (Φ -∗ Φ') -∗
  Put_core_spec γ e v Φ -∗
  Put_core_spec γ e v Φ'.
Proof.
  iIntros "Hwand Hupd".
  iMod "Hupd".
  iModIntro.
  iDestruct "Hupd" as (?) "[H1 Hupd]".
  iExists _; iFrame "H1".
  iIntros "H1".
  iApply "Hwand".
  iApply "Hupd".
  iFrame.
Qed.

Lemma wp_Server__Put γ s args_ptr Φclient (e v:u64) :
  is_Server γ s -∗
  {{{
      "Hupd" ∷ EnterNewEpoch_spec γ e (Put_server_spec γ e v Φclient) ∗
      "Hargs_val" ∷ args_ptr ↦[PutArgs :: "v"] #v ∗
      "Hargs_epoch" ∷ args_ptr ↦[PutArgs :: "epoch"] #e
  }}}
    Server__Put #s #args_ptr
  {{{
        (err:u64), RET #err; Φclient err
  }}}.
Proof.
  iIntros "#His_srv !#" (Φ) "Hpre HΦ".
  iNamed "His_srv".
  iNamed "Hpre".
  wp_rec.
  wp_pures.
  wp_loadField.

  wp_apply (wp_Mutex__Lock with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".

  wp_pures.

  wp_loadField.
  wp_loadField.
  wp_pures.
  wp_if_destruct.
  { (* stale epoch number *)
    wp_loadField.
    iApply fupd_wp.
    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "Hupd".
    { set_solver. }
    iDestruct "Hupd" as (?) "Hupd".
    destruct (decide (uint.Z latestEpoch0 < uint.Z e)).
    { (* case: epoch number is fresh; contradicts the fact that we're in the
         stale case already *)
      iDestruct "Hupd" as "[Hlatest2 Hupd]".
      iDestruct (own_latest_epoch_combine with "Hlatest2 HghostLatestEpoch") as "[_ %Heq]".
      exfalso.
      rewrite Heq in l.
      word.
    }
    iDestruct "Hupd" as "[Hlatest Hupd]".
    iMod ("Hupd" with "Hlatest") as "Hupd".
    iMod "Hmask" as "_".

    (* second linearization point *)
    iMod "Hupd".
    clear latestEpoch0 n.
    iDestruct "Hupd" as (?) "[Hlatest2 Hupd]".
    destruct (decide (uint.Z latestEpoch0 = uint.Z e)).
    { (* case: epoch number is fresh; contradicts the fact that we're in the
         stale case *)
      iDestruct (own_latest_epoch_combine with "Hlatest2 HghostLatestEpoch") as "[_ %Heq]".
      exfalso.
      rewrite Heq in e0.
      word.
    }
    iMod ("Hupd" with "Hlatest2") as "HΦclient".
    iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$Hlocked $HmuInv HlatestEpoch Hv HghostLatestEpoch HghostV]").
    {
      iNext.
      iExists _, _.
      iFrame "∗#".
    }
    wp_pures.
    iApply "HΦ".
    iFrame.
    done.
  }
  { (* case: epoch number is valid *)
    wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_loadField.

    iApply fupd_wp.

    (* iAssert to join the two different cases of the EnterNewEpoch fupd *)
    iAssert (
        |={⊤}=> "Hupd" ∷ Put_server_spec γ e v Φclient ∗
               "Hlatest" ∷ own_latest_epoch γ e (1/2) ∗
               "Hval" ∷ own_val γ e v0 (1/2)
      )%I with "[Hupd HghostLatestEpoch HghostV]" as "HH".
    {
      iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "Hupd".

      { set_solver. }
      iDestruct "Hupd" as (?) "Hupd".

      destruct (decide (uint.Z latestEpoch0 < uint.Z e)).
      { (* case: first time seeing client's epoch number *)
        iDestruct "Hupd" as "(Hlatest2 & Hunused & Hupd)".
        iMod (activate_unused_epoch v0 with "HunusedInv Hunused") as "Hval".
        iEval (rewrite -Qp.half_half) in "Hval".
        iDestruct (own_val_split with "Hval") as "[Hval Hval2]".
        iDestruct (own_latest_epoch_combine with "Hlatest2 HghostLatestEpoch") as "[Hlatest %Heq]".
        rewrite Heq.
        rewrite (Qp.half_half).
        iMod (own_latest_epoch_update e with "Hlatest") as "Hlatest".
        { word. }
        iEval (rewrite -Qp.half_half) in "Hlatest".
        iDestruct (own_latest_epoch_split with "Hlatest") as "[Hlatest Hlatest2]".
        iMod ("Hupd" with "Hval2 HghostV Hlatest2") as "Hupd".
        iFrame.
      }
      { (* case: have seen epoch number before *)
        iDestruct "Hupd" as "[Hlatest2 Hupd]".
        iDestruct (own_latest_epoch_combine with "Hlatest2 HghostLatestEpoch") as "[Hlatest %Heq]".
        rewrite Heq.
        iDestruct (own_latest_epoch_split with "Hlatest") as "[Hlatest Hlatest2]".
        replace latestEpoch with e by word.
        iMod ("Hupd" with "Hlatest2") as "Hupd".
        iFrame.
        by iMod "Hmask".
      }
    }

    iMod "HH".
    iNamed "HH".

    (* second linearization point: PutAtEpoch () *)
    iMod "Hupd".
    iDestruct "Hupd" as (?) "[Hlatest2 Hupd]".
    iDestruct (own_latest_epoch_combine with "Hlatest2 Hlatest") as "[Hlatest %Heq]".
    rewrite Heq.
    iDestruct (own_latest_epoch_split with "Hlatest") as "[Hlatest Hlatest2]".
    rewrite decide_True; last done.
    iMod "Hupd".
    iDestruct "Hupd" as (vold) "[Hval2 Hupd]".
    iDestruct (own_val_combine with "Hval Hval2") as "[Hval %Hveq]".
    rewrite Hveq.
    rewrite Qp.half_half.
    iMod (own_val_update v with "Hval") as "Hval".
    iEval (rewrite -Qp.half_half) in "Hval".
    iDestruct (own_val_split with "Hval") as "[Hval Hval2]".
    iMod ("Hupd" with "Hval2") as "Hupd".
    iMod ("Hupd" with "Hlatest2") as "Hupd".
    iModIntro.

    wp_apply (wp_Mutex__Unlock with "[$Hlocked $HmuInv Hv HlatestEpoch Hlatest Hval]").
    {
      iNext.
      iExists _, _.
      iFrame "∗#".
    }
    wp_pures.
    iApply "HΦ".
    iFrame.
    done.
  }
Qed.

Lemma wp_Clerk__Put γ ck (e v:u64) :
  ∀ Φ,
  own_Clerk γ ck -∗
  EnterNewEpoch_spec γ e (
    |={⊤,∅}=> ∃ latestEpoch, own_latest_epoch γ latestEpoch (1 / 2) ∗
    (if decide (uint.Z latestEpoch = uint.Z e)
        then Put_core_spec γ e v (own_latest_epoch γ e (1 / 2) ={∅,⊤}=∗ (own_Clerk γ ck -∗ Φ #()))
        else
         own_latest_epoch γ latestEpoch (1 / 2) ={∅,⊤}=∗ True) (* Put_server_spec
         actually has an obligation here; here, we'll exit if the epoch is
         stale, so the client doesn't need to prove anything about this case *)
  )%I
  -∗
    WP Clerk__Put #ck #v #e {{ Φ }}.
Proof.
  iIntros (Φ) "Hck Hupd".
  wp_rec.
  wp_pures.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.

  (* TODO: put this in its own lemma *)
  wp_rec.
  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc").
  { done. }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc").
  { done. }
  iIntros "Henc".
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (req_sl reqData) "(%Hreq_enc & %Hreq_len & Hreq_sl)".
  wp_pures.

  iNamed "Hck".
  wp_loadField.
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_small".
  wp_apply (wp_erpc_NewRequest (Put_spec_erpc γ)
      (λ l, ∃ err, ⌜has_PutReply_encoding l err⌝ ∗
      if (decide (err = 0)) then
        (own_Clerk γ ck -∗ Φ #())
      else
        True
      )%I
             with "[$Hreq_small $Hecl_own Hupd]").
  {
    simpl.
    iExists _, _.
    simpl in Hreq_enc.
    iSplitL ""; first done.
    iApply (EnterNewEpoch_spec_wand with "[] Hupd").
    iIntros "Hupd".
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (?) "[Hlatest Hupd]".
    iExists _. iFrame.
    destruct (decide (_)).
    { (* epoch number is valid; do the operation *)
      iApply (Put_core_spec_wand with "[] Hupd").
      iIntros "Hupd".
      iIntros "Hlatest".
      iMod ("Hupd" with "Hlatest") as "Hupd".
      iModIntro.
      iIntros.
      iExists _.
      iSplitL ""; first done.
      setoid_rewrite decide_True; last done. (* TODO: What is setoid_rewrite?*)
      iApply "Hupd".
    }
    { (* epoch number is stale; do nothing *)
      iIntros "Hlatest".
      iMod ("Hupd" with "Hlatest").
      iModIntro.
      iIntros.
      iExists _; iSplitL ""; first done.
      setoid_rewrite decide_False; last done.
      done.
    }
  }

  (* FIXME: why is so much stuff exposed? Can we hide the urpc precondition etc.
     and return some blackbox thing that gives us the right to make a urpc
     client call (maybe we should just return a WP?). *)
  iIntros (y_urpc reqData_urpc reqSl_urpc) "(Hreq_sl & #Hpre_urpc & Hurpc_post_to_erpc_post)".
  wp_pures.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  wp_loadField.
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_small".
  iDestruct "Hhost" as "(Hhost1 & #Hhost_erpc & Hhost2)".
  wp_apply (wp_Client__Call with "[Hhost_erpc $Hrep $Hreq_small Hcl_is]").
  { iFrame "#". }
  iIntros (err) "(Hreq_urpc_sl & Hpost)".
  wp_pures.

  destruct err.
  { (* urpc error; got no response *)
    rewrite bool_decide_false; last first.
    { simpl. by destruct c. }
    wp_pures.
    wp_apply (wp_Exit).
    by iIntros "Hbad".
  }
  wp_pures.
  iDestruct "Hpost" as (rep_sl repData) "(Hrep_ptr & Hrep_sl & Hpost)".
  wp_load.
  iMod ("Hurpc_post_to_erpc_post" with "Hpost") as "Hpost".
  iDestruct "Hpost" as "[Hecl_own Hpost]".
  simpl.
  iDestruct "Hpost" as (errStale) "Hpost".
  iDestruct "Hpost" as "[>%HencRep Hpost]".

  wp_apply (wp_new_dec with "Hrep_sl").
  { done. }
  iIntros (dec) "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_pures.
  wp_if_destruct.
  { (* got stale error *)
    wp_apply (wp_Exit).
    by iIntros "Hbad".
  }
  wp_pures.
  iEval (simpl) in "Hpost".
  iApply "Hpost".
  iModIntro.
  iExists _, _, _.
  iFrame "Hcl Hcl_is He Hecl_own Hhost1 Hhost_erpc Hhost2".
Qed.

Lemma wp_StartServer host γ :
  is_host host γ -∗
  unused_epoch_inv γ -∗
  {{{
        "Hes" ∷ own_erpc_pre_server γ.(erpc_gn) ∗
        "HghostLatestEpoch" ∷ own_latest_epoch γ 0 (1/2) ∗
        "HghostV" ∷ own_val γ 0 0 (1/2)
  }}}
    StartServer #host
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros "#Hhost #Hunused !#" (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (s) "Hs".
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".
  simpl.

  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (mu) "HmuInv".

  wp_storeField.

  wp_apply (wp_erpc_MakeServer with "[$Hes]").
  iIntros (es) "#His_erpc".
  wp_storeField.
  wp_storeField.

  wp_apply (map.wp_NewMap u64).
  iIntros (handlers) "Hhandlers".

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_loadField.
  wp_apply (wp_erpc_Server_HandleRequest (Put_spec_erpc γ) with "[$His_erpc]").

  iIntros (put_urpc_handler) "#Hput_erpc_to_urpc".

  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_apply (wp_MakeServer with "Hhandlers").
  iIntros (r) "Hr".
  wp_pures.

  iAssert (|={⊤}=> is_Server γ s)%I with "[mu e v lastEpoch HmuInv HghostLatestEpoch HghostV]" as "HH".
  {
    unfold is_Server.
    iMod (readonly_alloc_1 with "mu") as "#Hmu".
    iMod (readonly_alloc_1 with "e") as "#He".
    iExists _, _; iFrame "#".
    iApply (alloc_lock with "HmuInv").
    iNext.
    iExists _, _.
    iFrame.
  }
  iMod "HH" as "#His_srv".

  wp_apply (wp_StartServer_pred with "[$Hr]").
  {
    set_solver.
  }
  {
    iDestruct "Hhost" as "(H1&H2&H3&Hhandlers)".
    unfold handlers_complete.
    repeat rewrite dom_insert_L.
    rewrite dom_empty_L.
    iSplitL "".
    {
      iExactEq "Hhandlers".
      f_equal.
      set_solver.
    }

    iApply (big_sepM_insert_2 with "").
    {
      simpl. iExists _; iFrame "#".
      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# Hpre HΦ".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_small & Hrep_ptr & Hpre)".
      wp_apply (wp_new_enc).
      iIntros (enc) "Henc".
      wp_pures.
      iNamed "His_srv".
      wp_loadField.
      wp_apply (wp_erpc_GetFreshCID with "[$Hes]").
      iIntros (cid) "Hpost".
      wp_apply (wp_Enc__PutInt with "Henc").
      { done. }
      iIntros "Henc".
      wp_pures.

      wp_apply (wp_Enc__Finish with "Henc").
      iIntros (rep_sl repData) "(%HrepEnc & %HrepLen & Hrep_sl)".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_small".
      wp_store.
      iApply "HΦ".
      iFrame.
      unfold GetFreshCID_spec.
      iApply ("Hpre" with "Hpost").
      done.
    }
    iApply (big_sepM_insert_2 with "").
    {
      simpl. iExists _; iFrame "#".
      iApply urpc_handler_to_handler.
      iApply "Hput_erpc_to_urpc".
      clear Φ.
      iIntros (?????) "!# Hpre HΦ".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_small & Hrep_ptr & Hpre)".
      iDestruct "Hpre" as (??) "[%HreqEnc Hpre]".

      (* TODO: put this in another lemma *)
      wp_rec.
      wp_apply (wp_new_dec with "[$Hreq_small]").
      { done. }
      iIntros (dec) "Hdec".
      wp_pures.
      wp_apply (wp_allocStruct).
      { repeat econstructor. }
      iIntros (args_ptr) "Hargs".
      wp_pures.
      iDestruct (struct_fields_split with "Hargs") as "HH".
      iNamed "HH".
      wp_apply (wp_Dec__GetInt with "Hdec").
      iIntros "Hdec".
      wp_storeField.

      wp_apply (wp_Dec__GetInt with "Hdec").
      iIntros "Hdec".
      wp_storeField.
      (* End separate lemma *)

      wp_pures.
      wp_apply (wp_Server__Put γ with "His_srv [$Hpre $v $epoch]").
      iIntros (err) "Hpost".
      wp_pures.

      wp_apply (wp_new_enc).
      iIntros (enc) "Henc".
      wp_pures.
      wp_apply (wp_Enc__PutInt with "Henc").
      { done. }
      iIntros "Henc".
      wp_pures.
      simpl.
      wp_apply (wp_Enc__Finish with "Henc").
      iIntros (rep_sl repData) "(%HrepEnc & %HrepLen & Hrep_sl)".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_small".
      wp_store.
      iModIntro.
      iApply "HΦ".
      iFrame.
      iApply "Hpost".
      done.
    }
    iApply (big_sepM_insert_2 with "").
    {
      simpl. iExists _; iFrame "#".
      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# Hpre HΦ".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_small & Hrep_ptr & Hpre)".
      iDestruct "Hpre" as (????) "[%HreqEnc Hpre]".

      wp_apply (wp_new_dec with "[$Hreq_small]").
      {
        done.
      }
      iIntros (dec) "Hdec".
      wp_pures.
      wp_apply (wp_Dec__GetInt with "Hdec").
      iIntros "Hdec".
      wp_pures.
      wp_apply (wp_allocStruct).
      { repeat econstructor. }
      iIntros (reply) "Hreply".
      iDestruct (struct_fields_split with "Hreply") as "HH".
      iNamed "HH".
      wp_pures.
      wp_apply (wp_Server__Get γ with "His_srv [$err $val Hpre]").
      {
        iDestruct "Hpre" as "[$ Hpre]".
        iFrame "Hpre".
      }
      iIntros (err v).
      iNamed 1.
      wp_pures.

      (* TODO: move this to a different lemma *)
      wp_rec.
      wp_apply (wp_new_enc).
      iIntros (enc) "Henc".
      wp_pures.
      wp_loadField.
      wp_apply (wp_Enc__PutInt with "Henc").
      { done. }
      iIntros "Henc".
      wp_pures.

      wp_loadField.
      wp_apply (wp_Enc__PutInt with "Henc").
      { done. }
      iIntros "Henc".
      wp_apply (wp_Enc__Finish with "Henc").
      iIntros (rep_sl repData) "(%HrepEnc & %HrepLen & Hrep_sl)".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_small".
      wp_store.
      iApply "HΦ".
      iModIntro.
      iFrame.
      iApply "Hpost".
      done.
    }
    iApply (big_sepM_empty).
    done.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_MakeClerk host γ :
  is_host host γ -∗
  {{{
      True
  }}}
    MakeClerk #host
  {{{
      (ck:loc), RET #ck; own_Clerk γ ck
  }}}.
Proof.
  iIntros "#Hhost !#" (Φ) "_ HΦ".
  wp_rec.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }

  iIntros (ck) "Hck".
  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".

  wp_pures.
  wp_apply (wp_MakeClient).
  iIntros (cl) "#His_cl".

  wp_storeField.
  wp_apply (wp_ref_of_zero).
  { done. }

  iIntros (reply_ptr) "Hrep".
  wp_pures.
  wp_apply (wp_NewSlice).
  iIntros (dummy_sl) "Hdummy_sl".
  iDestruct (own_slice_to_small with "Hdummy_sl") as "Hargs_small".
  wp_loadField.

  wp_apply (wp_Client__Call_pred _ _ _ _ _ _ _ _ _ _
                (λ l, (∃ cid, erpc_make_client_pre γ.(erpc_gn) cid ∗
                              ⌜has_encoding l [EncUInt64 cid]⌝))%I
             with "[His_cl $Hargs_small $Hrep]").
  {
    iFrame "#".
    iDestruct "Hhost" as "(_ & _ & $ & _)".
    iModIntro.
    iNext.
    simpl.
    iIntros.
    iExists _; iFrame.
    done.
  }
  iIntros (err) "(Hargs_small & Hpost)".
  wp_pures.
  destruct err.
  { (* error *)
    rewrite bool_decide_false; last first.
    { by destruct c. }
    wp_apply (wp_Exit).
    iIntros "Hbad".
    done.
  }
  wp_pures.

  iDestruct "Hpost" as (??) "(Hrep_ptr & Hrep_small & Hpost)".
  wp_load.
  iDestruct "Hpost" as (?) "[Hecl %HrepEnc]".
  wp_apply (wp_new_dec with "[$Hrep_small]").
  { done. }
  iIntros (dec) "Hdec".
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_apply (wp_erpc_MakeClient with "[$Hecl]").
  iIntros (e) "He".
  wp_storeField.
  iApply "HΦ".
  iExists _, _, _.
  iMod (readonly_alloc_1 with "cl") as "$".
  iMod (readonly_alloc_1 with "e") as "$".
  iFrame "He His_cl Hhost".
  done.
Qed.

End ctr_proof.
End ctr.
