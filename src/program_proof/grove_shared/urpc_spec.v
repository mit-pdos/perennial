(** Pre-postcondition-style specs for uRPCs
(translated to the predicate transformer style of the underlying lib *)
From iris.algebra Require Import gset.
From Perennial.algebra Require Import auth_map.
From Perennial.base_logic Require Import lib.ghost_map lib.saved_spec.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.grove_shared Require Import urpc_proof.

Section rpc_global_defs.

Context `{!urpcregG Σ}.
Context `{HPRE: !gooseGlobalGS Σ}.

(* Higher-level interface for defining a uRPC spec. *)
Polymorphic Record RpcSpec@{u} :=
  {
    spec_ty : Type@{u};
    spec_Pre : spec_ty → list u8 → iProp Σ;
    spec_Post : spec_ty → list u8 → list u8 → iProp Σ
  }.

Program Polymorphic Definition RpcSpec_Spec@{u} (spec : RpcSpec@{u}) : savedSpecO Σ (list u8) (list u8) :=
  λ args, λne (Φ : list u8 -d> iPropO Σ), (∃ x,
    spec.(spec_Pre) x args ∗ (∀ rep, spec.(spec_Post) x args rep -∗ Φ rep))%I.
Next Obligation. solve_proper. Qed.

Polymorphic Definition is_urpc_spec Γsrv (host:u64) (rpcid:u64) (spec : RpcSpec) :=
  is_urpc_spec_pred Γsrv host rpcid (RpcSpec_Spec spec).

Local Example spec_iprop :=
  {|
  spec_ty := iProp Σ;
  spec_Pre := λ (_:iProp Σ) _, True%I;
  spec_Post := λ _ _ _, True%I
  |}.

(* XXX: using this because [list] is not universe polymorphic. *)
Inductive plist (A : Type) :=
| pnil : plist A
| pcons : A -> plist A -> plist A.
Arguments pnil {A}.
Arguments pcons {A} a l.

(* XXX: added this because there were universe inconsistencies in how prod was
   used across memkv and simplepb. *)
Polymorphic Inductive pprod (A : Type) (B:Type) :=
| ppair : A → B → pprod A B.
Arguments ppair {A} {B} a b.
Definition pfst {A B} (p:pprod A B) := let (a, _) := p in a.
Definition psnd {A B} (p:pprod A B) := let (_, b) := p in b.

Set Universe Polymorphism.
Fixpoint dom_RpcSpec_list (l: plist (pprod u64 RpcSpec)) : gset u64 :=
  match l with
  | pnil => ∅
  | pcons x l => {[ pfst x ]} ∪ dom_RpcSpec_list l
  end.

Fixpoint is_urpc_spec_list γ host (l : plist (pprod u64 RpcSpec)) :=
  match l with
  | pnil => True%I
  | pcons x l =>
    (is_urpc_spec γ host (pfst x) (psnd x) ∗ is_urpc_spec_list γ host l)%I
  end.

Fixpoint RpcSpec_list_wf (l : plist (pprod u64 RpcSpec)) : Prop :=
  match l with
  | pnil => True
  | pcons x l =>
    (pfst x ∉ dom_RpcSpec_list l) ∧ RpcSpec_list_wf l
  end.

Lemma alloc_is_urpc_list (host : chan) (specs: plist (pprod u64 RpcSpec)) (Hwf: RpcSpec_list_wf specs) :
   host c↦ ∅ ={⊤}=∗ ∃ γ,
   is_urpc_dom γ (dom_RpcSpec_list specs) ∗
   is_urpc_spec_list γ host specs.
Proof.
  iIntros "Hchan".
  iMod (map_init (∅ : gmap u64 gname)) as (γmap) "Hmap_ctx".
  iMod (own_alloc (to_agree (dom_RpcSpec_list specs : gsetO u64))) as (γdom) "#Hdom".
  { econstructor. }
  set (Γsrv := {| scmap_name := γmap; scset_name := γdom |}).
  iMod (inv_alloc urpc_serverN _ ((server_chan_inner host Γsrv)) with "[Hchan]") as "#Hinv".
  { iNext. iExists _. iFrame.
    rewrite big_sepS_empty //. }
  iExists Γsrv.
  iAssert (∀ specs', ⌜ RpcSpec_list_wf specs' ⌝ ∗ ⌜ dom_RpcSpec_list specs' ⊆  dom_RpcSpec_list specs ⌝ →
           |==> ∃ gnames : gmap u64 gname, ⌜ dom gnames = dom_RpcSpec_list specs' ⌝ ∗
           map_ctx (scmap_name Γsrv) 1 gnames ∗
           is_urpc_spec_list Γsrv host specs')%I with "[Hmap_ctx]" as "H"; last first.
  { iMod ("H" with "[]") as (?) "(_&_&$)"; eauto. }
  iIntros (specs').
  iInduction specs' as [| hd spec] "IH".
  { iIntros (?). iModIntro. iExists ∅. iFrame.
    rewrite ?dom_empty_L //. }
  { iIntros ((Hwf'&Hdom')).
    iMod ("IH" with "[$] []") as (gnames Hdom) "(Hmap_ctx&Hmap)".
    { iPureIntro. split.
      - destruct Hwf' as (_&?); eauto.
      - etransitivity; last eassumption. set_solver. }
    iMod (saved_spec_alloc (RpcSpec_Spec (psnd hd))) as (γsave) "#Hsaved".
    iMod (map_alloc_ro (pfst hd) γsave
            with "Hmap_ctx") as "(Hmap_ctx&#Hsaved_name)"; auto.
    { apply not_elem_of_dom. destruct (Hwf') as (?&?). rewrite Hdom. eauto. }
    iExists _; iFrame. iModIntro.
    iSplit.
    { iPureIntro. rewrite ?dom_insert_L Hdom. set_solver. }
    iExists _, _. iFrame "#".
    { iPureIntro. simpl in Hdom'. set_solver. }
  }
Qed.

End rpc_global_defs.

Section urpc_spec_impl.
Context `{!heapGS Σ, !urpcregG Σ}.

Definition is_urpc_handler (f : val) (spec : RpcSpec)
   : iProp Σ :=
  ∀ (x : spec.(spec_ty)) (reqData : list u8) req rep,
  {{{
    own_slice_small req byteT (DfracOwn 1) reqData ∗
    rep ↦[slice.T byteT] (slice_val Slice.nil) ∗
    spec.(spec_Pre) x reqData
  }}}
    f (slice_val req) #rep
  {{{ rep_sl q repData, RET #();
      rep ↦[slice.T byteT] (slice_val rep_sl) ∗
      own_slice_small rep_sl byteT q repData ∗
      spec.(spec_Post) x reqData repData
  }}}.

(** Lift handler registration and RPC calls to RpcSpec *)

Lemma urpc_handler_to_handler f spec :
  is_urpc_handler f spec -∗
  is_urpc_handler_pred f (RpcSpec_Spec spec).
Proof.
  rewrite /is_urpc_handler_pred.
  iIntros "#Hf %reqData %Cont %req %repptr !# %Φ Hpre HΦ".
  iDestruct "Hpre" as "(Hreq & Hrepptr & Hpre)". iSimpl in "Hpre".
  iDestruct "Hpre" as (x) "[Hpre Hcont]".
  wp_apply ("Hf" with "[$Hrepptr $Hpre $Hreq]").
  iIntros (???) "(Hrepptr & Hrep & Hpost)".
  iApply "HΦ". iFrame. iApply "Hcont". done.
Qed.

Lemma wp_Client__Call γsmap (cl_ptr:loc) (rpcid:u64) (host:u64) req rep_out_ptr
      (timeout_ms : u64) dummy_sl_val (reqData:list u8) (spec : RpcSpec) (x : spec.(spec_ty)) :
  {{{
      "Hslice" ∷ own_slice_small req byteT (DfracOwn 1) reqData ∗
      "Hrep_out_ptr" ∷ rep_out_ptr ↦[slice.T byteT] dummy_sl_val ∗
      "#Hclient" ∷ is_uRPCClient cl_ptr host ∗
      "#Hhandler" ∷ is_urpc_spec γsmap host rpcid spec ∗
      "#Hspec" ∷ □(spec.(spec_Pre) x reqData)
  }}}
    urpc.Client__Call #cl_ptr #rpcid (slice_val req) #rep_out_ptr #timeout_ms
  {{{
       (err : option call_err), RET #(call_errno err);
       own_slice_small req byteT (DfracOwn 1) reqData ∗
       (if err is Some _ then rep_out_ptr ↦[slice.T byteT] dummy_sl_val else
        ∃ rep_sl (repData:list u8),
          rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
          own_slice_small rep_sl byteT (DfracOwn 1) repData ∗
          (spec.(spec_Post) x reqData repData))
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  iApply (wp_Client__Call_pred with "[Hhandler Hrep_out_ptr Hclient Hslice]").
  { iFrame "∗#".
    simpl. do 2 iModIntro.
    iExists _. iFrame "#". iIntros (?) "Hpost". iExact "Hpost". }
  done.
Qed.

Lemma wp_StartServer γ (host : u64) (handlers : gmap u64 val) (s : loc) :
  dom handlers ≠ ∅ →
  {{{
      handlers_complete γ handlers ∗
      own_Server s handlers ∗
      [∗ map] rpcid ↦ handler ∈ handlers,
      (∃ spec, is_urpc_spec γ host rpcid spec ∗ is_urpc_handler handler spec)
  }}}
    urpc.Server__Serve #s #host
  {{{
      RET #(); True
  }}}.
Proof.
  iIntros (? Φ) "(#Hcomplete&Hserver&#His_rpc_map) HΦ".
  wp_apply (wp_StartServer_pred with "[$Hserver]").
  { done. }
  { iFrame "#".
    iApply (big_sepM_impl with "His_rpc_map").
    iModIntro. iIntros (???) "[% [? ?]]".
    iExists _. iFrame.
    by iApply urpc_handler_to_handler.
  }
  by iApply "HΦ".
Qed.

End urpc_spec_impl.

Arguments pnil {A}.
Arguments pcons {A} a l.
Arguments ppair {A} {B} a b.
