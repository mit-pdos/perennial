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
Record uRPCSpec :=
  { spec_rpcid : u64;
    spec_ty : Type;
    spec_Pre : spec_ty → list u8 → iProp Σ;
    spec_Post : spec_ty → list u8 → list u8 → iProp Σ }.

Program Definition uRPCSpec_Spec (spec : uRPCSpec) : savedSpecO Σ (list u8) (list u8) :=
  λ args, λne (Φ : list u8 -d> iPropO Σ), (∃ x : spec.(spec_ty),
    spec.(spec_Pre) x args ∗ (∀ rep, spec.(spec_Post) x args rep -∗ Φ rep))%I.
Next Obligation. solve_proper. Qed.

Definition is_urpc_spec Γsrv (host:u64) (spec : uRPCSpec) :=
  is_urpc_spec_pred Γsrv host spec.(spec_rpcid) (uRPCSpec_Spec spec).

(* We define a custom type for a list of RPC specs in order to state lemmas
   about initializing a collection of handler_is facts. Unfortunately, using the
   standard list type leads to a universe error if the spec_ty field contains an
   iProp Σ, which turns out to be rather common. *)

Inductive uRPCSpecList : Type :=
| spec_nil : uRPCSpecList
| spec_cons (x: uRPCSpec) (l: uRPCSpecList) : uRPCSpecList.

Fixpoint dom_uRPCSpecList (l:  uRPCSpecList) : gset u64 :=
  match l with
  | spec_nil => ∅
  | spec_cons x l => {[ spec_rpcid x ]} ∪ dom_uRPCSpecList l
  end.

Fixpoint handler_uRPCSpecList γ host (l : uRPCSpecList) :=
  match l with
  | spec_nil => True%I
  | spec_cons x l =>
    (is_urpc_spec γ host x ∗
                handler_uRPCSpecList γ host l)%I
  end.

Fixpoint uRPCSpecList_wf (l : uRPCSpecList) : Prop :=
  match l with
  | spec_nil => True
  | spec_cons x l =>
    (spec_rpcid x ∉ dom_uRPCSpecList l) ∧ uRPCSpecList_wf l
  end.

Lemma handler_is_init_list (host : chan) (specs: uRPCSpecList) (Hwf: uRPCSpecList_wf specs) :
   host c↦ ∅ ={⊤}=∗ ∃ γ,
   is_urpc_dom γ (dom_uRPCSpecList specs) ∗
   handler_uRPCSpecList γ host specs.
Proof.
  iIntros "Hchan".
  iMod (map_init (∅ : gmap u64 gname)) as (γmap) "Hmap_ctx".
  iMod (own_alloc (to_agree (dom_uRPCSpecList specs : gsetO u64))) as (γdom) "#Hdom".
  { econstructor. }
  set (Γsrv := {| scmap_name := γmap; scset_name := γdom |}).
  iMod (inv_alloc urpc_serverN _ ((server_chan_inner host Γsrv)) with "[Hchan]") as "#Hinv".
  { iNext. iExists _. iFrame.
    rewrite big_sepS_empty //. }
  iExists Γsrv.
  iAssert (∀ specs', ⌜ uRPCSpecList_wf specs' ⌝ ∗ ⌜ dom_uRPCSpecList specs' ⊆  dom_uRPCSpecList specs ⌝ →
           |==> ∃ gnames : gmap u64 gname, ⌜ dom gnames = dom_uRPCSpecList specs' ⌝ ∗
           map_ctx (scmap_name Γsrv) 1 gnames ∗
           handler_uRPCSpecList Γsrv host specs')%I with "[Hmap_ctx]" as "H"; last first.
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
    iMod (saved_spec_alloc (uRPCSpec_Spec hd)) as (γsave) "#Hsaved".
    iMod (map_alloc_ro (spec_rpcid hd) γsave
            with "Hmap_ctx") as "(Hmap_ctx&#Hsaved_name)"; auto.
    { apply not_elem_of_dom. destruct (Hwf') as (?&?). rewrite Hdom. eauto. }
    iExists _; iFrame. iModIntro.
    iSplit.
    { iPureIntro. rewrite ?dom_insert_L Hdom. set_solver. }
    iExists _, _. iFrame "#".
    { iPureIntro. simpl in Hdom'. set_solver. }
  }
Qed.


(* More general version of above initialization lemma *)
Implicit Type (l:list (u64 * savedSpecO Σ (list u8) (list u8))).
Fixpoint is_urpc_spec_pred_list γ host l :=
  match l with
  | [] => True%I
  | x :: l =>
    (is_urpc_spec_pred γ host x.1 x.2 ∗ is_urpc_spec_pred_list γ host l)%I
  end.

Fixpoint dom_spec_list l : gset u64 :=
  match l with
  | [] => ∅
  | x :: l => {[ x.1 ]} ∪ dom_spec_list l
  end.

Fixpoint spec_list_wf l : Prop :=
  match l with
  | [] => True
  | x :: l =>
    (x.1 ∉ dom_spec_list l) ∧ spec_list_wf l
  end.

Lemma handler_is_init_list2 (host : chan) specs (Hwf: spec_list_wf specs) :
   host c↦ ∅ ={⊤}=∗ ∃ γ,
   is_urpc_dom γ (dom_spec_list specs) ∗
   is_urpc_spec_pred_list γ host specs.
Proof.
  iIntros "Hchan".
  iMod (map_init (∅ : gmap u64 gname)) as (γmap) "Hmap_ctx".
  iMod (own_alloc (to_agree (dom_spec_list specs : gsetO u64))) as (γdom) "#Hdom".
  { econstructor. }
  set (Γsrv := {| scmap_name := γmap; scset_name := γdom |}).
  iMod (inv_alloc urpc_serverN _ ((server_chan_inner host Γsrv)) with "[Hchan]") as "#Hinv".
  { iNext. iExists _. iFrame.
    rewrite big_sepS_empty //. }
  iExists Γsrv.
  iAssert (∀ specs', ⌜ spec_list_wf specs' ⌝ ∗ ⌜ dom_spec_list specs' ⊆  dom_spec_list specs ⌝ →
           |==> ∃ gnames : gmap u64 gname, ⌜ dom gnames = dom_spec_list specs' ⌝ ∗
           map_ctx (scmap_name Γsrv) 1 gnames ∗
           is_urpc_spec_pred_list Γsrv host specs')%I with "[Hmap_ctx]" as "H"; last first.
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
    iMod (saved_spec_alloc hd.2) as (γsave) "#Hsaved".
    iMod (map_alloc_ro (hd.1) γsave
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

Definition is_urpc_handler (f : val) (spec : uRPCSpec)
   : iProp Σ :=
  ∀ (x : spec.(spec_ty)) (reqData : list u8) req repptr dummy_rep_sl dummy,
  {{{
    own_slice_small req byteT 1 reqData ∗
    repptr ↦[slice.T byteT] (slice_val dummy_rep_sl) ∗
    own_slice (V:=u8) dummy_rep_sl byteT 1 dummy ∗
    spec.(spec_Pre) x reqData
  }}}
    f (slice_val req) #repptr
  {{{ rep_sl q repData, RET #();
      repptr ↦[slice.T byteT] (slice_val rep_sl) ∗
      own_slice_small rep_sl byteT q repData ∗
      spec.(spec_Post) x reqData repData
  }}}.

(** Lift handler registration and RPC calls to uRPCSpec *)

Lemma urpc_handler_to_handler f spec :
  is_urpc_handler f spec -∗
  is_urpc_handler_pred f (uRPCSpec_Spec spec).
Proof.
  rewrite /is_urpc_handler_pred.
  iIntros "#Hf %reqData %Cont %req %repptr !# %Φ Hpre HΦ".
  iDestruct "Hpre" as "(Hreq & Hrepptr & Hpre)". iSimpl in "Hpre".
  iDestruct "Hpre" as (x) "[Hpre Hcont]".
  wp_apply ("Hf" with "[$Hrepptr $Hpre $Hreq]").
  { iApply own_slice_zero. }
  iIntros (???) "(Hrepptr & Hrep & Hpost)".
  iApply "HΦ". iFrame. iApply "Hcont". done.
Qed.

Lemma wp_Client__Call_uRPCSpec γsmap (cl_ptr:loc) (rpcid:u64) (host:u64) req rep_out_ptr
      (timeout_ms : u64) dummy_sl_val (reqData:list u8) (spec : uRPCSpec) (x : spec.(spec_ty)) :
  rpcid = spec.(spec_rpcid) →
  is_urpc_spec γsmap host spec -∗
  {{{
      own_slice_small req byteT 1 reqData ∗
      rep_out_ptr ↦[slice.T byteT] dummy_sl_val ∗
      is_uRPCClient cl_ptr host ∗
      □(spec.(spec_Pre) x reqData)
  }}}
    urpc.Client__Call #cl_ptr #rpcid (slice_val req) #rep_out_ptr #timeout_ms
  {{{
       (err : option call_err), RET #(call_errno err);
       own_slice_small req byteT 1 reqData ∗
       (if err is Some _ then rep_out_ptr ↦[slice.T byteT] dummy_sl_val else
        ∃ rep_sl (repData:list u8),
          rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
          own_slice_small rep_sl byteT 1 repData ∗
          (spec.(spec_Post) x reqData repData))
  }}}.
Proof.
  iIntros (->) "#Hhandler !# %Φ Hpre HΦ".
  iDestruct "Hpre" as "(Hslice&Hrep_out_ptr&Hclient&#HSpec)".
  iApply (wp_Client__Call with "Hhandler [$Hrep_out_ptr $Hclient $Hslice]").
  { simpl. do 2 iModIntro.
    iExists _. iFrame "HSpec". iIntros (?) "Hpost". iExact "Hpost". }
  done.
Qed.

End urpc_spec_impl.
