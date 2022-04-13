(** Pre-postcondition-style specs for uRPCs
(translated to the predicate transformer style of the underlying lib *)
From Perennial.algebra Require Import auth_map.
From Perennial.base_logic Require Import lib.ghost_map lib.saved_spec.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Import urpc_proof.

Section rpc_global_defs.

Context `{!urpcregG Σ}.
Context `{HPRE: !gooseGlobalGS Σ}.

(* Higher-level interface for defining a handler with a given spec. *)
Record uRPCSpec :=
  { spec_rpcid : u64;
    spec_ty : Type;
    spec_Pre : spec_ty → list u8 → iProp Σ;
    spec_Post : spec_ty → list u8 → list u8 → iProp Σ }.

Program Definition uRPCSpec_Spec (spec : uRPCSpec) : savedSpecO Σ (list u8) (list u8) :=
  λ args, λne (Φ : list u8 -d> iPropO Σ), (∃ x : spec.(spec_ty),
    spec.(spec_Pre) x args ∗ (∀ rep, spec.(spec_Post) x args rep -∗ Φ rep))%I.
Next Obligation. (* FIXME solve_propert solved a very similar goal, why not this? *)
  intros ??? Φ1 Φ2 HΦ. f_equiv.
  intros x. f_equiv. f_equiv. intros rep. f_equiv. apply HΦ.
Qed.

Definition handler_urpc_spec Γsrv (host:u64) (spec : uRPCSpec) :=
  handler_spec Γsrv host spec.(spec_rpcid) (uRPCSpec_Spec spec).

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
    (handler_urpc_spec γ host x ∗
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
   handlers_dom γ (dom_uRPCSpecList specs) ∗
   handler_uRPCSpecList γ host specs.
Proof.
  iIntros "Hchan".
  iMod (map_init (∅ : gmap u64 gname)) as (γmap) "Hmap_ctx".
  iMod (own_alloc (to_agree (dom_uRPCSpecList specs : leibnizO (gset u64)))) as (γdom) "#Hdom".
  { econstructor. }
  set (Γsrv := {| scmap_name := γmap; scset_name := γdom |}).
  iMod (inv_alloc urpc_serverN _ ((server_chan_inner host Γsrv)) with "[Hchan]") as "#Hinv".
  { iNext. iExists _. iFrame.
    rewrite big_sepS_empty //. }
  iExists Γsrv.
  iAssert (∀ specs', ⌜ uRPCSpecList_wf specs' ⌝ ∗ ⌜ dom_uRPCSpecList specs' ⊆  dom_uRPCSpecList specs ⌝ →
           |==> ∃ gnames : gmap u64 gname, ⌜ dom (gset _) gnames = dom_uRPCSpecList specs' ⌝ ∗
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


End rpc_global_defs.
