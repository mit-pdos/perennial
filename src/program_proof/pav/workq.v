From New.experiments Require Import glob.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.
From iris.unstable.base_logic Require Import mono_list.

(* Even though the Go code is not generic, this proof is sorta generic by
   treating [Work] as having an opaque pointer for its [Req] and [Resp]. *)

Module Work.
Record t :=
  mk {
      done : bool;
      Req : loc;
      Resp : loc;
    }.
Section defn.
Context `{!heapGS Σ}.
Definition own l x : iProp Σ :=
  "done" ∷ l ↦[Work::"done"]{#1/2} #x.(done) ∗
  "Req" ∷ l ↦[Work::"Req"] #x.(Req) ∗
  "Resp" ∷ l ↦[Work::"Resp"] #x.(Resp)
.
End defn.
End Work.

Class workQG (Σ : gFunctors) := {
    work_mlistG :: mono_listG loc Σ
  }.

Inductive started_work_status :=
| WorkStarted
| WorkDone (resp : loc).

Record workQ :=
  mk {
      started_work : list started_work_status;
      new_reqs: list loc;
    }.

Section proof.
Context `{!heapGS Σ}.
Context `{!workQG Σ}.

Definition own_WorkQ wq (st : workQ) : iProp Σ :=
  ∃ work_sl (work_ptr : list loc),
    "work" ∷ wq ↦[WorkQ::"work"] (slice_val work_sl) ∗
    "Hwork_sl" ∷ own_slice work_sl ptrT (DfracOwn 1) work_ptr ∗
    "Hwork" ∷ ([∗ list] l; req ∈ work_ptr; st.(new_reqs), Work.own l (Work.mk false req null))
    "Hpast_work" ∷ ([∗ list] l; done ∈ past_work_ptrs; past_done,
                      l ↦[Work::"done"]{#1/2} #(LitBool done)
      ).

Definition own_WorkQ_ghost γ past_work_ptrs past_done reqs : iProp Σ :=
  mono_list_auth_own γ 1 past_work_ptrs ∗
  [∗ list] done ∈ past_done,
.

Definition is_WorkQ wq γ : iProp Σ :=
  ∃ (mu condCli condWorker : loc),
  "#mu" ∷ wq ↦[WorkQ::"mu"] #mu ∗
  "#Hmu" ∷ is_lock nroot #mu (∃ work, "Hown" ∷ own_WorkQ wq work ∗
                                      "Hghost" ∷ own_WorkQ_ghost γ work) ∗
  "#condCli" ∷ wq ↦[WorkQ::"condCli"] #condCli ∗
  "#HcondCli" ∷ is_cond condCli #mu ∗
  "#condWorker" ∷ wq ↦[WorkQ::"condWorker"] #condWorker ∗
  "#HcondWorker" ∷ is_cond condWorker #mu
.

End proof.
