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

Section proof.
Context `{!heapGS Σ}.

Definition is_Work w Ψ : iProp Σ :=
  ∃ (mu cond : loc),
  "#mu" ∷ w ↦[Work::"mu"] #mu ∗
  "#Hmu" ∷ is_lock nroot #mu (
      ∃ (done : bool),
        "done" ∷ w ↦[Work::"done"] #done ∗
        "Hdone" ∷ if done then
            ∃ (Resp : loc),
            "#Resp" ∷ w ↦[Work::"Resp"]□ #Resp ∗
            "HΨ" ∷ Ψ Resp
          else
            True
    ) ∗
  "#cond" ∷ w ↦[Work::"cond"] #cond ∗
  "#Hcond" ∷ is_cond cond #mu.

(* authority to read [Req] and write [Resp] *)
Definition own_Work (w : loc) (spec : loc → (loc → iProp Σ) → iProp Σ) : iProp Σ :=
  ∃ Ψ (Req : loc),
  "#Req" ∷ w ↦[Work::"Req"] #Req ∗
  "Resp" ∷ w ↦[Work::"Resp"] #null ∗
  "Hspec" ∷ (spec Req Ψ) ∗
  "#His" ∷ is_Work w Ψ.

Definition own_WorkQ wq spec : iProp Σ :=
  ∃ work_sl (work_ptr : list loc),
    "work" ∷ wq ↦[WorkQ::"work"] (slice_val work_sl) ∗
    "Hwork_sl" ∷ own_slice work_sl ptrT (DfracOwn 1) work_ptr ∗
    "Hwork" ∷ ([∗ list] w ∈ work_ptr, own_Work w spec)
.

Definition is_WorkQ wq spec : iProp Σ :=
  ∃ (mu cond : loc),
  "#mu" ∷ wq ↦[WorkQ::"mu"] #mu ∗
  "#Hmu" ∷ is_lock nroot #mu (own_WorkQ wq spec) ∗
  "#condCli" ∷ wq ↦[WorkQ::"cond"] #cond ∗
  "#HcondCli" ∷ is_cond cond #mu.

End proof.
