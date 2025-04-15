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
  "#mu" ∷ w ↦[Work::"mu"]□ #mu ∗
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
  "#cond" ∷ w ↦[Work::"cond"]□ #cond ∗
  "#Hcond" ∷ is_cond cond #mu.

(* authority to read [Req] and write [Resp] *)
Definition own_Work (w req : loc) (spec : loc → (loc → iProp Σ) → iProp Σ) : iProp Σ :=
  ∃ Ψ,
  "Resp" ∷ w ↦[Work::"Resp"] #null ∗
  "#Req" ∷ w ↦[Work::"Req"]□ #req ∗
  "Hspec" ∷ (spec req Ψ) ∗
  "#His" ∷ is_Work w Ψ.

Definition own_WorkQ wq spec : iProp Σ :=
  ∃ work_sl (work_ptr : list loc),
    "work" ∷ wq ↦[WorkQ::"work"] (slice_val work_sl) ∗
    "Hwork_sl" ∷ own_slice work_sl ptrT (DfracOwn 1) work_ptr ∗
    "Hwork" ∷ ([∗ list] w ∈ work_ptr, ∃ req, own_Work w req spec)
.

Definition is_WorkQ wq spec : iProp Σ :=
  ∃ (mu cond : loc),
  "#mu" ∷ wq ↦[WorkQ::"mu"] #mu ∗
  "#Hmu" ∷ is_lock nroot #mu (own_WorkQ wq spec) ∗
  "#condCli" ∷ wq ↦[WorkQ::"cond"] #cond ∗
  "#HcondCli" ∷ is_cond cond #mu.

Lemma wp_NewWork spec (req : loc) Ψ :
  {{{ spec req Ψ }}}
    NewWork #req
  {{{ w, RET #w; own_Work w req spec ∗ is_Work w Ψ }}}.
Proof.
  iIntros (?) "Hpre HΦ". wp_rec. wp_apply wp_new_free_lock.
  iIntros (mu) "Hmu". wp_pures. wp_apply wp_allocStruct; [val_ty|].
  iIntros (w) "Hw". wp_pures. iDestruct (struct_fields_split with "Hw") as "H".
  iNamed "H". wp_loadField. wp_apply (wp_newCond' with "[$]").
  iIntros (?) "[Hmu #Hcond]". wp_storeField.
  iApply "HΦ".
  iMod (struct_field_pointsto_persist with "Req") as "#Req".
  iMod (struct_field_pointsto_persist with "mu") as "#mu".
  iMod (struct_field_pointsto_persist with "cond") as "#cond".
  iMod (alloc_lock with "Hmu [done]") as "#Hmu".
  2:{ iModIntro. iFrame "∗#". }
  iNext. iFrame.
Qed.

End proof.
