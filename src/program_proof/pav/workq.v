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
Context `{!ghost_varG Σ unit}.

Definition is_Work w γ Ψ : iProp Σ :=
  ∃ (mu cond : loc),
  "#mu" ∷ w ↦[Work::"mu"]□ #mu ∗
  "#Hmu" ∷ is_lock nroot #mu (
      ∃ (done : bool),
        "done" ∷ w ↦[Work::"done"] #done ∗
        "Hdone" ∷ if done then
            ∃ (Resp : loc),
            "#Resp" ∷ w ↦[Work::"Resp"]□ #Resp ∗
            "HΨ" ∷ (ghost_var γ 1 () ∨ Ψ Resp)
          else
            True
    ) ∗
  "#cond" ∷ w ↦[Work::"cond"]□ #cond ∗
  "#Hcond" ∷ is_cond cond #mu.

(* authority to read [Req] and write [Resp] *)
Definition own_Work (w req : loc) (spec : loc → (loc → iProp Σ) → iProp Σ) : iProp Σ :=
  ∃ Ψ γ,
  "Resp" ∷ w ↦[Work::"Resp"] #null ∗
  "#Req" ∷ w ↦[Work::"Req"]□ #req ∗
  "Hspec" ∷ (spec req Ψ) ∗
  "#His" ∷ is_Work w γ Ψ.

Definition own_WorkQ wq spec : iProp Σ :=
  ∃ work_sl (work_ptr : list loc),
    "work" ∷ wq ↦[WorkQ::"work"] (slice_val work_sl) ∗
    "Hwork_sl" ∷ own_slice work_sl ptrT (DfracOwn 1) work_ptr ∗
    "Hwork" ∷ ([∗ list] w ∈ work_ptr, ∃ req, own_Work w req spec)
.

Definition is_WorkQ wq spec : iProp Σ :=
  ∃ (mu cond : loc),
  "#mu" ∷ wq ↦[WorkQ::"mu"]□ #mu ∗
  "#Hmu" ∷ is_lock nroot #mu (own_WorkQ wq spec) ∗
  "#cond" ∷ wq ↦[WorkQ::"cond"]□ #cond ∗
  "#Hcond" ∷ is_cond cond #mu.

Lemma wp_NewWork spec (req : loc) Ψ :
  {{{ spec req Ψ }}}
    NewWork #req
  {{{ w γ, RET #w; own_Work w req spec ∗ ghost_var γ 1 () ∗ is_Work w γ Ψ }}}.
Proof.
  iIntros (?) "Hpre HΦ". wp_rec. wp_apply wp_new_free_lock.
  iIntros (mu) "Hmu". wp_pures. wp_apply wp_allocStruct; [val_ty|].
  iIntros (w) "Hw". wp_pures. iDestruct (struct_fields_split with "Hw") as "H".
  iNamed "H". wp_loadField. wp_apply (wp_newCond' with "[$]").
  iIntros (?) "[Hmu #Hcond]". wp_storeField.
  iMod (ghost_var_alloc ()) as (γ) "Htok".
  iApply "HΦ". iFrame "Htok".
  iMod (struct_field_pointsto_persist with "Req") as "#Req".
  iMod (struct_field_pointsto_persist with "mu") as "#mu".
  iMod (struct_field_pointsto_persist with "cond") as "#cond".
  iMod (alloc_lock with "Hmu [done]") as "#Hmu".
  2:{ iModIntro. iFrame "∗#". }
  iNext. iFrame.
Qed.

Lemma wp_Work__Finish Ψ γ w (resp : loc) :
  {{{
      "Hw" ∷ is_Work w γ Ψ ∗
      "Resp" ∷ w ↦[Work::"Resp"] #resp ∗
      "Hpost" ∷ Ψ resp
  }}}
    Work__Finish #w
  {{{ RET #(); True }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre". wp_rec.
  iNamed "Hw". wp_loadField. wp_apply (wp_Mutex__Lock with "Hmu").
  iIntros "[Hlocked Hown]". iNamed "Hown". wp_pures. wp_storeField.
  wp_loadField. wp_apply (wp_Cond__Signal with "[$]"). wp_pures.
  wp_loadField. iClear "Hdone". iMod (struct_field_pointsto_persist with "Resp") as "#Resp".
  wp_apply (wp_Mutex__Unlock with "[-HΦ]"). { iFrame "#∗#". }
  wp_pures. by iApply "HΦ".
Qed.

Lemma wp_WorkQ__Do wq spec req :
  ∀ Φ,
  is_WorkQ wq spec -∗
  (spec req (λ resp, Φ #resp)) -∗
  WP WorkQ__Do #wq #req {{ Φ }}.
Proof.
  iIntros (?) "Hpre HΦ". wp_rec. wp_pures. iNamedSuffix "Hpre" "_wq".
  wp_apply (wp_NewWork with "HΦ"). iIntros "* (Hw & Htok & #His_w)".
  wp_pures. wp_loadField. wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown]". iNamed "Hown". wp_pures.
  wp_loadField. wp_apply (wp_SliceAppend with "[$Hwork_sl]").
  iIntros (work_sl') "Hwork_sl". wp_storeField. wp_loadField.
  wp_apply (wp_Cond__Signal with "[$]"). wp_pures. wp_loadField.
  wp_apply (wp_Mutex__Unlock with "[-Htok]").
  { iFrame "#∗#". rewrite big_sepL_nil //. }
  (* FIXME: iCombineNamed for persistent props. *)
  iClear "mu_wq Hmu_wq cond_wq Hcond_wq". clear work_sl work_ptr work_sl' mu cond.
  wp_pures. iNamed "His_w". wp_loadField. wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[? Hown]". wp_pures. wp_forBreak_cond.
  iNamed "Hown". wp_loadField. wp_pures. destruct done.
  {
    wp_pures. iRight. iModIntro. iSplitR; first done.
    wp_pures. wp_loadField. iNamed "Hdone".
    iDestruct "HΨ" as "[Hbad | HΦ]".
    { iCombine "Htok Hbad" gives %[Hbad _]. by apply Qp.not_add_le_l in Hbad. }
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "#∗#". }
    wp_pures. wp_loadField. iFrame.
  }
  {
    wp_pures. wp_loadField. wp_apply (wp_Cond__Wait with "[-Htok]").
    { iFrame "#∗#". }
    iIntros "[? Hown]". wp_pures. iLeft. iFrame. done.
  }
Qed.

Lemma wp_WorkQ__Get wq spec :
  {{{ "Hwq" ∷ is_WorkQ wq spec }}}
    WorkQ__Get #wq
  {{{
      work_sl (work : list loc), RET (slice_val work_sl);
        own_slice_small work_sl ptrT (DfracOwn 1) work ∗
        [∗ list] w ∈ work, ∃ req : loc, own_Work w req spec
  }}}.
Proof.
  iIntros (?) "Hpre HΦ". iNamed "Hpre". wp_rec. iNamed "Hwq".
  wp_loadField. wp_apply (wp_Mutex__Lock with "[$]"). iIntros "[Hlocked Hown]".
  wp_pures. wp_forBreak_cond.
  iNamed "Hown".
  wp_loadField. wp_pures.
  wp_pure; [done|].
  wp_if_destruct.
  {
    wp_loadField. wp_apply (wp_Cond__Wait with "[-HΦ]").
    { iFrame "#∗#". } iIntros "[? ?]". wp_pures. iLeft.
    iFrame. done.
  }
  iModIntro. iRight. iSplitR; first done.
  wp_pures. wp_loadField. wp_pures. wp_storeField.
  replace (slice.nil) with (slice_val Slice.nil) by done.
  wp_loadField. wp_apply (wp_Mutex__Unlock with "[-HΦ Hwork_sl Hwork]").
  { iFrame "#∗#". iDestruct (own_slice_zero) as "$". rewrite big_sepL_nil //. }
  wp_pures. iApply "HΦ". iDestruct (own_slice_to_small with "[$]") as "$".
  by iFrame.
Qed.

Lemma wp_NewWorkQ spec :
  {{{ True }}}
    NewWorkQ #()
  {{{ wq, RET #wq; is_WorkQ wq spec }}}.
Proof.
  iIntros (?) "Hpre HΦ". iApply wp_fupd. wp_rec. wp_apply wp_new_free_lock.
  iIntros (mu) "Hmu". wp_pures. wp_apply (wp_newCond' with "[$]").
  iIntros (cond) "[Hmu #Hcond]". wp_pures. wp_apply wp_allocStruct; [val_ty | ].
  iIntros (wq) "Hwq". iDestruct (struct_fields_split with "Hwq") as "H". iNamed "H".
  iApply "HΦ".
  iMod (struct_field_pointsto_persist with "mu") as "#mu".
  iMod (struct_field_pointsto_persist with "cond") as "#cond".
  iMod (alloc_lock with "Hmu [-]") as "$".
  { rewrite zero_slice_val. iFrame. iDestruct own_slice_zero as "$".
    rewrite big_sepL_nil //. }
  by iFrame "#".
Qed.

End proof.
