From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import aof.
From Perennial.algebra Require Import mlist map.
From iris.algebra Require Import mono_nat.
From Perennial.Helpers Require Import ModArith.
From Perennial.goose_lang Require Import crash_borrow.

From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.verus Require Import wpc_transformer.

Section file_wp_specs.
Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

Lemma wp_FileAppend f s q old data R R' Qc' S:
  {{{
        "Hsl" ∷ own_slice_small s byteT q data ∗
        "Hcrash" ∷ crash_borrow R (|C={⊤}=> Qc') ∗
        "Hacc" ∷ (R ={⊤}=∗ (f f↦ old) ∗
                  ((f f↦ old ∨ f f↦ (old ++ data)) -∗ |C={⊤}=> Qc') ∧ (f f↦ (old ++ data) ={⊤}=∗ R' ∗ S)) ∗
        "#HcrashOk" ∷ □(R' -∗ |C={⊤}=> Qc')
  }}}
    FileAppend #(str f) (slice_val s)
  {{{
        r, RET r; crash_borrow R' (|C={⊤}=> Qc') ∗ own_slice_small s byteT q data ∗ S
  }}}.
Proof.
  iIntros "* Hpre HΦ".
  iNamed "Hpre".
  wp_apply (wp_wpc_transformer_better  with "[- HΦ]").
  { done. }
  2:{
    iIntros "* [Hcrash HS]".
    iApply "HΦ".
    iFrame .
    shelve.
  }
  {
    iFrame "Hcrash".
    iSplit.
    {
      iIntros "HR".
      iMod ("Hacc" with "HR") as "[Hf HR]".
      iModIntro.
      wpc_apply wpc_cfupd.
      wpc_apply wpc_fupd.
      wpc_apply (wpc_FileAppend with "[$]").
      iSplit.
      { iLeft in "HR". iIntros "H". iMod ("HR" with "H") as "$". done. }
      { iNext. iRight in "HR".
        iIntros "[Hf Hsl]".
        iMod ("HR" with "Hf") as "HR".
        iModIntro. instantiate (1:=const _).
        simpl. iDestruct "HR" as "[HR HS]".
        iFrame. iAccu.
      }
    }
    iModIntro. simpl.
    iIntros "_ HR".
    iMod ("HcrashOk" with "HR"). iFrame. done.
  }
  Unshelve.
  iFrame.
Qed.

End file_wp_specs.

Section aof_proof.

Class aofG Σ := AofG {
  aof_flistG :> fmlistG u8 Σ ;
  aof_mnatG :> inG Σ mono_natUR ;
  aof_mapG :> mapG Σ u64 unit ;
  aof_tokG :> inG Σ (exclR unitO) ;
  (* XXX: a stagedG shows up in asyncfile, so don't want to bundle this in here. *)
  (* aof_stagedG :> stagedG Σ ; (* for crash borrows? *) *)
  aof_ghostG :> ghost_varG Σ unit ;
  aof_curdataG :> ghost_varG Σ (list u8) ;
}.

Definition aofΣ := #[
  fmlistΣ u8 ; GFunctor (mono_natUR) ;
  mapΣ u64 unit ;
  GFunctor (exclR unitO) ;
  ghost_varΣ unit ;
  ghost_varΣ (list u8)
].

Global Instance subG_aofΣ {Σ} : subG aofΣ Σ → aofG Σ.
Proof. solve_inG. Qed.

Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

Record aof_vol_names := mk_aof_vol_names {
  logdata : gname ;
  predurabledata : gname ;
  durabledata : gname ;
  len : gname ;
  len_toks : gname ;
  close_tok: gname ;
  close_req_tok: gname ;
  curdata : gname ;
  crashtok: gname ;
  initdata : list u8 ;
}.

Context `{aofG Σ}.

Implicit Types γ : aof_vol_names.
Implicit Types P: (list u8) → iProp Σ.

Definition aof_len_invariant γ : iProp Σ :=
  ∃ (l:u64),
    own γ.(len) (●MN{#1/2} (uint.nat l)) ∗
    [∗ set] x ∈ (fin_to_set u64), x ⤳[γ.(len_toks)] () ∨ ⌜uint.nat x > uint.nat l⌝
.

Definition aof_length_lb γ (l:u64) : iProp Σ :=
  own γ.(len) (mono_nat_lb (uint.nat l)).

Definition list_safe_size (l:list u8) := uint.nat (length l) = length l.

Definition aof_log_own γ data : iProp Σ :=
  fmlist γ.(logdata) (DfracOwn (1/2)) data ∗
  ghost_var γ.(close_req_tok) 1 () ∗
  ghost_var γ.(close_tok) 1 ()
.

Definition aof_durable_lb γ data : iProp Σ :=
  fmlist_lb γ.(durabledata) data
.

Context (aofN:namespace).
Definition aofN1 := aofN .@ "1".
Definition aofN2 := aofN .@ "2".
Definition aofNlk := aofN .@ "aoflk".
Definition aof_lenN := aofN .@ "aof_len".


Definition is_aof_ctx_inv γ P :=
  inv aofN1 (C ∗ ghost_var γ.(crashtok) 1 () ∨ (* either the node has crashed, *)
      ∃ (data:list u8),
        (fmlist γ.(logdata) DfracDiscarded data) ∗ ghost_var γ.(curdata) 1 data ∗ ghost_var γ.(close_req_tok) 1 ()
        ∨ (* or there's a witness that the user closed the file *)
      (* the fmlist_lb and the 1/2 durabledata ownership are to help prove a strong accessP lemma *)
      fmlist_lb γ.(logdata) data ∗ fmlist γ.(durabledata) (DfracOwn (1/2)) data ∗
      ghost_var γ.(curdata) (1/2) data ∗ P data) (* or P is available *)
.

Definition aof_close_resources (aof_ptr:loc) γ P Pcrash fname : iProp Σ :=
  ∃ (isClosed closeRequested:bool),
  "HcloseRequested" ∷ aof_ptr ↦[AppendOnlyFile :: "closeRequested"] #closeRequested ∗
  "Hclosed" ∷ aof_ptr ↦[AppendOnlyFile :: "closed"]{#1/2} #isClosed ∗ (* other half owned by background thread *)
  "#HexpectedData" ∷ (if closeRequested then ∃ expectedData, (fmlist γ.(logdata) (DfracDiscarded) expectedData) else True) ∗
  "Hreq_tok" ∷ (if closeRequested && negb isClosed then ghost_var γ.(close_req_tok) 1 () else True) ∗
  "HfileEscrow" ∷ (if isClosed then
              inv aofN2 (∃ data, crash_borrow (fname f↦ data ∗ P data) (|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ Pcrash data') ∗
                      fmlist γ.(logdata) DfracDiscarded data ∨
                      ghost_var γ.(close_tok) 1 ()
                     )
            else
                    True)
.

(* FIXME: the membuf fupd will need to be run while is_aof_ctx_inv is open, so
   it can't use aofN. Its mask needs adjustment. *)
Definition aof_mu_invariant (aof_ptr:loc) mu γ fname P Pcrash : iProp Σ :=
  ∃ membuf_sl membufC predurableC (durlen:u64) (durCond_ptr oldDurCond_ptr:loc),
  let memlen := length (predurableC ++ membufC) in
  "#Hcrash_wand" ∷ □ (∀ data, ▷ P data ={⊤}=∗ ▷ Pcrash data) ∗
  "Hmembuf" ∷ aof_ptr ↦[AppendOnlyFile :: "membuf"] (slice_val membuf_sl) ∗
  "HdurableLength" ∷ aof_ptr ↦[AppendOnlyFile :: "durableLength"]{#1/2} #durlen ∗
  "Hlength" ∷ aof_ptr ↦[AppendOnlyFile :: "length"] #(W64 memlen) ∗
  "Hmembuf_sl" ∷ typed_slice.own_slice membuf_sl byteT (DfracOwn 1) membufC ∗

  "Hpredurable" ∷ fmlist γ.(predurabledata) (DfracOwn (1/2)) (γ.(initdata) ++ predurableC) ∗
  "Hlogdata" ∷ fmlist γ.(logdata) (DfracOwn (1/2)) (γ.(initdata) ++ predurableC ++ membufC) ∗
  "%Hlengthsafe" ∷ ⌜list_safe_size (predurableC ++ membufC)⌝ ∗
  "Hlen_toks" ∷ ([∗ set] x ∈ (fin_to_set u64), x ⤳[γ.(len_toks)] () ∨ ⌜uint.nat x ≤ memlen⌝) ∗
  "Hmembuf_fupd" ∷ (P (γ.(initdata) ++ predurableC) -∗ fmlist_lb γ.(durabledata) (γ.(initdata) ++ predurableC ++ membufC)
                    ={⊤∖↑aofN}=∗ P (γ.(initdata) ++ predurableC ++ membufC)
     ∗ (own γ.(len) (●MN{#1/2} (length predurableC)) ={⊤}=∗ own γ.(len) (●MN{#1/2} memlen)
       )
  ) ∗
  "#Hdurlen_lb" ∷ aof_length_lb γ durlen ∗
  "Hclose" ∷ aof_close_resources aof_ptr γ P Pcrash fname ∗
  "HdurableCond" ∷ aof_ptr ↦[AppendOnlyFile :: "durableCond"] #durCond_ptr ∗
  "HoldDurableCond" ∷ aof_ptr ↦[AppendOnlyFile :: "oldDurableCond"] #oldDurCond_ptr ∗
  "#HoldDurCond" ∷ is_cond oldDurCond_ptr mu ∗
  "#HdurCond" ∷ is_cond durCond_ptr mu
.

Definition is_aof aof_ptr γ fname (P : (list u8) → iProp Σ) Pcrash : iProp Σ :=
  ∃ mu_ptr (lenCond_ptr cloCond_ptr:loc),
  "#Hmu" ∷ readonly (aof_ptr ↦[AppendOnlyFile :: "mu"] mu_ptr) ∗
  "#HlengthCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile :: "lengthCond"] #lenCond_ptr) ∗
  "#HclosedCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile :: "closedCond"] #cloCond_ptr) ∗
  "#HlenCond" ∷ is_cond lenCond_ptr mu_ptr ∗
  "#HcloCond" ∷ is_cond cloCond_ptr mu_ptr ∗
  "#Hmu_inv" ∷ is_lock aofNlk mu_ptr (aof_mu_invariant aof_ptr mu_ptr γ fname P Pcrash) ∗
  "#Haof_len_inv" ∷ inv aof_lenN (aof_len_invariant γ) ∗
  "#Hctx_inv" ∷ is_aof_ctx_inv γ P
.

Lemma ctx_inv_crash γ P data :
  is_aof_ctx_inv γ P -∗
  ghost_var γ.(curdata) (1 / 2) data -∗ ghost_var γ.(crashtok) 1 () -∗
  |C={⊤}=> ▷ P data.
Proof.
  iIntros "#Hinv Hcurdata Hcrashtok".

  iInv "Hinv" as "Hctx" "Hctx_close".
  iDestruct "Hctx" as "[[_ >Hbad]|Hctx]".
  { iDestruct (ghost_var_valid_2 with "Hcrashtok Hbad") as %Hbad.
    exfalso.
    naive_solver. }
  iDestruct "Hctx" as (?) "Hctx".
  iDestruct "Hctx" as "[[_ [>Hbad _]]|Hctx]".
  { iDestruct (ghost_var_valid_2 with "Hcurdata Hbad") as %Hbad.
    exfalso.
    naive_solver. }

  iDestruct "Hctx" as "(_ & _ & >Hcurdata2 & Hctx)".
  iDestruct (ghost_var_agree with "Hcurdata Hcurdata2") as %->.
  iIntros "#Hc".
  iMod ("Hctx_close" with "[Hcrashtok]").
  {
    iLeft. iFrame "∗#".
  }
  iFrame. done.
Qed.

Lemma ctx_inv_update γ P data data' Q :
prefix data data' →
  is_aof_ctx_inv γ P -∗
  £ 1 -∗
  fmlist_lb γ.(logdata) data' -∗
  (P data -∗ fmlist_lb γ.(durabledata) data' ={⊤∖↑aofN}=∗ P data' ∗ Q) -∗
  fmlist γ.(durabledata) (DfracOwn (1/2)) data -∗
  ghost_var γ.(curdata) (1/2) data -∗
  ghost_var γ.(crashtok) 1 () ={⊤}=∗
  ghost_var γ.(curdata) (1 / 2) data' ∗ ghost_var γ.(crashtok) 1 () ∗
  fmlist γ.(durabledata) (DfracOwn (1/2)) data' ∗ Q
.
Proof.
  intros.
  iIntros "#Hinv Hlc #Hloglb Hupd Hdurdata Hcurdata Hcrashtok".
  iInv "Hinv" as "Hctx" "Hctx_close".
  iMod (lc_fupd_elim_later with "Hlc Hctx") as "Hctx".
  iDestruct "Hctx" as "[[_ Hbad]|Hctx]".
  { iDestruct (ghost_var_valid_2 with "Hcrashtok Hbad") as %Hbad.
    exfalso.
    naive_solver. }
  iDestruct "Hctx" as (?) "Hctx".
  iDestruct "Hctx" as "[[_ [Hbad _]]|Hctx]".
  { iDestruct (ghost_var_valid_2 with "Hcurdata Hbad") as %Hbad.
    exfalso.
    naive_solver. }

  iDestruct "Hctx" as "(_ & Hdurdata2 & Hcurdata2 & Hctx)".
  iDestruct (ghost_var_agree with "Hcurdata Hcurdata2") as %<-.
  iCombine "Hdurdata Hdurdata2" as "Hdurdata".
  iMod (fmlist_update with "Hdurdata") as "[[Hdurdata Hdurdata2] Hdurdata_lb]".
  { done. }

  iMod (fmlist_get_lb with "Hdurdata") as "[Hdurdata #Hlog_lb]".
  iApply (fupd_mask_weaken (⊤ ∖ ↑aofN)); first by solve_ndisj.
  iIntros "Hfupd_clo".
  iMod ("Hupd" with "Hctx Hlog_lb") as "(Hctx & HQ)".
  iMod (ghost_var_update_2 with "Hcurdata Hcurdata2") as "[Hcurdata Hcurdata2]".
  { by rewrite Qp.half_half. }

  iMod "Hfupd_clo".
  iMod ("Hctx_close" with "[Hctx Hcurdata2 Hdurdata2]").
  {
    iRight. iExists _.
    iRight. iFrame "∗#".
  }
  iFrame.
  done.
Qed.

Lemma ctx_inv_close γ P data :
  is_aof_ctx_inv γ P -∗
  £ 1 -∗
  fmlist γ.(logdata) DfracDiscarded data -∗
  ghost_var γ.(curdata) (1 / 2) data -∗
  ghost_var γ.(close_req_tok) 1 () -∗
  ghost_var γ.(crashtok) 1 ()
  ={⊤}=∗
  P data ∗ ghost_var γ.(crashtok) 1 ()
.
Proof.
  iIntros "#Hinv Hlc Hclosed Hcurdata Hclose_req Hcrashtok".
  iInv "Hinv" as "Hctx" "Hctx_close".
  iMod (lc_fupd_elim_later with "Hlc Hctx") as "Hctx".
  iDestruct "Hctx" as "[[_ Hbad]|Hctx]".
  { iDestruct (ghost_var_valid_2 with "Hcrashtok Hbad") as %Hbad.
    exfalso.
    naive_solver. }
  iDestruct "Hctx" as (?) "Hctx".
  iDestruct "Hctx" as "[[_ [Hbad _]]|Hctx]".
  { iDestruct (ghost_var_valid_2 with "Hcurdata Hbad") as %Hbad.
    exfalso.
    naive_solver. }

  iDestruct "Hctx" as "(_ & _ & Hcurdata2 & Hctx)".
  iDestruct (ghost_var_agree with "Hcurdata Hcurdata2") as %->.
  iCombine "Hcurdata Hcurdata2" as "Hcurdata".

  iFrame.
  iMod ("Hctx_close" with "[-]").
  {
    iNext.
    iRight.
    iExists _; iLeft.
    iFrame.
  }
  done.
Qed.

Lemma wp_CreateAppendOnlyFile (fname:string) data P Pcrash :
□(∀ data, ▷ P data ={⊤}=∗ ▷ Pcrash data) -∗
  {{{
       crash_borrow (fname f↦ data ∗ P data)
                    (|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ Pcrash data')
  }}}
    CreateAppendOnlyFile #(str fname)
  {{{
       aof_ptr γ, RET #aof_ptr; is_aof aof_ptr γ fname P Pcrash ∗ aof_log_own γ data ∗ aof_durable_lb γ data
  }}}.
Proof.
  iIntros "#Hcrash_wand !#" (Φ) "Hpre HΦ".
  wp_lam.

  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
  iIntros (l) "Hl".
  iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl".

  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (mu) "Hmu_free".

  wp_pures.
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "Hmu_free").
  iIntros (lengthCond) "[Hmu_free #HlenCond]".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "Hmu_free").
  iIntros (durableCond) "[Hmu_free #HdurCond]".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "Hmu_free").
  iIntros (closedCond) "[Hmu_free #HoldDurCond]".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "Hmu_free").
  iIntros (oldDurableCond) "[Hmu_free #HcloCond]".

  (* Allocate ghost state and invariants *)
  iMod (fmlist_alloc data) as (γlogdata) "[Hlogdata Hlogdata2]".
  iMod (fmlist_get_lb with "Hlogdata2") as "[Hlogdata2 #Hlog_lb]".
  iMod (fmlist_alloc data) as (γpredurabledata) "[Hpredurable Hpredurable2]".
  iMod (fmlist_alloc data) as (γdurabledata) "[Hdurabledata Hdurabledata2]".
  iMod (fmlist_get_lb with "Hdurabledata") as "[Hdurabledata #Hdurable_lb]".
  iMod (ghost_map_alloc_fin ()) as (γlen_toks) "Hlen_toks".
  iMod (own_alloc (●MN 0)) as (γlen) "[Hlen Hlen2]".
  { apply mono_nat_auth_valid. }

  iDestruct (own_mono _ _ (◯MN 0) with "Hlen2") as "#Hdurlen_lb".
  { apply mono_nat_included. }
  iDestruct "durableLength" as "[HdurableLength HdurableLength2]".
  iMod (ghost_var_alloc ()) as (γclose_tok) "Hclose_tok".
  iMod (ghost_var_alloc ()) as (γclose_req_tok) "Hclose_req_tok".
  iMod (ghost_var_alloc data) as (γcurdata) "[Hcurdata Hcurdata2]".
  iMod (ghost_var_alloc ()) as (γcrashtok) "Hcrashtok".
  set (γ:=mk_aof_vol_names γlogdata γpredurabledata γdurabledata γlen γlen_toks γclose_tok γclose_req_tok γcurdata γcrashtok data).


  iDestruct (crash_borrow_wpc_nval _ _ _ (fname f↦data ∗ ghost_var γcurdata (1/2) data ∗ ghost_var γ.(crashtok) 1 ())
                                   (is_aof_ctx_inv γ P) with "Hpre [Hcurdata2 Hcurdata Hcrashtok Hdurabledata2]") as "Hnval_pre".
  {
    iNext.
    iIntros "[Hf HP]".
    iMod (inv_alloc with "[HP Hcurdata2 Hdurabledata2]") as "#Hctx_inv"; last iFrame "Hctx_inv".
    {
      iNext. iRight.
      iExists data.
      iRight.
      iFrame "∗#".
    }
    iFrame.
    instantiate (1:=⊤).
    iModIntro.
    iModIntro.
    iIntros "(Hf & Hcurdata & Htok)".
    iMod (ctx_inv_crash with "Hctx_inv Hcurdata Htok") as "HP".
    iMod ("Hcrash_wand" with "HP") as "HP".
    iModIntro.
    iExists _; iFrame.
  }

  wp_bind (struct.storeF _ _ _ _).
  iApply (wpc_wp _ _ _ _ True).
  wpc_apply (wpc_nval_elim with "Hnval_pre").
  { done. }
  { done. }
  iApply wp_wpc.
  wp_storeField.
  iIntros "[#Hctx_inv Hpre]".
  iDestruct "closed" as "(closed1&closed2)".

  iAssert ((|={⊤}=> is_aof l γ fname P Pcrash ∗
                      fmlist γ.(predurabledata) (DfracOwn (1/2)) γ.(initdata) ∗
                      fmlist γ.(durabledata) (DfracOwn (1/2)) γ.(initdata) ∗
                      l ↦[AppendOnlyFile :: "durableLength"]{#1/2} #0 ∗
                      own γ.(len) (●MN{#1/2} 0) ∗
                      aof_log_own γ γ.(initdata) ∗
                      ⌜data = γ.(initdata)⌝
                          )
          )%I with "[-Hpre closed2 HΦ]" as ">HH".
  {
    iAssert (
    ([∗ set] x ∈ fin_to_set u64,
      (x ⤳[γlen_toks] () ∨ ⌜uint.nat x ≤ 0%nat⌝) ∗
      (x ⤳[γlen_toks] () ∨ ⌜uint.nat x > 0%nat⌝))
      )%I with "[Hlen_toks]" as "HH".
    {
      iApply (big_sepS_impl with "Hlen_toks").
      iModIntro.
      iIntros.
      destruct (decide (uint.nat x <= 0%nat)).
      {
        iSplitR; iFrame.
        iRight. iPureIntro. done.
      }
      assert (uint.nat x > 0%nat) by word.
      iSplitL; iFrame.
      iRight. iPureIntro. done.
    }
    iDestruct (big_sepS_sep with "HH") as "[Hlen_toks Hlen_toks2]".

    iMod (inv_alloc aof_lenN _ (aof_len_invariant γ) with "[Hlen2 Hlen_toks2]") as "#Hinv".
    {
      iNext.
      iExists (W64 0).
      iFrame.
    }
    iMod (readonly_alloc_1 with "mu") as "#Hmu".
    iMod (readonly_alloc_1 with "lengthCond") as "#HlengthCond".
    iMod (readonly_alloc_1 with "closedCond") as "#HclosedCond".

    iMod (alloc_lock _ _ _ (aof_mu_invariant l (#mu) γ fname P Pcrash) with "Hmu_free [-Hlogdata2 HdurableLength2 Hpredurable2 Hdurabledata Hlen Hclose_tok Hclose_req_tok]") as "#HmuInv".
    {
      iNext.
      iExists (Slice.nil), [], [], (W64 0), _, _.
      iDestruct own_slice_zero as "$".
      simpl.
      rewrite app_nil_r.
      iFrame "∗#".
      iSplitR; first done.
      iSplitR.
      { by iIntros "$ _ !> $ !>". }
      done.
    }
    iModIntro.
    iFrame.
    iSplitL; last done.
    repeat iExists _.
    iFrame "#".
  }
  iDestruct "HH" as "(#His_aof & Hpredur & Hdur & HdurLen & Hlen & Hlog_own & %Hre)".
  rewrite Hre.
  replace (data) with (γ.(initdata)) by done.
  clear Hre.
  rename data into initial_data.
  wp_pures.
  wp_apply (wp_fork with "[-HΦ Hlog_own]").
  {
    iNext.
    iEval (simpl) in "closed2".
    iClear "HlenCond HdurCond HoldDurCond HcloCond Hcrash_wand Hctx_inv".
    iNamed "His_aof".
    wp_loadField.
    wp_apply (acquire_spec with "Hmu_inv").
    iIntros "[Hlocked Haof_own]".
    wp_pures.
    iAssert (∃ data',
              crash_borrow
             (fname f↦(γ.(initdata) ++ data') ∗ ghost_var γcurdata (1 / 2) (γ.(initdata) ++ data') ∗
                ghost_var γ.(crashtok) 1 ())
             (|C={⊤}=> ∃ data' : list u8, fname f↦data' ∗ ▷ Pcrash data') ∗

              fmlist γ.(predurabledata) (DfracOwn (1/2)) (γ.(initdata) ++ data') ∗
              fmlist γ.(durabledata) (DfracOwn (1/2)) (γ.(initdata) ++ data') ∗
              l ↦[AppendOnlyFile :: "durableLength"]{#1 / 2} #(W64 (length data')) ∗
              own γ.(len) (●MN{#1/2} (length (data')))
            )%I with "[Hpre Hdur Hpredur HdurLen Hlen]" as "Hfile_ctx".
    { iExists []; iFrame. rewrite app_nil_r. iFrame. }
    wp_forBreak.
    wp_pure1_credit "Hlc".

    iClear "Hdurlen_lb".
    iNamed "Haof_own".
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_pure1_credit "Hlc2".

    iNamed "Hclose".
    wp_apply (wp_and with "[HcloseRequested]").
    { iNamedAccu. }
    {
      wp_pures.
      done.
    }
    {
      iIntros.
      wp_loadField.
      wp_pures.
      iFrame.
      instantiate (2:=(closeRequested = false)).
      instantiate (1:=decide_rel eq _ _).
      iPureIntro.
      f_equal.
      destruct closeRequested.
      { rewrite bool_decide_false; done. }
      { rewrite bool_decide_true; done. }
    }
    iNamed 1.

    wp_if_destruct.
    {
      wp_loadField.
      wp_apply (wp_condWait with "[- closed2 Hfile_ctx]").
      { by iFrame "HlenCond Hmu_inv ∗#". }
      iIntros "[Hlocked Haof_own]".
      wp_pures.
      iLeft.
      iFrame.
      done.
    }

    wp_loadField.

    (* Prepare ghost state for writing to file; whether we close the file or
       not, we're going to do the FileAppend *)
    iDestruct "Hfile_ctx" as (data') "(Hfile_ctx & Hpredur & Hdur & HdurLen & Hlen)".
    iDestruct (fmlist_agree_1 with "Hpredur Hpredurable") as %Hpredur.
    apply app_inv_head in Hpredur.
    rewrite Hpredur.
    iCombine "Hpredur Hpredurable" as "Hpredur".
    iMod (fmlist_update (γ.(initdata) ++ predurableC ++ membufC) with "Hpredur") as "[Hpredur _]".
    { rewrite app_assoc. apply prefix_app_r. done. }
    iDestruct "Hpredur" as "[Hpredur Hpredurable]".

    iClear "Hlog_lb".
    iMod (fmlist_get_lb with "Hlogdata") as "[Hlogdata #Hlog_lb]".

    wp_if_destruct.
    { (* case: close aof; write the remaining stuff first, using the same
         arugment as when we write with the lock *)
      wp_loadField.

      (*
      wp_bind (FileAppend _ _).
      iApply (wpc_wp _ _ _ _ True).
      wpc_apply (wpc_crash_borrow_open_modify with "Hfile_ctx").
      { done. }
      iSplit; first done.
      iIntros "(Hfile & Hcurdata & Hcrashtok)".
      iApply wpc_fupd. *)

      iDestruct (own_slice_to_small with "Hmembuf_sl") as "Hmembuf_sl".
      (* wpc_apply (wpc_FileAppend with "[$Hfile $Hmembuf_sl]"). *)
      wp_apply (wp_FileAppend with "[-]").
      {
        iFrame "Hfile_ctx Hmembuf_sl".
        iSplitL.
        {
          iIntros "(Hfile & Hcurdata & Hcrashtok)".
          iFrame "Hfile".
          iModIntro.
          iSplit.
          { (* case that node crashes during FileAppend *)
            iIntros "[Hbefore|Hafter]".
            {
              iMod (ctx_inv_crash with "Hctx_inv Hcurdata Hcrashtok") as "HP".
              iMod ("Hcrash_wand" with "HP") as "HP".
              iModIntro.
              iExists _. iFrame.
            }
            {
              repeat rewrite -app_assoc.
              iMod (ctx_inv_update with "Hctx_inv Hlc Hlog_lb [Hmembuf_fupd] Hdur Hcurdata Hcrashtok") as "(Hcurdata & Hcrashtok & _)".
              {
                rewrite app_assoc.
                apply prefix_app_r.
                done.
              }
              {
                instantiate (1:=True%I).
                iIntros "HP Hlb".
                iMod ("Hmembuf_fupd" with "HP Hlb") as "[$ _]".
                done.
              }
              iMod (ctx_inv_crash with "Hctx_inv Hcurdata Hcrashtok") as "HP".
              iMod ("Hcrash_wand" with "HP") as "HP".
              iModIntro.
              iExists _. iFrame.
            }
          }
          { (* case that operation succeeds *)
            (* commit remaining operations before we close the file. *)
            iMod (ctx_inv_update with "Hctx_inv Hlc Hlog_lb [Hmembuf_fupd] Hdur Hcurdata Hcrashtok") as "(Hcurdata & Hcrashtok & Hdur & Hlen_fupd)".
            { rewrite app_assoc. apply prefix_app_r. done. }
            {
              iIntros "HP Hlb".
              iMod ("Hmembuf_fupd" with "HP Hlb") as "[$ Hlen_fupd]".
              iModIntro.
              iExact "Hlen_fupd".
            }

            iMod ("Hlen_fupd" with "Hlen") as "Hlen".
            iEval (rewrite mono_nat_auth_lb_op) in "Hlen".
            iDestruct "Hlen" as "[Hlen #Hlenlb]".

            (* Going to return the crash borrow to the user, so get it back into the
               form they want. *)
            iNamed "Hclose".
            iDestruct "HexpectedData" as (?) "HexpectedData".
            iDestruct (fmlist_agree_1 with "HexpectedData Hlogdata") as %->.
            iDestruct (struct_field_pointsto_agree with "Hclosed closed2") as %Heq.
            assert (isClosed = false) by naive_solver.

            iMod (ctx_inv_close with "Hctx_inv Hlc2 HexpectedData Hcurdata [Hreq_tok] Hcrashtok") as "[HP Hcrashtok]".
            { subst. iFrame. }

            rewrite -app_assoc.
            iIntros "Hfile".
            iModIntro.
            iAssert (⌜ isClosed = false ⌝)%I as "-#HisClosed"; first done.
            iDestruct "HexpectedData" as "-#HexpectedData".
            iDestruct "Hlenlb" as "-#Hlenlb".
            iSplitL "Hfile HP".
            { iAccu. }
            iNamedAccu.
          }
        }
        {
          iModIntro. iIntros "(Hfile & HP)".
          iMod ("Hcrash_wand" with "HP") as "HP".
          iModIntro.
          iExists _. iFrame.
        }
      }
      simpl.

      (* FIXME: find a nicer way to carry resources through in wp_FileAppend spec. *)
      iIntros (r) "(Hfile_ctx & Hslice & HS)".
      iNamed "HS".
      iDestruct "HisClosed" as "%HisClosed". subst.
      iDestruct "HexpectedData" as "#HexpectedData".
      iDestruct "Hlenlb" as "#Hlenlb".
      wp_pures.

      wp_apply (wp_NewSlice).
      iIntros (empty_membuf_sl) "Hmembuf_empty".
      wp_storeField.

      wp_loadField.

      iDestruct (struct_field_pointsto_agree with "HdurLen HdurableLength") as %Heq'.
      rewrite Heq'.
      iCombine "HdurLen HdurableLength" as "HdurLen".
      wp_storeField.
      wp_loadField.
      wp_apply (wp_condBroadcast).
      { iFrame "#". }
      wp_pures.
      iCombine "closed2 Hclosed" as "Hclosed".
      wp_storeField.
      iDestruct "Hclosed" as "(closed2&Hclosed)".
      wp_loadField.
      wp_apply (wp_condBroadcast).
      { iFrame "#". }
      wp_pures.
      wp_loadField.

      iMod (inv_alloc with "[Hfile_ctx]") as "#HfileEscrow2".
      {
        instantiate (1:=(∃ data : list u8,
                       crash_borrow (fname f↦data ∗ P data)
                       (|C={⊤}=> ∃ data'0 : list u8, fname f↦data'0 ∗ ▷ Pcrash data'0) ∗
                       fmlist γ.(logdata) DfracDiscarded data ∨ ghost_var γ.(close_tok) 1 ())%I).
        iNext.
        iExists _.
        iLeft.
        iFrame "∗#".
      }

      wp_apply (release_spec with "[-Hlen closed2]").
      {
        iFrame "Hmu_inv Hcrash_wand Hlocked".
        iNext.
        iDestruct "HdurLen" as "[HdurableLength HdurLen]".
        iExists _, [], _.
        rewrite app_nil_r.
        iFrame "∗#%".
        iSplitR.
        { by iIntros "$ _ !> $ !>". }
        unfold aof_length_lb.
        rewrite Hlengthsafe.
        iFrame "∗#".
      }
      wp_pures.
      iRight.
      done.
    }

    (* case: don't want to close the file, do a FileAppend after letting go of
       mutex and loop *)
    wp_loadField.
    wp_pures.
    wp_loadField.
    wp_pures.

    wp_apply (wp_new_slice).
    { done. }
    iIntros (empty_membuf_sl) "Hmembuf_empty".
    wp_apply (wp_storeField with "Hmembuf").
    { unfold AppendOnlyFile. unfold field_ty. simpl. apply slice_val_ty. }
    iIntros "Hmembuf".

    wp_pures.
    wp_loadField.
    wp_pures.
    wp_loadField.
    wp_storeField.
    wp_storeField.
    wp_loadField.

    wp_apply (release_spec with "[-Hfile_ctx Hpredur Hdur Hmembuf_fupd Hmembuf_sl HdurLen Hlen closed2]").
    { iFrame "Hmu_inv Hlocked Hcrash_wand". iNext. iExists _, [], (predurableC ++ membufC),_, _, _.
      rewrite app_nil_r. iFrame "∗#".
      iSplitL ""; first done.
      iIntros "$ _ !> $ !> //".
    }

    wp_pure1_credit "Hlc".
    wp_pures.

    iDestruct (typed_slice.own_slice_sz with "Hmembuf_sl") as %Hsz.
    iDestruct (own_slice_to_small with "Hmembuf_sl") as "Hmembuf_sl".

    wp_bind (FileAppend _ _).
    iApply (wpc_wp _ _ _ _ True).
    wpc_apply (wpc_crash_borrow_open_modify with "Hfile_ctx").
    { done. }
    iSplit; first done.
    iIntros "(Hfile & Hcurdata & Hcrashtok)".
    iApply wpc_fupd.

    wpc_apply (wpc_FileAppend with "[$Hfile $Hmembuf_sl]").
    iSplit.
    { (* This is the case in which the node crashes during the FileAppend. *)
      iIntros "[Hbefore|Hafter]".
      {
        iSplitR; first done.
        iMod (ctx_inv_crash with "Hctx_inv Hcurdata Hcrashtok") as "HP".
        iMod ("Hcrash_wand" with "HP") as "HP".
        iModIntro.
        iExists _. iFrame.
      }
      {
        iSplitR; first done.

        repeat rewrite -app_assoc.
        iMod (ctx_inv_update with "Hctx_inv Hlc Hlog_lb [Hmembuf_fupd] Hdur Hcurdata Hcrashtok") as "(Hcurdata & Hcrashtok & _)".
        {
          rewrite app_assoc.
          apply prefix_app_r.
          done.
        }
        {
          instantiate (1:=True%I).
          iIntros "HP Hlb".
          iMod ("Hmembuf_fupd" with "HP Hlb") as "[$ _]".
          done.
        }
        iMod (ctx_inv_crash with "Hctx_inv Hcurdata Hcrashtok") as "HP".
        iMod ("Hcrash_wand" with "HP") as "HP".
        iModIntro.
        iExists _. iFrame.
      }
    }

    iNext.
    iIntros "[Hfile _]".

    (* commit remaining operations before we close the file. *)
    iMod (ctx_inv_update with "Hctx_inv Hlc Hlog_lb [Hmembuf_fupd] Hdur Hcurdata Hcrashtok") as "(Hcurdata & Hcrashtok & Hdur & Hlen_fupd)".
    { rewrite app_assoc. apply prefix_app_r. done. }
    {
      iIntros "HP Hlb".
      iMod ("Hmembuf_fupd" with "HP Hlb") as "[$ Hlen_fupd]".
      iModIntro.
      iExact "Hlen_fupd".
    }

    iMod ("Hlen_fupd" with "Hlen") as "Hlen".
    iEval (rewrite mono_nat_auth_lb_op) in "Hlen".
    iDestruct "Hlen" as "[Hlen #Hlenlb]".

    iModIntro.
    iExists _.

    iSplitL "Hfile Hcurdata Hcrashtok".
    { iNamedAccu. }
    iSplit.
    {
      iModIntro. iNamed 1.
      iMod (ctx_inv_crash with "Hctx_inv Hcurdata Hcrashtok") as "HP".
      iMod ("Hcrash_wand" with "HP") as "HP".
      iModIntro.
      iExists _. rewrite -app_assoc.
      iFrame.
    }

    iIntros "Hfile_ctx".
    iSplit; first done.

    wp_pures.
    wp_loadField.
    wp_apply (acquire_spec with "Hmu_inv").
    iIntros "[Hlocked Haof_own]".
    iRename "Hdurlen_lb" into "Hdurlen_lb_old".
    iClear "Hcrash_wand".
    (* iRename "HdurCond" into "HoldDurCond". *)
    iNamed "Haof_own".
    wp_pures.

    iDestruct (struct_field_pointsto_agree with "HdurLen HdurableLength") as %Heq.
    rewrite Heq.
    iCombine "HdurLen HdurableLength" as "HdurLen".
    wp_storeField.

    wp_apply (wp_condBroadcast).
    { iFrame "#". }
    wp_pures.
    iLeft.
    iFrame.
    iSplitL ""; first done.
    iDestruct "HdurLen" as "[HdurableLength HdurLen]".
    iFrame.
    iSplitR "Hfile_ctx".
    {
      iFrame "∗#".
      unfold aof_length_lb.
      iSplitL ""; first done.
      unfold aof_length_lb.
      rewrite Hlengthsafe.
      iFrame "#".
      done.
    }
    {
      rewrite -Hpredur.
      repeat rewrite -app_assoc.
      by iFrame.
    }
  }
  wp_pures.
  iApply "HΦ".
  iFrame "∗#".
  done.
Qed.

Lemma wp_AppendOnlyFile__Append Q aof_ptr γ data_sl P Pcrash fname (oldData newData:list u8) q :
length newData > 0 →
list_safe_size newData →
is_aof aof_ptr γ fname P Pcrash -∗
  {{{
       typed_slice.own_slice_small data_sl byteT q newData ∗ aof_log_own γ oldData ∗
       (P oldData ={⊤∖↑aofN}=∗ P (oldData ++ newData) ∗ Q)
  }}}
    AppendOnlyFile__Append #aof_ptr (slice_val data_sl)
  {{{
       (l:u64), RET #l; aof_log_own γ (oldData ++ newData) ∗
                        (aof_length_lb γ l ={⊤}=∗ ▷ Q ∗ aof_durable_lb γ (oldData ++ newData))
  }}}.
Proof.
  intros HnewDataLen HnewDataSafe.
  iIntros "#Haof" (Φ) "!# Hpre HΦ".
  iNamed "Haof".
  wp_lam.
  wp_pures.

  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hlocked Haof]".
  iNamed "Haof".
  iDestruct "Hpre" as "(HnewData & Haof_log & Hfupd)".
  wp_pures.

  wp_loadField.
  iDestruct (own_slice_small_sz with "HnewData") as %Hsz.

  wp_apply (wp_WriteBytes with "[$Hmembuf_sl $HnewData]").
  iIntros (membuf_sl') "[Hmembuf_sl HnewData]".
  wp_apply (wp_storeField with "Hmembuf").
  { unfold AppendOnlyFile. unfold field_ty. simpl. apply slice_val_ty. }
  iIntros "Hmembuf".

  wp_pures.

  (* overflow guard *)
  wp_apply (wp_slice_len).
  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros (HnoOverflow).
  wp_storeField.

  wp_loadField.
  wp_pures.
  rewrite -HnewDataSafe in Hsz.
  assert (W64 (length newData) = data_sl.(Slice.sz)) as HH.
  {
    apply Z2Nat.inj in Hsz.
    { word_cleanup. naive_solver. }
    { word_cleanup. naive_solver. }
    word.
  }
  rewrite -HH.
  rewrite -HH in HnoOverflow.
  wp_pures.
  wp_loadField.
  wp_apply (wp_condSignal).
  { iFrame "#". }

  wp_pures.

  unfold aof_log_own.
  iDestruct "Haof_log" as "[Haof_log Htok]".
  iDestruct (fmlist_agree_1 with "Haof_log Hlogdata") as %->.
  iCombine "Haof_log Hlogdata" as "Haof_log".

  iMod (fmlist_update ((γ.(initdata) ++ predurableC ++ membufC) ++ newData) with "Haof_log") as "[Haof_log _]".
  { apply prefix_app_r. done. }

  iDestruct "Haof_log" as "[Hlogdata Haof_log]".

  rewrite -app_assoc.
  (* Want to prove membuf_fupd, and the postcondition *)
  set (membufC' := membufC ++ newData) in *.

  iAssert (([∗ set] x ∈ (fin_to_set u64 : gset u64), x ⤳[γ.(len_toks)] () ∨
                      ⌜uint.nat x <= length (predurableC ++ membufC)⌝ ∨
                      ⌜length (predurableC ++ membufC') < uint.nat x⌝
          ) ∗
          ([∗ set] x ∈ (fin_to_set u64 : gset u64), x ⤳[γ.(len_toks)] () ∨
                      ⌜uint.nat x ≤ length (predurableC ++ membufC')⌝
          ))%I
    with "[Hlen_toks]"
    as "HH".
  {
    iApply big_sepS_sep.
    iApply (big_sepS_impl with "Hlen_toks").
    iModIntro.
    iIntros (x ?) "Hx".
    iDestruct "Hx" as "[Hx|%Hineq]".
    {
      destruct (bool_decide (length (predurableC ++ membufC') < uint.nat x)) as [|] eqn:Hineq.
      {
        apply bool_decide_eq_true in Hineq.
        iSplitR "Hx".
        { iRight; iRight. done. }
        iLeft. iFrame.
      }
      {
        apply bool_decide_eq_false in Hineq.
        iSplitL "Hx".
        { iFrame. }
        iRight.
        iPureIntro.
        word.
      }
    }
    {
      iSplitL.
      {
        iRight; iLeft. done.
      }
      iRight. iPureIntro.
      replace (membufC') with (membufC ++ newData) by done.
      rewrite app_assoc.
      rewrite app_length.
      word.
    }
  }

  iDestruct "HH" as "[Htoks Hlen_toks]".

  assert (uint.nat (W64 (length (predurableC ++ membufC'))) = (length (predurableC ++ membufC'))) as Hsafesize'.
  {
    replace (membufC') with (membufC ++ newData) by done.
    rewrite app_assoc.
    rewrite app_length.
    word_cleanup.
    rewrite -Hlengthsafe.
    repeat (rewrite Nat2Z.inj_add).
    replace (length newData) with (Z.to_nat (Z.of_nat (length newData))) by lia.
    rewrite -Z2Nat.inj_add.
    {
      rewrite Z2Nat.inj_iff.
      {
        rewrite Z2Nat.id.
        {
          rewrite wrap_small; first word.
          split.
          {
            apply Z.add_nonneg_nonneg; word_cleanup; naive_solver.
          }
          {
            rewrite Nat2Z.id.
            rewrite -HnewDataSafe.
            replace (Z.of_nat (uint.nat (length newData))) with (uint.Z (length newData)); last first.
            { rewrite u64_Z_through_nat. done. }
            destruct (bool_decide (uint.Z (length (predurableC ++ membufC)) + (uint.Z (length newData)) < 2 ^ 64))%Z eqn:Hnov.
            { apply bool_decide_eq_true in Hnov. done. }
            {
              apply bool_decide_eq_false in Hnov.
              word.
            }
          }
        }
        naive_solver.
      }
      {
        word_cleanup.
        unfold word.wrap.
        by apply Z_mod_lt.
      }
      {
        word_cleanup.
        apply Z.add_nonneg_nonneg; word_cleanup; naive_solver.
      }
    }
    { naive_solver. }
    { lia. }
  }

  iAssert (|={⊤}=> (P (γ.(initdata) ++ predurableC) -∗ fmlist_lb γ.(durabledata) (γ.(initdata) ++ predurableC ++ membufC')
                   ={⊤∖↑aofN}=∗ P (γ.(initdata) ++ predurableC ++ membufC')
                          ∗ (own γ.(len) (●MN{#1/2} (length predurableC))
                             ={⊤}=∗ own γ.(len)
                                      (●MN{#1/2} (length (predurableC ++ membufC'))))
  ) ∗ (aof_length_lb γ (W64 (length (predurableC ++ membufC'))) ={⊤}=∗ ▷ Q ∗ aof_durable_lb γ (γ.(initdata) ++ predurableC ++ membufC')))%I with "[Hmembuf_fupd Hfupd Htoks]" as "HH".
  {
    (* allocate invariant to escrow Q *)
    iMod (own_alloc (Excl ())) as "HQtok".
    { done. }
    iDestruct "HQtok" as (γtok) "Htok".
    iMod (own_alloc (Excl ())) as "HQexcl".
    { done. }
    iDestruct "HQexcl" as (γq) "HQexcl".
    iDestruct (big_sepS_elem_of_acc _ _ (W64 (length (predurableC ++ membufC'))) with "Htoks") as "[Hlen_tok Hlen_toks_rest]".
    { set_solver. }
    iDestruct "Hlen_tok" as "[Hlen_tok|%Hbad]"; last first.
    {
      exfalso.
      rewrite Hsafesize' in Hbad.
      rewrite app_length in Hbad.
      rewrite app_length in Hbad.
      rewrite app_length in Hbad.
      word.
    }
    iMod (inv_alloc aofN1 _ (own γtok (Excl ()) ∗ aof_length_lb γ (W64 (length (predurableC ++ membufC'))) ∨ (W64 (length (predurableC ++ membufC')) ⤳[γ.(len_toks)] ()) ∨ (Q ∗ aof_durable_lb γ (γ.(initdata) ++ predurableC ++ membufC')) ∗ own γq (Excl ())) with "[Hlen_tok]") as "#HQinv".
    {
      iRight. iLeft.
      iFrame.
    }
    iSplitR "Htok"; last first.
    {
      iModIntro.
      iIntros "Haof_lb".
      iInv "HQinv" as "Hq" "Hqclose".
      iDestruct "Hq" as "[>[Htok2 _]|Hq]".
      { iDestruct (own_valid_2 with "Htok Htok2") as %Hbad. contradiction. }
      iDestruct "Hq" as "[>Hlentok|Hq]".
      {
        iInv "Haof_len_inv" as ">Ha" "Haclose".
        unfold aof_len_invariant.
        iDestruct "Ha" as (l) "[Hlen Ha]".
        iDestruct (own_valid_2 with "Hlen Haof_lb") as %Hineq.
        apply mono_nat_both_dfrac_valid in Hineq as [_ Hineq].
        iDestruct (big_sepS_elem_of_acc _ _ (W64 (length (predurableC ++ membufC'))) with "Ha") as "[Ha Harest]".
        { set_solver. }
        iDestruct "Ha" as "[Hlentok2|%Hbad]"; last first.
        { exfalso. lia. }
        iDestruct (ghost_map_points_to_valid_2 with "Hlentok Hlentok2") as %[Hbad _].
        exfalso.
        rewrite dfrac_op_own in Hbad.
        done.
      }
      iMod ("Hqclose" with "[Htok Haof_lb]").
      { iLeft. iNext. iFrame. }
      iDestruct "Hq" as "[[$ >$] _]".
      by iModIntro.
    }

    iModIntro.
    iIntros "Hctx #Hdur_lb".
    iMod ("Hmembuf_fupd" with "Hctx [Hdur_lb]") as "[Hctx Hmembuf_fupd]".
    {
      iApply (fmlist_lb_mono with "Hdur_lb").
      repeat rewrite app_assoc.
      apply prefix_app_r.
      done.
    }
    rewrite -app_assoc.
    iMod ("Hfupd" with "Hctx") as "[$ HQ]".
    iModIntro.

    (* length stuff *)
    iIntros "Hlen".
    iInv "HQinv" as "Hq" "Hqclose".
    iDestruct "Hq" as "[[_ >Hlb]|Hq]".
    {
      iDestruct (own_valid_2 with "Hlen Hlb") as %Hbad.
      exfalso.
      apply mono_nat_both_dfrac_valid in Hbad as [_ Hbad].
      rewrite Hsafesize' in Hbad.
      rewrite app_length in Hbad.
      rewrite app_length in Hbad.
      lia.
    }
    iDestruct "Hq" as "[>Hlen_tok|[_ >HQexcl2]]"; last first.
    { iDestruct (own_valid_2 with "HQexcl HQexcl2") as %Hbad. contradiction. }

    iDestruct ("Hlen_toks_rest" with "[$Hlen_tok]") as "Hlen_toks".
    iMod ("Hqclose" with "[HQexcl HQ]") as "_".
    { iRight; iRight; iFrame. iFrame "∗#". }

    iMod ("Hmembuf_fupd" with "Hlen") as "Hlen".

    (* Use tokens to update mono_nat counter *)
    iInv "Haof_len_inv" as ">Ha" "Haclose".
    iDestruct "Ha" as (len) "[Hlen2 Ha]".
    iDestruct (own_valid_2 with "Hlen Hlen2") as %Hleneq.
    apply mono_nat_auth_dfrac_op_valid in Hleneq as [_ <-].
    iCombine "Hlen Hlen2" as "Hlen".
    iMod (own_update _ _ (mono_nat_auth _ (length (predurableC ++ membufC'))) with "Hlen") as "Hlen".
    {
      apply mono_nat_update.
      repeat rewrite app_length.
      lia.
    }
    iDestruct "Hlen" as "[Hlen Hlen2]".

    iMod ("Haclose" with "[Ha Hlen_toks Hlen2]") as "_".
    {
      iNext. iExists _. rewrite -Hsafesize'.
      iFrame.
      iApply (big_sepS_impl with "[Ha Hlen_toks]").
      { iApply big_sepS_sep. iFrame. }

      iModIntro.
      iIntros (x ?) "Hx".
      destruct (bool_decide (uint.nat (length (predurableC ++ membufC')) < uint.nat x)) as [|] eqn:Hineq.
      {
        apply bool_decide_eq_true in Hineq.
        iRight.
        iPureIntro.
        word.
      }
      {
        apply bool_decide_eq_false in Hineq.
        iLeft.
        iDestruct "Hx" as "[[$|%Hbad] [$|%Hineq2]]".
        exfalso.
        word.
      }
    }
    iFrame.
    by iModIntro.
  }

  iMod "HH" as "[Hmembuf_fupd HfupdQ]".

  wp_loadField.
  wp_apply (release_spec with "[-HΦ Haof_log HfupdQ Htok]").
  {
    iFrame "Hmu_inv Hlocked Hcrash_wand".
    iNext.
    repeat iExists _.
    rewrite -app_assoc.
    iFrame "∗#".
    replace (word.add (length (predurableC ++ membufC)) (length newData)) with
        (W64 (length (predurableC ++ membufC'))); last first.
    {
      repeat rewrite app_length.
      rewrite -word.ring_morph_add.
      word_cleanup.
      repeat (rewrite Nat2Z.inj_add).
      rewrite Z.add_assoc.
      done.
    }
    iFrame.
    done.
  }
  wp_pures.
  iApply "HΦ".
  iFrame.
  iModIntro.
  iIntros "#Hlb".
  rewrite -app_assoc.
  iMod ("HfupdQ" with "[Hlb]") as "$"; last by iModIntro.
  replace (W64 (length (predurableC ++ membufC'))) with
      (word.add (length (predurableC ++ membufC)) (length newData)).
  { iFrame "#". }

  repeat rewrite app_length.
  repeat (rewrite Nat2Z.inj_add).
  rewrite Z.add_assoc.
  rewrite -word.ring_morph_add.
  unfold W64.
  done.
Qed.

Lemma wp_AppendOnlyFile__WaitAppend aof_ptr γ (l:u64) fname P Pcrash :
is_aof aof_ptr γ fname P Pcrash -∗
  {{{
       True
  }}}
    AppendOnlyFile__WaitAppend #aof_ptr #l
  {{{
       RET #(); aof_length_lb γ l
  }}}.
Proof.
  iIntros "#Haof" (Φ) "!# _ HΦ".
  wp_lam.
  wp_pures.
  iNamed "Haof".
  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hlocked Haof_own]".
  wp_pures.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (cond_ptr) "Hcond".
  wp_pures.
  iNamed "Haof_own".

  (* determine condvar *)
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_loadField.
  wp_apply (wp_If_join with "[Hcond HoldDurableCond HdurableCond]").
  {
    iSplit.
    {
      iIntros.
      wp_loadField.
      wp_store.
      iModIntro.
      iSplitR; first done.
      iAssert (∃ (cond:loc), cond_ptr ↦[ptrT] #cond ∗ is_cond cond mu_ptr)%I with "[Hcond]" as "Hcond".
      { iExists _; iFrame "∗#". }
      iNamedAccu.
    }
    {
      iIntros.
      wp_loadField.
      wp_store. iModIntro.
      iSplitR; first done.
      by iFrame.
    }
  }
  iNamed 1.
  iDestruct "Hcond" as (?) "[Hcond #His_cond]".
  wp_pures.

  iAssert (aof_mu_invariant aof_ptr mu_ptr γ fname P Pcrash) with "[-Hlocked HΦ Hcond]" as "Haof_own".
  { repeat iExists _; iFrame "∗#%". }
  iClear "Haof_len_inv Hctx_inv Hcrash_wand Hdurlen_lb HoldDurCond HdurCond".

  wp_apply (wp_forBreak_cond' with "[-]").
  {
    iNamedAccu.
  }
  iModIntro.
  iNamed 1.

  wp_pures.
  iNamed "Haof_own".
  wp_loadField.
  wp_pures.
  wp_if_destruct.
  {
    wp_pures.
    wp_load.
    wp_apply (wp_condWait with "[- HΦ Hcond]").
    {
      iFrame "His_cond Hmu_inv HdurableCond". by iFrame "∗#".
    }
    iIntros "[Hlocked Haof_own]".
    wp_pures.
    iLeft.
    iFrame.
    done.
  }
  iSpecialize ("HΦ" with "[Hdurlen_lb]").
  {
    assert (uint.nat l ≤ uint.nat durlen0) as Hineq.
    {
      word.
    }
    unfold aof_length_lb.
    replace (uint.nat durlen0)%nat with ((uint.nat durlen0) `max` uint.nat l)%nat by word.
    rewrite mono_nat_lb_op.
    iDestruct "Hdurlen_lb" as "[_ $]".
  }
  iRight.
  iSplitL ""; first done.
  iModIntro.
  wp_pures.

  wp_loadField.
  wp_apply (release_spec with "[- HΦ]").
  {
    by iFrame "Hmu_inv HdurableCond ∗#".
  }
  wp_pures.
  iApply "HΦ".
Qed.

Lemma wp_AppendOnlyFile__Close aof_ptr γ P Pcrash fname data :
is_aof aof_ptr γ fname P Pcrash -∗
  {{{
       aof_log_own γ data
  }}}
    AppendOnlyFile__Close #aof_ptr
  {{{
       RET #(); crash_borrow (fname f↦ data ∗ P data) (|C={⊤}=> ∃ data', fname f↦ data' ∗ ▷ Pcrash data')
  }}}.
Proof.
  iIntros "#Haof" (Φ) "!# Haof_log HΦ".
  wp_lam.
  wp_pures.
  iNamed "Haof".
  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hlocked Haof_own]".
  wp_pures.
  iNamed "Haof_own".
  iNamed "Hclose".
  wp_storeField.
  wp_loadField.
  wp_apply (wp_condSignal).
  { iFrame "#". }
  wp_pures.

  iDestruct "Haof_log" as "[Haof_log [Hreq_tok Htok]]".
  iMod (fmlist_freeze with "Haof_log") as "#Hexpected".

  iAssert (aof_mu_invariant aof_ptr mu_ptr γ fname P Pcrash) with "[-Htok HΦ Hlocked]" as "Haof_own".
  {
    iFrame "HdurableCond HoldDurableCond Hclosed HcloseRequested".
    iFrame "∗#".
    destruct isClosed; iEval simpl;
    iDestruct "Hclose" as "(_ & _ & Hclose)"; by iFrame.
  }

  wp_forBreak_cond.

  iClear "Hdurlen_lb Hcrash_wand HdurCond".
  iNamed "Haof_own".
  iNamed "Hclose".
  wp_loadField.
  wp_if_destruct.
  { (* aof not closed yet, keep looping *)
    wp_pures.
    wp_loadField.
    wp_apply (wp_condWait with "[-Htok HΦ]").
    {
      iFrame "Hmu_inv HdurableCond HoldDurableCond Hclosed HcloseRequested".
      by iFrame "∗#".
    }
    iIntros "[Hlocked Haof_own]".
    wp_pures.
    iLeft.
    iSplitR; first done.
    iModIntro.
    iFrame.
  }
  (* aof closed *)
  iRight.
  iModIntro.
  iSplitR; first done.
  iDestruct "Hclose" as "[HcloseRest [Hreq #H]]".
  iNamed "H".

  wp_pure1_credit "Hlc".
  iApply fupd_wp.
  iInv "HfileEscrow" as "Hi" "Hiclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iDestruct "Hi" as (?) "[[Hf #Hdata]|Hbad]"; last first.
  {
    iDestruct (ghost_var_valid_2 with "Htok Hbad") as %Hbad.
    exfalso. naive_solver.
  }
  iMod ("Hiclose" with "[$Htok]").
  { done. }
  iModIntro.

  iDestruct (fmlist_agree_1 with "Hexpected Hdata") as %->.

  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hf]").
  {
    iFrame "Hmu_inv HdurableCond ∗#%".
    by simpl.
  }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

Lemma accessP aof_ptr fname γ P Pcrash data durablePrefix :
  is_aof aof_ptr γ fname P Pcrash -∗
  aof_durable_lb γ durablePrefix -∗
  aof_log_own γ data -∗
  (|NC={⊤,⊤∖↑aofN}=> ∃ durableData, ⌜prefix durableData data⌝ ∗
                           ⌜prefix durablePrefix durableData⌝ ∗
                           ▷ P durableData ∗ (▷ P durableData -∗ |NC={⊤∖↑aofN,⊤}=> aof_log_own γ data)
  )
  .
Proof.
  iIntros "#Hinv #Hlb Hlog".
  iNamed "Hinv".

  iInv "Hctx_inv" as "Hctx" "Hctx_close".
  iDestruct "Hctx" as "[[>Hbad _]|Hctx]".
  {
    rewrite ncfupd_eq.
    unfold ncfupd_def.
    iIntros (?) "Hnc".
    iDestruct (NC_C with "Hnc Hbad") as %Hbad.
    by exfalso.
  }
  iDestruct "Hctx" as (?) "Hctx".
  iDestruct "Hctx" as "[[>Hbad [_ >Hbad']]|Hctx]".
  {
    iDestruct "Hlog" as "[Hlog [Hlog' Hreq]]".
    iDestruct (ghost_var_valid_2 with "[$] [$]") as %Hbad.
    exfalso.
    naive_solver.
  }
  iDestruct "Hctx" as "(>Hlb1 & >Hl & >Hcurdata2 & Hctx)".
  iDestruct "Hlog" as "(Hl'&?)".
  iDestruct (fmlist_agree_2 with "Hl' [$]") as %Hpref.
  rewrite ncfupd_eq.
  unfold ncfupd_def.
  iIntros (q) "HNC".
  iApply (fupd_mask_weaken (⊤ ∖ ↑aofN)).
  { solve_ndisj. }
  iIntros "Hclo".
  iModIntro. iFrame "HNC".
  iExists _. iFrame.
  iSplit; auto.
  iDestruct (fmlist_agree_2 with "Hl Hlb") as %Hprefix.
  iSplit.
  { iPureIntro.
    destruct Hprefix as [??].
    destruct Hpref as [??].
    eexists _.
    rewrite H0.
    repeat rewrite -app_assoc.
    done.
  }
  iIntros "HP". iIntros (?) "HNC".
  iMod "Hclo".
  iMod ("Hctx_close" with "[-HNC]"); last by eauto.
  iRight. iExists _. iNext. iFrame.
  iRight. iFrame.
Qed.

Lemma accessP_weak aof_ptr fname γ P Pcrash data :
  is_aof aof_ptr γ fname P Pcrash -∗
  aof_log_own γ data -∗
  (|NC={⊤,⊤∖↑aofN}=> ∃ durableData, ⌜prefix durableData data⌝ ∗
                           ▷ P durableData ∗ (▷ P durableData -∗ |NC={⊤∖↑aofN,⊤}=> aof_log_own γ data)
  )
  .
Proof.
  iIntros "#Hinv Hlog".
  iNamed "Hinv".

  iInv "Hctx_inv" as "Hctx" "Hctx_close".
  iDestruct "Hctx" as "[[>Hbad _]|Hctx]".
  {
    rewrite ncfupd_eq.
    unfold ncfupd_def.
    iIntros (?) "Hnc".
    iDestruct (NC_C with "Hnc Hbad") as %Hbad.
    by exfalso.
  }
  iDestruct "Hctx" as (?) "Hctx".
  iDestruct "Hctx" as "[[>Hbad [_ >Hbad']]|Hctx]".
  {
    iDestruct "Hlog" as "[Hlog [Hlog' Hreq]]".
    iDestruct (ghost_var_valid_2 with "[$] [$]") as %Hbad.
    exfalso.
    naive_solver.
  }
  iDestruct "Hctx" as "(>Hlb1 & >Hl & >Hcurdata2 & Hctx)".
  iDestruct "Hlog" as "(Hl'&?)".
  iDestruct (fmlist_agree_2 with "Hl' [$]") as %Hpref.
  rewrite ncfupd_eq.
  unfold ncfupd_def.
  iIntros (q) "HNC".
  iApply (fupd_mask_weaken (⊤ ∖ ↑aofN)).
  { solve_ndisj. }
  iIntros "Hclo".
  iModIntro. iFrame "HNC".
  iExists _. iFrame.
  iSplit; auto.
  iIntros "HP". iIntros (?) "HNC".
  iMod "Hclo".
  iMod ("Hctx_close" with "[-HNC]"); last by eauto.
  iRight. iExists _. iNext. iFrame.
  iRight. iFrame.
Qed.

End aof_proof.
