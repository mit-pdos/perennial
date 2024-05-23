From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import asyncfile.
From Perennial.algebra Require Import map.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang Require Import crash_borrow.

Record af_names := mk_af_names {
  index_gn : gname ;
  index_escrow_gn : gname ;
  predur_data : gname ;
  predur_index : gname ;
  dur_index: gname ;
  vol_data : gname ;
  close_req_tok: gname ;
  close_tok: gname ;
}.

Class asyncfileG Σ :=
  AsyncFileG {
    map_inG :> mapG Σ u64 ();
    data_inG :> ghost_varG Σ (list u8);
    tok_inG :> ghost_varG Σ ();
    idx_ing :> ghost_varG Σ u64;
    stagedG :> stagedG Σ ; (* for crash borrows? *)
  }.

Definition asyncfileΣ :=
  #[mapΣ u64 () ; ghost_varΣ (list u8); ghost_varΣ (); ghost_varΣ u64 ;
    stagedΣ].
Global Instance subG_asyncfileΣ {Σ} : subG (asyncfileΣ) Σ → (asyncfileG Σ).
Proof. solve_inG. Qed.

Section asyncfile_proof.

Context `{!heapGS Σ}.
Context `{!asyncfileG Σ}.
Implicit Types (P: list u8 → iProp Σ).

(* Plan: have a per-index escrow token to reclaim the Q resources.
   The mutex invariant owns all the unused index tokens.
   When closed, ownership of P and the file is put into escrow,
   with the token owned by the Close() thread.
   In order for the durableIndex
 *)

Definition own_write_token γ (idx:u64) : iProp Σ :=
  idx ⤳[γ.(index_gn)] ().

Definition is_write_witness γ (idx:u64) : iProp Σ :=
  idx ⤳[γ.(index_gn)]□ ().

Definition own_escrow_token γ (idx:u64) : iProp Σ :=
  idx ⤳[γ.(index_escrow_gn)] ().

Definition own_vol_data γ (data:list u8) : iProp Σ :=
  ghost_var γ.(vol_data) (1/2) data.

Definition own_predurable_data γ (data:list u8) : iProp Σ :=
  ghost_var γ.(predur_data) (1/2) data.

Definition own_predurable_index γ (idx:u64) : iProp Σ :=
  ghost_var γ.(predur_index) (1/2) idx.

Definition own_durable_index γ (idx:u64) : iProp Σ :=
  ghost_var γ.(dur_index) (1/2) idx.

Definition own_close_req_token γ : iProp Σ :=
  ghost_var γ.(close_tok) 1 ().

Definition own_close_token γ : iProp Σ :=
  ghost_var γ.(close_tok) 1 ().

(* invariant for resources for a single write *)
Definition is_write_inv N γ idx Q : iProp Σ :=
  inv N (
        own_write_token γ idx ∨
        is_write_witness γ idx ∗
        (Q ∨ own_escrow_token γ idx)
      )
.

Definition own_unused γ (idx:u64): iProp Σ :=
  [∗ set] i ∈ fin_to_set u64,
                 if decide (uint.nat idx < uint.nat i)%nat then
                   own_write_token γ i ∗ own_escrow_token γ i
                 else
                   True
.

Definition is_witnesses γ (durableIndex: u64) : iProp Σ :=
  □ ([∗ set] x ∈ fin_to_set u64,
                 if decide (uint.nat x <= uint.nat durableIndex)%nat then
                   is_write_witness γ x
                 else
                   True)
.

(* XXX: mpaxos doesn't use Close() *)

Definition own_AsyncFile_ghost N γ P fname data idx durableIndex (closeRequested closed:bool) : iProp Σ :=
  ∃ durdata predurIdx,
  "Hunused" ∷ own_unused γ idx ∗
  "HvolData" ∷ own_vol_data γ data ∗
  "HpreData" ∷ own_predurable_data γ durdata ∗
  "HpreIdx" ∷ own_predurable_index γ predurIdx ∗
  "HdurIdx" ∷ own_durable_index γ durableIndex ∗
  "Hbuf_upd" ∷ (P durdata ∗ is_witnesses γ predurIdx ={⊤}=∗ P data ∗ is_witnesses γ idx) ∗
  "#Hwits" ∷ is_witnesses γ durableIndex ∗
  "HcloseReq" ∷ (if (closeRequested || closed) then own_close_req_token γ else True) ∗
  "#Hclose" ∷ □ (if closed then
                inv N (
                      crash_borrow (P data ∗ fname f↦ data) (∃ d, P d ∗ fname f↦ d) ∨ own_close_token γ)
              else
                True)
.

Definition own_AsyncFile_internal f N γ P mu : iProp Σ :=
  ∃ data_sl fname (data:list u8) (idx durableIndex : u64) (indexCond durableIndexCond closedCond : loc)
    (closed closeRequested : bool) ,
  "#Hfilename" ∷ readonly (f ↦[AsyncFile :: "filename"] #(str fname)) ∗
  "Hdata_sl" ∷ f ↦[AsyncFile :: "data"] (slice_val data_sl) ∗
  "#Hdata" ∷ readonly (own_slice_small data_sl byteT (DfracOwn 1) data) ∗
  "Hindex" ∷ f ↦[AsyncFile :: "index"] #idx ∗
  "HdurableIndex" ∷ f ↦[AsyncFile :: "durableIndex"] #durableIndex ∗
  "HindexCond" ∷ f ↦[AsyncFile :: "indexCond"] #indexCond ∗
  "HdurableIndexCond" ∷ f ↦[AsyncFile :: "durableIndexCond"] #durableIndexCond ∗

  "HcloseRequested" ∷ f ↦[AsyncFile :: "closeRequested"] #closeRequested ∗
  "Hclosed" ∷ f ↦[AsyncFile :: "closed"] #closed ∗
  "HclosedCond" ∷ f ↦[AsyncFile :: "closedCond"] #closedCond ∗

  "#HindexCond_is" ∷ is_cond indexCond mu ∗
  "#HdurableIndexCond_is" ∷ is_cond durableIndexCond mu ∗

  "Hghost" ∷ own_AsyncFile_ghost N γ P fname data idx durableIndex closeRequested closed ∗
  "%HnoClose" ∷  ⌜ closeRequested = false ⌝ (* TODO: don't want to prove close()
  right now because it's unused. *)
.


Definition is_AsyncFile (N:namespace) (f:loc) γ P : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (f ↦[AsyncFile :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock N mu (own_AsyncFile_internal f N γ P mu)
.

Definition own_AsyncFile (N:namespace) (f:loc) γ (P: list u8 → iProp Σ) (data:list u8) : iProp Σ :=
  "#His" ∷ is_AsyncFile N f γ P ∗
  "Hvol_data" ∷ own_vol_data γ data ∗
  "Hnotclosed" ∷ own_close_req_token γ
.

Lemma get_write_witness i N γ fname data P idx durableIndex closeRequested closed :
  uint.nat i <= uint.nat durableIndex →
  own_AsyncFile_ghost N γ P fname data idx durableIndex closeRequested closed -∗
  is_write_witness γ i.
Proof.
  intros ?.
  iIntros "Hghost".
  iNamed "Hghost".
  iDestruct (big_sepS_elem_of_acc_impl i with "Hwits") as "[HH _]".
  { set_solver. }
  rewrite decide_True; last word.
  iFrame "#".
Qed.

Lemma wait_step N γ Q idx :
  is_write_inv N γ idx Q -∗
  own_escrow_token γ idx -∗
  is_write_witness γ idx ={⊤}=∗
  ▷ Q.
Proof.
  iIntros "#Hinv Htok #Hwit".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as "[>Hbad | Hi]".
  {
    iDestruct (ghost_map_points_to_valid_2 with "Hbad Hwit") as %[Hbad _].
    by exfalso.
  }
  iDestruct "Hi" as "[_ [HQ|>Hbad]]".
  2:{
    iDestruct (ghost_map_points_to_valid_2 with "Hbad Htok") as %[Hbad _].
    by exfalso.
  }
  iFrame.
  iMod ("Hclose" with "[-]"); last done.
  iNext. iRight. iFrame "#". iRight. iFrame.
Qed.

Lemma wp_AsyncFile__wait N f γ P Q (i:u64) :
  {{{
        "#His" ∷ is_AsyncFile N f γ P ∗
        "#Hinv" ∷ is_write_inv N γ i Q ∗
        "Htok" ∷ own_escrow_token γ i

  }}}
    AsyncFile__wait #f #i
  {{{
        RET #(); Q
  }}}
.
Proof.
  iIntros (Φ) "H HΦ".
  wp_lam.
  wp_pures.
  iNamed "H".
  iNamed "His".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  wp_pures.

  wp_forBreak_cond.
  iNamed "Hown".
  wp_loadField.
  wp_pures.
  wp_if_destruct.
  { (* case: wait *)
    wp_pures. wp_loadField.
    wp_apply (wp_condWait with "[-Htok HΦ]").
    {
      iFrame "HdurableIndexCond_is HmuInv Hlocked".
      repeat iExists _; iFrame "∗#%".
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iLeft.
    iSplitR; first done.
    iModIntro. iFrame.
  }
  { (* case: i is durable *)
    iModIntro.
    iRight. iSplitR; first done.
    wp_pures.
    wp_loadField.
    iDestruct (get_write_witness i with "[$]") as "#Hwit".
    { word. }
    wp_apply (release_spec with "[-Htok HΦ]").
    {
      iFrame "HmuInv Hlocked".
      repeat iExists _; iFrame "∗#%".
    }
    iMod (wait_step with "[$] [$] [$]") as "HQ".
    wp_pures.
    iModIntro. iApply "HΦ". iFrame.
  }
Qed.

Lemma write_step N γ fname somedata olddata data P Q idx durableIndex closeRequested closed :
  uint.nat (word.add idx 1) = (uint.nat idx + 1)%nat →
  own_close_req_token γ -∗
  own_vol_data γ olddata -∗
  own_AsyncFile_ghost N γ P fname somedata idx durableIndex closeRequested closed -∗
  (P olddata ={⊤}=∗ P data ∗ Q) ={⊤}=∗
  own_close_req_token γ ∗
  own_vol_data γ data ∗
  own_AsyncFile_ghost N γ P fname data (word.add idx 1) durableIndex closeRequested closed ∗
  own_escrow_token γ (word.add idx 1) ∗
  is_write_inv N γ (word.add idx 1) Q
.
Proof.
  intros ?.
  iIntros "Hnotclosed Hdata Hghost Hupd".
  iNamed "Hghost".
  destruct closed.
  {
    rewrite (orb_true_r) /=.
    iCombine "HcloseReq Hnotclosed" gives %[Hbad _].
    by exfalso.
  }
  iFrame "Hnotclosed".
  iDestruct (big_sepS_elem_of_acc_impl (word.add idx 1) with "Hunused") as "[HH Hunused]".
  { set_solver. }
  destruct (decide _).
  2:{ exfalso. word. }
  iDestruct "HH" as "[Htok $]".
  iMod (inv_alloc with "[Htok]") as "#Hinv"; last iFrame "Hinv".
  { iFrame. }
  iCombine "Hdata HvolData" gives %[_ Heq]. subst.
  iMod (ghost_var_update_2 with "Hdata HvolData") as "[Hvoldata Hvoldata2]".
  { apply Qp.half_half. }
  iModIntro.
  iFrame.
  repeat iExists _.
  iFrame "∗#".
  iSplitL "Hunused".
  {
    iApply "Hunused".
    {
      iModIntro. iIntros.
      destruct (decide _).
      { destruct (decide _); done. }
      rewrite decide_False; first done.
      { word. }
    }
    { rewrite decide_False; first done. word. }
  }
  iIntros "HP".
  iClear "Hwits".
  iMod ("Hbuf_upd" with "HP") as "[HP #Hwits]".
  iMod ("Hupd" with "HP") as "[HP HQ]".
  iFrame.
  iClear "Hclose".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as "[>Htok | [>#Hwit  _]]".
  2:{
    iMod ("Hclose" with "[-]").
    { iNext. iRight. iFrame "∗#". }
    iModIntro.
    iModIntro.
    iDestruct (big_sepS_impl with "Hwits []") as "$".
    iModIntro. iIntros.
    destruct (decide _).
    { destruct (decide _); done. }
    destruct (decide _).
    {
      replace (x) with (word.add idx 1).
      { iFrame "#". }
      {
        assert (uint.Z (word.add idx 1) = uint.Z x) by word.
        apply int_Z_inj in H1; first done.
        apply _. (* FIXME: why is this typeclass left? *)
      }
    }
    { done. }
  }
  iMod (ghost_map_points_to_persist with "Htok") as "#Hwit".
  iMod ("Hclose" with "[HQ]").
  { iRight. iFrame "∗#". }
  iModIntro.
  iDestruct (big_sepS_impl with "Hwits []") as "$".
  iModIntro. iIntros.
  destruct (decide _).
  { destruct (decide _); done. }
  destruct (decide _).
  {
    replace (x) with (word.add idx 1).
    { iFrame "#". }
    {
      assert (uint.Z (word.add idx 1) = uint.Z x) by word.
      apply int_Z_inj in H1; first done.
      apply _. (* FIXME: why is this typeclass left? *)
    }
  }
  { done. }
Qed.

Lemma wp_AsyncFile__Write N f γ P olddata data_sl data Q:
  {{{
        "Hf" ∷ own_AsyncFile N f γ P olddata ∗
        "Hdata_in" ∷ own_slice_small data_sl byteT (DfracOwn 1) data ∗
        "Hupd" ∷ (P olddata ={⊤}=∗ P data ∗ Q)
  }}}
    asyncfile.AsyncFile__Write #f (slice_val data_sl)
  {{{
        (w:val), RET w;
        own_AsyncFile N f γ P data ∗
        WP w #() {{ _, Q }}
  }}}
.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_lam.
  wp_pures.
  iNamed "Hf".
  iAssert (_) with "His" as "His2".
  iNamed "His2".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_storeField.
  wp_loadField.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hno_overflow).
  wp_storeField.
  wp_loadField.
  wp_pures.
  wp_loadField.
  iMod (write_step with "[$] [$] [$] Hupd") as "H".
  { word. }
  iDestruct "H" as "(Hnoclose & Hdat & Hghost & Hesc & #Hinv)".
  iMod (readonly_alloc_1 with "Hdata_in") as "#Hdata_in".
  wp_apply wp_condSignal.
  { iFrame "#". }
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hnoclose Hdat Hesc]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    repeat iExists _.
    iFrame "∗#%".
  }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame "∗#".
  wp_pures.
  wp_apply (wp_AsyncFile__wait N _ _ P with "[-]").
  { iFrame "∗#". }
  iIntros "HQ".
  wp_pures.
  by iFrame.
Qed.

Lemma get_upd N γ fname newdata data predurIdx P idx durableIndex closeRequested closed :
  own_predurable_data γ data -∗
  own_predurable_index γ predurIdx -∗
  own_durable_index γ predurIdx -∗
  own_AsyncFile_ghost N γ P fname newdata idx durableIndex closeRequested closed ==∗
  own_predurable_data γ newdata ∗
  own_predurable_index γ idx ∗
  own_durable_index γ predurIdx ∗
  (P data ={⊤}=∗ P newdata ∗ is_witnesses γ idx) ∗
  own_AsyncFile_ghost N γ P fname newdata idx durableIndex closeRequested closed
.
Proof.
  iIntros "HpreData2 HpreIdx2 HdurIdx2 Hghost".
  iNamed "Hghost".
  iCombine "HpreData HpreData2" gives %[_ H]; subst.
  iCombine "HpreIdx HpreIdx2" gives %[_ H]; subst.
  iCombine "HdurIdx HdurIdx2" gives %[_ H]; subst.
  iMod (ghost_var_update_2 with "HpreData HpreData2") as "[HpreData $]".
  { apply Qp.half_half. }
  iMod (ghost_var_update_2 with "HpreIdx HpreIdx2") as "[HpreIdx $]".
  { apply Qp.half_half. }
  iModIntro.
  iFrame.
  iSplitL "Hbuf_upd".
  {
    iIntros "HP". iMod ("Hbuf_upd" with "[HP]").
    { iFrame "∗#". }
    by iFrame.
  }
  iFrame "∗#".
  iIntros "$ !#". done.
Qed.

Lemma update_durable_index N γ fname data predurIdx P idx durableIndex newDurableIndex closeRequested closed :
  own_durable_index γ predurIdx -∗
  is_witnesses γ newDurableIndex -∗
  own_AsyncFile_ghost N γ P fname data idx durableIndex closeRequested closed ==∗
  own_durable_index γ newDurableIndex ∗
  own_AsyncFile_ghost N γ P fname data idx newDurableIndex closeRequested closed
.
Proof.
  iIntros "HdurIdx2 #HnewWits Hghost".
  iNamed "Hghost".
  iMod (ghost_var_update_2 with "HdurIdx HdurIdx2") as "[HdurIdx $]".
  { apply Qp.half_half. }
  iModIntro.
  iClear "Hwits".
  repeat iExists _.
  iFrame "∗#".
Qed.

Lemma wp_AsyncFile__flushThread fname N f γ P data :
  {{{
        "His" ∷ is_AsyncFile N f γ P ∗
        "HpreData" ∷ own_predurable_data γ data ∗
        "HpreIdx" ∷ own_predurable_index γ 0 ∗
        "HdurIdx" ∷ own_durable_index γ 0 ∗
        "#Hfilename_in" ∷ readonly (f ↦[AsyncFile :: "filename"] #(str fname)) ∗
        "Hfile" ∷ crash_borrow (P data ∗ fname f↦ data) (∃ d, P d ∗ fname f↦ d)
  }}}
    asyncfile.AsyncFile__flushThread #f
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_lam.
  iNamed "His".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iAssert (∃ curdata curidx,
              "HpreData" ∷ own_predurable_data γ curdata ∗
              "HpreIdx" ∷ own_predurable_index γ curidx ∗
              "HdurIdx" ∷ own_durable_index γ curidx ∗
              "Hfile" ∷ crash_borrow (P curdata ∗ fname f↦ curdata) (∃ d : list u8, P d ∗ fname f↦d)
          )%I with "[HpreData HpreIdx HdurIdx Hfile]" as "HH".
  { repeat iExists _; iFrame. }
  wp_forBreak.
  wp_pures.

  clear data.
  iNamed "Hown".
  subst.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_if_destruct.
  {
    wp_loadField.
    wp_apply (wp_condWait with "[-HΦ HH]").
    {
      iFrame "HindexCond_is HmuInv Hlocked".
      repeat iExists _; iFrame "∗#%".
      done.
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iLeft.
    iSplitR; first done.
    iModIntro. iFrame.
  }
  (* case: have something to write *)
  wp_loadField. wp_loadField.
  wp_loadField.

  iNamed "HH".
  iMod (get_upd with "[$] [$] [$] [$]") as "H".
  iDestruct "H" as "(HpreData & HpreIdx & HdurIdx & Hupd & Hghost)".
  wp_apply (release_spec with "[-HΦ HpreData HpreIdx HdurIdx Hupd Hfile]").
  {
    iFrame "HmuInv Hlocked".
    repeat iExists _; iFrame "∗#%".
    done.
  }
  wp_pures.
  wp_loadField.

  iMod (readonly_load with "Hfilename_in") as (?) "H1".
  iMod (readonly_load with "Hfilename") as (?) "H2".
  iDestruct (struct_field_pointsto_agree with "H1 H2") as %?.
  iClear "H1 H2".
  injection H as <-.
  wp_bind (FileWrite _ _).
  iApply (wpc_wp _ _ _ _ True).
  wpc_apply (wpc_crash_borrow_open_modify with "Hfile").
  { done. }
  iSplit; first done.
  iIntros "[HP Hf]".
  iMod (readonly_load with "Hdata") as (?) "Hdata2".
  iApply wpc_cfupd.
  iApply wpc_ncfupd.
  wpc_apply (wpc_FileWrite with "[Hf Hdata2]").
  { iFrame. }
  iSplit.
  { (* case: crash in the middle *)
    iIntros "[Hold|Hnew]".
    { iModIntro. iSplitR; first done.
      iExists _; iFrame. }
    {
      iMod ("Hupd" with "HP") as "[HP _]".
      iModIntro.
      iSplitR; first done. iExists _; iFrame.
    }
  }
  iNext.
  iIntros "[Hf _]".
  iExists _.
  iMod ("Hupd" with "HP") as "[HP #HnewWits]".
  iSplitL "HP Hf".
  { iModIntro. iAccu. }
  iModIntro.
  iSplitR.
  { iModIntro. iIntros "H". iExists _; iFrame. }
  iIntros "Hfile".
  iSplit; first done.

  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iClear "Hfilename Hdata HindexCond_is HdurableIndexCond_is".
  iNamed "Hown".
  wp_pures.
  wp_storeField.
  wp_loadField.
  wp_apply wp_condBroadcast.
  { iFrame "#". }
  wp_pures.
  iMod (update_durable_index with "[$] HnewWits [$]") as "[HdurIdx Hghost]".
  iModIntro.
  iLeft.
  iSplitR; first done.
  iFrame "HΦ Hlocked".
  iSplitR "HpreData HpreIdx HdurIdx Hfile".
  {
    repeat iExists _.
    iFrame "∗#%".
  }
  repeat iExists _; iFrame.
Qed.

Lemma alloc_ghost N P data fname :
  ⊢ |==>
    ∃ γ,
      "Hghost" ∷ own_AsyncFile_ghost N γ P fname data 0 0 false false ∗

      "HpreData" ∷ own_predurable_data γ data ∗
      "HpreIdx" ∷ own_predurable_index γ 0 ∗
      "HdurIdx" ∷ own_durable_index γ 0 ∗

      "Hvol_data" ∷ own_vol_data γ data ∗
      "Hnotclosed" ∷ own_close_req_token γ
.
Proof.
  (*
  index_gn : gname ;
  index_escrow_gn : gname ;
  predur_data : gname ;
  predur_index : gname ;
  dur_index: gname ;
  vol_data : gname ; *)
  iMod (ghost_map_alloc_fin ()) as (index) "Hunused1".
  iMod (ghost_map_alloc_fin ()) as (escrow) "Hunused2".
  iMod (ghost_var_alloc data) as (preData) "[HpreData HpreData2]".
  iMod (ghost_var_alloc data) as (volData) "[HvolData HvolData2]".
  iMod (ghost_var_alloc (W64 0)) as (preIdx) "[HpreIdx HpreIdx2]".
  iMod (ghost_var_alloc (W64 0)) as (durIdx) "[HdurIdx HdurIdx2]".
  iMod (ghost_var_alloc ()) as (closeReq) "HcloseReq".
  iMod (ghost_var_alloc ()) as (closed) "Hclosed".
  iDestruct (big_sepS_delete _ _ (W64 0) with "Hunused1") as "[Hwit1 Hunused1]".
  { set_solver. }
  iMod (ghost_map_points_to_persist with "Hwit1") as "#Hwit1".
  iModIntro.
  iExists (mk_af_names index escrow preData preIdx durIdx volData closeReq closed).
  iFrame.
  repeat iExists _.
  rewrite /is_witnesses /own_unused /is_write_witness /own_predurable_index /own_write_token
          /own_escrow_token /own_durable_index /own_predurable_data /own_vol_data /own_close_req_token /=.
  iFrame.
  iDestruct (big_sepS_delete _ _ (W64 0) with "Hunused2") as "[_ Hunused2]".
  { set_solver. }
  iSplitL "Hunused1 Hunused2".
  {
    iDestruct (big_sepS_sep with "[$Hunused1 $Hunused2]") as "Hunused".
    iApply (big_sepS_delete _ _ (W64 0)).
    { set_solver. }
    iSplitR.
    { setoid_rewrite decide_False; first done; word. }
    iApply (big_sepS_impl with "Hunused").
    iModIntro. iIntros.
    destruct (decide _); done.
  }
  simpl.
  iSplitR.
  { iIntros "$ !# //". }
  iSplitR; last done.
  iModIntro.
  iApply big_sepS_forall.
  { intros. destruct (decide _); apply _. }
  iIntros.
  replace (uint.nat 0) with (0%nat) by word.
  destruct (decide _).
  { replace (x) with (W64 0).
    { done. }
    { word. }
  }
  done.
Qed.

Lemma wp_MakeAsyncFile fname N P data :
  {{{
        "Hfile" ∷ crash_borrow (P data ∗ fname f↦ data) (∃ d, P d ∗ fname f↦ d)
  }}}
    asyncfile.MakeAsyncFile #(str fname)
  {{{
        γ sl f, RET (slice_val sl, #f); readonly (own_slice_small sl byteT (DfracOwn 1) data) ∗
                                        own_AsyncFile N f γ P data
  }}}
.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_lam.
  wp_apply wp_allocStruct.
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
  iIntros (f) "Hf".
  iDestruct (struct_fields_split with "Hf") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply wp_new_free_lock.
  iIntros (?) "HmuInv".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "[$]").
  iIntros (?) "[HmuInv #?]".
  wp_storeField.


  wp_loadField.
  wp_apply (wp_newCond' with "[$]").
  iIntros (?) "[HmuInv #?]".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "[$]").
  iIntros (?) "[HmuInv #?]".
  wp_storeField.
  wp_storeField.

  wp_bind (FileRead _).
  iApply (wpc_wp _ _ _ _ True).
  wpc_apply (wpc_crash_borrow_open with "Hfile").
  { done. }
  iSplit; first done.
  iIntros "[HP Hf]".
  wpc_apply (wpc_FileRead with "[$]").
  iSplit.
  { (* case: crash in the middle *)
    iIntros "Hf". iSplitR; first done. iExists _; iFrame.
  }
  iNext.
  iIntros (?) "[Hf Hdata]".
  iFrame.
  iIntros "Hfile".
  iSplitR; first done.

  repeat wp_storeField.

  wp_loadField.
  wp_pures.
  iMod (readonly_alloc_1 with "mu") as "#Hmu".
  iMod (readonly_alloc_1 with "filename") as "#Hfilename".
  iDestruct (own_slice_to_small with "Hdata") as "Hdata".
  iMod (readonly_alloc_1 with "Hdata") as "#Hdata".
  iMod (alloc_ghost N P data fname) as (γ) "H".
  iNamed "H".
  iAssert (|={⊤}=> is_AsyncFile N f γ P)%I with "[-HpreIdx HpreData HdurIdx Hfile HΦ Hvol_data Hnotclosed]" as ">#His".
  {
    repeat iExists _; iFrame "#".
    iMod (alloc_lock with "[$] [-]") as "$"; last done.
    iNext. repeat iExists _; iFrame "Hghost ∗ #".
    done.
  }

  wp_apply (wp_fork with "[HpreIdx HpreData HdurIdx Hfile]").
  {
    iNext.
    wp_apply (wp_AsyncFile__flushThread with "[-]").
    {
      (* iFrame performance slow: iFrame "His".*)
      iSplitR.
      { iExact "His". }
      iFrame "∗#".
    }
    done.
  }
  wp_pures.
  iApply "HΦ". iModIntro.
  iFrame "∗#".
Qed.

End asyncfile_proof.
