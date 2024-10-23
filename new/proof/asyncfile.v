From New.proof Require Import grove_prelude.
From New.code.github_com.mit_pdos.gokv Require Import asyncfile.
From Perennial.algebra Require Import map.
From New.proof Require Import std.
From New.proof Require Import sync own_crash.

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
    #[global] map_inG :: mapG Σ u64 ();
    #[global] data_inG :: ghost_varG Σ (list u8);
    #[global] tok_inG :: ghost_varG Σ ();
    #[global] idx_ing :: ghost_varG Σ u64;
    #[global] syncG :: syncG Σ ;
    #[global] simpleCrashG :: simpleCrashG Σ ;
  }.

Definition asyncfileΣ :=
  #[mapΣ u64 () ; ghost_varΣ (list u8); ghost_varΣ (); ghost_varΣ u64 ;
    simpleCrashΣ; syncΣ].
Global Instance subG_asyncfileΣ {Σ} : subG (asyncfileΣ) Σ → (asyncfileG Σ).
Proof. solve_inG. Qed.

Module AsyncFile.
  Record t :=
    mk {
        mu : loc;
        data : slice.t;
        filename :  string;
        index : w64;
        indexCond : loc;
        durableIndex : w64;
        durableIndexCond : loc;

        closeRequested : bool;
        closed : bool;
        closedCond : loc;
      }.
End AsyncFile.

Instance into_val_AsyncFile : IntoVal AsyncFile.t :=
  {|
    to_val_def :=
      λ v, struct.val AsyncFile [
               "mu" ::= #v.(AsyncFile.mu);
               "data" ::= #v.(AsyncFile.data);
               "filename" ::= #v.(AsyncFile.filename);
               "index" ::= #v.(AsyncFile.index);
               "indexCond" ::= #v.(AsyncFile.indexCond);
               "durableIndex" ::= #v.(AsyncFile.durableIndex);
               "durableIndexCond" ::= #v.(AsyncFile.durableIndexCond);
               "closeRequested" ::= #v.(AsyncFile.closeRequested);
               "closed" ::= #v.(AsyncFile.closed);
               "closedCond" ::= #v.(AsyncFile.closedCond)
             ]%V
  |}.

Program Instance into_val_typed_AsyncFile : IntoValTyped AsyncFile.t AsyncFile :=
{| default_val := AsyncFile.mk (default_val _) (default_val _) (default_val _) (default_val _)
                    (default_val _) (default_val _) (default_val _) (default_val _)
                    (default_val _) (default_val _)
|}.
Next Obligation. rewrite to_val_unseal /=. solve_has_go_type. Qed.

Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 solve_to_val_inj_step () : unit :=
  match! goal with
  | [ |- ∀ (_:_), _ ] => intros
  | [ |- Inj eq eq _ ] => intros [] [] Heq
  end.
Next Obligation.
  (* FIXME: [solve_zero_val] tactic *)
  intros. rewrite zero_val_eq to_val_unseal /= struct.val_unseal /=.
  rewrite zero_val_eq /= !to_val_unseal //.
Qed.
Next Obligation.
  rewrite to_val_unseal.
  intros x y Heq.
  destruct x, y.
  simpl in *.
  f_equal.
  - eapply (struct_val_inj _ _ _) in Heq; last by (do 0 right; left).
    simpl in Heq. by apply to_val_inj.
  - eapply (struct_val_inj _ _ _) in Heq; last by (do 1 right; left).
    simpl in Heq. by apply to_val_inj.
  - eapply (struct_val_inj _ _ _) in Heq; last by (do 2 right; left).
    simpl in Heq. by apply to_val_inj.
  - eapply (struct_val_inj _ _ _) in Heq; last by (do 3 right; left).
    simpl in Heq. by apply to_val_inj.
  - eapply (struct_val_inj _ _ _) in Heq; last by (do 4 right; left).
    simpl in Heq. by apply to_val_inj.
  - eapply (struct_val_inj _ _ _) in Heq; last by (do 5 right; left).
    simpl in Heq. by apply to_val_inj.
  - eapply (struct_val_inj _ _ _) in Heq; last by (do 6 right; left).
    simpl in Heq. by apply to_val_inj.
  - eapply (struct_val_inj _ _ _) in Heq; last by (do 7 right; left).
    simpl in Heq. by apply to_val_inj.
  - eapply (struct_val_inj _ _ _) in Heq; last by (do 8 right; left).
    simpl in Heq. by apply to_val_inj.
  - eapply (struct_val_inj _ _ _) in Heq; last by (do 9 right; left).
    simpl in Heq. by apply to_val_inj.
Qed.
Final Obligation. solve_decision. Qed.

Program Instance iv_AsyncFile_mu `{ffi_syntax} : IntoValStructField "mu" AsyncFile AsyncFile.mu.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). Qed.

Program Instance iv_AsyncFile_data `{ffi_syntax} : IntoValStructField "data" AsyncFile AsyncFile.data.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). Qed.

Program Instance iv_AsyncFile_filename `{ffi_syntax} : IntoValStructField "filename" AsyncFile AsyncFile.filename.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). Qed.

Program Instance iv_AsyncFile_index `{ffi_syntax} : IntoValStructField "index" AsyncFile AsyncFile.index.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). Qed.

Program Instance iv_AsyncFile_indexCond `{ffi_syntax} : IntoValStructField "indexCond" AsyncFile AsyncFile.indexCond.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). Qed.

Program Instance iv_AsyncFile_durableIndex `{ffi_syntax} : IntoValStructField "durableIndex" AsyncFile AsyncFile.durableIndex.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). Qed.

Program Instance iv_AsyncFile_durableIndexCond `{ffi_syntax} : IntoValStructField "durableIndexCond" AsyncFile AsyncFile.durableIndexCond.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). Qed.

Program Instance iv_AsyncFile_closeRequested `{ffi_syntax} : IntoValStructField "closeRequested" AsyncFile AsyncFile.closeRequested.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). Qed.

Program Instance iv_AsyncFile_closed `{ffi_syntax} : IntoValStructField "closed" AsyncFile AsyncFile.closed.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). Qed.

Program Instance iv_AsyncFile_closedCond `{ffi_syntax} : IntoValStructField "closedCond" AsyncFile AsyncFile.closedCond.
Final Obligation. intros. repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). Qed.

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
  inv (N.@"inv") (
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
  "Hbuf_upd" ∷ (P durdata ∗ is_witnesses γ predurIdx ={⊤∖↑N.@"crash"}=∗ P data ∗ is_witnesses γ idx) ∗
  "#Hwits" ∷ is_witnesses γ durableIndex ∗
  "HcloseReq" ∷ (if (closeRequested || closed) then own_close_req_token γ else True) ∗
  "#Hclose" ∷ □ (if closed then
                   inv (N.@"inv") (own_crash (N.@"crash") (∃ d, P d ∗ fname f↦ d) (P data ∗ fname f↦ data) ∨ own_close_token γ)
                 else
                   True)
.

Definition own_AsyncFile_internal f N γ P lk : iProp Σ :=
  ∃ data_sl fname (data:list u8) (idx durableIndex : u64) (indexCond durableIndexCond closedCond : loc)
    (closed closeRequested : bool) ,
  "#Hfilename" ∷ f ↦s[AsyncFile :: "filename"]□ fname ∗
  "Hdata_sl" ∷ f ↦s[AsyncFile :: "data"] (data_sl) ∗
  "#Hdata" ∷ data_sl ↦*□ data ∗
  "Hindex" ∷ f ↦s[AsyncFile :: "index"] idx ∗
  "HdurableIndex" ∷ f ↦s[AsyncFile :: "durableIndex"] durableIndex ∗
  "HindexCond" ∷ f ↦s[AsyncFile :: "indexCond"] indexCond ∗
  "HdurableIndexCond" ∷ f ↦s[AsyncFile :: "durableIndexCond"] durableIndexCond ∗

  "HcloseRequested" ∷ f ↦s[AsyncFile :: "closeRequested"] closeRequested ∗
  "Hclosed" ∷ f ↦s[AsyncFile :: "closed"] closed ∗
  "HclosedCond" ∷ f ↦s[AsyncFile :: "closedCond"] closedCond ∗

  "#HindexCond_is" ∷ is_Cond indexCond lk ∗
  "#HdurableIndexCond_is" ∷ is_Cond durableIndexCond lk ∗

  "Hghost" ∷ own_AsyncFile_ghost N γ P fname data idx durableIndex closeRequested closed ∗
  "%HnoClose" ∷  ⌜ closeRequested = false ⌝ (* TODO: don't want to prove close()
  right now because it's unused. *)
.


Definition is_AsyncFile (N:namespace) (f:loc) γ P : iProp Σ :=
  ∃ (mu : loc),
  "#Hmu" ∷ f ↦s[AsyncFile :: "mu"]□ mu ∗
  "#HmuInv" ∷ is_Mutex mu (own_AsyncFile_internal f N γ P (interface.mk #mu Mutex__mset_ptr))
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
  wp_call.
  iNamed "H".
  iNamed "His".
  iDestruct (Mutex_is_Locker with "[$]") as "#Hlk".
  wp_apply wp_with_defer.
  iIntros (defer) "Hdefer". simpl subst.

  wp_alloc s_addr as "Hlocal2".
  wp_pures.
  wp_alloc index_addr as "Hlocal1".
  wp_pures.
  wp_load. wp_pures.
  wp_load. wp_pures.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown]".
  wp_pures. wp_load.
  wp_pures. wp_load.
  wp_apply wp_Mutex__Unlock'.
  iIntros (m_unlock) "#Hunlock".
  wp_pures.
  wp_load. wp_pures. wp_store.
  iMod (typed_pointsto_persist with "Hdefer") as "#?".
  wp_pures.

  wp_for.
  iNamed "Hown".
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_load.
  wp_pures.
  destruct bool_decide eqn:?.
  { (* case: wait *)
    simpl. rewrite decide_True //.
    wp_pures. wp_load. wp_pures. wp_load.
    wp_apply (wp_Cond__Wait with "[-Htok HΦ Hlocal1 Hlocal2]").
    {
      iFrame "HdurableIndexCond_is Hlk".
      iFrame "∗#%".
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iApply wp_for_post_do.
    wp_pures.
    by iFrame.
  }
  { (* case: i is durable *)
    simpl.
    rewrite decide_False; last naive_solver.
    rewrite decide_True; last naive_solver.
    rewrite bool_decide_eq_false in Heqb.
    wp_pures.
    iDestruct (get_write_witness i with "[$]") as "#Hwit".
    { word. }
    wp_load. wp_pures.
    wp_apply ("Hunlock" with "[-Htok HΦ Hlocal1 Hlocal2]").
    {
      iFrame "HmuInv Hlocked".
      repeat iExists _; iFrame "∗#%".
    }
    iMod (wait_step with "[$] [$] [$]") as "HQ".
    wp_pures. iApply "HΦ". iFrame.
  }
Qed.

Lemma write_step N γ fname somedata olddata data P Q idx durableIndex closeRequested closed :
  uint.nat (word.add idx 1) = (uint.nat idx + 1)%nat →
  own_close_req_token γ -∗
  own_vol_data γ olddata -∗
  own_AsyncFile_ghost N γ P fname somedata idx durableIndex closeRequested closed -∗
  (P olddata ={⊤∖↑N.@"crash"}=∗ P data ∗ Q) ={⊤}=∗
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
        "Hdata_in" ∷ data_sl ↦* data ∗
        "Hupd" ∷ (P olddata ={⊤∖↑N}=∗ P data ∗ Q)
  }}}
    asyncfile.AsyncFile__Write #f #data_sl
  {{{
        (w:val), RET w;
        own_AsyncFile N f γ P data ∗
        WP w #() {{ _, Q }}
  }}}
.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_call.
  iNamed "Hf".
  iAssert (_) with "His" as "His2".
  iNamed "His2".

  wp_apply wp_with_defer.
  iIntros (defer) "Hdefer". simpl subst. wp_pures.

  wp_alloc data_addr as "Hlocal1".
  wp_pures.
  wp_alloc s_addr as "Hlocal2".
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures. wp_load.
  wp_pures. wp_load.
  wp_pures.
  wp_apply wp_Mutex__Unlock'.
  iIntros (m_unlock) "Hunlock".
  wp_pures. wp_load. wp_pures. wp_store.
  wp_pures.
  wp_load. wp_pures. wp_load. wp_pures. wp_store. wp_pures. wp_load.
  wp_pures. wp_load. wp_pures.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hno_overflow).
  wp_pures. wp_load. wp_pures. wp_store.
  wp_pures.
  rewrite -!default_val_eq_zero_val.
  wp_alloc index_ptr as "Hlocal3".
  wp_pures. wp_load.
  wp_pures. wp_load.
  wp_pures. wp_store.
  wp_pures. wp_load. wp_pures. wp_load.
  iMod (write_step with "[$] [$] [$] [Hupd]") as "H".
  { word. }
  {
    rewrite fupd_mask_mono; first done.
    solve_ndisj.
  }
  iDestruct "H" as "(Hnoclose & Hdat & Hghost & Hesc & #Hinv)".
  iMod (own_slice_persist with "Hdata_in") as "#Hdata_in".
  wp_apply wp_Cond__Signal.
  { iFrame "#". }
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply ("Hunlock" with "[-HΦ Hnoclose Hdat Hesc Hlocal1 Hlocal2 Hlocal3]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    repeat iExists _.
    iFrame "∗#%".
  }
  wp_pures.
  iApply "HΦ".
  iFrame "∗#".
  wp_pures. wp_load.
  wp_pures. wp_load.
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
  (P data ={⊤∖↑N.@"crash"}=∗ P newdata ∗ is_witnesses γ idx) ∗
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

Lemma wp_AsyncFile__flushThread fname N f γ P data Φ :
  (∀ (v : val),
  {{{
        "His" ∷ is_AsyncFile N f γ P ∗
        "HpreData" ∷ own_predurable_data γ data ∗
        "HpreIdx" ∷ own_predurable_index γ 0 ∗
        "HdurIdx" ∷ own_durable_index γ 0 ∗
        "#Hfilename_in" ∷ f ↦s[AsyncFile :: "filename"]□ fname ∗
        "Hfile" ∷ own_crash (N.@"crash") (∃ d, P d ∗ fname f↦ d) (P data ∗ fname f↦ data)
  }}}
    (v #())
  {{{
        RET #(); True
  }}} -∗ Φ v) -∗
  WP asyncfile.AsyncFile__flushThread #f {{ Φ }}.
Proof.
  iIntros "Hwp".
  wp_call.
  iApply "Hwp".
  clear Φ.
  iIntros (Φ) "!# H HΦ".
  iNamed "H".
  wp_pures.
  iNamed "His".
  wp_alloc s_addr as "Hlocal1".
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iAssert (∃ curdata curidx,
              "HpreData" ∷ own_predurable_data γ curdata ∗
              "HpreIdx" ∷ own_predurable_index γ curidx ∗
              "HdurIdx" ∷ own_durable_index γ curidx ∗
              "Hfile" ∷ own_crash (N.@"crash") (∃ d : list u8, P d ∗ fname f↦d) (P curdata ∗ fname f↦ curdata)
          )%I with "[HpreData HpreIdx HdurIdx Hfile]" as "HH".
  { repeat iExists _. iFrame. }
  wp_for.
  wp_pures.
  rewrite decide_True //.
  clear data.
  iNamed "Hown".
  subst.
  wp_pures. wp_load. wp_pures. wp_load.
  wp_pures.
  wp_load. wp_pures. wp_load.
  wp_pures. wp_load. wp_pures. wp_load.
  wp_pures.
  case_bool_decide.
  {
    wp_pures. wp_load. wp_pures. wp_load.
    wp_apply (wp_Cond__Wait with "[-HΦ HH Hlocal1]").
    {
      iFrame "HindexCond_is".
      iDestruct (Mutex_is_Locker with "[$]") as "$".
      iFrame "∗#%". done.
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iApply wp_for_post_continue.
    wp_pures. by iFrame.
  }
  (* case: have something to write *)
  wp_pures.
  rewrite -!default_val_eq_zero_val.
  wp_alloc index_ptr as "Hlocal2".
  wp_pures.
  wp_load. wp_pures. wp_load. wp_pures. wp_store. wp_pures.
  wp_alloc data_ptr as "Hlocal3".
  wp_pures. wp_load. wp_pures. wp_load. wp_pures. wp_store. wp_pures.
  wp_load. wp_pures. wp_load.

  iNamed "HH".
  iMod (get_upd with "[$] [$] [$] [$]") as "H".
  iDestruct "H" as "(HpreData & HpreIdx & HdurIdx & Hupd & Hghost)".
  wp_apply (wp_Mutex__Unlock with "[-HΦ HpreData HpreIdx HdurIdx Hupd Hfile Hlocal1 Hlocal2 Hlocal3]").
  {
    iFrame "HmuInv Hlocked".
    repeat iExists _; iFrame "∗#%".
    done.
  }
  wp_pures.
  wp_load. wp_pures. wp_load. wp_pures. wp_load.
  wp_pure_lc "H1". wp_pure_lc "H2".
  iCombine "H1 H2" as "Hlc".
  wp_pures.

  iCombine "Hfilename_in Hfilename" gives %[_ [=<-]].
  wp_apply (wp_FileWrite with "[$Hdata]").
  iDestruct (own_crash_unfold with "Hfile") as "Hfile".
  rewrite /own_crash_pre /=.
  unshelve iMod ("Hfile" $! _ _ with "[$]") as "[[HP $] Hau]".
  { set_solver. }
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hmask".
  iSplit.
  2:{ (* case: crash before finishing. *)
    iIntros "Hold".
    iMod "Hmask".
    iMod ("Hau" with "[] [HP Hold]") as "Hau".
    2:{ iAccu. }
    { eauto with iFrame. }
    done.
  }
  iIntros "Hf".
  iMod "Hmask".
  iMod ("Hupd" with "HP") as "[HP #HnewWits]".
  iMod ("Hau" with "[] [HP Hf]") as "HP".
  2: iAccu.
  { eauto with iFrame. }
  iModIntro.
  iIntros "Hfile".
  wp_pures.
  wp_load. wp_pures. wp_load.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hown]".
  iClear "Hfilename Hdata HindexCond_is HdurableIndexCond_is".
  iNamed "Hown".
  wp_pures.
  wp_load. wp_pures. wp_load. wp_pures. wp_store.
  wp_pures. wp_load. wp_pures. wp_load.
  wp_apply wp_Cond__Broadcast.
  { iFrame "#". }
  iMod (update_durable_index with "[$] HnewWits [$]") as "[HdurIdx Hghost]".
  wp_pures.
  iApply wp_for_post_do.
  wp_pures.
  iFrame "HΦ Hlocked".
  iFrame "∗#%".
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
        "Hfile" ∷ own_crash (N.@"crash") (∃ d, P d ∗ fname f↦ d) (P data ∗ fname f↦ data)
  }}}
    asyncfile.MakeAsyncFile #fname
  {{{
        γ sl f, RET (#sl, #f); sl ↦*□ data ∗ own_AsyncFile N f γ P data
  }}}
.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_call.
  wp_alloc filename_addr as "Hlocal".
  iMod (typed_pointsto_persist with "Hlocal") as "#?".
  wp_pures.
  rewrite -!default_val_eq_zero_val /=.
  wp_alloc mu as "Hmu".
  wp_pures.
  wp_alloc s as "Hlocal".
  wp_pures.
  wp_load.
  wp_pure_lc "H1". wp_pure_lc "H2".
  iCombine "H1 H2" as "Hlc".
  wp_apply wp_FileRead.
  iDestruct (own_crash_unfold with "Hfile") as "Hfile".
  unshelve iMod ("Hfile" $! _ _ with "[$]") as "[[HP $] Hau]".
  { solve_ndisj. }
  iApply ncfupd_mask_intro; first solve_ndisj.
  iIntros "Hmask".
  iIntros "Hf". iMod "Hmask" as "_".
  iMod ("Hau" with "[] [HP Hf]") as "Hfile". 2: iAccu.
  { eauto with iFrame. }
  iModIntro.
  iIntros (?) "Hdata_new".
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply (wp_NewCond with "[$]").
  iIntros (?) "#?".
  wp_pures.
  wp_apply (wp_NewCond with "[$]").
  iIntros (?) "#?".
  wp_pures.
  wp_apply (wp_NewCond with "[$]").
  iIntros (?) "#?".
  wp_pures.

  (* FIXME: automatically convert struct.make into the typed thing. *)
  eassert (struct.val AsyncFile _ = #(AsyncFile.mk _ _ _ _ _ _ _ _ _ _)) as ->.
  { repeat (rewrite ?to_val_unseal ?struct.val_unseal //=). }

  wp_alloc l as "Hl".
  wp_pures.
  wp_store.
  iMod (typed_pointsto_persist with "Hlocal") as "#?".
  wp_pures.
  wp_alloc data_ptr as "Hlocal".
  wp_pures.
  wp_load. wp_pures.

  iRename "Hmu" into "Hmu_uninit".

  iDestruct (struct_fields_split with "Hl") as "Hl".
  { done. }
  { apply _. }
  rewrite /struct_fields /=.
  repeat (iDestruct "Hl" as "[H1 Hl]";
          unshelve iSpecialize ("H1" $! _ _ _ _ _ _); try tc_solve;
          iNamed "H1").
  simpl.
  wp_load.
  wp_pures. wp_store.
  iMod (typed_pointsto_persist with "Hlocal") as "#?".
  wp_pures.

  iMod (typed_pointsto_persist with "Hmu") as "#Hmu".
  iMod (typed_pointsto_persist with "Hfilename") as "#Hfilename".
  iMod (own_slice_persist with "Hdata_new") as "#Hdata_new".
  iMod (alloc_ghost N P data fname) as (γ) "H".
  iNamed "H".
  iAssert (|={⊤}=> is_AsyncFile N l γ P)%I with "[-HpreIdx HpreData HdurIdx Hfile HΦ Hvol_data Hnotclosed]" as ">#His".
  {
    iMod (init_Mutex with "[$] [-]") as "$"; last done.
    iNext. by iFrame "∗#".
  }

  wp_pures.
  wp_load.
  wp_apply wp_AsyncFile__flushThread.
  iIntros (flush) "Hwp_flush".
  wp_pures.
  wp_bind (Fork (flush #()))%E.
  iApply (wp_fork with "[HpreIdx HpreData HdurIdx Hfile Hwp_flush]").
  {
    iNext.
    wp_apply ("Hwp_flush" with "[-]").
    { iFrame "∗#". }
    wp_pures.
    done.
  }
  iNext. wp_pures. wp_load. wp_load.
  wp_pures.
  iApply "HΦ".
  iFrame "∗#".
Qed.

End asyncfile_proof.
