From Perennial.program_proof.tpcc Require Import tpcc_prelude.

Section program.
Context `{!heapGS Σ}.

(**
 * Application-specific point-tos are defined in terms of [txnmaps_ptsto] and [dbmaps_ptsto].
 *)

(* Resources and operations on the Customer table. *)
Lemma struct_ty_customer_unfold :
  struct.t Customer = (uint64T * (uint64T * (slice.T byteT * unitT)))%ht.
Proof. reflexivity. Qed.

Definition customer_record_to_val (cid : u64) (cwid : u64) (clast : Slice.t) :=
  (#cid, (#cwid, (to_val clast, #())))%V.

Definition customer_tbl_txnpt (τ : gname) (tplid : u64) (data : u64 * u64 * (list u8)) :=
  txnmaps_ptsto τ (W64 0) (u64_le tplid) (Value (u64_le data.1.1 ++ u64_le data.1.2 ++ data.2)).

Definition customer_tbl_dbpt (τ : gname) (tplid : u64) q (data : u64 * u64 * (list u8)) :=
  dbmaps_ptsto τ (W64 0) (u64_le tplid) q (Value (u64_le data.1.1 ++ u64_le data.1.2 ++ data.2)).

Theorem wp_readCustomer txn tplid cid cwid clast tid view γ τ :
  {{{ own_txn txn tid view γ τ ∗ customer_tbl_txnpt τ tplid (cid, cwid, clast) }}}
    readCustomer #txn #tplid
  {{{ (clastS : Slice.t), RET (customer_record_to_val cid cwid clastS);
      own_txn txn tid view γ τ ∗ customer_tbl_txnpt τ tplid (cid, cwid, clast) ∗
      own_slice_small clastS byteT 1 clast
  }}}.
Proof.
  iIntros (Φ) "[Htxn Hpt] HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* var k = make([]byte, 0, 8)                              *)
  (* k = marshal.WriteInt(k, tplid)                          *)
  (***********************************************************)
  wp_apply wp_NewSliceWithCap; first word.
  iIntros (kPtr) "HkS".
  replace (uint.nat 0) with 0%nat by word. rewrite replicate_0.
  wp_apply wp_ref_to; first by auto.
  iIntros (kRef) "HkRef".
  wp_load.
  wp_apply (wp_WriteInt with "HkS").
  iIntros (kS) "HkS /=".
  wp_store.
  
  (***********************************************************)
  (* v, _ := txn.Read(MAPID_CUSTOMER_TBL, k)                 *)
  (***********************************************************)
  wp_load.
  wp_apply (wp_txn__Read with "[$Htxn $Hpt $HkS]").
  set v' := (u64_le _ ++ u64_le _ ++ _).
  iIntros (vS found v) "(Htxn & Hpt & HkS & HvS & %Hret)".
  destruct found eqn:Efound; last by inversion Hret.
  wp_pures.

  (***********************************************************)
  (* cid, v1 := marshal.ReadInt(v)                           *)
  (* cwid, clast := marshal.ReadInt(v1)                      *)
  (* return Customer {                                       *)
  (*     C_ID : cid,                                         *)
  (*     C_W_ID : cwid,                                      *)
  (*     C_LAST : clast,                                     *)
  (* }                                                       *)
  (***********************************************************)
  simpl in Hret. inversion Hret. subst v'.
  iDestruct (own_slice_to_small with "HvS") as "HvS".
  wp_apply (wp_ReadInt with "HvS").
  iIntros (vS') "HvS'".
  wp_pures.
  wp_apply (wp_ReadInt with "HvS'").
  iIntros (vS'') "HvS''".
  wp_pures.
  iApply "HΦ".
  by iFrame.
Qed.

(* Resources and operations on the Customer index. *)
Definition customer_idx_txnpt (τ : gname) (cid cwid : u64) (tplid : u64) :=
  txnmaps_ptsto τ (W64 1) ((u64_le cid) ++ (u64_le cwid)) (Value (u64_le tplid)).

Definition customer_idx_txnpt_nil (τ : gname) (cid cwid : u64) :=
  txnmaps_ptsto τ (W64 1) ((u64_le cid) ++ (u64_le cwid)) Nil.

Definition customer_idx_dbpt (τ : gname) (cid cwid : u64) q (tplid : u64) :=
  dbmaps_ptsto τ (W64 1) ((u64_le cid) ++ (u64_le cwid)) q (Value (u64_le tplid)).

Definition customer_idx_dbpt_nil (τ : gname) (cid cwid : u64) q :=
  dbmaps_ptsto τ (W64 1) ((u64_le cid) ++ (u64_le cwid)) q Nil.

Theorem wp_findCusomterByCID txn cid cwid tid tplid view γ τ :
  {{{ own_txn txn tid view γ τ ∗ customer_idx_txnpt τ cid cwid tplid }}}
    findCustomerByCID #txn #cid #cwid
  {{{ RET (#tplid, #true);
      own_txn txn tid view γ τ ∗ customer_idx_txnpt τ cid cwid tplid
  }}}.
Proof.
  iIntros (Φ) "[Htxn Hpt] HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* var k = make([]byte, 0, 16)                             *)
  (* k = marshal.WriteInt(k, cid)                            *)
  (* k = marshal.WriteInt(k, cwid)                           *)
  (***********************************************************)
  wp_apply wp_NewSliceWithCap; first word.
  iIntros (kPtr) "HkS".
  replace (uint.nat 0) with 0%nat by word. rewrite replicate_0.
  wp_apply wp_ref_to; first by auto.
  iIntros (kRef) "HkRef".
  wp_load.
  wp_apply (wp_WriteInt with "HkS").
  iIntros (kS) "HkS /=".
  wp_store.
  wp_load.
  wp_apply (wp_WriteInt with "HkS").
  iIntros (kS') "HkS'".
  wp_store.

  (***********************************************************)
  (* v, ok := txn.Read(MAPID_CUSTOMER_IDX_CID, k)            *)
  (* if !ok {                                                *)
  (*     return 0, false                                     *)
  (* }                                                       *)
  (***********************************************************)
  wp_load.
  wp_apply (wp_txn__Read with "[$Htxn $Hpt $HkS']").
  set k := (u64_le _ ++ u64_le _).
  iIntros (vS found v) "(Htxn & Hpt & HkS & HvS & %Hret)".
  destruct found eqn:Efound; last by inversion Hret.
  wp_pures.

  (***********************************************************)
  (* tplid, _ := marshal.ReadInt(v)                          *)
  (* return tplid, true                                      *)
  (***********************************************************)
  simpl in Hret. inversion Hret. subst v.
  iDestruct (own_slice_to_small with "HvS") as "HvS".
  wp_apply (wp_ReadInt with "HvS").
  iIntros (vS') "HvS'".
  wp_pures.
  iApply "HΦ".
  by iFrame.
Qed.

Theorem wp_findCusomterByCID_nil txn cid cwid tid view γ τ :
  {{{ own_txn txn tid view γ τ ∗ customer_idx_txnpt_nil τ cid cwid }}}
    findCustomerByCID #txn #cid #cwid
  {{{ RET (#(W64 0), #false);
      own_txn txn tid view γ τ ∗ customer_idx_txnpt_nil τ cid cwid
  }}}.
Proof.
  iIntros (Φ) "[Htxn Hpt] HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* var k = make([]byte, 0, 16)                             *)
  (* k = marshal.WriteInt(k, cid)                            *)
  (* k = marshal.WriteInt(k, cwid)                           *)
  (***********************************************************)
  wp_apply wp_NewSliceWithCap; first word.
  iIntros (kPtr) "HkS".
  replace (uint.nat 0) with 0%nat by word. rewrite replicate_0.
  wp_apply wp_ref_to; first by auto.
  iIntros (kRef) "HkRef".
  wp_load.
  wp_apply (wp_WriteInt with "HkS").
  iIntros (kS) "HkS /=".
  wp_store.
  wp_load.
  wp_apply (wp_WriteInt with "HkS").
  iIntros (kS') "HkS'".
  wp_store.

  (***********************************************************)
  (* v, ok := txn.Read(MAPID_CUSTOMER_IDX_CID, k)            *)
  (* if !ok {                                                *)
  (*     return 0, false                                     *)
  (* }                                                       *)
  (***********************************************************)
  wp_load.
  wp_apply (wp_txn__Read with "[$Htxn $Hpt $HkS']").
  set k := (u64_le _ ++ u64_le _).
  iIntros (vS found v) "(Htxn & Hpt & HkS & HvS & %Hret)".
  destruct found eqn:Efound; first inversion Hret.
  wp_pures.
  iApply "HΦ".
  by iFrame.
Qed.

(* Query the Customer table with its index. *)
Theorem wp_SelectCusomterByCID txn cid cwid (cref : loc) clast tid tplid view γ τ :
  {{{ own_txn txn tid view γ τ ∗ 
      customer_idx_txnpt τ cid cwid tplid ∗ customer_tbl_txnpt τ tplid (cid, cwid, clast) ∗
      (∃ cid' cwid' clast', cref ↦[structTy Customer] (customer_record_to_val cid' cwid' clast'))
  }}}
    SelectCustomerByCID #txn #cid #cwid #cref
  {{{ (clastS : Slice.t), RET #true;
      own_txn txn tid view γ τ ∗
      customer_idx_txnpt τ cid cwid tplid ∗ customer_tbl_txnpt τ tplid (cid, cwid, clast) ∗
      cref ↦[Customer :: "C_ID"] #cid ∗ cref ↦[Customer :: "C_W_ID"] #cwid ∗
      cref ↦[Customer :: "C_LAST"] (to_val clastS) ∗ own_slice_small clastS byteT 1 clast
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hidxpt & Htblpt & Hc) HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* tplid, found := findCustomerByCID(txn, cid, cwid)       *)
  (* if !found {                                             *)
  (*     return false                                        *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_findCusomterByCID with "[$Htxn $Hidxpt]").
  iIntros "[Htxn Hidxpt]".
  wp_pures.
  
  (***********************************************************)
  (* customer := readCustomer(txn, tplid)                    *)
  (* *cref = customer                                        *)
  (***********************************************************)
  wp_apply (wp_readCustomer with "[$Htxn $Htblpt]").
  iIntros (clastS) "(Htxn & Htblpt & HclastS)".
  wp_pures.
  iDestruct "Hc" as (cid' cwid' clast') "Hc".
  iDestruct (struct_fields_split with "Hc") as "Hc".
  iNamed "Hc".
  do 3 wp_storeField.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iApply "HΦ".
  by iFrame.
Qed.

Theorem wp_SelectCusomterByCID_nil txn cid cwid (cref : loc) tid view γ τ :
  {{{ own_txn txn tid view γ τ ∗ customer_idx_txnpt_nil τ cid cwid }}}
    SelectCustomerByCID #txn #cid #cwid #cref
  {{{ RET #false;
      own_txn txn tid view γ τ ∗ customer_idx_txnpt_nil τ cid cwid
  }}}.
Proof.
  iIntros (Φ) "[Htxn Hidxpt] HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* tplid, found := findCustomerByCID(txn, cid, cwid)       *)
  (* if !found {                                             *)
  (*     return false                                        *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_findCusomterByCID_nil with "[$Htxn $Hidxpt]").
  iIntros "[Htxn Hidxpt]".
  wp_pures.
  iApply "HΦ".
  by iFrame.
Qed.

(* Functions below are not the interface of this file. *)

(**
 * TODO: We're forcing full ownership of [customer_idx_dbpt] and
 * [customer_tbl_dbpt].
 * Maybe should define [dbmaps_ptstos_wr], which requires full
 * ownership of each individual [dbmaps_ptsto]s, and
 * [dbmaps_ptstos_rd] which requires only partial ownership, and prove
 * [wp_txn__DoTxn_readonly] that uses the latter one.
 *)
Theorem wp_TxnSelectCusomterByCID txn cid cwid γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (tplid : u64) (clast : list u8),
        customer_idx_dbpt γ cid cwid 1 tplid ∗ customer_tbl_dbpt γ tplid 1 (cid, cwid, clast)
    >>>
    TxnSelectCustomerByCID #txn #cid #cwid @ ⊤
    <<< customer_idx_dbpt γ cid cwid 1 tplid ∗ customer_tbl_dbpt γ tplid 1 (cid, cwid, clast) >>>
    {{{ (clastS : Slice.t), RET customer_record_to_val cid cwid clastS;
        own_txn_uninit txn γ ∗ own_slice_small clastS byteT 1 clast
    }}}.
Proof.
  iIntros (Φ) "!> Htxn HAU".
  wp_rec. wp_pures.

  (***********************************************************)
  (* var c Customer                                          *)
  (* body := func(txn *Txn) bool {                           *)
  (*     return selectCustomerByCID(txn, cid, cwid, &c)      *)
  (* }                                                       *)
  (* t.DoTxn(body)                                           *)
  (* return c                                                *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first by auto.
  iIntros (cRef) "HcRef".
  wp_pures.
  set m : u64 -> list u8 -> dbmaps :=
    λ (tplid : u64) (clast : list u8),
      {[ (W64 1, u64_le cid ++ u64_le cwid) := Value (u64_le tplid) ]} ∪
      {[ (W64 0, u64_le tplid) := Value (u64_le cid ++ u64_le cwid ++ clast) ]}.


  (* Q: Can we automate converting [big_sepM] to individual points-tos? *)
  iAssert (∀ (tplid : u64) (clast : list u8) (τ : gname),
             txnmaps_ptstos τ (m tplid clast) ∗-∗
             (customer_idx_txnpt τ cid cwid tplid ∗ customer_tbl_txnpt τ tplid (cid, cwid, clast))
          )%I as "Htxnptsiff".
  { iIntros (tplid clast τ).
    subst m. unfold txnmaps_ptstos.
    rewrite big_sepM_union; last first.
    { apply map_disjoint_dom_2. set_solver. }
    do 2 rewrite big_sepM_singleton.
    iSplit; by iIntros.
  }
  iAssert (∀ (tplid : u64) (clast : list u8),
             dbmaps_ptstos γ 1 (m tplid clast) ∗-∗
             (customer_idx_dbpt γ cid cwid 1 tplid ∗ customer_tbl_dbpt γ tplid 1 (cid, cwid, clast))
          )%I as "Hdbptsiff".
  { iIntros (tplid clast).
    subst m. unfold dbmaps_ptstos.
    rewrite big_sepM_union; last first.
    { apply map_disjoint_dom_2. set_solver. }
    do 2 rewrite big_sepM_singleton.
    iSplit; by iIntros.
  }


  set P := λ (r : dbmaps), ∃ (tplid : u64) (clast : list u8), r = m tplid clast.
  set Ri := (∃ cid cwid clastS,
                cRef ↦[structTy Customer] (customer_record_to_val cid cwid clastS))%I.
  set Ra := (λ (_ : dbmaps), Ri)%I.
  set Rc := (λ (r : dbmaps), ∃ (tplid : u64) (clast : list u8) (clastS : Slice.t),
                ⌜r !! (W64 1, u64_le cid ++ u64_le cwid) = Some (Value (u64_le tplid)) ∧
                 r !! (W64 0, u64_le tplid) = Some (Value (u64_le cid ++ u64_le cwid ++ clast))⌝ ∗
                cRef ↦[structTy Customer] (customer_record_to_val cid cwid clastS) ∗
                own_slice_small clastS byteT 1 clast)%I.
  wp_apply (wp_txn__DoTxn_readonly _ _ P Rc Rc with "[$Htxn HcRef]").
  { (* Transaction body. *)
    clear Φ. unfold spec_body.
    iIntros (tid r τ Φ) "(Htxn & %HP & Htxnpts) HΦ".
    unfold P in HP. destruct HP as (tplid & clast & Hr).
    rewrite {2} Hr.
    iDestruct ("Htxnptsiff" with "Htxnpts") as "[Hidxpt Htblpt]".
    wp_pures.
    wp_apply (wp_SelectCusomterByCID with "[$Htxn Hidxpt Htblpt HcRef]").
    { iFrame. rewrite /zero_val /=.
      iExists (W64 0), (W64 0), Slice.nil.
      iFrame.
    }
    iIntros (clastS) "(Htxn & Hidxpt & Htblpt & Hcid & Hcwid & Hclast & HclastS)".
    iApply "HΦ".
    iFrame.
    iSplitL "Hidxpt Htblpt".
    { rewrite Hr.
      (* Q: WOW how does IPM pick the correct direction? *)
      iDestruct ("Htxnptsiff" with "[$Hidxpt $Htblpt]") as "Htxnpts".
      iFrame.
    }
    iAssert (Rc r)%I with "[-]" as "H".
    { subst Rc.
      simpl.
      (* Q: How to stop simplifying [u64_le]? *)
      iExists tplid, clast, clastS.
      rewrite -struct_ty_customer_unfold struct_fields_split.
      iFrame.
      iPureIntro.
      subst m. simpl in Hr.
      split; last done.
      split; subst r.
      { apply lookup_union_Some_l. by rewrite lookup_singleton_eq. }
      { apply lookup_union_Some_r; last by rewrite lookup_singleton_eq.
        apply map_disjoint_dom_2.
        set_solver.
      }
    }
    iFrame.
  }
  iMod "HAU" as (tplid clast) "[[Hidxpt Htblpt] HAU]".
  iModIntro.
  iExists (m tplid clast).
  iDestruct ("Hdbptsiff" with "[$Hidxpt $Htblpt]") as "Hdbpts".
  iFrame.
  iSplit.
  { subst P. eauto. }
  iIntros "Hdbpts".
  iDestruct ("Hdbptsiff" with "Hdbpts") as "[Hidxpt Htblpt]".
  iMod ("HAU" with "[$Hidxpt $Htblpt]") as "HΦ".
  iIntros "!>" (ok) "[Htxn HR]".
  wp_pures.
  iAssert (Rc (m tplid clast))%I with "[HR]" as "HR".
  { destruct ok; done. }
  subst Rc.
  iDestruct "HR" as (tplid' clast' clastS) "([%Hlookup1 %Hlookup2] & HcRef & HclastS)".
  wp_load.
  wp_pures.
  iApply "HΦ".
  replace clast' with clast; last first.
  { subst m.
    rewrite (lookup_union_Some_l _ _ _ (Value (u64_le tplid))) in Hlookup1; last first.
    { by rewrite lookup_singleton_eq. }
    do 2 apply Some_inj in Hlookup1.
    rewrite -Hlookup1 in Hlookup2.
    rewrite (lookup_union_Some_r _ _ _ (Value (u64_le cid ++ u64_le cwid ++ clast))) in Hlookup2; last first.
    { by rewrite lookup_singleton_eq. }
    { apply map_disjoint_dom_2. set_solver. }
    do 2 apply Some_inj in Hlookup2.
    set_solver.
  }
  by iFrame.
Qed.

Theorem wp_TxnSelectCusomterByCID_nil txn cid cwid γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    (* [x] is just a placeholder for missing notations. *)
    <<< ∀∀ (x : u64), customer_idx_dbpt_nil γ cid cwid 1 >>>
    TxnSelectCustomerByCID #txn #cid #cwid @ ⊤
    <<< customer_idx_dbpt_nil γ cid cwid 1 >>>
    {{{ RET (zero_val (struct.t Customer)); own_txn_uninit txn γ }}}.
Proof.
  iIntros (Φ) "!> Htxn HAU".
  wp_rec. wp_pures.

  (***********************************************************)
  (* var c Customer                                          *)
  (* body := func(txn *Txn) bool {                           *)
  (*     return selectCustomerByCID(txn, cid, cwid, &c)      *)
  (* }                                                       *)
  (* t.DoTxn(body)                                           *)
  (* return c                                                *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first by auto.
  iIntros (cRef) "HcRef".
  wp_pures.
  set m : dbmaps := {[ (W64 1, u64_le cid ++ u64_le cwid) := Nil ]}.
  set P := λ (r : dbmaps), r = m.
  wp_apply (wp_txn__DoTxn_xres_readonly _ _ P with "[$Htxn]").
  { (* Transaction body. *)
    clear Φ. unfold spec_body.
    iIntros (tid r τ Φ) "(Htxn & %HP & Hidxpt) HΦ".
    unfold P in HP.
    wp_pures.
    unfold txnmaps_ptstos.
    rewrite {2}HP big_sepM_singleton.
    wp_apply (wp_SelectCusomterByCID_nil with "[$Htxn $Hidxpt]").
    iIntros "[Htxn Hidxpt]".
    iApply "HΦ".
    rewrite HP big_sepM_singleton.
    iFrame.
  }
  iMod "HAU".
  iModIntro.
  iDestruct "HAU" as (_) "[Hidxpt HAU]".
  iExists m.
  subst m.
  rewrite /dbmaps_ptstos big_sepM_singleton.
  iFrame.
  iSplit; first done.
  iIntros "Hidxpt".
  iMod ("HAU" with "Hidxpt") as "HΦ".
  iIntros "!>" (ok) "Htxn".
  wp_load.
  iApply "HΦ".
  by iFrame.
Qed.

(**
 * We need these invariants to use [SelectCusomterByCID]:
 * 1. Index and table well-formedness
 * 2. Index referential integrity 
 *
 * Invoking [SelectCusomterByCID]:
 * 1. Open the invariant.
 * 2. By index well-formedness, we can do a case analysis:
 * 3-1. No such index entry -> use [wp_TxnSelectCusomterByCID_nil].
 * 3-2. Index entry exists -> by referential integrity and table well-formedness -> use [wp_TxnSelectCusomterByCID].
 *)

End program.
