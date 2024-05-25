From RecordUpdate Require Import RecordSet.
From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com.mit_pdos.go_journal Require Import txn.
From Perennial.program_proof Require Import jrnl.sep_jrnl_proof.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof obj.obj_proof.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.goose_lang.lib Require Import slice.typed_slice map.impl.
From Perennial.Helpers Require Import PropRestore.
From Perennial.algebra Require Import auth_map.
From Perennial.program_logic Require Import na_crash_inv.

Section proof.
Context `{!jrnlG Σ}.
Context `{!heapGS Σ}.
Context `{!lockmapG Σ}.
Definition Njrnl := nroot .@ "jrnl".

Implicit Types γ : jrnl_names.
Implicit Types dinit : disk.
Implicit Types sz : u64.
Implicit Types objs_spec : gmap addr bufDataKind.
Implicit Types objs_dom : gset addr.
Implicit Types objs_dom_flat : gset u64.
Implicit Types mt_changed : gmap addr versioned_object.
Implicit Types mt_all : gmap addr object.
Implicit Types mt_committed : gmap addr object.
Implicit Types blkno : u64.
Implicit Types inst : nat.
Implicit Types γdurable_map : gmap nat gname.
Implicit Types locked_by_map : gmap u64 (option nat).

Definition modified := mspec.modified.
Definition committed := mspec.committed.

Definition pointsto_valid γ a obj :=
  valid_addr a ∧
  valid_off (objKind obj) a.(addrOff) ∧
  γ.(jrnl_txn_names).(txn_kinds) !! a.(addrBlock) = Some (objKind obj).

Definition twophase_pre_crash_inv_pred ex_pointsto γ a obj : iProp Σ :=
  "Hex_pointsto" ∷ ex_pointsto a obj ∗
  "Hdurable" ∷ durable_pointsto γ a obj ∗
  "%Hvalid" ∷ ⌜pointsto_valid γ a obj⌝.

Definition twophase_crash_inv_pred ex_pointsto γ a obj : iProp Σ :=
  "Hex_pointsto" ∷ ex_pointsto a obj ∗
  "Hdurable" ∷ durable_pointsto_own γ a obj ∗
  "%Hvalid" ∷ ⌜pointsto_valid γ a obj⌝.

Definition twophase_crash_inv ex_pointsto γ γ' a obj : iProp Σ :=
  crash_borrow (twophase_pre_crash_inv_pred ex_pointsto γ a obj)
    (|C={⊤}=> ∃ obj', twophase_crash_inv_pred ex_pointsto γ' a obj')%I.

Definition twophase_linv ex_pointsto γ γ' a : iProp Σ :=
  ∃ obj,
    "Htoken" ∷ modify_token γ a ∗
    "Hcrash_inv" ∷ twophase_crash_inv ex_pointsto γ γ' a obj ∗
    "%Hvalid" ∷ ⌜pointsto_valid γ a obj⌝.

Definition twophase_linv_flat ex_pointsto γ γ' flat_addr : iProp Σ :=
  ∃ a,
    "Hlinv" ∷ twophase_linv ex_pointsto γ γ' a ∗
    "%Ha" ∷ ⌜addr2flat a = flat_addr⌝.

Definition is_twophase_locks l γ γ' ex_pointsto objs_dom_flat (locks_held: gset u64) : iProp Σ :=
  ∃ (locksl: loc) (acquired_m: loc) ghs,
    "Htxn.locks" ∷ l ↦[Txn :: "locks"] #locksl ∗
    "Htxn.acquired" ∷
      l ↦[Txn :: "acquired"] #acquired_m ∗
    "Hacquired_m" ∷ own_map acquired_m (DfracOwn 1)
      (set_to_map (λ k, (k, true)) locks_held) ∗
    "Hlockeds" ∷ ([∗ set] flat_a ∈ locks_held,
      "Hlocked" ∷ Locked ghs flat_a
    ) ∗
    "#HlockMap" ∷ is_lockMap locksl ghs objs_dom_flat
      (twophase_linv_flat ex_pointsto γ γ') ∗
    "%Hlocks_in_dom" ∷ ⌜locks_held ⊆ objs_dom_flat⌝.

Lemma is_twophase_locks_get_pures l γ γ' ex_pointsto objs_dom_flat locks_held :
  "Hlocks" ∷ is_twophase_locks
    l γ γ' ex_pointsto objs_dom_flat locks_held -∗
  "%Hlocks_in_dom" ∷ ⌜locks_held ⊆ objs_dom_flat⌝.
Proof.
  iNamed 1.
  iNamed "Hlocks".
  iFrame "%".
Qed.

Definition is_twophase_jrnl l γ dinit mt_changed : iProp Σ :=
  ∃ (jrnll: loc) γtxn γdurable,
    "Htxn.jrnl" ∷ l ↦[Txn :: "buftxn"] #jrnll ∗
    "Hjrnl_mem" ∷ is_jrnl_mem
      Njrnl jrnll γ dinit γtxn γdurable ∗
    "Hjrnl_durable_frag" ∷ map_ctx
      γdurable (1/2) (committed <$> mt_changed) ∗
    "Hjrnl_maps_tos" ∷ ([∗ map] a ↦ vobj ∈ mt_changed,
      jrnl_maps_to γtxn a (modified vobj)
    ).

Definition is_twophase_raw l γ γ' dinit ex_pointsto objs_dom mt_changed : iProp Σ :=
  "Hlocks" ∷ is_twophase_locks
    l γ γ' ex_pointsto (set_map addr2flat objs_dom)
    (set_map addr2flat (dom mt_changed)) ∗
  "Hjrnl" ∷ is_twophase_jrnl l γ dinit mt_changed ∗
  "Hcrash_invs" ∷ (
    [∗ map] a ↦ vobj ∈ mt_changed,
      "Hcrash_inv" ∷ twophase_crash_inv
        ex_pointsto γ γ' a (committed vobj)
  ) ∗
  "#Htxn_cinv" ∷ txn_cinv Njrnl γ γ' ∗
  "%Hvalids" ∷ ⌜
    map_Forall
      (λ a vobj,
        pointsto_valid γ a (modified vobj)
      )
      mt_changed
  ⌝ ∗
  "%Haddrs_valid" ∷ ⌜set_Forall valid_addr objs_dom⌝.

Ltac wp_start :=
  iIntros (Φ) "Hpre HΦ";
  lazymatch goal with
  | |- context[Esnoc _ (INamed "HΦ") (▷ ?Q)%I] =>
    set (post:=Q)
  end;
  lazymatch iTypeOf "Hpre" with
  | Some (_, named _ _ ∗ _)%I => iNamed "Hpre"
  | Some (_, named _ _)%I => iNamed "Hpre"
  | _ => idtac
  end.

Lemma big_sepS_set_map `{Countable A, Countable B} (h : A → B) (s : gset A) (f : B → iProp Σ) :
  (∀ x y, x ∈ s → y ∈ s → h x = h y → x = y) →
  ([∗ set] x ∈ s, f (h x)) ⊢@{_} ([∗ set] x ∈ set_map h s, f x).
Proof.
  intros Hinj.
  induction s as [|x s ? IH] using set_ind_L.
  { by rewrite set_map_empty !big_opS_empty. }
  rewrite set_map_union_L set_map_singleton_L.
  rewrite !big_opS_union; [ | set_solver by idtac.. ]. (* FIXME regular set_solver fails *)
  rewrite !big_opS_singleton IH //.
  intros x' y' Hx_in Hy_in Heq.
  apply Hinj; set_solver.
Qed.

Lemma durable_pointsto_own_valid E γ a obj :
  ↑Njrnl ⊆ E →
  ↑invN ⊆ E →
  "#Htxn_system" ∷ is_txn_system Njrnl γ -∗
  "Hdurable_pointsto" ∷ durable_pointsto_own γ a obj
  -∗ |NC={E}=>
  "Hdurable_pointsto" ∷ durable_pointsto_own γ a obj ∗
  "%Hvalid" ∷ ⌜pointsto_valid γ a obj⌝.
Proof.
  iIntros (HNjrnl HinvN) "??".
  iNamed.
  iDestruct "Hdurable_pointsto" as "[Htoken Hdurable_pointsto]".
  iDestruct "Htoken" as (obj') "Htoken".
  iMod (
    durable_pointsto_pointsto_txn_agree with
    "Htxn_system Hdurable_pointsto Htoken"
  ) as "[<- [$ Hpointsto]]"; [assumption|assumption|solve_ndisj|].
  iNamed "Htxn_system".
  iMod (pointsto_txn_valid with "His_txn Hpointsto")
    as "[Hpointsto %Hvalid]"; first by assumption.
  iModIntro.
  iSplit; first by (iExists _; iFrame).
  iPureIntro.
  apply Hvalid.
Qed.

Lemma exchange_pointsto_valid γ γ' a obj :
  γ.(jrnl_txn_names).(txn_kinds) = γ'.(jrnl_txn_names).(txn_kinds) →
  pointsto_valid γ a obj →
  pointsto_valid γ' a obj.
Proof.
  intros Hkinds (Hvalid_addr&Hvalid_off&Hvalid_kinds).
  rewrite /pointsto_valid -Hvalid_kinds -Hkinds //=.
Qed.

Global Instance obj_inhabited: Inhabited object.
Proof. econstructor. econstructor. apply (bufBit true). Qed.

Theorem twophase_init_locks {E} ex_pointsto `{!∀ a obj, Timeless (ex_pointsto a obj)} mt γ γ' :
  ↑Njrnl ⊆ E →
  ↑invN ⊆ E →
  set_Forall valid_addr (dom mt) →
  "Hpre" ∷ ([∗ map] _ ↦ _ ∈ mt, pre_borrow) -∗
  "#Htxn_system" ∷ is_txn_system Njrnl γ -∗
  "#Htxn_cinv" ∷ txn_cinv Njrnl γ γ' -∗
  "Hpointstos" ∷ (
    [∗ map] a ↦ obj ∈ mt,
      "Hdurable_pointsto" ∷ durable_pointsto_own γ a obj ∗
      "Hex_pointsto" ∷ ex_pointsto a obj
  )
  -∗ |NC={E}=>
  "Hlinvs" ∷ (
    init_cancel ([∗ set] a ∈ set_map addr2flat (dom mt),
                 "Hlinv" ∷ twophase_linv_flat ex_pointsto γ γ' a)
                ("Hcrash" ∷
                   (|C={⊤}=> ([∗ map] a↦_ ∈ mt, ∃ (obj : object),
                                     "Hdurable_pointsto" ∷ durable_pointsto_own γ' a obj ∗
                                     "Hex_pointsto" ∷ ex_pointsto a obj ∗
                                     "%Hvalid" ∷ ⌜ pointsto_valid γ' a obj ⌝)))
  ).
Proof.
  iIntros (HNjrnl NinvN Haddrs_valid) "????".
  iNamed.
  iDestruct (big_sepM_sep with "Hpointstos")
    as "[Hdurable_pointstos Hex_pointstos]".
  iMod (
    big_sepM_mono_ncfupd _ (λ a obj,
      "Hdurable_pointsto" ∷ durable_pointsto_own γ a obj ∗
      "%Hkind" ∷ ⌜pointsto_valid γ a obj⌝
    )%I mt True%I with "[] [Hdurable_pointstos]"
  ) as "[_ Hmono]".
  2: {
    iSplit; first by trivial.
    iFrame.
  }
  {
    iIntros (a obj) "!> %Hacc (_&Hdurable_pointsto)".
    iMod (durable_pointsto_own_valid with "Htxn_system Hdurable_pointsto")
      as "Himpl".
    1-2: eassumption.
    iModIntro.
    iSplit; first by trivial.
    iFrame.
  }
  iDestruct (big_sepM_sep with "Hmono") as "[Hdurable_pointstos %Hkinds]".
  iDestruct (big_sepM_sep with "Hdurable_pointstos")
    as "[Htokens Hdurable_pointstos]".
  iApply fupd_ncfupd.
  iDestruct (
    big_sepM_crash_borrow_init_cancel
    (λ a _,
      |C={⊤}=> (∃ obj', twophase_crash_inv_pred ex_pointsto γ' a obj'))%I
    (λ a o, twophase_pre_crash_inv_pred ex_pointsto γ a o)
    with "Hpre [Hdurable_pointstos Hex_pointstos] []") as "Hcrash".
  {
    iDestruct (big_sepM_sep with "[$Hdurable_pointstos $Hex_pointstos]")
      as "Hpointstos".
    iApply (big_sepM_impl with "Hpointstos").
    iIntros (a obj Hacc) "!> [Hdurable_pointsto ?]".
    iFrame. eauto. }
  {
    iApply big_sepM_forall.
    iIntros (a obj Hacc) "!>Hpreds".
    iNamed "Hpreds".
    iMod (exchange_durable_pointsto1 with "[$]") as "Hdurable".
    iModIntro. iExists _. iFrame.
    iDestruct ("Htxn_cinv") as "(_&%)".
    iPureIntro. eapply exchange_pointsto_valid; eauto.
  }
  iModIntro. iApply (init_cancel_wand with "Hcrash [Htokens] []").
  {
    iIntros "Hcrash_invs".
    iApply big_sepS_set_map.
    {
      intros a1 a2 Hin_a1 Hin_a2 Heq.
      apply Haddrs_valid in Hin_a1.
      apply Haddrs_valid in Hin_a2.
      apply addr2flat_eq; assumption.
    }
    iApply big_sepM_dom.
    iDestruct (big_sepM_sep with "[$Htokens $Hcrash_invs]") as "Hlinvs".
    iApply (big_sepM_mono with "Hlinvs").
    iIntros (a obj Hacc) "[Hcrash_inv Htoken]".
    iExists _.
    iSplit; last by auto.
    iExists _.
    iFrame. iPureIntro.
    apply Hkinds.
    assumption.
  }
  iIntros "H #HC".
  iApply big_sepM_fupd.
  iApply (big_sepM_wand with "H").
  iApply big_sepM_intro. iIntros "!>" (???) "H".
  iMod ("H" with "[$]") as (obj) "(Hex&Hdur&Hpointsto_valid)".
  iModIntro. iExists _. iFrame.
Qed.

Theorem wp_Txn__Begin_raw (prel txnl locksl: loc) γ γ' dinit ex_pointsto ghs objs_dom :
  set_Forall valid_addr objs_dom →
  {{{
    "#Hpre.txn_ro" ∷ readonly (prel ↦[txn.Log :: "log"] #txnl) ∗
    "#Hpre.locks_ro" ∷ readonly (prel ↦[txn.Log :: "locks"] #locksl) ∗
    "#Htxn" ∷ (
      invariant.is_txn txnl γ.(jrnl_txn_names) dinit ∗
      is_txn_system Njrnl γ
    ) ∗
    "#Htxn_cinv" ∷ txn_cinv Njrnl γ γ' ∗
    "#HlockMap" ∷ is_lockMap locksl ghs
      (set_map addr2flat objs_dom)
      (twophase_linv_flat ex_pointsto γ γ')
  }}}
    Begin #prel
  {{{
    (l : loc), RET #l;
      "Htwophase_raw" ∷
        is_twophase_raw l γ γ' dinit ex_pointsto objs_dom ∅
  }}}.
Proof.
  intros Htracked_addrs_wf.
  wp_start.
  wp_call.
  iMod (readonly_load with "Hpre.txn_ro") as "Hpre.txn".
  iMod (readonly_load with "Hpre.locks_ro") as "Hpre.locks".
  iDestruct "Hpre.txn" as (qtxn) "Hpre.txn".
  iDestruct "Hpre.locks" as (qlocks) "Hpre.locks".
  wp_loadField.
  wp_apply (wp_Op__Begin' with "Htxn").
  iIntros (? ? jrnll) "(?&?)".
  iNamed.
  wp_loadField.
  wp_apply (wp_NewMap).
  iIntros (acquired_m) "Hacquired_m".
  wp_apply wp_allocStruct; first by auto.
  iIntros (l) "Hl".
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_pures.
  iApply "HΦ". iModIntro.

  iDestruct (struct_fields_split with "Hl") as "(?&?&?&_)".
  iNamed.
  iSplitL "locks acquired Hacquired_m".
  {
    iExists _, _, _.
    rewrite big_sepS_empty dom_empty_L set_map_empty.
    iFrame "∗ #".
    iPureIntro.
    set_solver.
  }
  iSplitL.
  {
    iExists _, _, _.
    rewrite fmap_empty big_sepM_empty.
    by iFrame.
  }
  auto.
Qed.

Lemma twophase_linv_get_addr_valid ex_pointsto γ γ' a :
  "Hlinv" ∷ twophase_linv ex_pointsto γ γ' a -∗
  "%Hvalid" ∷ ⌜valid_addr a⌝.
Proof.
  iNamed 1.
  iNamed "Hlinv".
  iPureIntro.
  rewrite /pointsto_valid in Hvalid.
  intuition.
Qed.

Lemma is_twophase_raw_get_valid l γ γ' dinit ex_pointsto objs_dom mt_changed :
  "Htwophase" ∷ is_twophase_raw
    l γ γ' dinit ex_pointsto objs_dom mt_changed -∗
  "%Hvalids" ∷ ⌜
    map_Forall
      (λ a vobj,
        pointsto_valid γ a (modified vobj)
      )
      mt_changed
  ⌝.
Proof.
  iNamed 1.
  iNamed "Htwophase".
  iFrame "%".
Qed.

Lemma is_twophase_raw_get_mt_in_spec l γ γ' dinit ex_pointsto objs_dom mt_changed :
  "Htwophase" ∷ is_twophase_raw
    l γ γ' dinit ex_pointsto objs_dom mt_changed -∗
  "Hmt_dom" ∷ ⌜dom mt_changed ⊆ objs_dom⌝.
Proof.
  iNamed 1.
  iNamed "Htwophase".
  iNamed "Hlocks".
  iPureIntro.
  intros a Hin.
  apply (elem_of_map_2 (D:=gset _)) with (f := addr2flat) in Hin as Hin'.
  pose proof ((iffLR (elem_of_subseteq _ _)) Hlocks_in_dom _ Hin') as Hin''.
  apply elem_of_map_1 in Hin''.
  destruct Hin'' as [addr' [Heq Haddr'_in]].
  apply addr2flat_eq in Heq; first by (subst addr'; assumption).
  - apply elem_of_dom in Hin.
    destruct Hin as [obj Hacc].
    apply Hvalids in Hacc.
    destruct Hacc as (Hvalid&_&_).
    assumption.
  - apply Haddrs_valid in Haddr'_in.
    assumption.
Qed.

Lemma pair_fst_fmap {A B} (l: list A) (b: B) :
  ((λ k, (k, b)) <$> l).*1 = l.
Proof.
  rewrite -list_fmap_compose (Forall_fmap_ext_1 _ id).
  2: apply Forall_forall; auto.
  apply list_fmap_id.
Qed.
Opaque crash_borrow.

Theorem wp_Txn__acquireNoCheck' l γ γ' ex_pointsto objs_dom_flat locks_held (a: addr):
  valid_addr a →
  addr2flat a ∈ objs_dom_flat →
  addr2flat a ∉ locks_held →
  ∀ Φ,
  "Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat locks_held
  -∗ (▷ ("Hlinv" ∷ twophase_linv ex_pointsto γ γ' a -∗
        wpc_nval ⊤ ("Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat ({[addr2flat a]} ∪ locks_held)
                    -∗ Φ #())))
     -∗ WP Txn__acquireNoCheck #l (addr2val a);; #() {{ v, Φ v }}.
Proof.
  intros Ha_valid Hin_spec Haddr_not_locked.
  iIntros (Φ).
  iIntros "Hlocks HΦ".
  wp_call.
  iNamed "Hlocks". iNamed "Hlocks".
  wp_apply wp_Addr__Flatid; first by (iPureIntro; assumption).
  iIntros (flat_addr) "->".
  wp_pures.
  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$HlockMap]");
    first by (iPureIntro; assumption).
  iIntros "[Hlinv Hlocked]".
  wp_loadField.
  iSpecialize ("HΦ" with "[Hlinv]").
  {
    iDestruct "Hlinv" as (a') "[? ?]".
    iNamed.
    iDestruct (twophase_linv_get_addr_valid with "Hlinv") as "%Ha'_valid".
    apply addr2flat_eq in Ha; [|assumption|assumption].
    subst a'.
    iFrame "Hlinv".
  }
  iApply (wpc_nval_elim_wp with "[$]"); eauto.

  wp_apply (wp_MapInsert with "Hacquired_m"); first by auto.
  iIntros "Hacquired_m".
  rewrite /typed_map.map_insert.
  replace (<[_:=_]>_) with (
    set_to_map (λ k, (k, true)) ({[addr2flat a]} ∪ locks_held): gmap _ _
  ).
  2: {
    apply map_eq.
    intros a'.
    destruct
      (set_to_map (λ k, (k, true)) ({[addr2flat a]} ∪ locks_held) !! a')
      as [b|] eqn:Hacc.
    2: {
      apply not_elem_of_list_to_map_2 in Hacc.
      rewrite pair_fst_fmap in Hacc.
      apply (iffLRn (elem_of_elements _ _)) in Hacc.
      apply not_elem_of_union in Hacc.
      destruct Hacc as [Hnota' Hnotin].
      apply not_elem_of_singleton_1 in Hnota'.
      rewrite lookup_insert_ne; last by auto.
      rewrite not_elem_of_list_to_map_1 //.
      rewrite pair_fst_fmap.
      set_solver.
    }
    apply lookup_set_to_map in Hacc; last by auto.
    destruct Hacc as [a'' [Hin Heq]].
    inversion Heq; subst a' b; clear Heq.
    apply elem_of_union in Hin.
    destruct (decide (a'' = addr2flat a)) as [Heq|Hneq].
    {
      subst a''.
      rewrite lookup_insert.
      reflexivity.
    }
    destruct Hin as [Hin|Hin]; first by set_solver.
    rewrite lookup_insert_ne; last by auto.
    symmetry.
    eapply (lookup_set_to_map (λ k, (k, true))); first by auto.
    eexists _.
    split; last by reflexivity.
    assumption.
  }

  wp_pures. iModIntro.
  iIntros "HΦ".
  iApply "HΦ".
  iExists _, _, _.
  rewrite big_sepS_union.
  2: {
    apply disjoint_singleton_l.
    assumption.
  }
  rewrite big_sepS_singleton.
  iFrame "∗ #".
  iPureIntro.
  set_solver.
Qed.

(*
Theorem wp_Txn__acquireNoCheck l γ γ' ex_pointsto objs_dom_flat locks_held (a: addr):
  valid_addr a →
  addr2flat a ∈ objs_dom_flat →
  addr2flat a ∉ locks_held →
  {{{
    "Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat locks_held
  }}}
    Txn__acquireNoCheck #l (addr2val a)
  {{{
    RET #();
    "Hlocks" ∷ is_twophase_locks
      l γ γ' ex_pointsto objs_dom_flat ({[addr2flat a]} ∪ locks_held) ∗
    "Hlinv" ∷ twophase_linv ex_pointsto γ γ' a
  }}}.
Proof.
  intros Ha_valid Hin_spec Haddr_not_locked.
  wp_start.
  wp_apply (wp_Txn__acquireNoCheck' with "[$] [-]"); eauto.
  iNext. iNamed 1.
  iApply wpc_nval_intro.
  iNext. iIntros "H". iApply "HΦ". iFrame.
Qed.
*)

Theorem wp_Txn__isAlreadyAcquired' l γ γ' ex_pointsto objs_dom_flat locks_held a :
  valid_addr a →
  addr2flat a ∈ objs_dom_flat →
  ∀ Φ,
  "Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat locks_held -∗
   ▷ ("Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat locks_held
            -∗ wpc_nval ⊤ (Φ #(bool_decide (addr2flat a ∈ locks_held)))) -∗
  WP Txn__isAlreadyAcquired #l (addr2val a) {{ v, Φ v }}.
Proof.
  intros Ha_valid Haddr_wf.
  wp_start.
  rewrite /post.
  wp_call.
  wp_apply wp_Addr__Flatid; first by (iPureIntro; assumption).
  iIntros (flat_addr) "->".
  iNamed "Hlocks".
  wp_loadField.
  wp_apply (wp_MapGet with "Hacquired_m").
  iIntros (b ok) "[%Hget Hacquired_m]".
  rewrite /map_get /= in Hget.
  inversion Hget; subst b ok; clear Hget.
  iSpecialize ("HΦ" with "[-]").
  {
    iExists _, _, _. iFrame "∗ # %".
  }
  iApply (wpc_nval_elim_wp with "[$]"); auto.
  wp_pures.
  iModIntro.
  replace (default _ _) with (bool_decide (addr2flat a ∈ locks_held)).
  2: {
    destruct (set_to_map (λ k, (k, true)) locks_held !! addr2flat a)
      as [b|] eqn:Hacc.
    2: {
      rewrite bool_decide_eq_false_2 //.
      apply (not_elem_of_list_to_map_2 ((λ k, (k, true)) <$> _) _) in Hacc.
      rewrite pair_fst_fmap in Hacc.
      apply (iffLRn (elem_of_elements _ _)) in Hacc.
      assumption.
    }
    simpl.
    eapply (lookup_set_to_map (λ k, (k, true))) in Hacc; last by auto.
    destruct Hacc as [a' [Hin Heq]].
    inversion Heq; subst a' b; clear Heq.
    apply bool_decide_eq_true_2.
    assumption.
  }
  eauto.
Qed.

Theorem wp_Txn__isAlreadyAcquired l γ γ' ex_pointsto objs_dom_flat locks_held a :
  valid_addr a →
  addr2flat a ∈ objs_dom_flat →
  {{{
    "Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat locks_held
  }}}
    Txn__isAlreadyAcquired #l (addr2val a)
  {{{
    RET #(bool_decide (addr2flat a ∈ locks_held));
    "Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat locks_held
  }}}.
Proof.
  intros Ha_valid Haddr_wf.
  wp_start.
  wp_apply (wp_Txn__isAlreadyAcquired' with "[$] [-]"); eauto.
  iNext. iNamed 1.
  iApply wpc_nval_intro.
  iNext. iApply "HΦ". iFrame.
Qed.

Theorem wp_Txn__Acquire' l γ γ' ex_pointsto objs_dom_flat locks_held (a: addr):
  valid_addr a →
  addr2flat a ∈ objs_dom_flat →
  ∀ Φ,
  is_twophase_locks l γ γ' ex_pointsto objs_dom_flat locks_held -∗
  ▷ ("Hlinv" ∷ (if decide (addr2flat a ∈ locks_held) then True else twophase_linv ex_pointsto γ γ' a) -∗
     wpc_nval ⊤ ("Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat
                (if decide (addr2flat a ∈ locks_held) then locks_held else {[addr2flat a]} ∪ locks_held) -∗
                Φ #())) -∗
  WP Txn__Acquire #l (addr2val a) {{ v, Φ v }}.
Proof.
  iIntros (?? Φ) "Hlocks HΦ".
  wp_call.
  wp_apply (wp_Txn__isAlreadyAcquired with "Hlocks");
    [assumption|assumption|].
  iNamed 1.
  destruct (bool_decide) eqn:Heqb.
  - apply bool_decide_eq_true in Heqb.
    rewrite !(decide_True _ _ Heqb).
    iSpecialize ("HΦ" with "[//]").
    iApply (wpc_nval_elim_wp with "HΦ"); auto.
    wp_pures. iIntros "!> H". by iApply "H".
  - apply bool_decide_eq_false in Heqb.
    rewrite !(decide_False _ _ Heqb).
    wp_pures.
    wp_apply (wp_Txn__acquireNoCheck' with "Hlocks"); eauto.
Qed.

Theorem wp_Txn__Acquire l γ γ' ex_pointsto objs_dom_flat locks_held (a: addr):
  valid_addr a →
  addr2flat a ∈ objs_dom_flat →
  {{{
    "Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat locks_held
  }}}
    Txn__Acquire #l (addr2val a)
  {{{
    RET #();
    let a_locked := addr2flat a ∈ locks_held in
    "Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat (
      if decide (a_locked) then locks_held
      else ({[addr2flat a]} ∪ locks_held)
    ) ∗
    "Hlinv" ∷ (
      if decide (a_locked)
      then True
      else twophase_linv ex_pointsto γ γ' a
    )
  }}}.
Proof.
  intros Ha_valid Hin_spec.
  wp_start.
  wp_apply (wp_Txn__Acquire' with "[$] [-]"); eauto.
  iNext. iNamed 1.
  iApply wpc_nval_intro.
  iNext. iIntros "Hlocks". iApply "HΦ". iFrame.
Qed.

Lemma is_twophase_jrnl_not_in_map l γ dinit mt_changed a obj :
  "Hjrnl" ∷ is_twophase_jrnl l γ dinit mt_changed -∗
  "Hold_vals" ∷ (
    [∗ map] a ↦ vobj ∈ mt_changed,
      "Hdurable_pointsto" ∷ durable_pointsto γ a (committed vobj)
  ) -∗
  "Hdurable_pointsto" ∷ durable_pointsto γ a obj -∗
  ⌜mt_changed !! a = None⌝.
Proof.
  iIntros "???".
  iNamed.
  iNamed "Hjrnl".
  iNamed "Hjrnl_mem".
  iDestruct (map_ctx_agree with "Hjrnl_durable_frag Hdurable") as %<-.
  iDestruct (
    is_jrnl_durable_not_in_map with
    "Hdurable_pointsto [Hjrnl_durable_frag Hold_vals] Hdurable"
  ) as "%Hnotin".
  2: {
    iPureIntro.
    rewrite lookup_fmap in Hnotin.
    apply fmap_None in Hnotin.
    assumption.
  }
  iExists _.
  iFrame.
  iSplitL; first by (iApply big_sepM_fmap; iFrame).
  iModIntro.
  iIntros (?) "Hpointstos".
  trivial.
Qed.

Theorem twophase_lift l γ γ' dinit mt_changed ex_pointsto `{!∀ a obj, Timeless (ex_pointsto a obj)} a :
  mt_changed !! a = None →
  "#Htxn_cinv" ∷ txn_cinv Njrnl γ γ' -∗
  "Hjrnl" ∷ is_twophase_jrnl l γ dinit mt_changed -∗
  "Hcrash_invs" ∷ (
    [∗ map] a' ↦ vobj' ∈ mt_changed,
      "Hcrash_inv" ∷ twophase_crash_inv
        ex_pointsto γ γ' a' (committed vobj')
  ) -∗
  "Hlinv" ∷ twophase_linv ex_pointsto γ γ' a
  -∗ wpc_nval ⊤ (∃ obj,
    let mt_changed' := <[a:=object_to_versioned obj]>mt_changed in
    "Hjrnl" ∷ is_twophase_jrnl l γ dinit mt_changed' ∗
    "Hcrash_invs" ∷ (
      [∗ map] a' ↦ vobj' ∈ mt_changed',
        "Hcrash_inv" ∷ twophase_crash_inv
          ex_pointsto γ γ' a' (committed vobj')
    ) ∗
    "%Hvalid" ∷ ⌜pointsto_valid γ a obj⌝
  ).
Proof.
  iIntros (Hnotin) "????".
  iNamed.
  iNamed "Hlinv".
  iNamed "Hjrnl".
  iPoseProof (
    crash_borrow_wpc_nval ⊤ _ _
    (twophase_pre_crash_inv_pred ex_pointsto γ a obj)
    (
      "Hjrnl_mem" ∷ is_jrnl_mem
        Njrnl jrnll γ dinit γtxn γdurable ∗
      "Hjrnl_durable_frag" ∷ map_ctx
        γdurable (1/2) (<[a:=obj]>(committed <$> mt_changed)) ∗
      "Hjrnl_maps_to" ∷ jrnl_maps_to γtxn a obj
    )%I
    with "[$Hcrash_inv] [Htoken Hjrnl_mem Hjrnl_durable_frag]")
    as "Hnval".
  {
    iNext. iIntros "(?&?&_)".
    iNamed.
    iMod (lift_into_txn' with "
      Hjrnl_mem Hjrnl_durable_frag [$Hdurable $Htoken]
    ") as "(?&?&?&?&?)".
    1-3: solve_ndisj.
    iNamed.
    iFrame "∗ #".
    iIntros "!>".
    iSplit; last by (iPureIntro; assumption).
    iIntros "!> (?&?&?)".
    iIntros "Hc".
    iMod (exchange_durable_pointsto1 with "[$] [$]") as "Hdurable".
    iNamed.
    iIntros "!>".
    iExists _.
    iFrame "∗ %".
    iDestruct ("Htxn_cinv") as "(_&%)".
    iPureIntro. eapply exchange_pointsto_valid; eauto.
  }
  iApply (wpc_nval_strong_mono with "Hnval").
  iNext. iDestruct 1 as "[(?&?&?) Hcrash_inv]".
  iNamed.
  iModIntro.
  iExists _.
  iSplitR "Hcrash_inv Hcrash_invs".
  {
    iExists _, _, _.
    rewrite fmap_insert /committed committed_to_versioned.
    iFrame "Hjrnl_mem Htxn.jrnl Hjrnl_durable_frag".
    iApply big_sepM_insert; first by assumption.
    rewrite /modified modified_to_versioned.
    iFrame.
  }
  iSplit; last by (iPureIntro; eassumption).
  iApply big_sepM_insert; first by assumption.
  rewrite /committed committed_to_versioned.
  iFrame.
Qed.

Theorem twophase_lift_if_needed l γ γ' dinit mt_changed ex_pointsto `{!∀ a obj, Timeless (ex_pointsto a obj)} a :
  "Htxncinv" ∷ txn_cinv Njrnl γ γ' -∗
  "Hjrnl" ∷ is_twophase_jrnl l γ dinit mt_changed -∗
  "Hcrash_invs" ∷ (
    [∗ map] a' ↦ vobj' ∈ mt_changed,
      "Hcrash_inv" ∷ twophase_crash_inv
        ex_pointsto γ γ' a' (committed vobj')
  ) -∗
  "Hlinv" ∷ (
    match mt_changed !! a with
    | Some _ => True
    | None => "Hlinv" ∷ twophase_linv ex_pointsto γ γ' a
    end
  )
  -∗ wpc_nval ⊤ (∃ obj,
    let mt_changed' := (
      match mt_changed !! a with
      | Some _ => mt_changed
      | None => <[a:=object_to_versioned obj]>mt_changed
      end
    ) in
    "Hjrnl" ∷ is_twophase_jrnl l γ dinit mt_changed' ∗
    "Hcrash_invs" ∷ (
      [∗ map] a' ↦ vobj' ∈ mt_changed',
        "Hcrash_inv" ∷ twophase_crash_inv
          ex_pointsto γ γ' a' (committed vobj')
    ) ∗
    "%Hvalid" ∷ ⌜
      match mt_changed !! a with
      | Some _ => True
      | None => pointsto_valid γ a obj
      end
    ⌝
  ).
Proof.
  iIntros "????".
  iNamed.
  destruct (mt_changed !! a) as [vobj|] eqn:Hacc;
    first by (iApply wpc_nval_intro; iExists (committed vobj); iModIntro; iFrame).
  iNamed.
  iPoseProof (twophase_lift with "Htxncinv Hjrnl Hcrash_invs Hlinv") as "H"; first by assumption.
  iApply (wpc_nval_strong_mono with "H").
  iNext.
  iDestruct 1 as (?) "(?&?)".
  iNamed.
  iModIntro.
  iExists _.
  iFrame "∗ %".
Qed.

Lemma decide_is_Some {A B} (x: option A) (P Q: B) :
  (if decide (is_Some x) then P else Q) =
  (match x with | Some _ => P | None => Q end).
Proof.
  destruct x; rewrite //=.
Qed.

Theorem wp_Txn__Acquire_lift l γ γ' dinit ex_pointsto `{!∀ a obj, Timeless (ex_pointsto a obj)} objs_dom mt_changed a:
  a ∈ objs_dom →
  {{{
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed
  }}}
    Txn__Acquire #l (addr2val a)
  {{{
    obj, RET #();
    let mt_changed' :=
      match mt_changed !! a with
      | Some _ => mt_changed
      | None => <[a:=object_to_versioned obj]>mt_changed
      end
    in
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed'
  }}}.
Proof.
  intros Hin_spec.
  wp_start.
  iDestruct (is_twophase_raw_get_mt_in_spec with "Htwophase")
    as "%Hmt_in_spec".
  iNamed "Htwophase".
  iApply wp_ncfupd.
  wp_apply (wp_Txn__Acquire' with "Hlocks").
  {
    apply Haddrs_valid.
    assumption.
  }
  {
    apply elem_of_map_2.
    assumption.
  }
  iNamed 1.
  assert (
    addr2flat a ∈ (set_map addr2flat (dom mt_changed): gset _) ↔
    is_Some (mt_changed !! a)
  ) as Hlocked_iff.
  {
    split.
    - intros Hlocked.
      apply elem_of_dom.
      apply elem_of_map_1 in Hlocked.
      destruct Hlocked as (a'&Ha_eq&Ha').
      pose proof ((iffLR (elem_of_subseteq _ _)) Hmt_in_spec _ Ha')
        as Ha'_tracked.
      apply Haddrs_valid in Ha'_tracked.
      apply Haddrs_valid in Hin_spec.
      apply addr2flat_eq in Ha_eq;
        [subst a'; assumption|assumption|assumption].
    - intros Hin.
      apply elem_of_dom in Hin.
      apply (elem_of_map_2 (D:=gset _) addr2flat) in Hin.
      assumption.
  }
  rewrite !(decide_ext _ _ _ _ Hlocked_iff) !decide_is_Some.
  iPoseProof (twophase_lift_if_needed with "Htxn_cinv Hjrnl Hcrash_invs Hlinv")
    as "H".
  iApply (wpc_nval_strong_mono with "H").
  iNext. iIntros "H".
  iNamed "H".
  iIntros "!> Hlocks !>".
  iNamed.
  iApply "HΦ".
  rewrite /is_twophase_raw.
  iFrame "Hjrnl ∗ #".
  iSplitL "Hlocks".
  {
    destruct (mt_changed !! a) as [v|] eqn:Hacc; first by iFrame.
    rewrite dom_insert_L set_map_union_L set_map_singleton_L //.
  }
  iPureIntro.
  destruct (mt_changed !! a) as [old_vobj|] eqn:Hlookup_old;
    first by intuition.
  split; last by assumption.
  apply map_Forall_insert_2; last by assumption.
  apply Hvalid.
Qed.

Lemma big_sepM_list_to_map `{Countable K} {A} l (Φ: K → A → iProp Σ) :
  NoDup l.*1 →
  ([∗ list] x ∈ l, Φ x.1 x.2) -∗
  ([∗ map] k↦v ∈ list_to_map l, Φ k v).
Proof.
  induction l as [|x].
  {
    iIntros (HNoDup) "Hsep".
    rewrite list_to_map_nil.
    iApply big_sepM_empty.
    auto.
  }
  iIntros (HNoDup) "Hsep".
  destruct x as [k v].
  rewrite list_to_map_cons.
  iDestruct (big_sepL_cons with "Hsep") as "[Hx Hsep]".
  rewrite fmap_cons in HNoDup.
  apply NoDup_cons in HNoDup.
  destruct HNoDup as [Hnotin HNoDup].
  iApply big_sepM_insert.
  {
    apply not_elem_of_list_to_map_1.
    auto.
  }
  simpl.
  iFrame.
  iApply ((IHl HNoDup) with "Hsep").
Qed.

Theorem wp_Txn__ReleaseAll l γ γ' ex_pointsto objs_dom_flat locks_held :
  {{{
    "Hlocks" ∷ is_twophase_locks l γ γ' ex_pointsto objs_dom_flat locks_held ∗
    "Hlinvs" ∷ ([∗ set] flat_a ∈ locks_held, (
      "Hlinv" ∷ twophase_linv_flat ex_pointsto γ γ' flat_a
    ))
  }}}
    Txn__ReleaseAll #l
  {{{
    RET #(); True
  }}}.
Proof.
  wp_start.
  wp_call.
  iNamed "Hlocks".
  wp_loadField.
  wp_apply (
    wp_MapIter_3 _ _ _ _ _
    (λ mtodo mdone,
      "Htxn.locks" ∷ l ↦[Txn :: "locks"] #locksl ∗
      "Hlockeds" ∷ ([∗ set] flat_a ∈ dom mtodo,
        "Hlocked" ∷ Locked ghs flat_a
      ) ∗
      "Hlinvs" ∷ ([∗ set] flat_a ∈ dom mtodo,
        "Hlinv" ∷ twophase_linv_flat ex_pointsto γ γ' flat_a
      )
    )%I
    with "Hacquired_m [$Htxn.locks Hlockeds Hlinvs] [] [HΦ]"
  ).
  {
    rewrite dom_list_to_map_L pair_fst_fmap list_to_set_elements_L.
    iFrame.
  }
  {
    iIntros (a b ? ? Φ') "!> (Hpre&%Htodo_done&(%Hdisj&%Hin_todo)) HΦ'".
    iNamed "Hpre".
    wp_loadField.
    rewrite -(insert_id mtodo a b); last by assumption.
    rewrite -insert_delete_insert dom_insert_L.
    rewrite big_sepS_insert; last by set_solver.
    rewrite big_sepS_insert; last by set_solver.
    iDestruct "Hlockeds" as "[? Hlockeds]".
    iDestruct "Hlinvs" as "[? Hlinvs]".
    iNamed.
    wp_apply (wp_LockMap__Release with "[$HlockMap $Hlocked $Hlinv]").
    iApply "HΦ'".
    rewrite delete_insert; last by apply lookup_delete.
    iFrame.
  }
  iIntros "(Hacquired_m&Hpost)".
  iNamed "Hpost".
  wp_pures. iApply "HΦ".
  done.
Qed.

Lemma wpc_crash_borrow_open_modify_sepM {A} `{Countable K} Qnew  E1 e Φ Φc
       Q P (m: gmap K A) :
  to_val e = None →
  (□ (∀ i x, ⌜ m !! i = Some x ⌝ → Q i x -∗ P i x)) -∗
  ([∗ map] i ↦ v ∈ m, crash_borrow (Q i v) (P i v)) -∗
  (Φc ∧
   (([∗ map] i ↦ v ∈ m, Q i v) -∗
      WPC e @ E1
      {{λ retv,
        ([∗ map] i ↦ v ∈ m, Qnew retv i v) ∗
          ([∗ map] i ↦ v ∈ m, □ (Qnew retv i v -∗ P i v)) ∗
         Φc ∧ (([∗ map] i ↦ v ∈ m, crash_borrow (Qnew retv i v) (P i v)) -∗ (Φ retv))
      }}
      {{Φc ∗ ([∗ map] i ↦ v ∈ m, P i v)}}) -∗
  WPC e @ E1 {{ Φ }} {{ Φc }}).
Proof.
  iIntros (Hnval) "#Hstatuses Hcrash_invs Hwpc".
  iInduction m as [|i x m] "IH" using map_ind forall (Φ Φc).
  {
    iDestruct "Hwpc" as "[_ Hwpc]".
    iDestruct ("Hwpc" with "[]") as "Hwpc"; first by auto.
    iDestruct (wpc_subscript_mono _ _ _ E1 with "Hwpc") as "Hwpc";
      [auto|auto|].
    iApply (wpc_mono with "Hwpc").
    {
      iIntros (v) "/= (_&_&(_&Hcrash))".
      iDestruct ("Hcrash" with "[//]") as "$".
    }
    iIntros "[$ _]".
  }
  iDestruct (big_sepM_insert with "Hcrash_invs") as "(Hcrash_inv&Hcrash_invs)"; auto.
  iApply (
    wpc_crash_borrow_open_modify
    with "Hcrash_inv [Hwpc Hcrash_invs]"
  ).
  { eauto. }
  iSplit.
  { iDestruct "Hwpc" as "[H _]". iFrame. }
  iIntros "HQ".
  iApply wpc_fupd.
  iApply (wpc_strong_mono _ _ _ _ _ _ _
                          (Φc ∗ (P i x ∨ Q i x))%I with "[-] []"); auto; last first.
  { iSplit.
   { iIntros (?) "H". iModIntro. iExact "H". }
   iIntros "($&Hsep)".
   iDestruct "Hsep" as "[HP|HQ]"; first auto.
   iModIntro.
   iApply "Hstatuses".
   { rewrite lookup_insert //=. }
   eauto.
  }
  iApply ("IH" $! _ (Φc ∗ (P i x ∨ Q i x))%I with "[] Hcrash_invs [HQ Hwpc]").
  { iModIntro. iIntros. iApply "Hstatuses".
    - iPureIntro. rewrite lookup_insert_ne; congruence.
    - eauto. }
  {
    iSplit.
    { iLeft in "Hwpc". iFrame. }
    iRight in "Hwpc".
    iIntros "HQs".
    iDestruct ("Hwpc" with "[HQs HQ]") as "Hwpc".
    {
      iApply big_sepM_insert; first by assumption.
      iFrame.
    }
    iApply (wpc_strong_mono with "Hwpc"); auto.
    iSplit.
    {
      iIntros (v) "(Hnew&Hstatuses'&HΦc)".
      iDestruct (big_sepM_insert with "Hstatuses'")
        as "[#Hstatus Hstatuses']"; first by assumption.
      iDestruct (big_sepM_insert with "Hnew") as "(HnewQ&HnewQs)"; first by assumption.
      iFrame "Hstatuses' HnewQs".
      iModIntro.
      iSplit.
      { iLeft in "HΦc".
        iFrame. iDestruct ("Hstatus" with "[$]") as "?". iFrame.
      }
      iIntros "Hcrashes".
      iFrame. iModIntro.
      iExists (Qnew v i x).
      iFrame.
      iSplitL "".
      {
        iModIntro. iIntros. iSpecialize ("Hstatus" with "[$]").
        eauto.
      }
      iIntros "Hcrash".
      iSplit.
      { iLeft in "HΦc". eauto. }
      iRight in "HΦc". iApply "HΦc".
      iApply big_sepM_insert; auto. iFrame.
    }
    iIntros "($&H)".
    iModIntro. iDestruct (big_sepM_insert with "H") as "($&$)". auto.
  }
Qed.

Theorem wp_Txn__commitNoRelease_raw l γ γ' dinit ex_pointsto `{!∀ a obj, Discretizable (ex_pointsto a obj)} `{!∀ a obj, Timeless (ex_pointsto a obj)} objs_dom mt_changed Qok Qnok :
  {{{
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed ∗
    "Hfupd" ∷ (
      (
        "Hcommitted" ∷ (
          [∗ map] a ↦ vobj ∈ mt_changed,
            ex_pointsto a (committed vobj)
        )
        -∗ |C={⊤}=>
        "Hmodified" ∷ (
          [∗ map] a ↦ vobj ∈ mt_changed,
            ex_pointsto a (modified vobj)
        )
      ) ∧ ▷ (
        "Hcommitted" ∷ (
          [∗ map] a ↦ vobj ∈ mt_changed,
            ex_pointsto a (committed vobj)
        )
        -∗
        (
          |NC={⊤}=>
          "Hmodified" ∷ (
            [∗ map] a ↦ vobj ∈ mt_changed,
              ex_pointsto a (modified vobj)
          ) ∗
          "HQ" ∷ Qok
        ) ∧
        (
          "Hcommitted" ∷ (
            [∗ map] a ↦ vobj ∈ mt_changed,
              ex_pointsto a (committed vobj)
          ) ∗
          "HQ" ∷ Qnok
        )
      )
    )
  }}}
    Txn__commitNoRelease #l #true
  {{{
    (ok:bool), RET #ok;
    "Hlocks" ∷ is_twophase_locks
      l γ γ' ex_pointsto (set_map addr2flat objs_dom)
      (set_map addr2flat (dom mt_changed)) ∗
    "Hlinvs" ∷ (
      [∗ set] a ∈ dom mt_changed,
        "Hlinv" ∷ twophase_linv_flat ex_pointsto γ γ' (addr2flat a)
    ) ∗
    "HQ" ∷ (if ok then Qok else Qnok)
  }}}.
Proof.
  wp_start.
  wp_call.
  wp_apply util_proof.wp_DPrintf.
  wp_pures.
  iNamed "Htwophase".
  iNamed "Hjrnl".
  wp_loadField.
  iApply (wpc_wp _ _ _ _ True).
  iApply (
    wpc_crash_borrow_open_modify_sepM
    (λ v a vobj,
      let vobj_branch := (
        if decide (v = #true) then modified else committed
      ) in
      twophase_pre_crash_inv_pred ex_pointsto γ a (vobj_branch vobj)
    )%I
    _ _
    with "[] Hcrash_invs"
  ); try trivial.
  {
    iModIntro.
    iIntros (?? Hacc) "[? [? %]]".
    iIntros "HC".
    iMod (exchange_durable_pointsto1 _ _ _ with "[$] [$]") as "Hdurable".
    iModIntro. iExists _. iFrame.
    iDestruct ("Htxn_cinv") as "(_&%)".
    iPureIntro. eapply exchange_pointsto_valid; eauto.
  }
  iSplit; first by auto.
  iIntros "Hcrash_invs".
  iDestruct (big_sepM_sep with "Hcrash_invs")
    as "[Hex_pointstos Hdurable_pointstos]".
  iDestruct (big_sepM_sep with "Hdurable_pointstos")
    as "[Hdurable_pointstos #Hwfs]".
  iApply big_sepM_fmap in "Hjrnl_maps_tos".
  iApply big_sepM_fmap in "Hdurable_pointstos".
  iApply wpc_cfupd.
  iApply wpc_ncfupd.
  wpc_apply (wpc_Op__CommitWait' with "[
    $Hjrnl_mem $Hjrnl_durable_frag $Hjrnl_maps_tos $Hdurable_pointstos
    $Htxn_cinv
  ]").
  1-3: solve_ndisj.
  iSplit.
  {
    iDestruct "Hfupd" as "[Hfupd _]".
    iIntros "Hdurable_pointstos HC".
    iSplitR; first by trivial.
    iDestruct (big_sepM_forall with "Hwfs") as "%Hwfs".
    iDestruct "Htxn_cinv" as "(_&%Hkinds)".
    iDestruct "Hdurable_pointstos" as "[Hdurable_pointstos|Hdurable_pointstos]".
    {
      iIntros "!>".
      iApply (big_sepM_fmap committed) in "Hdurable_pointstos".
      iDestruct (big_sepM_sep with "[$Hex_pointstos $Hdurable_pointstos]")
        as "Hpointstos".
      iApply (big_sepM_impl with "Hpointstos").
      iIntros (a vobj Hacc) "!> [? Hdurable_pointsto]".
      iModIntro.
      iExists _.
      iFrame.
      iPureIntro.
      apply Hwfs in Hacc.
      eapply exchange_pointsto_valid; eassumption.
    }
    iDestruct "HC" as "#HC".
    iMod ("Hfupd" with "Hex_pointstos HC") as "?".
    iNamed.
    iIntros "!>".
    iApply (big_sepM_fmap modified) in "Hdurable_pointstos".
    iDestruct (big_sepM_sep with "[$Hmodified $Hdurable_pointstos]")
      as "Hpointstos".
    iApply (big_sepM_impl with "Hpointstos").
    iIntros (a vobj Hacc) "!> [? Hdurable_pointsto]".
    iModIntro.
    iExists _.
    iFrame.
    iPureIntro.
    apply Hwfs in Hacc.
    eapply exchange_pointsto_valid; eassumption.
  }
  iDestruct "Hfupd" as "[_ Hfupd]".
  iModIntro.
  iIntros (ok) "Hdurable_pointstos".
  iDestruct (big_sepM_sep with "Hdurable_pointstos") as
    "[Htokens Hdurable_pointstos]".
  replace (if ok then _ else _) with
    ((if ok then modified else committed) <$> mt_changed);
    last by (destruct ok; reflexivity).
  iApply (
    big_sepM_fmap (if ok then modified else committed)
  ) in "Hdurable_pointstos".
  iAssert (
    |NC={⊤}=>
      ([∗ map] a ↦ vobj ∈ mt_changed,
        ex_pointsto a ((if ok then modified else committed) vobj)
      ) ∗ (if ok then Qok else Qnok)
  )%I with "[Hex_pointstos Hfupd]" as "> [Hex_pointstos HQ]".
  {
    iDestruct ("Hfupd" with "Hex_pointstos") as "Hfupd".
    destruct ok.
    - iDestruct "Hfupd" as "[> [??] _]".
      iFrame; trivial.
    - iDestruct "Hfupd" as "[_ [??]]".
      iFrame; trivial.
  }
  iModIntro.
  iDestruct (big_sepM_sep with "[$Hex_pointstos $Hdurable_pointstos]")
    as "Hpointstos".
  iSplitL "Hpointstos".
  {
    iApply (big_sepM_impl with "Hpointstos").
    iIntros (a vobj Hacc) "!> [? Hdurable_pointsto]".
    apply Hvalids in Hacc.
    destruct (decide (#ok = #true)) as [Hok|Hok].
    - rewrite decide_True; last by assumption.
      destruct ok; last by inversion Hok.
      iFrame.
      iPureIntro.
      assumption.
    - rewrite decide_False; last by assumption.
      destruct ok; first by contradiction.
      iFrame.
      iPureIntro.
      assumption.
  }
  iSplitR.
  {
    iApply big_sepM_forall.
    iIntros (a vobj Hacc) "!> [? [? %]]".
    iIntros "HC".
    iMod (exchange_durable_pointsto1 with "[$] [$]") as "Hdurable".
    iModIntro. iExists _. iFrame.
    iDestruct ("Htxn_cinv") as "(_&%)".
    iPureIntro. eapply exchange_pointsto_valid; eauto.
  }
  iSplit; first by auto.
  iIntros "Hcrash_invs".

  iApply "HΦ".
  iFrame "Hlocks ∗".
  iApply (
    big_sepM_fmap (if ok then modified else committed)
  ) in "Htokens".
  iDestruct (big_sepM_sep with "[$Htokens $Hcrash_invs]")
    as "Hlinvs".
  iApply big_sepM_dom.
  iApply (big_sepM_impl with "Hlinvs").
  iIntros (a vobj Hacc) "!> [Htoken Hcrash_inv]".
  apply Hvalids in Hacc.
  iExists _.
  iSplit; last by auto.
  iExists _.
  iFrame.
  destruct (decide (#ok = #true)) as [Hok|Hok].
  - rewrite decide_True; last by assumption.
    destruct ok; last by inversion Hok.
    iPureIntro.
    assumption.
  - rewrite decide_False; last by assumption.
    destruct ok; first by contradiction.
    iPureIntro.
    assumption.
Qed.

Theorem wp_Txn__readBufNoAcquire l γ γ' dinit ex_pointsto objs_dom mt_changed a obj (sz: u64) :
  modified <$> (mt_changed !! a) = Some obj →
  bufSz (objKind obj) = uint.nat sz →
  {{{
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed
  }}}
    Txn__readBufNoAcquire #l (addr2val a) #sz
  {{{
    data_s data, RET (slice_val data_s);
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed ∗
    "Hdata_s" ∷ own_slice data_s byteT (DfracOwn 1) data ∗
    "%Hdata" ∷ ⌜data_has_obj data a obj⌝
  }}}.
Proof.
  iIntros (Hlifted Hsz).
  wp_start.
  wp_call.
  iNamed "Htwophase".
  iNamed "Hjrnl".
  wp_loadField.
  apply fmap_Some in Hlifted.
  destruct Hlifted as [vobj [Hvobj ->]].
  iDestruct (big_sepM_lookup_acc with "Hjrnl_maps_tos")
    as "[Hjrnl_maps_to Hjrnl_maps_tos]";
    first by eassumption.
  wp_apply (wp_Op__ReadBuf with "[$Hjrnl_mem $Hjrnl_maps_to]");
    first by assumption.
  iIntros (??) "[Hbuf Hrestore]".
  wp_apply (wp_buf_loadField_data with "Hbuf").
  iIntros (?) "[Hbuf_data Hbuf_without_data]".
  iDestruct (is_buf_data_has_obj with "Hbuf_data")
    as (data) "[Hslice %Hdata]".
  wp_apply (util_proof.wp_CloneByteSlice with "Hslice").
  iIntros (s') "[Hslice Hclone]".
  iDestruct (data_has_obj_to_buf_data with "Hslice") as "Hbuf_data";
    first by eassumption.
  iMod ("Hrestore" with "[Hbuf_data Hbuf_without_data] []")
    as "[Hjrnl_mem Hjrnl_maps_to]";
    [by (iExists _; iFrame)|by intuition|].
  wp_pures.
  iApply "HΦ". iModIntro.
  iFrame (Hdata) "Hclone".
  destruct vobj.
  simpl.
  iDestruct ("Hjrnl_maps_tos" with "Hjrnl_maps_to")
    as "Hjrnl_maps_tos".

  iFrame "Hlocks Hcrash_invs".
  iSplitL "
    Htxn.jrnl Hjrnl_mem Hjrnl_durable_frag Hjrnl_maps_tos
  "; first by iFrame "Hjrnl_mem ∗".
  by iFrame "# %".
Qed.

Theorem wp_Txn__ReadBuf_raw l γ γ' dinit ex_pointsto `{!∀ a obj, Timeless (ex_pointsto a obj)} objs_dom mt_changed a sz :
  a ∈ objs_dom →
  bufSz <$> (
    γ.(jrnl_txn_names).(txn_kinds) !! a.(addrBlock)
  ) = Some (uint.nat sz) →
  {{{
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed
  }}}
    Txn__ReadBuf #l (addr2val a) #sz
  {{{
    data_s data obj mt_changed', RET (slice_val data_s);
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed' ∗
    "Hdata_s" ∷ own_slice data_s byteT (DfracOwn 1) data ∗
    "%Hdata" ∷ ⌜data_has_obj data a obj⌝ ∗
    "%Hobj" ∷ ⌜modified <$> (mt_changed' !! a) = Some obj⌝ ∗
    "%Hmt_changed'" ∷ ⌜
      mt_changed' =
        match mt_changed !! a with
        | Some _ => mt_changed
        | None => <[a:=object_to_versioned obj]>mt_changed
        end
    ⌝
  }}}.
Proof.
  iIntros (Ha_in_dom Hsz).
  wp_start.
  wp_call.
  apply fmap_Some in Hsz.
  destruct Hsz as [kind [Hkind Hsz]].
  wp_apply (wp_Txn__Acquire_lift with "Htwophase"); first by assumption.

  iIntros (obj') "?".
  iNamed.
  iDestruct (is_twophase_raw_get_valid with "Htwophase") as "%Hvalids".
  wp_apply (
    wp_Txn__readBufNoAcquire
    _ _ _ _ _ _ _ _
    (
      match mt_changed !! a with
      | Some vobj' => modified vobj'
      | None => obj'
      end
    )
    with "Htwophase"
  ).
  {
    destruct (mt_changed !! a) as [vobj'|] eqn:Hlookup_old.
    - rewrite Hlookup_old //=.
    - destruct obj'.
      rewrite lookup_insert
        /object_to_versioned /modified /mspec.modified //=.
  }
  {
    rewrite Hsz.
    f_equal.
    destruct (mt_changed !! a) as [vobj'|] eqn:Hlookup_old.
    - apply Hvalids in Hlookup_old.
      destruct Hlookup_old as (_&_&Hkind').
      rewrite Hkind' in Hkind.
      inversion Hkind.
      reflexivity.
    - apply map_Forall_insert_1_1 in Hvalids.
      destruct Hvalids as (_&_&Hkind').
      rewrite Hkind' in Hkind.
      inversion Hkind.
      reflexivity.
  }
  iIntros (??).
  iNamed 1.
  iApply "HΦ".
  iFrame "∗ %".
  iPureIntro.
  destruct (mt_changed !! a) as [vobj'|] eqn:Hlookup_old.
  {
    split; last by reflexivity.
    rewrite Hlookup_old //=.
  }
  split; last by reflexivity.
  destruct obj'.
  rewrite lookup_insert
    /object_to_versioned /modified /mspec.modified //=.
Qed.

Theorem inv_litbyte {ext:ffi_syntax} l1 l2 : LitByte l1 = LitByte l2 -> l1 = l2.
Proof.
  inversion 1; auto.
Qed.

Lemma u8_val_ne (x1 x2:u8) :
  #x1 ≠ #x2 -> uint.Z x1 ≠ uint.Z x2.
Proof.
  intros Hne.
  intros Heq%word.unsigned_inj.
  congruence.
Qed.

Theorem wp_Txn__ReadBufBit l γ γ' dinit ex_pointsto `{!∀ a obj, Timeless (ex_pointsto a obj)} objs_dom mt_changed a :
  a ∈ objs_dom →
  γ.(jrnl_txn_names).(txn_kinds) !! a.(addrBlock) = Some KindBit →
  {{{
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed
  }}}
    Txn__ReadBufBit #l (addr2val a)
  {{{
    b mt_changed', RET #b;
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed' ∗
    "%Hobj" ∷ ⌜
      modified <$> (mt_changed' !! a) = Some (existT _ (bufBit b))
    ⌝ ∗
    "%Hmt_changed'" ∷ ⌜
      mt_changed' =
        match mt_changed !! a with
        | Some _ => mt_changed
        | None =>
          <[a:=object_to_versioned (existT _ (bufBit b))]>mt_changed
        end
    ⌝
  }}}.
Proof.
  intros Ha_in_dom Hkind.
  wp_start.
  wp_call.
  wp_apply (wp_Txn__ReadBuf_raw with "Htwophase").
  1: eassumption.
  1: rewrite Hkind //.
  iIntros (????) "Hpost".
  iNamed "Hpost".
  iDestruct (own_slice_small_read with "Hdata_s")
    as "[Hslice Hslice_restore]".
  iDestruct (is_twophase_raw_get_valid with "Htwophase") as "%Hvalids".
  apply fmap_Some_1 in Hobj as [vobj [Hacc_vobj ->]].
  apply Hvalids in Hacc_vobj as Hvalid.
  destruct Hvalid as (Hvalid_addr&Hvalid_off&Hvalid_γ).
  rewrite Hvalid_γ in Hkind.
  rewrite /data_has_obj in Hdata.
  destruct vobj as [vobj_kind [vobj_c vobj_m]].
  simpl in Hkind.
  simpl in Hdata.
  destruct vobj_m as [b|data'|data'].
  2-3: inversion Hkind.
  destruct Hdata as [data_b [-> Hb]].
  wp_apply (wp_SliceGet (V:=u8) with "[$Hslice]").
  1: trivial.
  iIntros "Hslice".
  wp_pures.
  match goal with
  | |- context[bool_decide ?cond] =>
    replace (bool_decide cond) with b
  end.
  2: {
    subst b.
    match goal with
    | |- context[bool_decide ?cond] =>
      destruct (decide cond) as [Hcond|Hcond]
    end.
    - rewrite bool_decide_eq_true_2; last by assumption.
      rewrite /get_bit -bool_decide_decide bool_decide_eq_true_2;
        first by reflexivity.
      congruence.
    - rewrite bool_decide_eq_false_2; last by assumption.
      rewrite /get_bit -bool_decide_decide bool_decide_eq_false_2;
        first by reflexivity.
      congruence.
  }
  iApply "HΦ".
  iFrame "Htwophase".
  iPureIntro.
  split.
  - rewrite Hacc_vobj //.
  - rewrite Hmt_changed' //.
Qed.

Theorem wp_Txn__OverWrite_raw l γ γ' dinit ex_pointsto `{!∀ a obj, Timeless (ex_pointsto a obj)} objs_dom mt_changed a sz data_s data obj' :
  a ∈ objs_dom →
  γ.(jrnl_txn_names).(txn_kinds) !! a.(addrBlock) = Some (objKind obj') →
  bufSz (objKind obj') = uint.nat sz →
  data_has_obj data a obj' →
  {{{
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed ∗
    "Hdata_s" ∷ own_slice_small data_s byteT (DfracOwn 1) data
  }}}
    Txn__OverWrite #l (addr2val a) #sz (slice_val data_s)
  {{{
    vobj, RET #();
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom (<[a:=vobj]>mt_changed) ∗
    "%Hvobj_committed" ∷ ⌜
      match mt_changed !! a with
      | Some vobj' => committed vobj = committed vobj'
      | None => True
      end
    ⌝ ∗
    "%Hvobj_modified" ∷ ⌜modified vobj = obj'⌝
  }}}.
Proof.
  intros Ha_in_dom Hobj' Hsz Hdata.
  wp_start.
  wp_call.
  wp_apply (wp_Txn__Acquire_lift with "Htwophase");
    first by assumption.
  iIntros (?) "?".
  iNamed.
  iNamed "Htwophase".
  iNamed "Hjrnl".
  wp_loadField.
  destruct (mt_changed !! a) as [vobj'|] eqn:Hlookup_old.
  - iDestruct (big_sepM_delete with "Hjrnl_maps_tos")
      as "[Hjrnl_maps_to Hjrnl_maps_tos]";
      first by eassumption.
    pose proof (Hvalids _ _ Hlookup_old) as (Hvalid_addr&Hvalid_off&Hkind).
    wp_apply (
      wp_Op__OverWrite
      with "[$Hjrnl_mem Hjrnl_maps_to Hdata_s]"
    ); [eassumption|eassumption| |by iFrame|].
    {
      apply Hvalids in Hlookup_old.
      rewrite Hobj' in Hkind.
      inversion Hkind as [Hkind'].
      rewrite /objKind in Hkind'.
      rewrite /sep_jrnl_invariant.objKind Hkind' //=.
    }
    iIntros "[Hjrnl_mem Hjrnl_maps_to]".

    destruct vobj' as [kind [vobj'_c vobj'_m]].
    simpl in Hkind.
    rewrite Hkind in Hobj'.
    inversion Hobj'.
    subst kind.
    wp_pures. iModIntro.
    iApply ("HΦ" $! (
      mspec.mkVersioned vobj'_c (objData obj')
    )).
    iSplit.
    2: {
      iPureIntro.
      destruct obj'.
      rewrite /modified /mspec.modified //=.
    }

    rewrite /is_twophase_raw dom_insert_L subseteq_union_1_L.
    2: {
      apply elem_of_subseteq_singleton.
      apply elem_of_dom.
      eexists _.
      eassumption.
    }
    iFrame "Hlocks".
    iSplitR "Hcrash_invs".
    {
      iExists _,  _, _.
      rewrite fmap_insert insert_id;
        last by rewrite lookup_fmap Hlookup_old //=.
      iFrame.
      rewrite -insert_delete_insert -!(big_sepM_fmap modified) fmap_insert.
      iApply big_sepM_insert;
        first by rewrite lookup_fmap lookup_delete //=.
      iFrame.
      rewrite /modified /mspec.modified /=.
      destruct obj'.
      rewrite //=.
    }
    iSplit.
    {
      rewrite -!(big_sepM_fmap committed) fmap_insert insert_id;
        last by rewrite lookup_fmap Hlookup_old //=.
      iFrame.
    }
    iFrame "#".
    iPureIntro.
    split; last by assumption.
    apply map_Forall_insert_2; last by assumption.
    rewrite /pointsto_valid //.
  - iDestruct (big_sepM_insert with "Hjrnl_maps_tos")
      as "[Hjrnl_maps_to Hjrnl_maps_tos]";
      first by assumption.
    wp_apply (
      wp_Op__OverWrite
      with "[$Hjrnl_mem Hjrnl_maps_to Hdata_s]"
    ); [eassumption|eassumption| |by iFrame|].
    {
      apply map_Forall_insert_1_1 in Hvalids.
      destruct Hvalids as (_&_&Hkind).
      rewrite Hobj' in Hkind.
      inversion Hkind as [Hkind'].
      rewrite /objKind in Hkind'.
      rewrite /sep_jrnl_invariant.objKind Hkind' //=.
    }
    iIntros "[Hjrnl_mem Hjrnl_maps_to]".
    destruct obj as [kind obj].
    destruct obj' as [kind' obj'].
    pose proof (map_Forall_insert_1_1 _ _ _ _ Hvalids) as Hvalid.
    simpl in Hvalid.
    destruct Hvalid as (Hvalid_addr&Hvalid_off&Hkind).
    rewrite Hobj' /= in Hkind.
    inversion Hkind.
    subst kind'.
    wp_pures. iModIntro.
    iApply ("HΦ" $! (mspec.mkVersioned obj obj')).
    iSplit; last by rewrite /modified /mspec.modified //=.

    rewrite /is_twophase_raw !dom_insert_L.
    iFrame "Hlocks".
    iSplitR "Hcrash_invs".
    {
      iExists _, _, _.
      iFrame.
      rewrite -!(big_sepM_fmap modified) !fmap_insert
        /committed /mspec.committed
        /modified /mspec.modified /=.
      iFrame.
      iApply big_sepM_insert.
      {
        rewrite lookup_fmap.
        apply fmap_None.
        assumption.
      }
      iFrame.
    }
    iSplit;
      first by rewrite -!(big_sepM_fmap committed) !fmap_insert
        /committed /mspec.committed //=.
    iFrame "#".
    iPureIntro.
    split; last by assumption.
    apply map_Forall_insert_2; first by rewrite /pointsto_valid //.
    apply map_Forall_insert_1_2 in Hvalids; assumption.
Qed.

Lemma unsigned_U8 z : uint.Z (W8 z) = @word.wrap 8 _ _ z.
Proof.
  unfold W8; rewrite word.unsigned_of_Z; auto.
Qed.

Theorem wp_bitToByte (off: u64) (b: bool) :
  (0 ≤ uint.Z off < 8)%Z →
  {{{
    True
  }}}
    bitToByte #off #b
  {{{
    RET #(W8 (if b then (1 ≪ uint.Z off) else 0));
    True
  }}}.
Proof.
  intros Hoff.
  wp_start.
  wp_call.
  wp_if_destruct.
  2: {
    iApply "HΦ".
    trivial.
  }
  wp_pures.
  assert (
    uint.Z (word.slu (W8 1) (W8 $ uint.Z off)) = uint.Z (W8 (1 ≪ uint.Z off))
  ) as Harith.
  {
    rewrite word.unsigned_slu.
    2: rewrite unsigned_U8 /word.wrap !Z.mod_small; lia.
    rewrite !unsigned_U8 /word.wrap !(Z.mod_small 1); last by lia.
    rewrite !(Z.mod_small (uint.Z off)); last by lia.
    reflexivity.
  }
  apply word.unsigned_inj in Harith.
  rewrite Harith.
  iApply "HΦ".
  trivial.
Qed.

Lemma Z_mod_pos_bound_weak a b bound :
  (0 < b)%Z → (b ≤ bound)%Z → (0 ≤ a `mod` b)%Z ∧ (a `mod` b < bound)%Z.
Proof.
  intros Hb Hbound.
  epose proof (Z.mod_pos_bound _ b Hb) as [Hge Hlt].
  split; first by apply Hge.
  lia.
Qed.

Theorem wp_Txn__OverWriteBit l γ γ' dinit ex_pointsto `{!∀ a obj, Timeless (ex_pointsto a obj)} objs_dom mt_changed a b :
  a ∈ objs_dom →
  γ.(jrnl_txn_names).(txn_kinds) !! a.(addrBlock) = Some KindBit →
  {{{
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom mt_changed
  }}}
    Txn__OverWriteBit #l (addr2val a) #b
  {{{
    vobj, RET #();
    "Htwophase" ∷ is_twophase_raw
      l γ γ' dinit ex_pointsto objs_dom (<[a:=vobj]>mt_changed) ∗
    "%Hvobj_committed" ∷ ⌜
      match mt_changed !! a with
      | Some vobj' => committed vobj = committed vobj'
      | None => True
      end
    ⌝ ∗
    "%Hvobj_modified" ∷ ⌜modified vobj = existT _ (bufBit b)⌝
  }}}.
Proof.
  intros Ha_in_dom Hkind.
  wp_start.
  wp_call.
  wp_apply (wp_NewSlice (V:=u8)).
  iIntros (sl) "Hslice".
  rewrite unsigned_U64 /word.wrap Z.mod_small //=.
  iDestruct (own_slice_small_read with "Hslice")
    as "[Hslice Hslice_restore]".
  wp_apply wp_bitToByte.
  {
    rewrite word.unsigned_modu_nowrap; last by word.
    rewrite unsigned_U64 /word.wrap (Z.mod_small 8); last by lia.
    apply Z.mod_pos_bound.
    lia.
  }
  wp_apply (wp_SliceSet (V:=u8) with "[$Hslice]").
  {
    iPureIntro.
    rewrite unsigned_U64 /word.wrap Z.mod_small //=.
  }
  iIntros "Hslice".
  rewrite unsigned_U64 /word.wrap Z.mod_small //=.
  unshelve (wp_apply (
    wp_Txn__OverWrite_raw _ _ _ _ _ _ _ _ _ _ _
    (existT _ (bufBit b))
    with "[$Htwophase $Hslice]"
  )).
  1: assumption.
  1: assumption.
  1: eassumption.
  1: rewrite //=.
  {
    eexists _.
    split; first by reflexivity.
    rewrite word.unsigned_modu; last by word.
    rewrite (unsigned_U64 8) (wrap_small 8); last by lia.
    rewrite wrap_small;
      last by (apply Z_mod_pos_bound_weak; lia).
    rewrite /get_bit -bool_decide_decide.
    unshelve (erewrite bool_decide_ext).
    4: {
      split.
      - intros Heq.
        apply (f_equal word.unsigned) in Heq.
        apply Heq.
      - intros Heq.
        apply word.unsigned_inj in Heq.
        assumption.
    }
    1: refine _.
    unshelve (erewrite bool_decide_ext).
    4: {
      rewrite word.unsigned_and word.unsigned_modu;
        last by word.
      rewrite unsigned_U64 (wrap_small 8); last by lia.
      unfold word.wrap at 2.
      rewrite (Z.mod_small _ (2^64));
        last by (apply Z_mod_pos_bound_weak; lia).
      rewrite unsigned_U8 wrap_small; last by lia.
      rewrite word.unsigned_sru.
      2: {
        rewrite unsigned_U8 wrap_small;
          last by (apply Z_mod_pos_bound_weak; lia).
        apply Z.mod_pos_bound.
        lia.
      }
      rewrite !unsigned_U8.
      rewrite (wrap_small (_ `mod` _));
        last by (apply Z_mod_pos_bound_weak; lia).
      apply Logic.iff_refl.
    }
    1: refine _.
    destruct b.
    2: {
      rewrite bool_decide_eq_false_2; first by reflexivity.
      rewrite (wrap_small 0); last by lia.
      rewrite Z.shiftr_0_l.
      rewrite (wrap_small 0); last by lia.
      lia.
    }
    rewrite bool_decide_eq_true_2; first by reflexivity.
    rewrite Z.shiftl_1_l Z.shiftr_div_pow2;
      last by apply Z.mod_pos_bound.
    rewrite (wrap_small (2^_)).
    2: {
      split; first by (apply Z.pow_nonneg; lia).
      apply Z.pow_lt_mono_r; [lia|lia|].
      apply Z.mod_pos_bound.
      lia.
    }
    rewrite Z.div_same.
    2: {
      match goal with
      | |- context[(?a ^ ?b)%Z] =>
        unshelve (epose proof (Z.pow_le_mono_r a 0 b _ _) as Hle)
      end.
      1: lia.
      1: apply Z.mod_pos_bound; lia.
      lia.
    }
    rewrite (wrap_small 1); last by lia.
    reflexivity.
  }
  iIntros (?) "Hpost".
  iNamed "Hpost".
  wp_pures. iApply "HΦ".
  by iFrame "∗ %".
Qed.

End proof.
