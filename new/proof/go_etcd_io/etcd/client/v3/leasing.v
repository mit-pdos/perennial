From Perennial.base_logic.lib Require Import ghost_map.
Require Import New.code.go_etcd_io.etcd.client.v3.leasing.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.leasing.
Require Import New.generatedproof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.
Require Import New.proof.proof_prelude.
From New.proof Require Import context sync.

Require Import New.proof.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.proof.go_etcd_io.etcd.client.v3.

Class leasingG Σ :=
  {
    concurrency_inG :: concurrencyG Σ;
    (* context_inG :: contextG Σ *) (* FIXME: skipped to avoid duplicate [inG]s. *)
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

(* FIXME: come up with a plan for global addrs of imported packages. *)
Context `{!concurrency.GlobalAddrs}.
Context `{!rpctypes.GlobalAddrs}.
Context `{!leasing.GlobalAddrs}.
Context `{!goGlobalsGS Σ}.
Context `{leasingG Σ}.

(* FIXME: move these *)
Program Instance : IsPkgInit bytes :=
  ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit status.status := ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit codes := ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit rpctypes := ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit errors := ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit time := ltac2:(build_pkg_init ()).

Program Instance : IsPkgInit strings := ltac2:(build_pkg_init ()).

#[global]
Program Instance : IsPkgInit leasing := ltac2:(build_pkg_init ()).

Context `{!syncG Σ}.

(* TODO: move this somewhere else *)
Context `{!ghost_mapG Σ nat ()}.
Lemma trivial_WaitGroup_start_done N' wg_ptr γ (N : namespace) ctr :
  (↑N' : coPset) ## ↑N →
  is_WaitGroup wg_ptr γ N ∗ own_WaitGroup γ ctr ={⊤}=∗
  [∗] (replicate (Z.to_nat (sint.Z ctr))
         (∀ Φ, is_pkg_init sync -∗ Φ #() -∗ WP wg_ptr @ sync @ "WaitGroup'ptr" @ "Done" #() {{ Φ }})).
Proof using ghost_mapG0.
  intros HN.
  iIntros "(#His & Hctr)".
  destruct (decide (sint.Z ctr > 0)).
  2:{ rewrite Z2Nat.nonpos // replicate_0 big_sepL_nil //. }
  set (n:=Z.to_nat (sint.Z ctr)).
  unshelve iMod (ghost_map_alloc (gset_to_gmap () (list_to_set $ seq 0 n))) as (γtoks) "[Hm Htoks]".
  iDestruct (big_sepM_gset_to_gmap with "Htoks") as "Htoks".
  iDestruct (big_sepS_list_to_set with "Htoks") as "Htoks".
  { apply NoDup_seq. }
  iMod (inv_alloc N' _ (
            ∃ ctr m,
              "Hctr" ∷ own_WaitGroup γ ctr ∗
              "Hm" ∷ ghost_map_auth γtoks 1 m ∗
              "%Hm" ∷ ⌜ size (dom m) = Z.to_nat (sint.Z ctr) ⌝ ∗
              "%Hctr" ∷ ⌜ sint.Z ctr < 2^32 ⌝
          )%I with "[-Htoks]") as "#Hinv".
  {
    iFrame. iPureIntro.
    rewrite dom_gset_to_gmap.
    rewrite size_list_to_set.
    2:{ apply NoDup_seq. }
    rewrite length_seq.
    subst n. word.
  }
  iModIntro.
  rewrite <- (seq_replicate_fmap 0).
  rewrite big_sepL_fmap.
  iApply (big_sepL_impl with "Htoks []").
  iIntros "!# * % Hx * #Hinit HΦ".
  clear ctr g n H3.
  wp_apply (wp_WaitGroup__Done with "[$]").
  iInv "Hinv" as ">Hi" "Hclose".
  iNamed "Hi".
  iCombine "Hm Hx" gives %Helem.
  destruct (decide (sint.Z ctr > 0)).
  2:{
    exfalso.
    rewrite Z2Nat.nonpos // size_dom in Hm.
    apply map_size_empty_inv in Hm. subst. done.
  }
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iFrame.
  iSplitR.
  { word. }
  iSplitR.
  { iLeft. word. }
  iIntros "_ Hctr". iMod "Hmask" as "_".
  iMod (ghost_map_delete with "[$] [$]") as "Hm".
  iMod ("Hclose" with "[-]").
  {
    iFrame. iPureIntro.
    rewrite dom_delete.
    rewrite size_difference.
    2:{ rewrite singleton_subseteq_l elem_of_dom //. }
    rewrite size_singleton. word.
  }
  done.
Qed.

Record leasingKV_names := {
    etcd_gn : clientv3_names
  }.

Implicit Types γ : leasingKV_names.

(* FIXME: make this a global instance where it's defined?; this is to have contextG
   available here without directly adding it to [leasingG]. *)
Local Existing Instance clientv3_inG.
Local Existing Instance clientv3_contextG.

Definition own_leaseKey (lk : loc) γ (key : go_string) (resp : v3.RangeResponse.t) : iProp Σ :=
  True.

Definition own_leaseCache_locked lc γ q : iProp Σ :=
  ∃ entries_ptr (entries : gmap go_string loc) revokes_ptr (revokes : gmap go_string time.Time.t),
  "entries_ptr" ∷ lc ↦s[leasing.leaseCache :: "entries"]{#q} entries_ptr ∗
  "entries" ∷  own_map entries_ptr (DfracOwn 1) entries ∗
  "Hentries" ∷ ([∗ map] key ↦ lk ∈ entries, ∃ resp, own_leaseKey lk γ key resp) ∗
  "entries_ptr" ∷ lc ↦s[leasing.leaseCache :: "revokes"]{#q} revokes_ptr ∗
  "entries" ∷  own_map revokes_ptr (DfracOwn 1) revokes
  (* TODO: header? *)
.

(* Proposition guarded by [lkv.leases.mu] *)
Definition own_leasingKV_locked lkv (γ : leasingKV_names) q : iProp Σ :=
  let leases := (struct.field_ref_f leasing.leasingKV "leases" lkv) in
  ∃ (sessionc : chan.t) (session : loc),
    "sessionc" ∷ lkv ↦s[leasing.leasingKV :: "sessionc"]{#q} sessionc ∗
    "#Hsessionc" ∷ is_closeable_chan sessionc True ∗
    "session" ∷ lkv ↦s[leasing.leasingKV :: "session"]{#q/2} session ∗
    "#Hsession" ∷ (if decide (session = null) then True else ∃ lease, is_Session session γ.(etcd_gn) lease) ∗
    "Hleases" ∷ own_leaseCache_locked leases γ q
.

(* This is owned by the background thread running [monitorSession]. *)
Definition own_leasingKV_monitorSession lkv γ : iProp Σ :=
  ∃ (session : loc),
  "session" ∷ lkv ↦s[leasing.leasingKV :: "session"]{#(1/2)} session ∗
  "#Hsession" ∷ if decide (session = null) then True else ∃ lease, is_Session session γ.(etcd_gn) lease.

(* Almost persistent. *)
Definition own_leasingKV (lkv : loc) γ : iProp Σ :=
  ∃ (cl : loc) (ctx : context.Context.t) ctx_st,
  "#cl" ∷ lkv ↦s[leasing.leasingKV :: "cl"]□ cl ∗
  "#Hcl" ∷ is_Client cl γ.(etcd_gn) ∗
  "#ctx" ∷ lkv ↦s[leasing.leasingKV::"ctx"]□ ctx ∗
  "#Hctx" ∷ is_Context ctx ctx_st ∗
  "Hmu" ∷ own_RWMutex (struct.field_ref_f leasing.leaseCache "mu" (struct.field_ref_f leasing.leasingKV "leases" lkv))
    (own_leasingKV_locked lkv γ)
.

Lemma wp_optional R e Φ :
  R -∗
  (R -∗ WP e {{ _, R }}) -∗
  (∀ v, R -∗ Φ v) -∗
  WP e {{ Φ }}.
Proof.
  iIntros "HR He HΦ".
  iSpecialize ("He" with "HR").
  iApply (wp_wand with "He").
  iIntros (?) "HR". iApply "HΦ". iFrame.
Qed.

Lemma wp_leasingKV__monitorSession lkv γ :
  {{{
      is_pkg_init leasing ∗
      "Hown_kv" ∷ own_leasingKV lkv γ ∗
      "Hown" ∷ own_leasingKV_monitorSession lkv γ
  }}}
    lkv @ leasing @ "leasingKV'ptr" @ "monitorSession" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "Hpre". iNamed "Hpre". wp_auto.
  wp_for. iNamed "Hown_kv". wp_auto. iNamed "Hctx".
  wp_apply "HErr". iIntros (?) "_". wp_pures.
  destruct bool_decide.
  2:{
    rewrite decide_False //; last naive_solver.
    rewrite decide_True //. wp_auto. iApply "HΦ". eauto.
  }
  rewrite decide_True //. wp_auto.
  iNamed "Hown".
  wp_auto.
  wp_bind (if: _ then _ else _)%E.
  iApply (wp_wand _ _ _ (λ v,
                           (⌜ v = execute_val #tt ⌝ ∨
                                    ⌜ v = return_val #tt ⌝) ∗
                           "session" ∷ _ ↦s[_::_]{#1/2} session ∗ _)%I with "[-]").
  {
    wp_if_destruct.
    { simpl. iFrame "session". iSplitR.
      { by iLeft. }
      iNamedAccu. }
    { (* not nil *)
      rewrite decide_False //. iNamed "Hsession".
      wp_auto.
      wp_apply "HDone".
      wp_bind.
      iApply wp_Session__Done.
      {
        iSplitR.
        { solve_pkg_init. (* FIXME: solve_pkg_init is pretty slow here. *) }
        iFrame "#".
      }
      iNext. iIntros "* #HsessDone".
      wp_auto.
      wp_apply wp_chan_select_blocking.
      rewrite big_andL_cons.
      iSplit.
      2:{
        rewrite big_andL_cons. rewrite big_andL_nil.
        iSplit; last done.
        repeat iExists _.
        iApply (closeable_chan_receive with "HDone_ch").
        iIntros "_". simpl. wp_auto. iFrame. by iRight.
      }
      repeat iExists _.
      iApply (closeable_chan_receive with "HsessDone").
      iIntros "_". wp_auto. iFrame. by iLeft.
    }
  }
  iIntros "* ([%|%] & H)"; subst; iNamed "H".
  2:{ wp_auto. wp_for_post. by iApply "HΦ". }
  wp_auto.
  wp_apply (wp_RWMutex__Lock with "[$Hmu]").
  iIntros "[Hmu Hown]".
  wp_auto.
  wp_bind (chan.select _ _).
  iApply (wp_optional with "[-]"); first iNamedAccu.
  {
    iNamed 1. iNamedSuffix "Hown" "_lock". wp_auto.
    wp_apply (wp_chan_select_nonblocking [False%I]).
    repeat iSplit.
    - rewrite big_opL_singleton.
      repeat iExists _.
      (*
      iApply (closeable_chan_receive with "[$]"). iIntros "_".
      wp_auto. wp_apply (wp_chan_make (V:=unit)). iIntros "* Hsessionc'".
      iMod (alloc_closeable_chan True with "[$]") as "[H ?]"; [done..|].
      wp_auto. iFrame "∗#%". *)
      admit.
    - (* default *) iIntros "Hnr". wp_auto. iFrame "∗#%".
  }
Admitted.

Lemma wp_NewKV cl γetcd (pfx : go_string) opts_sl :
  {{{
      is_pkg_init leasing ∗
      "#Hcl" ∷ is_Client cl γetcd ∗
      "Hopts_sl"  ∷ opts_sl ↦* ([] : list concurrency.SessionOption.t)
  }}}
    leasing @ "NewKV" #cl #pfx #opts_sl
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply (wp_Client__Ctx with "[$]") as "* #Hclient_ctx".
  iDestruct (is_Client_to_pub with "[$]") as "#Hclient_pub".
  iNamed "Hclient_pub".
  wp_apply (wp_WithCancel with "Hclient_ctx").
  iIntros "* #(Hctx' & Hcancel_spec & Hctx_done)".
  wp_auto.
  unshelve wp_apply wp_map_make as "%revokes Hrevokes"; try tc_solve; try tc_solve.
  { done. }
  unshelve wp_apply wp_chan_make as "* ?"; try tc_solve.
  wp_alloc lkv as "Hlkv".
  wp_auto.
  iDestruct (struct_fields_split with "Hlkv") as "Hl".
  iEval (simpl) in "Hl".
  iRename "Hcl" into "#Hcl_in".
  iNamed "Hl".
  iMod (init_WaitGroup (nroot .@ "wg") with "[$]") as (γwg) "(#Hwg_is & Hwg_ctr & Hwg_wait)".
  wp_apply (wp_WaitGroup__Add with "[]").
  { iFrame "#". }
  iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask"].
  iFrame "Hwg_ctr Hwg_wait".
  iSplitR.
  { word. }
  iIntros "[%Hbad|Hwg_wait] Hwg_ctr".
  { by exfalso. }
  iMod "Hmask" as "_". iModIntro.
  wp_auto.
  replace (word.add _ (W32 (uint.Z (W64 2)))) with (W32 2) by word.

  (* monitorSession is the only thread that modifies `lkv.session`. *)
  iDestruct "Hsession" as "[session session_monitor]".
  iPersist "lkv".
  iMod (trivial_WaitGroup_start_done (nroot .@ "done") with "[$]") as "H".
  { solve_ndisj. }
  replace (Z.to_nat (sint.Z (W32 2))) with (2%nat) by done.
  iEval (simpl) in "H".
  iDestruct "H" as "[Hwg_done1 Hwg_done2]".

  iPersist "Hcl Hkv Hctx".
  iDestruct (struct_fields_split with "Hleases") as "H".
  iNamed "H".
  (*
  iDestruct (init_RWMutex with "[] [Hleases Hcancel HsessionOpts session Hsessionc Hwg_wait] [$]") as "H".
  iAssert (own_leasingKV lkv ltac:(econstructor)) with "[-]" as "Hlkv".
  { iFrame "∗#". }

  wp_apply (wp_fork with "[Hwg_done1 session_monitor]").
  {
    wp_apply wp_with_defer as "%defer defer".
    simpl subst.
    wp_auto.
    wp_bind.
    Time iApply (wp_leasingKV__monitorSession with "[session_monitor]").
    {
      (* iFrame. iFrame "#". *)
      iSplitR.
      { Time solve_pkg_init. (* FIXME: solve_pkg_init is pretty slow here. *) }
      (* ~13 seconds. *)
      iFrame "∗#".
    }
    iNext. iIntros "_". wp_auto.
    wp_apply "Hwg_done1".
    { admit. (* FIXME: [is_pkg_init] got unfolded.... *) }
    done.
  }
  wp_apply (wp_fork with "[Hwg_done2]").
  {
    (* TODO: wp_clearOldRevokes. *)
    admit.
  }
  (* TODO: wp_waitSession. *)
  admit. *)
Admitted.

End proof.
