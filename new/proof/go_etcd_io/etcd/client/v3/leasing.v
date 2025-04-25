From Perennial.base_logic.lib Require Import ghost_map.
Require Import New.code.go_etcd_io.etcd.client.v3.leasing.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.leasing.
Require Import New.generatedproof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.
Require Import New.proof.proof_prelude.
From New.proof Require Import context sync.

Require Import New.proof.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.proof.go_etcd_io.etcd.client.v3.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

(* FIXME: come up with a plan for global addrs of imported packages. *)
Context `{!concurrency.GlobalAddrs}.
Context `{!rpctypes.GlobalAddrs}.
Context `{!leasing.GlobalAddrs}.
Context `{!goGlobalsGS Σ}.

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
  clear ctr g n H2.
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

Definition is_leasingKV (lkv : loc) γ : iProp Σ :=
  ∃ (cl : loc) (ctx : context.Context.t) ctx_st (session : loc),
  "#cl" ∷ lkv ↦s[leasing.leasingKV :: "cl"]□ cl ∗
  "#Hcl" ∷ is_Client cl γ.(etcd_gn) ∗
  "#ctx" ∷ lkv ↦s[leasing.leasingKV::"ctx"]□ ctx ∗
  "#Hctx" ∷ is_Context ctx ctx_st.

(* Half of this goes in the RWMutex. *)
Definition own_leasingKV_monitorSession lkv γ q : iProp Σ :=
  ∃ (session : loc) lease,
  "session" ∷ lkv ↦s[leasing.leasingKV :: "session"]{#q} session ∗
  "#Hsession" ∷ is_Session session γ.(etcd_gn) lease
.

Lemma wp_leasingKV__monitorSession lkv γ :
  {{{
      is_pkg_init leasing ∗
      "#His_kv" ∷ is_leasingKV lkv γ ∗
      "Hown" ∷ own_leasingKV_monitorSession lkv γ (1/2)
  }}}
    lkv @ leasing @ "leasingKV'ptr" @ "monitorSession" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "Hpre". iNamed "Hpre". wp_auto.
  wp_for. iNamed "His_kv". wp_auto. iNamed "Hctx".
  wp_apply "HErr". iIntros (?) "_". wp_pures.
  destruct bool_decide.
  2:{
    rewrite decide_False //; last naive_solver.
    rewrite decide_True //. wp_auto. iApply "HΦ". eauto.
  }
  rewrite decide_True //. wp_auto.
  iNamed "Hown".
  wp_auto. wp_if_destruct.
  2:{ (* not nil *)
    wp_auto.
    wp_apply "HDone".

Qed.

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
  wp_apply (wp_Client__Ctx with "[$]") as "% _".
  iDestruct (is_Client_to_pub with "[$]") as "#Hclient_pub".
  iNamed "Hclient_pub".
  wp_apply (wp_WithCancel with "[$]").
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
  wp_apply (wp_fork with "[Hwg_done1 session_monitor]").
  {
    wp_apply wp_with_defer as "%defer defer".
    simpl subst.
    wp_auto.
    (* TODO: wp_monitorSession. *)
    admit.
  }
  wp_apply (wp_fork with "[Hwg_done2]").
  {
    (* TODO: wp_clearOldRevokes. *)
    admit.
  }
  (* TODO: wp_waitSession. *)
  admit.
Admitted.

End proof.
