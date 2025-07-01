From Perennial.base_logic.lib Require Import ghost_map.
Require Import New.code.go_etcd_io.etcd.client.v3.leasing.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.leasing.
Require Import New.generatedproof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.
Require Import New.proof.proof_prelude.
From New.proof Require Import context sync.

Require Import New.proof.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.proof.go_etcd_io.etcd.client.v3.
From Perennial.algebra Require Import ghost_var.
Require Import Perennial.base.


Class leasingG Σ :=
  {
    concurrency_inG :: concurrencyG Σ;
    (* context_inG :: contextG Σ *) (* FIXME: skipped to avoid duplicate [inG]s. *)
    entries_ready_inG :: ghost_varG Σ bool;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

(* FIXME: come up with a plan for global addrs of imported packages. *)
Context `{!etcdserverpb.GlobalAddrs}.
Context `{!concurrency.GlobalAddrs}.
Context `{!rpctypes.GlobalAddrs}.
Context `{!leasing.GlobalAddrs}.
Context `{!goGlobalsGS Σ}.
Context `{leasingG Σ}.

(* FIXME: move these *)

#[global]
Program Instance is_pkg_init_bytes : IsPkgInit bytes := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_bytes.

#[global]
Program Instance is_pkg_init_status : IsPkgInit status.status := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_status.

#[global]
Program Instance is_pkg_init_codes : IsPkgInit codes := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_codes.

#[global]
Program Instance is_pkg_init_rpctypes : IsPkgInit rpctypes := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_rpctypes.

#[global]
Program Instance is_pkg_init_strings : IsPkgInit strings := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_strings.

#[global]
Program Instance is_pkg_init_leasing : IsPkgInit leasing := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_leasing.
#[local] Transparent is_pkg_init_leasing.

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
  iIntros "!# * %Hlook Hx * #Hinit HΦ".
  clear ctr g n Hlook.
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
    etcd_gn : clientv3_names;
    entries_ready_gn : gname;
  }.

Implicit Types γ : leasingKV_names.

(* FIXME: make this a global instance where it's defined?; this is to have contextG
   available here without directly adding it to [leasingG]. *)
Local Existing Instance clientv3_inG.
Local Existing Instance clientv3_contextG.

Definition own_leaseKey (lk : loc) γ (key : go_string) (resp : RangeResponse.t) : iProp Σ :=
  True.

Definition own_leaseCache_locked lc γ q : iProp Σ :=
  ∃ entries_ptr (entries : gmap go_string loc) revokes_ptr (revokes : gmap go_string time.Time.t)
    (entries_ready : bool),
  "entries_ptr" ∷ lc ↦s[leasing.leaseCache :: "entries"]{#q} entries_ptr ∗
  "entries" ∷ (if entries_ready then entries_ptr ↦$ entries else ⌜ entries_ptr = null ∧ entries = ∅ ⌝
    ) ∗
  "Hentries" ∷ ([∗ map] key ↦ lk ∈ entries, ∃ resp, own_leaseKey lk γ key resp) ∗
  "revokes_ptr" ∷ lc ↦s[leasing.leaseCache :: "revokes"]{#q} revokes_ptr ∗
  "revokes" ∷  revokes_ptr ↦$ revokes ∗
  "Hentries_ready" ∷ ghost_var γ.(entries_ready_gn)
                                (if entries_ready then DfracDiscarded else (DfracOwn 1)) entries_ready
  (* TODO: header? *)
.

Definition is_entries_ready γ := ghost_var γ.(entries_ready_gn) DfracDiscarded true.

(* Proposition guarded by [lkv.leases.mu] *)
Local Definition own_leasingKV_locked lkv (γ : leasingKV_names) q : iProp Σ :=
  let leases := (struct.field_ref_f leasing.leasingKV "leases" lkv) in
  ∃ (sessionc : chan.t) (session : loc),
    "sessionc" ∷ lkv ↦s[leasing.leasingKV :: "sessionc"]{#q/2} sessionc ∗
    "#Hsessionc" ∷ own_closeable_chan sessionc (is_entries_ready γ) closeable.Unknown ∗
    "session" ∷ lkv ↦s[leasing.leasingKV :: "session"]{#q/2} session ∗
    "#Hsession" ∷ (if decide (session = null) then True else ∃ lease, is_Session session γ.(etcd_gn) lease) ∗
    "Hleases" ∷ own_leaseCache_locked leases γ q.

(* This is owned by the background thread running [monitorSession]. *)
Local Definition own_leasingKV_monitorSession lkv γ : iProp Σ :=
  ∃ (session : loc) sessionc (open : bool),
  "session" ∷ lkv ↦s[leasing.leasingKV :: "session"]{#(1/2)} session ∗
  "#Hsession" ∷ (if decide (session = null) then True else ∃ lease, is_Session session γ.(etcd_gn) lease) ∗
  "sessionc" ∷ lkv ↦s[leasing.leasingKV :: "sessionc"]{#(1/2)} sessionc ∗
  "Hsessionc" ∷ own_closeable_chan sessionc (is_entries_ready γ) (if open then closeable.Open else closeable.Closed).

(* Almost persistent. *)
Definition own_leasingKV (lkv : loc) γ : iProp Σ :=
  ∃ (cl : loc) (ctx : context.Context.t) ctx_st,
  "#cl" ∷ lkv ↦s[leasing.leasingKV :: "cl"]□ cl ∗
  "#Hcl" ∷ is_Client cl γ.(etcd_gn) ∗
  "#ctx" ∷ lkv ↦s[leasing.leasingKV::"ctx"]□ ctx ∗
  "#Hctx" ∷ is_Context ctx ctx_st ∗
  "#session_opts" ∷ lkv ↦s[leasing.leasingKV :: "sessionOpts"]□ slice.nil ∗
  "Hmu" ∷ own_RWMutex (struct.field_ref_f leasing.leaseCache "mu" (struct.field_ref_f leasing.leasingKV "leases" lkv))
    (own_leasingKV_locked lkv γ).
#[global] Opaque own_leasingKV.
#[local] Transparent own_leasingKV.

Instance own_leasingKV_locked_frac lkv γ : fractional.Fractional (own_leasingKV_locked lkv γ).
Proof. Admitted.

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
  wp_apply "HErr"; first iFrame "#". iIntros (?) "_". wp_pures.
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
      wp_apply "HDone". wp_auto.
      wp_apply wp_Session__Done.
      { iFrame "#". }
      iIntros "* #HsessDone".
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
  iNamedSuffix "Hown" "_lock".
  iCombine "sessionc_lock sessionc" gives %[_ Heq]. subst.
  iCombine "sessionc_lock sessionc" as "sessionc".
  wp_apply (wp_wand _ _ _
              (λ v,
                 ∃ sessionc,
                   ⌜ v = execute_val #tt ⌝ ∗
                   "sessionc" ∷ _ ↦s[_::_] sessionc ∗
                   "Hsessionc" ∷ own_closeable_chan sessionc (is_entries_ready γ) closeable.Open ∗
                   "lkv" ∷ lkv_ptr ↦ lkv
              )%I
              with "[Hsessionc sessionc lkv]"
           ).
  {
    wp_apply (wp_chan_select_nonblocking [⌜ open = true ⌝]%I).
    { reflexivity. }
    repeat iSplit.
    { rewrite big_opL_singleton.
      repeat iExists _.
      iApply (own_closeable_chan_nonblocking_receive with "[$]").
      destruct open.
      - iSplit; first done.
        iIntros "Ho". done.
      - iSplit; last done. iIntros "_".
        wp_auto. unshelve wp_apply (wp_chan_make (V:=unit)); try tc_solve. iIntros "* Hch".
        iMod (alloc_closeable_chan with "[$Hch]") as "H"; [done.. | ].
        wp_auto. iFrame. done.
    }
    { iIntros "[% _]". subst. wp_auto. iFrame. done. }
  }
  iClear "Hsessionc_lock". clear sessionc.
  iIntros "* (% & % & H)". subst. wp_auto. iNamed "H".
  wp_apply (wp_map_make (K:=go_string) (V:=loc)); [done..|].
  iNamedSuffix "Hleases_lock" "_leases".
  iIntros "* entries_new_leases".
  wp_auto.
  iDestruct (own_closeable_chan_Unknown with "[$]") as "#?".
  iDestruct "sessionc" as "[sessionc sessionc_lock]".

  iAssert (|==> "#Hentries_ready" ∷ ghost_var γ.(entries_ready_gn) DfracDiscarded true)%I
    with "[Hentries_ready_leases entries_leases]"as ">#Hentries_ready".
  {
    destruct entries_ready.
    { by iFrame "∗#". }
    iMod (ghost_var_update with "[$]") as "H".
    iMod (ghost_var_persist with "[$]") as "H".
    iFrame "H". done.
  }
  iClear "Hentries_leases".
  iCombineNamed "*_leases" as "Hleases_lock".
  iCombineNamed "*_lock" as "H".
  wp_apply (wp_RWMutex__Unlock with "[H Hmu]").
  {
    iNamed "H". iFrame "∗#%". iNamed "Hleases_lock".
    iFrame "∗#". iExists ∅, true. iFrame "∗#". iApply big_sepM_empty. done.
  }
  iIntros "Hmu".
  wp_auto.
  wp_apply wp_NewSession.
  { iFrame "#". }
  iIntros "* #Hsession_new". wp_auto.
  wp_if_destruct.
  { (* got a valid session *)
    rewrite (decide_True _ _ eq_refl).
    rewrite bool_decide_true //.
    wp_auto. wp_apply (wp_RWMutex__Lock with "[$Hmu]").
    iIntros "[Hmu Hown]". wp_auto.
    iClear "Hsession_lock".
    iNamedSuffix "Hown" "_lock".
    iCombine "session_lock session" gives %[_ Heq]. subst.
    iCombine "session_lock session" as "session".
    iCombine "sessionc_lock sessionc" gives %[_ Heq]. subst.
    wp_auto.
    wp_apply (wp_closeable_chan_close with "[$Hsessionc]").
    { done. }
    iIntros "#Hclosed".
    wp_auto.
    iDestruct "session" as "[session session_lock]".
    iCombineNamed "*_lock" as "H".
    wp_apply (wp_RWMutex__Unlock with "[$Hmu H]").
    { iNamed "H". iFrame "∗#%". destruct (decide (s = null)); done. }
    iIntros "Hmu".
    wp_auto.
    wp_for_post.
    iFrame "∗#%". iExists false.
    iFrame "#". destruct (decide (s = null)); done.
  }
  { (* not a valid session. *)
    rewrite bool_decide_false //. wp_auto. wp_for_post.
    iFrame "∗#%". iExists true. iFrame.
  }
Qed.

Definition own_leaseCache (lc : loc) γ : iProp Σ :=
  ∃ P,
  "Hmu" ∷ own_RWMutex (struct.field_ref_f leasing.leaseCache "mu" lc) P ∗
  "#HP" ∷ □(∀ q, P q -∗ own_leaseCache_locked lc γ q ∗ (own_leaseCache_locked lc γ q -∗ P q)).

(* FIXME: move to `time` *)
(* 1.23 model: chan is unbuffered. *)
Lemma wp_After (d : time.Duration.t) :
  {{{ is_pkg_init time }}}
    time @ "After" #d
  {{{
        ch, RET #ch;
        is_chan time.Time.t ch ∗
        (* Q: is it OK for the user to send on this channel? *)
        inv nroot (∃ (st : chanstate.t time.Time.t), own_chan ch st ∗
                         (⌜ st.(chanstate.cap) = 0 ∧
                            st.(chanstate.closed) = false ⌝)
          )
  }}}.
Proof.
Admitted.

Lemma wp_leaseCache__clearOldRevokes lc γ ctx ctx_desc :
  {{{ is_pkg_init leasing ∗ own_leaseCache lc γ ∗ is_Context ctx ctx_desc }}}
    lc @ leasing @ "leaseCache'ptr" @ "clearOldRevokes" #ctx
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[Hlc #Hctx]". wp_auto.
  wp_for.
  wp_apply wp_After.
  iIntros (after_ch) "#[after_ch Hafter_ch]".
  wp_auto.
  iNamed "Hctx".
  wp_apply "HDone". wp_auto.
  wp_apply wp_chan_select_blocking.
  rewrite big_andL_cons.
  iSplit.
  { repeat iExists _.
    iApply closeable_chan_receive.
    { iExactEq "HDone_ch".
      f_equal.
      admit. (* FIXME: another duplicate [inG] problem *) }
    iIntros "_". wp_auto. wp_for_post. iApply "HΦ". done. }
  rewrite big_andL_cons big_andL_nil.
  iSplit; last done. repeat iExists _.
  iFrame "#". iInv "Hafter_ch" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hafter_ch_own %Hafter_ch]".
  iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
  iExists _; iFrame. rewrite decide_False.
  2:{ destruct Hafter_ch. apply not_and_r. left. congruence. }
  iNext. iIntros "Hafter_ch_own".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hafter_ch_own]") as "_". { iFrame "∗%". }
  iModIntro. clear Hafter_ch.
  iInv "Hafter_ch" as ">Hi" "Hclose".
  iDestruct "Hi" as (?) "[Hafter_ch_own %Hafter_ch]".
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iFrame. iNext. iIntros (t) "_ Hafter_ch_own".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hafter_ch_own]") as "_". { iFrame "∗%". }
  iModIntro. wp_auto. iNamed "Hlc".
  wp_apply (wp_RWMutex__Lock with "[$Hmu]").
  iIntros "[Hlocked Hown]". wp_auto.
  iDestruct ("HP" with "Hown") as "[Hown HcloseP]". iNamed "Hown".
  wp_auto.
  (* Search map.for_range. *)
  (* FIXME: need reasoning principle for [map.for_range] *)
  admit.
Admitted.

Definition num_lkvs : Z := rwmutex.actualMaxReaders - 2.
Local Hint Unfold num_lkvs : word.

Program Definition own_RWMutex_sealed := sealed own_RWMutex.

(* FIXME: how to avoid this?
   This removes [name :: _] in the goal when trying to frame.

   This has lower cost than [frame_here] because [frame_here] causes unification
   between [name :: Q] and [Q], which sometimes hangs. This instance tries to
   immediately get rid of [named] before recursively looking for a [Frame]
   instance.

   Q: [frame_here_absorbing] has the same cost, so why doesn't that get applied
   first and cause the same problem?
*)
Instance frame_named {PROP : bi} p (P Q R : PROP) name :
  Frame p P Q R → Frame p P (name ∷ Q) R | 0.
Proof. unfold named. done. Qed.

Lemma wp_leasingKV__waitSession lkv ctx ctx_desc γ :
  {{{ is_pkg_init leasing ∗ own_leasingKV lkv γ ∗ is_Context ctx ctx_desc }}}
    lkv @ leasing @ "leasingKV'ptr" @ "waitSession" #ctx
  {{{ err, RET #err;
      own_leasingKV lkv γ ∗
      if decide (err = interface.nil) then ghost_var γ.(entries_ready_gn) DfracDiscarded true
      else True
  }}}.
Proof.
  wp_start as "[Hlkv #Hctx_in]". wp_auto. iNamedSuffix "Hlkv" "_lkv".
  wp_apply (wp_RWMutex__RLock with "[$Hmu_lkv]").
  iIntros "[Hrlocked Hown]". wp_auto. iNamedSuffix "Hown" "_rlock".
  wp_auto. iCombineNamed "*_rlock" as "H".
  wp_apply (wp_RWMutex__RUnlock with "[$Hrlocked H]").
  { iNamed "H". iFrame "∗#". }
  iIntros "Hmu_lkv".
  wp_auto.
  iNamed "Hctx_in".
  wp_apply "HDone". wp_auto.
  iNamedSuffix "Hctx_lkv" "_lkv".
  wp_apply "HDone_lkv". wp_auto.
  wp_apply wp_chan_select_blocking.
  rewrite !big_andL_cons big_andL_nil right_id.
  iSplit.
  {
    repeat iExists _.
    iApply closeable_chan_receive. { iFrame "#". }
    iIntros "#[Hready Hclosed]".
    wp_auto. iApply "HΦ". rewrite (decide_True (P:=interface.nil = _)) //.
    iFrame "∗#".
  }
  iSplit.
  {
    repeat iExists _.
    iApply (closeable_chan_receive (closeable_chanG0:=clientv3_contextG.(closeable_inG))
             with "[$HDone_ch_lkv]"). (* FIXME: multiple [inG]s *)
    iIntros "[_ #Hclosed]". wp_auto. wp_apply ("HErr_lkv" with "[$Hclosed]").
    iIntros "* %Herr". wp_auto. iApply "HΦ".
    rewrite (decide_False (P:=err = interface.nil)) //. iFrame "∗#".
  }
  {
    repeat iExists _.
    iApply (closeable_chan_receive (closeable_chanG0:=clientv3_contextG.(closeable_inG))
             with "[$HDone_ch]"). (* FIXME: multiple [inG]s *)
    iIntros "[_ #Hclosed]". wp_auto. wp_apply ("HErr" with "[$Hclosed]").
    iIntros "* %Herr". wp_auto. iApply "HΦ".
    rewrite (decide_False (P:=err = interface.nil)) //. iFrame "∗#".
  }
Qed.

(* Requires no options. *)
Definition own_KV (kv : interface.t) (γetcd : clientv3_names) : iProp Σ :=
  "#HPut" ∷ (∀ (ctx : context.Context.t) (key v : go_string),
               {{{ True }}}
                 interface.get "Put" #kv #ctx #key #v #slice.nil
               {{{ (resp : loc) (err : error.t), RET (#resp, #err); True }}}) ∗
  "#HGet" ∷ (∀ (ctx : context.Context.t) (key : go_string),
               {{{ True }}}
                 interface.get "Get" #kv #ctx #key #slice.nil
               {{{ (resp : loc) (err : error.t), RET (#resp, #err); True }}})

  (* Put(ctx context.Context, key, val string, opts ...OpOption) (PutResponse, error) *)
  (* Put, Get *)
.

Lemma wp_leasingKV__Put lkv ctx ctx_desc (key v : go_string) γ :
  {{{ is_pkg_init leasing ∗ is_Context ctx ctx_desc ∗ own_leasingKV lkv γ }}}
    lkv@leasing@"leasingKV'ptr"@"Put" #ctx #key #v #slice.nil
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[#Hctx Hlkv]". wp_auto.
  (* TODO: spec for `OpPut` *)
  (* NOTE: put() is called in two different places, so it should have its own spec.
     Also, it's only ever call
   *)
  wp_apply wp_OpPut. iIntros "* #Hop".
  wp_auto.
Admitted.

Lemma wp_leasingKV__put ctx ctx_desc lkv γ op put_req :
  {{{ is_pkg_init leasing ∗
      "#Hctx" ∷ is_Context ctx ctx_desc ∗
      "Hlkv" ∷ own_leasingKV lkv γ ∗
      "#Hop" ∷ is_Op op (Op.Put put_req)
  }}}
    lkv@leasing@"leasingKV'ptr"@"put" #ctx #op
  {{{
      (pr_ptr : loc) (err : error.t), RET (#pr_ptr, #err);
        if decide (err = interface.nil) then
          False
        else
          True
  }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  wp_alloc errs_ptr as "errs". wp_auto.
  wp_apply (wp_leasingKV__waitSession with "[$Hlkv]").
  { iFrame "#". }
  iIntros "* [Hlkv Hready]".
  wp_auto. wp_if_destruct.
  2:{
    rewrite bool_decide_false; last done.
    wp_auto. iApply "HΦ". rewrite !decide_False //.
  }
  rewrite bool_decide_decide !decide_True //.
  iDestruct "Hready" as "#Hready".
  wp_auto. wp_for.
  iPoseProof "Hctx" as "Hctx2".
  iNamedSuffix "Hctx2" "_ctx".
  wp_apply "HErr_ctx".
  { iFrame "#". }
  iIntros (?) "Herr".
  wp_auto.
  wp_if_destruct.
  2:{
    rewrite bool_decide_decide !decide_False //. wp_auto.
    wp_apply ("HErr_ctx" with "[$Herr]"). iIntros (?) "%Herr". wp_auto.
    iApply "HΦ". rewrite !decide_False //.
  }
  rewrite bool_decide_decide !decide_True //. wp_auto.
  rename err_ptr into outer_err_ptr. iRename "err" into "outer_err".
  wp_auto.
  (* wp_apply wp_leasingKV__tryModifyOp. *)
Admitted.

Lemma wp_leasingKV__tryModifyOp ctx ctx_desc op o lkv γ :
  {{{ is_pkg_init leasing ∗
      "#Hctx" ∷ is_Context ctx ctx_desc ∗
      "#Hop" ∷ is_Op op o ∗
      "Hlkv" ∷ own_leasingKV lkv γ
  }}}
    lkv@leasing@"leasingKV'ptr"@"tryModifyOp" #ctx #op
  {{{
      (resp_ptr : loc) (wc : chan.t) err, RET (#resp_ptr, #wc, #err);
        if decide (err = interface.nil) then
          True
        else
          True
  }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  (* FIXME: Op__KeyBytes *)
Admitted.

(* FIXME: [own_leasingKV] should contain [is_entries_ready]. Can have a special
   version that doesn't have [is_entries_ready] for the goroutines kicked off
   inside [NewKV]. *)
Lemma own_leasingKV_own_KV lkv γ :
  is_entries_ready γ -∗
  own_leasingKV lkv γ -∗
  own_KV (interface.mk (leasing, "leasingKV'ptr"%go) #lkv) γ.(etcd_gn).
Proof.
Admitted.

(* FIXME: tie γetcd to γ. *)
Lemma wp_NewKV cl γetcd (pfx : go_string) :
  {{{
      is_pkg_init leasing ∗
      "#Hcl" ∷ is_Client cl γetcd
  }}}
    leasing @ "NewKV" #cl #pfx #slice.nil
  {{{ kv (close : func.t) err, RET (#kv, #close, #err);
      if decide (err = interface.nil) then
        [∗] replicate (Z.to_nat num_lkvs) (own_KV kv γetcd)
        (* {{{ True }}} #close #() {{{ RET #(); True }}} *) (* FIXME: need to have own_leasingKV for this, so not persistent.... *)
      else True
  }}}.
Proof using Type*.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply (wp_Client__Ctx with "[$]") as "* #Hclient_ctx".
  wp_auto.
  iDestruct (is_Client_to_pub with "[$]") as "#Hclient_pub".
  iNamed "Hclient_pub".
  wp_apply (wp_WithCancel True with "Hclient_ctx").
  iIntros "* #[Hcancel_fn Hctx']".
  wp_auto.
  unshelve wp_apply wp_map_make as "%revokes revokes"; try tc_solve; try tc_solve.
  { done. }
  wp_auto. wp_apply (wp_chan_make (V:=unit)) as "* ?".
  wp_auto. wp_alloc lkv as "Hlkv".
  wp_auto.
  iDestruct (struct_fields_split with "Hlkv") as "Hl".
  iEval (simpl) in "Hl".
  iRename "Hcl" into "Hcl_in".
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
  iDestruct "H" as "(Hwg_done1 & Hwg_done2 & _)".

  iPersist "Hcl Hkv Hctx HsessionOpts".
  iDestruct (struct_fields_split with "Hleases") as "H".
  iEval (simpl) in "H".
  iNamed "H".
  iDestruct "Hsessionc" as "[sessionc sessionc_monitor]".
  iMod (ghost_var_alloc false) as (γready) "Hentries_ready".
  iMod (alloc_closeable_chan with "[$]") as "Hopen_monitor"; [done.. | ].
  iDestruct (own_closeable_chan_Unknown with "[$]") as "#?".

  iMod (init_RWMutex
          (own_leasingKV_locked lkv {| etcd_gn := γetcd; entries_ready_gn := γready |} )
         with "[] [Hentries_ready Hentries Hrevokes Hcancel HsessionOpts session sessionc Hwg_wait revokes] [$]") as "Hmus".
  {
    iIntros "!# *". rewrite fractional.fractional //.
    iDestruct equiv_wand_iff as "$". done.
  }
  { iFrame "∗#%". iExists ∅, false. iFrame. iSplit; first done.
    iApply big_sepM_empty. done. }

  replace (rwmutex.actualMaxReaders) with (1 + 1 + num_lkvs).
  2:{ unfold num_lkvs. word. }
  rewrite Z2Nat.inj_add //.
  rewrite -> replicate_add.
  iDestruct ("Hmus") as "[Hmu Hmus]".
  iDestruct "Hmu" as "(Hmu1 & Hmu2 & _)".
  iAssert (own_leasingKV lkv ltac:(econstructor)) with "[Hmu1]" as "Hlkv".
  { Time iFrame "Hcl". Time iFrame "∗#". }
  iAssert (own_leaseCache (struct.field_ref_f leasing.leasingKV "leases" lkv) ltac:(econstructor))
            with "[Hmu2]" as "Hlc".
  { iFrame "Hmu2". iClear "#". iIntros "!# *". iNamed 1. iFrame. iIntros "H". iFrame "∗#". }

  iCombineNamed "*_monitor" as "Hmonitor".
  wp_apply (wp_fork with "[Hwg_done1 Hmonitor Hlkv]").
  {
    wp_auto. wp_apply wp_with_defer as "%defer defer".
    simpl subst.
    wp_auto.
    wp_apply (wp_leasingKV__monitorSession with "[Hmonitor Hlkv]").
    { iNamed "Hmonitor". iFrame. iExists true. iFrame. }
    (*
      iSplitL "Hlkv".
      {
        iApply to_named.
        Fail Timeout 4 set (x:= _ : (Frame false (own_leasingKV lkv {| etcd_gn := γetcd; entries_ready_gn := γready |})
           ("Hown_kv" ∷ own_leasingKV lkv _) _)).

        Opaque own_leasingKV.
        set (x := (λ y, ⌜ y = O⌝%I : iProp Σ)).

        Definition own_leasingKV2 (lkv : loc) γ : iProp Σ :=
          ∃ (cl : loc) (ctx : context.Context.t) ctx_st,
            "#cl" ∷ lkv ↦s[leasing.leasingKV :: "cl"]□ cl ∗
            "#Hcl" ∷ is_Client cl γ.(etcd_gn) ∗
            "#ctx" ∷ lkv ↦s[leasing.leasingKV::"ctx"]□ ctx ∗
            "#Hctx" ∷ is_Context ctx ctx_st ∗
            "#session_opts" ∷ lkv ↦s[leasing.leasingKV :: "sessionOpts"]□ slice.nil ∗
            "Hmu" ∷ own_RWMutex (struct.field_ref_f leasing.leaseCache "mu" (struct.field_ref_f leasing.leasingKV "leases" lkv))
              (own_leasingKV_locked lkv γ).

        Time eunify
          (named "ok" (own_leasingKV2 lkv {| etcd_gn := γetcd; entries_ready_gn := γready |}))
          (named "ok" (own_leasingKV2 lkv _)). (* Slow *)
        Time eunify
          ("other" ∷ own_leasingKV lkv {| etcd_gn := γetcd; entries_ready_gn := γready |})
          ("1" ∷ own_leasingKV lkv _). (* Slow *)
        Time eunify
          (own_leasingKV2 lkv {| etcd_gn := γetcd; entries_ready_gn := γready |})
          (own_leasingKV2 lkv _). (* Fast *)
        (* FIXME: sealing allows unification to suceed, albeit still kinda slowly. *)
        eunify
          ("other" ∷ own_leasingKV2 lkv {| etcd_gn := γetcd; entries_ready_gn := γready |})
            (own_leasingKV2 lkv _).

        iFrame "Hlkv".
        iExact "Hlkv".

        Set Typeclasses Debug.
        Set Debug "tactic-unification".
        (* FIXME: iFrame timing out. *)
        (*
        iFrame "Hlkv". iApply to_named. iExactEq "Hlkv". done. }
      Fail Timeout 10 iFrame "Hlkv".
      (* iFrame. iFrame "#". *)
      iSplitR.
      { Time solve_pkg_init. (* FIXME: solve_pkg_init is pretty slow here. *) }
      (* ~13 seconds. *)
      iFrame "∗#". *)
    } *)
    wp_auto. wp_apply "Hwg_done1".
    wp_auto. done.
  }
  iPersist "cctx".
  wp_auto. wp_apply (wp_fork with "[Hwg_done2 Hlc]").
  {
    wp_auto. wp_apply wp_with_defer as "%defer defer".
    simpl subst.
    wp_auto.
    wp_apply (wp_leaseCache__clearOldRevokes with "[Hlc]").
    { iFrame "Hlc Hctx'". }
    wp_auto. wp_apply "Hwg_done2".
    wp_auto. done.
  }

  replace (num_lkvs) with (1 + (num_lkvs - 1)) by word.
  rewrite Z2Nat.inj_add //.
  rewrite -> replicate_S.
  iDestruct "Hmus" as "[Hmu Hmus]".
  wp_auto. wp_apply (wp_leasingKV__waitSession with "[Hmu]").
  { iFrame "∗#%". }
  iIntros (err) "[Hmu Hmaybe_ready]".
  wp_auto.
  iApply "HΦ".
  destruct decide.
  2:{ done. }
  iDestruct "Hmaybe_ready" as "#Hready".
  rewrite -> replicate_S.
  iSplitL "Hmu".
  { iDestruct (own_leasingKV_own_KV with "[$] [$]") as "$". }
  iDestruct (big_sepL2_const_sepL_r with "[$Hmus]") as "H".
  2:{
    iDestruct (big_sepL2_impl _ (λ _ x _, x) with "H []") as "H".
    2:{
      iDestruct big_sepL2_const_sepL_l  as "[Hlem _]".
      iDestruct ("Hlem" with "H") as "H".
      instantiate (1:=replicate _ _).
      iRight in "H".
      iFrame "H".
    }
    iIntros "!# * %Hin %Hin2".
    rewrite -> lookup_replicate in Hin, Hin2. destruct Hin as [? _].
    destruct Hin2 as [? _]. subst.
    iIntros "Hown".
    iApply (own_leasingKV_own_KV with "[$] [-]").
    iFrame "∗#%".
  }
  iPureIntro. len.
Qed.

End proof.
