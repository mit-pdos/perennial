(** Global resources. *)
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm Require Import big_sep.
From Perennial.program_proof.rsm.pure Require Import vslice fin_maps.
From Perennial.program_proof.rsm.distx Require Import base.

Section res.
  Context `{!distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition db_ptsto γ (k : dbkey) (v : dbval) : iProp Σ.
  Admitted.

  Definition db_ptstos γ (m : dbmap) : iProp Σ :=
    [∗ map] k ↦ v ∈ m, db_ptsto γ k v.

  Lemma db_ptsto_update {γ k v1 v2} v :
    db_ptsto γ k v1 -∗
    db_ptsto γ k v2 ==∗
    db_ptsto γ k v ∗ db_ptsto γ k v.
  Admitted.

  Lemma db_ptsto_agree γ k v1 v2 :
    db_ptsto γ k v1 -∗
    db_ptsto γ k v2 -∗
    ⌜v2 = v1⌝.
  Admitted.

  Definition hist_repl_half γ (k : dbkey) (h : dbhist) : iProp Σ.
  Admitted.

  Definition hist_repl_lb γ (k : dbkey) (h : dbhist) : iProp Σ.
  Admitted.

  #[global]
  Instance is_hist_repl_lb_persistent α key hist :
    Persistent (hist_repl_lb α key hist).
  Admitted.

  Lemma hist_repl_update {γ k h1} h2 :
    prefix h1 h2 ->
    hist_repl_half γ k h1 -∗
    hist_repl_half γ k h1 ==∗
    hist_repl_half γ k h2 ∗ hist_repl_half γ k h2.
  Admitted.

  Lemma hist_repl_big_update {γ hs1} hs2 :
    dom hs1 = dom hs2 ->
    prefixes hs1 hs2 ->
    ([∗ map] k ↦ h ∈ hs1, hist_repl_half γ k h) -∗
    ([∗ map] k ↦ h ∈ hs1, hist_repl_half γ k h) ==∗
    ([∗ map] k ↦ h ∈ hs2, hist_repl_half γ k h) ∗
    ([∗ map] k ↦ h ∈ hs2, hist_repl_half γ k h).
  Proof.
    iIntros (Hdom Hprefix) "Hhs1x Hhs1y".
    iCombine "Hhs1x Hhs1y" as "Hhs1".
    rewrite -2!big_sepM_sep.
    iApply big_sepM_bupd.
    iApply (big_sepM_impl_dom_eq with "Hhs1"); first done.
    iIntros (k h1 h2 Hh1 Hh2) "!> [Hh1x Hh1y]".
    iApply (hist_repl_update with "Hh1x Hh1y").
    by specialize (Hprefix _ _ _ Hh1 Hh2).
  Qed.

  Lemma hist_repl_witness {γ k h} :
    hist_repl_half γ k h -∗
    hist_repl_lb γ k h.
  Admitted.

  Lemma hist_repl_prefix {γ k h hlb} :
    hist_repl_half γ k h -∗
    hist_repl_lb γ k hlb -∗
    ⌜prefix hlb h⌝.
  Admitted.

  Definition hist_repl_at γ (k : dbkey) (ts : nat) (v : dbval) : iProp Σ :=
    ∃ hist, hist_repl_lb γ k hist ∗ ⌜hist !! ts = Some v⌝.

  Lemma hist_repl_lookup γ k h ts v :
    hist_repl_half γ k h -∗
    hist_repl_at γ k ts v -∗
    ⌜h !! ts = Some v⌝.
  Proof.
    iIntros "Hhalf (%lb & #Hlb & %Hv)".
    iDestruct (hist_repl_prefix with "Hhalf Hlb") as %Hprefix.
    iPureIntro.
    by eapply prefix_lookup_Some.
  Qed.

  Definition hist_cmtd_auth γ (k : dbkey) (h : dbhist) : iProp Σ.
  Admitted.

  Definition hist_cmtd_lb γ (k : dbkey) (h : dbhist) : iProp Σ.
  Admitted.

  #[global]
  Instance hist_cmtd_lb_persistent α key hist :
    Persistent (hist_cmtd_lb α key hist).
  Admitted.

  Definition hist_cmtd_length_lb γ key n : iProp Σ :=
    ∃ lb, hist_cmtd_lb γ key lb ∗ ⌜(n ≤ length lb)%nat⌝.

  Lemma hist_cmtd_update {γ k h1} h2 :
    prefix h1 h2 ->
    hist_cmtd_auth γ k h1 ==∗
    hist_cmtd_auth γ k h2.
  Admitted.

  Lemma hist_cmtd_witness {γ k h} :
    hist_cmtd_auth γ k h -∗
    hist_cmtd_lb γ k h.
  Admitted.

  Lemma hist_cmtd_prefix {γ k h hlb} :
    hist_cmtd_auth γ k h -∗
    hist_cmtd_lb γ k hlb -∗
    ⌜prefix hlb h⌝.
  Admitted.

  Definition hist_lnrz_auth γ (k : dbkey) (l : dbhist) : iProp Σ.
  Admitted.

  Definition hist_lnrz_lb γ (k : dbkey) (l : dbhist) : iProp Σ.
  Admitted.

  #[global]
  Instance hist_lnrz_lb_persistent α key hist :
    Persistent (hist_lnrz_lb α key hist).
  Admitted.

  Lemma hist_lnrz_update {γ k l} l' :
    prefix l l' ->
    hist_lnrz_auth γ k l ==∗
    hist_lnrz_auth γ k l'.
  Admitted.

  Lemma hist_lnrz_witness γ k l :
    hist_lnrz_auth γ k l -∗
    hist_lnrz_lb γ k l.
  Admitted.

  Lemma hist_lnrz_prefix {γ k h hlb} :
    hist_lnrz_auth γ k h -∗
    hist_lnrz_lb γ k hlb -∗
    ⌜prefix hlb h⌝.
  Admitted.

  Definition hist_lnrz_at γ (k : dbkey) (ts : nat) (v : dbval) : iProp Σ :=
    ∃ lb, hist_lnrz_lb γ k lb ∗ ⌜lb !! ts = Some v⌝.

  Lemma hist_lnrz_lookup γ k h ts v :
    hist_lnrz_auth γ k h -∗
    hist_lnrz_at γ k ts v -∗
    ⌜h !! ts = Some v⌝.
  Proof.
    iIntros "Hauth (%lb & #Hlb & %Hv)".
    iDestruct (hist_lnrz_prefix with "Hauth Hlb") as %Hprefix.
    iPureIntro.
    by eapply prefix_lookup_Some.
  Qed.

  Definition ts_repl_half γ (k : dbkey) (ts : nat) : iProp Σ.
  Admitted.

  Lemma ts_repl_agree {γ k ts1 ts2} :
    ts_repl_half γ k ts1 -∗
    ts_repl_half γ k ts2 -∗
    ⌜ts2 = ts1⌝.
  Admitted.

  (** Replicated tuple [tuple_repl] simply combines [hist_repl] and [ts_repl]. *)
  Definition tuple_repl_half γ (k : dbkey) (t : dbtpl) : iProp Σ :=
    hist_repl_half γ k t.1 ∗ ts_repl_half γ k t.2.

  Lemma tuple_repl_agree {γ k t1 t2} :
    tuple_repl_half γ k t1 -∗
    tuple_repl_half γ k t2 -∗
    ⌜t2 = t1⌝.
  Admitted.

  Lemma tuple_repl_big_agree {γ tpls1 tpls2} :
    dom tpls1 = dom tpls2 ->
    ([∗ map] k ↦ t ∈ tpls1, tuple_repl_half γ k t) -∗
    ([∗ map] k ↦ t ∈ tpls2, tuple_repl_half γ k t) -∗
    ⌜tpls2 = tpls1⌝.
  Admitted.

  Lemma tuple_repl_update {γ k t1} t2 :
    prefix t1.1 t2.1 ->
    tuple_repl_half γ k t1 -∗
    tuple_repl_half γ k t1 ==∗
    tuple_repl_half γ k t2 ∗ tuple_repl_half γ k t2.
  Admitted.

  Lemma tuple_repl_big_update {γ tpls1} tpls2 :
    dom tpls1 = dom tpls2 ->
    (∀ k tpl1 tpl2, tpls1 !! k = Some tpl1 -> tpls2 !! k = Some tpl2 -> prefix tpl1.1 tpl2.1) ->
    ([∗ map] k ↦ t ∈ tpls1, tuple_repl_half γ k t) -∗
    ([∗ map] k ↦ t ∈ tpls1, tuple_repl_half γ k t) ==∗
    ([∗ map] k ↦ t ∈ tpls2, tuple_repl_half γ k t) ∗ ([∗ map] k ↦ t ∈ tpls2, tuple_repl_half γ k t).
  Proof.
    iIntros (Hdom Hprefix) "H1 H2".
    iCombine "H1 H2" as "Htpls1".
    rewrite -2!big_sepM_sep.
    iApply big_sepM_bupd.
    iApply (big_sepM_impl_dom_eq with "Htpls1"); first done.
    iIntros (k tpl1 tpl2 Htpl1 Htpl2)"!> [H1 H2]".
    iApply (tuple_repl_update with "H1 H2").
    by eapply Hprefix.
  Qed.

  (* Transaction result map RA. *)
  Definition txnres_auth γ (resm : gmap nat txnres) : iProp Σ.
  Admitted.

  Definition txnres_receipt γ (ts : nat) (res : txnres) : iProp Σ.
  Admitted.

  #[global]
  Instance txnres_receipt_persistent γ ts res :
    Persistent (txnres_receipt γ ts res).
  Admitted.

  Definition txnres_cmt γ ts wrs :=
    txnres_receipt γ ts (ResCommitted wrs).

  Definition txnres_abt γ ts :=
    txnres_receipt γ ts ResAborted.

  Lemma txnres_insert {γ resm} ts res :
    resm !! ts = None ->
    txnres_auth γ resm ==∗
    txnres_auth γ (<[ts := res]> resm).
  Admitted.

  Lemma txnres_witness γ resm ts res :
    resm !! ts = Some res ->
    txnres_auth γ resm -∗
    txnres_receipt γ ts res.
  Admitted.

  Lemma txnres_lookup γ resm ts res :
    txnres_auth γ resm -∗
    txnres_receipt γ ts res -∗
    ⌜resm !! ts = Some res⌝.
  Admitted.

  (* Transaction write-sets. This resource allows us to specify that [CmdPrep]
  is submitted to only the participant group, as encoded in
  [safe_submit]. Without which we won't be able to prove that learning a commit
  under an aborted state is impossible, as a non-participant group could have
  received [CmdPrep] and aborted. *)
  Definition txnwrs_auth γ (wrsm : gmap nat (option dbmap)) : iProp Σ.
  Admitted.

  Definition txnwrs_frag γ (ts : nat) (dq : dfrac) (owrs : option dbmap) : iProp Σ.
  Admitted.

  Definition txnwrs_excl γ (ts : nat) :=
    txnwrs_frag γ ts (DfracOwn 1) None.

  Definition txnwrs_cancel γ (ts : nat) :=
    txnwrs_frag γ ts DfracDiscarded None.

  Definition txnwrs_receipt γ (ts : nat) (wrs : dbmap) :=
    txnwrs_frag γ ts DfracDiscarded (Some wrs).

  #[global]
  Instance txnwrs_cancel_persistent γ ts :
    Persistent (txnwrs_cancel γ ts).
  Admitted.

  #[global]
  Instance txnwrs_receipt_persistent γ ts wrs :
    Persistent (txnwrs_receipt γ ts wrs).
  Admitted.

  Lemma txnwrs_allocate γ wrsm ts :
    wrsm !! ts = None ->
    txnwrs_auth γ wrsm ==∗
    txnwrs_auth γ (<[ts := None]> wrsm) ∗ txnwrs_excl γ ts.
  Admitted.

  Lemma txnwrs_excl_persist γ ts :
    txnwrs_excl γ ts ==∗ txnwrs_cancel γ ts.
  Admitted.

  Lemma txnwrs_set γ wrsm ts wrs :
    txnwrs_excl γ ts -∗
    txnwrs_auth γ wrsm ==∗
    txnwrs_auth γ (<[ts := Some wrs]> wrsm) ∗ txnwrs_receipt γ ts wrs.
  Admitted.

  Lemma txnwrs_lookup γ wrsm ts dq owrs :
    txnwrs_frag γ ts dq owrs -∗
    txnwrs_auth γ wrsm -∗
    ⌜wrsm !! ts = Some owrs⌝.
  Admitted.

  Lemma txnwrs_frag_agree γ ts dq1 dq2 owrs1 owrs2 :
    txnwrs_frag γ ts dq1 owrs1 -∗
    txnwrs_frag γ ts dq2 owrs2 -∗
    ⌜owrs2 = owrs1⌝.
  Admitted.

  Lemma txnwrs_receipt_lookup γ wrsm ts wrs :
    txnwrs_receipt γ ts wrs -∗
    txnwrs_auth γ wrsm -∗
    ⌜wrsm !! ts = Some (Some wrs)⌝.
  Proof. iIntros "#Hwrs Hwrsm". by iApply txnwrs_lookup. Qed.

  Lemma txnwrs_excl_elem_of γ wrsm ts :
    txnwrs_excl γ ts -∗
    txnwrs_auth γ wrsm -∗
    ⌜ts ∈ dom wrsm⌝.
  Proof.
    iIntros "Hwrs Hwrsm".
    iDestruct (txnwrs_lookup with "Hwrs Hwrsm") as %Hlookup.
    by apply elem_of_dom_2 in Hlookup.
  Qed.

  Lemma txnwrs_receipt_agree γ ts wrs1 wrs2 :
    txnwrs_receipt γ ts wrs1 -∗
    txnwrs_receipt γ ts wrs2 -∗
    ⌜wrs2 = wrs1⌝.
  Admitted.

  (* Custom transaction status. *)
  Definition txnprep_auth γ (gid : groupid) (pm : gmap nat bool) : iProp Σ.
  Admitted.

  Definition txnprep_receipt γ (gid : groupid) (ts : nat) (p : bool) : iProp Σ.
  Admitted.

  #[global]
  Instance txnprep_receipt_persistent γ gid ts p :
    Persistent (txnprep_receipt γ gid ts p).
  Admitted.

  Definition txnprep_prep γ gid ts :=
    txnprep_receipt γ gid ts true.

  Definition txnprep_unprep γ gid ts :=
    txnprep_receipt γ gid ts false.

  Lemma txnprep_receipt_agree γ gid ts p1 p2 :
    txnprep_receipt γ gid ts p1 -∗
    txnprep_receipt γ gid ts p2 -∗
    ⌜p2 = p1⌝.
  Admitted.

  Lemma txnprep_insert {γ gid pm} ts p :
    pm !! ts = None ->
    txnprep_auth γ gid pm ==∗
    txnprep_auth γ gid (<[ts := p]> pm).
  Admitted.

  Lemma txnprep_witness γ gid pm ts p :
    pm !! ts = Some p ->
    txnprep_auth γ gid pm -∗
    txnprep_receipt γ gid ts p.
  Admitted.

  Lemma txnprep_lookup γ gid pm ts p :
    txnprep_auth γ gid pm -∗
    txnprep_receipt γ gid ts p -∗
    ⌜pm !! ts = Some p⌝.
  Admitted.

  Definition kmod_lnrz_half γ (k : dbkey) (kmod : dbkmod) : iProp Σ.
  Admitted.

  Lemma kmod_lnrz_agree {γ k m1 m2} :
    kmod_lnrz_half γ k m1 -∗
    kmod_lnrz_half γ k m2 -∗
    ⌜m2 = m1⌝.
  Admitted.

  Lemma kmod_lnrz_vslice_agree {γ k m im} :
    k ∈ keys_all ->
    ([∗ set] key ∈ keys_all, kmod_lnrz_half γ key (vslice m key)) -∗
    kmod_lnrz_half γ k im -∗
    ⌜im = vslice m k⌝.
  Proof.
    iIntros (Hin) "Hkeys Hk".
    iDestruct (big_sepS_elem_of with "Hkeys") as "Hkey"; first apply Hin.
    by iDestruct (kmod_lnrz_agree with "Hkey Hk") as %?.
  Qed.

  Lemma kmod_lnrz_update {γ k kmod1 kmod2} kmod :
    kmod_lnrz_half γ k kmod1 -∗
    kmod_lnrz_half γ k kmod2 ==∗
    kmod_lnrz_half γ k kmod ∗ kmod_lnrz_half γ k kmod.
  Admitted.

  Lemma kmod_lnrz_big_agree {γ keys kmods f} :
    dom kmods = keys ->
    ([∗ set] k ∈ keys, kmod_lnrz_half γ k (f k)) -∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_lnrz_half γ k kmod) -∗
    ⌜map_Forall (λ k kmod, kmod = f k) kmods⌝.
  Proof.
    iIntros (Hdom) "Hkeys Hkmods".
    rewrite -Hdom.
    rewrite big_sepS_big_sepM.
    iCombine "Hkmods Hkeys" as "Hkmods".
    rewrite -big_sepM_sep.
    iApply big_sepM_pure.
    iApply (big_sepM_impl with "Hkmods").
    iIntros "!>" (k kmod Hkmod) "[Hkmod Hf]".
    iApply (kmod_lnrz_agree with "Hf Hkmod").
  Qed.

  Lemma kmod_lnrz_big_update {γ keys kmods f} f' :
    dom kmods = keys ->
    ([∗ set] k ∈ keys, kmod_lnrz_half γ k (f k)) -∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_lnrz_half γ k kmod) ==∗
    ([∗ set] k ∈ keys, kmod_lnrz_half γ k (f' k)) ∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_lnrz_half γ k (f' k)).
  Proof.
    iIntros (Hdom) "Hkeys Hkmods".
    rewrite -Hdom.
    rewrite 2!big_sepS_big_sepM.
    iCombine "Hkmods Hkeys" as "Hkmods".
    rewrite -2!big_sepM_sep.
    iApply big_sepM_bupd.
    iApply (big_sepM_mono with "Hkmods").
    iIntros (k kmod Hkmod) "[Hkmod Hf]".
    iMod (kmod_lnrz_update (f' k) with "Hkmod Hf") as "[Hkmod Hf]".
    by iFrame.
  Qed.

  Definition kmod_cmtd_half γ (k : dbkey) (kmod : dbkmod) : iProp Σ.
  Admitted.

  Lemma kmod_cmtd_agree {γ k m1 m2} :
    kmod_cmtd_half γ k m1 -∗
    kmod_cmtd_half γ k m2 -∗
    ⌜m2 = m1⌝.
  Admitted.

  Lemma kmod_cmtd_vslice_agree {γ k m im} :
    k ∈ keys_all ->
    ([∗ set] key ∈ keys_all, kmod_cmtd_half γ key (vslice m key)) -∗
    kmod_cmtd_half γ k im -∗
    ⌜im = vslice m k⌝.
  Proof.
    iIntros (Hin) "Hkeys Hk".
    iDestruct (big_sepS_elem_of with "Hkeys") as "Hkey"; first apply Hin.
    by iDestruct (kmod_cmtd_agree with "Hkey Hk") as %?.
  Qed.

  Lemma kmod_cmtd_update {γ k kmod1 kmod2} kmod :
    kmod_cmtd_half γ k kmod1 -∗
    kmod_cmtd_half γ k kmod2 ==∗
    kmod_cmtd_half γ k kmod ∗ kmod_cmtd_half γ k kmod.
  Admitted.

  Lemma kmod_cmtd_big_agree {γ keys kmods f} :
    dom kmods = keys ->
    ([∗ set] k ∈ keys, kmod_cmtd_half γ k (f k)) -∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_cmtd_half γ k kmod) -∗
    ⌜map_Forall (λ k kmod, kmod = f k) kmods⌝.
  Proof.
    iIntros (Hdom) "Hkeys Hkmods".
    rewrite -Hdom.
    rewrite big_sepS_big_sepM.
    iCombine "Hkmods Hkeys" as "Hkmods".
    rewrite -big_sepM_sep.
    iApply big_sepM_pure.
    iApply (big_sepM_impl with "Hkmods").
    iIntros "!>" (k kmod Hkmod) "[Hkmod Hf]".
    iApply (kmod_cmtd_agree with "Hf Hkmod").
  Qed.

  Lemma kmod_cmtd_big_update {γ keys kmods f} f' :
    dom kmods = keys ->
    ([∗ set] k ∈ keys, kmod_cmtd_half γ k (f k)) -∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_cmtd_half γ k kmod) ==∗
    ([∗ set] k ∈ keys, kmod_cmtd_half γ k (f' k)) ∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_cmtd_half γ k (f' k)).
  Proof.
    iIntros (Hdom) "Hkeys Hkmods".
    rewrite -Hdom.
    rewrite 2!big_sepS_big_sepM.
    iCombine "Hkmods Hkeys" as "Hkmods".
    rewrite -2!big_sepM_sep.
    iApply big_sepM_bupd.
    iApply (big_sepM_mono with "Hkmods").
    iIntros (k kmod Hkmod) "[Hkmod Hf]".
    iMod (kmod_cmtd_update (f' k) with "Hkmod Hf") as "[Hkmod Hf]".
    by iFrame.
  Qed.

  (* Linearized transactions. *)
  Definition txns_lnrz_auth γ (tids : gset nat) : iProp Σ.
  Admitted.

  Definition txns_lnrz_receipt γ (tid : nat) : iProp Σ.
  Admitted.

  #[global]
  Instance txns_lnrz_receipt_persistent γ tid :
    Persistent (txns_lnrz_receipt γ tid).
  Admitted.

  Lemma txns_lnrz_insert γ tids tid :
    tid ∉ tids ->
    txns_lnrz_auth γ tids ==∗
    txns_lnrz_auth γ ({[ tid ]} ∪ tids) ∗ txns_lnrz_receipt γ tid.
  Admitted.

  Lemma txns_lnrz_elem_of γ tids tid :
    txns_lnrz_auth γ tids -∗
    txns_lnrz_receipt γ tid -∗
    ⌜tid ∈ tids⌝.
  Admitted.

  (* Transactions predicted to abort. *)
  Definition txns_abt_auth γ (tids : gset nat) : iProp Σ.
  Admitted.

  Definition txns_abt_elem γ (tid : nat) : iProp Σ.
  Admitted.

  Lemma txns_abt_insert {γ tids} tid :
    tid ∉ tids ->
    txns_abt_auth γ tids ==∗
    txns_abt_auth γ ({[ tid ]} ∪ tids) ∗ txns_abt_elem γ tid.
  Admitted.

  Lemma txns_abt_delete {γ tids} tid :
    txns_abt_elem γ tid -∗
    txns_abt_auth γ tids ==∗
    txns_abt_auth γ (tids ∖ {[ tid ]}).
  Admitted.

  Lemma txns_abt_elem_of γ tids tid :
    txns_abt_auth γ tids -∗
    txns_abt_elem γ tid -∗
    ⌜tid ∈ tids⌝.
  Admitted.

  (* Transactions predicted to commit/has committed. *)
  Definition txns_cmt_auth γ (tmods : gmap nat dbmap) : iProp Σ.
  Admitted.

  Definition txns_cmt_elem γ (tid : nat) (wrs : dbmap) : iProp Σ.
  Admitted.

  Lemma txns_cmt_insert {γ tmods} tid wrs :
    tmods !! tid = None ->
    txns_cmt_auth γ tmods ==∗
    txns_cmt_auth γ (<[tid := wrs]> tmods) ∗ txns_cmt_elem γ tid wrs.
  Admitted.

  Lemma txns_cmt_lookup γ tmods tid wrs :
    txns_cmt_auth γ tmods -∗
    txns_cmt_elem γ tid wrs -∗
    ⌜tmods !! tid = Some wrs⌝.
  Admitted.

  (* Exclusive transaction IDs. *)
  Definition tids_excl_auth γ (tids : gset nat) : iProp Σ.
  Admitted.

  Definition tids_excl_frag γ (tid : nat) : iProp Σ.
  Admitted.

  Lemma tids_excl_insert γ tids tid :
    tid ∉ tids ->
    tids_excl_auth γ tids ==∗
    tids_excl_auth γ ({[ tid ]} ∪ tids) ∗ tids_excl_frag γ tid.
  Admitted.

  Lemma tids_excl_ne γ tid1 tid2 :
    tids_excl_frag γ tid1 -∗
    tids_excl_frag γ tid2 -∗
    ⌜tid2 ≠ tid1⌝.
  Admitted.

  Lemma tids_excl_not_elem_of γ tids tid :
    ([∗ set] t ∈ tids, tids_excl_frag γ t) -∗
    tids_excl_frag γ tid -∗
    ⌜tid ∉ tids⌝.
  Proof.
    iIntros "Htids Htid".
    destruct (decide (tid ∈ tids)) as [Hin | ?]; last done.
    iDestruct (big_sepS_elem_of with "Htids") as "Htid'"; first apply Hin.
    by iDestruct (tids_excl_ne with "Htid Htid'") as %?.
  Qed.

  (* Transaction post-condition. Might need a [ghost_map nat gname] and a [saved_prop]? *)
  Definition txnpost_auth γ (posts : gmap nat (dbmap -> Prop)) : iProp Σ.
  Admitted.

  Definition txnpost_receipt γ (tid : nat) (post : dbmap -> Prop) : iProp Σ.
  Admitted.

  #[global]
  Instance txnpost_receipt_persistent γ tid post :
    Persistent (txnpost_receipt γ tid post).
  Admitted.

  Lemma txnpost_insert γ posts tid post :
    posts !! tid = None ->
    txnpost_auth γ posts ==∗
    txnpost_auth γ (<[tid := post]> posts) ∗ txnpost_receipt γ tid post.
  Admitted.

  Lemma txnpost_elem_of γ posts tid post :
    txnpost_auth γ posts -∗
    txnpost_receipt γ tid post -∗
    ⌜posts !! tid = Some post⌝.
  Admitted.

  Lemma txnpost_receipt_agree γ tid post1 post2 :
    txnpost_receipt γ tid post1 -∗
    txnpost_receipt γ tid post2 -∗
    ⌜post2 = post1⌝.
  Admitted.

  (* Paxos log and command pool. TODO: rename clog to just log. *)
  Definition clog_half γ (gid : groupid) (log : dblog) : iProp Σ.
  Admitted.

  Definition clog_lb γ (gid : groupid) (log : dblog) : iProp Σ.
  Admitted.

  #[global]
  Instance clog_lb_persistent γ gid log :
    Persistent (clog_lb γ gid log).
  Admitted.

  Definition clog_lbs γ (logs : gmap groupid dblog) : iProp Σ :=
    [∗ map] gid ↦ log ∈ logs, clog_lb γ gid log.

  Definition cpool_half γ (gid : groupid) (cpool : gset command) : iProp Σ.
  Admitted.

  Definition cmd_receipt γ (gid : groupid) (lsn : nat) (term : nat) (c : command) : iProp Σ.
  Admitted.

  #[global]
  Instance cmd_receipt_persistent γ gid lsn term c :
    Persistent (cmd_receipt γ gid lsn term c).
  Admitted.

  Lemma log_witness γ gid log :
    clog_half γ gid log -∗
    clog_lb γ gid log.
  Admitted.

  Lemma log_prefix γ gid log logp :
    clog_half γ gid log -∗
    clog_lb γ gid logp -∗
    ⌜prefix logp log⌝.
  Admitted.

  Lemma log_lb_prefix γ gid logp1 logp2 :
    clog_lb γ gid logp1 -∗
    clog_lb γ gid logp2 -∗
    ⌜prefix logp1 logp2 ∨ prefix logp2 logp1⌝.
  Admitted.

  Lemma log_lb_weaken {γ gid} logp1 logp2 :
    prefix logp1 logp2 ->
    clog_lb γ gid logp2 -∗
    clog_lb γ gid logp1.
  Admitted.

  Definition cpool_subsume_log (cpool : gset command) (log : list command) :=
    Forall (λ c, c ∈ cpool) log.

  Lemma log_cpool_incl γ gid log cpool :
    clog_half γ gid log -∗
    cpool_half γ gid cpool -∗
    ⌜cpool_subsume_log cpool log⌝.
  Admitted.

  Lemma log_update γ gid log cpool v :
    v ∈ cpool ->
    clog_half γ gid log -∗
    cpool_half γ gid cpool ==∗
    clog_half γ gid (log ++ [v]).
  Admitted.

  (* Global timestamp. *)
  Definition ts_auth γ (ts : nat) : iProp Σ.
  Admitted.

  Definition ts_lb γ (ts : nat) : iProp Σ.
  Admitted.

  Lemma ts_le γ tslb ts :
    ts_lb γ tslb -∗
    ts_auth γ ts -∗
    ⌜(tslb ≤ ts)%nat⌝.
  Admitted.

  Lemma ts_witness γ ts :
    ts_auth γ ts -∗
    ts_lb γ ts.
  Admitted.

  Lemma ts_lb_weaken {γ ts} ts' :
    (ts' ≤ ts)%nat ->
    ts_lb γ ts -∗
    ts_lb γ ts'.
  Admitted.

  #[global]
  Instance ts_lb_persistent γ ts :
    Persistent (ts_lb γ ts).
  Admitted.

  Definition txn_proph γ (p : proph_id) (acts : list action) : iProp Σ.
  Admitted.

End res.
