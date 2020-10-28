From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import gset.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.
From Perennial.algebra Require Import fmcounter.

Section simulation.
  Context `{!invG Σ}.
  Context {state: Type} (wf: state -> Prop) (P: state -> iProp Σ).
  Context (E: coPset).
  (* TODO: if we can start using this everywhere I think we can start proving
  generic theorems about simulation, like the one below *)
  Definition simulation_fupd {T} (tr: transition state T) (Q: T -> iProp Σ): iProp Σ :=
    (∀ σ σ' r,
         ⌜wf σ⌝ -∗
         ⌜relation.denote tr σ σ' r⌝ -∗
        (P σ ={E}=∗ P σ' ∗ ⌜wf σ'⌝ ∗ Q r)).

  Theorem simulation_bind_fupd {A B}
          (tr1: transition state A)
          (tr2: A -> transition state B)
          (Q: B -> iProp Σ) :
    simulation_fupd tr1 (fun x => simulation_fupd (tr2 x) Q) -∗
    simulation_fupd (bind tr1 tr2) Q.
  Proof.
    iIntros "Hfupd".
    iIntros (σ1 σ3 r Hwf Htr) "HP".
    simpl in Htr.
    inversion Htr; subst; clear Htr.
    rename s2 into σ2.
    iMod ("Hfupd" with "[] [] HP") as "(HP&%Hwf2&Hfupd2)"; eauto.
    iMod ("Hfupd2" with "[] [] HP") as "(HP&%Hwf3&HQ)"; eauto.
    iFrame.
    auto.
  Qed.
End simulation.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: list update.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let innerN := walN .@ "wal".
Let circN := walN .@ "circ".

Definition in_bounds γ (a: u64): iProp Σ :=
  ∃ d,
    "Hbounddisk" ∷ is_base_disk γ d ∗
    "%Hinbounds" ∷ ⌜is_Some (d !! int.val a)⌝.

Instance in_bounds_persistent γ a : Persistent (in_bounds γ a) := _.

(* TODO: this will actually require combining in_bounds with some authoritative
resource from the invariant, obviously it can't be for an arbitrary [σ] *)
Theorem in_bounds_valid γ σ a :
  is_base_disk γ σ.(log_state.d) -∗
  in_bounds γ a -∗ ⌜is_Some (σ.(log_state.d) !! int.val a)⌝.
Proof.
  iIntros "Hbase Hbound".
  iNamed "Hbound".
  iDestruct (is_base_disk_agree with "Hbase Hbounddisk") as %<-.
  eauto.
Qed.

(* this is more or less big_sepM_lookup_acc, but with is_installed_read unfolded *)
Theorem is_installed_read_lookup {γ d txns installed_lb durable_txn_id} {a: u64} :
  is_Some (d !! int.val a) ->
  is_installed γ d txns installed_lb durable_txn_id -∗
  ∃ txn_id b,
    ⌜(installed_lb ≤ txn_id ≤ durable_txn_id)%nat ∧
      apply_upds (txn_upds (take (S txn_id) txns)) d !! int.val a = Some b⌝ ∗
    int.val a d↦ b ∗ (int.val a d↦ b -∗ is_installed γ d txns installed_lb durable_txn_id).
Proof.
  rewrite /is_installed_read.
  iIntros (Hlookup) "Hbs".
  destruct Hlookup as [b0 Hlookup].
  iNamedRestorable "Hbs".
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hlookup with "Hdata") as "[Hb Hdata]".
  iApply restore_intro in "Hb".
  iDestruct "Hb" as (b txn_id') "((%Hin_bounds&%Halready_installed&%Happly_upds) &Hb & %Ha_bound &Hb')".
  iDestruct (restore_elim with "Hb'") as "#Hb_restore"; iClear "Hb'".
  iExists txn_id', b.
  iFrame "Hb".
  iSplit.
  { iPureIntro. auto with lia. }
  iIntros "Hb".
  iApply "Hbs"; iFrame.
  iApply "Hdata".
  iApply "Hb_restore".
  iFrame.
Qed.

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

Lemma sliding_set_mutable_start f (σ: slidingM.t) :
  slidingM.start (set slidingM.mutable f σ) = slidingM.start σ.
Proof. by destruct σ. Qed.

(* TODO: move memWrite proofs to sliding.v *)
Lemma memWrite_one_NoDup σ u :
  NoDup (update.addr <$> σ.(slidingM.log)) →
  int.val σ.(slidingM.mutable) - int.val σ.(slidingM.start) = 0 →
  NoDup (update.addr <$> (memWrite_one σ u).(slidingM.log)).
Proof.
  intros Hnodup Hro_len.
  rewrite /memWrite_one.
  destruct (find_highest_index _) as [i|] eqn:Hlookup; simpl.
  - rewrite Hro_len.
    rewrite -> decide_True by word.
    simpl.
    rewrite list_fmap_insert.
    rewrite list_insert_id //.
    apply find_highest_index_ok' in Hlookup as [Hlookup _].
    auto.
  - rewrite fmap_app.
    apply NoDup_app.
    split_and!; auto.
    + simpl.
      intros x Hx ->%elem_of_list_singleton.
      apply elem_of_list_lookup in Hx as [txn_id Hx].
      eapply find_highest_index_none in Hlookup; eauto.
    + simpl.
      apply NoDup_singleton.
Qed.

Lemma memWrite_all_NoDup σ bufs:
  NoDup (update.addr <$> σ.(slidingM.log)) →
  int.val σ.(slidingM.mutable) - int.val σ.(slidingM.start) = 0 →
  NoDup (update.addr <$> (memWrite σ bufs).(slidingM.log)).
Proof.
  generalize dependent σ.
  induction bufs as [|u bufs]; simpl; intuition.
  apply IHbufs.
  - apply memWrite_one_NoDup; auto.
  - rewrite memWrite_one_same_start memWrite_one_same_mutable //.
Qed.

Theorem wp_absorbBufs b_s (bufs: list update.t) :
  {{{ updates_slice_frag b_s 1 bufs }}}
    absorbBufs (slice_val b_s)
  {{{ b_s' q bufs', RET slice_val b_s';
      "Habsorbed" ∷ updates_slice_frag b_s' q bufs' ∗
      "%Hsame_upds" ∷ ⌜∀ d, apply_upds bufs' d = apply_upds bufs d⌝ ∗
      "%Hnodup" ∷ ⌜NoDup (update.addr <$> bufs')⌝ ∗
      "%Hsubset" ∷ ⌜bufs' ⊆ bufs⌝ (* this is implied by Hsame_upds but would be hard to prove from there *)
  }}}.
Proof.
  wp_start.
  wp_call.
  change slice.nil with (slice_val Slice.nil).
  wp_apply (wp_mkSliding _ []).
  { simpl; word. }
  { iSplitL.
    - iExists []; simpl.
      rewrite right_id.
      by iApply is_slice_small_nil.
    - iApply is_slice_cap_nil. }
  iIntros (l) "Hsliding".
  iDestruct (updates_slice_frag_len with "Hpre") as "%Hbufslen".
  wp_apply (wp_sliding__memWrite with "[$Hsliding $Hpre]").
  { iPureIntro.
    rewrite /slidingM.memEnd /=. word. }
  iIntros "Hsliding".
  wp_apply (wp_sliding__clearMutable with "Hsliding"); iIntros "Hsliding".
  wp_apply (wp_sliding__end with "Hsliding"); iIntros "Hsliding".
  simpl.
  set (bufs':=(memWrite
                 {|
                   slidingM.log := [];
                   slidingM.start := 0;
                   slidingM.mutable := int.val 0 + 0%nat |} bufs)).
  iDestruct (is_sliding_wf with "Hsliding") as %Hwf.
  wp_apply (wp_sliding__takeTill with "Hsliding").
  { rewrite sliding_set_mutable_start /=.
    rewrite slidingM_endPos_val //=.
    word. }
  iIntros (q b_s') "[Hsliding Hbufs']".
  simpl.
  rewrite take_ge.
  { iApply "HΦ"; iFrame "Hbufs'".
    iPureIntro; intuition.
    - intros; rewrite memWrite_apply_upds //.
    - subst bufs'.
      apply memWrite_all_NoDup; simpl.
      + constructor.
      + word.
    - admit.
  }
  rewrite /slidingM.logIndex /=.
  rewrite slidingM_endPos_val //=.
  replace bufs'.(slidingM.start) with (U64 0) by rewrite memWrite_same_start //.
  word.
Admitted.

Lemma is_durable_txn_bound γ cs txns diskEnd_txn_id durable_lb :
  is_durable_txn (Σ:=Σ) γ cs txns diskEnd_txn_id durable_lb -∗
  ⌜(diskEnd_txn_id < length txns)%nat⌝.
Proof.
  iNamed 1.
  iPureIntro.
  apply is_txn_bound in Hend_txn; lia.
Qed.

Theorem wp_Walog__ReadInstalled (Q: Block -> iProp Σ) l γ dinit a :
  {{{ is_wal P l γ dinit ∗
      in_bounds γ a ∗
       (∀ σ σ' b,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_read_installed a) σ σ' b⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q b))
   }}}
    Walog__ReadInstalled #l #a
  {{{ bl, RET slice_val bl; ∃ b, is_block bl 1 b ∗ Q b}}}.
Proof.
  iIntros (Φ) "(#Hwal & #Ha_valid & Hfupd) HΦ".
  wp_call.
  wp_apply (wp_Read_fupd _ _ 1 (* q=1 *)).
  iDestruct "Hwal" as "[Hwal Hcirc]".
  iInv "Hwal" as (σ) "[Hinner HP]" "Hclose".
  iDestruct "Hinner" as "(>? & ? & ? & >? & >Hdisk)"; iNamed.
  iNamed "Hdisk".
  iNamed "Hdisk".
  iNamed "Hdisk".

  iDestruct (in_bounds_valid _ σ with "Hbasedisk Ha_valid") as %Hlookup.
  iDestruct (is_installed_read_lookup Hlookup with "Hinstalled") as
      (txn_id b [Htxn_id Hbval]) "(Hb&Hinstalled)".
  iModIntro.
  iExists b; iFrame "Hb".
  iNext.
  iIntros "Hb".
  iSpecialize ("Hinstalled" with "Hb").
  iNamed "circ.start".
  fold innerN.
  iMod (fupd_intro_mask' _ (⊤∖↑N)) as "HinnerN".
  { solve_ndisj. }
  iDestruct (is_durable_txn_bound with "circ.end") as %Hdurable_bound.

  iMod ("Hfupd" $! σ σ b with "[//] [] HP") as "[HP HQ]".
  { iPureIntro.
    repeat (simpl; monad_simpl).
    exists σ txn_id.
    { econstructor; eauto; lia. }
    repeat (simpl; monad_simpl). }
  iMod "HinnerN" as "_".
  iFrame.
  iMod ("Hclose" with "[-HQ HΦ]") as "_".
  {
    iModIntro.
    iExists _; iFrame "HP".
    iFrame.
    iSplit; auto.
    iExists _; iFrame.
    iExists _, _; iFrame "# ∗".
    auto.
  }
  iIntros "!>" (s) "Hs".
  iApply "HΦ".
  iExists _; iFrame.
  iDestruct (is_slice_to_small with "Hs") as "$".
Qed.

Lemma apply_upds_equiv_implies_has_updates_equiv upds1 upds2 txns :
  (∀ d : disk, apply_upds upds2 d = apply_upds upds1 d) →
  has_updates upds1 txns →
  has_updates upds2 txns.
Proof.
  intros Hequiv Hupds1 d.
  rewrite (Hequiv d) //.
Qed.

Lemma Forall_subset {A} f (l1: list A) (l2: list A) :
  l1 ⊆ l2 →
  Forall f l2 →
  Forall f l1.
Proof.
  intros Hsubset Hl2.
  apply List.Forall_forall.
  intros x Hin_l1.
  apply elem_of_list_In in Hin_l1.
  destruct (elem_of_subseteq l1 l2) as (Hsubset_elem_of&_).
  apply Hsubset_elem_of with (x := x) in Hsubset; intuition.
  destruct (List.Forall_forall f l2) as (Hl2_impl&_).
  apply elem_of_list_In in Hsubset.
  apply (Hl2_impl Hl2 x) in Hsubset.
  done.
Qed.

Lemma apply_upds_notin d upds (a: u64) :
  a ∉ (update.addr <$> upds) →
  apply_upds upds d !! int.val a = d !! int.val a.
Proof.
  rewrite -(reverse_involutive upds).
  remember (reverse upds) as upds_r.
  clear Hequpds_r upds.
  induction upds_r.
  1: eauto.
  intros Hnotin.
  rewrite fmap_reverse fmap_cons reverse_cons -fmap_reverse in Hnotin.
  apply not_elem_of_app in Hnotin.
  destruct Hnotin as (Hnotin&Hneq).
  apply IHupds_r in Hnotin.
  rewrite reverse_cons apply_upds_app.
  destruct a0.
  simpl.
  rewrite lookup_insert_ne.
  2: {
    simpl in Hneq.
    apply not_elem_of_cons in Hneq.
    destruct (decide (int.val addr = int.val a)).
    2: intuition.
    assert (addr = a) by word.
    intuition.
  }
  intuition.
Qed.

Lemma apply_upds_NoDup_lookup d upds i a b :
  NoDup (update.addr <$> upds) →
  upds !! i = Some {| update.addr := a; update.b := b |} →
  (apply_upds upds d) !! int.val a = Some b.
Proof.
  intros Hnodup Hlookup.
  rewrite -(take_drop (S i) upds).
  rewrite -(take_drop (S i) upds) fmap_app in Hnodup.
  apply NoDup_app in Hnodup.
  destruct Hnodup as (Hnodup&Heither&_).
  rewrite apply_upds_app apply_upds_notin.
  2: {
    apply Heither.
    rewrite -(lookup_take _ (S i)) in Hlookup.
    2: lia.
    apply (elem_of_list_lookup_2 _ i).
    rewrite list_lookup_fmap Hlookup //.
  }
  rewrite (take_S_r _ _ _ Hlookup) apply_upds_app /=.
  apply lookup_insert.
Qed.

Theorem wp_installBlocks γ l dinit d bufs_s (bufs: list update.t)
        (installed_txn_id: nat) subtxns :
  (* {{{ "#Hbufs_s" ∷ readonly (updates_slice_frag bufs_s 1 bufs) ∗ *)
  {{{ "Hbufs_s" ∷ updates_slice_frag bufs_s 1 bufs ∗
      "#Hwal" ∷ is_wal P l γ dinit ∗
      "%Hbufs" ∷ ⌜has_updates bufs subtxns⌝ ∗
      "%Hbufs_addrs" ∷ ⌜Forall (λ u : update.t, ∃ (b: Block), dinit !! int.val u.(update.addr) = Some b) bufs⌝ ∗
      "Halready_installed_installer" ∷ ghost_var γ.(already_installed_name) (1/2) (∅: gset Z) ∗
      "Hinstalled_txn_installer" ∷ fmcounter γ.(installed_txn_name) (1/2) installed_txn_id ∗
      "Hbeing_installed_txns_installer" ∷ ghost_var γ.(being_installed_txns_name) (1/2) subtxns
  }}}
    installBlocks #d (slice_val bufs_s)
  {{{ RET #();
      "#Hwal" ∷ is_wal P l γ dinit ∗
      "Halready_installed_installer" ∷ ghost_var γ.(already_installed_name) (1/2) (list_to_set (C:=gset Z) ((λ u, int.val (update.addr u)) <$> bufs)) ∗
      "Hinstalled_txn_installer" ∷ fmcounter γ.(installed_txn_name) (1/2) installed_txn_id ∗
      "Hbeing_installed_txns_installer" ∷ ghost_var γ.(being_installed_txns_name) (1/2) subtxns
  }}}.
Proof.
  wp_start.
  wp_call.
  wp_apply (wp_absorbBufs with "Hbufs_s").
  iIntros (bks_s q upds) "Hpost".
  iNamed "Hpost".
  apply (apply_upds_equiv_implies_has_updates_equiv _ _ _ Hsame_upds) in Hbufs.
  apply (Forall_subset _ _ _ Hsubset) in Hbufs_addrs.

  wp_pures.
  iDestruct "Habsorbed" as (bks) "(Hbks_s&Hupds)".

  iDestruct (slice.is_slice_small_sz with "Hbks_s") as %Hslen.
  rewrite fmap_length in Hslen.
  iDestruct (big_sepL2_length with "Hupds") as %Hslen2.

  wp_apply (slice.wp_forSlice (fun i =>
    ("Hupds" ∷ [∗ list] uv;upd ∈ bks;upds, is_update uv q upd) ∗
    "Halready_installed_installer" ∷ ghost_var γ.(already_installed_name) (1/2) (list_to_set (C:=gset Z) (take (int.nat i) ((λ u, int.val (update.addr u)) <$> upds))) ∗
    "Hinstalled_txn_installer" ∷ fmcounter γ.(installed_txn_name) (1/2) installed_txn_id ∗
    "Hbeing_installed_txns_installer" ∷ ghost_var γ.(being_installed_txns_name) (1/2) subtxns
    )%I with "[] [$Hbks_s $Hupds $Halready_installed_installer $Hinstalled_txn_installer $Hbeing_installed_txns_installer]").
  {
    iIntros (i buf Φₗ) "!> [HI [% %]] HΦ".
    iNamed "HI".

    rewrite list_lookup_fmap in H0.
    apply fmap_Some in H0.
    destruct H0 as [ [addr bk_s] [Hbkseq ->] ].
    list_elem upds i as u.
    iDestruct (big_sepL2_lookup_acc with "Hupds") as "[Hi Hupds]"; eauto.
    destruct u as [addr_i b_i]; simpl.
    iDestruct "Hi" as "[%Heq Hi]".
    simpl in Heq; subst.

    wp_pures.
    wp_apply util_proof.wp_DPrintf.
    wp_pures.
    wp_apply (wp_Write_fupd (⊤ ∖ ↑walN.@"wal") with "Hi").
    destruct (Forall_lookup_1 _ _ _ _ Hbufs_addrs Hu_lookup) as (binit, Hbinit).
    simpl in Hbinit.

    iDestruct "Hwal" as "[Hwal Hcircular]".
    iInv "Hwal" as (σs) "[Hinner HP]" "Hclose".
    iDestruct "Hinner" as "(>%Hwf&Hmem&>?&>?&>?&>?)"; iNamed.
    iNamed "Hdisk".
    iNamed "Hdisk".
    (* TODO: why is this not using [is_installed_read_lookup]? *)
    iNamed "Hinstalled".
    iNamed "Howninstalled".

    iDestruct (ghost_var_agree with "Halready_installed_installer Halready_installed") as %<-.
    iDestruct (fmcounter_agree_1 with "Hinstalled_txn_installer Hinstalled_txn") as %<-.
    iDestruct (ghost_var_agree with "Hbeing_installed_txns_installer Hbeing_installed_txns") as %->.
    iMod (ghost_var_update_halves (list_to_set (C:=gset Z) (take (S (int.nat i)) ((λ u, int.val (update.addr u)) <$> upds)))
      with "Halready_installed_installer Halready_installed") as
          "[Halready_installed_installer Hbeing_installed]".

    apply mk_is_Some in Hbinit.
    apply Hdaddrs_init in Hbinit.
    destruct Hbinit as (b&Hbsome).

    iDestruct (big_sepM_lookup_acc_impl _ _ _ _ _ Hbsome with "Hdata") as "Hdata".
    iDestruct ("Hdata" with "[]") as "(Hdata_acc&Hdata)".
    {
      iModIntro.
      iIntros (addr' b' Hb' Hneq) "Hdata".
      iDestruct "Hdata" as (b_old txn_id') "([%Htxn_id' %Happly_upds] &Hmapsto&%Haddr_bound)".
      (* TODO: this proof hasn't been updated to new invariant, the way
      [is_installed_read_lookup] has been *)
      Existential 2 := (λ a _,
   ∃ (b: Block) (txn_id': nat),
     (* every disk block has at least through installed_txn_id (most have
      exactly, but some blocks may be in the process of being installed) *)
     let txns := σs.(log_state.txns) in
     let already_installed := (take (S (int.nat i)) ((λ u, int.val (update.addr u)) <$> upds)) in
     ⌜installed_txn_id ≤ txn_id' ≤ new_installed_txn_id ∧
      ( a ∈ already_installed → txn_id' = new_installed_txn_id ) ∧
      let txns := take (S txn_id') txns in
      apply_upds (txn_upds txns) σs.(log_state.d) !! a = Some b⌝ ∗
     a d↦ b ∗ ⌜2 + LogSz ≤ a⌝)%I.
      rewrite /=.
      iExists _, txn_id'.
      iFrame (Haddr_bound) "∗".
      iPureIntro.
      admit.

      (*
      (* TODO: restore this proof to new invariant *)
      destruct (decide (addr' = int.val addr_i)); first intuition.
      destruct (decide (addr' ∈ take (S (int.nat i)) ((λ u : update.t, int.val u.(update.addr)) <$> upds))).
      - rewrite (take_S_r _ _ (int.val addr_i)) in e.
        2: rewrite list_lookup_fmap Hu_lookup //=.
        apply elem_of_app in e.
        destruct e as [He | He].
        2: apply elem_of_list_singleton in He; contradiction.
        rewrite decide_True in Htxn_id'.
        2: {
          apply elem_of_list_to_set.
          assumption.
        }
        subst. eauto.
      - rewrite (take_S_r _ _ (int.val addr_i)) in n0.
        2: rewrite list_lookup_fmap Hu_lookup //=.
        apply not_elem_of_app in n0.
        destruct n0 as (Hn&_).
        rewrite decide_False in Htxn_id'.
        2: {
          apply not_elem_of_list_to_set.
          assumption.
        }
        intuition subst; eauto.
*)
    }

    iDestruct "Hdata_acc" as (b_disk txn_id') "(%Hb_disk&Haddr_i_mapsto&%Haddr_LogSz_bound)".
    iExists _.
    iFrame "Haddr_i_mapsto".
    iIntros "!> !> /= Haddr_i_mapsto".

    admit. (* TODO: fix this remainder for new is_installed_core *)

    (*
    iMod ("Hclose" with "[Hmem Htxns_ctx γtxns HnextDiskEnd_inv Howncs Hinstalled_txn Halready_installed Hbeing_installed_txns HP Hdata Haddr_i_mapsto]") as "_".
    {
      iIntros "!>".
      iExists _.
      iFrame "∗".
      iFrame (Hwf).
      iExists _.
      iFrame.
      iExists _, _.
      iFrame "# ∗".
      iFrame (Hdaddrs_init).
      iExists _, _.
      iFrame (Hinstalled_bounds) "∗".
      iSpecialize ("Hdata" with "[Haddr_i_mapsto]").
      {
        iExists _.
        iFrame (Haddr_LogSz_bound) "∗".
        iPureIntro.
        rewrite decide_True.
        2: {
          apply (elem_of_list_lookup_2 _ (int.nat i)).
          rewrite lookup_take.
          2: lia.
          rewrite list_lookup_fmap Hu_lookup //=.
        }
        rewrite -subslice_from_start -(subslice_app_contig _ (S installed_txn_id)).
        2: lia.
        rewrite txn_upds_app apply_upds_app -Hbufs.
        apply (apply_upds_NoDup_lookup _ _ (int.nat i)); intuition.
      }
      iApply big_sepM_mono.
      2: iFrame.
      iIntros (addr' b' Hb') "Hsep".
      iDestruct "Hsep" as (b_sep) "(%Hsep&Hd&%Haddr_bound)".
      iExists _, _.
      iFrame (Haddr_bound) "∗".
      iPureIntro.
      destruct (decide (addr' = int.val addr_i)).
      2: {
        destruct (decide (addr' ∈ take (S (int.nat i)) ((λ u : update.t, int.val u.(update.addr)) <$> upds))).
        - rewrite decide_True //.
          apply elem_of_list_to_set.
          assumption.
        - rewrite decide_False //.
          2: {
            apply not_elem_of_list_to_set.
            assumption.
          }
          intuition eauto.
          admit.
      }
      subst.
      rewrite decide_True.
      2: {
        apply elem_of_list_to_set.
        apply (elem_of_list_lookup_2 _ (int.nat i)).
        rewrite lookup_take.
        2: lia.
        rewrite list_lookup_fmap Hu_lookup //=.
      }
      rewrite decide_True in Hsep.
      2: {
        apply (elem_of_list_lookup_2 _ (int.nat i)).
        rewrite lookup_take.
        2: lia.
        rewrite list_lookup_fmap Hu_lookup //=.
      }
      intuition eauto.
    }
    iIntros "!> Hb_i".
    iApply "HΦ".
    iFrame.
    replace (int.nat (word.add i 1)) with (S (int.nat i)).
    2: {
      assert (int.val bks_s.(Slice.sz) ≤ 2^64 - 1) by word.
      word.
    }
    iFrame.
    iApply "Hupds".
    rewrite /is_update /=.
    eauto.
  }
  iIntros "[(?&?&?&?) Hbks_s]".
  iNamed.
  iApply "HΦ".
  iFrame "∗ #".
  rewrite take_ge.
  2: {
    rewrite fmap_length.
    lia.
  }
  admit.
*)
Admitted.

(* TODO: why do we need this here again? *)
Opaque is_sliding.


(* Lemma snapshot_memLog_txns_are γ l log diskEnd_pos diskEnd_txn_id :
  is_wal P l γ -∗
  memLog_linv γ log diskEnd_pos diskEnd_txn_id -∗
  (* TODO: shouldn't memStart_txn_id be the same as installed_txn_id? and
  shouldn't the logger have a lock on that? *)
  |={⊤}=> ∃ memStart_txn_id subtxns,
    ⌜length subtxns = (diskEnd_txn_id - memStart_txn_id)%nat⌝ ∗
    ⌜has_updates
      (take (slidingM.logIndex log diskEnd_pos) log.(slidingM.log))
      subtxns⌝ ∗
    txns_are γ memStart_txn_id subtxns ∗
    memLog_linv γ log diskEnd_pos diskEnd_txn_id.
Proof.
  iIntros "#Hwal HmemLog".
  iDestruct (restore_intro with "HmemLog") as "H".
  iNamed "H".
  iDestruct "H" as "[Hpure H]"; iNamed "Hpure". (* iNamedRestorable doesn't do
  this (due to something unexpected in iNamed) *)
  iDestruct (restore_elim with "H") as "#HmemLog"; iClear "H".
  iNamed "Htxns".
  iMod (txn_pos_valid_locked with "[$] HnextDiskEnd_txn Howntxns") as (HnextDiskEnd_txn%is_txn_bound) "Howntxns".
  iMod (get_txns_are _ _ _ _ memStart_txn_id diskEnd_txn_id with "Howntxns Hwal") as "[Htxns Howntxns]".
  { eauto. }
  { lia. }
  iModIntro.
  iExists memStart_txn_id, _; iFrame "Htxns".
  iSplitR.
  { iPureIntro.
    rewrite subslice_length; len. }
  iSplitR.
  { iPureIntro.
    admit. (* TODO: this seems false, we don't have anything about this specific
    range in the invariant... *)
  }
  iApply "HmemLog"; iFrame.
Admitted. *)

(* Lemma ghost_var_update_new_installed_emp γ l (installed_txn_id: nat) (new_installed_txn_id: nat) (txns: list (u64 * list update.t)):
  "#Hwal" ∷ is_wal P l γ -∗
  (* "%Hnew_installed_txn_id_bound" ∷ ⌜installed_txn_id ≤ new_installed_txn_id ≤ diskEnd_txn_id⌝ -∗ *)
  "Halready_installed_installer" ∷ ghost_var γ.(already_installed_name) (1 / 2) (∅: gset Z) -∗
  "Hnew_installed_installer" ∷ ghost_var γ.(new_installed_name) (1 / 2) installed_txn_id -∗
  "Hbeing_installed_txns_installer" ∷ ghost_var γ.(being_installed_txns_name) (1 / 2) txns -∗
  |={⊤}=> ∃ (new_txns: list (u64 * list update.t)),
    is_wal P l γ ∗
    ghost_var γ.(already_installed_name) (1 / 2) (∅: gset Z) ∗
    ghost_var γ.(new_installed_name) (1 / 2) new_installed_txn_id ∗
    ghost_var γ.(being_installed_txns_name) (1 / 2) new_txns.
Proof.
  iIntros "? ? ? ? ?".
  iNamed.

  iDestruct "Hwal" as "[Hwal Hcircular]".
  iInv "Hwal" as (σs) "[Hinner HP]" "Hclose".
  iDestruct "Hinner" as "(>%Hwf&Hmem&>?&>?&>?&>?)"; iNamed.
  iNamed "Hdisk".
  iNamed "Hdisk".
  iNamed "Hinstalled".
  iNamed "Howninstalled".

  iMod (ghost_var_update_halves new_installed_txn_id with "Hnew_installed_installer Hnew_installed") as
        "[Hnew_installed_installer Hnew_installed]".
  iMod (ghost_var_update_halves (subslice (S installed_txn_id0) (S new_installed_txn_id) σs.(log_state.txns))
    with "Hbeing_installed_txns_installer Hbeing_installed_txns") as
        "[Hbeing_installed_txns_installer Hbeing_installed_txns]".
  iMod ("Hclose" with "[Hmem Htxns_ctx γtxns HnextDiskEnd_inv Howncs γdiskEnd_txn_id2 Hdurable Hnew_installed Halready_installed Hbeing_installed_txns Hdata HP]").
  {
    iExists _.
    iFrame "% ∗".
    iExists _.
    iFrame.
    iExists _, _.
    iFrame "# ∗".
    iExists new_installed_txn_id, _.
    iFrame "Hnew_installed".
    iFrame "Halready_installed".
    iFrame "Hbeing_installed_txns".
    iSplitR.
    {
      iPureIntro.
      intuition lia.
    iFrame "Hdata".
  iExists _.
  iFrame "# % ∗".
  iNamed "Hmem".
Admitted. *)

Lemma readonly_struct_field_mapsto_agree E l d f v1 v2 :
  readonly (l ↦[d :: f] v1) -∗
  readonly (l ↦[d :: f] v2) -∗
  |={E}=> ⌜v1 = v2⌝.
Proof.
  iIntros "#H1 #H2".
  iMod (readonly_load with "H1") as (q1) "Hv1".
  iMod (readonly_load with "H2") as (q2) "Hv2".
  iDestruct (struct_field_mapsto_agree with "Hv1 Hv2") as "%Hv".
  done.
Qed.

Theorem wp_Walog__logInstall γ l dinit (installed_txn_id: nat) (subtxns: list (u64 * list update.t)) σₛ :
  {{{ "#st" ∷ readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      "#d" ∷ readonly (l ↦[Walog.S :: "d"] σₛ.(wal_d)) ∗
      "#memLock" ∷ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      "#condInstall" ∷ readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      "#Hwal" ∷ is_wal P l γ dinit ∗
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "His_locked" ∷ locked #σₛ.(memLock) ∗
      "#lk" ∷ is_lock N #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ) ∗
      "#cond_install" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      "Halready_installed_installer" ∷ ghost_var γ.(already_installed_name) (1/2) (∅: gset Z) ∗
      "Hinstalled_txn_installer" ∷ fmcounter γ.(installed_txn_name) (1/2) installed_txn_id ∗
      "Hbeing_installed_txns_installer" ∷ ghost_var γ.(being_installed_txns_name) (1/2) subtxns
  }}}
    Walog__logInstall #l
  {{{ (blkCount installEnd:u64), RET (#blkCount, #installEnd);
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "His_locked" ∷ locked #σₛ.(memLock)
  }}}.
Proof.
  wp_start.
  iNamedRestorable "Hlkinv".
  iNamedRestorable "Hfields".
  iNamed "Hfield_ptsto".

  iMod (is_wal_read_mem with "Hwal") as "#Hmem".
  wp_call.
  iNamed "Hmem".
  iClear "Hmem".
  iDestruct "Hstfields" as "(memLock'&d'&circ'&st'&Hstfields)".
  iMod (readonly_struct_field_mapsto_agree with "st st'") as "<-".
  iMod (readonly_struct_field_mapsto_agree with "memLock memLock'") as "<-".

  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.

  wp_apply (wp_sliding__takeTill with "His_memLog"); first by word.
  iIntros (q s) "(His_memLog&Htxn_slice)".

  iNamed "HmemLog_linv".

  iDestruct "Hwal" as "[Hwal Hcircular]".
  rewrite -fupd_wp.
  iInv "Hwal" as (σs) "[Hinner HP]" "Hclose".
  iDestruct "Hinner" as "(>%Hwf&#Hmem&>Htxns_ctx&>γtxns&>HnextDiskEnd_inv&>Hdisk)".
  iDestruct "Hdisk" as (cs) "(Howncs&Hdisk)".
  iDestruct "Hdisk" as (? ?) "(Hinstalled&Hdisk)".
  iDestruct "Hinstalled" as (? ?) "(Howninstalled&Hinstalled)".
  iNamed "Howninstalled".
  iNamed "Howninstalled".
  iDestruct (ghost_var_agree with "Halready_installed_installer Halready_installed") as %<-.
  iMod (ghost_var_update_halves (subslice (S installed_txn_id0) (S diskEnd_txn_id) σs.(log_state.txns))
    with "Hbeing_installed_txns_installer Hbeing_installed_txns") as
        "[Hbeing_installed_txns_installer Hbeing_installed_txns]".
  iMod ("Hclose" with "[Htxns_ctx γtxns HnextDiskEnd_inv Howncs Hinstalled_txn Halready_installed Hbeing_installed_txns Hdisk Hinstalled HP]") as "_".
  {
    iExists _.
    iFrame "∗ # %".
    iExists _.
    iFrame "∗ #".
    iExists _, _.
    iFrame "∗ #".
    iExists diskEnd_txn_id, _.
    iFrame.
    iNamed "Hinstalled".
    iSplitR.
    {
      iPureIntro.
      intuition lia.
    }
    iApply (big_sepM_mono with "Hdata").
    iIntros (addr blk Haddr_bound) "Hdata".
    destruct (decide (addr ∈ (∅ : gset _))); try set_solver.
    iDestruct "Hdata" as (b txn_id') "(%Hb&Haddr_d&%Haddr_bound')".
    iExists b, txn_id'.
    iFrame "∗ %". iPureIntro. intuition eauto.
    admit.
  }

  iModIntro.
  wp_pures.
  wp_apply wp_slice_len; wp_pures.
  wp_if_destruct; wp_pures.
  {
    iApply "HΦ".
    iFrame "His_locked".
    iApply "Hlkinv"; iFrameNamed.
    iSplitR "His_memLog HmemLog HdiskEnd Hshutdown Hnthread".
    {
      iExists _, _, _, _, _, _.
      iFrame "∗ # %".
    }
    iApply "Hfields"; iFrameNamed.
  }
  (* note that we get to keep Htxn_slice *)
  (* TODO: need to checkout some persistent fact that keeps these transactions
  tied to the abstract state, so that installBlocks can install them *)

  (* TODO: get a start position out of memLog_linv, combine with is_wal
  ([get_txns_are]) to extract exists subtxns corresponding to the updates in
  Htxn_slice *)

  wp_loadField.
  wp_apply (release_spec with "[$lk $His_locked HdiskEnd_circ Hstart_circ
    Howntxns HnextDiskEnd HownLoggerPos_linv HownLoggerTxn_linv Htxns
    His_memLog HmemLog HdiskEnd Hshutdown Hnthread]").
  {
    iNext.
    iApply "Hlkinv"; iFrameNamed.
    iSplitR "His_memLog HmemLog HdiskEnd Hshutdown Hnthread".
    {
      iExists _, _, _, _, _, _.
      iFrame "∗ # %".
    }
    iApply "Hfields"; iFrameNamed.
  }
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_pures.

  (* wp_apply wp_installBlocks. *)

  admit. (* TODO: need reasonably correct spec for installBlocks *)
Admitted.

Theorem wp_Walog__installer γ l dinit :
  {{{ is_wal P l γ dinit }}}
    Walog__installer #l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hwal HΦ".
  iMod (is_wal_read_mem with "Hwal") as "#Hmem".
  wp_call.
  iNamed "Hmem".
  iNamed "Hstfields".
  wp_loadField.
  wp_apply (acquire_spec with "lk").
  iIntros "[Hlocked Hlockinv]".
  wp_apply (wp_inc_nthread with "[$Hlockinv $st]"); iIntros "Hlockinv".
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (fun _ => "Hlockinv" ∷ wal_linv σₛ.(wal_st) γ ∗ "Hlocked" ∷ locked #σₛ.(memLock))%I
           with "[] [$Hlocked $Hlockinv]").
  { clear Φ.
    iIntros "!>" (Φ) "I HΦ"; iNamed "I".
    wp_apply (wp_load_shutdown with "[$st $Hlockinv]"); iIntros (shutdown) "Hlockinv".
    wp_pures.
    wp_if_destruct.
    - wp_pures.
      wp_apply (wp_Walog__logInstall with "[$Hwal $st $d $lk $memlock $condInstall $cond_install $Hlocked $Hlockinv]").
      { admit. (* XXX: need being_installed, installed_txn, and
      being_installed_txns ghost variables *) }
      iIntros (blkCount installEnd) "post"; iNamed "post".
      wp_pures.
      wp_bind (If _ _ _).
      wp_if_destruct.
      { wp_apply util_proof.wp_DPrintf; wp_pures.
        iApply ("HΦ" with "[$]"). }
      wp_loadField.
      wp_apply (wp_condWait with "[$cond_install $lk $His_locked $Hlkinv]").
      iIntros "[His_locked Hlkinv]".
      wp_pures.
      iApply ("HΦ" with "[$]").
    - iApply ("HΦ" with "[$]"). }
  iIntros "I"; iNamed "I".
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_dec_nthread with "[$Hlockinv $st]"); iIntros "Hlockinv".
  wp_loadField.
  wp_apply (wp_condSignal with "[$cond_shut]").
  wp_loadField.
  wp_apply (release_spec with "[$lk $Hlocked $Hlockinv]").
  iApply ("HΦ" with "[$]").
Admitted.

End goose_lang.
