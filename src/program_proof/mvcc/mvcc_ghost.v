From iris.algebra Require Import dfrac_agree.
From iris.algebra.lib Require Import mono_nat mono_list gmap_view.
From Perennial.program_proof Require Import disk_prelude.

Definition dbval := option u64.
Notation Nil := (None : dbval).
Notation Value x := (Some x : dbval).

Definition N_TXN_SITES : Z := 64.

Definition keys_all : gset u64 := fin_to_set u64.
Definition sids_all : list u64 := U64 <$> seqZ 0 N_TXN_SITES.

(* Tuple-related RAs. *)
Local Definition vchainR := mono_listR (leibnizO dbval).
Local Definition key_vchainR := gmapR u64 vchainR.
(* GC-related RAs. *)
Local Definition tidsR := gmap_viewR u64 (leibnizO unit).
Local Definition sid_tidsR := gmapR u64 tidsR.
Local Definition sid_min_tidR := gmapR u64 mono_natR.
(* SST-related RAs. (SST = Strictly Serializable Transactions) *)
Local Definition tid_modsR := gmap_viewR (u64 * (gmap u64 u64)) (leibnizO unit).

Lemma sids_all_lookup (sid : u64) :
  int.Z sid < N_TXN_SITES ->
  sids_all !! (int.nat sid) = Some sid.
Proof.
  intros H.
  unfold sids_all.
  rewrite list_lookup_fmap.
  rewrite lookup_seqZ_lt; last word.
  simpl. f_equal. word.
Qed.

Class mvcc_ghostG Σ :=
  {
    (* tuple *)
    mvcc_key_vchainG :> inG Σ key_vchainR;
    (* GC *)
    mvcc_sid_tidsG :> inG Σ sid_tidsR;
    mvcc_sid_min_tidG :> inG Σ sid_min_tidR;
    (* SST *)
    mvcc_abort_tids_ncaG :> inG Σ tidsR;
    mvcc_abort_tids_faG :> inG Σ tidsR;
    mvcc_abort_tids_fciG :> inG Σ tid_modsR;
    mvcc_abort_tids_fccG :> inG Σ tid_modsR;
    mvcc_commit_tidsG :> inG Σ tid_modsR;
  }.

Definition mvcc_ghostΣ :=
  #[
     GFunctor key_vchainR;
     GFunctor sid_tidsR;
     GFunctor sid_min_tidR;
     GFunctor tidsR;
     GFunctor tidsR;
     GFunctor tid_modsR;
     GFunctor tid_modsR;
     GFunctor tid_modsR
   ].

Global Instance subG_mvcc_ghostG {Σ} :
  subG mvcc_ghostΣ Σ → mvcc_ghostG Σ.
Proof. solve_inG. Qed.

(* TODO: remove the [mvcc_] prefix? *)
Record mvcc_names :=
  {
    mvcc_key_vchain : gname;
    mvcc_sid_tids_gn : gname;
    mvcc_sid_min_tid_gn : gname;
    mvcc_abort_tids_nca : gname;
    mvcc_abort_tids_fa : gname;
    mvcc_abort_tids_fci : gname;
    mvcc_abort_tids_fcc : gname;
    mvcc_commit_tids : gname
  }.

Section definitions.
Context `{!mvcc_ghostG Σ}.

Definition mvccN := nroot.
Definition mvccNTuple := nroot .@ "tuple".
Definition mvccNGC := nroot .@ "gc".

Definition vchain_ptsto γ q (k : u64) (vchain : list dbval) : iProp Σ :=
  own γ.(mvcc_key_vchain) {[k := ●ML{# q } (vchain : list (leibnizO dbval))]}.

Definition vchain_lb γ (k : u64) (vchain : list dbval) : iProp Σ :=
  own γ.(mvcc_key_vchain) {[k := ◯ML (vchain : list (leibnizO dbval))]}.

Definition view_ptsto γ (k : u64) (v : option u64) (tid : u64) : iProp Σ :=
  ∃ vchain, vchain_lb γ k vchain ∗ ⌜vchain !! (int.nat tid) = Some v⌝.

Definition mods_token γ (k tid : u64) : iProp Σ :=
  ∃ vchain, vchain_ptsto γ (1/4) k vchain ∗ ⌜Z.of_nat (length vchain) ≤ (int.Z tid) + 1⌝.

(* Definitions/theorems about GC-related resources. *)
Definition site_active_tids_half_auth γ (sid : u64) tids : iProp Σ :=
  own γ.(mvcc_sid_tids_gn) {[sid := (gmap_view_auth (DfracOwn (1 / 2)) tids)]}.

Definition site_active_tids_frag γ (sid : u64) tid : iProp Σ :=
  own γ.(mvcc_sid_tids_gn) {[sid := (gmap_view_frag (V:=leibnizO unit) tid (DfracOwn 1) tt)]}.

Definition active_tid γ (tid sid : u64) : iProp Σ :=
  (site_active_tids_frag γ sid tid ∧ ⌜int.Z sid < N_TXN_SITES⌝) ∧ ⌜0 < int.Z tid < 2 ^ 64 - 1⌝ .

Definition site_min_tid_half_auth γ (sid : u64) tidN : iProp Σ :=
  own γ.(mvcc_sid_min_tid_gn) {[sid := (●MN{#(1 / 2)} tidN)]}.

Definition site_min_tid_lb γ (sid : u64) tidN : iProp Σ :=
  own γ.(mvcc_sid_min_tid_gn) {[sid := (◯MN tidN)]}.

Definition min_tid_lb γ tidN : iProp Σ :=
  [∗ list] sid ∈ sids_all, site_min_tid_lb γ sid tidN.

Definition mvcc_inv_tuple_def γ : iProp Σ :=
  [∗ set] key ∈ keys_all,
    ∃ (vchain : list dbval),
      vchain_ptsto γ (1/2) key vchain.

Definition mvcc_inv_gc_def γ : iProp Σ :=
  [∗ list] sid ∈ sids_all,
    ∃ (tids : gmap u64 unit) (tidmin : u64),
      site_active_tids_half_auth γ sid tids ∗
      site_min_tid_half_auth γ sid (int.nat tidmin) ∗
      ∀ tid, ⌜tid ∈ (dom tids) -> (int.nat tidmin) ≤ (int.nat tid)⌝.

End definitions.

Section mvccinv.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition mvcc_inv_tuple γ : iProp Σ :=
  inv mvccNTuple (mvcc_inv_tuple_def γ).

Definition mvcc_inv_gc γ : iProp Σ :=
  inv mvccNGC (mvcc_inv_gc_def γ).

End mvccinv.

Section lemmas.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Lemma vchain_combine {γ} q {q1 q2 key vchain1 vchain2} :
  (q1 + q2 = q)%Qp ->
  vchain_ptsto γ q1 key vchain1 -∗
  vchain_ptsto γ q2 key vchain2 -∗
  vchain_ptsto γ q key vchain1 ∧ ⌜vchain2 = vchain1⌝.
Proof.
  iIntros "%Hq Hv1 Hv2".
  iCombine "Hv1 Hv2" as "Hv".
  iDestruct (own_valid with "Hv") as %Hvalid.
  rewrite singleton_valid mono_list_auth_dfrac_op_valid_L in Hvalid.
  destruct Hvalid as [_ <-].
  rewrite -mono_list_auth_dfrac_op dfrac_op_own Hq.
  naive_solver.
Qed.

Lemma vchain_split {γ q} q1 q2 {key vchain} :
  (q1 + q2 = q)%Qp ->
  vchain_ptsto γ q key vchain -∗
  vchain_ptsto γ q1 key vchain ∗ vchain_ptsto γ q2 key vchain.
Proof.
  iIntros "%Hq Hv".
  unfold vchain_ptsto.
  rewrite -Hq.
  rewrite -dfrac_op_own.
  (* rewrite mono_list_auth_dfrac_op. *)
Admitted.

Lemma vchain_witness γ q k vchain :
  vchain_ptsto γ q k vchain -∗ vchain_lb γ k vchain.
Proof.
  iApply own_mono.
  apply singleton_mono, mono_list_included.
Qed.

Lemma vchain_update {γ E key vchain} vchain' :
  prefix vchain vchain' →
  ↑mvccNTuple ⊆ E ->
  mvcc_inv_tuple γ -∗
  vchain_ptsto γ (1 / 2) key vchain ={E}=∗
  vchain_ptsto γ (1 / 2) key vchain'.
Proof.
  iIntros "%Hprefix %Hsubseteq #Hinvtuple Hvchain".
  iInv "Hinvtuple" as ">HinvtupleO" "HinvtupleC".
  unfold mvcc_inv_tuple_def.
  iDestruct (big_sepS_elem_of_acc _ _ key with "HinvtupleO") as "[HvchainInv HvchainInvC]"; first set_solver.
  iDestruct "HvchainInv" as (vchainInv') "HvchainInv".
  iDestruct (vchain_combine 1%Qp with "Hvchain HvchainInv") as "[Hvchain ->]"; first compute_done.
  iMod (own_update with "Hvchain") as "Hvchain".
  { apply singleton_update, mono_list_update, Hprefix. }
  iDestruct (vchain_split (1 / 2) (1 / 2) with "Hvchain") as "[Hvchain Hvchain']"; first compute_done.
  iDestruct ("HvchainInvC" with "[Hvchain]") as "Hvchains"; first auto.
  iMod ("HinvtupleC" with "[Hvchains]") as "_"; done.
Qed.

Lemma vchain_false {γ E q key vchain} :
  (1 / 2 < q)%Qp ->
  ↑mvccNTuple ⊆ E ->
  mvcc_inv_tuple γ -∗
  vchain_ptsto γ q key vchain ={E}=∗
  False.
Proof.
  iIntros "%Hq %Hsubseteq #Hinvtuple Hvchain".
  iInv "Hinvtuple" as ">HinvtupleO" "HinvtupleC".
  unfold mvcc_inv_tuple_def.
  iDestruct (big_sepS_elem_of_acc _ _ key with "HinvtupleO") as "[HvchainInv HvchainInvC]"; first set_solver.
  iDestruct "HvchainInv" as (vchainInv') "HvchainInv".
  iDestruct (vchain_combine (q + 1 / 2) with "Hvchain HvchainInv") as "[Hvchain ->]"; first done.
  iDestruct (own_valid with "Hvchain") as %Hvalid.
  rewrite singleton_valid mono_list_auth_dfrac_valid dfrac_valid_own in Hvalid.
  by rewrite (Qp_add_lt_mono_r _ _ (1 / 2)) Qp_half_half Qp_lt_nge in Hq.
Qed.

Theorem view_ptsto_agree γ (k : u64) (v v' : option u64) (tid : u64) :
  view_ptsto γ k v tid -∗ view_ptsto γ k v' tid -∗ ⌜v = v'⌝.
Admitted.

Lemma site_active_tids_elem_of γ (sid : u64) tids tid :
  site_active_tids_half_auth γ sid tids -∗ site_active_tids_frag γ sid tid -∗ ⌜tid ∈ (dom tids)⌝.
Admitted.

Lemma site_active_tids_agree γ (sid : u64) tids tids' :
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids' -∗
  ⌜tids = tids'⌝.
Admitted.

Lemma site_active_tids_insert {γ sid tids} tid :
  tid ∉ dom tids ->
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids ==∗
  site_active_tids_half_auth γ sid (<[tid := tt]>tids) ∗
  site_active_tids_half_auth γ sid (<[tid := tt]>tids) ∗
  site_active_tids_frag γ sid tid.
Admitted.

Lemma site_active_tids_delete {γ sid tids} tid :
  site_active_tids_frag γ sid tid -∗
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids ==∗
  site_active_tids_half_auth γ sid (delete tid tids) ∗
  site_active_tids_half_auth γ sid (delete tid tids). 
Admitted.

Lemma site_min_tid_valid γ (sid : u64) tidN tidlbN :
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_lb γ sid tidlbN -∗
  ⌜(tidlbN ≤ tidN)%nat⌝.
Admitted.

Lemma site_min_tid_lb_weaken γ (sid : u64) tidN tidN' :
  (tidN' ≤ tidN)%nat ->
  site_min_tid_lb γ sid tidN -∗
  site_min_tid_lb γ sid tidN'.
Admitted.

Lemma site_min_tid_agree γ (sid : u64) tidN tidN' :
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_half_auth γ sid tidN' -∗
  ⌜tidN = tidN'⌝.
Admitted.

Lemma site_min_tid_update {γ sid tidN} tidN' :
  (tidN ≤ tidN')%nat ->
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_half_auth γ sid tidN ==∗
  site_min_tid_half_auth γ sid tidN' ∗ site_min_tid_half_auth γ sid tidN'.
Admitted.

Lemma site_min_tid_witness {γ sid tidN} :
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_lb γ sid tidN.
Admitted.

Lemma min_tid_lb_zero γ :
  ⊢ min_tid_lb γ 0%nat.
Admitted.

Lemma mvcc_ghost_init :
  ⊢ |==> ∃ γ, mvcc_inv_tuple_def γ ∗
              ([∗ set] key ∈ keys_all, vchain_ptsto γ (1/2) key [Nil]) ∗
              mvcc_inv_gc_def γ ∗
              ([∗ list] sid ∈ sids_all, site_active_tids_half_auth γ sid ∅) ∗
              ([∗ list] sid ∈ sids_all, site_min_tid_half_auth γ sid 0).
Admitted.

Theorem active_ge_min γ (tid tidlb : u64) (sid : u64) :
  mvcc_inv_gc_def γ -∗
  active_tid γ tid sid -∗
  min_tid_lb γ (int.nat tidlb) -∗
  ⌜int.Z tidlb ≤ int.Z tid⌝.
Proof using heapGS0 mvcc_ghostG0 Σ.
  iIntros "Hinv Hactive Hlb".
  iDestruct "Hactive" as "[[Htid %Hlookup] _]".
  apply sids_all_lookup in Hlookup.
  apply elem_of_list_lookup_2 in Hlookup.
  iDestruct (big_sepL_elem_of with "Hlb") as "Htidlb"; first done.
  iDestruct (big_sepL_elem_of with "Hinv") as (tids tidmin) "(Htids & Htidmin & %Hle)"; first done.
  (* Obtaining [tidmin ≤ tid]. *)
  iDestruct (site_active_tids_elem_of with "Htids Htid") as "%Helem".
  apply Hle in Helem.
  (* Obtaining [tidlb ≤ tidmin]. *)
  iDestruct (site_min_tid_valid with "Htidmin Htidlb") as "%Hle'".
  iPureIntro.
  apply Z.le_trans with (int.Z tidmin); word.
Qed.

End lemmas.


Section event.

Inductive event :=
| EvCommit (tid : u64) (mods : gmap u64 u64)
| EvRead   (tid : u64) (key : u64)
| EvAbort  (tid : u64).

Definition head_commit (tid : u64) (mods : gmap u64 u64) (l : list event) :=
  head l = Some (EvCommit tid mods).

Definition head_read (tid : u64) (key : u64) (l : list event) :=
  head l = Some (EvRead tid key).

Definition head_abort (tid : u64) (l : list event) :=
  head l = Some (EvAbort tid).

Definition no_commit_abort (tid : u64) (l : list event) :=
  (∀ mods, EvCommit tid mods ∉ l) ∧
  (EvAbort tid ∉ l).

Definition first_abort (tid : u64) (l : list event) :=
  ∃ e lp ls,
    e = EvAbort tid ∧
    l = lp ++ e :: ls ∧
    no_commit_abort tid lp.

Definition compatible (tid : u64) (mods : gmap u64 u64) (e : event) :=
  match e with
  | EvCommit tid' mods' => (int.Z tid') < (int.Z tid) ∨ (dom mods) ∩ (dom mods') = ∅
  | EvRead tid' key => (int.Z tid') ≤ (int.Z tid) ∨ key ∉ (dom mods)
  | EvAbort tid' => True
  end.

Instance compatible_dec tid mods e : Decision (compatible tid mods e).
Proof. destruct e; simpl; apply _. Defined.

Definition incompatible (tid : u64) (mods : gmap u64 u64) (e : event) := not (compatible tid mods e).

Instance incompatible_dec tid mods e : Decision (incompatible tid mods e).
Proof. destruct e; simpl; apply _. Defined.

Definition compatible_all (tid : u64) (mods : gmap u64 u64) (l : list event) :=
  Forall (compatible tid mods) l.

Definition incompatible_exists (tid : u64) (mods : gmap u64 u64) (l : list event) :=
  Exists (incompatible tid mods) l.

Definition first_commit (tid : u64) (mods : gmap u64 u64) (l lp ls : list event) (e : event) :=
  e = EvCommit tid mods ∧
  l = lp ++ e :: ls ∧
  no_commit_abort tid lp.

Definition first_commit_incompatible (tid : u64) (mods : gmap u64 u64) (l : list event) :=
  ∃ e lp ls,
    first_commit tid mods l lp ls e ∧
    incompatible_exists tid mods lp.

Definition first_commit_compatible (tid : u64) (mods : gmap u64 u64) (l : list event) :=
  ∃ e lp ls,
    first_commit tid mods l lp ls e ∧
    compatible_all tid mods lp.

Definition is_commit_abort_tid (tid : u64) (e : event) : Prop :=
  match e with
  | EvCommit tid' _ => tid = tid'
  | EvAbort tid' => tid = tid'
  | _ => False
  end.

Instance is_commit_abort_dec tid e : Decision (is_commit_abort_tid tid e).
Proof. destruct e; simpl; apply _. Defined.

Lemma is_commit_abort_tid_lor tid e :
  is_commit_abort_tid tid e ->
  (∃ mods, e = EvCommit tid mods) ∨ e = EvAbort tid.
Proof. intros. destruct e; set_solver. Qed.

Fixpoint find_max_prefix (tid : u64) (lp ls : list event) : (list event * list event) :=
  match ls with
  | [] => (lp, ls)
  | hd :: tl => if decide (is_commit_abort_tid tid hd)
              then (lp, ls)
              else find_max_prefix tid (lp ++ [hd]) tl
  end.

Lemma spec_find_max_prefix tid lp ls :
  ∃ ls1 ls2,
    (lp ++ ls1, ls2) = find_max_prefix tid lp ls ∧
    ls = ls1 ++ ls2 ∧
    no_commit_abort tid ls1 ∧
    (match head ls2 with
     | Some e => is_commit_abort_tid tid e
     | _ => True
     end).
Proof.
  generalize dependent lp.
  unfold no_commit_abort.
  induction ls as [| e ls IHls]; intros lp; simpl.
  - exists [], [].
    split; first by rewrite app_nil_r.
    set_solver.
  - case_decide.
    + exists [], (e :: ls).
      split; first by rewrite app_nil_r.
      set_solver.
    + destruct (IHls (lp ++ [e])) as (ls1 & ls2 & Heq & Hls2 & Hnca & Hhead).
      exists ([e] ++ ls1), ls2.
      rewrite -Heq.
      split; first by rewrite app_assoc.
      split; set_solver.
Qed.

Inductive tcform :=
| NCA
| FA
| FCI (mods : gmap u64 u64)
| FCC (mods : gmap u64 u64).

Definition peek (tid : u64) (l : list event) : tcform :=
  let (lp, ls) := find_max_prefix tid [] l
  in match head ls with
     | None => NCA
     | Some e => match e with
                | EvCommit _ mods => if decide (compatible_all tid mods lp) then FCC mods else FCI mods
                | _ => FA
                end
     end.

Theorem spec_peek tid l :
  match peek tid l with
  | NCA => no_commit_abort tid l
  | FA => first_abort tid l
  | FCI mods => first_commit_incompatible tid mods l
  | FCC mods => first_commit_compatible tid mods l
  end.
Proof.
  unfold peek.
  destruct (spec_find_max_prefix tid [] l) as (lp & ls & Hspec & Hl & Hnca & Hls).
  rewrite -Hspec.
  destruct (head ls) eqn:Els.
  - destruct e eqn:Ee.
    + simpl.
      apply is_commit_abort_tid_lor in Hls.
      destruct Hls as [[mods' Hls] | Hls]; last set_solver.
      inversion Hls. subst tid0 mods'.
      assert (Hfc : first_commit tid mods l lp (tail ls) e).
      { unfold first_commit.
        split; first done.
        split; last done.
        rewrite Hl.
        f_equal.
        rewrite Ee.
        by apply hd_error_tl_repr.
      }
      case_decide.
      * unfold first_commit_compatible.
        exists (EvCommit tid mods), lp, (tail ls).
        by rewrite Ee in Hfc.
      * unfold first_commit_incompatible.
        exists (EvCommit tid mods), lp, (tail ls).
        unfold compatible_all in H.
        apply not_Forall_Exists in H; last apply _.
        by rewrite Ee in Hfc.
    + unfold is_commit_abort_tid in Hls. set_solver.
    + apply is_commit_abort_tid_lor in Hls.
      destruct Hls; first set_solver.
      inversion H. subst tid0.
      unfold first_abort.
      exists (EvAbort tid), lp, (tail ls).
      split; first done.
      split; last done.
      rewrite Hl.
      f_equal.
      by apply hd_error_tl_repr.
  - apply head_None in Els.
    rewrite Els in Hl. rewrite app_nil_r in Hl. by rewrite Hl.
Qed.

Lemma no_commit_abort_false (tid : u64) (l : list event) :
  no_commit_abort tid l ->
  (∃ mods, head_commit tid mods l) ∨ (head_abort tid l) ->
  False.
Proof.
  intros [HnotinC HnotinA] [[mods Hhead] | Hhead]; apply head_Some_elem_of in Hhead; set_solver.
Qed.

Lemma head_middle {X} (l lp ls : list X) (x : X) :
  l = lp ++ x :: ls ->
  head l = head (lp ++ [x]).
Proof.
  intros Hl. rewrite Hl. destruct lp; auto.
Qed.

Lemma first_abort_false (tid : u64) (mods : gmap u64 u64) (l : list event) :
  first_abort tid l ->
  head_commit tid mods l ->
  False.
Proof.
  intros (e & lp & ls & He & Hl & HnotinC & _) Hhead.
  unfold head_commit in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  apply head_Some_elem_of in Hhead.
  set_solver.
Qed.

Lemma first_commit_false (tid : u64) (mods : gmap u64 u64) (l lp ls : list event) (e : event) :
  first_commit tid mods l lp ls e ->
  head_abort tid l ->
  False.
Proof.
  intros (He & Hl & _ & HnotinA) Hhead.
  unfold head_abort in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  apply head_Some_elem_of in Hhead.
  set_solver.
Qed.

Lemma safe_extension (tid tid' : u64) (mods : gmap u64 u64) (key : u64) (l : list event) :
  first_commit_compatible tid mods l ->
  head_read tid' key l ->
  key ∈ (dom mods) ->
  (int.Z tid') ≤ (int.Z tid).
Proof.
  intros (e & lp & ls & (He & Hl & _) & Hcomp) Hhead Hin.
  unfold head_read in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  destruct lp; first set_solver.
  simpl in Hhead.
  inversion Hhead.
  unfold compatible_all in Hcomp.
  rewrite Forall_forall in Hcomp.
  destruct (Hcomp (EvRead tid' key)); [| done | done].
  rewrite H0.
  apply elem_of_list_here.
Qed.

Lemma first_commit_incompatible_false (tid : u64) (mods : gmap u64 u64) (l : list event) :
  first_commit_incompatible tid mods l ->
  head_commit tid mods l ->
  False.
Proof.
  intros (e & lp & ls & (_ & Hl & [HnotinC _]) & Hincomp) Hhead.
  destruct lp; first by apply Exists_nil in Hincomp.
  unfold head_commit in Hhead.
  set_solver.
Qed.


End event.
