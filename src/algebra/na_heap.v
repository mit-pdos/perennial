From stdpp Require Export namespaces.
From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree reservation_map.
From iris.algebra Require Export dfrac.
From iris.algebra Require Import csum excl auth cmra_big_op numbers lib.gmap_view.
From iris.bi Require Import fractional.
From Perennial.base_logic Require Export lib.own.
From iris.proofmode Require Export tactics.
From Perennial.algebra Require Export blocks.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Import uPred.

(* Heap that supports non-atomic operations. Very mildly adapted from
   lambda-rust by Jung et al., and generalized to support arbitrary
   domains/ranges of values, as opposed to lambda-rust locs and values.

   This is used for the physical heap in GooseLang. *)

Definition lock_stateR : cmra :=
  csumR unitR natR.

Instance lock_stateR_total : CmraTotal lock_stateR.
Proof. rewrite /CmraTotal. destruct x; eauto. Qed.

Definition na_heap_cmra (V : Type) : cmra :=
  prodR lock_stateR (agreeR (leibnizO V)).

Definition na_heapUR (L V: Type) `{Countable L} : ucmra :=
  gmap_viewUR L (na_heap_cmra V).

Definition na_sizeUR (L: Type) `{Countable L} : ucmra :=
  gmapUR L (agreeR (leibnizO Z)).

Class na_heapGS (L V: Type) Σ `{BlockAddr L} := Na_HeapG {
  na_heap_inG :> inG Σ (na_heapUR L V);
  na_size_inG :> inG Σ (authR (na_sizeUR Z));
  na_meta_inG :> inG Σ (gmap_viewR L (agreeR gnameO));
  na_meta_data_inG :> inG Σ (reservation_mapR (agreeR positiveO));
  na_heap_name : gname;
  na_size_name : gname;
  na_meta_name : gname
}.

Arguments na_heap_name {_ _ _ _ _ _} _ : assert.
Arguments na_size_name {_ _ _ _ _ _} _ : assert.
Arguments na_meta_name {_ _ _ _ _ _} _ : assert.

Class na_heapGpreS (L V : Type) (Σ : gFunctors) `{BlockAddr L} := {
  na_heap_preG_inG :> inG Σ (na_heapUR L V);
  na_size_preG_inG :> inG Σ (authR (na_sizeUR Z));
  na_meta_preG_inG :> inG Σ (gmap_viewR L (agreeR gnameO));
  na_meta_data_preG_inG :> inG Σ (reservation_mapR (agreeR positiveO));
}.

Definition na_heapΣ (L V : Type) `{BlockAddr L} : gFunctors := #[
  GFunctor (na_heapUR L V);
  GFunctor (authR (na_sizeUR Z));
  GFunctor (gmap_viewR L (agreeR gnameO));
  GFunctor (reservation_mapR (agreeR positiveO))
].

Ltac solve_inG_deep :=
  intros; lazymatch goal with
   | H:subG (?xΣ _ _ _ _ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _ _) _ |- _ => try unfold xΣ in H
   | H:subG (?xΣ _) _ |- _ => try unfold xΣ in H
   | H:subG ?xΣ _ |- _ => try unfold xΣ in H
   end; repeat match goal with
               | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
               end; repeat match goal with
                           | H:subG _ _ |- _ =>apply subG_inG in H || clear H
                           end; intros; try done; split; assumption || by apply _.

#[global]
Instance subG_na_heapPreG {Σ L V} `{BlockAddr L} :
  subG (na_heapΣ L V) Σ → na_heapGpreS L V Σ.
Proof. solve_inG_deep. Qed.

Inductive lock_state :=
  | WSt : lock_state
  | RSt: nat → lock_state.

Definition to_lock_stateR (x : lock_state) : lock_stateR :=
  match x with RSt n => Cinr n | WSt => Cinl (()) end.

Definition to_na_heap {L V LK} `{Countable L} (tls : LK → lock_state) :
  gmap L (LK * V) → gmap L (na_heap_cmra _) :=
  fmap (λ v, (to_lock_stateR $ tls v.1, to_agree v.2)).

Definition to_na_size {L} `{Countable L} :
  gmap L Z → na_sizeUR L := fmap (λ v, to_agree v).

Section definitions.
  Context `{BlockAddr L, hG : !na_heapGS L V Σ}.
  Context `{LK} (tls: LK → lock_state).

  Definition na_heap_pointsto_st (st : lock_state)
             (l : L) (dq : dfrac) (v: V) : iProp Σ :=
    own (na_heap_name hG) (@gmap_view_frag L _ _ (na_heap_cmra V) l dq (to_lock_stateR st, to_agree v)).

  Definition na_heap_pointsto_def (l : L) (dq : dfrac) (v: V) : iProp Σ :=
    na_heap_pointsto_st (RSt 0) l dq v.
  Definition na_heap_pointsto_aux : seal (@na_heap_pointsto_def). by eexists. Qed.
  Definition na_heap_pointsto := unseal na_heap_pointsto_aux.
  Definition na_heap_pointsto_eq : @na_heap_pointsto = @na_heap_pointsto_def :=
    seal_eq na_heap_pointsto_aux.

  Definition na_block_size_def (l: L) (z: Z) : iProp Σ :=
    own (na_size_name hG) (◯ {[ addr_id l := to_agree z ]}).
  Definition na_block_size_aux : seal (@na_block_size_def). by eexists. Qed.
  Definition na_block_size := unseal na_block_size_aux.
  Definition na_block_size_eq : @na_block_size = @na_block_size_def :=
    seal_eq na_block_size_aux.

  Definition meta_token_def (l : L) (E : coPset) : iProp Σ :=
    (∃ γm, own (na_meta_name hG) (gmap_view_frag l DfracDiscarded (to_agree γm)) ∗
           own γm (reservation_map_token E))%I.
  Definition meta_token_aux : seal (@meta_token_def). Proof. by eexists. Qed.
  Definition meta_token := meta_token_aux.(unseal).
  Definition meta_token_eq : @meta_token = @meta_token_def := meta_token_aux.(seal_eq).

  Definition meta_def `{Countable A} (l : L) (N : namespace) (x : A) : iProp Σ :=
    (∃ γm, own (na_meta_name hG) (gmap_view_frag l DfracDiscarded (to_agree γm)) ∗
           own γm (reservation_map_data (positives_flatten N) (to_agree (encode x))))%I.
  Definition meta_aux : seal (@meta_def). Proof. by eexists. Qed.
  Definition meta {A dA cA} := meta_aux.(unseal) A dA cA.
  Definition meta_eq : @meta = @meta_def := meta_aux.(seal_eq).

  Definition block_sizes_wf (σ: gmap L (LK * V)) (sz: gmap Z Z) : Prop :=
    (∀ l z, l ∈ dom σ → sz !! addr_id l = Some z → (0 ≤ addr_offset l < z)%Z) ∧
    (∀ l, l ∈ dom sz → addr_encode (l, 0)%Z ∈ dom σ).

  Definition na_heap_ctx (σ:gmap L (LK * V)) : iProp Σ := (∃ (m : gmap L (agreeR gnameO)) (sz: gmap Z Z),
    ⌜ dom m ⊆ dom σ ⌝ ∧
     own (na_heap_name hG) (@gmap_view_auth _ _ _ (na_heap_cmra V) (DfracOwn 1) (to_na_heap tls σ)) ∗
     own (na_meta_name hG) (gmap_view_auth (DfracOwn 1) m) ∗
     own (na_size_name hG) (● to_na_size sz) ∗
     ⌜ block_sizes_wf σ sz ⌝ )%I.
End definitions.

Typeclasses Opaque na_heap_pointsto.
#[global]
Instance: Params (@na_heap_pointsto) 8 := {}.

Notation "l ↦{# q } v" := (na_heap_pointsto l (DfracOwn q) v)
  (at level 20, q at level 50, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦□ v" := (na_heap_pointsto l DfracDiscarded v)
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{ dq } v" := (na_heap_pointsto l dq v)
  (at level 20, dq at level 50, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦ v" := (na_heap_pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.

Local Notation "l ↦{# q } -" := (∃ v, l ↦{#q} v)%I
  (at level 20, q at level 50, format "l  ↦{# q }  -") : bi_scope.
Local Notation "l ↦□ -" := (∃ v, l ↦□ v)%I
  (at level 20, format "l  ↦□  -") : bi_scope.
Local Notation "l ↦{ dq } -" := (∃ v, l ↦{dq} v)%I
  (at level 20, dq at level 50, format "l  ↦{ dq }  -") : bi_scope.
Local Notation "l ↦ -" := (l ↦{#1} -)%I (at level 20) : bi_scope.

Section to_na_heap.
  Context (L V LK : Type) `{Countable L}.
  Implicit Types σ : gmap L (LK * V).
  Implicit Types m : gmap L gname.

  Lemma to_na_heap_valid tls σ : ✓ to_na_heap tls σ.
  Proof.
    intros l. rewrite lookup_fmap.
    case (σ !! l) =>//=. intros (lk&v) => //=. destruct (tls lk) => //=.
  Qed.

  Lemma lookup_to_na_heap_None tls σ l : σ !! l = None → to_na_heap tls σ !! l = None.
  Proof. by rewrite /to_na_heap lookup_fmap=> ->. Qed.

  Lemma to_na_heap_insert tls σ l x v :
    to_na_heap tls (<[l:=(x, v)]> σ)
    = <[l:=(to_lock_stateR (tls x), to_agree v)]> (to_na_heap tls σ).
  Proof. by rewrite /to_na_heap fmap_insert. Qed.

  Lemma to_na_heap_delete tls σ l : to_na_heap tls (delete l σ) = delete l (to_na_heap tls σ).
  Proof. by rewrite /to_na_heap fmap_delete. Qed.
End to_na_heap.

Section to_na_size.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : gmap L Z.

  Lemma to_na_size_valid σ : ✓ to_na_size σ.
  Proof. intros l. rewrite lookup_fmap. case (σ !! l) =>//=. Qed.

  Lemma lookup_to_na_size_None σ l : σ !! l = None → to_na_size σ !! l = None.
  Proof. by rewrite /to_na_size lookup_fmap=> ->. Qed.

  Lemma to_na_size_insert σ l z :
    to_na_size (<[l:=z]> σ)
    = <[l:=(to_agree z)]> (to_na_size σ).
  Proof. by rewrite /to_na_size fmap_insert. Qed.

End to_na_size.

Lemma na_heap_init `{BlockAddr L, !na_heapGpreS L V Σ} {LK} (tls: LK → lock_state) σ :
  ⊢ |==> ∃ _ : na_heapGS L V Σ, na_heap_ctx tls σ.
Proof.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) (to_na_heap tls σ))) as (γh) "Hh".
  { apply gmap_view_auth_valid. }
  iMod (own_alloc (● to_na_size ∅)) as (γs) "Hs".
  { rewrite auth_auth_valid. exact: to_na_size_valid. }
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) (∅ : gmap L (agreeR gnameO)))) as (γm) "Hm".
  { apply gmap_view_auth_valid. }
  iModIntro. iExists (Na_HeapG L V Σ _ _ _ _ _ _ _ γh γs γm).
  iExists ∅, ∅; simpl. iFrame "Hh Hm". rewrite dom_empty_L. iFrame.
  iPureIntro; split.
  - set_solver.
  - rewrite /block_sizes_wf. set_solver.
Qed.

Section na_heap.
  Context {L V} {LK: Type} `{BlockAddr L, hG: !na_heapGS L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L (LK * V).
  Implicit Types m : gmap L gname.
  Implicit Types sz : gmap Z Z.
  Implicit Types h g : na_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.
  Implicit Types E : coPset.

  (** General properties of pointsto and freeable *)
  Global Instance na_heap_pointsto_timeless l dq v : Timeless (l↦{dq}v).
  Proof. rewrite na_heap_pointsto_eq /na_heap_pointsto_def. apply _. Qed.

  Global Instance na_heap_pointsto_st_fractional l v: Fractional (λ q, na_heap_pointsto_st WSt l (DfracOwn q) v)%I.
  Proof.
    intros p q. rewrite /na_heap_pointsto_st.
    rewrite -own_op -gmap_view_frag_add -pair_op.
    rewrite agree_idemp.
    rewrite // Cinl_op.
  Qed.

  Global Instance na_heap_pointsto_st_as_fractional l q v:
    AsFractional (na_heap_pointsto_st WSt l (DfracOwn q) v) (λ q, na_heap_pointsto_st WSt l (DfracOwn q) v)%I q.
  Proof. split; first done. apply _. Qed.

  Global Instance na_heap_pointsto_fractional l v: Fractional (λ q, l ↦{#q} v)%I.
  Proof.
    intros p q.
    rewrite na_heap_pointsto_eq -own_op -gmap_view_frag_add -pair_op.
    rewrite agree_idemp.
    rewrite // Cinr_op.
  Qed.
  Global Instance na_heap_pointsto_as_fractional l q v:
    AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Global Instance na_heap_pointsto_persistent l v : Persistent (l ↦□ v).
  Proof. rewrite na_heap_pointsto_eq. apply _. Qed.

  Lemma na_heap_pointsto_persist l dq v:
    l ↦{dq} v ==∗ l ↦□ v.
  Proof.
    rewrite na_heap_pointsto_eq.
    iApply own_update.
    apply gmap_view_frag_persist.
  Qed.

  Lemma na_heap_pointsto_st_agree l st1 st2 q1 q2 v1 v2 :
    na_heap_pointsto_st st1 l q1 v1 ∗
    na_heap_pointsto_st st2 l q2 v2 ⊢
    ⌜v1 = v2⌝.
  Proof.
    iIntros "[H1 H2]".
    iCombine "H1 H2" gives %[? Hag]%gmap_view_frag_op_valid.
    rewrite -pair_op pair_valid in Hag.
    destruct Hag as [Hag1 Hag2].
    rewrite to_agree_op_valid_L in Hag2.
    done.
  Qed.

  Lemma na_heap_pointsto_st_WSt_agree l st q1 q2 v1 v2 :
    na_heap_pointsto_st WSt l q1 v1 ∗
    na_heap_pointsto_st st l q2 v2 ⊢
    ⌜WSt = st⌝.
  Proof.
    destruct st; first eauto.
    iIntros "[H1 H2]".
    iCombine "H1 H2" gives %[? Hag]%gmap_view_frag_op_valid.
    rewrite -pair_op pair_valid in Hag.
    destruct Hag as [Hag1 Hag2].
    inversion Hag1.
  Qed.

  Lemma na_heap_pointsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ⌜v1 = v2⌝.
  Proof. by rewrite na_heap_pointsto_eq na_heap_pointsto_st_agree. Qed.

  Lemma na_heap_pointsto_st_frac_valid l q st v : na_heap_pointsto_st st l (DfracOwn q) v -∗ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    rewrite /na_heap_pointsto_st.
    rewrite own_valid discrete_valid.
    rewrite gmap_view_frag_valid dfrac_valid.
    iPureIntro. naive_solver.
  Qed.

  Lemma na_heap_pointsto_frac_valid l q v : na_heap_pointsto l (DfracOwn q) v -∗ ⌜(q ≤ 1)%Qp⌝.
  Proof. by rewrite na_heap_pointsto_eq; apply na_heap_pointsto_st_frac_valid. Qed.

  Lemma na_heap_pointsto_st_frac_valid2 l q q' st st' v v' :
    na_heap_pointsto_st st l (DfracOwn q) v -∗
    na_heap_pointsto_st st' l (DfracOwn q') v' -∗
    ⌜(q ⋅ q' ≤ 1)%Qp⌝.
  Proof.
    iIntros "Hown1 Hown2". iCombine "Hown1 Hown2" as "Hown".
    rewrite own_valid discrete_valid.
    rewrite gmap_view_frag_valid dfrac_valid.
    iDestruct "Hown" as %Hpure.
    iPureIntro. naive_solver.
  Qed.

  Lemma na_heap_pointsto_st_rd_frac l n n' q q' v :
    na_heap_pointsto_st (RSt (n + n')) l (DfracOwn (q + q')) v ⊣⊢
    na_heap_pointsto_st (RSt n) l (DfracOwn q) v ∗
    na_heap_pointsto_st (RSt n') l (DfracOwn q') v.
  Proof.
    rewrite /na_heap_pointsto_st.
    rewrite -own_op -gmap_view_frag_op -?pair_op -Cinr_op ?agree_idemp nat_op //=.
  Qed.

  (** General properties of [meta] and [meta_token] *)
  Global Instance meta_token_timeless l N : Timeless (meta_token l N).
  Proof. rewrite meta_token_eq /meta_token_def. apply _. Qed.
  Global Instance meta_timeless `{Countable A} l N (x : A) : Timeless (meta l N x).
  Proof. rewrite meta_eq /meta_def. apply _. Qed.
  Global Instance meta_persistent `{Countable A} l N (x : A) : Persistent (meta l N x).
  Proof. rewrite meta_eq /meta_def. apply _. Qed.

  Global Instance na_block_size_timeless l z : Timeless (na_block_size l z).
  Proof. rewrite na_block_size_eq /na_block_size_def. apply _. Qed.
  Global Instance na_block_size_persistent l z : Persistent (na_block_size l z).
  Proof. rewrite na_block_size_eq /na_block_size_def. apply _. Qed.

  Lemma meta_token_union_1 l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) -∗ meta_token l E1 ∗ meta_token l E2.
  Proof.
    rewrite meta_token_eq /meta_token_def. intros ?. iDestruct 1 as (γm1) "[#Hγm Hm]".
    rewrite reservation_map_token_union //. iDestruct "Hm" as "[Hm1 Hm2]".
    iSplitL "Hm1"; eauto.
  Qed.
  Lemma meta_token_union_2 l E1 E2 :
    meta_token l E1 -∗ meta_token l E2 -∗ meta_token l (E1 ∪ E2).
  Proof.
    rewrite meta_token_eq /meta_token_def.
    iDestruct 1 as (γm1) "[#Hγm1 Hm1]". iDestruct 1 as (γm2) "[#Hγm2 Hm2]".
    iAssert ⌜ γm1 = γm2 ⌝%I as %->.
    { iDestruct (own_valid_2 with "Hγm1 Hγm2") as %Hγ; iPureIntro.
      apply gmap_view_frag_op_valid in Hγ. destruct Hγ as [Ha Hb].
      apply to_agree_op_inv_L in Hb. done. }
    iDestruct (own_valid_2 with "Hm1 Hm2") as %?%reservation_map_token_valid_op.
    iExists γm2. iFrame "Hγm2". rewrite reservation_map_token_union //. by iSplitL "Hm1".
  Qed.
  Lemma meta_token_union l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) ⊣⊢ meta_token l E1 ∗ meta_token l E2.
  Proof.
    intros; iSplit; first by iApply meta_token_union_1.
    iIntros "[Hm1 Hm2]". by iApply (meta_token_union_2 with "Hm1 Hm2").
  Qed.

  Lemma meta_token_difference l E1 E2 :
    E1 ⊆ E2 → meta_token l E2 ⊣⊢ meta_token l E1 ∗ meta_token l (E2 ∖ E1).
  Proof.
    intros. rewrite {1}(union_difference_L E1 E2) //.
    by rewrite meta_token_union; last set_solver.
  Qed.

  Lemma meta_agree `{Countable A} l i (x1 x2 : A) :
    meta l i x1 -∗ meta l i x2 -∗ ⌜x1 = x2⌝.
  Proof.
    rewrite meta_eq /meta_def.
    iDestruct 1 as (γm1) "[Hγm1 Hm1]"; iDestruct 1 as (γm2) "[Hγm2 Hm2]".
    iAssert ⌜ γm1 = γm2 ⌝%I as %->.
    { iDestruct (own_valid_2 with "Hγm1 Hγm2") as %Hγ; iPureIntro.
      apply gmap_view_frag_op_valid in Hγ. destruct Hγ as [Ha Hb].
      apply to_agree_op_inv_L in Hb. done. }
    iDestruct (own_valid_2 with "Hm1 Hm2") as %Hγ; iPureIntro.
    move: Hγ. rewrite -reservation_map_data_op reservation_map_data_valid.
    move=> /to_agree_op_inv_L. naive_solver.
  Qed.
  Lemma meta_set `{Countable A} E l (x : A) N :
    ↑ N ⊆ E → meta_token l E ==∗ meta l N x.
  Proof.
    rewrite meta_token_eq meta_eq /meta_token_def /meta_def.
    iDestruct 1 as (γm) "[Hγm Hm]". iExists γm. iFrame "Hγm".
    iApply (own_update with "Hm").
    apply reservation_map_alloc; last done.
    cut (positives_flatten N ∈@{coPset} ↑N); first by set_solver.
    rewrite namespaces.nclose_unseal. apply elem_coPset_suffixes.
    exists 1%positive. by rewrite left_id_L.
  Qed.

  Lemma na_heap_alloc tls σ l v lk :
    (0 ≤ addr_offset l)%Z →
    σ !! l = None →
    σ !! addr_base l = None →
    tls lk = RSt 0 →
    na_heap_ctx tls σ ==∗ na_heap_ctx tls (<[l:=(lk, v)]>σ) ∗ l ↦ v ∗ meta_token l ⊤.
  Proof.
    iIntros (Hnonneg Hσl Hσbase Hread). rewrite /na_heap_ctx.
    iDestruct 1 as (m sz Hσm) "[Hσ [Hm [Hsz Hwf]]]".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply (gmap_view_alloc _ l (DfracOwn 1%Qp) (Cinr 0%nat, to_agree (v:leibnizO _)))=> //.
      apply lookup_to_na_heap_None, Hσl. }
    iMod (own_alloc (reservation_map_token ⊤)) as (γm) "Hγm".
    { apply reservation_map_token_valid. }
    iMod (own_update with "Hm") as "[Hm Hlm]".
    { eapply (gmap_view_alloc _ l DfracDiscarded (to_agree _)). 2: done. 2: done.
      { move: Hσl. rewrite -!(not_elem_of_dom (D:=gset L)). set_solver. } }
    iDestruct "Hwf" as %[Hwf1 Hwf2].
    assert (sz !! addr_id l = None).
    {
      destruct (sz !! addr_id l) as [?|] eqn:Heq; last done.
      exfalso. apply (not_elem_of_dom (D := gset L)) in Hσbase. apply Hσbase.
      eapply Hwf2. apply elem_of_dom. eauto.
    }
    (*
    iMod (own_update with "Hsz") as "[Hsz Hszl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (to_agree (z: leibnizO Z))) => //.
      by apply lookup_to_na_size_None. }
     *)
    iModIntro. rewrite na_heap_pointsto_eq/na_heap_pointsto_def.
    iFrame "Hl".
    iSplitL "Hσ Hm Hsz". (* last by eauto with iFrame. *)
    { iExists (<[l:=(to_agree γm)]> m), sz.
      rewrite to_na_heap_insert /block_sizes_wf
              !dom_insert_L Hread //=.
      iFrame; iPureIntro; split_and!.
      * set_solver.
      * set_unfold => l' z'. intros [->|Hin].
        { intros; congruence. }
        { intros. eapply Hwf1; eauto. }
      *set_unfold => l'. eauto.
    }
    { rewrite meta_token_eq /meta_token_def. eauto. }
  Qed.

  Lemma na_heap_alloc_base tls σ l v lk (z: Z) :
    (0 < z)%Z →
    (∀ z', (z <= z')%Z ∨ (z' < 0)%Z → σ !! addr_plus_off l z' = None) →
    σ !! l = None →
    addr_offset l = 0%Z →
    tls lk = RSt 0 →
    na_heap_ctx tls σ ==∗ na_heap_ctx tls (<[l:=(lk, v)]>σ) ∗ l ↦ v ∗ meta_token l ⊤ ∗ na_block_size l z.
  Proof.
    iIntros (Hz0 Hσl_all Hσl Hoff Hread). rewrite /na_heap_ctx.
    iDestruct 1 as (m sz Hσm) "[Hσ [Hm [Hsz Hwf]]]".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply (gmap_view_alloc _ l (DfracOwn 1%Qp) (Cinr 0%nat, to_agree (v:leibnizO _)))=> //.
      by apply lookup_to_na_heap_None. }
    iMod (own_alloc (reservation_map_token ⊤)) as (γm) "Hγm".
    { apply reservation_map_token_valid. }
    iMod (own_update with "Hm") as "[Hm Hlm]".
    { eapply (gmap_view_alloc _ l DfracDiscarded (to_agree _)). 2: done. 2: done.
      move: Hσl. rewrite -!(not_elem_of_dom (D:=gset L)). set_solver. }
    iDestruct "Hwf" as %[Hwf1 Hwf2].
    assert (sz !! addr_id l = None).
    {
      destruct (sz !! addr_id l) as [?|] eqn:Heq; last done.
      exfalso. apply (not_elem_of_dom (D := gset L)) in Hσl. apply Hσl.
      rewrite -(addr_encode_decode' l) Hoff.
      eapply Hwf2. apply elem_of_dom. eauto.
    }
    iMod (own_update with "Hsz") as "[Hsz Hszl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (to_agree (z: leibnizO Z))) => //.
      by apply lookup_to_na_size_None. }
    iModIntro. rewrite na_heap_pointsto_eq/na_heap_pointsto_def na_block_size_eq/na_block_size_def.
    iFrame "Hl Hszl".
    iSplitL "Hσ Hm Hsz". (* last by eauto with iFrame. *)
    { iExists (<[l:=(to_agree γm)]> m), (<[addr_id l:=z]> sz).
      rewrite to_na_heap_insert to_na_size_insert /block_sizes_wf
              !dom_insert_L Hread //=.
      iFrame; iPureIntro; split_and!.
      * set_solver.
      * set_unfold => l' z'. intros [->|Hin].
        { rewrite lookup_insert. inversion 1. rewrite Hoff. split; subst; eauto. lia. }
        { destruct (decide (addr_id l = addr_id l')) as [e|ne].
          - rewrite -e. rewrite lookup_insert. inversion 1; subst.
            cut (¬ (z' <= addr_offset l') ∧ ¬ (addr_offset l' < 0))%Z; first by lia.
            apply elem_of_dom in Hin as (x&Heq).
            rewrite (addr_plus_off_decode l') in Heq.
            assert (addr_base l' = l) as <-.
            {
              rewrite /addr_base -Hoff -e addr_encode_decode' //.
            }
            split; intros Hlt; rewrite Hσl_all in Heq; eauto; congruence.
          - rewrite lookup_insert_ne //. eapply Hwf1; eauto.
        }
      * set_unfold => l'. intros [->|?].
        { left. rewrite -Hoff addr_encode_decode' //=. }
        { right. eapply Hwf2. auto. }
    }
    { rewrite meta_token_eq /meta_token_def. eauto. }
  Qed.

  (*
  Fixpoint heap_array (l : L) (vs : list V) lk : gmap L (LK * V) :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := (lk, v)]} ∪ heap_array (addr_plus_off l 1) vs' lk
  end.

  Lemma heap_array_lookup_lk l (vs: list V) lk lk' w k :
    heap_array l vs lk !! k = Some (lk', w) → lk = lk'.
  Proof.
    revert k l; induction vs as [|v' vs IH]=> l' l /=.
    { rewrite lookup_empty. naive_solver lia. }
    rewrite -insert_union_singleton_l lookup_insert_Some.
    intros [[-> Heq] | (Hl & ?)].
    { congruence. }
    eapply IH. eauto.
  Qed.

  Lemma heap_array_lookup l (vs: list V) lk w k :
    heap_array l vs lk !! k = Some (lk, w) ↔
    ∃ (j : Z), (0 ≤ j)%Z ∧ k = addr_plus_off l j ∧ vs !! (Z.to_nat j) = Some w.
  Proof.
    revert k l; induction vs as [|v' vs IH]=> l' l /=.
    { rewrite lookup_empty. naive_solver lia. }
    rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
    - intros [[-> Heq] | (Hl & j & ? & -> & ?)].
      { inversion Heq; subst. exists 0. rewrite addr_plus_off_0. naive_solver lia. }
      exists (1 + j)%Z. rewrite addr_plus_plus !Z.add_1_l Z2Nat.inj_succ; auto with lia.
    - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
      { rewrite addr_plus_off_0; eauto. }
      right. split.
      { rewrite -{1}(addr_plus_off_0 l). intros ?%(inj (addr_plus_off _)); lia. }
      assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
      { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
      rewrite Hj /= in Hil.
      exists (j - 1)%Z. rewrite addr_plus_plus Z.add_sub_assoc Z.add_simpl_l.
      auto with lia.
  Qed.
   *)

  Lemma na_heap_alloc_list_aux tls σ l (vs: list V) off (lk: LK)  :
    (0 < off)%Z →
    (0 ≤ addr_offset l)%Z →
    (∀ z, 0 ≤ z ≤ length vs → σ !! addr_plus_off l (off + z) = None) →
    σ !! addr_base l = None →
    tls lk = RSt 0 →
    na_heap_ctx tls σ ==∗ na_heap_ctx tls (heap_array (addr_plus_off l off) (fmap (λ v, (lk, v)) vs) ∪ σ) ∗
                 [∗ list] i↦v ∈ vs, (addr_plus_off l (off + i)) ↦ v ∗ meta_token (addr_plus_off l (off + i)) ⊤.
  Proof.
    revert l off.
    induction vs as [ | v vs]; intros l off Hpos Hoffset Hrange_empty Hbase_empty Hread.
    - iIntros "Hctx". rewrite //= left_id. by iFrame.
    - iIntros "Hctx".
      iMod (IHvs l (off + 1)%Z  with "[$]") as "(Hctx&Hlist)"; eauto.
      { lia. }
      { intros ? (?&?). replace (off + 1 + z)%Z with (off + (S z))%Z by lia.
        eapply Hrange_empty; split; eauto. simpl; lia. }
      rewrite big_sepL_cons.
      iMod (na_heap_alloc tls _ (addr_plus_off l off) v with "Hctx") as "(Hctx&Hpts)".
      { rewrite addr_offset_of_plus. lia. }
      { apply lookup_union_None. split; last first.
        { replace off with (off + O)%Z by lia. eapply Hrange_empty. lia. }
        destruct (_ !! addr_plus_off l off) as [(lk'&?)|] eqn:Hlookup; auto.
        revert Hlookup; rewrite heap_array_lookup => Heq.
        destruct Heq as (j&Hnonneg&Hplus&Hlookup).
        rewrite addr_plus_plus in Hplus.
        apply (inj (addr_plus_off l)) in Hplus. lia.
      }
      {
        rewrite addr_base_of_plus.
        apply lookup_union_None. split; last first.
        { eauto. }
        destruct (heap_array (addr_plus_off l (off + 1)) _ !! addr_base l) as [(lk'&?)|] eqn:Hlookup; auto.
        revert Hlookup; rewrite heap_array_lookup => Heq.
        destruct Heq as (j&Hnonneg&Hplus&Hlookup).
        rewrite addr_plus_plus in Hplus.
        apply (f_equal addr_offset) in Hplus.
        rewrite addr_offset_of_plus addr_offset_of_base in Hplus.
        lia.
      }
      { eauto. }
      iFrame. replace (off + 0%nat)%Z with off by lia. iFrame.
      rewrite /= addr_plus_plus insert_union_singleton_l assoc. iFrame.
      iApply (big_sepL_mono with "Hlist"). intros.
      simpl. replace (off + S k)%Z with (off + 1 + k)%Z by lia. eauto.
  Qed.

  Lemma na_heap_alloc_list tls σ l (vs: list V) (lk: LK)  :
    (0 < length vs) →
    (addr_offset l = 0)%Z →
    (∀ z, σ !! addr_plus_off l z = None) →
    σ !! l = None →
    tls lk = RSt 0 →
    na_heap_ctx tls σ ==∗ na_heap_ctx tls (heap_array l (fmap (λ v, (lk, v)) vs) ∪ σ) ∗
                 na_block_size l (length vs) ∗
                 [∗ list] i↦v ∈ vs, (addr_plus_off l i) ↦ v ∗ meta_token (addr_plus_off l i) ⊤.
  Proof.
    destruct vs.
    - rewrite /= left_id. lia.
    - iIntros (Hlen Hoff Hrange ??) "Hctx".
      simpl. rewrite -assoc -insert_union_singleton_l.
      iMod (na_heap_alloc_list_aux tls σ l vs 1 lk with "Hctx") as "(Hctx&?)"; eauto.
      { lia. }
      { lia. }
      { cut (addr_base l = l); first congruence.
        rewrite /addr_base -Hoff addr_encode_decode'; eauto.
      }
      iMod (na_heap_alloc_base _ _ _ _ _ (length (v :: vs)) with "Hctx") as "(Hctx&(?&?&?))"; eauto.
      { simpl; lia. }
      { intros. apply lookup_union_None; split.
        * destruct (heap_array (addr_plus_off l 1) _ !! addr_plus_off l z') as [(lk'&?)|] eqn:Heq; last auto.
          revert Heq; rewrite heap_array_lookup => Heq.
          destruct Heq as (j&Hnonneg&Hplus&Hlookup).
          rewrite addr_plus_plus in Hplus.
          apply (inj (addr_plus_off l)) in Hplus.
          apply lookup_lt_Some in Hlookup.
          rewrite fmap_length in Hlookup.
          simpl in *. lia.
        * eauto.
      }
      { intros. apply lookup_union_None; split.
        * destruct (heap_array (addr_plus_off l 1) _ !! l) as [(lk'&?)|] eqn:Heq; last auto.
          revert Heq; rewrite heap_array_lookup => Heq.
          destruct Heq as (j&Hnonneg&Hplus&Hlookup).
          rewrite addr_plus_plus in Hplus.
          apply (f_equal addr_offset) in Hplus.
          rewrite addr_offset_of_plus in Hplus. lia.
        * eauto.
      }
      iFrame. rewrite addr_plus_off_0. iFrame.
      iApply (big_sepL_mono with "[$]"). intros.
      simpl. replace (1 + k)%Z with (Z.of_nat $ S k)%Z by lia. eauto.
  Qed.

  (*
  Lemma na_heap_alloc_gen tls σ σ' :
    σ' ##ₘ σ →
    (∀ l lkv, σ' !! l = Some lkv → tls (lkv.1) = RSt 0) →
    na_heap_ctx tls σ ==∗
    na_heap_ctx tls (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↦ v.2) ∗ ([∗ map] l ↦ _ ∈ σ', meta_token l ⊤).
  Proof.
    revert σ; induction σ' as [| l lkv σ' Hl IH] using map_ind; iIntros (σ Hdisj Hread) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ [Hσ' ?]]"; first by eapply map_disjoint_insert_l.
    { intros l' lkv' ?. apply (Hread l').
      rewrite lookup_insert_ne //= => ?. subst. congruence.
    }
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    iMod (na_heap_alloc _ _ l _ (fst lkv) with "Hσ'σ") as "(? & ? & ?)";
      first by apply lookup_union_None.
    { eapply (Hread l). rewrite lookup_insert //=. }
    { by destruct lkv; iFrame. }
  Qed.
   *)

  Lemma na_heap_pointsto_lookup tls σ l lk (q: dfrac) v :
    own (na_heap_name hG) (gmap_view_auth (DfracOwn 1) (to_na_heap tls σ)) -∗
    own (na_heap_name hG) (@gmap_view_frag L _ _ (na_heap_cmra V) l q (to_lock_stateR lk, to_agree v)) -∗
    ⌜∃ ls' (n' : nat),
                σ !! l = Some (ls', v) ∧
                tls ls' = match lk with
                          | RSt n => RSt (n+n')
                          | WSt => WSt
                          end⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %Hag.
    apply gmap_view_both_dfrac_valid_discrete_total in Hag.
    destruct Hag as [v' Hag].
    destruct Hag as (? & ? & Hna & ? & Hincl).
    rewrite /to_na_heap lookup_fmap in Hna.
    apply fmap_Some in Hna. destruct Hna as (x & Hlookup & Hx). destruct x as [ls'' v'']. rewrite Hx /= in Hincl.
    iPureIntro.
    apply pair_included in Hincl. destruct Hincl as [Hls'' Hincl].
      rewrite to_agree_included_L in Hincl. subst. simpl in Hls''.
    destruct lk as [|n] eqn:Hls, (tls ls'') as [|n''] eqn:Hls'.
    { by exists ls'', O. }
    { rewrite csum_included in Hls''. destruct Hls'' as [Hls'' | [Hls'' | Hls'']].
      { inversion Hls''. }
      { destruct Hls'' as (a & b & ? & Hls'' & ?). inversion Hls''. }
      { destruct Hls'' as (a & b & Hls'' & ? & ?). inversion Hls''. } }
    { rewrite csum_included in Hls''. destruct Hls'' as [Hls'' | [Hls'' | Hls'']].
      { inversion Hls''. }
      { destruct Hls'' as (a & b & Hls'' & ? & ?). inversion Hls''. }
      { destruct Hls'' as (a & b & ? & Hls'' & ?). inversion Hls''. } }
    { rewrite csum_included in Hls''. destruct Hls'' as [Hls'' | [Hls'' | Hls'']].
      { inversion Hls''. }
      { destruct Hls'' as (a & b & Hls'' & ? & ?). inversion Hls''. }
      destruct Hls'' as (a & b & Ha & Hb & Hincl). inversion Ha; inversion Hb; subst.
      apply nat_included in Hincl.
      exists ls'', (b-a). intuition eauto.
      rewrite Hls'. f_equal. lia.
    }
  Qed.

  Lemma na_heap_pointsto_lookup_1 tls σ l lk v :
    own (na_heap_name hG) (gmap_view_auth (DfracOwn 1) (to_na_heap tls σ)) -∗
    own (na_heap_name hG) (@gmap_view_frag L _ _ (na_heap_cmra V) l (DfracOwn 1) (to_lock_stateR lk, to_agree v)) -∗
    ⌜∃ ls', σ !! l = Some (ls', v) ∧ tls ls' = lk⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %Hag.
    apply gmap_view_both_valid in Hag.
    destruct Hag as (Hq & Hv & Hlookup).
    rewrite /to_na_heap lookup_fmap fmap_Some_equiv in Hlookup.
    destruct Hlookup as (x & Hlookup & Hequiv). destruct x as [lk' v'].
    rewrite pair_equiv /= in Hequiv. destruct Hequiv as [Hequiv1 Hval].
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    iPureIntro.
    exists lk'. intuition eauto.
    destruct lk, (tls lk'); inversion Hequiv1; eauto.
  Qed.

  Lemma na_heap_read_vs tls σ n1 n2 nf l q v lk lk':
    σ !! l = Some (lk, v) →
    tls lk = RSt (n1 + nf) →
    tls lk' = RSt (n2 + nf) →
    own (na_heap_name hG) (gmap_view_auth (DfracOwn 1) (to_na_heap tls σ)) -∗ na_heap_pointsto_st (RSt n1) l q v
    ==∗ own (na_heap_name hG) (gmap_view_auth (DfracOwn 1) (to_na_heap tls (<[l:=(lk', v)]> σ)))
        ∗ na_heap_pointsto_st (RSt n2) l q v.
  Proof.
    intros Hσv Hr1 Hr2. apply entails_wand, wand_intro_r. rewrite -!own_op to_na_heap_insert.
    eapply own_update, gmap_view_update_local.
    { by rewrite /to_na_heap lookup_fmap Hσv. }
    rewrite Hr1 Hr2 => //=.
    unshelve (apply: prod_local_update_1).
    apply csum_local_update_r.
    apply nat_local_update; lia.
  Qed.

  Lemma na_block_size_oob_lookup tls σ l n (Hoff: (addr_offset l < 0 ∨ n <= addr_offset l)%Z):
    na_heap_ctx tls σ -∗ na_block_size (addr_base l) n -∗ ⌜ σ !! l = None ⌝.
  Proof.
    iIntros "Hσ". iIntros "Hmt".
    iDestruct "Hσ" as (m sz Hσm) "[Hσ [? [Hsize Hwf]]]".
    rewrite na_block_size_eq /na_block_size_def.
    iDestruct (own_valid_2 with "Hsize Hmt") as %[Hl?]%auth_both_valid_discrete.
    iDestruct "Hwf" as %Hwf.
    iPureIntro. move: Hl=> /singleton_included_l [H' [Hlook Hincl]].
    move: Hlook. rewrite /to_na_heap lookup_fmap fmap_Some_equiv.
    intros (z&Hlook&Hequiv). revert Hincl; rewrite Hequiv.
    move=> /Some_included_total/to_agree_included. inversion 1; subst.
    destruct Hwf as (Hwf1&Hwf2).
    destruct (decide (l ∈ dom σ)).
    - opose proof (Hwf1 l _ _ _); eauto.
      { rewrite -addr_id_of_base; eauto. }
      { lia. }
    - apply (not_elem_of_dom (D := gset L)); eauto.
  Qed.

  Lemma na_heap_write_lookup tls σ l q v :
    na_heap_ctx tls σ -∗ na_heap_pointsto_st WSt l q v -∗ ⌜∃ lk, σ !! l = Some (lk, v) ∧ tls lk = WSt⌝.
  Proof.
    iIntros "Hσ". iIntros "Hmt".
    iDestruct "Hσ" as (m sz Hσm) "[Hσ ?]".
    iDestruct (na_heap_pointsto_lookup with "Hσ Hmt") as %[n' [Hσl ?]]; eauto.
  Qed.

  Lemma na_heap_read' tls σ n l q v :
    na_heap_ctx tls σ -∗
    na_heap_pointsto_st (RSt n) l q v -∗
    ∃ lk n', ⌜σ !! l = Some (lk, v) ∧ tls lk = RSt n' ∧ n ≤ n'⌝.
  Proof.
    iIntros "Hσ". iIntros "Hmt".
    iDestruct "Hσ" as (m sz Hσm) "[Hσ ?]".
    iDestruct (na_heap_pointsto_lookup with "Hσ Hmt") as %[n' [Hσl [? ?]]]; eauto.
    iPureIntro. eexists _, _. split_and!; eauto. lia.
  Qed.

  Lemma na_heap_read tls σ l q v :
    na_heap_ctx tls σ -∗ l ↦{q} v -∗ ∃ lk n, ⌜σ !! l = Some (lk, v) ∧ tls lk = RSt n⌝.
  Proof.
    rewrite na_heap_pointsto_eq. iIntros "H1 H2".
    iDestruct (na_heap_read' with "H1 H2") as %Hpure.
    iPureIntro. destruct Hpure as (?&?&?&?&?); eauto.
  Qed.

  Lemma na_heap_read_1' tls σ n l v :
    na_heap_ctx tls σ -∗ na_heap_pointsto_st (RSt n) l (DfracOwn 1) v -∗ ⌜∃ lk, σ !! l = Some (lk, v) ∧ tls lk = RSt n⌝.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct "Hσ" as (m sz Hσm) "[Hσ ?]".
    iDestruct (na_heap_pointsto_lookup_1 with "Hσ Hmt") as %[n' Hσl]; eauto.
  Qed.

  Lemma na_heap_read_1 tls σ l v :
    na_heap_ctx tls σ -∗ l ↦ v -∗ ⌜∃ lk, σ !! l = Some (lk, v) ∧ tls lk = RSt O⌝.
  Proof. rewrite na_heap_pointsto_eq. iApply na_heap_read_1'. Qed.

  (* States whether the rl function has the effect of updating a lk
     to a lk with an additional reader *)
  Definition is_read_lock tls (rl: LK → LK) :=
    (∀ lk n, tls lk = RSt n → tls (rl lk) = RSt (S n)).

  Definition is_read_unlock tls (url: LK → LK) :=
    (∀ lk n, tls lk = RSt (S n) → tls (url lk) = RSt n).

  Lemma block_sizes_wf_override σ l sz a b:
    σ !! l = Some a →
    block_sizes_wf (<[l := b]> σ) sz ↔ block_sizes_wf σ sz.
  Proof.
    rewrite /block_sizes_wf dom_insert_L => ?.
    assert ({[l]} ∪ dom σ = dom σ) as ->.
    { cut (l ∈ dom σ); first by set_solver.
      apply elem_of_dom; eauto. }
    eauto.
  Qed.

  Lemma na_heap_read_prepare' tls rl σ l n q v :
    is_read_lock tls rl →
    na_heap_ctx tls σ -∗ na_heap_pointsto_st (RSt n) l q v ==∗ ∃ lk n',
      ⌜ σ !! l = Some (lk, v) ∧ tls lk = RSt n' ⌝ ∗
      na_heap_ctx tls (<[l:=(rl lk, v)]> σ) ∗
      na_heap_pointsto_st (RSt (S n)) l q v.
  Proof.
    iIntros (Hrl) "Hσ Hmt".
    iDestruct "Hσ" as (m sz Hσm) "[Hσ Hσm]".
    iDestruct (na_heap_pointsto_lookup with "Hσ Hmt") as %[lk [n' [Hσl Hlkeq]]]; eauto.
    iMod (na_heap_read_vs _ _ n (S n) with "Hσ Hmt") as "[Hσ Hmt]"; [ done | done | by eapply Hrl | ].
    iModIntro. iExists lk, (n + n'); iSplit; [done|]. iFrame "Hσ Hmt".
    iExists _, _. rewrite dom_insert_L block_sizes_wf_override //. iFrame. iPureIntro; set_solver.
  Qed.

  Lemma na_heap_read_prepare tls rl σ l dq v :
    is_read_lock tls rl →
    na_heap_ctx tls σ -∗ l ↦{dq} v ==∗ ∃ lk n,
      ⌜ σ !! l = Some (lk, v) ∧ tls lk = RSt n ⌝ ∗
      na_heap_ctx tls (<[l:=(rl lk, v)]> σ) ∗
      na_heap_pointsto_st (RSt 1) l dq v.
  Proof. rewrite na_heap_pointsto_eq. apply na_heap_read_prepare'. Qed.

  Lemma na_heap_read_finish_vs' tls url l n q v:
    is_read_unlock tls url →
    na_heap_pointsto_st (RSt (S n)) l q v -∗
    (∀ σ2, na_heap_ctx tls σ2 ==∗ ∃ lk n',
            ⌜σ2 !! l = Some (lk, v) ∧ tls lk = RSt (S n') ⌝ ∗
            na_heap_ctx tls (<[l:=(url lk, v)]> σ2) ∗
            na_heap_pointsto_st (RSt n) l q v).
  Proof.
    iIntros (Hurl) "Hmt".
    iIntros (σ2). iIntros "Hσ".
    iDestruct "Hσ" as (m' sz Hσm) "[Hσ Hσm]".
    iDestruct (na_heap_pointsto_lookup with "Hσ Hmt") as %[lk [n' [Hσl Hlkeq]]]; eauto.
    iMod (na_heap_read_vs _ _ (S n) n with "Hσ Hmt") as "[Hσ Hmt]"; [ done | done | by eapply Hurl | ].
    iExists lk, (n + n'); iModIntro; iSplit; [done|]. iFrame. iExists _, _.
    rewrite dom_insert_L block_sizes_wf_override //. iFrame. iPureIntro; set_solver.
  Qed.

  Lemma na_heap_read_finish_vs tls url l q v:
    is_read_unlock tls url →
    na_heap_pointsto_st (RSt 1) l q v -∗
    (∀ σ2, na_heap_ctx tls σ2 ==∗ ∃ lk n,
            ⌜σ2 !! l = Some (lk, v) ∧ tls lk = RSt (S n) ⌝ ∗
            na_heap_ctx tls (<[l:=(url lk, v)]> σ2) ∗ l ↦{q} v).
  Proof. rewrite na_heap_pointsto_eq. apply na_heap_read_finish_vs'. Qed.

  Lemma na_heap_read_na tls rl url σ l q v :
    is_read_lock tls rl →
    is_read_unlock tls url →
    na_heap_ctx tls σ -∗ l ↦{q} v ==∗ ∃ lk n,
      ⌜σ !! l = Some (lk, v) ∧ tls lk = RSt n⌝ ∗
      na_heap_ctx tls (<[l:=(rl lk, v)]> σ) ∗
      (∀ σ2, na_heap_ctx tls σ2 ==∗ ∃ lk n2,
             ⌜σ2 !! l = Some (lk, v) ∧ tls lk = RSt (S n2) ⌝ ∗
             na_heap_ctx tls (<[l:=(url lk, v)]> σ2) ∗ l ↦{q} v).
  Proof.
    iIntros (Hrl Hurl) "Hσ Hmt".
    iMod (na_heap_read_prepare with "[$] [$]") as (lk n Heq) "(Hσ&Hmt)"; eauto.
    iModIntro. iExists _, _. iSplitL ""; eauto. iFrame.
    iIntros.
    iMod (na_heap_read_finish_vs with "[$] [$]") as (lk' n' Heq') "(Hσ&Hmt)"; eauto.
    iModIntro. iExists _, _. iSplitL ""; eauto. iFrame.
  Qed.

  Lemma na_heap_write_vs tls σ st1 st2 l v v':
    σ !! l = Some (st1, v) →
    own (na_heap_name hG) (gmap_view_auth (DfracOwn 1) (to_na_heap tls σ)) -∗ na_heap_pointsto_st (tls st1) l (DfracOwn 1%Qp) v
    ==∗ own (na_heap_name hG) (gmap_view_auth (DfracOwn 1) (to_na_heap tls (<[l:=(st2, v')]> σ)))
        ∗ na_heap_pointsto_st (tls st2) l (DfracOwn 1%Qp) v'.
  Proof.
    intros Hσv. apply entails_wand, wand_intro_r. rewrite -!own_op to_na_heap_insert.
    eapply own_update, gmap_view_replace.
    by destruct (tls st2).
  Qed.

  Lemma na_heap_write tls σ l lk v v' :
    tls lk = RSt 0 →
    na_heap_ctx tls σ -∗ l ↦ v ==∗ na_heap_ctx tls (<[l:=(lk, v')]> σ) ∗ l ↦ v'.
  Proof.
    iIntros (Hread_lk) "Hσ Hmt".
    rewrite na_heap_pointsto_eq.
    iDestruct "Hσ" as (m sz Hσm) "[Hσ Hσm]".
    iDestruct (na_heap_pointsto_lookup_1 with "Hσ Hmt") as %(?&?&Hread); auto.
    iMod (na_heap_write_vs with "Hσ [Hmt]") as "[Hσ ?]"; first done.
    { by rewrite /na_heap_pointsto_def Hread. }
    iFrame. rewrite /na_heap_pointsto_def Hread_lk. iFrame. iModIntro.
    iExists _, _. rewrite dom_insert_L block_sizes_wf_override //. iFrame. iPureIntro; set_solver.
  Qed.

  Definition tls_write_unique (tls: LK → _) :=
    ∀ lk1 lk2, tls lk1 = WSt → tls lk2 = WSt → lk1 = lk2.

  Lemma na_heap_write_prepare tls σ l v lkw :
    tls lkw = WSt →
    na_heap_ctx tls σ -∗ l ↦ v ==∗
      ∃ lk1,
      ⌜ σ !! l = Some (lk1, v) ∧ tls lk1 = RSt 0 ⌝ ∗
      na_heap_ctx tls (<[l:=(lkw, v)]> σ) ∗
      na_heap_pointsto_st WSt l (DfracOwn 1%Qp) v.
  Proof.
    iIntros (Hwrite) "Hσ Hmt".
    rewrite na_heap_pointsto_eq.
    iDestruct "Hσ" as (m sz Hσm) "[Hσ Hσm]".
    iDestruct (na_heap_pointsto_lookup_1 with "Hσ Hmt") as %(lkr&?&Hread); eauto.
    iMod (na_heap_write_vs with "Hσ [Hmt]") as "[Hσ Hmt]"; first done.
    { by rewrite /na_heap_pointsto_def Hread. }
    iModIntro. iExists lkr. iSplit; [done|]. iFrame. rewrite Hwrite //. iFrame.
    iExists _, _. rewrite dom_insert_L block_sizes_wf_override //. iFrame. iPureIntro; set_solver.
  Qed.

  Lemma na_heap_write_finish_vs tls l v v' lk' :
    tls lk' = RSt 0 →
    na_heap_pointsto_st WSt l (DfracOwn 1%Qp) v -∗
    (∀ σ2, na_heap_ctx tls σ2 ==∗ ∃ lkw, ⌜σ2 !! l = Some (lkw, v) ∧ tls lkw = WSt⌝ ∗
        na_heap_ctx tls (<[l:=(lk', v')]> σ2) ∗ l ↦ v').
  Proof.
    iIntros (Hread) "Hmt". iIntros (σ) "Hσ".
    iDestruct "Hσ" as (m sz Hσm) "[Hσ Hσm]".
    iDestruct (na_heap_pointsto_lookup with "Hσ Hmt") as %(lk2&n&Hσl&Hlk'); eauto.
    iMod (na_heap_write_vs _ _ _ lk' with "Hσ [Hmt]") as "[Hσ Hmt]"; first done.
    { by rewrite Hlk'. }
    iExists lk2. iFrame. iModIntro; iSplit; [done|].
    rewrite na_heap_pointsto_eq /na_heap_pointsto_def Hread. iFrame.
    iExists _, _. rewrite dom_insert_L block_sizes_wf_override //. iFrame. iPureIntro; set_solver.
  Qed.

  Lemma na_heap_write_na tls σ l v v' lkw :
    tls_write_unique tls →
    tls lkw = WSt →
    na_heap_ctx tls σ -∗ l ↦ v ==∗
      ∃ lk1,
      ⌜ σ !! l = Some (lk1, v) ∧ tls lk1 = RSt 0 ⌝ ∗
      na_heap_ctx tls (<[l:=(lkw, v)]> σ) ∗
      ∀ σ2, na_heap_ctx tls σ2 ==∗ ⌜σ2 !! l = Some (lkw, v)⌝ ∗
        na_heap_ctx tls (<[l:=(lk1, v')]> σ2) ∗ l ↦ v'.
  Proof.
    iIntros (Huniq Hwrite) "Hσ Hmt".
    iMod (na_heap_write_prepare with "Hσ Hmt") as (lkr (?&Hread)) "[Hσ Hmt]"; eauto.
    iPoseProof (na_heap_write_finish_vs with "Hmt") as "Hmt"; eauto.
    iModIntro. iExists _. iFrame.
    iSplit; [done|]. iIntros. iMod ("Hmt" with "[$]") as (? (->&?)) "[Hσ Hmt]". iFrame.
    iPureIntro; repeat f_equal. eapply Huniq; eauto.
  Qed.
End na_heap.

Section na_heap_defs.
  Context {L1 V : Type} `{BlockAddr L1}.

  Record na_heap_names :=
    {
      na_heap_heap_name : gname;
      na_heap_size_name : gname;
      na_heap_meta_name : gname;
    }.

  Definition na_heapGS_update {Σ} (hG: na_heapGS L1 V Σ) (names: na_heap_names) :=
    Na_HeapG _ _ _ _ _ _
             (@na_heap_inG _ _ _ _ _ _ hG)
             (@na_size_inG _ _ _ _ _ _ hG)
             (@na_meta_inG _ _ _ _ _ _ hG)
             (@na_meta_data_inG _ _ _ _ _ _ hG)
             (na_heap_heap_name names)
             (na_heap_size_name names)
             (na_heap_meta_name names).

  Definition na_heapGS_update_pre {Σ} (hG: na_heapGpreS L1 V Σ) (names: na_heap_names) :=
    Na_HeapG _ _ _ _ _ _
             (@na_heap_preG_inG _ _ _ _ _ _ hG)
             (@na_size_preG_inG _ _ _ _ _ _ hG)
             (@na_meta_preG_inG _ _ _ _ _ _ hG)
             (@na_meta_data_preG_inG _ _ _ _ _ _ hG)
             (na_heap_heap_name names)
             (na_heap_size_name names)
             (na_heap_meta_name names).

  Definition na_heapGS_get_names {Σ} (hG: na_heapGS L1 V Σ) : na_heap_names :=
    {| na_heap_heap_name := na_heap_name hG;
       na_heap_size_name := na_size_name hG;
       na_heap_meta_name := na_meta_name hG |}.

  Lemma na_heapGS_get_update {Σ} (hG: na_heapGS L1 V Σ) :
    na_heapGS_update hG (na_heapGS_get_names hG) = hG.
  Proof. destruct hG => //=. Qed.

  Lemma na_heapGS_update_pre_get {Σ} (hG: na_heapGpreS L1 V Σ) names:
    (na_heapGS_get_names (na_heapGS_update_pre hG names)) = names.
  Proof. destruct hG, names => //=. Qed.

  Lemma na_heap_name_init `{!na_heapGpreS L1 V Σ} {LK} (tls: LK → _) σ :
    ⊢ |==> ∃ names : na_heap_names, na_heap_ctx (hG := na_heapGS_update_pre _ names) tls σ.
  Proof.
    iMod (own_alloc (gmap_view_auth (DfracOwn 1) (to_na_heap tls σ))) as (γh) "Hh".
    { apply gmap_view_auth_valid. }
    iMod (own_alloc (● to_na_size ∅)) as (γs) "Hs".
    { rewrite auth_auth_valid. exact: to_na_size_valid. }
    iMod (own_alloc (gmap_view_auth (DfracOwn 1) (∅ : gmap L1 (agreeR gnameO)))) as (γm) "Hm".
    { apply gmap_view_auth_valid. }
    iModIntro. iExists {| na_heap_heap_name := γh; na_heap_size_name := γs; na_heap_meta_name := γm |}.
    iExists ∅, ∅; simpl. iFrame "Hh Hm". rewrite dom_empty_L. iFrame.
    iPureIntro; split.
    - set_solver.
    - rewrite /block_sizes_wf. set_solver.
  Qed.

  Lemma na_heap_reinit {Σ} (hG: na_heapGS L1 V Σ) {LK} (tls: LK → _) σ :
    ⊢ |==> ∃ names : na_heap_names, na_heap_ctx (hG := na_heapGS_update hG names) tls σ.
  Proof.
    iMod (own_alloc (gmap_view_auth (DfracOwn 1) (to_na_heap tls σ))) as (γh) "Hh".
    { apply gmap_view_auth_valid. }
    iMod (own_alloc (gmap_view_auth (DfracOwn 1) (∅ : gmap L1 (agreeR gnameO)))) as (γm) "Hm".
    { apply gmap_view_auth_valid. }
    iMod (own_alloc (● to_na_size ∅)) as (γs) "Hs".
    { rewrite auth_auth_valid. exact: to_na_size_valid. }
    iModIntro. iExists {| na_heap_heap_name := γh; na_heap_size_name := γs; na_heap_meta_name := γm |}.
    iExists ∅, ∅; simpl. iFrame "Hh Hm". rewrite dom_empty_L. iFrame.
    iPureIntro; split.
    - set_solver.
    - rewrite /block_sizes_wf. set_solver.
  Qed.

End na_heap_defs.
