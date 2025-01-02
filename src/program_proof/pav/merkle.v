From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import merkle.

From Perennial.program_proof.pav Require Import classes misc cryptoffi.
From Perennial.program_proof Require Import std_proof marshal_stateless_proof.

Section internal.
Context `{!heapGS Σ}.

Inductive tree : Type :=
  (* Cut only exists for proof checking trees. *)
  | Cut : list w8 → tree
  | Leaf : list w8 → tree
  | Interior : list (option tree) → tree.

(* The core invariant that defines the recursive hashing structure of merkle trees. *)
Fixpoint is_node_hash (tr : tree) (hash : list w8) : iProp Σ :=
  match tr with
  | Cut hash' => ⌜hash = hash' ∧ length hash' = 32%nat⌝
  | Leaf val => is_hash (val ++ [W8 1]) hash
  | Interior children =>
    ∃ (child_hashes : list (list w8)),
    let map_fn := (λ c h,
                     match c with
                     | None => is_hash [W8 0] h
                     | Some c => is_node_hash c h
                     end
                  ) in
    ([∗ list] child_fn;hash' ∈ (map_fn <$> children);child_hashes,
      child_fn hash') ∗
    is_hash (concat child_hashes ++ [W8 2]) hash
  end%I.

Local Fixpoint tree_height (t : tree) : nat :=
  match t with
  | (Interior children) =>
      let map_fn := (λ c,
                       match c with
                       | None => O
                       | Some c => tree_height c
                       end
                    ) in
      S (list_max (map_fn <$> children))
  | _ => O
  end.

Lemma tree_ind_strong_aux (P : tree → Prop) :
  ∀ (h' : nat),
  ∀ h, (h ≤ h')%nat →
  ∀ t, tree_height t = h →
  (∀ l : list w8, P (Cut l)) →
  (∀ l : list w8, P (Leaf l)) →
  (∀ l : list (option tree),
     (∀ x, In (Some x) l → P x) →
     P (Interior l)) →
  P t.
Proof.
  induction h'.
  - intros. destruct h; last lia.
    destruct t.
    + done.
    + done.
    + exfalso. simpl in *. lia.
  -
    intros.
    destruct (decide (h = S h')).
    2:{ eapply (IHh' h); try done; lia. }
    subst.
    destruct t.
    + exfalso. simpl in *. lia.
    + exfalso. simpl in *. lia.
    + apply H3.
      intros.
      eapply IHh'.
      2:{ done. }
      {
        simpl in e.
        inversion_clear e.
        clear H.
        induction l.
        - simpl. done.
        - destruct H0 as [|].
          + subst. simpl. lia.
          + simpl.
            rewrite Nat.max_le_iff.
            right.
            by apply IHl.
      }
      all: done.
Qed.

Lemma tree_ind_strong (P : tree → Prop) :
  (∀ l : list w8, P (Cut l)) →
  (∀ l : list w8, P (Leaf l)) →
  (∀ l : list (option tree),
     (∀ x, In (Some x) l → P x) →
     P (Interior l)) →
  ∀ t, P t.
Proof.
  intros. by eapply tree_ind_strong_aux.
Qed.

Lemma list_lookup_In (V : Type) (l : list V) i v : l !! i = Some v → In v l.
Proof.
  revert i v.
  induction l; first done; intros.
  destruct i.
  - simpl. naive_solver.
  - right. simpl in H. by eapply IHl.
Qed.

#[global]
Instance is_node_hash_timeless tr hash : Timeless (is_node_hash tr hash).
Proof.
  revert hash.
  induction tr using tree_ind_strong; try apply _.
  intros hash.
  simpl.
  apply exist_timeless. intros.
  apply sep_timeless; try apply _.
  apply big_sepL2_timeless.
  intros.
  apply list_lookup_fmap_Some in H0 as [? ?].
  intuition. subst. destruct x0; try apply _.
  apply list_lookup_In in H2.
  by apply H.
Qed.

#[global]
Instance is_node_hash_persistent tr hash : Persistent (is_node_hash tr hash).
Proof.
  revert hash.
  induction tr using tree_ind_strong; try apply _.
  intros hash.
  simpl.
  apply exist_persistent. intros.
  apply sep_persistent; try apply _.
  apply big_sepL2_persistent.
  intros.
  apply list_lookup_fmap_Some in H0 as [? ?].
  intuition. subst. destruct x0; try apply _.
  apply list_lookup_In in H2.
  by apply H.
Qed.

Lemma node_hash_len tr hash :
  is_node_hash tr hash -∗ ⌜length hash = 32%nat⌝.
Proof.
  iIntros "Htree".
  destruct tr.
  { iDestruct "Htree" as "[%Heq %Hlen]". naive_solver. }
  { iDestruct (is_hash_len with "Htree") as "%Hlen"; naive_solver. }
  {
    iDestruct "Htree" as (ch) "[_ Htree]".
    by iDestruct (is_hash_len with "Htree") as "%Hlen".
  }
Qed.

Lemma concat_len_eq {A : Type} sz (l1 l2 : list (list A)) :
  concat l1 = concat l2 →
  (Forall (λ l, length l = sz) l1) →
  (Forall (λ l, length l = sz) l2) →
  0 < sz →
  l1 = l2.
Proof.
  intros Heq_concat Hlen_l1 Hlen_l2 Hsz.
  apply (f_equal length) in Heq_concat as Heq_concat_len.
  do 2 rewrite concat_length in Heq_concat_len.
  generalize dependent l2.
  induction l1 as [|a1]; destruct l2 as [|a2]; simpl;
    intros Heq_concat Hlen_l2 Heq_concat_len;
    decompose_Forall; eauto with lia.
  apply (f_equal (take (length a1))) in Heq_concat as Htake_concat.
  apply (f_equal (drop (length a1))) in Heq_concat as Hdrop_concat.
  rewrite <-H in Htake_concat at 2.
  rewrite <-H in Hdrop_concat at 2.
  do 2 rewrite take_app_length in Htake_concat.
  do 2 rewrite drop_app_length in Hdrop_concat.
  rewrite Htake_concat.
  apply (app_inv_head_iff [a2]).
  apply IHl1; eauto with lia.
Qed.

(* Ownership of a merkle tree node, where the hashes on all nodes down path
   [path] may be invalid. *)
Definition own_node_except' (recur : option (list w8) -d> loc -d> tree -d> iPropO Σ) : option (list w8) -d> loc -d> tree -d> iPropO Σ :=
  (λ path ptr_tr tr,
     ∃ (hash val : list w8) sl_hash sl_children ptr_children sl_val,
       "Hptr_hash" ∷ ptr_tr ↦[node :: "hash"] (slice_val sl_hash) ∗
       "Hptr_val" ∷ ptr_tr ↦[node :: "mapVal"] (slice_val sl_val) ∗
       "Hptr_children" ∷ ptr_tr ↦[node :: "children"] (slice_val sl_children) ∗

       "Hsl_children" ∷ own_slice_small sl_children ptrT (DfracOwn 1) ptr_children ∗
       "#Hval" ∷ own_slice_small sl_val byteT DfracDiscarded val ∗

       "#Hhash" ∷ own_slice_small sl_hash byteT DfracDiscarded hash ∗
       "#His_hash" ∷ match path with
         | None => is_node_hash tr hash
         | _ => True
         end ∗
       "Hchildren" ∷ match tr with
       (* We should never have cuts in in-memory trees. *)
       | Cut _ => False
       | Leaf v => ⌜ v = val ⌝
       | Interior children =>
           "%Hchildren_len" ∷ ⌜ length ptr_children = uint.nat (W64 256) ⌝ ∗
           "Hchildren" ∷
             ([∗ list] idx ↦ child;ptr_child ∈ children;ptr_children,
                match child with
                | None => ⌜ ptr_child = null ⌝
                | Some child =>
                    ▷ recur (match path with
                             | Some (a :: path) => if decide (uint.nat a = idx) then (Some path)
                                                 else None
                             | _ => None
                             end)
                      ptr_child child
                end
             )
         end)%I.

Local Instance own_node_except'_contractive : Contractive own_node_except'.
Proof.
  intros ????.
  repeat intros ?.
  destruct x2; try solve_proper.
  solve_proper_prepare.
  repeat (f_contractive || f_equiv).
  apply H. (* XXX: doing this manually because [f_equiv] doesn't look for 3
              arguments*)
Qed.

Definition own_node_except : option (list w8) → loc → tree → iProp Σ := fixpoint own_node_except'.

Lemma own_node_except_unfold path ptr obj :
  own_node_except path ptr obj ⊣⊢ (own_node_except' own_node_except) path ptr obj.
Proof.
  apply (fixpoint_unfold own_node_except').
Qed.

Fixpoint is_tree_lookup (tr : tree) (k : list w8) (v : option (list w8)) : Prop :=
  match tr with
  | Cut _ => False
  | Leaf v' => match k with
             | [] => v = Some v'
             | _ => v = None
             end
  | Interior children =>
      match k with
      | [] => v = None
      | pos :: k => match (children !! (uint.nat pos)) with
                  | Some (Some child) => is_tree_lookup child k v
                  | Some None => v = None
                  | None => False
                  end
      end
  end.

Definition eq_tree_map (tr : tree) (key_prefix: list w8) (m : gmap (list w8) (list w8)) : Prop :=
  ∀ k, is_tree_lookup tr k (m !! (key_prefix ++ k)).

Lemma own_node_except_mono path2 path1 root tr :
  match path1, path2 with
  | Some a, Some b => prefix a b
  | None, _ => True
  | _, _ => False
  end →
  own_node_except path1 root tr -∗
  own_node_except path2 root tr.
Proof.
  iLöb as "IH" forall (tr root path1 path2).
  iIntros (Hpre) "Hnode".
  rewrite own_node_except_unfold.
  rewrite own_node_except_unfold.
  iNamed "Hnode".
  iFrame "Hptr_hash ∗#".
  iSplitR.
  { by destruct path1, path2. }
  destruct tr; iFrame.
  iNamed "Hchildren".
  iSplitR; first done.
  iApply (big_sepL2_impl with "Hchildren").
  iModIntro. iIntros.
  destruct x1; last done.
  iApply ("IH" with "[] [$]").
  iPureIntro.
  destruct path1 as [[]|]; destruct path2 as [[]|]; try done.
  + exfalso. by apply prefix_nil_not in Hpre.
  + pose proof Hpre as Hpre2.
    apply prefix_cons_inv_1 in Hpre2.
    apply prefix_cons_inv_2 in Hpre.
    subst. by destruct decide.
Qed.

End internal.

Section external.
Context `{!heapGS Σ}.

Definition full_height := (W64 32).

Definition has_tree_height tr (height : nat) : Prop :=
  (fix go tr height {struct height} :=
     match height with
     | O => match tr with Cut _ => False | Interior _ => False | _ => True end
     | S height => match tr with
                  | Leaf _ => False
                  | Cut _ => True
                  | Interior children =>
                      Forall (λ ochild,
                                match ochild with
                                | None => True
                                | Some child => go child height
                                end
                        ) children
                  end
     end) tr height.

Definition is_context c : iProp Σ :=
  ∃ (emptyHash_sl : Slice.t) (emptyHash : list w8),
    "#HemptyHash" ∷ c ↦[context :: "emptyHash"]□ (slice_val emptyHash_sl) ∗
    "#Hhash_sl" ∷ own_slice_small emptyHash_sl byteT DfracDiscarded emptyHash ∗
    "#Hhash" ∷ is_hash [W8 0] emptyHash.

Typeclasses Opaque is_context.

(* own_merkle denotes ownership of a merkle tree containing some entries. *)
Definition own_merkle ptr_tr entries : iProp Σ :=
  ∃ (root ctx : loc),
  "Hroot" ∷ ptr_tr ↦[Tree :: "root"] #root ∗
  "Hctx" ∷ ptr_tr ↦[Tree :: "ctx"] #ctx ∗
  "Hnode" ∷ (if decide (root = null) then ⌜ entries = ∅ ⌝
             else
               ∃ tr,
               "Hnode" ∷ own_node_except None root tr ∗
               "%Htree" ∷ ⌜ eq_tree_map tr [] entries ⌝ ∗
               "%Hheight" ∷ ⌜ has_tree_height tr (uint.nat full_height) ⌝
    ) ∗
  "#His_ctx" ∷ is_context ctx
.

(* is_dig says that the tree with these entries has this digest. *)
Definition is_dig entries dig : iProp Σ :=
  ("%Hentries_empty" ∷ ⌜ entries = ∅ ⌝ ∗
  "#Hdig" ∷ is_hash [W8 0] dig) ∨
  (∃ tr,
  "%Htree" ∷ ⌜ eq_tree_map tr [] entries ⌝ ∗
  "#Hdig" ∷ is_node_hash tr dig)
.

(* is_merkle_entry says that (id, val) is contained in the tree with this digest.
we use (val : option string) instead of (val : tree) bc there are really
only two types of nodes we want to allow. *)
Definition is_merkle_entry id val digest : iProp Σ :=
  (is_hash [W8 0] digest ∧ ⌜ val = None ⌝)
  ∨
  (∃ tr, is_node_hash tr digest ∧ ⌜ is_tree_lookup tr id val ⌝)
.

Lemma is_node_hash_not_empty tr dig id val :
  is_tree_lookup tr id val →
  is_node_hash (Σ := Σ) tr dig -∗
  is_hash [W8 0] dig -∗
  False.
Proof.
  iIntros (H) "Hdig1 Hdig2".
  destruct tr.
  + by destruct id.
  + simpl. iDestruct (is_hash_inj with "Hdig1 Hdig2") as %Hbad.
    apply (f_equal last) in Hbad. by rewrite last_app in Hbad.
  + simpl. iDestruct "Hdig1" as (?) "[_ Hdig1]".
    iDestruct (is_hash_inj with "Hdig1 Hdig2") as %Hbad.
    apply (f_equal last) in Hbad. by rewrite last_app in Hbad.
Qed.

Lemma is_merkle_entry_inj id val1 val2 digest :
  is_merkle_entry id val1 digest -∗
  is_merkle_entry id val2 digest -∗
  ⌜val1 = val2⌝.
Proof.
  iInduction (id) as [|a] "IH" forall (digest).
  {
    iIntros "[[Hval1 %]|(%tr1 & Htree1 & %Hlookup1)] [[Hval2 %]|(%tr2 & Htree2 & %Hlookup2)]"; subst; try done.
    - iExFalso. by iDestruct (is_node_hash_not_empty with "[$] [$]") as "$".
    - iExFalso. by iDestruct (is_node_hash_not_empty with "[$] [$]") as "$".
    - simpl in *.  destruct tr1, tr2; simpl in *; subst; try done.
      + iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
        list_simplifier. done.
      + simpl. iDestruct "Htree2" as (?) "[? Htree2]".
        iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
        exfalso. by list_simplifier.
      + simpl. iDestruct "Htree1" as (?) "[? Htree1]".
        iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
        exfalso. by list_simplifier.
  }
  iIntros "[[Hval1 %]|(%tr1 & Htree1 & %Hlookup1)] [[Hval2 %]|(%tr2 & Htree2 & %Hlookup2)]"; subst; try done.
  { iExFalso. by iDestruct (is_node_hash_not_empty with "[$] [$]") as "$". }
  { iExFalso. by iDestruct (is_node_hash_not_empty with "[$] [$]") as "$". }
  {
    simpl in *.
    destruct tr1, tr2; subst; try done.
    - simpl. iDestruct "Htree2" as (?) "[? Htree2]".
      iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
      exfalso. by list_simplifier.
    - simpl. iDestruct "Htree1" as (?) "[? Htree1]".
      iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
      exfalso. by list_simplifier.
    - simpl.
      iDestruct "Htree1" as (?) "[Hchildren1 Htree1]".
      iDestruct "Htree2" as (?) "[Hchildren2 Htree2]".
      iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
      list_simplifier.
      rename H into Heq.
      iClear "Htree1 Htree2".

      iAssert (⌜ child_hashes0 = child_hashes ⌝)%I with "[-]" as %->.
      {
        iApply pure_mono.
        { by pose proof (and_ind (and_ind (concat_len_eq (32%nat) _ _ Heq))). }
        iSplit.
        2:{ word. }
        iSplit.
        - rewrite Forall_forall.
          iIntros (hash Helem_of).
          clear a Hlookup1 Hlookup2.
          apply elem_of_list_lookup_1 in Helem_of as [a Hlookup].
          iClear "Hchildren1".
          iDestruct (big_sepL2_lookup_2_some _ _ _ a with "Hchildren2") as %[? Hlookup'].
          { done. }
          apply list_lookup_fmap_Some in Hlookup' as (? & Hlookup' & ->).
          iDestruct (big_sepL2_lookup _ _ _ a with "Hchildren2") as "H".
          { rewrite list_lookup_fmap Hlookup' //. }
          { done. }
          simpl.
          destruct x0.
          { by iApply node_hash_len. }
          { by iApply is_hash_len. }
        - rewrite Forall_forall.
          iIntros (hash Helem_of).
          clear a Hlookup1 Hlookup2.
          apply elem_of_list_lookup_1 in Helem_of as [a Hlookup].
          iClear "Hchildren2".
          iDestruct (big_sepL2_lookup_2_some _ _ _ a with "Hchildren1") as %[? Hlookup'].
          { done. }
          apply list_lookup_fmap_Some in Hlookup' as (? & Hlookup' & ->).
          iDestruct (big_sepL2_lookup _ _ _ a with "Hchildren1") as "H".
          { rewrite list_lookup_fmap Hlookup' //. }
          { done. }
          simpl.
          destruct x0.
          { by iApply node_hash_len. }
          { by iApply is_hash_len. }
      }
      destruct (l !! uint.nat a) eqn:Hlookup; [|done].
      destruct (l0 !! uint.nat a) eqn:Hlookup0; [|done].
      iDestruct (big_sepL2_lookup_1_some _ _ _ (uint.nat a) with "Hchildren1") as %[? Hlookup'].
      { rewrite list_lookup_fmap Hlookup //. }
      iDestruct (big_sepL2_lookup_1_some _ _ _ (uint.nat a) with "Hchildren2") as %[? Hlookup0'].
      { rewrite list_lookup_fmap Hlookup0 //. }


      iDestruct (big_sepL2_lookup _ _ _ (uint.nat a) with "Hchildren1") as "Hchild1".
      { rewrite list_lookup_fmap Hlookup //. }
      { done. }
      iDestruct (big_sepL2_lookup _ _ _ (uint.nat a) with "Hchildren2") as "Hchild2".
      { rewrite list_lookup_fmap Hlookup0 //. }
      { done. }
      simpl.
      destruct o, o0; subst.
      + iApply ("IH" with "[Hchild1] [Hchild2]").
        { iRight. by iFrame. }
        { iRight. by iFrame. }
      + destruct t.
        { simpl in *. destruct id; done. }
        { simpl. iDestruct (is_hash_inj with "[$] [$]") as "%Hbad".
          apply (f_equal last) in Hbad. rewrite last_snoc //= in Hbad. }
        { simpl. iDestruct "Hchild1" as (?) "[? ?]". iDestruct (is_hash_inj with "[$] [$]") as "%Hbad".
          apply (f_equal last) in Hbad. rewrite last_snoc //= in Hbad. }
      + destruct t.
        { simpl in *. destruct id; done. }
        { simpl. iDestruct (is_hash_inj with "[$] [$]") as "%Hbad".
          apply (f_equal last) in Hbad. rewrite last_snoc //= in Hbad. }
        { simpl. iDestruct "Hchild2" as (?) "[? ?]". iDestruct (is_hash_inj with "[$] [$]") as "%Hbad".
          apply (f_equal last) in Hbad. rewrite last_snoc //= in Hbad. }
      + done.
  }
Qed.

Lemma is_dig_inj m1 m2 digest :
  is_dig m1 digest -∗
  is_dig m2 digest -∗
  ⌜ m1 = m2 ⌝.
Proof.
  iIntros "Hval1 Hval2".
  iDestruct "Hval1" as "[Hval1|Hval1]"; iNamedSuffix "Hval1" "1";
  try (rename tr into tr1);
  iDestruct "Hval2" as "[Hval2|Hval2]"; iNamedSuffix "Hval2" "2";
  try (rename tr into tr2); subst.
  - done.
  - iExFalso. specialize (Htree2 []).
    iDestruct (is_node_hash_not_empty with "[$] [$]") as "?"; done.
  - iExFalso. specialize (Htree1 []).
    iDestruct (is_node_hash_not_empty with "[$] [$]") as "?"; done.
  - iApply pure_mono; first apply map_eq.
    iIntros (k).
    specialize (Htree1 k).
    specialize (Htree2 k).
    iDestruct (is_merkle_entry_inj with "[] []") as %Heq.
    { iRight. iExists _. iFrame "Hdig1". done. }
    { iRight. iExists _. iFrame "Hdig2". done. }
    done.
Qed.

(* is_merkle_entry_with_map says that if you know an entry as well
as the underlying map, you can combine those to get a pure map fact. *)
Lemma is_merkle_entry_with_map id val dig m :
  is_merkle_entry id val dig -∗ is_dig m dig -∗ ⌜ m !! id = val ⌝.
Proof.
  iIntros "Hentry Hdig".
  iDestruct "Hdig" as "[Hbad|H]".
  {
    iNamed "Hbad". subst.
    iDestruct "Hentry" as "[[Hempty %]| (%tr & #Hhash2 & %)]"; subst; try done.
    by iDestruct (is_node_hash_not_empty with "[$] [$]") as "?".
  }
  iNamed "H".
  iDestruct (is_merkle_entry_inj with "[] [$]") as %Heq.
  { iRight. iExists _; iFrame "Hdig". done. }
  { done. }
Qed.

End external.

(*
Module pathProof.
Record t :=
  mk {
    id: list w8;
    nodeHash: list w8;
    digest: list w8;
    childHashes: list (list (list w8));
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_id sl_nodeHash sl_digest sl_childHashes,
  "Hid" ∷ own_slice_small sl_id byteT (DfracOwn 1) obj.(id) ∗
  "Hptr_id" ∷ ptr ↦[pathProof :: "id"] (slice_val sl_id) ∗
  "HnodeHash" ∷ own_slice_small sl_nodeHash byteT (DfracOwn 1) obj.(nodeHash) ∗
  "Hptr_nodeHash" ∷ ptr ↦[pathProof :: "nodeHash"] (slice_val sl_nodeHash) ∗
  "Hdigest" ∷ own_slice_small sl_digest byteT (DfracOwn 1) obj.(digest) ∗
  "Hptr_digest" ∷ ptr ↦[pathProof :: "digest"] (slice_val sl_digest) ∗
  "#HchildHashes" ∷ is_Slice3D sl_childHashes obj.(childHashes) ∗
  "Hptr_childHashes" ∷ ptr ↦[pathProof :: "childHashes"] (slice_val sl_childHashes) ∗
  "%Hlen_id_depth" ∷ ⌜length obj.(id) = length obj.(childHashes)⌝ ∗
  "%Hlen_id_ub" ∷ ⌜length obj.(id) ≤ 32⌝.
End local_defs.
End pathProof. *)

Section wps.
Context `{!heapGS Σ}.

Lemma wp_newCtx :
  {{{ True }}}
    newCtx #()
  {{{ ctx, RET #ctx; is_context ctx }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_rec.
  wp_rec.
  wp_apply (wp_SliceSingleton (V:=w8)).
  iIntros (?) "Hsl".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_Hash with "[$]").
  iIntros "*". iNamed 1.
  iApply wp_fupd.
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H".
  iNamed "H".
  iApply "HΦ".
  iClear "Hdata".
  iMod (struct_field_pointsto_persist with "[$]") as "#?".
  iMod (own_slice_small_persist with "[$]") as "#?".
  iMod (own_slice_small_persist with "[$]") as "#?".
  by iFrame "#".
Qed.

Lemma own_node_except_not_null p t:
  own_node_except p null t -∗
  False.
Proof.
  iIntros "Hnode".
  iDestruct (own_node_except_unfold with "Hnode") as "Hnode".
  wp_pures.
  iDestruct "Hnode" as (??????) "(_ & H & _)".
  iExFalso.
  iDestruct (struct_field_pointsto_not_null with "H") as %?; done.
Qed.

Lemma wp_context__getHash ctx n tr :
  {{{
        "#Hctx" ∷ is_context ctx ∗
        "Hnode" ∷ own_node_except None n tr
  }}}
    context__getHash #ctx #n
  {{{
        hash_sl hash, RET (slice_val hash_sl);
        own_node_except None n tr ∗
        own_slice_small hash_sl byteT DfracDiscarded hash ∗
        is_node_hash tr hash
  }}}.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_rec.
  wp_pures. wp_if_destruct.
  { by iDestruct (own_node_except_not_null with "[$]") as "?". }
  iDestruct (own_node_except_unfold with "Hnode") as "Hnode".
  iNamed "Hnode".
  wp_loadField.
  iApply "HΦ".
  iFrame "∗#%".
  iApply own_node_except_unfold.
  iFrame "∗#%".
Qed.

Lemma wp_context__getHash_null ctx :
  {{{
        "#Hctx" ∷ is_context ctx
  }}}
    context__getHash #ctx #null
  {{{
        hash_sl hash, RET (slice_val hash_sl);
        own_slice_small hash_sl byteT DfracDiscarded hash ∗
        is_hash [W8 0] hash
  }}}.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H". iNamed "Hctx".
  wp_rec.
  wp_pures.
  wp_loadField.
  iApply "HΦ".
  iFrame "#".
Qed.

Lemma wp_Tree_Digest ptr_tr entries :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries
  }}}
  Tree__Digest #ptr_tr
  {{{
    sl_dig dig, RET (slice_val sl_dig);
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "Hdig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
    "#HisDig" ∷ is_dig entries dig
  }}}.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_rec.
  iNamed "Htree".
  wp_loadField.
  iNamed "Hctx".
  wp_loadField.
  destruct decide.
  - subst. wp_apply (wp_context__getHash_null with "[$]").
    iIntros "* #[? ?]".
    iApply "HΦ".
    iDestruct "Hnode" as %->.
    iFrame. simpl. iFrame "His_ctx". iSplitL; first done.
    iFrame.
    simpl.
    iFrame "#".
    by iLeft.
  - iNamed "Hnode".
    wp_apply (wp_context__getHash with "[$]").
    iIntros "* (Hnode & #? & #?)".
    iApply "HΦ".
    iFrame.
    rewrite decide_False //.
    iFrame "∗His_ctx #%".
Qed.

Lemma wp_compLeafNodeHash mapVal_sl mapVal dq :
   {{{ own_slice_small mapVal_sl byteT dq mapVal }}}
     compLeafNodeHash (slice_val mapVal_sl)
   {{{
         hash_sl hash, RET (slice_val hash_sl);
         own_slice_small mapVal_sl byteT dq mapVal ∗
         own_slice_small hash_sl byteT (DfracOwn 1) hash ∗
         is_node_hash (Leaf mapVal) hash
   }}}.
Proof.
  iIntros (?) "HmapVal HΦ".
  wp_rec.
  wp_apply wp_slice_len.
  iDestruct (own_slice_small_sz with "[$]") as %Hsz.
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { word. }
  iIntros (?) "Hhash_sl".
  wp_apply wp_ref_to; [val_ty|].
  iIntros (b_ptr) "Hb".
  wp_pures.
  wp_load.
  wp_apply (wp_WriteBytes with "[$]").
  iIntros (?) "[? ?]".
  wp_store.
  wp_load.
  wp_apply (wp_SliceAppend with "[$]").
  iIntros (?) "?".
  wp_store.
  wp_load.
  iDestruct (own_slice_to_small with "[$]") as "H".
  wp_apply (wp_Hash with "[$]").
  iIntros "*". iNamed 1.
  iApply "HΦ".
  iFrame.
  simpl.
  rewrite replicate_0. done.
Qed.

Lemma new_interior_eq_empty k' :
  eq_tree_map (Interior (replicate (uint.nat 256) None)) k' ∅.
Proof.
  intros ?. destruct k.
  { done. }
  { simpl. rewrite lookup_replicate_2; [done|word]. }
Qed.

Lemma new_leaf_eq_map k' :
  eq_tree_map (Leaf []) k' {[ k' := [] ]}.
Proof.
  intros ?. destruct k.
  { rewrite /= app_nil_r lookup_insert //. }
  { rewrite lookup_singleton_ne //. intros H.
    apply (f_equal length) in H. rewrite app_length /= in H.
    lia.
  }
Qed.

Lemma eq_tree_map_child children x child kp m :
  children !! (uint.nat x) = Some (Some child) →
  eq_tree_map (Interior children) kp m →
  eq_tree_map child (kp ++ [x]) m.
Proof.
  intros Hchild Heq k.
  specialize (Heq (x :: k)).
  rewrite -app_assoc /=.
  by rewrite /= Hchild in Heq.
Qed.

Lemma eq_tree_map_new_interior children (x : u8) kp m :
  length children = uint.nat (W64 256) →
  children !! (uint.nat x) = Some None →
  eq_tree_map (Interior children) kp m →
  eq_tree_map (Interior (<[uint.nat x:=Some (Interior (replicate (uint.nat (W64 256)) None))]> children))
    kp m.
Proof.
  intros Hlen Hchild Heq k.
  specialize (Heq k).
  destruct k.
  - done.
  - simpl in *.
    destruct (decide (x = w)).
    + subst. rewrite Hchild in Heq.
      rewrite list_lookup_insert; last word.
      destruct k.
      * done.
      * rewrite /= lookup_replicate_2; [done|word].
    + rewrite list_lookup_insert_ne //.
      intros H. apply n. word.
Qed.

Lemma eq_tree_map_insert_leaf children (x : u8) kp m v :
  length children = uint.nat (W64 256) →
  match (children !! (uint.nat x)) with
  | Some (Some (Leaf _)) => True
  | Some None => True
  | _ => False
  end →
  eq_tree_map (Interior children) kp m →
  eq_tree_map (Interior (<[uint.nat x:=Some (Leaf v)]> children))
    kp (<[ kp ++ [x] := v ]> m).
Proof.
  intros Hlen Hleaf Heq k.
  specialize (Heq k).
  destruct k.
  - simpl in *. rewrite lookup_insert_ne //.
    intros Hbad. naive_solver.
  - destruct (decide (x = w)).
    + subst. simpl in *.
      rewrite list_lookup_insert; last word.
      destruct k; simpl.
      * rewrite lookup_insert //.
      * destruct (children !! uint.nat w) as [[[]|]|]; try done.
        -- simpl in *. rewrite lookup_insert_ne //.
           intros Hbad. list_simplifier.
        -- simpl in *. rewrite lookup_insert_ne //.
           intros Hbad. list_simplifier.
    + simpl in *.
      rewrite list_lookup_insert_ne //.
      2:{ intros H. apply n. word. }
      rewrite lookup_insert_ne //.
      intros Hbad.
      list_simplifier.
Qed.

Lemma has_tree_height_interior children (pos h : nat) :
  (h > 1)%nat →
  has_tree_height (Interior children) h →
  has_tree_height (Interior (<[pos := Some (Interior (replicate (uint.nat (W64 256)) None))]> children)) h.
Proof.
  intros ? Hheight.
  destruct h; first lia.
  simpl in *.
  destruct h; first lia.
  apply Forall_insert; try done.
  simpl. apply Forall_forall.
  intros. rewrite elem_of_replicate in H0. naive_solver.
Qed.

Lemma wp_updInteriorHash (ctx n : loc) b children :
  {{{
        "#Hctx" ∷ is_context ctx ∗
        "Hnode" ∷ own_node_except (Some []) n (Interior children) ∗
        "Hsl" ∷ own_slice b byteT (DfracOwn 1) ([] : list w8)
  }}}
    context__updInteriorHash #ctx (slice_val b) #n
  {{{
        sl (x : list w8), RET (slice_val sl);
        own_slice sl byteT (DfracOwn 1) x ∗
        own_node_except None n (Interior children)
  }}}.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_rec.
  wp_pures.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (b_ptr) "Hb".
  wp_pures.
  iDestruct (own_node_except_unfold with "Hnode") as "H".
  iNamed "H". iNamed "Hchildren".
  iClear "Hhash".
  eset (loopInv:=(λ (i : w64),
                   ∃ sl hashes,
                   "Hb" ∷ b_ptr ↦[slice.T byteT] (slice_val sl) ∗
                   "Hsl" ∷ own_slice sl byteT (DfracOwn 1) (concat hashes) ∗
                   "Hhash" ∷ ([∗ list] c;h ∈ (take (uint.nat i) children);hashes,
                                match c with
                                | None => is_hash [W8 0] h
                                | Some c => is_node_hash c h
                                end) ∗
                   "Hchildren" ∷ _
                )%I
      ).
  wp_loadField.
  wp_apply (wp_forSlice loopInv with "[] [Hsl_children Hb Hsl Hchildren]").
  2:{
    iSplitR "Hsl_children"; last iFrame.
    repeat iExists _.
    iFrame.
    rewrite take_0.
    instantiate (1:=[]).
    simpl.
    iFrame "∗#".
  }
  {
    clear Φ.
    iIntros (? child_ptr ?) "!# (HloopInv & %Hlt & %Hlookup) HΦ".
    iNamed "HloopInv".
    iDestruct (big_sepL2_lookup_2_some with "Hchildren") as %[child Hchild];
      try eassumption.
    iDestruct (big_sepL2_lookup_acc with "Hchildren") as "[Hchild Hchildren]";
      try eassumption.
    destruct child.
    - wp_pures.
      wp_apply (wp_context__getHash with "[$Hchild]").
      { iFrame "Hctx". }
      iIntros "* (Hchild & Hchild_hash_sl & Hchild_hash)".
      wp_load.
      wp_apply (wp_WriteBytes with "[$]").
      iIntros (?) "[Hsl _]".
      wp_store.
      iApply "HΦ".
      iSpecialize ("Hchildren" with "[$]").
      repeat iExists _. iFrame.
      instantiate (1:=hashes ++ [hash0]).
      rewrite concat_app /= app_nil_r.
      iFrame.
      iModIntro.
      replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
      erewrite take_S_r; last done.
      iApply big_sepL2_snoc.
      iFrame.
    - wp_pures.
      iDestruct "Hchild" as %->.
      wp_apply (wp_context__getHash_null with "[]").
      { iFrame "Hctx". }
      iIntros "* (Hchild_hash_sl & Hchild_hash)".
      wp_load.
      wp_apply (wp_WriteBytes with "[$]").
      iIntros (?) "[Hsl _]".
      wp_store.
      iApply "HΦ".
      iSpecialize ("Hchildren" with "[//]").
      repeat iExists _. iFrame.
      instantiate (1:=hashes ++ [hash0]).
      rewrite concat_app /= app_nil_r.
      iFrame.
      iModIntro.
      replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
      erewrite take_S_r; last done.
      iApply big_sepL2_snoc.
      iFrame.
  }
  iIntros "[HloopInv Hsl_children]".
  iDestruct (own_slice_small_sz with "Hsl_children") as %Hchildren_sl_len.
  wp_pures.
  iNamed "HloopInv".
  iDestruct (big_sepL2_length with "Hchildren") as %Hlen.
  wp_load.
  wp_apply (wp_SliceAppend with "[$Hsl]").
  iIntros (?) "Hsl".
  wp_store.
  wp_load.
  iDestruct (own_slice_split with "Hsl") as "[Hsl Hcap]".
  wp_apply (wp_Hash with "[$]").
  iClear "His_hash".
  iRename "Hhash" into "His_hashes".
  iIntros "*". iNamed 1.
  wp_storeField.
  wp_load.
  iApply "HΦ".
  iFrame.
  iApply own_node_except_unfold.
  iMod (own_slice_small_persist with "Hhash") as "Hhash".
  iFrame "Hptr_val ∗".
  iFrame "#%".
  iApply big_sepL2_fmap_l.
  rewrite take_ge; last word.
  iModIntro.
  iApply (big_sepL2_impl with "His_hashes").
  iIntros "!# * %% $".
Qed.

(* is_merkle_proof says that the merkle proof gives rise to a cut tree
that has digest dig. and is_merkle_entry id val dig.
the cut tree is the existential tree in is_merkle_entry. *)
Definition is_merkle_proof (proof : (list w8)) (id : list w8)
    (val : option (list w8)) (dig : list w8) : iProp Σ :=
  ∃ (proof' : list (list (list w8))),
    ⌜ proof = concat (concat (proof')) ⌝ ∧
  let otr :=
    foldl (λ tr '(sibling_digs, pos),
             let siblings := Some <$> (Cut <$> sibling_digs) in
             Some (Interior ((take (uint.nat pos) siblings) ++ [tr] ++ (drop (uint.nat pos) siblings)))
      ) (Leaf <$> val) (zip proof' id) in
  match otr with
  | Some tr => is_node_hash tr dig ∧ ⌜ is_tree_lookup tr id val ⌝
  | None => is_hash [W8 0] dig ∧ ⌜ val = None ⌝
  end.

Global Instance is_merkle_proof_persis proof id val dig :
  Persistent (is_merkle_proof proof id val dig).
Proof. apply _. Qed.

Lemma is_merkle_proof_to_entry proof id val dig :
  is_merkle_proof proof id val dig -∗ is_merkle_entry id val dig.
Proof.
  iIntros "(% & % & #?)"; subst.
  rewrite /is_merkle_proof.
  destruct foldl.
  { iRight. iFrame "#". }
  { iLeft. iFrame "#". }
Qed.


Lemma own_node_except_None_is_node_hash n tr :
  own_node_except None n tr -∗
  ∃ dig, is_node_hash tr dig.
Proof.
  iIntros "H".
  iDestruct (own_node_except_unfold with "H") as "H".
  iNamed "H".
  iFrame "#".
Qed.

Lemma wp_context__getProof v ctx n tr (label : list w8) label_sl dq :
  is_tree_lookup tr label v →
  length label = 32%nat →
  {{{
        "#Hctx" ∷ is_context ctx ∗
        "Hnode" ∷ own_node_except None n tr ∗
        "Hlabel_sl" ∷ own_slice_small label_sl byteT dq label ∗
        "%Hheight" ∷ ⌜ has_tree_height tr (uint.nat full_height) ⌝
  }}}
    context__getProof #ctx #n (slice_val label_sl)
  {{{
        proof_sl (proof : list w8), RET (slice_val proof_sl);
        own_node_except None n tr ∗
        own_slice_small label_sl byteT dq label ∗
        own_slice proof_sl byteT (DfracOwn 1) proof ∗
        (∀ dig,
           is_node_hash tr dig -∗
           is_merkle_proof proof label v dig
        )
  }}}.
Proof.
  iIntros (Hlookup Hlabel_length ?) "H HΦ".
  iNamed "H".
  wp_rec. wp_pures.
  wp_apply wp_NewSliceWithCap; [word|].
  iIntros (?) "Hproof_sl".
  wp_apply wp_ref_to; [val_ty|].
  iIntros (proof_ptr) "Hproof_ptr".
  wp_pures.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (currNode_ptr) "HcurrNode_ptr".
  wp_pures.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (depth_ptr) "Hdepth".
  wp_pures.
  iDestruct (own_node_except_None_is_node_hash with "Hnode") as "#[%dig Hdigest]".
  rewrite replicate_0.
  iAssert (
      ∃ (depth : w64) (curr_ptr: loc) curr_tr proof proof_sl,
        "Hdepth" ∷ depth_ptr ↦[uint64T] #depth ∗
        "HcurrNode_ptr" ∷ currNode_ptr ↦[ptrT] #curr_ptr ∗
        "Hnode" ∷ own_node_except None curr_ptr curr_tr∗
        "HnodeClose" ∷ (own_node_except None curr_ptr curr_tr -∗ own_node_except None n tr) ∗
        "Hproof_ptr" ∷ proof_ptr ↦[slice.T byteT] (slice_val proof_sl) ∗
        "Hproof_sl" ∷ own_slice proof_sl byteT (DfracOwn 1) (concat (concat proof)) ∗
        "%Hlookup" ∷ ⌜ is_tree_lookup curr_tr (drop (uint.nat depth) label) v ⌝ ∗
        "%Hheight" ∷ ⌜ has_tree_height curr_tr (uint.nat full_height - uint.nat depth)%nat ⌝ ∗
        "#Hproof" ∷ (let otr :=
                      foldl (λ tr '(sibling_digs, pos),
                               let siblings := Some <$> (Cut <$> sibling_digs) in
                               Some (Interior ((take (uint.nat pos) siblings) ++ [tr] ++ (drop (uint.nat pos) siblings)))
                        ) (Some tr) (zip proof label) in
                    match otr with
                    | Some tr => is_node_hash tr dig ∧ ⌜ is_tree_lookup tr label v ⌝
                    | None => is_hash [W8 0] dig ∧ ⌜ v = None ⌝
                    end)
    )%I with "[Hdepth HcurrNode_ptr Hproof_ptr Hproof_sl Hnode]" as "HloopInv".
  {
    repeat iExists _. instantiate (1:=nil).
    iFrame "∗#%".
    iIntros "$".
  }
  wp_forBreak_cond.
  wp_pures.
  iNamed "HloopInv".
  wp_load.
  wp_pures.
  wp_bind (if: #_ then _ else _)%E.
  wp_if_destruct.
  { (* haven't walked reached a leaf *)
    wp_load. wp_pures.
    wp_if_destruct.
    { (* execute loop body *)
      wp_pures.
      wp_load.
      iDestruct (own_node_except_unfold with "Hnode") as "Hnode".
      iNamed "Hnode".
      wp_loadField.
      wp_pures.
      wp_load.
      opose proof (list_lookup_lt label (uint.nat depth) ltac:(word)) as [pos Hlabel_lookup].
      wp_apply (wp_SliceGet with "[$Hlabel_sl //]").
      iIntros "Hlabel_sl".
      wp_pures.

      set (loopInv:=
             (λ (i : w64),
                ∃ proof_sl sibling_digs,
                "Hproof_ptr" ∷ proof_ptr ↦[slice.T byteT] (slice_val proof_sl) ∗
                "Hproof" ∷ own_slice proof_sl byteT (DfracOwn 1) ((concat (concat proof)) ++
                                                                        concat (sibling_digs))
          )%I).
      destruct curr_tr; try done.
      { exfalso.
        destruct (uint.nat full_height - uint.nat depth)%nat eqn:Hbad.
        { simpl in *. unfold full_height in Hbad. word. }
        { done. }
      }
      iNamed "Hchildren".
      iDestruct (own_slice_small_sz with "Hsl_children") as %Hsl_children_sz.
      iDestruct (own_slice_small_wf with "Hsl_children") as %Hsl_children_wf.
      wp_apply wp_SliceTake.
      { word. }
      wp_apply (wp_forSlice loopInv with "[] [Hsl_children Hproof_ptr Hproof]");
        admit.
    }
    { (* done with inner loop *)
      admit.
    }
  }
  (* done with loop. *)
  wp_pures.
  iRight.
  iModIntro. iSplitR; first done.
  wp_pures.
  wp_load.
  iApply "HΦ".
  admit.
Admitted.

Lemma wp_Tree__Put ptr_tr entries sl_id id sl_val val d0 d1 :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val
  }}}
  Tree__Put #ptr_tr (slice_val sl_id) (slice_val sl_val)
  {{{
    sl_dig sl_proof (err : bool),
    RET ((slice_val sl_dig), (slice_val sl_proof), #err);
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "%Hgenie" ∷ ⌜ length id = hash_len ↔ err = false ⌝ ∗
    "Herr" ∷
      if negb err then
        ∃ dig proof,
        "Htree" ∷ own_merkle ptr_tr (<[id:=val]>entries) ∗
        "Hdig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
        "#HisDig" ∷ is_dig (<[id:=val]>entries) dig ∗
        "Hproof" ∷ own_slice_small sl_proof byteT DfracDiscarded proof ∗
        "His_proof" ∷ is_merkle_proof proof id (Some val) dig
      else
        "Htree" ∷ own_merkle ptr_tr entries
  }}}.
Proof.
  iIntros (?) "H HΦ". iNamed "H".
  wp_rec.
  wp_pures.
  iDestruct (own_slice_small_sz with "Hid") as %Hsz_id.
  wp_apply wp_slice_len.
  wp_pures.
  wp_if_destruct.
  { (* return an error. *)
    wp_pures.
    replace (slice.nil) with (slice_val Slice.nil) by done.
    iApply "HΦ".
    iModIntro. iFrame. iPureIntro.
    word.
  }
  wp_apply wp_NewSliceWithCap.
  { word. }
  iIntros (?) "Hinteriors".
  wp_apply wp_ref_to; [val_ty|].
  iIntros (interiors_ptr) "Hinteriors_ptr".
  wp_pures.
  iNamed "Htree".
  wp_loadField.
  wp_pures.

  wp_bind (if: _ then _ else _)%E.
  wp_apply (wp_wand _ _ _ (λ _,
                             ∃ (root : loc) tr,
                               "Hroot" ∷ ptr_tr ↦[Tree::"root"] #root ∗
                               "Hnode" ∷ own_node_except (Some id) root tr ∗
                               "%Htree" ∷ ⌜ eq_tree_map tr [] entries ⌝ ∗
                               "%Hheight" ∷ ⌜ has_tree_height tr (uint.nat full_height) ⌝
              )%I
             with "[Hnode Hroot]").
  {
    wp_if_destruct.
    2:{
      iModIntro. iFrame "∗%".
      rewrite decide_False //.
      iNamed "Hnode".
      iDestruct (own_node_except_mono (Some id) with "[$]") as "$"; done.
    }
    wp_rec.
    wp_apply wp_NewSlice.
    iIntros (?) "Hsl".
    iDestruct (own_slice_to_small with "[$]") as "Hsl".
    wp_pures. wp_apply wp_allocStruct.
    { val_ty. }

    iDestruct "Hnode" as %->.
    iIntros (?) "Hnode".
    wp_storeField.
    iDestruct (struct_fields_split with "Hnode") as "H".
    iNamed "H".
    iExists _, (Interior (replicate (uint.nat (W64 256)) None)).
    iFrame.
    iSplitL.
    2:{
      (* XXX: could have lemmas for stuff like this *)
      iPureIntro. split.
      - (* tree still matches empty map *)
        apply new_interior_eq_empty.
      - (* tree respects has_tree_height *)
        rewrite /has_tree_height /=.
        destruct (uint.nat full_height) eqn:H.
        { exfalso. done. }
        clear H.
        by apply Forall_replicate.
    }
    iApply own_node_except_unfold .
    rewrite zero_slice_val.
    iFrame.
    iExists [], [].
    iDestruct (own_slice_small_nil) as "$".
    { done. }
    iSplitR; first done.
    iSplitR; first done.
    iApply big_sepL2_replicate_r.
    { rewrite length_replicate //. }
    iApply big_sepL_impl.
    { by iApply big_sepL_emp. }
    iModIntro. iIntros.
    apply lookup_replicate in H as [-> ?]. done.
  }
  iIntros (?) "HifInv".
  wp_pures.
  clear v root.
  iNamed "HifInv".
  wp_loadField.
  wp_load.
  wp_apply (wp_SliceAppend with "[$]").
  iIntros (?) "Hinteriors". rewrite replicate_0 app_nil_l.
  wp_store.
  clear ptr.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (depth_ptr) "Hdepth".
  wp_pures.
  set (loopInv :=
         (λ (depth : w64),
            ∃ (currNode_ptr : loc) sub_tree interiors_sl (interiors : list loc),
              "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
              "Hinteriors_ptr" ∷ interiors_ptr ↦[slice.T ptrT] (slice_val interiors_sl) ∗
              "Hinteriors" ∷ own_slice interiors_sl ptrT (DfracOwn 1) interiors ∗

              "%Hinteriors_last" ∷ ⌜ last interiors = Some currNode_ptr ⌝ ∗
              "Hnode" ∷ own_node_except (Some (drop (uint.nat depth) id)) currNode_ptr sub_tree ∗
              "%Hinteriors_length" ∷ ⌜ length interiors = S (uint.nat depth) ⌝ ∗
              "%Hsubmap" ∷ ⌜ eq_tree_map sub_tree (take (uint.nat depth) id) entries ⌝ ∗
              "%Hheight" ∷ ⌜ has_tree_height sub_tree (uint.nat full_height - uint.nat depth)%nat ⌝ ∗

              "Hrest" ∷ (∀ children' ,
                 own_node_except None currNode_ptr (Interior children') -∗
                 ⌜ eq_tree_map (Interior children') (take (uint.nat depth) id) (<[id := val]> entries) ⌝ -∗
                 ⌜ has_tree_height (Interior children') (uint.nat full_height - uint.nat depth)%nat ⌝ -∗
                 (foldl (λ P node_ptr,
                          ∃ children, own_node_except (Some []) node_ptr (Interior children) ∗
                                (own_node_except None node_ptr (Interior children) -∗ P)
                   )
                   (∃ children', own_node_except None root (Interior children') ∗
                           ⌜ eq_tree_map (Interior children') [] (<[id := val]> entries) ⌝ ∗
                           ⌜ has_tree_height (Interior children') (uint.nat full_height) ⌝)
                   (removelast interiors))
              )
         )%I).
  wp_apply (wp_forUpto' loopInv with "[$Hdepth Hid Hnode Hinteriors_ptr Hinteriors]").
  {
    iSplitR; first word.
    iFrame. repeat iExists _. iSplitR; first done.
    iSplitR; first done. iSplitR; first done.
    iSplitR; first done.
    iIntros (?). iIntros.
    simpl. iExists _; iFrame. done.
  }
  { (* one loop iteration *)
    clear Φ Hheight Htree.
    iIntros "!# * (H & HpathIdx & %Hlt) HΦ'".
    iNamed "H".
    wp_pures. wp_load. wp_load.
    iDestruct (own_slice_split_1 with "Hinteriors") as "[Hinteriors Hinteriors_cap]".
    wp_apply (wp_SliceGet with "[$Hinteriors]").
    {
      iPureIntro.
      rewrite last_lookup in Hinteriors_last.
      rewrite Hinteriors_length /= in Hinteriors_last.
      done.
    }
    iIntros "Hinteriors".
    wp_pures.
    wp_load.
    replace (word.sub (W64 32) (W64 1)) with (W64 31) in Hlt by word.
    opose proof (list_lookup_lt id (uint.nat i) ltac:(word)) as [pos H].
    wp_apply (wp_SliceGet with "[$Hid //]").
    iIntros "Hid".
    wp_pures.

    wp_bind (if: _ then _ else _)%E.
    wp_apply (wp_wand _ _ _ (λ _,
                               ∃ children child,
                                 let sub_tree := (Interior children) in
                                 "Hnode" ∷ own_node_except (Some (drop (uint.nat i) id)) currNode_ptr sub_tree ∗
                                 "%Hchild_lookup" ∷ ⌜ children !! (uint.nat pos) = Some (Some child) ⌝ ∗
                                 "%Hsubmap" ∷ ⌜ eq_tree_map sub_tree (take (uint.nat i) id) entries ⌝ ∗
                                 "%Hheight" ∷ ⌜ has_tree_height sub_tree (uint.nat full_height - uint.nat i) ⌝
                )%I
               with "[Hnode]").
    {
      iDestruct (own_node_except_unfold with "Hnode") as "Hnode".
      iNamed "Hnode".
      wp_loadField.

      destruct sub_tree as [| | children].
      { by iExFalso. }
      { simpl in Hheight. exfalso. subst.
        destruct (uint.nat full_height - uint.nat i)%nat eqn:Hdepth; simpl in *.
        { unfold full_height in Hdepth. word. }
        { word. }
      }
      iNamed "Hchildren".
      opose proof (list_lookup_lt ptr_children (uint.nat pos) ltac:(word)) as [ptr_child Hptr_child].

      wp_apply (wp_SliceGet with "[$Hsl_children]").
      { iPureIntro. instantiate (1:=ptr_child). rewrite -Hptr_child. f_equal.
        word. }
      iIntros "Hsl_children".
      wp_pures.

      iDestruct (big_sepL2_lookup_2_some with "Hchildren") as %[child Hchildren_lookup].
      { done. }
      iDestruct (big_sepL2_lookup_acc with "Hchildren") as "[Hchild Hchildren]".
      { done. }
      { done. }
      destruct child.
      { (* child is not null *)
        wp_pures.
        case_bool_decide.
        { inversion_clear H0.
          wp_pures.
          by iDestruct (own_node_except_not_null with "Hchild") as %?.
        }
        iSpecialize ("Hchildren" with "[$Hchild]").
        wp_pures.
        iModIntro.
        iExists children, _.
        iSplitL; last done.
        iApply own_node_except_unfold.
        iFrame "Hptr_val Hhash ∗#%".
      }
      { (* child node is null *)
        iDestruct "Hchild" as %->.
        wp_pures.
        wp_rec.
        wp_apply wp_NewSlice.
        iIntros (?) "Hsl".
        iDestruct (own_slice_to_small with "[$]") as "Hsl".
        wp_pures. wp_apply wp_allocStruct.
        { val_ty. }
        iIntros (child_ptr) "Hnode".
        wp_loadField.
        wp_apply (wp_SliceSet with "[$Hsl_children]").
        { replace (uint.nat (W64 (uint.Z pos))) with (uint.nat pos) by word. done. }
        iIntros "Hsl_children".
        iSpecialize ("Hchildren" with "[//]").
        iDestruct (big_sepL2_length with "Hchildren") as %Hlen.

        iExists (<[ _ := _ ]> children), (Interior (replicate (uint.nat (W64 256)) None)).
        iSplitL.
        2:{ iPureIntro.
            split_and!.
            - apply list_lookup_insert. word.
            - eapply eq_tree_map_new_interior; try done. word.
            - apply has_tree_height_interior; try done.
              rewrite /full_height. word.
        }

        iApply own_node_except_unfold.
        repeat iExists _.
        iFrame "Hptr_hash Hptr_children ∗".
        iFrame "#".
        rewrite length_insert. iFrame "%".
        replace (uint.nat (W64 (uint.Z pos))) with (uint.nat pos) by word.
        iDestruct (big_sepL2_insert_acc with "Hchildren") as "[_ Hchildren]".
        { done. }
        { done. }
        iApply "Hchildren".
        iNext.
        iDestruct (struct_fields_split with "Hnode") as "Hnode".
        iNamed "Hnode".
        iFrame.
        iApply own_node_except_unfold.
        repeat iExists _.
        rewrite zero_slice_val.
        Opaque replicate.
        iFrame "∗".
        Transparent replicate.
        iDestruct (own_slice_small_nil) as "$"; first done.
        erewrite drop_S; last done.
        rewrite decide_True //.
        iFrame "#".
        rewrite length_replicate.
        iSplitR; first done.
        iApply big_sepL2_replicate_r.
        { rewrite length_replicate //. }
        iApply big_sepL_impl.
        { by iApply big_sepL_emp. }
        iModIntro. iIntros.
        rewrite lookup_replicate in H0.
        naive_solver.
      }
    }
    iIntros (unused) "HifInv".
    wp_pures.
    clear unused.
    clear Hheight Hsubmap sub_tree.
    iNamed "HifInv".

    iDestruct (own_node_except_unfold with "Hnode") as "Hnode".
    iNamed "Hnode".
    iNamed "Hchildren".
    wp_loadField.
    iDestruct (big_sepL2_length with "Hchildren") as %Hlen.
    iDestruct (big_sepL2_lookup_1_some with "Hchildren") as %[child_ptr Hptr_children_lookup].
    { done. }
    wp_apply (wp_SliceGet with "[$Hsl_children]").
    { iPureIntro. by replace (uint.nat (W64 (uint.Z pos))) with (uint.nat pos) by word. }
    iIntros "Hsl_children".
    wp_load.
    iDestruct (own_slice_split with "[$Hinteriors $Hinteriors_cap]") as "Hinteriors".
    wp_apply (wp_SliceAppend (V:=loc) with "[$]").
    iIntros (newInteriors_sl) "Hinteriors".

    iDestruct (big_sepL2_delete _ _ _ (uint.nat pos) with "Hchildren") as "[Hchild Hchildren]";
      try eassumption.

    wp_store.
    clear interiors_sl.

    iModIntro.
    iApply "HΦ'".
    iFrame "HpathIdx".
    repeat iExists _.
    iFrame.
    iSplitR.
    { rewrite last_snoc //. }
    replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
    iSplitL "Hchild".
    {
      erewrite drop_S; last done.
      rewrite decide_True //.
    }
    repeat (iSplitR; try iPureIntro).
    { rewrite length_app /=. word. }
    { erewrite take_S_r; last done. by eapply eq_tree_map_child. }
    {
      rewrite Nat.sub_succ_r.
      destruct (uint.nat full_height - (uint.nat i))%nat.
      { exfalso. done. }
      simpl in *.
      eapply Forall_lookup in Hheight; last done.
      rewrite /= // in Hheight.
    }

    iIntros (?) "Hnode' %Heq' %Hheight'".
    rewrite removelast_app // /= app_nil_r.
    replace (interiors) with (removelast interiors ++ [currNode_ptr]).
    2:{
      rewrite removelast_firstn_len.
      rewrite Hinteriors_length /=.
      rewrite -take_S_r.
      2:{ rewrite last_lookup Hinteriors_length /= // in Hinteriors_last. }
      rewrite take_ge //.
      lia.
    }
    rewrite foldl_snoc removelast_app //= app_nil_r.
    iExists ((<[uint.nat pos := Some (Interior children') ]> children)).
    iSplitR "Hrest".
    {
      iApply own_node_except_unfold.
      repeat iExists _.
      iFrame "Hptr_hash Hptr_children ∗".
      iSplitR; first done.
      iSplitR; first done.
      iSplitR; first done.
      iSplitR; first done.
      replace (uint.nat (W64 (uint.Z pos))) with (uint.nat pos) by word.
      simpl.
      iApply (big_sepL2_delete _ _ _ (uint.nat pos)).
      { rewrite list_lookup_insert //. word. }
      { done. }
      simpl.
      iFrame "Hnode'".
      iDestruct (big_sepL2_insert_acc _ _ _ (uint.nat pos) with "Hchildren") as "[_ Hchildren]".
      { done. }
      { done. }
      iSpecialize ("Hchildren" $! (Some _) child_ptr).
      iEval (rewrite (list_insert_id ptr_children); last done) in "Hchildren".
      iSpecialize ("Hchildren" with "[]").
      { rewrite decide_True //. }
      iApply (big_sepL2_impl with "Hchildren").
      iIntros "!# * %% H".
      destruct decide; first done.
      destruct x1.
      { erewrite drop_S; last done. rewrite decide_False //. }
      { done. }
    }
    iIntros "Htree".
    iApply ("Hrest" with "[$]").
    {
      iPureIntro.
      intros k.
      replace (uint.nat (w64_word_instance.(word.add) i (W64 1))) with (S (uint.nat i)) in Heq', Hheight' by word.
      (* replace (uint.nat full_height - _)%nat with (n) in Hheight' by word. *)
      set (id_rest:=(drop (S (uint.nat i)) id)) in *.
      destruct k.
      - (* If k is empty, then lookup in sub_map should be None. *)
        simpl.
        specialize (Hsubmap []).
        simpl in Hsubmap.
        rewrite lookup_insert_ne //.
        rewrite app_nil_r.
        intros Hbad.
        apply (f_equal length) in Hbad.
        rewrite length_take in Hbad.
        word.
      - assert (id = (take (uint.nat i) id) ++ pos :: id_rest) as Hid.
        {
          rewrite <- (take_drop (uint.nat i)) at 1.
          f_equal.
          subst id_rest.
          rewrite -drop_S //.
        }
        rewrite -> Hid at 2.
        destruct (decide (w = pos)) as [Hw|Hw].
        + (* k starts with pos *)
          subst pos.
          destruct (decide (id_rest = k)) as [Hrest|Hrest].
          * subst k.
            simpl in *.
            rewrite list_lookup_insert //.
            2:{ word. }
            specialize (Hsubmap (w :: id_rest)).
            simpl in Hsubmap.
            unfold id_rest.
            rewrite -drop_S //.
            rewrite take_drop.
            rewrite lookup_insert.
            specialize (Heq' id_rest).
            rewrite take_drop lookup_insert in Heq'.
            done.
          * rewrite lookup_insert_ne //.
            2:{ naive_solver. }
            simpl.
            rewrite list_lookup_insert //.
            2:{ word. }
            specialize (Hsubmap (w :: k)).
            specialize (Heq' k).
            erewrite take_S_r in Heq'; last done.
            rewrite -app_assoc /= in Heq'.
            rewrite -> Hid in Heq' at 2.
            rewrite /= Hchild_lookup in Hsubmap.
            rewrite lookup_insert_ne // in Heq'.
            naive_solver.
        + rewrite lookup_insert_ne /=.
          2:{ naive_solver. }
          rewrite list_lookup_insert_ne //.
          2:{ intros ?. apply Hw. word. }
          specialize (Hsubmap (w :: k)).
          simpl in Hsubmap. done.
    }
    {
      iPureIntro.
      simpl.
      rewrite Nat.sub_succ_r in Hheight'.
      destruct (uint.nat full_height - (uint.nat i))%nat; first by exfalso.
      by apply Forall_insert.
    }
  }
  iIntros "[Hinv Hdepth]".
  wp_pures.
  iNamed "Hinv".
  wp_load.
  iDestruct (own_slice_split_1 with "Hinteriors") as "[Hinteriors Hinteriors_cap]".
  wp_apply (wp_SliceGet with "[$Hinteriors]").
  {
    iPureIntro.
    rewrite last_lookup in Hinteriors_last.
    rewrite Hinteriors_length /= in Hinteriors_last.
    done.
  }
  iIntros "Hinteriors".
  wp_pures.
  opose proof (list_lookup_lt id (uint.nat (word.sub (W64 32) (W64 1))) ltac:(word)) as [pos Hpos].
  wp_apply (wp_SliceGet with "[$Hid //]").
  iIntros "Hid".
  wp_pures.
  rewrite zero_slice_val.
  wp_apply (wp_compLeafNodeHash with "[$Hval]").
  iIntros "* (Hval_in & Hhash_sl & His_leaf_hash)".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (leaf_ptr) "Hleaf".
  Opaque node.
  iDestruct (own_node_except_unfold with "Hnode") as "Hnode".
  iNamed "Hnode".
  destruct sub_tree as [| | children]; try done.
  wp_loadField.
  iNamed "Hchildren".
  opose proof (list_lookup_lt ptr_children (uint.nat pos) ltac:(word)) as [child Hchild].

  wp_apply (wp_SliceSet with "[$Hsl_children]").
  { iPureIntro. replace (uint.nat (W64 (uint.Z pos))) with (uint.nat pos) by word. done. }
  iIntros "Hsl_children".
  wp_pures.
  wp_apply wp_NewSliceWithCap.
  { word. }
  iIntros (?) "HloopBuf".
  wp_apply wp_ref_to; [val_ty|].
  iIntros (loopBuf_ptr) "HloopBuf_ptr".
  wp_pures.
  wp_apply wp_ref_to; [val_ty|].
  iClear "Hdepth".
  clear depth_ptr.
  iIntros (depth_ptr) "Hdepth_ptr".
  wp_pures.

  clear loopInv.
  iMod (own_slice_small_persist with "Hval_in") as "Hval_in".
  iMod (own_slice_small_persist with "Hhash_sl") as "Hhash_sl".
  iAssert (
      ∃ (depth : w64) current_children loopBuf_sl,
        "Hdepth" ∷ depth_ptr ↦[uint64T] #depth ∗
        "HloopBuf_ptr" ∷ loopBuf_ptr ↦[slice.T byteT] (slice_val loopBuf_sl) ∗
        "HloopBuf" ∷ own_slice loopBuf_sl byteT (DfracOwn 1) ([] : list w8) ∗
        "%Hdepth_ge" ∷ ⌜ uint.nat depth ≥ 0 ⌝ ∗
        if decide (uint.nat depth = 0)%nat then
          "HcurrNode" ∷ own_node_except None root (Interior current_children) ∗
          "%Hmap_eq" ∷ ⌜ eq_tree_map (Interior current_children) [] (<[id:=val]> entries) ⌝ ∗
          "%Hheight" ∷ ⌜ has_tree_height (Interior current_children) (uint.nat full_height) ⌝
        else
          ∃ current_ptr,
          "HcurrNode" ∷ own_node_except (Some []) current_ptr (Interior current_children) ∗
          "%HinteriorLookup" ∷ ⌜ interiors !! ((uint.nat depth) - 1)%nat = Some current_ptr ⌝ ∗
          "Hrest" ∷ (own_node_except None current_ptr (Interior current_children) -∗
                     foldl
                       (λ (P : iPropI Σ) (node_ptr : loc),
                          ∃ children, own_node_except (Some []) node_ptr (Interior children) ∗
                                      (own_node_except None node_ptr (Interior children) -∗ P))
                       (∃ children', own_node_except None root (Interior children') ∗
                                     ⌜ eq_tree_map (Interior children') [] (<[id:=val]> entries) ⌝ ∗
                                     ⌜ has_tree_height (Interior children') (uint.nat full_height) ⌝)
                       (take (uint.nat depth - 1)%nat interiors)
            )
    )%I with "[Hdepth_ptr His_leaf_hash Hleaf Hptr_hash Hrest Hval_in Hhash_sl
              Hptr_val Hptr_children Hchildren Hsl_children HloopBuf_ptr HloopBuf]" as "HloopInv".
  {
    iFrame "Hdepth_ptr".
    iFrame.
    iExists (<[ uint.nat pos := Some $ Leaf val ]> children).
    iDestruct (big_sepL2_length with "Hchildren") as %Hchildren_length.
    iSplitR.
    { word. }
    erewrite decide_False; last word.
    iExists currNode_ptr.
    iSplitR "Hrest".
    {
      iApply own_node_except_unfold.
      iFreeze "Hval_in Hhash_sl".
      iFrame "∗#%".
      iThaw "Hval_in Hhash_sl".
      rewrite length_insert. iFrame "%".
      replace (uint.nat (W64 (uint.Z pos))) with (uint.nat pos) by word.
      iApply (big_sepL2_delete _ _ _ (uint.nat pos)).
      { apply list_lookup_insert. word. }
      { apply list_lookup_insert. word. }
      iSplitL "Hleaf Hhash_sl His_leaf_hash Hval_in".
      { (* prove [own_node_except] for leaf *)
        iDestruct (struct_fields_split with "Hleaf") as "H".
        iNamed "H". iNext.
        iApply own_node_except_unfold.
        iFrame "∗#".
        iDestruct (own_slice_small_nil) as "$"; done.
      }
      iDestruct (big_sepL2_lookup_2_some with "Hchildren") as %[? ?].
      { done. }

      (* XXX: this is like re-establishing Hrest in the loop *)
      iDestruct (big_sepL2_delete _ _ _ (uint.nat pos) with "Hchildren") as "[_ Hchildren]";
        try eassumption.
      iDestruct (big_sepL2_insert_acc _ _ _ (uint.nat pos) with "Hchildren") as "[_ Hchildren]";
        try eassumption.
      iSpecialize ("Hchildren" $! (Some (Leaf val)) leaf_ptr with "[]").
      { rewrite decide_True //. }
      iApply (big_sepL2_impl with "Hchildren").
      iIntros "!# * %% H".
      destruct decide; first done.
      destruct x1.
      { erewrite drop_S; last done. rewrite decide_False //. }
      { done. }
    }
    iSplitR.
    { iPureIntro. rewrite -Hinteriors_last last_lookup.
      f_equal. rewrite Hinteriors_length. word. }
    iIntros "Ht".
    rewrite removelast_firstn_len /=.
    iSpecialize ("Hrest" with "[$] [] []").
    {
      iPureIntro.
      apply (eq_tree_map_insert_leaf _ pos _ _ val) in Hsubmap.
      2:{ word. }
      2:{
        replace (uint.nat _ - _)%nat with (S O) in Hheight0.
        2:{ unfold full_height. word. }
        simpl in Hheight0.
        opose proof (list_lookup_lt children (uint.nat pos) ltac:(word)) as [? Hchild'].
        rewrite Hchild'.
        eapply Forall_lookup in Hheight0; last done.
        destruct x as [[]|]; try done.
      }
      erewrite <- take_S_r in Hsubmap.
      2:{ done. }
      rewrite -> (take_ge _ (S _)) in Hsubmap.
      2:{ word. }
      done.
    }
    {
      iPureIntro.
      replace (uint.nat _ - _)%nat with (S O).
      2:{ unfold full_height. word. }
      simpl. by apply Forall_insert.
    }
    iExactEq "Hrest".
    repeat f_equal.
    rewrite Hinteriors_length.
    word.
  }
  wp_forBreak_cond.

  iNamed "HloopInv".
  wp_load.
  wp_pures.
  wp_if_destruct.
  { (* run the loop body *)
    erewrite decide_False; last word.
    iNamed "HloopInv".
    wp_pures. wp_load. wp_pures.
    wp_load.
    wp_apply (wp_SliceGet with "[$Hinteriors]").
    { iPureIntro. erewrite <- HinteriorLookup. f_equal. word. }
    iIntros "Hinteriors".
    wp_pures.
    wp_load.
    wp_loadField.
    wp_apply (wp_updInteriorHash with "[$HloopBuf $His_ctx $HcurrNode]").
    iIntros "* [Hsl HcurrNode]".
    wp_store.
    wp_load.
    wp_apply (wp_SliceTake_full with "Hsl").
    { word. }
    iIntros "Hsl". rewrite take_0.
    wp_store.
    wp_load.
    wp_store.
    iLeft. iModIntro.
    iSplitR; first done.
    iSpecialize ("Hrest" with "HcurrNode").
    replace (uint.nat (word.sub depth (W64 1))) with (uint.nat depth - 1)%nat by word.
    destruct (uint.nat depth - 1)%nat eqn:Hdepth.
    {
      iDestruct "Hrest" as (?) "(Hnode & % & %)".
      iFrame.
      repeat iExists _.
      iSplitR; first word.
      erewrite decide_True; last word.
      iFrame "Hnode %".
    }
    {
      opose proof (list_lookup_lt interiors n _) as [next_ptr Hnext_lookup].
      { apply lookup_lt_Some in HinteriorLookup. lia. }
      erewrite take_S_r; last done.
      rewrite foldl_snoc.
      iDestruct "Hrest" as (?) "[Hnode Hrest]".
      iFrame.
      repeat iExists _.
      iSplitR; first word.
      erewrite decide_False; last word.
      simpl.
      replace (uint.nat (word.sub _ _) - 1)%nat with (n) by word.
      iFrame "∗%".
    }
  }
  (* done with loop *)
  iRight.
  iModIntro; iSplitR; first done.
  wp_pures.
  wp_loadField.
  wp_loadField.
  erewrite decide_True; last word.
  iNamed "HloopInv".
  wp_apply (wp_context__getHash with "[$HcurrNode $His_ctx]").
  iClear "His_hash".
  iIntros "* (Hnode & #Hhash_sl & #His_hash)".
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_context__getProof with "[$His_ctx $Hnode $Hid]").
  { done. }
  { word. }
  { done. }
  iIntros "* (Hnode & Hid & Hproof & His_proof)".
  wp_pures.
  destruct (decide (root = null)); subst.
  { by iDestruct (own_node_except_not_null with "Hnode") as %?. }
  iApply "HΦ".
  iFrame.
  (*
  iSplitR; first done.
  iDestruct (own_slice_to_small with "Hproof") as "Hproof".
  iMod (own_slice_small_persist with "Hproof") as "Hproof".
  iModIntro.
  rewrite decide_False //.
  iFrame "His_ctx".
  iFrame "∗%".
  iFrame "∗#%".
  rewrite lookup_insert.
  iApply "His_proof".
  { specialize (Hmap_eq id).
    done. }
  *)
Admitted.

Lemma wp_Tree__Get ptr_tr entries sl_id id d0 :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id
  }}}
  Tree__Get #ptr_tr (slice_val sl_id)
  {{{
    sl_val sl_dig (proofTy : bool) sl_proof (err : bool),
    RET (slice_val sl_val, slice_val sl_dig, #proofTy, slice_val sl_proof, #err);
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "%Hgenie" ∷ ⌜ length id = hash_len ↔ err = false ⌝ ∗
    "Herr" ∷ (if err then True else
      ∃ val dig proof,
      "#Hsl_val" ∷ own_slice_small sl_val byteT DfracDiscarded val ∗
      "#Hsl_dig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
      "#Hsl_proof" ∷ own_slice_small sl_proof byteT DfracDiscarded proof ∗
      "#His_dig" ∷ is_dig entries dig ∗
      "#His_proof" ∷ is_merkle_proof proof id (if proofTy then Some val else None) dig)
  }}}.
Proof. Admitted.

(*
Lemma wp_pathProof_check ptr_proof proof val :
  {{{
    "Hproof" ∷ pathProof.own ptr_proof proof ∗
    let node := match val with
    | None => Empty
    | Some val' => Leaf val'
    end in
    "Hhash" ∷ is_node_hash node proof.(pathProof.nodeHash)
  }}}
  pathProof__check #ptr_proof
  {{{
    (err : bool), RET #err;
    if negb err then
      "Hpath" ∷ is_merkle_entry proof.(pathProof.id) val proof.(pathProof.digest)
    else True%I
  }}}.
Proof.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hproof".
  rewrite /pathProof__check.
  wp_apply wp_ref_to; [val_ty|];
    iIntros (ptr_err) "Hptr_err".
  wp_loadField.
  wp_apply wp_ref_to; [val_ty|]. iIntros (ptr_currHash) "HcurrHash".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_apply wp_ref_to; [val_ty|]; iIntros (ptr_loopIdx) "HloopIdx".
  iDestruct ("HchildHashes") as (?) "H"; iNamed "H".
  iMod (own_slice_small_persist with "HnodeHash") as "#HnodeHash".
  iDestruct (big_sepL2_length with "Hsep_dim0") as "%Hlen_childHashes".
  iDestruct (own_slice_small_sz with "Hsl_dim0") as "%Hlen_list_dim0".

  (* Entering the main loop. *)
  set for_inv :=
    (λ loopIdx, ∃ sl_currHash currHash (err : bool),
      "Hid" ∷ own_slice_small sl_id byteT (DfracOwn 1) proof.(pathProof.id) ∗
      "Hptr_id" ∷ ptr_proof ↦[pathProof :: "id"] sl_id ∗
      "Hptr_childHashes" ∷ ptr_proof ↦[pathProof :: "childHashes"] sl_childHashes ∗
      "#Hsl_currHash" ∷ own_slice_small sl_currHash byteT DfracDiscarded currHash ∗
      "Hptr_currHash" ∷ ptr_currHash ↦[slice.T byteT] sl_currHash ∗
      "Hptr_err" ∷ ptr_err ↦[boolT] #err ∗
      "Herr_pred" ∷ if negb err then
        "Hpath_val" ∷ is_merkle_entry
          (drop (length proof.(pathProof.id) - (Z.to_nat (word.unsigned loopIdx)))
          proof.(pathProof.id)) val currHash
      else True)%I : w64 → iProp Σ.
  wp_apply (wp_forUpto for_inv with "[] [$Hid $Hptr_id $Hptr_childHashes $HloopIdx $HcurrHash $HnodeHash $Hptr_err Hhash]"); [word|..].
  2: {
    assert ((length proof.(pathProof.id) - 0%nat)%nat = length proof.(pathProof.id)) as H by word;
      iEval (rewrite H); clear H.
    iEval (rewrite drop_all).
    iFrame.
    destruct val; done.
  }
  {
    iEval (rewrite /for_inv); clear for_inv.
    iIntros (loopIdx Φ2) "!> (Hinv & HloopIdx & %HloopBound) HΦ2";
      iNamed "Hinv".
    wp_load.
    wp_apply (wp_loadField with "[$Hptr_childHashes]");
      iIntros "Hptr_childHashes".

    (* Note: move all the sep fetches into one block, like this. *)
    (* TODO: change all uint out of backwords compat thing *)
    assert (∃ (sl_dim1' : Slice.t),
      list_dim0 !! uint.nat (length list_dim0 - 1 - uint.nat loopIdx) =
      Some sl_dim1') as [sl_dim1' Hlook_sl_dim1'].
    { apply lookup_lt_is_Some. word. }
    iDestruct (big_sepL2_lookup_1_some with "Hsep_dim0") as %[obj_dim1' Hlook_obj_dim1']; [done|].
    iDestruct (big_sepL2_lookup with "Hsep_dim0") as (list_dim1') "H";
      [done..|]; iNamed "H".
    iDestruct (own_slice_small_sz with "Hsl_dim1") as "%Hlen_list_dim1'".
    iDestruct (big_sepL2_length with "Hsep_dim1") as "%Hlen_obj_dim1'".
    iDestruct (own_slice_small_sz with "Hid") as "%Hlen_id".

    (* Rewrite this early since it appears in multiple sub-terms. *)
    replace (word.sub (word.sub sl_childHashes.(Slice.sz) 1) loopIdx) with
      (W64 (length list_dim0 - 1 - uint.nat loopIdx)) by word.

    wp_apply (wp_SliceGet with "[$Hsl_dim0]"); [done|]; iIntros "_".
    wp_apply wp_slice_len.

    wp_if_destruct.
    { wp_store. iApply "HΦ2". by iFrame "#∗". }
    replace (word.sub 256 1) with (W64 255) in Heqb;
      [|word]; rename Heqb into Hsz_sl_dim1'.
    wp_apply (wp_isValidHashSl with "[$Hsl_dim1 $Hsep_dim1]").
      iIntros (ok) "H".
    wp_if_destruct.
    { wp_store. iApply "HΦ2". by iFrame "#∗". }
    iSimpl in "H"; iNamed "H"; rename Hlen into Hhash_len_obj_dim1'.

    wp_apply (wp_loadField with "[$Hptr_id]");
      iIntros "Hptr_id".
    assert (∃ (pos : w8),
      proof.(pathProof.id) !! uint.nat (length list_dim0 - 1 - uint.nat loopIdx) =
      Some pos) as [pos Hlook_pos].
    { apply lookup_lt_is_Some. word. }
    wp_apply (wp_SliceGet with "[$Hid]"); [done|];
      iIntros "Hid".

    (* TODO: word should know this. *)
    assert (length list_dim1' = 255%nat) as H255_list_dim1'.
    { rewrite Hlen_list_dim1'. rewrite Hsz_sl_dim1'. word. }
    (* Note: this slows down word for some reason. *)
    pose proof (word.unsigned_range pos) as Hpos_bound.

    (* The complicated slice splitting logic. *)
    iDestruct (own_slice_small_wf with "Hsl_dim1") as "%Hwf_sl_dim1".
    iDestruct (slice_small_split _ (W64 (word.unsigned pos)) with "Hsl_dim1") as "[Hsl_before Hsl_after]".
    (* TODO: word should know this. *)
    { rewrite u8_to_u64_Z. lia. }
    wp_apply wp_SliceTake.
    { rewrite u8_to_u64_Z. lia. }
    wp_apply wp_SliceSkip.
    { rewrite u8_to_u64_Z. lia. }
    iEval (rewrite u8_to_u64_Z) in "Hsl_before".
    iEval (rewrite u8_to_u64_Z) in "Hsl_after".

    wp_apply wp_ref_of_zero; [done|];
      iIntros (ptr_hr) "Hptr_hr".
    iEval (rewrite zero_slice_val) in "Hptr_hr".
    iDestruct (own_slice_small_nil byteT (DfracOwn 1) (Slice.nil)) as "Hnil"; [done|].
    wp_apply (wp_HasherWriteSl with "[$Hptr_hr $Hnil $Hsl_before]").
    {
      iApply big_sepL2_prefix.
      4: iFrame "#".
      1: apply prefix_take.
      1: apply (prefix_take _ (uint.nat pos)).
      { do 2 rewrite length_take. lia. }
    }
    iIntros (sl_hr) "H"; iNamed "H".
    wp_load.
    wp_apply (wp_HasherWrite with "[$Hptr_hr $Hhr $Hsl_currHash]");
      clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_apply (wp_HasherWriteSl with "[$Hptr_hr $Hhr $Hsl_after]").
    {
      iApply big_sepL2_suffix.
      4: iFrame "#".
      1: apply suffix_drop.
      1: apply (suffix_drop _ (uint.nat pos)) .
      { do 2 rewrite length_drop. lia. }
    }
    clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_apply wp_SliceSingleton; [val_ty|];
      iIntros (sl_tag) "H";
      iDestruct (slice.own_slice_to_small with "H") as "Hsl_tag".
    iAssert (own_slice_small _ _ _ [W8 2]) with "Hsl_tag" as "Hsl_tag".
    iMod (own_slice_small_persist with "Hsl_tag") as "#Hsl_tag".
    wp_apply (wp_HasherWrite with "[$Hptr_hr $Hhr $Hsl_tag]").
    clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_load.
    wp_apply (wp_HasherSumNil with "Hhr");
      iIntros (sl_hash hash) "H"; iNamed "H".
    wp_store.
    iMod (own_slice_small_persist with "Hsl_hash") as "#Hsl_hash".
    iClear (sl_tag) "HnodeHash Hsl_before Hsl_after Hnil Hsl_tag".

    (* Done with code, now re-establish loop inv. *)

    destruct err; iNamed "Herr_pred"; iApply "HΦ2"; iFrame "#∗"; [done|].
    rewrite /is_merkle_entry.
    iDestruct "Herr_pred" as "[Htr_hash %Htr_contains]".
    iExists (Interior (
      ((λ h, Cut h) <$> (take (uint.nat pos) obj_dim1')) ++
      [tr] ++
      ((λ h, Cut h) <$> (drop (uint.nat pos) obj_dim1')))).
    iIntros "!>".
    iSplit.
    {
      iExists (
        (take (uint.nat pos) obj_dim1') ++
        [currHash] ++
        (drop (uint.nat pos) obj_dim1')).
      iSplit.
      {
        iEval (rewrite fmap_app).
        iApply big_sepL2_app.
        {
          iEval (rewrite <-list_fmap_compose).
          iApply big_sepL2_fmap_l.
          iApply big_sepL_sepL2_diag.
          iApply big_sepL_take.
          iPureIntro.
          naive_solver.
        }
        iEval (rewrite fmap_cons).
        iApply big_sepL2_cons.
        iFrame.
        {
          iEval (rewrite <-list_fmap_compose).
          iApply big_sepL2_fmap_l.
          iApply big_sepL_sepL2_diag.
          iApply (big_sepL_drop (λ _ _, _)).
          iPureIntro.
          naive_solver.
        }
      }
      iEval (do 2 rewrite concat_app).
      by list_simplifier.
    }
    iPureIntro.
    clear Hpos_bound.
    rewrite (drop_S _ pos _ _).
    2: { rewrite <-Hlook_pos. f_equal. word. }
    (* TODO: is there a good way of extracting this goal automatically? *)
    replace (S (length proof.(pathProof.id) - uint.nat (word.add loopIdx 1))) with
      ((length proof.(pathProof.id) - uint.nat loopIdx)%nat) by word.
    exists tr.
    split; [|done].
    rewrite (lookup_app_r _ _ _ _).
    2: {
      rewrite length_fmap.
      rewrite (length_take_le _ _ _); [done|].
      pose proof (word.unsigned_range pos) as Hpos_bound.
      lia.
    }
    rewrite length_fmap.
    rewrite (length_take_le _ _ _).
    2: { pose proof (word.unsigned_range pos) as Hpos_bound. lia. }
    replace ((uint.nat pos - uint.nat pos)%nat) with (0%nat) by lia.
    naive_solver.
  }

  (* Last chunk of code after for loop. *)
  iEval (rewrite /for_inv); clear for_inv.
  iIntros "[H _]"; iNamed "H".
  wp_load.
  wp_if_destruct; [by iApply "HΦ"|]; clear err Heqb.
  iSimpl in "Herr_pred"; iNamed "Herr_pred".
  wp_apply (wp_loadField with "Hptr_digest");
    iIntros "Hptr_digest".
  wp_load.
  (* TODO: framing doesn't work here. $Hsl_currHash frames this persis thing twice. *)
  wp_apply (wp_BytesEqual with "[Hdigest]"); [iFrame "#∗"|];
    iIntros "[_ Hdigest]".
  wp_if_destruct; [by iApply "HΦ"|]; rename Heqb into Heq_currHash.
  iEval (replace ((length proof.(pathProof.id) - uint.nat sl_childHashes.(Slice.sz))%nat)
    with (0%nat) by word) in "Hpath_val".
  iEval (rewrite drop_0 Heq_currHash) in "Hpath_val".
  by iApply "HΦ".
Qed. *)

Definition wp_CheckProof sl_id sl_val sl_dig (proofTy : bool) sl_proof proof (id val dig : list w8)
  dq0 dq1 dq2 dq3 :
  {{{
    "Hproof" ∷ own_slice sl_proof byteT dq0 proof ∗
    "Hid" ∷ own_slice_small sl_id byteT dq1 id ∗
    "Hval" ∷ own_slice_small sl_val byteT dq2 val ∗
    "Hdig" ∷ own_slice_small sl_dig byteT dq3 dig
  }}}
  CheckProof #proofTy (slice_val sl_proof) (slice_val sl_id) (slice_val sl_val) (slice_val sl_dig)
  {{{
    (err : bool), RET #err;
    "Hproof" ∷ own_slice sl_proof byteT dq0 proof ∗
    "Hid" ∷ own_slice_small sl_id byteT dq1 id ∗
    "Hval" ∷ own_slice_small sl_val byteT dq2 val ∗
    "Hdig" ∷ own_slice_small sl_dig byteT dq3 dig ∗
    let expected_val := (if proofTy then Some val else None) in
    "Hgenie" ∷ (if err then True else is_merkle_proof proof id expected_val dig)
  }}}.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_rec.
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  wp_if_destruct.
  { iApply "HΦ". by iFrame. }
  wp_pures.
  wp_if_destruct.
  { iApply "HΦ". by iFrame. }
  wp_apply wp_slice_len. wp_pures.
  wp_if_destruct.
  { iApply "HΦ". by iFrame. }
Admitted.

Lemma wp_NewTree :
  {{{ True }}}
    NewTree #()
  {{{ m, RET #m; own_merkle m ∅ }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_rec.
  wp_apply wp_newCtx.
  iIntros "* Hctx".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H".
  iNamed "H".
  iApply "HΦ".
  repeat iExists _.
  iFrame. simpl. done.
Qed.

End wps.
