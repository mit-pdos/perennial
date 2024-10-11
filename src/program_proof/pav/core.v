From Perennial.Helpers Require Import Integers ListLen.

From stdpp Require Import ssreflect prelude gmap.

Notation uid_ty := w64 (only parsing).
(* TODO: make ver_ty, epoch_ty work for w64. *)
Notation ver_ty := nat (only parsing).
Notation epoch_ty := nat (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation map_label_ty := (uid_ty * ver_ty)%type (only parsing).
Notation map_val_ty := (epoch_ty * pk_ty)%type (only parsing).
Notation map_ty := (gmap map_label_ty map_val_ty) (only parsing).
(* sub-maps are useful for helping us state non-existence of
keys in a way that they carry across map subsets. *)
Notation submap_ty := (gmap map_label_ty (option map_val_ty)) (only parsing).

Section msv.

(* maximum sequence of versions. *)

Definition msv_aux (m : map_ty) uid vals :=
  (∀ i, i < length vals → m !! (uid, i) = vals !! i).

Definition msv m uid vals :=
  msv_aux m uid vals ∧
  m !! (uid, (length vals)) = None.

(* TODO: upstream. *)
Lemma lookup_snoc {A} (l : list A) (x : A) :
  (l ++ [x]) !! (length l) = Some x.
Proof. by opose proof (proj2 (lookup_snoc_Some x l (length l) x) _) as H; [naive_solver|]. Qed.

Lemma msv_aux_snoc {m uid l x} :
  msv_aux m uid (l ++ [x]) →
  msv_aux m uid l ∧ m !! (uid, length l) = Some x.
Proof.
  intros HM. split.
  - intros i ?. ospecialize (HM i _). { rewrite length_app/=. lia. }
    by rewrite lookup_app_l in HM; [|lia].
  - ospecialize (HM (length l) _). { rewrite length_app/=. lia. }
    by rewrite lookup_snoc in HM.
Qed.

Lemma msv_aux_agree {m uid vals0 vals1} :
  msv_aux m uid vals0 →
  msv_aux m uid vals1 →
  length vals0 = length vals1 →
  vals0 = vals1.
Proof.
  revert vals1. induction vals0 as [|x0 l0 IH] using rev_ind;
    destruct vals1 as [|x1 l1 _] using rev_ind.
  - done.
  - rewrite length_app/=. lia.
  - rewrite length_app/=. lia.
  - rewrite !length_app/=. intros H0 H1 ?.
    apply msv_aux_snoc in H0 as [H0 Hx0]. apply msv_aux_snoc in H1 as [H1 Hx1].
    assert (length l0 = length l1) as HT by lia. rewrite HT in Hx0. clear HT.
    simplify_map_eq/=. ospecialize (IH l1 _ _ _); [done..|lia|]. naive_solver.
Qed.

Lemma msv_len_agree_aux {m uid vals0 vals1} :
  msv m uid vals0 →
  msv m uid vals1 →
  length vals0 < length vals1 →
  False.
Proof.
  intros HM0 HM1 ?. destruct HM0 as [_ HM0]. destruct HM1 as [HM1 _].
  ospecialize (HM1 (length vals0) _); [lia|].
  opose proof (lookup_lt_is_Some_2 vals1 (length vals0) _) as [? Hsome]; [lia|].
  rewrite Hsome in HM1. naive_solver.
Qed.

Lemma msv_len_agree {m uid vals0 vals1} :
  msv m uid vals0 →
  msv m uid vals1 →
  length vals0 = length vals1.
Proof.
  intros ??.
  destruct (decide (length vals0 = length vals1)) as [?|?]; [done|].
  exfalso. destruct (decide (length vals0 < length vals1)) as [?|?].
  - eapply (msv_len_agree_aux (vals0:=vals0) (vals1:=vals1)); [done..|lia].
  - eapply (msv_len_agree_aux (vals0:=vals1) (vals1:=vals0)); [done..|lia].
Qed.

Lemma msv_agree {m uid vals0 vals1} :
  msv m uid vals0 →
  msv m uid vals1 →
  vals0 = vals1.
Proof.
  intros HM0 HM1. eapply msv_aux_agree.
  - by destruct HM0 as [? _].
  - by destruct HM1 as [? _].
  - by eapply msv_len_agree.
Qed.

End msv.

Section ts_msv.

(* timeseries and its interaction with msv. *)

(* lookup_weaken_None and lookup_weaken are useful with this. *)
Definition maps_mono (ms : list map_ty) :=
  ∀ i j mi mj,
  ms !! i = Some mi →
  ms !! j = Some mj →
  i ≤ j →
  mi ⊆ mj.

(* note: auditor allows entry to be added after expected.
but originating client ensures that doesn't happen. *)
Definition maps_epoch_ok (ms : list map_ty) :=
  ∀ ep m_ep (k : uid_ty * ver_ty) ep' (pk : pk_ty),
  ms !! ep = Some m_ep →
  m_ep !! k = Some (ep', pk) →
  (* can't have new entries in an old epoch. *)
  ep' ≤ ep.

Definition adtr_inv ms := maps_mono ms ∧ maps_epoch_ok ms.

Record ts_ty :=
  mk_ts {
    entries: list (epoch_ty * pk_ty);
    bound: epoch_ty;
  }.

(* ts_get fetches the seq of pk's through this ep. *)
Definition ts_get ts ep := filter (λ x, x.1 ≤ ep) ts.(entries).

Definition ts_epoch_mono (ts : ts_ty) :=
  ∀ i j ep_i pk_i ep_j pk_j,
  ts.(entries) !! i = Some (ep_i, pk_i) →
  ts.(entries) !! j = Some (ep_j, pk_j) →
  i < j →
  ep_i < ep_j.

Definition ts_bound_ok0 (ts : ts_ty) :=
  ∀ i ep pk,
  ts.(entries) !! i = Some (ep, pk) →
  ep ≤ ts.(bound).

Definition ts_bound_ok1 (ts : ts_ty) (ms : list map_ty) :=
  ts.(bound) < length ms.

Definition ts_entry_know (ts : ts_ty) (ms : list map_ty) uid :=
  ∀ ver ep pk m,
  ts.(entries) !! ver = Some (ep, pk) →
  ms !! ep = Some m →
  m !! (uid, ver) = Some (ep, pk) ∧ m !! (uid, S ver) = None.

Definition ts_bound_know (ts : ts_ty) (ms : list map_ty) uid :=
  ∀ m,
  ms !! ts.(bound) = Some m →
  m !! (uid, length ts.(entries)) = None.

(* maintained by client. *)
Definition ts_inv ts ms uid :=
  ts_epoch_mono ts ∧
  ts_bound_ok0 ts ∧
  ts_bound_ok1 ts ms ∧
  ts_entry_know ts ms uid ∧
  ts_bound_know ts ms uid.

Lemma ts_interp ts ms uid ep m :
  ts_inv ts ms uid →
  adtr_inv ms →
  ms !! ep = Some m →
  ep ≤ ts.(bound) →
  msv m uid (ts_get ts ep).
Proof.
  intros Hts Hadtr Hm_look Hbound. split.
  (* ver memb. should come all from the ts_get entries. *)
  - admit.
  (* ver non-memb. the next ver is either in the TS or in the bound. *)
  - destruct (decide (filter (λ x, ep < x.1) ts.(entries) = [])) as [Hbig|Hbig].
    (* in the bound. *)
    + destruct Hts as (_&_&Hok&_&Hknow).
      list_elem ms (bound ts) as m_bnd; [done|].
      ospecialize (Hknow m_bnd Hm_bnd_lookup).
      assert (length (ts_get ts ep) = length (ts.(entries))) as ->.
      { pose proof (filter_app_complement (λ x, ep < x.1) ts.(entries)) as H.
        rewrite Hbig in H. list_simplifier. apply Permutation_length in H.
        rewrite (list_filter_iff _ (λ x, x.1 ≤ ep)) in H; [done|lia]. }
      destruct Hadtr as (Hmono&_).
      ospecialize (Hmono _ _ _ _ Hm_look Hm_bnd_lookup Hbound).
      by eapply lookup_weaken_None.
    (* in the TS. *)
    + eapply (proj2 (head_is_Some _)) in Hbig as [xlt Hbig].
      destruct Hts as (_&_&_&Hent&_).
      (* prove that next ver is head of remaining TS. *)
      admit.
  (* TODO: maybe better approach is defining ts_get as a recursive prefix,
  then proving (with ts_inv) that it satisfies the list_filter prop. *)
Admitted.

End ts_msv.
