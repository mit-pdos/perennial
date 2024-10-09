From Perennial.Helpers Require Import Integers.

From stdpp Require Import ssreflect prelude gmap.

Notation uid_ty := w64 (only parsing).
(* TODO: make ver_ty, epoch_ty work for w64. *)
Notation ver_ty := nat (only parsing).
Notation epoch_ty := nat (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation map_ty := (gmap (uid_ty * ver_ty) pk_ty) (only parsing).
(* sub-maps are useful for helping us state non-existence of
certain keys in a way that they carry across map subsets. *)
Notation submap_ty := (gmap (uid_ty * ver_ty) (option pk_ty)) (only parsing).

Section msv.

Definition msv_aux (m : map_ty) uid pks :=
  (∀ i, i < length pks → m !! (uid, i) = pks !! i).

(* maximum sequence of versions. *)
Definition msv m uid pks :=
  msv_aux m uid pks ∧
  m !! (uid, (length pks)) = None.

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

Lemma msv_aux_agree {m uid pks0 pks1} :
  msv_aux m uid pks0 →
  msv_aux m uid pks1 →
  length pks0 = length pks1 →
  pks0 = pks1.
Proof.
  revert pks1. induction pks0 as [|x0 l0 IH] using rev_ind;
    destruct pks1 as [|x1 l1 _] using rev_ind.
  - done.
  - rewrite length_app/=. lia.
  - rewrite length_app/=. lia.
  - rewrite !length_app/=. intros H0 H1 ?.
    apply msv_aux_snoc in H0 as [H0 Hx0]. apply msv_aux_snoc in H1 as [H1 Hx1].
    assert (length l0 = length l1) as HT by lia. rewrite HT in Hx0. clear HT.
    simplify_map_eq/=. ospecialize (IH l1 _ _ _); [done..|lia|]. naive_solver.
Qed.

Lemma msv_len_agree_aux {m uid pks0 pks1} :
  msv m uid pks0 →
  msv m uid pks1 →
  length pks0 < length pks1 →
  False.
Proof.
  intros HM0 HM1 ?. destruct HM0 as [_ HM0]. destruct HM1 as [HM1 _].
  ospecialize (HM1 (length pks0) _); [lia|].
  opose proof (lookup_lt_is_Some_2 pks1 (length pks0) _) as [? Hsome]; [lia|].
  rewrite Hsome in HM1. naive_solver.
Qed.

Lemma msv_len_agree {m uid pks0 pks1} :
  msv m uid pks0 →
  msv m uid pks1 →
  length pks0 = length pks1.
Proof.
  intros ??.
  destruct (decide (length pks0 = length pks1)) as [?|?]; [done|].
  exfalso. destruct (decide (length pks0 < length pks1)) as [?|?].
  - eapply (msv_len_agree_aux (pks0:=pks0) (pks1:=pks1)); [done..|lia].
  - eapply (msv_len_agree_aux (pks0:=pks1) (pks1:=pks0)); [done..|lia].
Qed.

Lemma msv_agree {m uid pks0 pks1} :
  msv m uid pks0 →
  msv m uid pks1 →
  pks0 = pks1.
Proof.
  intros HM0 HM1. eapply msv_aux_agree.
  - by destruct HM0 as [? _].
  - by destruct HM1 as [? _].
  - by eapply msv_len_agree.
Qed.

End msv.
