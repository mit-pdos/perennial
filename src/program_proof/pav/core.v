From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.pav Require Import serde.

(*
From Perennial.base_logic.lib Require Import ghost_map.
From iris.unstable.base_logic Require Import mono_list.
*)

From RecordUpdate Require Export RecordSet.
From Perennial.base_logic.lib Require Export ghost_map.
From iris.unstable.base_logic Require Export mono_list.

(* TODO: for same reason not using alias's in go code,
prob shouldn't define all these notations. *)
Notation comm_ty := (list w8) (only parsing).
Notation dig_ty := (list w8) (only parsing).
Notation uid_ty := w64 (only parsing).
Notation ver_ty := w64 (only parsing).
(* TODO: make fake_ver_ty, fake_epoch_ty work for w64. *)
Notation fake_ver_ty := nat (only parsing).
Notation epoch_ty := w64 (only parsing).
Notation fake_epoch_ty := nat (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation map_label_ty := (uid_ty * ver_ty)%type (only parsing).
Notation fake_map_label_ty := (uid_ty * fake_ver_ty)%type (only parsing).
Notation opaque_label_ty := (list w8) (only parsing).
Notation map_val_ty := (epoch_ty * pk_ty)%type (only parsing).
Notation fake_map_val_ty := (fake_epoch_ty * pk_ty)%type (only parsing).
Notation map_ty := (gmap map_label_ty map_val_ty) (only parsing).
Notation fake_map_ty := (gmap fake_map_label_ty fake_map_val_ty) (only parsing).
Notation merkle_map_ty := (gmap (list w8) (list w8)) (only parsing).
Notation map_adtr_ty := (gmap opaque_label_ty (epoch_ty * comm_ty)) (only parsing).
Notation cli_map_val_ty := (option (epoch_ty * comm_ty))%type (only parsing).
Notation cli_map_ty := (gmap map_label_ty cli_map_val_ty) (only parsing).

Section misc.
Class pavG Σ :=
  {
    #[global] pavG_adtr :: mono_listG (gmap opaque_label_ty (epoch_ty * comm_ty)) Σ;
    #[global] pavG_client_seen_maps :: mono_listG (option (dig_ty * gname)) Σ;
    #[global] pavG_client_submaps :: ghost_mapG Σ map_label_ty cli_map_val_ty;
  }.
End misc.

Section msv.

(* maximum sequence of versions. *)

Definition msv_aux (m : fake_map_ty) uid vals :=
  (* TODO: change to know elem exists there. *)
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

Section hist_msv.

(* history and its interaction with msv. *)

Definition lower_adtr (m : map_adtr_ty) : merkle_map_ty :=
  (λ v, MapValPre.encodesF (MapValPre.mk v.1 v.2)) <$> m.

(* lookup_weaken_None and lookup_weaken are useful with this. *)
Definition maps_mono (ms : list merkle_map_ty) :=
  ∀ i j mi mj,
  ms !! i = Some mi →
  ms !! j = Some mj →
  i ≤ j →
  mi ⊆ mj.

(* note: auditor allows entry to be added after expected.
but originating client ensures that doesn't happen. *)
Definition maps_epoch_ok (ms : list map_adtr_ty) :=
  ∀ ep m_ep k ep' comm,
  ms !! ep = Some m_ep →
  m_ep !! k = Some (ep', comm) →
  (* can't have new entries in an old epoch. *)
  uint.nat ep' ≤ ep.

Definition adtr_inv ms := maps_mono (lower_adtr <$> ms) ∧ maps_epoch_ok ms.

(* tmp duplicate adtr invs that use the same map type as below. *)
Definition maps_mono' (ms : list fake_map_ty) :=
  ∀ i j mi mj,
  ms !! i = Some mi →
  ms !! j = Some mj →
  i ≤ j →
  mi ⊆ mj.

Definition maps_epoch_ok' (ms : list fake_map_ty) :=
  ∃ ep m_ep uid ver ep' val,
  ms !! ep = Some m_ep →
  m_ep !! (uid, ver) = Some (ep', val) →
  ep' ≤ ep.

Definition adtr_inv' ms := maps_mono' ms ∧ maps_epoch_ok' ms.

Record hist_entry_ty :=
  mk_hist_entry {
    (* TODO: make msv only talk about latest val at some version.
    this seems to more naturally capture what people care abt with KT.
    and it'd allow us to only make visible the latest val and version here.
    do this by proving new msv on top of old one. *)
    vals: list (nat * list w8);
  }.

Definition know_entry (uid : w64) (ep : nat) (entry : hist_entry_ty) (ms : list fake_map_ty) :=
  (* vals exist in prior maps. *)
  (∀ ver val, entry.(vals) !! ver = Some val →
    (∃ prior m, prior ≤ ep ∧ ms !! prior = Some m ∧ m !! (uid, ver) = Some val)) ∧
  (* next ver doesn't exist in some future map. *)
  (∃ bound m, bound ≥ ep ∧ ms !! bound = Some m ∧ m !! (uid, length entry.(vals)) = None).

Definition know_hist (uid : w64) (hist : list hist_entry_ty) (ms : list fake_map_ty) :=
  (∀ ep entry, hist !! ep = Some entry → know_entry uid ep entry ms).

Lemma hist_msv ms uid hist ep m entry :
  adtr_inv' ms →
  know_hist uid hist ms →
  hist !! ep = Some entry →
  ms !! ep = Some m →
  msv m uid entry.(vals).
Proof.
  intros Hadtr Hhist Hlook_entry Hlook_m. split.
  - intros ver Hlook_ver.
    specialize (Hhist _ _ Hlook_entry) as [Hhist _].
    list_elem entry.(vals) ver as val.
    specialize (Hhist _ _ Hval_lookup) as (?&?&?&Hlook_prior&Hlook_mprior).
    opose proof ((proj1 Hadtr) _ _ _ _ Hlook_prior Hlook_m _); [lia|].
    rewrite Hval_lookup.
    by eapply lookup_weaken.
  - specialize (Hhist _ _ Hlook_entry).
    destruct Hhist as [_ (bound&mbound&Hlt_bound&Hlook_bound&Hlook_mbound)].
    opose proof ((proj1 Hadtr) _ _ _ _ Hlook_m Hlook_bound _); [lia|].
    by eapply lookup_weaken_None.
Qed.

End hist_msv.
