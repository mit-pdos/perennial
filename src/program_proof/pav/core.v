From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.pav Require Import serde.

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
Notation lat_val_ty := (option (fake_ver_ty * fake_map_val_ty)) (only parsing).

Section misc.
Class pavG Σ :=
  {
    #[global] pavG_adtr :: mono_listG (gmap opaque_label_ty (epoch_ty * comm_ty)) Σ;
    #[global] pavG_client_seen_maps :: mono_listG (option (dig_ty * gname)) Σ;
    #[global] pavG_client_submaps :: ghost_mapG Σ map_label_ty cli_map_val_ty;
  }.
End misc.

Section msv_core.

(* maximum sequence of versions. *)

Definition msv_core_aux (m : fake_map_ty) uid (vals : list fake_map_val_ty) :=
  (∀ ver val, vals !! ver = Some val → m !! (uid, ver) = Some val).

Definition msv_core m uid vals :=
  msv_core_aux m uid vals ∧
  m !! (uid, (length vals)) = None.

(* TODO: upstream. *)
Lemma lookup_snoc {A} (l : list A) (x : A) :
  (l ++ [x]) !! (length l) = Some x.
Proof. by opose proof (proj2 (lookup_snoc_Some x l (length l) x) _) as H; [naive_solver|]. Qed.

Lemma msv_core_aux_snoc {m uid l x} :
  msv_core_aux m uid (l ++ [x]) →
  msv_core_aux m uid l ∧ m !! (uid, length l) = Some x.
Proof.
  intros HM. split.
  - intros ?? Hlook. ospecialize (HM _ _ _); [|done].
    rewrite lookup_app_l; [exact Hlook|by eapply lookup_lt_Some].
  - ospecialize (HM (length l) _ _); [apply lookup_snoc|done].
Qed.

Lemma msv_core_aux_agree {m uid vals0 vals1} :
  msv_core_aux m uid vals0 →
  msv_core_aux m uid vals1 →
  length vals0 = length vals1 →
  vals0 = vals1.
Proof.
  revert vals1. induction vals0 as [|x0 l0 IH] using rev_ind;
    destruct vals1 as [|x1 l1 _] using rev_ind.
  - done.
  - rewrite length_app/=. lia.
  - rewrite length_app/=. lia.
  - rewrite !length_app/=. intros H0 H1 ?.
    apply msv_core_aux_snoc in H0 as [H0 Hx0]. apply msv_core_aux_snoc in H1 as [H1 Hx1].
    assert (length l0 = length l1) as HT by lia. rewrite HT in Hx0. clear HT.
    simplify_map_eq/=. ospecialize (IH l1 _ _ _); [done..|lia|]. naive_solver.
Qed.

Lemma msv_core_len_agree_aux {m uid vals0 vals1} :
  msv_core m uid vals0 →
  msv_core m uid vals1 →
  length vals0 < length vals1 →
  False.
Proof.
  intros HM0 HM1 ?. destruct HM0 as [_ HM0], HM1 as [HM1 _].
  list_elem vals1 (length vals0) as val.
  ospecialize (HM1 _ _ _); [exact Hval_lookup|naive_solver].
Qed.

Lemma msv_core_len_agree {m uid vals0 vals1} :
  msv_core m uid vals0 →
  msv_core m uid vals1 →
  length vals0 = length vals1.
Proof.
  intros Hcore0 Hcore1.
  destruct (decide (length vals0 = length vals1)) as [?|?]; [done|].
  exfalso. destruct (decide (length vals0 < length vals1)) as [?|?].
  - eapply (msv_core_len_agree_aux Hcore0 Hcore1); [done..|lia].
  - eapply (msv_core_len_agree_aux Hcore1 Hcore0); [done..|lia].
Qed.

Lemma msv_core_agree {m uid vals0 vals1} :
  msv_core m uid vals0 →
  msv_core m uid vals1 →
  vals0 = vals1.
Proof.
  intros HM0 HM1. eapply msv_core_aux_agree.
  - by destruct HM0 as [? _].
  - by destruct HM1 as [? _].
  - by eapply msv_core_len_agree.
Qed.

End msv_core.

Section msv.

(* msv hides all but the latest val.
a None val corresponds to an unregistered val. *)
Definition msv (m : fake_map_ty) uid (lat : lat_val_ty) :=
  let len_vals := match lat with None => 0 | Some (ver, val) => S ver end in
  ∃ vals, length vals = len_vals ∧ last vals = snd <$> lat ∧
  msv_core m uid vals.

Lemma msv_agree {m uid val0 val1} :
  msv m uid val0 →
  msv m uid val1 →
  val0 = val1.
Proof.
  intros HM0 HM1.
  destruct HM0 as (?&Hlen0&?&HM0). destruct HM1 as (?&Hlen1&?&HM1).
  pose proof (msv_core_agree HM0 HM1) as ->. rewrite Hlen0 in Hlen1.
  destruct val0 as [[??]|], val1 as [[??]|]; naive_solver.
Qed.

End msv.

Section hist_msv.

(* history and its interaction with msv. *)

(* for now, duplicate adtr invs so that below proofs can use this more pure version. *)
Definition maps_mono' (ms : list fake_map_ty) :=
  ∀ i j mi mj,
  ms !! i = Some mi →
  ms !! j = Some mj →
  i ≤ j →
  mi ⊆ mj.

(* maps_epoch_ok prevents entries from being added too early. *)
Definition maps_epoch_ok' (ms : list fake_map_ty) :=
  ∀ ep m k ep' comm,
  ms !! ep = Some m →
  m !! k = Some (ep', comm) →
  ep' ≤ ep.

Definition adtr_inv' ms := maps_mono' ms ∧ maps_epoch_ok' ms.

(* TODO: this is one way to write it. consolidates cases.
let's see how easy it is to prove with the physical hist. *)
Definition know_hist_val (ms : list fake_map_ty) (uid : w64) (ep : nat) (lat : lat_val_ty) :=
  let len_vals := match lat with None => 0 | Some (ver, val) => S ver end in
  ∃ vals, length vals = len_vals ∧ last vals = snd <$> lat ∧
  (* prior vers exist in prior or this map. *)
  (∀ ver val, vals !! ver = Some val →
    (∃ prior m, prior ≤ ep ∧ ms !! prior = Some m ∧ m !! (uid, ver) = Some val)) ∧
  ( (* next ver doesn't exist in this or later map. *)
    (∃ bound m, bound ≥ ep ∧ ms !! bound = Some m ∧ m !! (uid, length vals) = None)
    ∨
    (* next ver exists in later map. *)
    (∃ bound m comm, bound > ep ∧ ms !! bound = Some m ∧ m !! (uid, length vals) = Some (bound, comm))).

Definition know_hist (ms : list fake_map_ty) (uid : w64) (hist : list lat_val_ty) :=
  (∀ ep lat, hist !! ep = Some lat → know_hist_val ms uid ep lat).

(* hist_msv says that for every latest val in the hist,
we can derive an msv for it. *)
Lemma hist_msv ms uid hist ep m lat :
  adtr_inv' ms →
  know_hist ms uid hist →
  hist !! ep = Some lat →
  ms !! ep = Some m →
  msv m uid lat.
Proof.
  intros Hadtr Hhist Hlook_hist Hlook_m.
  specialize (Hhist _ _ Hlook_hist) as (vals&?&?&Hhist&Hbound).
  exists vals. split_and?; [done..|]. split; [|destruct Hbound as [Hbound|Hbound]].
  - intros ?? Hlook_ver.
    specialize (Hhist _ _ Hlook_ver) as (?&?&?&?Hlook_prior&?).
    opose proof ((proj1 Hadtr) _ _ _ _ Hlook_prior Hlook_m _); [lia|].
    by eapply lookup_weaken.
  - destruct Hbound as (?&?&?&Hlook_bound&?).
    opose proof ((proj1 Hadtr) _ _ _ _ Hlook_m Hlook_bound _); [lia|].
    by eapply lookup_weaken_None.
  - destruct Hbound as (?&?&?&?&Hlook_bound&?).
    destruct (decide $ is_Some $ m !! (uid, length vals)) as [[? Hlook_mkey]|]; last first.
    { by eapply eq_None_not_Some. }
    opose proof ((proj1 Hadtr) _ _ _ _ Hlook_m Hlook_bound _); [lia|].
    opose proof (lookup_weaken _ _ _ _ Hlook_mkey _); [done|]. simplify_eq/=.
    opose proof ((proj2 Hadtr) _ _ _ _ _ Hlook_m Hlook_mkey) as ?. lia.
Qed.

End hist_msv.

Section proper_adtr_inv.

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

End proper_adtr_inv.
