From New.experiments Require Import glob.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core cryptoffi cryptoutil serde merkle.
From Perennial.goose_lang.lib.rwlock Require Import rwlock_noncrash.

Class epoch_versioned_mapG Σ :=
  {
    epoch_versioned_map_histG :: mono_listG (gmap w64 (ver_ty * pk_ty)) Σ;
    epoch_versioned_map_mapG :: ghost_mapG Σ w64 (ver_ty * pk_ty);
  }.

Section epoch_versioned_map.
Context `{!invGS Σ}.
Context `{!epoch_versioned_mapG Σ}.

Record epoch_map_names :=
{
  hist_gn: gname;
  latest_gn: gname;
}.

Implicit Type γ : epoch_map_names.

(** Ownership of [uid], knowing the current version is [ver] and the current
    public key is [pk]. *)
Definition own_uid_dfrac γ dq (uid : w64) (ver : ver_ty) (pk : pk_ty) : iProp Σ :=
  uid ↪[γ.(latest_gn)]{dq} (ver, pk).

Notation own_uid γ uid ver pk := (own_uid_dfrac γ (DfracOwn 1) uid ver pk).

(** Knowledge that the pk map at epoch [epoch] is [m]. *)
Definition is_map γ (epoch : w64) (m : gmap w64 (ver_ty * pk_ty)) : iProp Σ :=
  mono_list_idx_own γ.(hist_gn) (uint.nat epoch) m.

Definition is_epoch_lb γ (epoch : w64) : iProp Σ :=
  ∃ m, is_map γ epoch m.

(** Ownership of the precise history of all pk maps so far. *)
Definition own_history γ (ms : list (gmap w64 (ver_ty * pk_ty))) : iProp Σ :=
  mono_list_auth_own γ.(hist_gn) (1/2) ms ∗
  ghost_map_auth γ.(latest_gn) (1/2) (default ∅ (last ms)).

Definition is_epoch_versioned_map γ (N : namespace) : iProp Σ :=
  inv N (
      ∃ ms,
        mono_list_auth_own γ.(hist_gn) (1/2) ms ∗
        ghost_map_auth γ.(latest_gn) (1/2) (default ∅ (last ms))
    ).

Lemma history_is_map (epoch : w64) γ ms m :
  ms !! (uint.nat epoch) = Some m →
  own_history γ ms -∗
  is_map γ epoch m.
Proof.
Admitted.

Lemma history_append {E} N (updates : gmap w64 (ver_ty * pk_ty * pk_ty)) γ ms :
  ↑N ⊆ E →
  own_history γ ms -∗
  ([∗ map] uid ↦ '(ver, pk, _) ∈ updates, own_uid γ uid ver pk) ={E}=∗
  own_history γ
    (ms ++ [((λ '(ver, _, pk'), (word.add ver (W64 1), pk')) <$> updates) ∪ default ∅ (last ms)]) ∗
  ([∗ map] uid ↦ '(ver, _, pk') ∈ updates, own_uid γ uid (word.add ver (W64 1)) pk').
Proof.
Admitted.

Lemma history_agree γ ms dq uid pk ver :
  own_history γ ms -∗
  own_uid_dfrac γ dq uid ver pk -∗
  ⌜ default ∅ (last ms) !! uid = Some (ver, pk) ⌝.
Proof.
Admitted.

End epoch_versioned_map.

Module userState.
Record t :=
  mk {
    numVers: w64;
    plainPk: list w8;
  }.

Section defs.
Context `{!heapGS Σ}.

Definition own ptr x d : iProp Σ :=
  ∃ plainPk_sl,
  "numVers" ∷ ptr ↦[userState :: "numVers"]{d} #x.(numVers) ∗
  "plainPk" ∷ ptr ↦[userState :: "plainPk"]{d} (slice_val plainPk_sl) ∗
  "plainPk_sl" ∷ own_slice_small plainPk_sl byteT DfracDiscarded x.(plainPk).
End defs.
End userState.

Module servEpochInfo.
Record t :=
  mk {
    updates: gmap (list w8) (w64 * list w8);
    dig: list w8;
    sig: list w8;
  }.

Section defs.
Context `{!heapGS Σ}.

Definition is_own ptr x : iProp Σ :=
  ∃ (updates_ptr : loc) updates_phys dig_sl sig_sl,
  "#updates" ∷ ptr ↦[servEpochInfo :: "updates"]□ #updates_ptr ∗
  "#updates_map" ∷ own_map updates_ptr DfracDiscarded updates_phys ∗
  "#updates_sl" ∷ ([∗ map] sl;y ∈ updates_phys;x.(updates),
                     own_slice_small sl byteT DfracDiscarded
                       (MapValPre.encodesF $ MapValPre.mk y.1 y.2)) ∗
  "#dig" ∷ ptr ↦[servEpochInfo :: "dig"]□ (slice_val dig_sl) ∗
  "#dig_sl" ∷ own_slice_small dig_sl byteT DfracDiscarded x.(dig) ∗
  "#sig" ∷ ptr ↦[servEpochInfo :: "sig"]□ (slice_val sig_sl) ∗
  "#sig_sl" ∷ own_slice_small sig_sl byteT DfracDiscarded x.(sig).

Global Instance pers ptr x : Persistent (is_own ptr x) := _.
End defs.

End servEpochInfo.

Module Server.
Record t :=
  mk {
      keyMap : gmap (list w8) (list w8);
      userInfo : gmap w64 userState.t;
      epochHist : list servEpochInfo.t;
  }.

Section defs.
Context `{!heapGS Σ}.
Definition own_phys ptr q s : iProp Σ :=
  ∃ epochHist_sl (userInfo_ptr keyMap_ptr : loc) userInfo_phys epochHist_ptrs,
  "epochHist" ∷ ptr ↦[Server :: "epochHist"]{DfracOwn q} (slice_val epochHist_sl) ∗
  "userInfo" ∷ ptr ↦[Server :: "userInfo"] #userInfo_ptr ∗
  "keyMap" ∷ ptr ↦[Server :: "keyMap"] #keyMap_ptr ∗

  "HkeyMap" ∷ own_Tree keyMap_ptr s.(keyMap) (DfracOwn q) ∗
  "HuserInfo_map" ∷ own_map userInfo_ptr (DfracOwn q) userInfo_phys ∗
  "HuserInfo_own" ∷ ([∗ map] l;x ∈ userInfo_phys; s.(userInfo), userState.own l x (DfracOwn q)) ∗
  "HepochHist_sl" ∷ own_slice epochHist_sl ptrT (DfracOwn q) epochHist_ptrs ∗
  "#HepochHist_is" ∷ ([∗ list] l;x ∈ epochHist_ptrs; s.(epochHist), servEpochInfo.is_own l x).
End defs.
End Server.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Record Server_names :=
  {
    map_gn : epoch_map_names;
    sig_pk : list w8;
    vrf_pk : list w8;
    commitSecret : list w8;
  }.

Implicit Types γ : Server_names.

(* Abstraction relation between the map in the merkle tree (which has hidden
   labels and pks) and a map from (uid,ver) pairs to pk. *)
Definition encode_uid_ver uid_ver :=
  (MapLabelPre.encodesF $ MapLabelPre.mk uid_ver.1 uid_ver.2).

Definition encode_pk γ pk :=
  (CommitOpen.encodesF $ CommitOpen.mk pk γ.(commitSecret)).

Definition is_map_relation γ (mₗ : gmap (list w8) (list w8))
  (mₕ : gmap (uid_ty * ver_ty) (epoch_ty * pk_ty)) : iProp Σ :=
  (* A (uid_er, epoch_pk) pair is in the abstract map iff a corresponding
     (hidden) element is in the physical map *)
  (∀ uid_ver epoch_pk,
     ⌜ mₕ !! uid_ver = Some epoch_pk ⌝ ∗-∗
     ∃ label commit,
       is_vrf_out γ.(vrf_pk) (encode_uid_ver uid_ver) label ∗
       is_hash (encode_pk γ epoch_pk.2) commit ∗
       ⌜ mₗ !! label = Some (MapValPre.encodesF $ MapValPre.mk epoch_pk.1 commit) ⌝).

Context `{!epoch_versioned_mapG Σ}.

(** Ghost ownership, invariants, and cryptographic knowledge related to mutable Server state. *)
Definition own_Server_ghost γ st : iProp Σ :=
  ∃ history openKeyMap (currentMap : gmap w64 (ver_ty * pk_ty)),
  (* abstract away the cryptographically private aspect of keyMap *)
  "#HkeyMap" ∷ is_map_relation γ st.(Server.keyMap) openKeyMap ∗

  "Hhistory" ∷ own_history γ.(map_gn) history ∗
  "%HlastHistory" ∷  ⌜ last history = Some currentMap ⌝ ∗
  "%HkeyMapLatest" ∷ (⌜ ∀ uid,
                        match currentMap !! uid with
                        | Some (ver, pk) =>
                            snd <$> openKeyMap !! (uid, ver) = Some pk ∧
                            (∀ ver', (uid, ver') ∈ dom openKeyMap ↔ uint.nat ver' ≤ uint.nat ver)
                        | None => (∀ ver, (uid, ver) ∉ dom openKeyMap)
                        end
    ⌝) ∗

  (* For every [userState] in [userInfo], the map has the latest value. *)
  "%HuserState" ∷
    (⌜ ∀ uid uinfo,
       st.(Server.userInfo) !! uid = Some uinfo →
       currentMap !! uid = Some ((word.sub uinfo.(userState.numVers) (W64 1)), uinfo.(userState.plainPk)) ⌝) ∗

   (* Everything in epochHist is signed; could make this a crypto property of [servEpochInfo]. *)
  "#HepochHist" ∷
    □(∀ epoch info,
        ⌜ st.(Server.epochHist) !! (uint.nat epoch) = Some info ⌝ →
        is_sig γ.(sig_pk) (PreSigDig.encodesF $ PreSigDig.mk epoch info.(servEpochInfo.dig))
          info.(servEpochInfo.sig)
    ) ∗

  (* The current keyMap is computed from applying updates *)
  "%HepochHistUpdates" ∷ (⌜ st.(Server.keyMap) =
                          (λ v, MapValPre.encodesF (MapValPre.mk v.1 v.2)) <$>
                            (foldl union (∅ : gmap _ _)
                               (servEpochInfo.updates <$> st.(Server.epochHist)))
                            ⌝)
.

(** Proposition guarded by RWMutex. *)
Definition own_Server γ s q : iProp Σ :=
  ∃ (st : Server.t),
    "Hphys" ∷ Server.own_phys s (q/2) st ∗
    "Hghost" ∷ own_Server_ghost γ st
.

Definition is_Server γ s : iProp Σ :=
  ∃ commitSecret_sl,
  "#commitSecret" ∷ s ↦[Server :: "commitSecret"]□ (slice_val commitSecret_sl) ∗
  "#commitSecret_sl" ∷ own_slice_small commitSecret_sl byteT DfracDiscarded γ.(commitSecret) ∗
  "#Hepoch_map" ∷ is_epoch_versioned_map γ.(map_gn) nroot
  (* TODO: RWMutex invariant *)
.
