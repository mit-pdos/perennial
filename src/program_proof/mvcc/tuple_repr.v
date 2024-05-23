From Perennial.program_proof.mvcc Require Import tuple_prelude.

Definition TID_SENTINEL := (W64 18446744073709551615).
Definition RET_SUCCESS := (W64 0).
Definition RET_NONEXIST := (W64 1).
Definition RET_RETRY := (W64 100).
Definition RET_UNSERIALIZABLE := (W64 200).

Section repr.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition tuple_wellformed (vers : list pver) (tidlast tidgc : u64) : iProp Σ :=
  "%HtidlastGt" ∷ ⌜Forall (λ ver, uint.Z ver.1.1 < uint.Z tidlast) vers⌝ ∗
  "%HexistsLt" ∷ ⌜∀ (tid : u64), 0 < uint.Z tid ->
                                 uint.Z tidgc ≤ uint.Z tid ->
                                 Exists (λ ver, uint.Z ver.1.1 < uint.Z tid) vers⌝ ∗
  "%HtidgcLe" ∷ ⌜Forall (λ ver, uint.Z tidgc ≤ uint.Z ver.1.1) (tail vers)⌝ ∗
  "%Hnotnil" ∷ ⌜vers ≠ []⌝.

Definition own_tuple_phys
           (tuple : loc) (owned : bool) (tidlast : u64) (vers : list pver)
  : iProp Σ :=
  ∃ (versS : Slice.t),
    "Howned" ∷ tuple ↦[Tuple :: "owned"] #owned ∗
    "Htidlast" ∷ tuple ↦[Tuple :: "tslast"] #tidlast ∗
    "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val versS) ∗
    "HversS" ∷ slice.own_slice versS (structTy Version) (DfracOwn 1) (ver_to_val <$> vers).

Definition own_tuple_repr
           (key : u64) (tidlast tidgc : u64) (vers : list pver) (vchain : list dbval) γ
  : iProp Σ :=
  "%HtupleAbs" ∷ (∀ tid, ⌜uint.Z tidgc ≤ uint.Z tid ≤ uint.Z tidlast ->
                         vchain !! (uint.nat tid) = Some (spec_lookup vers tid)⌝) ∗
  (* We need this as [HtupleAbs] is not useful when [tidlast < tidgc]. *)
  "%Hlast" ∷ ⌜last vchain = Some (spec_lookup vers tidlast)⌝ ∗
  "%HvchainLen" ∷ ⌜(Z.of_nat (length vchain)) = ((uint.Z tidlast) + 1)%Z⌝ ∗
  "#Hgclb" ∷  min_tid_lb γ (uint.nat tidgc) ∗
  "#Hwellformed" ∷ tuple_wellformed vers tidlast tidgc.

Definition own_tuple (tuple : loc) (key : u64) γ : iProp Σ :=
  ∃ (owned : bool) (tidlast tidgc : u64) (vers : list pver) (vchain : list dbval),
    "Hphys"   ∷ own_tuple_phys tuple owned tidlast vers ∗
    "Hrepr"   ∷ own_tuple_repr key tidlast tidgc vers vchain γ ∗
    "Hptuple" ∷ ptuple_auth γ (if owned then (1 / 4) else (1 / 2))%Qp key vchain.

Definition own_tuple_read
           (tuple : loc) (key : u64) (owned : bool) (vchain : list dbval) γ
  : iProp Σ :=
  ∃ (tidlast tidgc : u64) (vers : list pver),
    "Hphys" ∷ own_tuple_phys tuple owned tidlast vers ∗
    "Hrepr" ∷ own_tuple_repr key tidlast tidgc vers vchain γ.

Definition is_tuple_locked tuple (key : u64) γ : iProp Σ :=
  ∃ (latch : loc) (rcond : loc),
    "#Hlatch" ∷ readonly (tuple ↦[Tuple :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_tuple tuple key γ) ∗
    "#Hrcond" ∷ readonly (tuple ↦[Tuple :: "rcond"] #rcond) ∗
    "#HrcondC" ∷ is_cond rcond #latch ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "Hlocked" ∷ locked #latch.

Definition own_tuple_locked
           (tuple : loc) (key : u64) (tid : nat) (vchain vchain' : list dbval) γ
  : iProp Σ :=
  ∃ (owned : bool) (tidlast tidgc : u64) (vers : list pver),
    "Hphys"   ∷ own_tuple_phys tuple owned tidlast vers ∗
    "Hrepr"   ∷ own_tuple_repr key tidlast tidgc vers vchain γ ∗
    "Hlock"   ∷ is_tuple_locked tuple key γ ∗
    "Hptuple" ∷ ptuple_auth γ (1 / 2)%Qp key vchain' ∗
    "%Hlen"   ∷ ⌜(length vchain ≤ S tid)%nat⌝.

Definition own_tuples_locked (tid : nat) (tpls : gmap u64 loc) γ : iProp Σ :=
  [∗ map] k ↦ tpl ∈ tpls, ∃ phys, own_tuple_locked tpl k tid phys phys γ.

Definition own_tuples_updated
           (tid : nat) (mods : dbmap) (tpls : gmap u64 loc) γ
  : iProp Σ :=
  [∗ map] k ↦ tpl; v ∈ tpls; mods, ∃ phys,
      own_tuple_locked tpl k tid phys (extend (S tid) phys ++ [v]) γ.

Definition is_tuple (tuple : loc) (key : u64) γ : iProp Σ :=
  ∃ (latch : loc) (rcond : loc) (p : proph_id),
    "#Hlatch" ∷ readonly (tuple ↦[Tuple :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_tuple tuple key γ) ∗
    "#Hrcond" ∷ readonly (tuple ↦[Tuple :: "rcond"] #rcond) ∗
    "#HrcondC" ∷ is_cond rcond #latch ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "#Hinv"   ∷ mvcc_inv_sst γ p ∗
    "_" ∷ True.

End repr.

#[global]
Hint Extern 1 (environments.envs_entails _ (own_tuple_phys _ _ _ _)) => unfold own_tuple_phys : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_tuple_repr _ _ _ _ _ _)) => unfold own_tuple_repr : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_tuple_read _ _ _ _ _)) => unfold own_tuple_read : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_tuple_locked _ _ _ _ _)) => unfold own_tuple_locked : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_tuple _ _ _)) => unfold own_tuple : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (is_tuple _ _ _)) => unfold is_tuple : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (is_tuple_locked _ _ _)) => unfold is_tuple_locked : core.

Section lemma.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Lemma is_tuple_invgc tuple key γ :
  is_tuple tuple key γ -∗
  mvcc_inv_gc γ.
Proof. iIntros "Htuple". by iNamed "Htuple". Qed.

End lemma.
