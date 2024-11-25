From iris.proofmode Require Import proofmode.
From Perennial.program_proof.rsm.pure Require Import list.

Section lemmas.
  Context `{FinMap K M}.

  Lemma map_to_list_not_elem_of_take_key {A} {m : M A} l i k v :
    map_to_list m ≡ₚ l ->
    l !! i = Some (k, v) ->
    k ∉ (take i l).*1.
  Proof.
    intros Hl Hkv.
    pose proof (NoDup_fst_map_to_list m) as Hnd.
    rewrite Hl in Hnd.
    pose proof (list_lookup_fmap fst l i) as Hi.
    rewrite Hkv in Hi.
    pose proof (not_elem_of_take _ _ _ Hnd Hi) as Htake.
    by rewrite -fmap_take in Htake.
  Qed.

End lemmas.
