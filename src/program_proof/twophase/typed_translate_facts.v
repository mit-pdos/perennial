From Perennial.Helpers Require Import Tactics.

From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.program_proof Require Import
     buf.defs
     addr.addr_proof
     twophase.typed_translate.

(* TODO: this file reduces the assumptions required in twophase_initP. Using
these theorems, it should be straightforward to delete the last two assumptions
there and derive the old definition, removing these complex assumptions from the
TCB. *)

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma kind_heap0_ok kinds :
  (∀ (a: u64), a ∈ dom (gset _) kinds → int.Z a * 4096 * 8 < 2^64) →
  map_Forall  (kinds_mapsto_valid kinds) (recovery_proof.kind_heap0 kinds).
Proof.
  intros Hdom.
  apply map_Forall_lookup => a o Hlookup.
  destruct a as [blk off].
  rewrite /recovery_proof.kind_heap0 lookup_gmap_curry in Hlookup.
  rewrite lookup_fmap in Hlookup.
  rewrite option_fmap_bind in Hlookup.
  apply bind_Some in Hlookup as [k [Hlookup Ho]].
  simpl in Ho.
  rewrite /kinds_mapsto_valid /=.
  split.
  - rewrite /valid_addr /=.
    rewrite /addr2flat_z /=.
    apply elem_of_dom_2 in Hlookup.
    apply Hdom in Hlookup.
    change disk.block_bytes with (Z.to_nat 4096) in *.
    assert (int.Z off < Z.to_nat 4096 * 8).
    { destruct k.
      - apply recovery_proof.lookup_bit0_map in Ho as [? ->]; simpl.
        unfold disk.block_bytes in *.
        word.
      - apply recovery_proof.lookup_inode0_map in Ho as [i (?&?&?)]; subst.
        word.
      - apply recovery_proof.lookup_block0_map in Ho as [? ?]; subst.
        word.
    }
    repeat split; try word.
  - destruct k; simpl in *.
    + apply recovery_proof.lookup_bit0_map in Ho as [? ->]; simpl.
      split; last done.
      rewrite /valid_off /=.
      word.
    + apply recovery_proof.lookup_inode0_map in Ho as [i (?&?&?)]; subst; simpl.
      split; last done.
      rewrite /valid_off /=.
      word.
    + apply recovery_proof.lookup_block0_map in Ho as [? ?]; subst; simpl.
      split; last done.
      rewrite /valid_off /=.
      auto.
Qed.

Lemma wf_jrnl_alt kinds :
  map_Forall  (kinds_mapsto_valid kinds) (recovery_proof.kind_heap0 kinds) →
  let σj := {| jrnlData := (bufObj_to_obj <$> recovery_proof.kind_heap0 kinds);
                jrnlKinds := kinds;
                jrnlAllocs := ∅
            |} in
  wf_jrnl σj.
Proof.
  simpl; intros.
  rewrite /wf_jrnl.
  split.
  - rewrite /offsets_aligned /=.
    rewrite dom_fmap_L.
    intros.
    pose proof H0 as [v Hlookup]%elem_of_dom.
    eapply map_Forall_lookup_2 in Hlookup; eauto.
    destruct Hlookup as (Hvalid_addr&Hvalid_off&Hkind_lookup).
    eauto.
  - rewrite /sizes_correct /=.
    intros a o' Hlookup.
    fmap_Some in Hlookup as o.
    destruct a as [blk off]; simpl.
    rewrite /recovery_proof.kind_heap0 lookup_gmap_curry in Hlookup.
    rewrite lookup_fmap in Hlookup.
    rewrite option_fmap_bind in Hlookup.
    apply bind_Some in Hlookup as [k [Hlookup Ho]].
    simpl in Ho.
    eexists; split; first by eauto.
    apply (inj Z.of_nat).
    destruct k.
    + apply recovery_proof.lookup_bit0_map in Ho as [? ?];
        subst; reflexivity.
    + apply recovery_proof.lookup_inode0_map in Ho as [i (?&?&?)];
        subst; reflexivity.
    + apply recovery_proof.lookup_block0_map in Ho as [? ?];
        subst; reflexivity.
Qed.
