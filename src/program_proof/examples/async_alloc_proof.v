From Perennial.program_proof Require Import async_disk_prelude.
From Perennial.program_proof Require Import async_disk_lib.
From Perennial.program_proof Require Import util_proof.
From Perennial.Helpers Require Import bytes range_set.
From Goose.github_com.mit_pdos.perennial_examples Require Import async_alloc.
From Perennial.goose_lang Require Import crash_borrow.

(* TODO: this file isn't using typed_slice, should fix that *)

Definition numbits := 8 * 4096.
Lemma numbits_unfold : numbits = 8 * 4096.
Proof. reflexivity. Qed.
Opaque numbits.
Definition max := U64 (8 * 4096).


Lemma Z_u8_to_u64 x : int.Z (u8_to_u64 x) = int.Z x.
Proof.
  rewrite /u8_to_u64 /U64.
  rewrite /U64.
  rewrite word.unsigned_of_Z_nowrap //.
  pose proof (word.unsigned_range x).
  lia.
Qed.

Lemma and_1_u8 (x: u8) : 0 ≤ int.Z (word.and x (U8 1)) ≤ 1.
Proof.
  assert (Lt ≠ Gt) by congruence.
  assert (Eq ≠ Gt) by congruence.
  byte_cases x; vm_compute; auto.
Qed.


Definition bit_lookup (bn: u64) (bits: list u8) : bool :=
  match bits !! int.nat (word.divu bn 8) with
  | None => false
  | Some byt =>
    match byte_to_bits byt !! (int.nat (word.modu bn 8)) with
    | None => false
    | Some bt => bt
    end
  end.

Definition is_set (bn: u64) (bits : list u8) : bool := (bit_lookup bn bits).
Definition is_unset (bn: u64) (bits : list u8) : bool := negb (bit_lookup bn bits).

Definition unset_bit (bn: u64) (bits : list u8) : list u8 :=
  match bits !! int.nat (word.divu bn 8) with
  | Some b => (<[int.nat (word.divu bn 8):=(word.and b (word.not (word.slu (U8 1) (u8_from_u64 (word.modu bn 8
                )))))]> bits)
  | _ => bits
  end.

Definition set_bit (bn : u64) (bits : list u8) : list u8 :=
  match bits !! int.nat (word.divu bn 8) with
  | Some b => (<[int.nat (word.divu bn 8):=(word.or b (word.slu (U8 1) (u8_from_u64 (word.modu bn 8))))]>
                 bits)
  | _ => bits
  end.

(* We postulate abstract predicates for the ghost state we will need *)
Section ghost_state.
  Context `{!heapGS Σ}.

  Inductive bit_state :=
  | Dirty (mem_val : bool) (disk_val: bool)
  | Clean (bit_val : bool)
  | Clean_synced (bit_val : bool).

  Definition get_disk_val (bs : bit_state) : bool :=
    match bs with
    | Dirty _ bv => bv
    | Clean bv => bv
    | Clean_synced bv => bv
    end.

  Definition reserve_bit (bs : bit_state) : bit_state :=
    match bs with
    | Dirty mv dv => Dirty true dv
    | Clean bv => Dirty true bv
    | Clean_synced bv => Dirty true bv
    end.

  Definition free_bit (bs : bit_state) : bit_state :=
    match bs with
    | Dirty mv dv => Dirty false dv
    | Clean bv => Dirty false bv
    | Clean_synced bv => Dirty false bv
    end.

  Definition bit_state_map := gmap u64 bit_state.

  Definition map_reserve_bit bn bsm : bit_state_map :=
    match bsm !! bn with
    | None => bsm
    | Some bs => <[bn := reserve_bit bs]>bsm
    end.

  Definition map_free_bit bn bsm : bit_state_map :=
    match bsm !! bn with
    | None => bsm
    | Some bs => <[bn := free_bit bs]>bsm
    end.

  Definition mark_clean (bs : bit_state) :=
    match bs with
    | Dirty bv _ => Clean bv
    | Clean bv => Clean bv
    | Clean_synced bv => Clean_synced bv
    end.

  Definition mark_sync (bs : bit_state) :=
    match bs with
    | Dirty mv dv  => Dirty mv dv
    | Clean bv => Clean_synced bv
    | Clean_synced bv => Clean_synced bv
    end.

  Parameter bufblock_gnames : Set.

  Parameter bufblock_auth : bufblock_gnames → list u8 → list u8 → bit_state_map → iProp Σ.
  Parameter bufblock_frag :  bufblock_gnames → list u8 → list u8 → iProp Σ.
  Parameter bit_ptsto : bufblock_gnames → u64 → bit_state → iProp Σ.

  Lemma bufblock_auth_length γ memblk diskblk bsm :
    bufblock_auth γ memblk diskblk bsm -∗ ⌜ length memblk = Z.to_nat 4096 ∧ length diskblk = Z.to_nat 4096 ⌝.
  Proof. Admitted.

  Lemma bufblock_frag_length γ memblk diskblk :
    bufblock_frag γ memblk diskblk -∗ ⌜ length memblk = Z.to_nat 4096 ∧ length diskblk = Z.to_nat 4096 ⌝.
  Proof. Admitted.

  Lemma bufblock_auth_frag_agree γ memblk1 diskblk1 bsm memblk2 diskblk2 :
    bufblock_auth γ memblk1 diskblk1 bsm -∗ bufblock_frag γ memblk2 diskblk2 -∗
                  ⌜ memblk1 = memblk1 ∧ diskblk2 = diskblk2 ⌝.
  Proof. Admitted.

  Lemma bufblock_reserve_mem γ memblk1 diskblk1 memblk2 diskblk2 bsm k bs :
    bufblock_auth γ memblk1 diskblk1 bsm -∗
    bufblock_frag γ memblk2 diskblk2 -∗
    bit_ptsto γ k bs ==∗
    bufblock_auth γ (set_bit k memblk1) diskblk1 (map_reserve_bit k bsm) ∗
    bufblock_frag γ (set_bit k memblk2) diskblk2 ∗
    bit_ptsto γ k (reserve_bit bs).
  Proof. Admitted.

  Lemma bufblock_free_mem γ memblk1 diskblk1 memblk2 diskblk2 bsm k bs :
    bufblock_auth γ memblk1 diskblk1 bsm -∗
    bufblock_frag γ memblk2 diskblk2 -∗
    bit_ptsto γ k bs ==∗
    bufblock_auth γ (unset_bit k memblk1) diskblk1 (map_free_bit k bsm) ∗
    bufblock_frag γ (unset_bit k memblk2) diskblk2 ∗
    bit_ptsto γ k (free_bit bs).
  Proof. Admitted.

  Lemma bufblock_flush γ memblk1 diskblk1 memblk2 diskblk2 bsm :
    bufblock_auth γ memblk1 diskblk1 bsm -∗
    bufblock_frag γ memblk2 diskblk2 ==∗
    bufblock_auth γ memblk1 memblk1 (mark_clean <$> bsm) ∗
    bufblock_frag γ memblk2 memblk2.
  Proof. Admitted.

  Lemma bufblock_barrier γ memblk diskblk bsm k bv :
    bufblock_auth γ memblk diskblk bsm -∗
    bit_ptsto γ k (Clean bv) ==∗
    bufblock_auth γ memblk diskblk (mark_sync <$> bsm) ∗
    bit_ptsto γ k (Clean_synced bv).
  Proof. Admitted.

  Lemma bufblock_init blk :
    length blk = Z.to_nat 4096 →
    ⊢ |==> ∃ γ bsm, bufblock_auth γ blk blk bsm ∗ bufblock_frag γ blk blk ∗
                  [∗ set] i ∈ rangeSet 0 numbits, bit_ptsto γ i (Clean_synced (bit_lookup i blk)).
  Proof. Admitted.

End ghost_state.

Section proof.
Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

Let N: namespace := nroot .@ "alloc".
Let Ninv: namespace := nroot .@ "alloc_inv".

Opaque crash_borrow.

Context (Ψ: u64 → iProp Σ).

(* TODO: put bufblock frag also in crash borrow? Then we never generate a fresh γ or need exchanger? *)

Definition alloc_linv γ (l: loc) : iProp Σ :=
  ∃ (next: u64) (bitmap_s: Slice.t) (membits diskbits: list u8) (dirty : bool) (markedset : gset u64),
  "next" ∷ l ↦[Alloc :: "next"] #next ∗
  "bitmap" ∷ l ↦[Alloc :: "bitmap"] (slice_val bitmap_s) ∗
  "dirty" ∷ l ↦[Alloc :: "dirty"] #dirty ∗
  "%Hdirty" ∷ ⌜ if negb dirty then membits = diskbits else True ⌝ ∗
  "%Hnext_bound" ∷ ⌜int.Z next < int.Z max⌝ ∗
  "%Hbits_len" ∷ ⌜int.Z max = (8 * (Z.of_nat $ length membits))%Z⌝ ∗
  "%Hmarkedset" ∷ ⌜ ∀ x, x ∈ markedset → is_set x membits ⌝ ∗
  "Hbits" ∷ is_slice_small bitmap_s byteT 1 (b2val <$> membits) ∗
  "Hbufblock_frag" ∷ bufblock_frag γ membits diskbits ∗
  "Hborrow" ∷ crash_borrow ([∗ set] i ∈ rangeSet 0 numbits ∖ markedset, (∃ bs, bit_ptsto γ i bs) ∗ Ψ i)
                           ([∗ set] i ∈ rangeSet 0 numbits ∖ markedset, bit_ptsto γ i (Clean_synced true) ∨ Ψ i)
.

(*
  "Hborrow" ∷ crash_borrow ([∗ set] i ∈ rangeSet 0 numbits,
                            if is_unset i membits then
                              (∃ bs, bit_ptsto γ i bs) ∗ Ψ i
                            else
                               True)
                           ([∗ set] i ∈ rangeSet 0 numbits, bit_ptsto γ i (Clean_synced true) ∨ Ψ i)

  "Hborrow" ∷ crash_borrow ([∗ set] i ∈ rangeSet 0 numbits ∖ markedset, (∃ bs, bit_ptsto γ i bs) ∗ Ψ i)
                           ([∗ set] i ∈ rangeSet 0 numbits ∖ markedset, bit_ptsto γ i (Clean_synced true) ∨ Ψ i)


*)

Definition bits_synced (bsm : bit_state_map) (aset : gset Block) :=
  (∀ i, i ∈ rangeSet 0 numbits →
        ∃ bs, bsm !! i = Some bs ∧
              match bs with
              | Clean_synced bt => (∀ blk : Block, blk ∈ aset → bit_lookup i blk = bt)
              | _ => True
              end).


Definition alloc_inv_inner γ (a : u64) (l : loc)  : iProp Σ :=
  ∃ (memblk diskblk : list u8) aset bsm,
  "Hbufblock_auth" ∷ bufblock_auth γ memblk diskblk bsm ∗
  "Hblock_ptsto" ∷ int.Z a d↦[aset] (list_to_block diskblk) ∗
  "%Hbitval" ∷ ⌜ bits_synced bsm aset ⌝
.

Definition alloc_inv γ a l := inv Ninv (alloc_inv_inner γ a l).

Definition is_alloc γ (addr : u64) (l: loc) : iProp Σ :=
  ∃ d (mu_l: loc),
    "%Hmax_nonzero" ∷ ⌜0 < int.Z max⌝ ∗
    "#d" ∷ readonly (l ↦[Alloc :: "d"] (disk_val d)) ∗
    "#mu" ∷ readonly (l ↦[Alloc :: "mu"] #mu_l) ∗
    "#addr" ∷ readonly (l ↦[Alloc :: "addr"] #addr) ∗
    "#His_lock" ∷ is_lock N #mu_l (alloc_linv γ l) ∗
    "#His_alloc_inv" ∷ alloc_inv γ addr l
.

Global Instance is_alloc_persistent γ addr l : Persistent (is_alloc γ addr l).
Proof. apply _. Qed.

(* State needed to initialize allocator *)
Definition is_alloc_pre_durable (addr : u64) : iProp Σ :=
  ∃ (bits : list u8),
    "%Hlen" ∷ ⌜ length bits = Z.to_nat 4096 ⌝ ∗
    "Hblk" ∷ int.Z addr d↦[∅] (list_to_block bits) ∗
    "HΨs" ∷ ([∗ set] i ∈ rangeSet 0 numbits, if is_unset i bits then Ψ i else True).

Lemma wpc_MkAlloc (addr: u64) d :
  {{{ is_alloc_pre_durable addr }}}
    MkAlloc (async_disk.disk_val d) #addr @ ⊤
  {{{ γ l, RET #l; is_alloc γ addr l }}}
  {{{ is_alloc_pre_durable addr }}}.
Proof.
  iIntros (Φ Φc) "Hd HΦ".
  wpc_call; try by iFrame.
  wpc_pures.
  { iLeft in "HΦ". by iApply "HΦ". }
  iNamed "Hd".
  wpc_bind (disk.Read #addr).
  iApply wpc_crash_borrow_generate_pre; first done.
  wpc_apply (wpc_Read with "[$]").
  iSplit.
  { iIntros. iLeft in "HΦ". iApply "HΦ". iExists _. iFrame. eauto. }
  iNext. iIntros (s) "(Hd&Hs)".
  iIntros "Hpre".
  iMod (bufblock_init bits) as (γ bsm) "(Hauth&Hfrag&Hptstos)"; first done.
  iCombine "HΨs Hptstos" as "HΨs".
  rewrite -big_sepS_sep.
  iDestruct (crash_borrow_init_cancel
               ([∗ set] i ∈ rangeSet 0 numbits,
                            if is_unset i bits then
                              (∃ bs, bit_ptsto γ i bs) ∗ Ψ i
                            else
                               True)
               ([∗ set] i ∈ rangeSet 0 numbits, bit_ptsto γ i (Clean_synced true) ∨ Ψ i)
               with "[$] [HΨs] []") as "Hinit_cancel".
  


  iDestruct (crash_borrow_init_cancel
               ([∗ set] i ∈ rangeSet 0 numbits,
                            if is_unset i bits then
                              (∃ bs, bit_ptsto γ i bs) ∗ Ψ i
                            else
                               True)
               ([∗ set] i ∈ rangeSet 0 numbits, bit_ptsto γ i (Clean_synced true) ∨ Ψ i)
               with "[$] [HΨs] []") as "Hinit_cancel".
  { iApply (big_sepS_mono with "HΨs"). iIntros (x Hin) "(?&?)".
    destruct (is_unset _ _); iFrame.
    iExists _; by iFrame. }
  { iModIntro.


  wpc_frame "Hd HΦ HΨs".
  { iLeft in "HΦ". iApply "HΦ". iExists _. iFrame. eauto. }
  wp_pures.
  wp_apply wp_new_free_lock.
  iIntros (mu_l) "Hl".
  wp_pures.
  wp_apply wp_allocStruct; first by eauto.
  iIntros (l) "Halloc".
  iApply struct_fields_split in "Halloc".
  iNamed "Halloc".
  unshelve (iMod (readonly_alloc_1 with "mu") as "#mu"); try apply _.
  unshelve (iMod (readonly_alloc_1 with "addr") as "#addr"); try apply _.
  unshelve (iMod (readonly_alloc_1 with "d") as "#d"); try apply _.
  iMod (alloc_lock N _ _ (alloc_linv l) with "Hl [Hs next bitmap]") as "#Hl".
  { iNext.
    iExists _, _, _; iFrame.
    rewrite list_to_block_to_vals; auto.
    iDestruct (is_slice_to_small with "Hs") as "$".
    iPureIntro.
    rewrite /max. word.
  }
  wp_pures.
  iModIntro. iNamed 1.
  iApply "HΦ".
  iExists _, _; iFrame "#".
  iPureIntro.
  rewrite /max; word.
Qed.

Lemma bits_lookup_byte (max: u64) (bits: list u8) (num: u64) :
  int.Z max = 8 * length bits →
  int.Z num < int.Z max →
  ∃ (b:u8), (b2val <$> bits) !! int.nat (word.divu num 8) = Some (b2val b).
Proof.
  intros Hmax Hnum.
  assert (int.Z num / 8 < length bits).
  { apply Zdiv_lt_upper_bound; lia. }
  destruct (list_lookup_lt _ bits (Z.to_nat (int.Z num / 8)%Z)) as [b Hlookup].
  { apply Nat2Z.inj_lt.
    word. }
  exists b.
  rewrite list_lookup_fmap.
  apply fmap_Some.
  eexists; split; eauto.
  rewrite word.unsigned_divu_nowrap; auto.
Qed.

(* TODO: identical to freeBit proof, would be nice to share some of this *)
Lemma wp_MarkUsed max l (bn: u64) :
  int.Z bn < int.Z max →
  {{{ is_alloc max l }}}
    Alloc__MarkUsed #l #bn
  {{{ RET #(); True }}}.
Proof.
  intros Hbound.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hlinv]".
  wp_pures.
  iNamed "Hlinv".
  wp_loadField.
  destruct (bits_lookup_byte max bits bn) as [b Hlookup]; [ done | done | ].
  wp_apply (wp_SliceGet with "[$Hbits]"); first by eauto.
  iIntros "[Hbits _]".
  wp_loadField.
  wp_apply (wp_SliceSet with "[$Hbits]").
  { iSplit; iPureIntro; [ done | auto ]. }
  iIntros "Hbits".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[$His_lock $Hlocked next bitmap Hbits]").
  { rewrite -list_fmap_insert.
    iExists _, _, _; iFrame "∗%".
    rewrite insert_length.
    iFrame "%". }
  wp_pures. by iApply "HΦ".
Qed.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma wp_MkMaxAlloc (max: u64) :
  0 < int.Z max →
  int.Z max `mod` 8 = 0 →
  {{{ True }}}
    MkMaxAlloc #max
  {{{ l, RET #l; is_alloc max l }}}.
Proof.
  iIntros (Hbound Hmod Φ) "_ HΦ".
  wp_call.
  rewrite -> bool_decide_eq_true_2 by word.
  wp_pures.
  rewrite bool_decide_eq_true_2; last first.
  { repeat (f_equal; try word). }
  wp_pures.
  wp_apply wp_new_slice; first by auto.
  iIntros (bitmap_s) "Hs".
  wp_pures.
  iApply is_slice_to_small in "Hs".
  replace (replicate (int.nat (word.divu max 8)) (zero_val byteT))
          with (b2val <$> replicate (int.nat (word.divu max 8)) (U8 0));
    last first.
  { rewrite fmap_replicate //. }
  wp_apply (wp_MkAlloc with "[$Hs]").
  { rewrite replicate_length.
    word. }
  { rewrite replicate_length.
    word. }
  iIntros (a_l) "#Ha".
  rewrite replicate_length.
  wp_pures.
  wp_apply (wp_MarkUsed with "Ha").
  { word. }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iExactEq "Ha".
  f_equal.
  word.
Qed.

Lemma wp_incNext (max: u64) (l: loc) :
  0 < int.Z max →
  {{{ alloc_linv max l }}}
    Alloc__incNext #l
  {{{ (next': u64), RET #next'; ⌜int.Z next' < int.Z max⌝ ∗
                                alloc_linv max l }}}.
Proof.
  iIntros (Hbound Φ) "Hl HΦ".
  iNamed "Hl".
  wp_call.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_loadField.
  wp_pures.
  wp_if_destruct.
  - wp_storeField.
    wp_loadField.
    iApply "HΦ".
    iSplit.
    + iPureIntro.
      word.
    + iExists _, _, _.
      iFrame "∗%".
  - wp_loadField.
    iApply "HΦ".
    iDestruct (is_slice_small_sz with "Hbits") as %Hsz_len.
    rewrite fmap_length in Hsz_len.
    rewrite word.unsigned_mul in Heqb.
    rewrite -> wrap_small in Heqb by word.
    change (int.Z 8) with 8 in Heqb.
    iSplit.
    + iPureIntro.
      revert Heqb. word.
    + iExists _, _, _.
      iFrame "∗%".
      iPureIntro.
      revert Heqb; word.
Qed.

Lemma wp_allocBit (max: u64) (l: loc) :
  {{{ is_alloc max l }}}
    Alloc__allocBit #l
  {{{ (n: u64), RET #n; ⌜int.Z n < int.Z max⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (typed_mem.wp_AllocAt uint64T); first by auto.
  iIntros (num_l) "num".
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "His_lock").
  iIntros "[Hlocked Hlinv]".
  wp_apply (wp_incNext with "Hlinv"); auto.
  iIntros (?) "[%Hnext_bound Hlinv]".
  wp_store.
  wp_load.
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak (λ _, ∃ (num: u64),
                            "%Hnum_bound" ∷ ⌜int.Z num < int.Z max⌝ ∗
                            "num" ∷ num_l ↦[uint64T] #num ∗
                            "Hlinv" ∷ alloc_linv max l)%I
                        with "[] [num Hlinv]"); swap 1 2.
  - (* initial loop invariant *)
    iExists _; iFrame "∗%".
  - clear Φ.
    iIntros "!>" (Φ) "Hinv HΦ". iNamed "Hinv".
    wp_pures. wp_load. wp_load.
    wp_pures.
    iNamed "Hlinv".
    wp_loadField.
    destruct (bits_lookup_byte max bits num) as [b Hlookup]; [ done | done | ].
    wp_apply (wp_SliceGet _ _ _ _ _ _ _ (b2val b) with "[$Hbits]"); first done.
    iIntros "[Hbits _]".
    wp_pures.
    wp_if_destruct.
    + wp_loadField.
      wp_apply (wp_SliceGet with "[$Hbits]"); first done.
      iIntros "[Hbits _]".
      wp_loadField.
      wp_apply (wp_SliceSet with "[$Hbits]").
      { iSplit; iPureIntro; [ done | auto ]. }
      iIntros "Hbits".
      wp_pures.
      iApply "HΦ".
      iExists _; iFrame.
      iModIntro.
      iSplit; first by (iPureIntro; word).
      rewrite -list_fmap_insert.
      iExists _, _, _; iFrame "∗%".
      rewrite insert_length.
      iFrame "%".
    + wp_apply (wp_incNext max with "[next bitmap Hbits]"); first done.
      { iExists _, _, _; iFrame "∗%". }
      iIntros (next'') "[%Hnext'' Hlinv]".
      wp_store.
      wp_load.
      wp_if_destruct.
      { wp_store.
        iApply "HΦ".
        iExists _; iFrame "∗%". eauto. }
      iApply "HΦ".
      iExists _; iFrame "∗%"; eauto.
  - iNamed 1.
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[$His_lock $Hlocked $Hlinv]").
    wp_load.
    iApply "HΦ".
    iPureIntro; done.
Qed.

Lemma wp_freeBit max l (bn: u64) :
  int.Z bn < int.Z max →
  {{{ is_alloc max l }}}
    Alloc__freeBit #l #bn
  {{{ RET #(); True }}}.
Proof.
  intros Hbound.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hlinv]".
  wp_pures.
  iNamed "Hlinv".
  wp_loadField.
  destruct (bits_lookup_byte max bits bn) as [b Hlookup]; [ done | done | ].
  wp_apply (wp_SliceGet with "[$Hbits]"); first by eauto.
  iIntros "[Hbits _]".
  wp_loadField.
  wp_apply (wp_SliceSet with "[$Hbits]").
  { iSplit; iPureIntro; [ done | auto ]. }
  iIntros "Hbits".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[$His_lock $Hlocked next bitmap Hbits]").
  { rewrite -list_fmap_insert.
    iExists _, _, _; iFrame "∗%".
    rewrite insert_length.
    iFrame "%". }
  wp_pures. by iApply "HΦ".
Qed.

Lemma wp_AllocNum max l :
  {{{ is_alloc max l }}}
    Alloc__AllocNum #l
  {{{ (n: u64), RET #n; ⌜int.Z n < int.Z max⌝ }}}.
Proof.
  iIntros (Φ) "H HΦ".
  wp_call.
  wp_apply (wp_allocBit with "H").
  iIntros (n Hlt).
  wp_pures. iModIntro.
  iApply "HΦ". auto.
Qed.

Lemma wp_FreeNum max l (num: u64) :
  int.Z num < int.Z max →
  int.Z num ≠ 0 →
  {{{ is_alloc max l }}}
    Alloc__FreeNum #l #num
  {{{ RET #(); True }}}.
Proof.
  intros Hnum Hnonzero.
  iIntros (Φ) "H HΦ".
  wp_call.
  wp_if_destruct.
  { contradiction Hnonzero. word. }
  wp_apply (wp_freeBit with "H"); eauto.
  wp_pures. by iApply "HΦ".
Qed.

Lemma wp_popCnt (b: u8) :
  {{{ True }}}
    popCnt #b
  {{{ (n: u64), RET #n; ⌜int.Z n ≤ 8⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply (typed_mem.wp_AllocAt uint64T); auto.
  iIntros (count_l) "Hcount".
  wp_pures.
  wp_apply wp_ref_to; auto.
  iIntros (x_l) "Hx".
  wp_pures.
  wp_apply wp_ref_to; auto.
  iIntros (i_l) "Hi".
  wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ (x: u8) (count: u64),
                           "Hx" ∷ x_l ↦[byteT] #x ∗
                           "Hcount" ∷ count_l ↦[uint64T] #count ∗
                           "%Hcount_bound" ∷ ⌜int.Z count ≤ int.Z i⌝)%I
              with "[] [Hx Hcount $Hi]").
  - word.
  - clear.
    iIntros (i Φ) "!> Hpre HΦ".
    iDestruct "Hpre" as "(Hpre & Hi & %Hi)".
    iNamed "Hpre".
    wp_pures.
    wp_load. wp_load. wp_store. wp_load. wp_store.
    iModIntro.
    iApply "HΦ".
    iFrame "Hi".
    iExists _, _; iFrame.
    iPureIntro.
    word_cleanup.
    rewrite Z_u8_to_u64.
    pose proof (and_1_u8 x).
    rewrite wrap_small; lia.
  - iExists _, _; iFrame.
    iPureIntro.
    word.
  - iIntros "[Hinv _]".
    iNamed "Hinv".
    wp_pures. wp_load.
    iModIntro.
    iApply "HΦ".
    iPureIntro. word.
Qed.

Lemma wp_NumFree max l :
  {{{ is_alloc max l }}}
    Alloc__NumFree #l
  {{{ (n:u64), RET #n; ⌜0 ≤ int.Z n ≤ int.Z max⌝}}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hlinv]".
  wp_pures.
  iNamed "Hlinv".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_apply (typed_mem.wp_AllocAt uint64T); first by val_ty.
  iIntros (count_l) "Hcount".
  wp_pures.
  wp_loadField.

  iDestruct (is_slice_small_sz with "Hbits") as %Hsz.
  rewrite fmap_length in Hsz.

  wp_apply (wp_forSlice (λ i, ∃ (count: u64),
                            "Hcount" ∷ count_l ↦[uint64T] #count ∗
                            "%Hcount_bound" ∷ ⌜int.Z count ≤ 8 * int.Z i⌝)%I
           with "[] [Hcount $Hbits]").
  - clear Φ.
    iIntros (i x Φ) "!> [Hinv [%Hbound %Hlookup]] HΦ". iNamed "Hinv".
    fmap_Some in Hlookup as b.
    wp_pures.
    wp_load.
    wp_apply wp_popCnt.
    iIntros (popcnt Hpop_bound).
    wp_store.
    iModIntro.
    iApply "HΦ".
    iExists _; iFrame.
    iPureIntro.
    word.
  - iExists _; iFrame.
    iPureIntro; word.
  - iIntros "[Hinv Hbits]". iNamed "Hinv".
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[$His_lock $Hlocked next bitmap Hbits]").
    { iExists _, _, _; iFrame "∗%". }
    wp_load.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iPureIntro.
    word_cleanup.
    rewrite word.unsigned_mul.
    word.
Qed.

End proof.

Ltac Zify.zify_post_hook ::= idtac.
