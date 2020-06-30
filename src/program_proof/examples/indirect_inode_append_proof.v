From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import indirect_inode.

From Perennial.program_proof.examples Require Import alloc_crash_proof indirect_inode_proof.
From Perennial.goose_lang.lib Require Import lock.crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.Helpers Require Import List.
From Perennial.program_proof Require Import marshal_proof disk_lib.

Section goose.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!stagedG Σ}.
Context `{!allocG Σ}.

Context (inodeN allocN: namespace).

Implicit Types (σ: inode.t).
Implicit Types (l:loc) (γ:gname) (P: inode.t → iProp Σ).

Definition reserve_fupd E (Palloc: alloc.t → iProp Σ) : iProp Σ :=
  ∀ (σ σ': alloc.t) ma,
    ⌜match ma with
     | Some a => a ∈ alloc.free σ ∧ σ' = <[a:=block_reserved]> σ
     | None => σ' = σ ∧ alloc.free σ = ∅
     end⌝ -∗
  ▷ Palloc σ ={E}=∗ ▷ Palloc σ'.

(* free really means unreserve (we don't have a way to unallocate something
marked used) *)
Definition free_fupd E (Palloc: alloc.t → iProp Σ) (a:u64) : iProp Σ :=
  ∀ (σ: alloc.t),
    ⌜σ !! a = Some block_reserved⌝ -∗
  ▷ Palloc σ ={E}=∗ ▷ Palloc (<[a:=block_free]> σ).

(* This is useless because you need to do this together with some other action. *)
Definition use_fupd E (Palloc: alloc.t → iProp Σ) (a: u64): iProp Σ :=
  (∀ σ : alloc.t,
      ⌜σ !! a = Some block_reserved⌝ -∗
      ▷ Palloc σ ={E}=∗ ▷ Palloc (<[a:=block_used]> σ)).

Let Ψ (a: u64) := (∃ b, int.val a d↦ b)%I.

Theorem wp_appendDirect {l σ addr} (a: u64) b:
  {{{
    "Ha" ∷ int.val a d↦ b ∗
    "Hinv" ∷ inode_linv l σ addr
  }}}
  Inode__appendDirect #l #a
  {{{ (ok: bool), RET #ok; if ok then
      (∀ σ', ⌜σ' = set inode.blocks (λ bs, bs ++ [b]) (set inode.addrs ({[a]} ∪.) σ)⌝ -∗
                         "%Hsize" ∷ ⌜length σ.(inode.blocks) < maxDirect⌝
                         ∗ "Ha" ∷ int.val a d↦ b
                         ∗ "Hinv" ∷ inode_linv l σ' addr)
      else ⌜ length σ.(inode.blocks) >= maxDirect ⌝
  }}}.
Proof.
  iIntros (Φ) "Hpre". iNamed "Hpre". iNamed "Hinv".
  iNamed "Hdurable".
  unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  iIntros "HΦ".
  wp_call.
  wp_loadField.
  wp_if_destruct.
  (* Fits within maxDirect *)
  {
    iDestruct (is_slice_sz with "Hdirect") as %HlenDir.
    replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in Heqb0 by word.
    wp_loadField.
    wp_apply (wp_SliceAppend (V:=u64) with "[$Hdirect]").
    {
      iPureIntro.
      rewrite /list.untype fmap_take /fmap_length in HlenDir.
      rewrite take_length Min.min_l in HlenDir; try word.
      rewrite fmap_length. word.
    }
    iIntros (direct_s') "Hdirect".
    Transparent slice.T.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_apply (wp_Inode__mkHdr l
                            (length σ.(inode.blocks) + 1)
                            _
                              (take (length σ.(inode.blocks)) dirAddrs ++ [a])
                              _
                              direct_s' indirect_s _ with "[direct indirect size Hdirect Hindirect]").
    {
      iFrame.
      replace (word.add (U64 (Z.of_nat (length σ.(inode.blocks)))) (U64 1))
      with (U64 (Z.of_nat (length σ.(inode.blocks)) + 1)); auto; word.
    }
    iIntros (s b') "(Hb & %Hencoded' &?&?&?&?&?)"; iNamed.
    wp_let.
    wp_loadField.
    wp_apply (wp_Write with "[Hhdr Hb]").
    { iExists hdr; iFrame. }

    iIntros "[Hhdr Hb]".
    wp_pures.
    iApply "HΦ".
    iIntros.
    iFrame.
    iSplitR; auto.
    rewrite a0; simpl.
    iExists hdr, direct_s', indirect_s,
    numInd, (take (length σ.(inode.blocks)) dirAddrs ++ [a] ++ (drop (int.nat maxDirect - length σ'.(inode.blocks)) dirAddrs)), indAddrs, indBlkAddrsList, indBlocks.
    iFrame.
  }
  {

  }
Admitted.

Theorem wp_writeIndirect {l σ addr} (indA a: u64) (indBlk b: Block) (addrs : list u64) addr_s:
  {{{
       "%Hsize" ∷ ⌜length σ.(inode.blocks) >= maxDirect⌝ ∗
       "%Haddrs" ∷ ⌜∃ ls, addrs = ls ++ [a]⌝ ∗
       "Haddr_s" ∷ is_slice addr_s uint64T 1 addrs ∗
       "Ha" ∷ int.val a d↦ b ∗
       "HindA" ∷ int.val indA d↦ indBlk ∗
       "Hinv" ∷ inode_linv l σ addr
  }}}
  Inode__writeIndirect #l #a (slice_val addr_s)
  {{{ RET #();
      ∀ σ',
        ⌜σ' = set inode.blocks (λ bs, bs ++ [b]) (set inode.addrs ({[a]} ∪.) σ)⌝ -∗
                  ("Hinv" ∷ inode_linv l σ' addr
                          ∗ "Ha" ∷ int.val a d↦ b
                          ∗ "HIndA" ∷ int.val indA d↦ indBlk)
  }}}.
Proof.
Admitted.

Theorem wp_appendIndirect {l σ addr} (a: u64) b:
  {{{
    "%Hsize" ∷ ⌜length σ.(inode.blocks) >= maxDirect⌝ ∗
    "Hinv" ∷ inode_linv l σ addr ∗
    "Ha" ∷ int.val a d↦ b
  }}}
  Inode__appendDirect #l #a
  {{{ (ok: bool), RET #ok;
      if ok then
      (∀ σ',
          ⌜σ' = set inode.blocks (λ bs, bs ++ [b]) (set inode.addrs ({[a]} ∪.) σ)⌝ -∗
                  "Hinv" ∷ inode_linv l σ' addr ∗ "Ha" ∷ int.val a d↦ b ∗
                  "Hsize" ∷ ∃ indirect_s,
                      l ↦[Inode.S :: "indirect"] (slice_val indirect_s) -∗
                        ⌜ (Z.add (((length σ.(inode.blocks)) - maxDirect) `div` indirectNumBlocks) 1) < int.val indirect_s.(Slice.sz) ⌝)
      else
        "Hinv" ∷ inode_linv l σ addr ∗
        "Ha" ∷ int.val a d↦ b ∗
        "Hsize" ∷  ∃ indirect_s,
          l ↦[Inode.S :: "indirect"] (slice_val indirect_s) -∗
            ⌜ (Z.add (((length σ.(inode.blocks)) - maxDirect) `div` indirectNumBlocks) 1) >= int.val indirect_s.(Slice.sz) ⌝
  }}}.
Proof.
Admitted.

Theorem wpc_Inode__Append {k E2}
        {l k' P addr}
        (* allocator stuff *)
        {Palloc γalloc domain n}
        (alloc_ref: loc) q (b_s: Slice.t) (b0: Block) :
  (S (S k) < n)%nat →
  (S (S k) < k')%nat →
  nroot.@"readonly" ## allocN →
  nroot.@"readonly" ## inodeN →
  inodeN ## allocN →
  ∀ Φ Φc,
      "Hinode" ∷ is_inode inodeN l (LVL k') P addr ∗ (* XXX why did I need to put inodeN here? *)
      "Hbdata" ∷ is_block b_s q b0 ∗
      "#Halloc" ∷ is_allocator Palloc Ψ allocN alloc_ref domain γalloc n ∗
      "#Halloc_fupd" ∷ □ reserve_fupd (⊤ ∖ ↑allocN) Palloc ∗
      "#Hfree_fupd" ∷ □ (∀ a, free_fupd (⊤ ∖ ↑allocN) Palloc a) ∗
      "Hfupd" ∷ (Φc ∧ ▷ (Φ #false ∧ ∀ σ σ' addr',
        ⌜σ' = set inode.blocks (λ bs, bs ++ [b0])
                              (set inode.addrs ({[addr']} ∪.) σ)⌝ -∗
        ⌜inode.wf σ⌝ -∗
        ∀ s,
        ⌜s !! addr' = Some block_reserved⌝ -∗
         ▷ P σ ∗ ▷ Palloc s ={⊤ ∖ ↑allocN ∖ ↑inodeN}=∗
         ▷ P σ' ∗ ▷ Palloc (<[addr' := block_used]> s) ∗ (Φc ∧ Φ #true))) -∗
  WPC Inode__Append #l (slice_val b_s) #alloc_ref @ NotStuck; LVL (S (S k)); ⊤; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (????? Φ Φc) "Hpre"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
Admitted.
End goose.
