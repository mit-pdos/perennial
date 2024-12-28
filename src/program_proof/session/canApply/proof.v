From Goose.github_com.session Require Import canApply.
From Perennial.program_proof Require Import std_proof. 
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.
From Perennial.program_logic Require Export atomic.
From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang.lib Require Import struct.struct into_val.
From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import prelude.

Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.

Section heap.
  
  Context `{hG: !heapGS Σ}.

  Fixpoint coqCanApply (serverId: w64) (v1: list w64) (v2: list w64) (index: nat) (canApply: bool) : bool :=
    match v1 with
    | [] => true
    | cons h1 t1 => match v2 with
                    | [] => true
                    | cons h2 t2 => if (uint.nat serverId) =? index then
                                      (coqCanApply serverId t1 t2 (index + 1) (canApply))
                                      else (if (canApply && (uint.Z h1 + 1 =? uint.Z h2)) then (coqCanApply serverId t1 t2 (index + 1) (false)) else false)
                    end
    end.
                      
  Lemma canApply_equiv (serverId: w64) (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) :
    {{{
          own_slice x uint64T (DfracOwn 1) xs ∗
          own_slice y uint64T (DfracOwn 1) ys ∗
          ⌜length xs = length ys⌝ ∗
          ⌜length xs < 2^64⌝
    }}}
       oneOffVersionVector #serverId x y 
      {{{
            r , RET #r;
            ⌜r = coqCanApply serverId xs ys 0 true⌝ ∗ 
            own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys ∗
            ⌜length xs = length ys⌝ ∗
            ⌜length xs < 2^64⌝
      }}}.
  Proof.
    iIntros (Φ) "(H1 & H2 & H3 & H4) H5".
    unfold oneOffVersionVector. wp_pures.
    wp_apply wp_ref_to; auto.
    iIntros (output) "H6". wp_pures.
    wp_apply wp_ref_to; auto.
    iIntros (canApply) "H7". wp_pures.
    wp_apply wp_ref_to; auto.
    iIntros (index) "H8". wp_pures.
    wp_apply wp_slice_len.
    wp_apply wp_ref_to; auto.
    iIntros (l) "H9". wp_pures.
    wp_apply (wp_forBreak_cond
                (λ continue,
                  ∃ (b1 b2: bool) (i: w64),
                    "Hx" ∷ own_slice x uint64T (DfracOwn 1) xs ∗
                      "Hy" ∷ own_slice y uint64T (DfracOwn 1) ys ∗
                      output ↦[boolT] #b1 ∗
                      canApply ↦[boolT] #b2 ∗
                      index ↦[uint64T] #i ∗
                      l ↦[uint64T] #(length xs) 
                )%I
               with "[] []").
    - iIntros (?). iModIntro. iIntros "H1 H2".
      iNamed "H1". iDestruct "H1" as "(H1 & H3 & H4 & H5)".
      wp_load. wp_load. wp_if_destruct.
      + wp_load. wp_if_destruct.
        * wp_load. wp_pures. wp_store. iModIntro. iApply "H2".
          iExists (b1). iExists (b2).
          iExists ((w64_word_instance.(word.add) serverId (W64 1))).
          iFrame.
        * 


    



