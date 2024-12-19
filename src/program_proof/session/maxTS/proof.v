From Goose.github_com.session Require Import maxTS.
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

  Definition coqMax (x: w64) (y: w64) :=
    if uint.Z x >? uint.Z y then x else y. 

  Fixpoint maxTSCoq (t1: list w64) (t2: list w64) : list w64 :=
    match t1 with
    | [] => []
    | cons hd1 tl1 => match t2 with
                      | [] => [] (* this shouldn't happen*)
                      | cons hd2 tl2 => if (uint.Z hd1) >? (uint.Z hd2) then
                                          (cons hd1 (maxTSCoq tl1 tl2)) else (cons hd2 (maxTSCoq tl1 tl2))
                      end
    end.

  Lemma max_equiv (x: w64) (y: w64) :
    {{{
          True
    }}}
      maxTwoInts #x #y 
      {{{
            r , RET #r;
            ⌜r = coqMax x y⌝
      }}}.
  Proof.
    iIntros (Φ) "H H1".
    unfold maxTwoInts. wp_pures.
    wp_if_destruct.
    - iModIntro. iApply "H1". iPureIntro.
      unfold coqMax. apply Z.gtb_lt in Heqb.
      rewrite Heqb. auto.
    - iModIntro. iApply "H1". iPureIntro.
      unfold coqMax.
      assert (uint.Z y >= uint.Z x) by word.
      assert (uint.Z x >? uint.Z y = false) by word.
      rewrite H0.
      auto.
  Qed.

  (* Lemma getMaxTsEquiv (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) :
    {{{
          own_slice x uint64T (DfracOwn 1) xs ∗
          own_slice y uint64T (DfracOwn 1) ys 
    }}}
      maxTS x y 
      {{{
            (r: Slice.t), RET slice_val r;
            own_slice r uint64T (DfracOwn 1) (maxTSCoq xs ys) ∗ (* what is slice_val? *)
            own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys 
      }}}.
  Proof.
    iIntros (Φ) "H H1".
    unfold maxTS.
    wp_pures. wp_apply wp_ref_to. *)
    
    
End heap.
