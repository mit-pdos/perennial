From New.proof Require Import proof_prelude.

(*
 Used for big sep props where a sequential index is needed, mostly just combines lemmas from seqZ and big_sep_L. If needed this could be expanded and generalized more but using this just for the channel model for now. 
*)

Section proof.
 Context `{hG: heapGS Σ, !ffi_semantics _ _}. 

Definition big_sep_seq (start: Z) (size: Z) (Φ : Z → iProp Σ) : iProp Σ :=
⌜ 0 ≤ size ⌝ ∗ 
[∗ list] _↦(i:Z) ∈ (seqZ start size), Φ i
.

Lemma big_sep_seq_singleton  (Φ : Z → iProp Σ) :
  ∀ (start: Z),
  big_sep_seq start 1 Φ  ⊣⊢  (Φ (start)%Z ).
  Proof.
    intros Hsize. unfold big_sep_seq.
    simpl. replace (0%nat + Hsize)%Z with Hsize by lia.
    {
      iSplitL "".
      { iIntros "(%Hsize2 & H &  emp)". done. }
      { iIntros "H". iFrame. iPureIntro. done. }
    }
Qed.

Lemma big_sep_seq_nil :
  ∀ start Φ,
  big_sep_seq start 0 Φ ⊣⊢ emp.
  Proof.
     intros start. intros. unfold big_sep_seq.
     simpl. iFrame. done.
Qed.
  
Lemma big_sep_seq_snoc (start: Z) (size: Z)   (Φ : Z → iProp Σ) :
  (0 ≤ size)%Z ->
  Φ (start + size)%Z ∗ big_sep_seq start size Φ  -∗ big_sep_seq start (size + 1)%Z Φ.
  Proof.
    intros H. iIntros "(Hpred & %Hsize & Hsep)".
    unfold big_sep_seq. 
    rewrite seqZ_app. all: try lia.
    {
      rewrite big_sepL_snoc.
      iFrame. iPureIntro. lia.
    }
Qed.

Lemma big_sep_seq_cons (start: Z) (size: Z) (Φ : Z → iProp Σ) :
  (0 ≤ size)%Z ->
  big_sep_seq start (size + 1)%Z Φ -∗ Φ (start + size)%Z ∗ big_sep_seq start size Φ.
  Proof.
    intros H. iIntros "(%Hsize & Hpred)".
    unfold big_sep_seq. 
    rewrite seqZ_app. all: try lia.
    {
      rewrite big_sepL_app.
      rewrite big_sepL_singleton.
       simpl.
       replace (0%nat + (start + size))%Z with (start + size)%Z by lia.
       iDestruct "Hpred" as "[Hlist Hpred]". iFrame.
       iPureIntro. lia.
    }
  Qed.

Lemma big_sep_seq_pop (start: Z) (size: Z)   (Φ : Z → iProp Σ) :
  1 ≤ size ->
  big_sep_seq start size%Z Φ -∗ Φ (start)%Z ∗ big_sep_seq (start + 1) (size - 1) Φ.
  Proof.
    intros H. iIntros "(%Hsize & Hpred)".
    unfold big_sep_seq. 
    rewrite seqZ_cons.
    {
      rewrite big_sepL_cons.
      iDestruct "Hpred" as "[Hs Hl]". iFrame. iPureIntro. lia.
    }
    {
      lia.
    }
Qed.

End proof.

