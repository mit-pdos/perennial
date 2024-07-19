From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com.tchajed.goose Require Import unittest.

Section proof.
Context `{!heapGS Σ}.

Lemma proph_test : ⊢ WP unittest.Oracle #() {{ _, True }}.
Proof.
  iStartProof. wp_rec.
  wp_apply wp_NewProph_list.
  iIntros (p pvs1) "Hp".
  wp_apply (wp_ResolveProph_list with "Hp").
  iIntros (pvs2) "[_ Hp]".
  wp_apply (wp_ResolveProph_list with "Hp").
  iIntros (pvs3) "[_ Hp]".
  wp_pures. auto.
Qed.

End proof.
