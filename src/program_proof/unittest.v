From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com.tchajed.goose Require Import unittest.

Section proof.
Context `{!heapGS Σ}.

Lemma proph_test : ⊢ WP unittest.Oracle #() {{ _, True }}.
Proof.
  wp_lam.
  wp_apply wp_NewProph_list.
  iIntros (pvs p) "Hp".
  wp_apply (wp_ResolveProph_list with "Hp").
  iIntros (pvs') "[_ Hp]".
  wp_apply (wp_ResolveProph_list with "Hp").
  iIntros (pvs'') "[_ Hp]".
  wp_pures. auto.
Qed.

End proof.
