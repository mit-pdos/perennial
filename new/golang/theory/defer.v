From New.golang.theory Require Import exception mem.
From New.golang.defn Require Import defer.

Section proof.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

  Lemma wp_with_defer e Φ :
    (∀ defer, defer ↦[funcT] (λ: <>, #())%V -∗
              WP (let: "$func_ret" := exception_do (subst "$defer" #defer e) in ![funcT] #defer #();; "$func_ret")
              {{ Φ }}) -∗
    WP (with_defer': e) {{ Φ }}.
  Proof.
    iIntros "Hwp".
    wp_pures.
    wp_rec.
    wp_apply wp_ref_ty; [econstructor|]. iIntros (defer) "Hdefer". wp_pures.
    wp_apply "Hwp". iFrame.
  Qed.

End proof.
