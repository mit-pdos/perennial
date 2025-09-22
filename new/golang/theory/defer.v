From New.golang.theory Require Import exception mem.
From New.golang.defn Require Import defer.

Section proof.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

  Lemma wp_with_defer e Φ :
    (∀ (defer : loc),
       defer ↦ (func.mk <> <> #())%V -∗
       WP (let: "$func_ret" := exception_do (subst "$defer" #defer e) in ![funcT] #defer #();; "$func_ret")
         {{ Φ }}) -∗
    WP (wrap_defer #(func.mk <> ("$defer" : string) e)) {{ Φ }}.
  Proof.
    iIntros "Hwp".
    wp_call.
    wp_apply wp_ref_ty. iIntros (defer) "Hdefer". wp_pures.
    iApply "Hwp". iFrame.
  Qed.

End proof.
