From New.golang.defn Require Export exception mem.

Section defn.
Context `{!ffi_syntax}.

Definition wrap_defer : val :=
  λ: "body",
    let: "$defer" := (ref_ty funcT (λ: <>, #())) in
    let: "$func_ret" := exception_do ("body" "$defer") in
    (![funcT] "$defer") #();;
    "$func_ret".

End defn.

Global Notation "with_defer: e" := (wrap_defer (λ: "$defer", e%E)%E)
  (at level 90, e at level 85, format "with_defer:  '[' e ']'") : expr_scope.

Global Notation "with_defer': e" := (wrap_defer (λ: "$defer", e%E)%V)
  (at level 90, e at level 85, format "with_defer':  '[' e ']'") : expr_scope.
