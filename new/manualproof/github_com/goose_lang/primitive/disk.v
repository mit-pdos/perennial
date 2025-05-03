Require Export New.proof.disk_prelude.
Require Export New.golang.theory.

Require Export New.code.github_com.goose_lang.primitive.disk.
Module disk.
Module Disk.
Definition t := loc.
End Disk.

Section instances.

Global Instance : IntoVal Disk.t :=
  {|
    to_val_def := λ v, #v
  |}.

Global Program Instance into_val_typed_Disk : IntoValTyped Disk.t disk.Disk :=
{| default_val := null |}.
Next Obligation. rewrite to_val_unseal /=; solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_unseal /=. rewrite to_val_unseal /=. rewrite to_val_unseal /=. done. Qed.
Next Obligation. rewrite /Inj to_val_unseal /=. rewrite to_val_unseal /=. intros. inversion H. done. Qed.

End instances.

End disk.
