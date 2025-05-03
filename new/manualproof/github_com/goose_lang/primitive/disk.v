Require Export New.proof.disk_prelude.
Require Export New.golang.theory.

Require Export New.code.github_com.goose_lang.primitive.disk.
Module disk.
Module Disk.
Definition t := loc.
End Disk.

Section instances.

Global Instance : IntoVal Disk.t := _.
Global Program Instance into_val_typed_Disk : IntoValTyped Disk.t disk.Disk := _.

End instances.

End disk.
