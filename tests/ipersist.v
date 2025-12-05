From Perennial.goose_lang Require Export ipersist.

Section proof.

Context `{!BiBUpd PROP} {P Q : PROP} `{!UpdateIntoPersistently P Q}.

Lemma cant_persist :
  P -∗ Q.
Proof.
  iIntros "HP".
  Fail iPersist "HP".
Abort.


Lemma can_persist :
  P ==∗ Q.
Proof.
  iIntros "HP".
  iPersist "HP". done.
Qed.

End proof.
