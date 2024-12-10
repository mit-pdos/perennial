From New.proof Require Import grove_prelude.
From New.code.github_com.mit_pdos.gokv Require globals_test.
From Perennial.algebra Require Import map.
From New.proof Require Import std.

Section proof.

Context `{!heapGS Σ}.

Lemma wp_define' :
  {{{ True }}}
    globals_test.define' #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

Lemma wp_initialize' :
  {{{ True }}}
    globals_test.initialize' #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

End proof.
