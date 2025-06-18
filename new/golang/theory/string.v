From Perennial.Helpers Require Import List ListLen Fractional NamedProps.
From iris.algebra Require Import dfrac.
From Perennial.iris_lib Require Import dfractional.
From Perennial.goose_lang Require Import ipersist.
From New.golang.defn Require Export string.
From New.golang.theory Require Import list assume exception loop typing primitive auto.
From New.golang.theory Require Import mem slice.
From Perennial Require Import base.

Set Default Proof Using "Type".

Section wps.
  
  Context `{hG: heapGS Σ, !ffi_semantics _ _}.

  Lemma wp_StringToBytes (s:go_string) :
  {{{
        True
  }}}
    string.to_bytes #s
  {{{
        (sl:slice.t), RET #sl; own_slice sl (DfracOwn 1) s         
  }}}.
  Admitted.

  Lemma wp_StringFromBytes sl q (l:go_string):
  {{{
        own_slice sl q l
  }}}
    string.from_bytes #sl
  {{{
        RET #l;
        own_slice sl q l
  }}}.
  Admitted.

End wps.
