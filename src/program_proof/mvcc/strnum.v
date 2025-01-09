From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.vmvcc.examples Require Export strnum.

Section program.
Context `{!heapGS Σ}.

Definition u64_to_string (n : u64) : string.
Admitted.

Lemma u64_to_string_inj n1 n2 :
  u64_to_string n1 = u64_to_string n2 ->
  n1 = n2.
Admitted.

Theorem wp_StringToU64 (s : byte_string) (n : u64) :
  {{{ ⌜u64_to_string n = s⌝ }}}
    StringToU64 #(LitString s)
  {{{ (n : u64), RET #n; ⌜u64_to_string n = s⌝ }}}.
Admitted.

Theorem wp_U64ToString (n : u64) :
  {{{ True }}}
    U64ToString #n
  {{{ (s : byte_string), RET #(LitString s); ⌜u64_to_string n = s⌝ }}}.
Admitted.

End program.
