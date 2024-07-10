From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import interface.

Section pure_execs.
Context `{ffi_sem: ffi_semantics}.

Global Instance pure_interface_call (iv : gmap string val) (name : string) (m : val) :
  WpPureExec (iv !! name = Some m) 2 (interface.call (interface.val iv) #(str name)) m.
Proof.
Admitted.

End pure_execs.
