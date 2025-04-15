From New.golang.defn Require Import mem loop typing.

Module chan.
Section defns.
Context `{ffi_syntax}.

Axiom make : go_type → val.
Axiom receive : val.
Axiom send : val.
Axiom select : val.
Axiom close : val.
Axiom len : val.
Axiom cap : val.
Axiom for_range : val.

End defns.
End chan.
