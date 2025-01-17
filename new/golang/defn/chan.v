From New.golang.defn Require Export mem loop typing.

Module chan.
Section defns.
Context `{ffi_syntax}.

Axiom make : go_type → val.
Axiom receive : val.
Axiom send : val.
Axiom select : val.
Axiom nil : val.
Axiom close : val.
Axiom len : val.
Axiom cap : val.

End defns.
End chan.
