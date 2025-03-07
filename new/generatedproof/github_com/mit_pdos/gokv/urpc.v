(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.grove_prelude.
Require Export New.generatedproof.log.
Require Export New.generatedproof.sync.
Require Export New.generatedproof.github_com.goose_lang.primitive.
Require Export New.generatedproof.github_com.goose_lang.std.
Require Export New.generatedproof.github_com.mit_pdos.gokv.grove_ffi.
Require Export New.generatedproof.github_com.tchajed.marshal.
Require Export New.golang.theory.

Require Export New.code.github_com.mit_pdos.gokv.urpc.
Module urpc.
Axiom falso : False.
Module Server.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  handlers' : loc;
}.
End def.
End Server.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Server `{ffi_syntax}: Settable _ :=
  settable! Server.mk < Server.handlers' >.
Global Instance into_val_Server `{ffi_syntax} : IntoVal Server.t.
Admitted.

Global Instance into_val_typed_Server `{ffi_syntax} : IntoValTyped Server.t urpc.Server :=
{|
  default_val := Server.mk (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Server_handlers `{ffi_syntax} : IntoValStructField "handlers" urpc.Server Server.handlers'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Server `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} handlers':
  PureWp True
    (struct.make urpc.Server (alist_val [
      "handlers" ::= #handlers'
    ]))%struct
    #(Server.mk handlers').
Admitted.


Global Instance Server_struct_fields_split dq l (v : Server.t) :
  StructFieldsSplit dq l v (
    "Hhandlers" ∷ l ↦s[urpc.Server :: "handlers"]{dq} v.(Server.handlers')
  ).
Admitted.

End instances.
Module Callback.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  reply' : loc;
  state' : loc;
  cond' : loc;
}.
End def.
End Callback.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Callback `{ffi_syntax}: Settable _ :=
  settable! Callback.mk < Callback.reply'; Callback.state'; Callback.cond' >.
Global Instance into_val_Callback `{ffi_syntax} : IntoVal Callback.t.
Admitted.

Global Instance into_val_typed_Callback `{ffi_syntax} : IntoValTyped Callback.t urpc.Callback :=
{|
  default_val := Callback.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Callback_reply `{ffi_syntax} : IntoValStructField "reply" urpc.Callback Callback.reply'.
Admitted.

Global Instance into_val_struct_field_Callback_state `{ffi_syntax} : IntoValStructField "state" urpc.Callback Callback.state'.
Admitted.

Global Instance into_val_struct_field_Callback_cond `{ffi_syntax} : IntoValStructField "cond" urpc.Callback Callback.cond'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Callback `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} reply' state' cond':
  PureWp True
    (struct.make urpc.Callback (alist_val [
      "reply" ::= #reply';
      "state" ::= #state';
      "cond" ::= #cond'
    ]))%struct
    #(Callback.mk reply' state' cond').
Admitted.


Global Instance Callback_struct_fields_split dq l (v : Callback.t) :
  StructFieldsSplit dq l v (
    "Hreply" ∷ l ↦s[urpc.Callback :: "reply"]{dq} v.(Callback.reply') ∗
    "Hstate" ∷ l ↦s[urpc.Callback :: "state"]{dq} v.(Callback.state') ∗
    "Hcond" ∷ l ↦s[urpc.Callback :: "cond"]{dq} v.(Callback.cond')
  ).
Admitted.

End instances.
Module Client.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  mu' : loc;
  conn' : grove_ffi.Connection.t;
  seq' : w64;
  pending' : loc;
}.
End def.
End Client.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Client `{ffi_syntax}: Settable _ :=
  settable! Client.mk < Client.mu'; Client.conn'; Client.seq'; Client.pending' >.
Global Instance into_val_Client `{ffi_syntax} : IntoVal Client.t.
Admitted.

Global Instance into_val_typed_Client `{ffi_syntax} : IntoValTyped Client.t urpc.Client :=
{|
  default_val := Client.mk (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Client_mu `{ffi_syntax} : IntoValStructField "mu" urpc.Client Client.mu'.
Admitted.

Global Instance into_val_struct_field_Client_conn `{ffi_syntax} : IntoValStructField "conn" urpc.Client Client.conn'.
Admitted.

Global Instance into_val_struct_field_Client_seq `{ffi_syntax} : IntoValStructField "seq" urpc.Client Client.seq'.
Admitted.

Global Instance into_val_struct_field_Client_pending `{ffi_syntax} : IntoValStructField "pending" urpc.Client Client.pending'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Client `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} mu' conn' seq' pending':
  PureWp True
    (struct.make urpc.Client (alist_val [
      "mu" ::= #mu';
      "conn" ::= #conn';
      "seq" ::= #seq';
      "pending" ::= #pending'
    ]))%struct
    #(Client.mk mu' conn' seq' pending').
Admitted.


Global Instance Client_struct_fields_split dq l (v : Client.t) :
  StructFieldsSplit dq l v (
    "Hmu" ∷ l ↦s[urpc.Client :: "mu"]{dq} v.(Client.mu') ∗
    "Hconn" ∷ l ↦s[urpc.Client :: "conn"]{dq} v.(Client.conn') ∗
    "Hseq" ∷ l ↦s[urpc.Client :: "seq"]{dq} v.(Client.seq') ∗
    "Hpending" ∷ l ↦s[urpc.Client :: "pending"]{dq} v.(Client.pending')
  ).
Admitted.

End instances.

Module Error.
Section def.
Context `{ffi_syntax}.
Definition t := w64.
End def.
End Error.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Global Instance is_pkg_defined_instance : IsPkgDefined urpc :=
{|
  is_pkg_defined := is_global_definitions urpc var_addrs;
|}.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_MakeServer :
  WpFuncCall urpc "MakeServer" _ (is_pkg_defined urpc) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_TryMakeClient :
  WpFuncCall urpc "TryMakeClient" _ (is_pkg_defined urpc) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_MakeClient :
  WpFuncCall urpc "MakeClient" _ (is_pkg_defined urpc) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_Server'ptr_Serve :
  WpMethodCall urpc "Server'ptr" "Serve" _ (is_pkg_defined urpc) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Server'ptr_readThread :
  WpMethodCall urpc "Server'ptr" "readThread" _ (is_pkg_defined urpc) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Server'ptr_rpcHandle :
  WpMethodCall urpc "Server'ptr" "rpcHandle" _ (is_pkg_defined urpc) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Client'ptr_Call :
  WpMethodCall urpc "Client'ptr" "Call" _ (is_pkg_defined urpc) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Client'ptr_CallComplete :
  WpMethodCall urpc "Client'ptr" "CallComplete" _ (is_pkg_defined urpc) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Client'ptr_CallStart :
  WpMethodCall urpc "Client'ptr" "CallStart" _ (is_pkg_defined urpc) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Client'ptr_replyThread :
  WpMethodCall urpc "Client'ptr" "replyThread" _ (is_pkg_defined urpc) :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End urpc.
