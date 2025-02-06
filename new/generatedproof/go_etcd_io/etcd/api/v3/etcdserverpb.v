(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import go_etcd_io.etcd.api.v3.etcdserverpb.
From New.golang Require Import theory.

Axiom falso : False.

Module Compare_CompareResult.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End Compare_CompareResult.
Module Compare_CompareTarget.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End Compare_CompareTarget.
Module ResponseHeader.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  ClusterId' : w64;
  MemberId' : w64;
  Revision' : w64;
  RaftTerm' : w64;
  XXX_NoUnkeyedLiteral' : unit;
  XXX_unrecognized' : slice.t;
  XXX_sizecache' : w32;
}.
End def.
End ResponseHeader.


Global Instance settable_ResponseHeader `{ffi_syntax}: Settable _ :=
  settable! ResponseHeader.mk < ResponseHeader.ClusterId'; ResponseHeader.MemberId'; ResponseHeader.Revision'; ResponseHeader.RaftTerm'; ResponseHeader.XXX_NoUnkeyedLiteral'; ResponseHeader.XXX_unrecognized'; ResponseHeader.XXX_sizecache' >.
Global Instance into_val_ResponseHeader `{ffi_syntax} : IntoVal ResponseHeader.t.
Admitted.

Global Instance into_val_typed_ResponseHeader `{ffi_syntax} : IntoValTyped ResponseHeader.t etcdserverpb.ResponseHeader :=
{|
  default_val := ResponseHeader.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_ResponseHeader_ClusterId `{ffi_syntax} : IntoValStructField "ClusterId" etcdserverpb.ResponseHeader ResponseHeader.ClusterId'.
Admitted.

Global Instance into_val_struct_field_ResponseHeader_MemberId `{ffi_syntax} : IntoValStructField "MemberId" etcdserverpb.ResponseHeader ResponseHeader.MemberId'.
Admitted.

Global Instance into_val_struct_field_ResponseHeader_Revision `{ffi_syntax} : IntoValStructField "Revision" etcdserverpb.ResponseHeader ResponseHeader.Revision'.
Admitted.

Global Instance into_val_struct_field_ResponseHeader_RaftTerm `{ffi_syntax} : IntoValStructField "RaftTerm" etcdserverpb.ResponseHeader ResponseHeader.RaftTerm'.
Admitted.

Global Instance into_val_struct_field_ResponseHeader_XXX_NoUnkeyedLiteral `{ffi_syntax} : IntoValStructField "XXX_NoUnkeyedLiteral" etcdserverpb.ResponseHeader ResponseHeader.XXX_NoUnkeyedLiteral'.
Admitted.

Global Instance into_val_struct_field_ResponseHeader_XXX_unrecognized `{ffi_syntax} : IntoValStructField "XXX_unrecognized" etcdserverpb.ResponseHeader ResponseHeader.XXX_unrecognized'.
Admitted.

Global Instance into_val_struct_field_ResponseHeader_XXX_sizecache `{ffi_syntax} : IntoValStructField "XXX_sizecache" etcdserverpb.ResponseHeader ResponseHeader.XXX_sizecache'.
Admitted.

Instance wp_struct_make_ResponseHeader `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} ClusterId' MemberId' Revision' RaftTerm' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache':
  PureWp True
    (struct.make etcdserverpb.ResponseHeader (alist_val [
      "ClusterId" ::= #ClusterId';
      "MemberId" ::= #MemberId';
      "Revision" ::= #Revision';
      "RaftTerm" ::= #RaftTerm';
      "XXX_NoUnkeyedLiteral" ::= #XXX_NoUnkeyedLiteral';
      "XXX_unrecognized" ::= #XXX_unrecognized';
      "XXX_sizecache" ::= #XXX_sizecache'
    ]))%V
    #(ResponseHeader.mk ClusterId' MemberId' Revision' RaftTerm' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache').
Admitted.

Module RangeResponse.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Header' : loc;
  Kvs' : slice.t;
  More' : bool;
  Count' : w64;
  XXX_NoUnkeyedLiteral' : unit;
  XXX_unrecognized' : slice.t;
  XXX_sizecache' : w32;
}.
End def.
End RangeResponse.


Global Instance settable_RangeResponse `{ffi_syntax}: Settable _ :=
  settable! RangeResponse.mk < RangeResponse.Header'; RangeResponse.Kvs'; RangeResponse.More'; RangeResponse.Count'; RangeResponse.XXX_NoUnkeyedLiteral'; RangeResponse.XXX_unrecognized'; RangeResponse.XXX_sizecache' >.
Global Instance into_val_RangeResponse `{ffi_syntax} : IntoVal RangeResponse.t.
Admitted.

Global Instance into_val_typed_RangeResponse `{ffi_syntax} : IntoValTyped RangeResponse.t etcdserverpb.RangeResponse :=
{|
  default_val := RangeResponse.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_RangeResponse_Header `{ffi_syntax} : IntoValStructField "Header" etcdserverpb.RangeResponse RangeResponse.Header'.
Admitted.

Global Instance into_val_struct_field_RangeResponse_Kvs `{ffi_syntax} : IntoValStructField "Kvs" etcdserverpb.RangeResponse RangeResponse.Kvs'.
Admitted.

Global Instance into_val_struct_field_RangeResponse_More `{ffi_syntax} : IntoValStructField "More" etcdserverpb.RangeResponse RangeResponse.More'.
Admitted.

Global Instance into_val_struct_field_RangeResponse_Count `{ffi_syntax} : IntoValStructField "Count" etcdserverpb.RangeResponse RangeResponse.Count'.
Admitted.

Global Instance into_val_struct_field_RangeResponse_XXX_NoUnkeyedLiteral `{ffi_syntax} : IntoValStructField "XXX_NoUnkeyedLiteral" etcdserverpb.RangeResponse RangeResponse.XXX_NoUnkeyedLiteral'.
Admitted.

Global Instance into_val_struct_field_RangeResponse_XXX_unrecognized `{ffi_syntax} : IntoValStructField "XXX_unrecognized" etcdserverpb.RangeResponse RangeResponse.XXX_unrecognized'.
Admitted.

Global Instance into_val_struct_field_RangeResponse_XXX_sizecache `{ffi_syntax} : IntoValStructField "XXX_sizecache" etcdserverpb.RangeResponse RangeResponse.XXX_sizecache'.
Admitted.

Instance wp_struct_make_RangeResponse `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Header' Kvs' More' Count' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache':
  PureWp True
    (struct.make etcdserverpb.RangeResponse (alist_val [
      "Header" ::= #Header';
      "Kvs" ::= #Kvs';
      "More" ::= #More';
      "Count" ::= #Count';
      "XXX_NoUnkeyedLiteral" ::= #XXX_NoUnkeyedLiteral';
      "XXX_unrecognized" ::= #XXX_unrecognized';
      "XXX_sizecache" ::= #XXX_sizecache'
    ]))%V
    #(RangeResponse.mk Header' Kvs' More' Count' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache').
Admitted.

Module Compare.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Result' : w32;
  Target' : w32;
  Key' : slice.t;
  TargetUnion' : interface.t;
  RangeEnd' : slice.t;
  XXX_NoUnkeyedLiteral' : unit;
  XXX_unrecognized' : slice.t;
  XXX_sizecache' : w32;
}.
End def.
End Compare.


Global Instance settable_Compare `{ffi_syntax}: Settable _ :=
  settable! Compare.mk < Compare.Result'; Compare.Target'; Compare.Key'; Compare.TargetUnion'; Compare.RangeEnd'; Compare.XXX_NoUnkeyedLiteral'; Compare.XXX_unrecognized'; Compare.XXX_sizecache' >.
Global Instance into_val_Compare `{ffi_syntax} : IntoVal Compare.t.
Admitted.

Global Instance into_val_typed_Compare `{ffi_syntax} : IntoValTyped Compare.t etcdserverpb.Compare :=
{|
  default_val := Compare.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Compare_Result `{ffi_syntax} : IntoValStructField "Result" etcdserverpb.Compare Compare.Result'.
Admitted.

Global Instance into_val_struct_field_Compare_Target `{ffi_syntax} : IntoValStructField "Target" etcdserverpb.Compare Compare.Target'.
Admitted.

Global Instance into_val_struct_field_Compare_Key `{ffi_syntax} : IntoValStructField "Key" etcdserverpb.Compare Compare.Key'.
Admitted.

Global Instance into_val_struct_field_Compare_TargetUnion `{ffi_syntax} : IntoValStructField "TargetUnion" etcdserverpb.Compare Compare.TargetUnion'.
Admitted.

Global Instance into_val_struct_field_Compare_RangeEnd `{ffi_syntax} : IntoValStructField "RangeEnd" etcdserverpb.Compare Compare.RangeEnd'.
Admitted.

Global Instance into_val_struct_field_Compare_XXX_NoUnkeyedLiteral `{ffi_syntax} : IntoValStructField "XXX_NoUnkeyedLiteral" etcdserverpb.Compare Compare.XXX_NoUnkeyedLiteral'.
Admitted.

Global Instance into_val_struct_field_Compare_XXX_unrecognized `{ffi_syntax} : IntoValStructField "XXX_unrecognized" etcdserverpb.Compare Compare.XXX_unrecognized'.
Admitted.

Global Instance into_val_struct_field_Compare_XXX_sizecache `{ffi_syntax} : IntoValStructField "XXX_sizecache" etcdserverpb.Compare Compare.XXX_sizecache'.
Admitted.

Instance wp_struct_make_Compare `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Result' Target' Key' TargetUnion' RangeEnd' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache':
  PureWp True
    (struct.make etcdserverpb.Compare (alist_val [
      "Result" ::= #Result';
      "Target" ::= #Target';
      "Key" ::= #Key';
      "TargetUnion" ::= #TargetUnion';
      "RangeEnd" ::= #RangeEnd';
      "XXX_NoUnkeyedLiteral" ::= #XXX_NoUnkeyedLiteral';
      "XXX_unrecognized" ::= #XXX_unrecognized';
      "XXX_sizecache" ::= #XXX_sizecache'
    ]))%V
    #(Compare.mk Result' Target' Key' TargetUnion' RangeEnd' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache').
Admitted.

Module isCompare_TargetUnion.
Section def.
Context `{ffi_syntax}.
Definition t := interface.t.
End def.
End isCompare_TargetUnion.
Module TxnResponse.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Header' : loc;
  Succeeded' : bool;
  Responses' : slice.t;
  XXX_NoUnkeyedLiteral' : unit;
  XXX_unrecognized' : slice.t;
  XXX_sizecache' : w32;
}.
End def.
End TxnResponse.


Global Instance settable_TxnResponse `{ffi_syntax}: Settable _ :=
  settable! TxnResponse.mk < TxnResponse.Header'; TxnResponse.Succeeded'; TxnResponse.Responses'; TxnResponse.XXX_NoUnkeyedLiteral'; TxnResponse.XXX_unrecognized'; TxnResponse.XXX_sizecache' >.
Global Instance into_val_TxnResponse `{ffi_syntax} : IntoVal TxnResponse.t.
Admitted.

Global Instance into_val_typed_TxnResponse `{ffi_syntax} : IntoValTyped TxnResponse.t etcdserverpb.TxnResponse :=
{|
  default_val := TxnResponse.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_TxnResponse_Header `{ffi_syntax} : IntoValStructField "Header" etcdserverpb.TxnResponse TxnResponse.Header'.
Admitted.

Global Instance into_val_struct_field_TxnResponse_Succeeded `{ffi_syntax} : IntoValStructField "Succeeded" etcdserverpb.TxnResponse TxnResponse.Succeeded'.
Admitted.

Global Instance into_val_struct_field_TxnResponse_Responses `{ffi_syntax} : IntoValStructField "Responses" etcdserverpb.TxnResponse TxnResponse.Responses'.
Admitted.

Global Instance into_val_struct_field_TxnResponse_XXX_NoUnkeyedLiteral `{ffi_syntax} : IntoValStructField "XXX_NoUnkeyedLiteral" etcdserverpb.TxnResponse TxnResponse.XXX_NoUnkeyedLiteral'.
Admitted.

Global Instance into_val_struct_field_TxnResponse_XXX_unrecognized `{ffi_syntax} : IntoValStructField "XXX_unrecognized" etcdserverpb.TxnResponse TxnResponse.XXX_unrecognized'.
Admitted.

Global Instance into_val_struct_field_TxnResponse_XXX_sizecache `{ffi_syntax} : IntoValStructField "XXX_sizecache" etcdserverpb.TxnResponse TxnResponse.XXX_sizecache'.
Admitted.

Instance wp_struct_make_TxnResponse `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Header' Succeeded' Responses' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache':
  PureWp True
    (struct.make etcdserverpb.TxnResponse (alist_val [
      "Header" ::= #Header';
      "Succeeded" ::= #Succeeded';
      "Responses" ::= #Responses';
      "XXX_NoUnkeyedLiteral" ::= #XXX_NoUnkeyedLiteral';
      "XXX_unrecognized" ::= #XXX_unrecognized';
      "XXX_sizecache" ::= #XXX_sizecache'
    ]))%V
    #(TxnResponse.mk Header' Succeeded' Responses' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache').
Admitted.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.go_etcd_io.etcd.api.v3.etcdserverpb.
Require Export New.proof.proof_prelude.
Module etcdserverpb.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions etcdserverpb.pkg_name' var_addrs etcdserverpb.functions' etcdserverpb.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End defs.
End etcdserverpb.
