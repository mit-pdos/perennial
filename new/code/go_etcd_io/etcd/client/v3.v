(* autogenerated from go.etcd.io/etcd/client/v3 *)
From New.golang Require Import defn.
Require Export New.code.go_etcd_io.etcd.api.v3.etcdserverpb.
Require Export New.code.go_etcd_io.etcd.api.v3.mvccpb.

Module clientv3.
Section code.
Context `{ffi_syntax}.


Axiom ErrNoAvailableEndpoints'init : val.

Axiom ErrOldCluster'init : val.

Axiom Client : go_type.

Definition Cluster : go_type := interfaceT.

Definition Cmp : go_type := etcdserverpb.Compare.

Definition PutResponse : go_type := etcdserverpb.PutResponse.

Definition GetResponse : go_type := etcdserverpb.RangeResponse.

Definition DeleteResponse : go_type := etcdserverpb.DeleteRangeResponse.

Definition TxnResponse : go_type := etcdserverpb.TxnResponse.

Definition KV : go_type := interfaceT.

Definition OpResponse : go_type := structT [
  "put" :: ptrT;
  "get" :: ptrT;
  "del" :: ptrT;
  "txn" :: ptrT
].

Definition LeaseID : go_type := int64T.

Definition LeaseGrantResponse : go_type := structT [
  "ResponseHeader" :: ptrT;
  "ID" :: LeaseID;
  "TTL" :: int64T;
  "Error" :: stringT
].

Definition NoLease : expr := #(W64 0).

Axiom LeaseResponseChSize'init : val.

Definition Lease : go_type := interfaceT.

Axiom noPrefixEnd'init : val.

Axiom Op : go_type.

Definition OpOption : go_type := funcT.

Axiom defaultWaitForReady'init : val.

Axiom defaultMaxCallSendMsgSize'init : val.

Axiom defaultMaxCallRecvMsgSize'init : val.

Axiom defaultUnaryMaxRetries'init : val.

Axiom defaultStreamMaxRetries'init : val.

Axiom defaultBackoffWaitBetween'init : val.

Axiom defaultBackoffJitterFraction'init : val.

Axiom defaultCallOpts'init : val.

Axiom defaultOptions'init : val.

Definition Txn : go_type := interfaceT.

Definition EventTypeDelete : expr := mvccpb.DELETE.

Definition Event : go_type := mvccpb.Event.

Definition WatchResponse : go_type := structT [
  "Header" :: etcdserverpb.ResponseHeader;
  "Events" :: sliceT;
  "CompactRevision" :: int64T;
  "Canceled" :: boolT;
  "Created" :: boolT;
  "closeErr" :: error;
  "cancelReason" :: stringT
].

Definition WatchChan : go_type := chanT WatchResponse.

Definition Watcher : go_type := interfaceT.

Axiom valCtxCh'init : val.

Axiom zeroTime'init : val.

Axiom maxBackoff'init : val.

Definition pkg_name' : go_string := "go.etcd.io/etcd/client/v3".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [("Cmp"%go, []); ("Cmp'ptr"%go, []); ("PutResponse"%go, []); ("PutResponse'ptr"%go, []); ("GetResponse"%go, []); ("GetResponse'ptr"%go, []); ("DeleteResponse"%go, []); ("DeleteResponse'ptr"%go, []); ("TxnResponse"%go, []); ("TxnResponse'ptr"%go, []); ("OpResponse"%go, []); ("OpResponse'ptr"%go, []); ("LeaseID"%go, []); ("LeaseID'ptr"%go, []); ("LeaseGrantResponse"%go, []); ("LeaseGrantResponse'ptr"%go, []); ("OpOption"%go, []); ("OpOption'ptr"%go, []); ("Event"%go, []); ("Event'ptr"%go, []); ("WatchChan"%go, []); ("WatchChan'ptr"%go, []); ("WatchResponse"%go, []); ("WatchResponse'ptr"%go, [])].

#[global] Instance info' : PkgInfo pkg_name' :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [etcdserverpb.pkg_name'; mvccpb.pkg_name'];
  |}.

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' (λ: <>,
      exception_do (do:  mvccpb.initialize';;;
      do:  etcdserverpb.initialize';;;
      do:  (ErrNoAvailableEndpoints'init #());;;
      do:  (ErrOldCluster'init #());;;
      do:  (LeaseResponseChSize'init #());;;
      do:  (noPrefixEnd'init #());;;
      do:  (defaultWaitForReady'init #());;;
      do:  (defaultMaxCallSendMsgSize'init #());;;
      do:  (defaultMaxCallRecvMsgSize'init #());;;
      do:  (defaultUnaryMaxRetries'init #());;;
      do:  (defaultStreamMaxRetries'init #());;;
      do:  (defaultBackoffWaitBetween'init #());;;
      do:  (defaultBackoffJitterFraction'init #());;;
      do:  (defaultCallOpts'init #());;;
      do:  (defaultOptions'init #());;;
      do:  (valCtxCh'init #());;;
      do:  (zeroTime'init #());;;
      do:  (maxBackoff'init #()))
      ).

End code.
End clientv3.
