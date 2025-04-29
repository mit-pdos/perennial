From New.code.go_etcd_io.raft Require v3.
From New.code.github_com.goose_lang.goose.testdata.examples Require unittest semantics.
(* required just to make sure this demo works *)
From New.golang.theory Require static_mem.
From New.proof Require go_etcd_io.etcd.raft.v3.
From New.proof.github_com.mit_pdos Require partialapp asyncfile lockservice globals_test.

(* FIXME: keeping this out because of universe inconsistency. *)
(* From New.proof Require go_etcd_io.etcd.client.v3.concurrency. *)
(* in the meantime, at least check goose output  *)
From New.generatedproof.go_etcd_io.etcd
  Require client.v3.leasing client.v3.concurrency.
From New.proof Require Import chan context.

Require New.generatedproof.github_com.mit_pdos.gokv.vrsm.apps.closed.
