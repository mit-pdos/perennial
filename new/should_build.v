From New.generatedproof.github_com.goose_lang.goose.testdata.examples
  Require unittest semantics unittest.externalglobals.
(* required just to make sure this demo works *)
From New.golang.theory Require static_mem.
From New.proof Require go_etcd_io.etcd.raft.v3.
From New.proof.github_com.mit_pdos.gokv Require partialapp asyncfile lockservice globals_test.
From New.proof.github_com.goose_lang.goose.testdata.examples
  Require unittest unittest.generics.
(* TODO: change to importing the proof once that works *)
From New.proof.github_com.goose_lang.goose.testdata.examples
  Require channel.

From New.proof Require go_etcd_io.etcd.client.v3.leasing.
From New.proof Require Import bytes chan context.

Require New.generatedproof.github_com.mit_pdos.gokv.vrsm.apps.closed.

From New.proof.github_com.mit_pdos.go_journal Require
  common addr util lockmap alloc buf wal.

From New.proof Require Import inG_problem.

From New.generatedproof.github_com.sanjit_bhat.pav Require alicebob.
From New.proof.github_com.sanjit_bhat.pav Require hashchain merkle.
