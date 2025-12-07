From New.generatedproof.github_com.goose_lang.goose.testdata.examples
  Require semantics unittest.externalglobals.
From New.generatedproof Require math.rand testing unsafe.

From New.generatedproof.github_com.stretchr.testify Require assert.

From New.proof Require Import bytes chan context sort slices runtime.

(* required just to make sure this demo works *)
From New.golang.theory Require static_mem.
From New.proof Require go_etcd_io.raft.v3.
From New.proof.github_com.mit_pdos.gokv Require gokv.
From New.proof.github_com.goose_lang.goose.testdata.examples
  Require unittest unittest.generics.
From New.proof.github_com.goose_lang.goose.testdata.examples
  Require channel channel_search_replace elimination_stack.

From New.proof.github_com.goose_lang.goose.model.channel.protocol
  Require protocols.
(* From New.proof.github_com.goose_lang.goose.model.channel.logatom
  Require chan_au_sel. *)

From New.proof Require go_etcd_io.etcd.client.v3.leasing leasing_proof.protocol.

Require New.generatedproof.github_com.mit_pdos.gokv.vrsm.apps.closed.

From New.proof.github_com.mit_pdos.go_journal Require
  common addr util lockmap alloc buf wal.

From New.proof Require Import inG_problem.

From New.proof.github_com.sanjit_bhat.pav Require alicebob.
From New.proof.github_com.sanjit_bhat.pav.experiments Require should_build.

Require New.proof.go_etcd_io.etcd.server.v3.etcdserver.

(* might not be maintained going forward but do currently build *)
From New.experiments Require all_scmra all_ucmra chan lang records.
