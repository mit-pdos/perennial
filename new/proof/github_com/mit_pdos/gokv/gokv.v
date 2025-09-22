(* Ported Proofs *)
From New.proof.github_com.mit_pdos.gokv Require partialapp asyncfile lockservice globals_test.
(* Grackle generated marshaling proofs *)
From New.proof.github_com.mit_pdos.gokv.cachekv Require cachevalue_proof_gk.
From New.proof.github_com.mit_pdos.gokv.fencing.ctr Require error_proof_gk getargs_proof_gk getreply_proof_gk putargs_proof_gk.
From New.proof.github_com.mit_pdos.gokv.memkv Require conditionalputreply_proof_gk conditionalputrequest_proof_gk error_proof_gk getreply_proof_gk getrequest_proof_gk kvop_proof_gk moveshardrequest_proof_gk putreply_proof_gk putrequest_proof_gk shardmap_proof_gk.
From New.proof.github_com.mit_pdos.gokv.paxi.comulti Require preparereply_proof_gk proposeargs_proof_gk.
From New.proof.github_com.mit_pdos.gokv.paxi.reconf Require config_proof_gk error_proof_gk monotonicvalue_proof_gk preparereply_proof_gk proposeargs_proof_gk trycommitreply_proof_gk.
From New.proof.github_com.mit_pdos.gokv.reconfig.replica Require appendargs_proof_gk becomeprimaryargs_proof_gk becomereplicaargs_proof_gk configuration_proof_gk error_proof_gk getlogreply_proof_gk logentry_proof_gk.
From New.proof.github_com.mit_pdos.gokv.reconfig.util Require configuration_proof_gk.
From New.proof.github_com.mit_pdos.gokv.tutorial.kvservice Require conditionalput_proof_gk get_proof_gk put_proof_gk.
From New.proof.github_com.mit_pdos.gokv.tutorial.lockservice Require lockrequest_proof_gk.
From New.proof.github_com.mit_pdos.gokv.tutorial.objectstore.chunk Require writechunk_proof_gk.
From New.proof.github_com.mit_pdos.gokv.tutorial.objectstore.dir Require chunkhandle_proof_gk finishwrite_proof_gk preparedread_proof_gk preparedwrite_proof_gk recordchunk_proof_gk.
From New.proof.github_com.mit_pdos.gokv.vrsm.apps.vkv Require condputargs_proof_gk getargs_proof_gk putargs_proof_gk.
From New.proof.github_com.mit_pdos.gokv.vrsm.configservice Require config_proof_gk state_proof_gk.
From New.proof.github_com.mit_pdos.gokv.vrsm.paxos Require applyasfollowerargs_proof_gk applyasfollowerreply_proof_gk applyreply_proof_gk enternewepochargs_proof_gk enternewepochreply_proof_gk error_proof_gk paxosstate_proof_gk.
From New.proof.github_com.mit_pdos.gokv.vrsm.replica Require applyasbackupargs_proof_gk applyreply_proof_gk becomeprimaryargs_proof_gk err_proof_gk getstateargs_proof_gk getstatereply_proof_gk increasecommitargs_proof_gk setstateargs_proof_gk.

