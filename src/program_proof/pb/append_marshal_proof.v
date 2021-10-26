From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.

Section append_marshal_proof.
(* TODO: move to a different file *)
Record AppendArgsC :=
{
  AA_cn:u64;
  AA_commitIdx: u64;
  AA_log: list u8;
}.

Definition own_AppendArgs (args_ptr:loc) (args:AppendArgsC) : iProp Σ :=
  ∃ (log_sl:Slice.t),
  "HAcn" ∷ args_ptr ↦[AppendArgs :: "cn"] #args.(AA_cn) ∗
  "HAcommitIdx" ∷ args_ptr ↦[AppendArgs :: "commitIdx"] #args.(AA_commitIdx) ∗
  "HAlog" ∷ args_ptr ↦[AppendArgs :: "log"] (slice_val log_sl) ∗
  "HAlog_slice" ∷ is_slice log_sl byteT 1%Qp args.(AA_log)
.

End append_marshal_proof.
