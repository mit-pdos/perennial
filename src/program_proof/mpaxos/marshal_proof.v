From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Export mpaxos.
From Perennial.program_proof Require Import marshal_stateless_proof.

Module applyAsFollowerArgs.
Section applyAsFollowerArgs.
Context `{!heapGS Σ}.

Record C :=
mkC {
  epoch : u64 ;
  nextIndex : u64 ;
  state : list u8 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)) ++ (u64_le args.(nextIndex)) ++ args.(state).

Context `{!heapGS Σ}.

Definition own args_ptr args q : iProp Σ :=
  ∃ state_sl,
  "Hargs_epoch" ∷ args_ptr ↦[mpaxos.applyAsFollowerArgs :: "epoch"]{q} #args.(epoch) ∗
  "Hargs_index" ∷ args_ptr ↦[mpaxos.applyAsFollowerArgs :: "nextIndex"]{q} #args.(nextIndex) ∗
  "Hargs_state" ∷ args_ptr ↦[mpaxos.applyAsFollowerArgs :: "state"]{q} (slice_val state_sl) ∗
  "Hargs_state_sl" ∷ is_slice_small state_sl byteT q args.(state)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) q :
  {{{
        own args_ptr args q
  }}}
    mpaxos.encodeApplyAsFollowerArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Admitted.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}
    mpaxos.decodeApplyAsFollowerArgs (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args 1
  }}}.
Admitted.

End applyAsFollowerArgs.
End applyAsFollowerArgs.

Module applyReply.
Section applyReply.
Context `{!heapGS Σ}.

Record C :=
mkC {
  err: u64 ;
  ret: list u8 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(err)) ++ args.(ret).

Context `{!heapGS Σ}.

Definition own args_ptr args q : iProp Σ :=
  ∃ ret_sl,
  "Hargs_epoch" ∷ args_ptr ↦[mpaxos.applyReply :: "err"]{q} #args.(err) ∗
  "Hargs_ret" ∷ args_ptr ↦[mpaxos.applyReply :: "ret"]{q} (slice_val ret_sl) ∗
  "Hargs_ret_sl" ∷ is_slice_small ret_sl byteT q args.(ret)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) q :
  {{{
        own args_ptr args q
  }}}
    mpaxos.encodeApplyAsFollowerArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Admitted.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}
    mpaxos.decodeApplyAsFollowerArgs (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args 1
  }}}.
Admitted.

End applyReply.
End applyReply.
