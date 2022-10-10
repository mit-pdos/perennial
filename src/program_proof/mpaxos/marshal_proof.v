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

Definition own args_ptr args : iProp Σ :=
  ∃ state_sl,
  "#Hargs_epoch" ∷ readonly (args_ptr ↦[mpaxos.applyAsFollowerArgs :: "epoch"] #args.(epoch)) ∗
  "#Hargs_index" ∷ readonly (args_ptr ↦[mpaxos.applyAsFollowerArgs :: "nextIndex"] #args.(nextIndex)) ∗
  "#Hargs_state" ∷ readonly (args_ptr ↦[mpaxos.applyAsFollowerArgs :: "state"] (slice_val state_sl)) ∗
  "#Hargs_state_sl" ∷ readonly (is_slice_small state_sl byteT 1 args.(state))
  .

Lemma wp_Encode (args_ptr:loc) (args:C) :
  {{{
        own args_ptr args
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
        args_ptr, RET #args_ptr; own args_ptr args
  }}}.
Admitted.

End applyAsFollowerArgs.
End applyAsFollowerArgs.

Module applyAsFollowerReply.
Section applyAsFollowerReply.
Context `{!heapGS Σ}.

Record C :=
mkC {
  err: u64 ;
}.

Definition has_encoding (encoded:list u8) (reply:C) : Prop :=
  encoded = (u64_le reply.(err)).

Context `{!heapGS Σ}.

Definition own reply_ptr reply q : iProp Σ :=
  "Hreply_err" ∷ reply_ptr ↦[mpaxos.applyAsFollowerReply :: "err"]{q} #reply.(err)
  .

Lemma wp_Encode (reply_ptr:loc) (reply:C) q :
  {{{
        own reply_ptr reply q
  }}}
    mpaxos.encodeApplyAsFollowerReply #reply_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc reply⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Admitted.

Lemma wp_Decode enc enc_sl (reply:C) :
  {{{
        ⌜has_encoding enc reply⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}
    mpaxos.decodeApplyAsFollowerReply (slice_val enc_sl)
  {{{
        reply_ptr, RET #reply_ptr; own reply_ptr reply 1
  }}}.
Admitted.

End applyAsFollowerReply.
End applyAsFollowerReply.

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
  "Hreply_epoch" ∷ args_ptr ↦[mpaxos.applyReply :: "err"]{q} #args.(err) ∗
  "Hreply_ret" ∷ args_ptr ↦[mpaxos.applyReply :: "ret"]{q} (slice_val ret_sl) ∗
  "Hreply_ret_sl" ∷ is_slice_small ret_sl byteT q args.(ret)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) q :
  {{{
        own args_ptr args q
  }}}
    mpaxos.encodeApplyReply #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Admitted.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        is_slice_small enc_sl byteT 1 enc
  }}}
    mpaxos.decodeApplyReply (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args 1
  }}}.
Admitted.

End applyReply.
End applyReply.
