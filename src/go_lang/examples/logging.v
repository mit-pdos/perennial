From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Export ffi.disk.
From Perennial.go_lang Require Import proofmode notation.

Existing Instances disk_op disk_model disk_semantics disk_interp.

Coercion Var' (s: string) : expr := Var s.

Definition init (sz: u64): val :=
  λ: <>,
  let: "hdr" := AllocN #4096 #(LitByte 0) in
  EncodeInt #0 "hdr";;
  EncodeInt #(LitInt sz) ("hdr" +ₗ #8);;
  ExternalOp Write (#0, "sz_buf").
