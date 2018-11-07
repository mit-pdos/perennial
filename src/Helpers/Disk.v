Require Extraction.
From SimpleClasses Require Import Classes.
From Array Require Export Array.

Set Implicit Arguments.


(** * Model of bytes.

    In our lab assignments, we will model disks as consisting of
    blocks, which are in turn composed of bytes.  Here, we define
    a notion of a byte array: the type of an array of [n] bytes
    will be [bytes n].

    There's one unusual aspect of how we model bytes: instead of
    defining the bytes type in Coq, we simply add it as an [Axiom]. This
    means we are not providing a Coq (Gallina) implementation of bytes,
    and instead we are telling Coq to assume that there exists something
    called [bytes], and there exist other functions that manipulate
    bytes that we define here as well (like [bytes_dec] to decide if two
    byte arrays are equal).

    When we generate executable code by extracting our Coq (Gallina)
    code into Haskell, we will be required to provide a Haskell
    implementation of any such [Axiom].  This correspondence is
    made below, using [Extract Constant], and we (as developers)
    are responsible for making sure any axioms we state (like
    [bsplit_bappend]) are true of our Haskell implementations.
  *)

Axiom bytes : nat -> Type.

Axiom bytes_dec : forall n, EqualDec (bytes n).
Existing Instance bytes_dec.

(**
    Two "initial" byte values: an all-zero array, [bytes0], and
    an all-ones array, [bytes1].  We also promise that all-zero
    and all-ones arrays are different, as long as there's at least
    one element.
  *)

Axiom bytes0 : forall n, bytes n.

Extraction Language Haskell.

Extract Constant bytes => "Data.ByteString.ByteString".
Extract Constant bytes_dec => "(\n b1 b2 -> b1 Prelude.== b2)".
Extract Constant bytes0 => "(\n -> Data.ByteString.replicate (Prelude.fromIntegral n) 0)".


(** * Model of blocks.

    We represent blocks as a byte array of a fixed size.

    We define the block size as a separate constant, [blockbytes], to avoid the
    literal constant [1024] reducing performance of proofs.
  *)

Definition blockbytes := 1024.

Definition block := bytes blockbytes.
Definition block0 : block := bytes0 _.

Instance bytes_default n : Default (bytes n) := bytes0 n.
Instance block_default : Default block := _.

(** Mark [blockbytes] as opaque so that Coq doesn't expand it too eagerly.
  *)

Opaque blockbytes.

Definition disk := list block.
Definition addr := nat.
