Require Import Arith.
Require Import Disk.

Set Implicit Arguments.

(* disk layout:

| log header (1 block) | descriptor block (1 block) |
| log value region (LOG_LENGTH blocks; see below) | data region |
*)

(* The descriptor block encodes 32-bit addresses; it fits 1024byte/32bits = 256
addresses. *)
Definition LOG_LENGTH: nat := 256.
Opaque LOG_LENGTH.
Definition __log_length_calculation: LOG_LENGTH = blockbytes / 4
  := eq_refl.

Record LogHdr :=
  { committed: bool;
    log_length: nat;
    log_length_ok: log_length <= LOG_LENGTH; }.

Record Descriptor :=
  { addresses: list addr;
    (* TODO: restrict addrs to be < 2^32 for encoding in one block *)
    addresses_length:
      length addresses = LOG_LENGTH; }.

Record block_encoder T :=
  { encode: T -> block;
    decode: block -> T;
    encode_decode: forall (x:T), decode (encode x) = x; }.
