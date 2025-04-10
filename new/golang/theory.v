From Perennial.goose_lang Require Export lang.
From New.golang Require Export defn.
(* NOTE: unused for now but still should be compiled *)
From New.golang.theory Require dynamic_mem.
From New.golang.theory Require Export exception list typing dynamic_typing loop struct
  mem slice map interface defer typing builtin primitive chan pkg auto globals.

Export uPred. (* XXX: inherited from proof_prelude.v; not sure why it's here. *)
Global Set Default Proof Using "Type".
Global Set Printing Projections.
