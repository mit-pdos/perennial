From Perennial.goose_lang Require Export lang.
From New.golang Require Export defn.
(* required just to make sure this demo works *)
From New.golang.theory Require mem.
From New.golang.theory Require Export exception list typing dynamic_typing loop struct
  slice map interface defer typing builtin primitive chan pkg auto globals.
From New.golang.theory Require Export typed_pointsto dynamic_mem.
From Perennial Require Export base.

Export uPred. (* XXX: inherited from proof_prelude.v; not sure why it's here. *)
Global Set Default Proof Using "Type".
Global Set Printing Projections.
