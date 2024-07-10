From Perennial.goose_lang Require Export lang notation proofmode wpc_proofmode.
From New.golang Require Export defn.
From New.golang.theory Require Export exception typing loop struct mem slice list.

Export uPred. (* XXX: inherited from proof_prelude.v; not sure why it's here. *)
Global Set Default Proof Using "Type".
Global Set Printing Projections.
