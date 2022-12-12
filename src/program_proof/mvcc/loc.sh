#!/bin/bash

echo "Tuple:"
wc -l tuple*.v

echo "Transaction:"
wc -l txn*.v wrbuf*.v

echo "Index:"
wc -l index*.v

echo "Timestamp generation:"
wc -l tid*.v

echo "Misc:"
wc -l mvcc_prelude.v mvcc_misc.v

echo "Ghost states:"
wc -l mvcc_ghost.v

echo "Global invariants:"
wc -l mvcc_inv.v mvcc_action.v mvcc_tuplext.v proph_proof.v

echo "Not counted: mvcc_proof.v examples_proof.v print_assumptions.v"
