#!/bin/bash

CLOC="cloc --include-lang=Coq --quiet"

$CLOC . ../rsm/pure ../rsm/big_sep.v

echo "Transaction:"
$CLOC --not-match-f='(encode|decode)' ./program/txn ./program/gcoord

echo "Backup coordinator:"
$CLOC ./program/backup

echo "Replica:"
$CLOC --not-match-f='(encode|decode)' ./program/replica

echo "Transaction log:"
$CLOC ./program/txnlog

echo "Paxos:"
$CLOC ./paxos

echo "Tuple:"
$CLOC ./program/tuple ./program/index

echo "Message:"
$CLOC --match-f='(encode|decode)' ./program/gcoord ./program/replica

echo "Misc:"
$CLOC ./program/prelude.v ./program/quorum.v ./program/util

echo "Invariance proofs:"
$CLOC ./invariance

echo "Invariant/resource definitions:"
$CLOC ./*.v

echo "General lemmas:"
$CLOC ../rsm/pure ../rsm/big_sep.v
