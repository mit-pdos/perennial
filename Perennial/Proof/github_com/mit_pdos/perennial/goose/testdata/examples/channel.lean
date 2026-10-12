/-
The proofs of the goose channel examples (package `channel`): hedged requests,
hello-world futures, cancellation, joins, pointer exchange and broadcast examples,
Fibonacci numbers over an SPSC channel, the Google search, higher-order workers and
tricky nonblocking `select`s, using the channel idioms (bag, handshake, broadcast,
future, spsc). The shared definitions (`Base`, `FibonacciDefs`, `GoogleDefs`,
`HigherOrderDefs`, `SelectTrickyDefs`) and the linked results (`Link`), `wp_<F>` for
each function `F`.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.FibonacciDefs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.GoogleDefs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HigherOrderDefs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.SelectTrickyDefs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Link

@[expose] public section
