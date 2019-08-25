---
title: "Armada artifact experiments"
---

[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

We don't have performance evaluation experiments in the way a traditional
systems paper might, so instead we organize this file into the claims made in
the paper's evaluation and how you might evaluate them.

## Implementation lines of code

Table 2 and Table 3 divide Armada into several groups and list lines of code for
each. You can generate these tables by running `~/armada-artifact/armada-paper/loc.py ~/armada ~/go/src/github.com/tchajed/goose`. The lines-of-code script takes a `--debug`
flag to print all of the matching files for each category.

Table 4 compares lines of code between Mailboat and CMAIL. The Mailboat numbers
come from the following:

- Implementation: `cloc ~/mailboat/mailboat.go`
- Proof: `~/armada-artifact/armada-paper/loc.py --debug ~/armada ~/go/src/github.com/tchajed/goose` includes a section for "Mailboat proof",
  though this is not automatically emitted to LaTeX.
- Framework: round the Armada total from Table 2.

The CMAIL numbers are derived from the [CSPEC
paper](https://pdos.csail.mit.edu/papers/cspec.pdf). We did some post-processing
on Figure 14 and Figure 18. To run these calculations run
`~/armada-artifact/armada-paper/cmail_loc.py`, and run
`~/armada-artifact/armada-paper/cmail_loc.py --help` to get a description of
where those numbers come from.

## Crash safety examples

Section 8.1 talks about several verified examples, which are in
`~/armada/src/Examples`.

We mention that recovery reclaims space by deleting temp file; the code for this
is in [mailboat.go's Recover function](https://github.com/tchajed/mailboat/blob/d7e4be5abf767edfa178efbbcfed8179a3a39afd/mailboat.go#L173-L184).
The specification can't capture this, and write crash-testing infrastructure to
directly exercise it, but the code is fairly simple and the proof shows that
these deletes are essentially invisible to the user.

## Trusted computing base

Section 8.2 discusses what assumptions the correctness proof relies on. One
assumption to check is to look over the Goose semantics (described in the paper
in Section 6.2) and compare it to an informal understanding of Go. These
semantics are defined in `~/armada/src/Goose`, especially `Heap.v` and
`Filesys.v`. For `Filesys.v`, compare against the Goose file-system library at
`~/goose/machine/filesys`, especially `dir.go` which implements the file-system
API using syscalls to the operating system (as opposed to an in-memory
filesystem we use only for internal tests). The Go part of the implementation is
small; the real trust is in the semantics of the underlying filesystem.

Another component of the TCB is Goose. The Goose implementation attempts to
carefully narrow the scope of supported code so that the model is faithful. One
to evaluate this is to look over the test suite for Goose. The examples are run
via `~/goose/examples_test.go`. There are two types of tests: `testdata/` has
negative tests that Goose should reject (along with annotations for the correct
error message), and `internal/examples` has three packages that Goose should
build along with expected golden output. `examples/unittest` has a variety of
small functions, `mailserver` is a copy of Mailboat, and `simpledb` is a
key-value store we were working on but which has no proof.

The goose output for these examples is also in `~/armada/src/Goose/Examples/`,
where it builds with Coq using the Armada Makefile. Some of the checks necessary
for the Goose model to be accurate aren't performed in the translation but
produce code that doesn't type check in Coq.

## Mailboat

One useful evaluation of Mailboat is to read its specification, which is at
`~/armada/src/Examples/MailServer/MailAPI.v`.

Note that Goose isn't technically part of the Mailboat build process - instead,
for convenience, we commit the output of Goose to
`~/armada/src/Goose/Examples/MailServer.v`. You should re-run Goose, which will
re-generate the file exactly:

```
goose -out ~/armada/src/Goose/Examples/MailServer.v ~/go/src/github.com/tchajed/mailboat
```

## Mailboat performance evaluation

Figure 11 shows the throughput of Mailboat as we vary the number of cores
delivering messages. We compare against two baselines: CMAIL, a verified mail
server without a proof of crash safety, and GoMail, an unverified baseline used
in the CSPEC paper to evaluate CMAIL. Mailboat is written in Go but is not the
same as GoMail (and indeed it achieves even better performance).

This graph is annoying to reproduce due to the software required to run the
three systems (Go, Coq, and Haskell Stack) and the need for real hardware as
opposed to a virtual machine (in fact, these numbers are from a machine with 12
physical cores). For the software, you can run Mailboat and GoMail relatively
easily with just Go. For the hardware, even in a VM you can conclude that
Mailboat gets faster with more cores (though it isn't as scalable), and it has
performance comparable to GoMail and CMAIL (although the performance difference
isn't as dramatic).

The graph is generated by running `cd ~/armada-artifact/armada-paper; gnuplot -e 'numcores=12' mailboat.plot`; the script has been adjusted slightly to output a
PNG rather than a TikZ figure. We include the data used to generate the plot in
the paper. To run the benchmark and re-generate the data, run:

```
~/armada-artifact/armada-paper/get-data.sh ~/mailboat/scripts/run-mailboat.sh 12 > ~/armada-artifact/armada-paper/mailboat.data
~/armada-artifact/armada-paper/get-data.sh ~/cspec/scripts/run-mailserver.sh 12 > ~/armada-artifact/armada-paper/cmail.data
~/armada-artifact/armada-paper/get-data.sh ~/cspec/scripts/run-gomail.sh 12 > ~/armada-artifact/armada-paper/gomail.data
```

You can also replace 12 with a smaller number to test up to a smaller number of
threads. In that case, replace the number of cores in the call to `gnuplot`
(this only affects the scaling of requests/sec).

## Bugs discussion

The two bugs mentioned in the paper are
https://github.com/tchajed/mailboat/commit/15e15a3a (resulting in an infinite
loop in `Pickup`) and https://github.com/tchajed/mailboat/commit/e80f1eb2
(resulting in running out of file descriptors after delivering too many
messages). The first bug comes with a test case which will fail by running out
of memory if you revert the fix. You can introduce the bug in
`~/mailboat/mailboat.go` and then run `go test github.com/tchajed/mailboat`. The
second bug isn't as easy to reproduce, but it's pretty easy to see what went wrong.

## Mailboat compatibility

We tested the mailboat server by running postal, a benchmark suite for mail
servers. Note that this tests both the verified mail server library as well as
the unverified server code, including SMTP and POP3 handling. We didn't find
bugs in the verified component by running postal, but our initial server
implementation unsurprisingly didn't work with postal (or rabid, a tool
distributed with postal to test email retrieval).

We provide a user-list with the first five users in the artifact release.

```sh
$ mailboat-server
$ # in another shell instance:
$ postal -t 2 -r 120 -p 2525 -s 0 -c 100 localhost ~/armada-artifact/user-list
$ # kill postal at some point, then run:
$ rabid -p 2 -i 0 -d 100:0 -z debug '[localhost]2110' ~/armada-artifact/user-list
$ # kill rabid at some point
$ # run this to also mix in some deletes (70%/30% split of downloads and deletes)
$ rabid -p 2 -i 0 -d 70:30 -z debug '[localhost]2110' ~/armada-artifact/user-list
```

You can also restart the server by killing it and running `mailboat-server --recover`, especially between running postal to deliver mail and rabid to
retrieve it.

The files `postal.log` and `rabid.log` record what each tool is doing. Postal
records the MD5 of the email it sends, while rabid just records a sequence of
MD5 hashes it has retrieved.

You can check that things are working by looking at the output of `postal`,
which should emit a status line every minute of the form:

```
time,messages,data(K),errors,connections,SSL connections
01:17,10,62,0,2,0
```

The third column from the right should be 0 (no errors), and it should deliver a
few messages.

Rabid doesn't print anything out (not sure why), but the file `rabid.log` should
have a list of hashes of the mail rabid retrieved, and `debug:1` and
`debug:2` have a detailed log of all POP3 traffic.

If you want to see the internal details, the terminal with `mailboat-server`
will also print some logging messages, and you can see the stored messages in
`/tmp/mailboat/user[0-4]`. The messages are briefly spooled in
`/tmp/mailboat/spool`.
