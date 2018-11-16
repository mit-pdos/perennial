# Client for using logging on two unreliable disks

To extract the logging example, run `make extract` at the root. Then compile the
`logging-cli` binary using
[stack](https://docs.haskellstack.org/en/stable/README/) by running `stack
build` in this directory (you may need to run `stack setup` to initially
download a sandboxed version of GHC).

The implementation operates on a two-disk API with two disks, one of which is
allowed to fail at any time according to the model used by the proof. The
replicated disk is simulated using two files `disk0.img` and `disk1.img`.

You can run the binary with `stack exec -- logging-cli`. It has the following
operations (all of which support `--help`):

- `logging-cli init` initializes the two disks, replication, and logging; the two disks are hosted in files disk0.img and disk1.img (by default 1MB each)
- `logging-cli read a` reads block `a` as an integer
- `logging-cli write a v` writes the number `v` to block `a` in the current transaction. The log can hold 256 writes, after which wriets will fail
- `logging-cli commit` commits the current transaction
- `logging-cli recover` recovers from a crash and aborts any in-progress and uncommitted transaction

You can run `./demo.sh` to see the operations illustrated:

```text
$ ./demo.sh
> init
# basic interaction
> read 0
0
> write 0 10
## reads use the persistent state
> read 0
0
> write 1 12
> write 3 15
## out-of-bounds writes silently do nothing
> write 1000000000 15
> commit
> recover
> read 0
10
> read 1
12
> read 3
15
> read 1000000000
0

# aborting a transaction, replication
> write 1 12
> write 3 25
## "fail" one of the disks
rm disk0.img
> write 100 7
## to simulate a crash we run recovery
> recover
> read 0
10
> read 1
12
> read 3
15
> read 100
0

## cleanup
rm disk1.img
```
