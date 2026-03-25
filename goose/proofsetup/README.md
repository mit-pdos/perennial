# proof-setup

used alongside `goose` and `proofgen`.  
example usage:
```shell
goose -dir go -out src ./...
proofgen -dir go -out src -configdir src/code ./...
proof-setup -dir go -out src ./...
```
the _RocqProject file will need the following flags at least:
```
-Q src/code New.code
-Q src/generatedproof New.generatedproof
-Q src/proof New.proof
```
alongside any additional flags that are needed for building and for perennial
