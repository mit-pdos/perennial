# Extraction benchmarking

To get some nice plots:

```
stack build
stack exec extraction-bench -- -o criterion-write.html +RTS -N2 -RTS 'write'
stack exec extraction-bench -- -o criterion-read.html +RTS -N2 -RTS 'read'
```

Note that multiple runs within the same invocation are affected by each other due to GC effects.
