# Extraction benchmarking

To get some nice plots:

```
stack build
stack exec extraction-bench -- -o criterion-write.html +RTS -N2 -RTS 'hashtable/write'
stack exec extraction-bench -- -o criterion-ht-read.html +RTS -N2 -RTS 'hashtable/read'
stack exec extraction-bench -- -o criterion-append.html +RTS -N2 -RTS 'array/append'
stack exec extraction-bench -- -o criterion-array-read.html +RTS -N2 -RTS 'array/read'
```

Note that multiple runs within the same invocation are affected by each other due to GC effects.
