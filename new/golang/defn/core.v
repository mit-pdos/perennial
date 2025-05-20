(* a set of "core" libraries for goose code, intended to bootstrap models that
are written in Go and translated with goose *)
From Perennial.goose_lang Require Export lang notation.
From New.golang.defn Require Export
  typing dynamic_typing globals exception
  mem struct pkg loop list.
Open Scope struct_scope.
