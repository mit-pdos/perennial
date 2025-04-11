From Perennial.goose_lang Require Export lang notation.
(* NOTE: dynamic_mem should replace mem, not used yet *)
From New.golang.defn Require dynamic_mem.
From New.golang.defn Require Export exception list typing dynamic_typing noop loop struct mem
  slice map string interface defer chan builtin array globals pkg.
Open Scope struct_scope.
