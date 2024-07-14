From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import list.

(* This defines a "value map" for use in other GooseLang libraries. It does not
   provide a semantics for Go maps; for that, see map.v *)

Module vmap.
Section goose_lang.
Context {ext:ffi_syntax}.
Local Coercion Var' (s:string) : expr := Var s.

Definition Insert : val := λ: "k" "v" "m", [(Pair "k" "v") ; "m"].

Definition Get : val :=
  rec: "get" "k" "m" :=
    list.Match "m"
      (λ: <>, InjLV #()) (* [] *)
      (λ: "kv" "m",     (* kv::m *)
         let: ("k2", "v") := "kv" in
         if: "k" = "k2" then
           InjR "v"
         else
           "get" "k" "m")
.

Definition Delete : val :=
  rec: "delete" "k" "m" :=
    list.Match "m"
    (λ: <>, [])
    (λ: "kv" "m",
       let: ("k2", "v") := "kv" in
       let: "m" := "delete" "k" "m" in
       if: "k" = "k2" then "m"
       else list.Cons (Pair "k2" "v") "m"
    )
.

Definition Match : val :=
  λ: "m" "handleEmpty" "handleInsert",
    list.Match "m" "handleEmpty"
      (λ: "kv" "m",
         let: ("k", "v") := "kv" in
         "handleInsert" (Delete "m" "k") "k" "v"
      )
.

Definition val_def (m : gmap val val) :=
  list.val (map_fold (λ k v kvs, (PairV k v) :: kvs) ([] : list val) m).
Program Definition val := unseal (_:seal (@val_def)). Obligation 1. by eexists. Qed.
Definition val_unseal : val = _ := seal_eq _.
End goose_lang.
End vmap.

Notation "{[]}" := (vmap.val ∅) : expr_scope.
Notation "{[  k  :=  v  ]}" :=
  (App (App (App (Val vmap.Insert) k) v) (Val (vmap.val ∅))) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11 ; k12 := v12  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11 ; k12 := v12 ]}) : expr_scope.
Notation "{[  k1 := v1 ; k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11 ; k12 := v12 ; k13 := v13  ]}" :=
  (App (App (App (Val vmap.Insert) k1) v1) {[ k2 := v2 ; k3 := v3 ; k4 := v4 ; k5 := v5 ; k6 := v6 ; k7 := v7 ; k8 := v8 ; k9 := v9 ; k10 := v10 ; k11 := v11 ; k12 := v12 ; k13 := v13 ]}) : expr_scope.
