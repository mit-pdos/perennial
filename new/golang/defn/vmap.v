From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import list.

Module vmap.
Section goose_lang.
Context {ext:ffi_syntax}.
Local Coercion Var' (s:string) : expr := Var s.

Definition Insert : val :=
  rec: "insert" "k" "v" "m" :=
    list.Match "m"
      (λ: <>, [(Pair "k" "v")])
      (λ: "kv" "m2",
         let: ("k2", "v2") := "kv" in
         if: (TotalLe "k" "k2") then
           if: (TotalLe "k2" "k") then (* k2 = k *)
             list.Cons (Pair "k" "v") "m2"
           else (* k < k2 *)
             list.Cons (Pair "k" "v") "m"
         else
           list.Cons (Pair "k2" "v2") ("insert" "k" "v" "m")
      ).

Definition Get : val :=
  rec: "get" "k" "m" :=
    list.Match "m"
      (λ: <>, InjLV #()) (* [] *)
      (λ: "kv" "m",     (* kv::m *)
         let: ("k2", "v") := "kv" in
         if: "k" = "k2" then
           InjR "v"
         else
           "get" "k" "m").

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

Fixpoint insert_replace_sorted {A} (le : A → A → bool) (a : A) (l : list A) :=
  match l with
  | [] => [a]
  | h :: t => if (le a h) then
        if (le h a) then a :: t
        else a :: h :: t
      else h :: insert_replace_sorted le a t
  end.

Local Definition val_list_def (m : gmap val val) :=
  (fmap (λ '(a, b), PairV a b)
     (map_fold (λ k v kvs, insert_replace_sorted (λ '(a, _) '(b, _), val_le a b)
                             (k, v) kvs)
        ([] : list (val * val)) m))
.
Definition val_def (m : gmap val val) :=
  list.val (val_list_def m).

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
