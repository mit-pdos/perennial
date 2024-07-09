From New.golang.defn Require Import mem list.

Declare Scope struct_scope.
Notation "f :: t" := (@pair string go_type f%string t) : struct_scope.
Notation "f ::= v" := (PairV #(str f%string) v%V) (at level 60) : val_scope.
Notation "f ::= v" := (Pair #(str f%string) v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.

Module struct.
Section goose_lang.
Infix "=?" := (String.eqb).

Context `{ffi_syntax}.
Local Coercion Var' (s:string) : expr := Var s.

Fixpoint field_offset (d : struct.descriptor) f0 : (Z * go_type) :=
  match d with
  | [] => (-1, ptrT)
  | (f,t)::fs => if f =? f0 then (0, t)
               else match field_offset fs f0 with
                    | (off, t') => ((go_type_size t) + off, t')
                    end
  end.

Definition field_ref (d : struct.descriptor) f0: val :=
  λ: "p", BinOp (OffsetOp (field_offset d f0).1) (Var "p") #1.

Definition field_ty d f0 : go_type := (field_offset d f0).2.

Local Definition assocl_lookup_goose : val :=
  rec: "assocl_lookup" "fvs" "f" :=
    list.Match "fvs"
              (λ: <>, InjLV #())
              (λ: "fv" "fvs",
                 let: ("f'", "v") := "fv" in
                 if: "f" = "f'" then InjR "v" else "assocl_lookup" "fvs" "f").

Fixpoint make_def (d : struct.descriptor) : val :=
  match d with
  | [] => λ: "fvs", Val #()
  | (f,ft)::fs => λ: "fvs", Val #() (Match (assocl_lookup_goose "fvs" f) <> (Val (zero_val ft)) "x" "x",
                                     (make_def fs) "fvs")
  end.
Program Definition make := unseal (_:seal (@make_def)). Obligation 1. by eexists. Qed.
Definition make_unseal : make = _ := seal_eq _.

End goose_lang.
End struct.
