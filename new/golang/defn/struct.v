From New.golang.defn Require Import mem.

Declare Scope struct_scope.
Notation "f :: t" := (@pair string go_type f%string t) : struct_scope.
Notation "f ::= v" := (@pair string val f%string v%V) (at level 60) : val_scope.
Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.

Module struct.
Section goose_lang.
Infix "=?" := (String.eqb).

Context `{ffi_syntax}.
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

Fixpoint make_def (d : struct.descriptor) (field_vals: list (string*expr)) : expr :=
  match d with
  | [] => Val #()
  | (f,ft)::fs => (default (Val (zero_val ft)) (assocl_lookup field_vals f), make_def fs field_vals)
  end.
Program Definition make := unseal (_:seal (@make_def)). Obligation 1. by eexists. Qed.
Definition make_unseal : make = _ := seal_eq _.

Local Definition assocl_lookup_goose : val :=
  λ: "fvs" "f",

Fixpoint make2_def (d : struct.descriptor) : expr :=
  λ: "fvs",
    match d with
    | [] => Val #()
    | (f,ft)::fs =>
        if:
        (default (Val (zero_val ft)) (assocl_lookup field_vals f), make2_def fs field_vals)
    end.
Program Definition make := unseal (_:seal (@make_def)). Obligation 1. by eexists. Qed.
Definition make_unseal : make = _ := seal_eq _.

End goose_lang.
End struct.
