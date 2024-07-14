From New.golang.defn Require Import mem list vmap.

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

Definition field_offset (t : go_type) f0 : (Z * go_type) :=
  match t with
  | structT d =>
      (fix field_offset_struct (d : struct.descriptor) : (Z * go_type) :=
         match d with
         | [] => (-1, badT)
         | (f,t)::fs => if f =? f0 then (0, t)
                      else match field_offset_struct fs with
                           | (off, t') => ((go_type_size t) + off, t')
                           end
         end) d
  | _ => (-1, badT)
  end
.

Definition field_ref (t : go_type) f0 : val :=
  λ: "p", BinOp (OffsetOp (field_offset t f0).1) (Var "p") #1.

Definition field_ty d f0 : go_type := (field_offset d f0).2.

Definition field_get_def (t : go_type) f : val :=
  match t with
  | structT d =>
      (fix field_get_struct fs :=
         match fs with
         | (f',_)::fs =>
             if f' =? f then
               (λ: "s", Fst "s")%V
             else
               (λ: "s", field_get_struct fs f (Snd "s"))%V
         | [] => LitV LitPoison
         end
      ) d
  | _ => LitV LitPoison
  end.
Program Definition field_get := unseal (_:seal (@field_get_def)). Obligation 1. by eexists. Qed.
Definition field_get_unseal : field_get = _ := seal_eq _.

Definition make_def (t : go_type) : val :=
  match t with
  | structT d =>
      (fix make_def_struct (fs : struct.descriptor) : val :=
         match fs with
         | [] => (λ: "fvs", Val #())%V
         | (f,ft)::fs => (λ: "fvs", Val #() (Match (vmap.Get "fvs" #(str f)) <> (Val (zero_val ft)) "x" "x",
                                            (make_def_struct fs) "fvs"))%V
         end) d
  | _ => LitV $ LitPoison
  end.
Program Definition make := unseal (_:seal (@make_def)). Obligation 1. by eexists. Qed.
Definition make_unseal : make = _ := seal_eq _.

End goose_lang.
End struct.
