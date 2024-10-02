From New.golang.defn Require Import mem list.

(* FIXME: these notations don't work properly. *)
Declare Scope struct_scope.
Notation "f :: t" := (@pair string go_type f%string t) : struct_scope.
Notation "f ::= v" := (PairV #(f%string) v%V) (at level 60) : val_scope.
Notation "f ::= v" := (Pair #(f%string) v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.
Global Arguments structT _%_list%_struct.

Module struct.
Section goose_lang.
Infix "=?" := (String.eqb).

Context `{ffi_syntax}.

Definition field_offset (t : go_type) f : (Z * go_type) :=
  match t with
  | structT d =>
      (fix field_offset_struct (d : struct.descriptor) : (Z * go_type) :=
         match d with
         | [] => (-1, badT)
         | (f',t)::fs => if f' =? f then (0, t)
                      else match field_offset_struct fs with
                           | (off, t') => ((go_type_size t) + off, t')
                           end
         end) d
  | _ => (-1, badT)
  end
.

Definition field_ref (t : go_type) f: val :=
  λ: "p", BinOp (OffsetOp (field_offset t f).1) (Var "p") #(W64 1).

Definition field_ty d f : go_type := (field_offset d f).2.

Definition field_get (t : go_type) f : val :=
  match t with
  | structT d =>
      (fix field_get_struct (d : struct.descriptor) : val :=
         match d with
         | [] => (λ: <>, #())%V
         | (f',_)::fs => if f' =? f
                       then (λ: "v", Fst (Var "v"))%V
                       else (λ: "v", field_get_struct fs (Snd (Var "v")))%V
         end
      ) d
      | _ => (#())
  end.

Definition assocl_lookup : val :=
  rec: "assocl_lookup" "f" "fvs" :=
    list.Match "fvs"
              (λ: <>, InjLV #())
              (λ: "fv" "fvs",
                 let: ("f'", "v") := "fv" in
                 if: "f" = "f'" then InjR "v" else "assocl_lookup" "f" "fvs").

Definition make_def (t : go_type) : val :=
  match t with
  | structT d =>
      (fix make_def_struct (fs : struct.descriptor) : val :=
         match fs with
         | [] => (λ: "fvs", Val #())%V
         | (f,ft)::fs => (λ: "fvs", ((match: (assocl_lookup #f "fvs") with
                                     InjL <> => (Val (zero_val ft))
                                     | InjR "x" => "x" end),
                                            (make_def_struct fs) "fvs"))%V
         end) d
  | _ => LitV $ LitPoison
  end.
Program Definition make := unseal (_:seal (@make_def)). Obligation 1. by eexists. Qed.
Definition make_unseal : make = _ := seal_eq _.

End goose_lang.
End struct.

Notation "[{ }]" := (struct.fields_val []) (only parsing) : expr_scope.
Notation "[{ x }]" := (list.Cons x [{ }]%E) : expr_scope.
Notation "[{ x ; y ; .. ; z }]" := (list.Cons x (list.Cons y .. (list.Cons z [{ }]%E) ..)) : expr_scope.
