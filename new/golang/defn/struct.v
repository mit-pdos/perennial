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

Definition field_ref (t : go_type) f0: val :=
  λ: "p", BinOp (OffsetOp (field_offset t f0).1) (Var "p") #1.

Definition field_ty d f0 : go_type := (field_offset d f0).2.

Local Definition assocl_lookup_goose : val :=
  rec: "assocl_lookup" "fvs" "f" :=
    list.Match "fvs"
              (λ: <>, InjLV #())
              (λ: "fv" "fvs",
                 let: ("f'", "v") := "fv" in
                 if: "f" = "f'" then InjR "v" else "assocl_lookup" "fvs" "f").

Definition make_def (t : go_type) : val :=
  match t with
  | structT d =>
      (fix make_def_struct (fs : struct.descriptor) : val :=
         match fs with
         | [] => (λ: "fvs", Val #())%V
         | (f,ft)::fs => (λ: "fvs", ((match: (vmap.Get #(str f) "fvs") with
                                     InjL <> => (Val (zero_val ft))
                                     | InjR "x" => "x" end),
                                            (make_def_struct fs) "fvs"))%V
         end) d
  | _ => LitV $ LitPoison
  end.
Program Definition make := unseal (_:seal (@make_def)). Obligation 1. by eexists. Qed.
Definition make_unseal : make = _ := seal_eq _.

Definition fields_val_def (m : gmap string val) : val :=
  vmap.val (kmap (LitV ∘ LitString) m).
Program Definition fields_val := unseal (_:seal (@fields_val_def)). Obligation 1. by eexists. Qed.
Definition fields_val_unseal : fields_val = _ := seal_eq _.

End goose_lang.
End struct.
