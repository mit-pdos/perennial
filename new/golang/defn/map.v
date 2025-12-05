From New.golang.defn Require Export loop predeclared slice.

(* One subtlety (from https://go.dev/ref/spec#Map_types): inserting into or
   lookup up from a map can cause a run-time panic:
   "If the key type is an interface type, these comparison operators [== and !=]
   must be defined for the dynamic key values; failure will cause a run-time
   panic."
   The values which result in panics are not precisely defined by the spec (e.g.
   what about an interface with dynamic value being a nil slice? `==` is technically
   defined as a special case for nil slices). A better source of what is safe
   and not is the implementation:
   https://cs.opensource.google/go/go/+/refs/tags/go1.25.4:src/internal/runtime/maps/map.go;l=831

   This corresponds: `k` is a safe map key iff [go_eq k k] is safe to execute.
   The latter is safe when
     #(interface.mk key_type k) =⟨go.any⟩ #(interface.mk key_type k)
   is safe.
*)

Module map.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Definition lookup2 (key_type elem_type : go.type) : val :=
  λ: "m" "k",
    (* make sure it's safe to look up *)
    InterfaceMake key_type "k" =⟨go.any⟩ InterfaceMake key_type "k";;
    if: "m" =⟨go.MapType key_type elem_type⟩ #map.nil then
      (* NOTE: this gets the zero value from element type in a hacky way. *)
      let: "default_elem" := GoLoad elem_type (GoAlloc elem_type #()) in
      ("default_elem", #false)
    else InternalMapLookup (Read "m", "k").

Definition lookup1 (key_type elem_type : go.type) : val :=
  λ: "m" "k", Fst (lookup2 key_type elem_type "m" "k").

Definition insert (key_type : go.type) : val :=
  λ: "m" "k" "v",
    (* make sure it's safe to look up *)
    InterfaceMake key_type "k" =⟨go.any⟩ InterfaceMake key_type "k";;
    Store "m" (InternalMapInsert (Read "m", "k", "v")).

(* Does not support modifications to the map during the loop. *)
Definition for_range (key_type elem_type : go.type) : val :=
  λ: "m" "body",
    if: "m" =⟨go.MapType key_type elem_type⟩ #map.nil then
      do: #()
    else
      let: "mv" := StartRead "m" in
      let: "key_sl" := CompositeLiteral (go.SliceType key_type) (InternalMapDomainLiteral "mv") in
      let: "v" :=
        (slice.for_range key_type
           (λ: <> "k", "body" "k" (lookup1 key_type elem_type "m" "k"))
           "key_sl") in
      FinishRead "m";;
      "v".

End defs.
End map.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.
Class MapSemantics `{!GoSemanticsFunctions} :=
{
  (* special cases for equality *)
  #[global] is_go_op_go_equals_map_nil_l kt vt s ::
    go.IsGoOp GoEquals (go.MapType kt vt) (#map.nil, #s)%V #(bool_decide (s = map.nil));
  #[global] is_go_op_go_equals_map_nil_r kt vt s ::
    go.IsGoOp GoEquals (go.MapType kt vt) (#s, #map.nil)%V #(bool_decide (s = map.nil));

  (* internal deterministic steps *)
  #[global] internal_map_lookup_step mv k ::
    go.IsGoStepPureDet InternalMapLookup (mv, k)%V (let '(ok, v) := map_lookup mv k in (v, #ok));
  #[global] internal_map_insert_step mv k v ::
    go.IsGoStepPureDet InternalMapInsert (mv, k, v)%V (map_insert mv k v);
  #[global] internal_map_delete_step mv k ::
    go.IsGoStepPureDet InternalMapDelete (mv, k)%V (map_delete mv k);
  #[global] internal_map_make_step v ::
    go.IsGoStepPureDet InternalMapMake v (map_empty v);

  is_map_pure (v : val) (m : val → bool * val) : Prop;
  map_default : val → val;

  is_map_pure_flatten mv m (H : is_map_pure mv m) :
    flatten_struct mv = [mv];
  map_lookup_pure k mv m (H : is_map_pure mv m) :
    map_lookup mv k = m k;
  is_map_pure_map_insert k v mv m (H : is_map_pure mv m) :
    is_map_pure (map_insert mv k v) (λ k', if decide (k' = k) then (true, v) else m k');
  is_map_pure_map_delete k mv m (H : is_map_pure mv m) :
    is_map_pure (map_delete mv k)
      (λ k', if decide (k' = k) then (false, map_default mv) else m k');
  is_map_pure_map_empty dv : is_map_pure (map_empty dv) (const (false, dv));

  map_default_map_empty dv : map_default (map_empty dv) = dv;
  map_default_map_insert m k v : map_default (map_insert m k v) = map_default m;
  map_default_map_delete m k : map_default (map_delete m k) = map_default m;

  is_map_domain_exists mv m (H : is_map_pure mv m) : ∃ ks, is_map_domain mv ks;
  is_map_domain_map_empty dv ks : is_map_domain (map_empty dv) ks → ks = [];
  is_map_domain_pure mv m ks :
    is_map_pure mv m →
    is_map_domain mv ks →
    NoDup ks ∧ (∀ k, (m k).1 = true ↔ k ∈ ks);

  #[global] clear_map key_type elem_type ::
    FuncUnfold go.clear [go.MapType key_type elem_type]
    (λ: "m", Store "m" $ Read $
               FuncResolve go.make1 [go.MapType key_type elem_type] #())%V;
  #[global] delete_map key_type elem_type ::
    FuncUnfold go.delete [go.MapType key_type elem_type]
    (λ: "m" "k",
       InterfaceMake key_type "k" =⟨go.any⟩ InterfaceMake key_type "k";;
       Store "m" $ InternalMapDelete (Read "m", "k"))%V;
  #[global] make2_map key_type elem_type ::
    FuncUnfold go.make2 [go.MapType key_type elem_type]
    (λ: "len",
       let: "default_elem" := GoLoad elem_type (GoAlloc elem_type #()) in
       ref (InternalMapMake "default_elem"))%V;
  #[global] make1_map key_type elem_type ::
    FuncUnfold go.make1 [go.MapType key_type elem_type]
    (λ: <>, FuncResolve go.make2 [go.MapType key_type elem_type] #() #(W64 0))%V;
  #[global] len_map key_type elem_type ::
    FuncUnfold go.len [go.MapType key_type elem_type]
    (λ: "m", InternalMapLength (Read "m"))%V;

  composite_literal_map key_type elem_type (l : list keyed_element) :
    composite_literal (go.MapType key_type elem_type) (LiteralValue l) =
    (let: "m" := FuncResolve go.make1 [go.MapType key_type elem_type] #() #() in
     (foldl (λ expr_so_far ke,
               match ke with
               | KeyedElement (Some k) v =>
                   let k_expr := (match k with
                                  | KeyExpression e => e
                                  | KeyLiteralValue l => CompositeLiteral key_type (LiteralValue l)
                                  | _ => Panic "invalid map literal"
                                  end) in
                   let v_expr := (match v with
                                  | ElementExpression e => e
                                  | ElementLiteralValue l => CompositeLiteral elem_type (LiteralValue l)
                                  end) in
                   expr_so_far;; (map.insert key_type "m" k_expr v_expr)
               | _ => Panic "invalid map literal"
               end)
        (#() : expr)
        l
     ) ;;
     "m"
    )%E
}.
End defs.
End go.
