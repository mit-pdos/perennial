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
    InternalMapCheckKey key_type "k";;
    if: "m" =⟨go.MapType key_type elem_type⟩ #map.nil then
      (GoZeroVal elem_type #(), #false)
    else InternalMapLookup (Read "m", "k").

Definition lookup1 (key_type elem_type : go.type) : val :=
  λ: "m" "k", Fst (lookup2 key_type elem_type "m" "k").

Definition insert (key_type : go.type) : val :=
  λ: "m" "k" "v",
    InternalMapCheckKey key_type "k";;
    Store "m" (InternalMapInsert (Read "m", "k", "v")).

(* Does not support modifications to the map during the loop. *)
Definition for_range (key_type elem_type : go.type) : val :=
  λ: "m" "body",
    if: "m" =⟨go.MapType key_type elem_type⟩ #map.nil then
      do: #()
    else
      let: "mv" := StartRead "m" in
      let: "v" := exception_do (InternalMapForRange key_type elem_type ("mv", "body")) in
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
  #[global] internal_map_lookup_step_pure m k ::
    ⟦InternalMapLookup, (m, k)⟧ ⤳ (let '(ok, v) := map_lookup m k in (v, #ok));
  #[global] internal_map_insert_step_pure m k v ::
    ⟦InternalMapInsert, (m, k, v)⟧ ⤳ (map_insert m k v);
  #[global] internal_map_delete_step_pure m k ::
    ⟦InternalMapDelete, (m, k)⟧ ⤳ (map_delete m k);
  #[global] internal_map_length_step_pure m ks (H : is_map_domain m ks) ::
    ⟦InternalMapLength, m⟧ ⤳ #(W64 (length ks));
  internal_map_domain_literal_step_pure mv m body key_type elem_type (Hm : is_map_pure mv m) :
    is_go_step_pure (InternalMapForRange key_type elem_type) (mv, body)%V =
    (λ e, ∃ ks (His_dom : is_map_domain mv ks),
        e =
        foldr (λ key remaining_loop,
                 let: "b" := body (Val key) (m key).2 in
                 if: (Fst "b") =⟨go.string⟩ #"break" then (return: (do: #())) else (do: #()) ;;;
                 if: (Fst "b" =⟨go.string⟩ #"continue") || (Fst $ Var "b" =⟨go.string⟩ #"execute") then
                   (λ: <>, remaining_loop)%V #()
                 else return: "b"
          )%E (return: (do: #()))%E ks);
  #[global] internal_map_make_step_pure v ::
    ⟦InternalMapMake, v⟧ ⤳ (map_empty v);
  #[global] internal_map_check_key_step key_type k ::
    ⟦InternalMapCheckKey key_type, k⟧ ⤳ (k =⟨key_type⟩ k);

  (* special cases for equality *)
  #[global] is_go_op_go_equals_map_nil_l kt vt s ::
    ⟦GoOp GoEquals (go.MapType kt vt), (#map.nil, #s)⟧ ⤳[under] #(bool_decide (s = map.nil));
  #[global] is_go_op_go_equals_map_nil_r kt vt s ::
    ⟦GoOp GoEquals (go.MapType kt vt), (#s, #map.nil)⟧ ⤳[under] #(bool_decide (s = map.nil));

  (* internal deterministic steps *)
  #[global] internal_map_lookup_step mv k ::
    ⟦InternalMapLookup, (mv, k)⟧ ⤳ (let '(ok, v) := map_lookup mv k in (v, #ok));
  #[global] internal_map_insert_step mv k v ::
    ⟦InternalMapInsert, (mv, k, v)⟧ ⤳ (map_insert mv k v);
  #[global] internal_map_delete_step mv k ::
    ⟦InternalMapDelete, (mv, k)⟧ ⤳ (map_delete mv k);
  #[global] internal_map_make_step v ::
    ⟦InternalMapMake, v⟧ ⤳ (map_empty v);

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
               FuncResolve go.make1 [go.MapType key_type elem_type] #() #())%V;
  #[global] delete_map key_type elem_type ::
    FuncUnfold go.delete [go.MapType key_type elem_type]
    (λ: "m" "k",
       InternalMapCheckKey key_type "k";;
       Store "m" $ InternalMapDelete (Read "m", "k"))%V;
  #[global] make2_map key_type elem_type ::
    FuncUnfold go.make2 [go.MapType key_type elem_type]
    (λ: "len",
       go.ref_one (InternalMapMake (GoZeroVal elem_type #())))%V;
  #[global] make1_map key_type elem_type ::
    FuncUnfold go.make1 [go.MapType key_type elem_type]
    (λ: <>, FuncResolve go.make2 [go.MapType key_type elem_type] #() #(W64 0))%V;
  #[global] len_map key_type elem_type ::
    FuncUnfold go.len [go.MapType key_type elem_type]
    (λ: "m", InternalMapLength (Read "m"))%V;

  #[global] composite_literal_map key_type elem_type (l : list keyed_element) ::
    ⟦CompositeLiteral (go.MapType key_type elem_type), (LiteralValueV l)⟧ ⤳[under]
    (let: "m" := FuncResolve go.make1 [go.MapType key_type elem_type] #() #() in
     (foldl (λ expr_so_far ke,
               match ke with
               | KeyedElement (Some k) v =>
                   let k_expr := (match k with
                                  | KeyExpression from e => Convert from key_type e
                                  | KeyLiteralValue l => CompositeLiteral key_type (LiteralValue l)
                                  | _ => Panic "invalid map literal"
                                  end) in
                   let v_expr := (match v with
                                  | ElementExpression from e => Convert from elem_type e
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
