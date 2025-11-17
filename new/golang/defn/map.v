From New.golang.defn Require Export loop assume predeclared.

Module map.
Definition t := loc.
Definition nil : t := null.

Section defs.
Context {ext : ffi_syntax}.
Definition Lookup2 (key_type elem_type : go.type) : val :=
  λ: "m" "k",
    let: "mv" := Read "m" in InternalMapLookup ("mv", "k").

Definition Lookup1 (key_type elem_type : go.type) : val :=
  λ: "m" "k", Fst (Lookup2 key_type elem_type "m" "k").

Definition Insert (key_type elem_type : go.type) : val :=
  λ: "m" "k" "v",
    let: "mv" := Read "m" in
    Store "m" (InternalMapInsert ("mv", "k", "v")).
End defs.
End map.

Module go.
Class MapSemantics {ext : ffi_syntax} `{!GoContext} :=
{
  equals_map_nil_l key_type elem_type m :
    go_equals (go.MapType key_type elem_type) #m #map.nil = Some $ bool_decide (m = map.nil);
  equals_map_nil_r key_type elem_type m :
    go_equals (go.MapType key_type elem_type) #map.nil #m = Some $ bool_decide (m = map.nil);

  map_lookup_pure k mv m (H : is_map_pure mv m) :
    map_lookup mv k = m k;
  map_insert_pure k v mv m (H : is_map_pure mv m) :
    is_map_pure (map_insert mv k v) (λ k', if decide (k' = k) then (true, v) else m k);

  make2_map key_type elem_type :
    ∃ default_elem mv, is_map_pure mv (const (false, default_elem)) ∧
    #(functions go.make2 [go.TypeLit $ go.MapType key_type elem_type]) =
    (λ: "len",
       let: "dynamic_default_elem" := GoLoad elem_type (GoAlloc elem_type #()) in
       (if: "dynamic_default_elem" ≠⟨elem_type⟩ default_elem then AngelicExit #()
        else #());;
       ref mv)%V;
  make1_map key_type elem_type :
    #(functions go.make2 [go.TypeLit $ go.MapType key_type elem_type]) =
    (λ: <>, FuncResolve go.make2 [go.TypeLit $ go.MapType key_type elem_type] #() #(W64 0))%V;

  clear_map key_type elem_type :
    #(functions go.clear [go.TypeLit $ go.MapType key_type elem_type]) =
    (λ: "m", Store "m" $ Load $
               FuncResolve go.make1 [go.TypeLit $ go.MapType key_type elem_type] #())%V;
}.
End go.
