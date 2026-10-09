/-
Map semantics.

One subtlety (from https://go.dev/ref/spec#Map_types): inserting into or
lookup up from a map can cause a run-time panic:
"If the key type is an interface type, these comparison operators [== and !=]
must be defined for the dynamic key values; failure will cause a run-time
panic."
The values which result in panics are not precisely defined by the spec (e.g.
what about an interface with dynamic value being a nil slice? `==` is
technically defined as a special case for nil slices). A better source of what
is safe and not is the implementation:
https://cs.opensource.google/go/go/+/refs/tags/go1.25.4:src/internal/runtime/maps/map.go;l=831

This corresponds: `k` is a safe map key iff `go_eq k k` is safe to execute.
The latter is safe when
  `#(interface.mk key_type k) =⟨go.any⟩ #(interface.mk key_type k)`
is safe.

`len_map` takes `[t ↓u go.MapType key_type elem_type]`, so `len` also unfolds
at named map types.
-/
module

public import Perennial.Golang.Defn.Loop
public import Perennial.Golang.Defn.Predeclared

@[expose] public section

namespace Perennial

namespace map
section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

def lookup2 (key_type elem_type : go.GoType) : val :=
  λ: "m" "k",
    InternalMapCheckKey key_type "k" ;;
    if: "m" =⟨go.MapType key_type elem_type⟩ #map.nil then
      (GoZeroVal elem_type #(), #false)
    else InternalMapLookup (Read "m", "k")

def lookup1 (key_type elem_type : go.GoType) : val :=
  λ: "m" "k", Fst (lookup2 key_type elem_type "m" "k")

def insert (key_type : go.GoType) : val :=
  λ: "m" "k" "v",
    InternalMapCheckKey key_type "k" ;;
    Store "m" (InternalMapInsert (Read "m", "k", "v"))

/-- Does not support modifications to the map during the loop. -/
def forRange (key_type elem_type : go.GoType) : val :=
  λ: "m" "body",
    if: "m" =⟨go.MapType key_type elem_type⟩ #map.nil then
      do: #()
    else
      let: "mv" := StartRead "m" in
      let: "v" := exceptionDo (InternalMapForRange key_type elem_type ("mv", "body")) in
      FinishRead "m" ;;
      "v"

end defs
end map

namespace go
section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

class MapSemantics [GoSemanticsFunctions] : Prop where
  internal_map_lookup_step_pure (m k : val) :
    ⟦InternalMapLookup, (m, k)⟧ ⤳ (let (ok, v) := mapLookup m k; gl((v, #ok)))
  internal_map_insert_step_pure (m k v : val) :
    ⟦InternalMapInsert, (m, k, v)⟧ ⤳ (mapInsert m k v)
  internal_map_delete_step_pure (m k : val) :
    ⟦InternalMapDelete, (m, k)⟧ ⤳ (mapDelete m k)
  /-- Not an instance in Lean: `ks` and `H` cannot be found by typeclass
  search. -/
  internal_map_length_step_pure (m : val) (ks : List val) (H : is_map_domain m ks) :
    ⟦InternalMapLength, m⟧ ⤳ #(W64 ks.length)
  internal_map_domain_literal_step_pure (mv : val) (m : val → Bool × val) (body : val)
    (key_type elem_type : go.GoType) (Hm : is_map_pure mv m) :
    is_go_step_pure (InternalMapForRange key_type elem_type) glv((mv, body)) =
    (fun (e : Expr) => ∃ ks, ∃ (_ : is_map_domain mv ks),
        e =
        List.foldr (fun key remaining_loop =>
                 gl(let: "b" := body (Val key) (m key).2 in
                 if: (Fst "b") =⟨go.string⟩ #"break" then (return: (do: #())) else (do: #()) ;;;
                 if: (Fst "b" =⟨go.string⟩ #"continue") ||
                     (Fst (Var "b") =⟨go.string⟩ #"execute") then
                   (λ: <>, remaining_loop : val) #()
                 else return: "b")
          ) gl(return: (do: #())) ks)
  internal_map_make_step_pure (v : val) :
    ⟦InternalMapMake, v⟧ ⤳ (mapEmpty v)
  internal_map_check_key_step (key_type : go.GoType) (k : val) :
    ⟦InternalMapCheckKey key_type, k⟧ ⤳ (k =⟨key_type⟩ k)

  -- special cases for equality
  is_go_op_go_equals_map_nil_l (kt vt : go.GoType) (s : GoMap) :
    ⟦GoOp GoEquals (go.MapType kt vt), (#map.nil, #s)⟧ ⤳[under] #(decide (s = map.nil))
  is_go_op_go_equals_map_nil_r (kt vt : go.GoType) (s : GoMap) :
    ⟦GoOp GoEquals (go.MapType kt vt), (#s, #map.nil)⟧ ⤳[under] #(decide (s = map.nil))

  -- internal deterministic steps
  internal_map_lookup_step (mv k : val) :
    ⟦InternalMapLookup, (mv, k)⟧ ⤳ (let (ok, v) := mapLookup mv k; gl((v, #ok)))
  internal_map_insert_step (mv k v : val) :
    ⟦InternalMapInsert, (mv, k, v)⟧ ⤳ (mapInsert mv k v)
  internal_map_delete_step (mv k : val) :
    ⟦InternalMapDelete, (mv, k)⟧ ⤳ (mapDelete mv k)
  internal_map_make_step (v : val) :
    ⟦InternalMapMake, v⟧ ⤳ (mapEmpty v)

  mapLookup_pure (k mv : val) (m : val → Bool × val) (H : is_map_pure mv m) :
    mapLookup mv k = m k
  is_map_pure_map_insert (k v mv : val) (m : val → Bool × val) (H : is_map_pure mv m) :
    is_map_pure (mapInsert mv k v) (fun k' => if k' = k then (true, v) else m k')
  is_map_pure_map_delete (k mv : val) (m : val → Bool × val) (H : is_map_pure mv m) :
    is_map_pure (mapDelete mv k)
      (fun k' => if k' = k then (false, mapDefault mv) else m k')
  is_map_pure_map_empty (dv : val) : is_map_pure (mapEmpty dv) (fun _ => (false, dv))

  mapDefault_map_empty (dv : val) : mapDefault (mapEmpty dv) = dv
  mapDefault_map_insert (m k v : val) : mapDefault (mapInsert m k v) = mapDefault m
  mapDefault_map_delete (m k : val) : mapDefault (mapDelete m k) = mapDefault m

  is_map_domain_exists (mv : val) (m : val → Bool × val) (H : is_map_pure mv m) :
    ∃ ks, is_map_domain mv ks
  is_map_domain_map_empty (dv : val) (ks : List val) : is_map_domain (mapEmpty dv) ks → ks = []
  is_map_domain_pure (mv : val) (m : val → Bool × val) (ks : List val) :
    is_map_pure mv m →
    is_map_domain mv ks →
    ks.Nodup ∧ (∀ k, (m k).1 = true ↔ k ∈ ks)

  clear_map (key_type elem_type : go.GoType) :
    FuncUnfold go.clear [go.MapType key_type elem_type]
    (λ: "m", Store "m" (Read
               (FuncResolve go.make1 [go.MapType key_type elem_type] #() #())) : val)
  delete_map (key_type elem_type : go.GoType) :
    FuncUnfold go.delete [go.MapType key_type elem_type]
    (λ: "m" "k",
       InternalMapCheckKey key_type "k" ;;
       Store "m" (InternalMapDelete (Read "m", "k")) : val)
  make2_map (key_type elem_type : go.GoType) :
    FuncUnfold go.make2 [go.MapType key_type elem_type]
    (λ: "len",
       Alloc (InternalMapMake (GoZeroVal elem_type #())) : val)
  make1_map (key_type elem_type : go.GoType) :
    FuncUnfold go.make1 [go.MapType key_type elem_type]
    (λ: <>, FuncResolve go.make2 [go.MapType key_type elem_type] #() #(W64 0) : val)
  /-- Go's `len` works on any type whose underlying type is a map, so (like
  `len_slice`/`len_chan`) this takes `[t ↓u go.MapType key_type elem_type]`
  rather than only a literal `go.MapType key_type elem_type`; otherwise `len(m)`
  would be stuck when `m` has a named map type (`type M map[K]V`).

  `len` of a nil map is `0` in Go (a nil map reads as empty), so the nil case
  is handled before the `Read`, exactly as `lookup2` and `for_range` do;
  without it `len` of a nil map was stuck on a read of the null location. -/
  len_map {t key_type elem_type : go.GoType} [t ↓u go.MapType key_type elem_type] :
    FuncUnfold go.len [t]
    (λ: "m",
       if: "m" =⟨go.MapType key_type elem_type⟩ #map.nil then #(W64 0)
       else InternalMapLength (Read "m") : val)

  composite_literal_map (key_type elem_type : go.GoType) (l : List keyed_element) :
    ⟦CompositeLiteral (go.MapType key_type elem_type), (LiteralValueV l)⟧ ⤳[under]
    (let: "m" := FuncResolve go.make1 [go.MapType key_type elem_type] #() #() in
     (List.foldl (fun expr_so_far ke =>
               match ke with
               | KeyedElement (some k) v =>
                   let k_expr := (match k with
                                  | KeyExpression from_ e => gl(Convert from_ key_type e)
                                  | KeyLiteralValue l =>
                                      gl(CompositeLiteral key_type (LiteralValue l))
                                  | _ => Panic "invalid map literal")
                   let v_expr := (match v with
                                  | ElementExpression from_ e => gl(Convert from_ elem_type e)
                                  | ElementLiteralValue l =>
                                      gl(CompositeLiteral elem_type (LiteralValue l)))
                   gl(expr_so_far ;; (map.insert key_type "m" k_expr v_expr))
               | _ => Panic "invalid map literal")
        (#() : Expr)
        l
     ) ;;
     "m"
    )

attribute [instance] MapSemantics.internal_map_lookup_step_pure
  MapSemantics.internal_map_insert_step_pure MapSemantics.internal_map_delete_step_pure
  MapSemantics.internal_map_make_step_pure MapSemantics.internal_map_check_key_step
  MapSemantics.is_go_op_go_equals_map_nil_l MapSemantics.is_go_op_go_equals_map_nil_r
  MapSemantics.internal_map_lookup_step MapSemantics.internal_map_insert_step
  MapSemantics.internal_map_delete_step MapSemantics.internal_map_make_step
  MapSemantics.clear_map MapSemantics.delete_map MapSemantics.make2_map MapSemantics.make1_map
  MapSemantics.len_map MapSemantics.composite_literal_map
export MapSemantics (internal_map_lookup_step_pure internal_map_insert_step_pure
  internal_map_delete_step_pure internal_map_length_step_pure
  internal_map_domain_literal_step_pure internal_map_make_step_pure internal_map_check_key_step
  is_go_op_go_equals_map_nil_l is_go_op_go_equals_map_nil_r internal_map_lookup_step
  internal_map_insert_step internal_map_delete_step internal_map_make_step mapLookup_pure
  is_map_pure_map_insert is_map_pure_map_delete is_map_pure_map_empty mapDefault_map_empty
  mapDefault_map_insert mapDefault_map_delete is_map_domain_exists is_map_domain_map_empty
  is_map_domain_pure clear_map delete_map make2_map make1_map len_map composite_literal_map)

end defs
end go

end Perennial
