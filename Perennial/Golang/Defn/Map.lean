/-
Map semantics.

A map value (`map.mapV`) is the value a lookup of a missing key gives and the map's entries
(id, key, value) in insertion order. Keys are compared with Go's `==` at the key type
(`=⟨key_type⟩`), as gc compares them, so a key type whose `==` is not equality of values
(floats: `NaN != NaN`, `-0 == +0`) gets Go's behaviour: a lookup finds the first entry whose key
is `==` to the key, an insert replaces that entry's key and value (gc overwrites the stored key,
which matters for `-0`/`+0`) or appends a new entry, and a delete removes it. A `NaN` key is
`==` to no key, so each insert of one adds an entry that no lookup or delete finds, as in gc.

An entry's id identifies it for `range`, which reads entries by id (a key may not find its own
entry). The ids of a map's entries are distinct, and an id is a function of the key and the
entries when it is made (`map.freshId`), not of the map's history: an entry for a key gets the
id `(key, 0)` unless an entry already has that id. So for key types whose `==` is equality of
values, the entry of key `k` always has the id `(k, 0)`, and a key deleted and re-added (or
added after a `clear`) during a `range` is produced if not yet reached (Go allows either).

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
public import Perennial.Golang.Defn.Assume
public import Perennial.Golang.Defn.Predeclared

@[expose] public section

namespace Perennial

namespace map
section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

/-- An entry id `PairV key (idV n)`: `idV n` is an unbounded counter. Ids are internal to the map
instructions: Go code never sees one. -/
def idV (n : Nat) : val := ArrayV (List.replicate n (LitV LitUnit))

/-- An entry of a map value: its id, its key and its value. -/
structure Entry where
  id : val
  key : val
  value : val

def entryV (e : Entry) : val := PairV e.id (PairV e.key e.value)

/-- A map value: the value a lookup of a missing key gives, and the entries in insertion
order. -/
def mapV (dv : val) (es : List Entry) : val := PairV dv (ArrayV (es.map entryV))

/-- The id of a new entry with key `k`: `PairV k (idV n)` for the least `n` that no entry of
`es` has. One of the first `es.length + 1` candidates is free, so the ids of a map's entries are
distinct, and a key that `==` itself, inserted when no entry has its id, gets
`PairV k (idV 0)`. -/
noncomputable def freshId (k : val) (es : List Entry) : val :=
  PairV k (idV (((List.range (es.length + 1)).find?
    (fun n => decide (PairV k (idV n) ∉ es.map (·.id)))).getD 0))

/-- Go's `==` at the key type, of the key looked up and a stored key (gc's order). -/
def keyEq (key_type : go.GoType) (k k' : val) : Expr :=
  App (Val (GoInstruction (GoOp GoEquals key_type))) (Pair (Val k) (Val k'))

/-- A lookup of `k`: the value of the first entry whose key is `==` to `k`. -/
def lookupExpr (key_type : go.GoType) (k dv : val) : List Entry → Expr
  | [] => Pair (Val dv) (Val #false)
  | e :: es =>
    If (keyEq key_type k e.key) (Pair (Val e.value) (Val #true))
      (lookupExpr key_type k dv es)

/-- An insert of `k ↦ v` into the entries `pre ++ es`, `pre` checked already: the first entry
of `es` whose key is `==` to `k` gets key `k` and value `v` (and keeps its id), or an entry with
the id `id` is appended. -/
def insertExpr (key_type : go.GoType) (k v dv id : val) (pre : List Entry) :
    List Entry → Expr
  | [] => Val (mapV dv (pre ++ [⟨id, k, v⟩]))
  | e :: es =>
    If (keyEq key_type k e.key) (Val (mapV dv (pre ++ ⟨e.id, k, v⟩ :: es)))
      (insertExpr key_type k v dv id (pre ++ [e]) es)

/-- A delete of `k` from the entries `pre ++ es`, `pre` checked already: the first entry of `es`
whose key is `==` to `k` is removed. -/
def deleteExpr (key_type : go.GoType) (k dv : val) (pre : List Entry) : List Entry → Expr
  | [] => Val (mapV dv pre)
  | e :: es =>
    If (keyEq key_type k e.key) (Val (mapV dv (pre ++ es)))
      (deleteExpr key_type k dv (pre ++ [e]) es)

/-- The entry with id `id`, as `((key, value), true)`, or `((#(), dv), false)` if there is
none. -/
noncomputable def lookupIdVal (dv : val) (es : List Entry) (id : val) : val :=
  match es.find? (fun e => decide (e.id = id)) with
  | some e => PairV (PairV e.key e.value) #true
  | none => PairV (PairV #() dv) #false

def lookup2 (key_type elem_type : go.GoType) : val :=
  λ: "m" "k",
    InternalMapCheckKey key_type "k" ;;
    if: "m" =⟨go.MapType key_type elem_type⟩ #map.nil then
      (GoZeroVal elem_type #(), #false)
    else InternalMapLookup key_type (Read "m", "k")

def lookup1 (key_type elem_type : go.GoType) : val :=
  λ: "m" "k", Fst (lookup2 key_type elem_type "m" "k")

def insert (key_type : go.GoType) : val :=
  λ: "m" "k" "v",
    InternalMapCheckKey key_type "k" ;;
    Store "m" (InternalMapInsert key_type (Read "m", "k", "v"))

/-- `for k, v := range m { body }`. The loop does not hold the map: it reads the map once to
get its entries' ids (`InternalMapForRange` enumerates them, in an arbitrary order), then for
each id reads the map again and looks the entry up by its id, skipping it if it is no longer
there, and calls the body with its current key and value. So the body may write the map (as Go
allows), and this follows Go's rule for such writes (https://go.dev/ref/spec#For_range): an
entry removed before it is reached is not produced, the current entry may be deleted or
assigned, and an entry added during the loop is produced only if it has the id of an entry not
yet reached (Go allows either). Each id is looked up once, so no entry is produced twice. The
entry is found by its id, not its key: a `NaN` key is `==` to no key, but its entry is
produced. -/
def forRange (key_type elem_type : go.GoType) : val :=
  λ: "m" "body",
    if: "m" =⟨go.MapType key_type elem_type⟩ #map.nil then
      do: #()
    else
      exceptionDo (InternalMapForRange key_type elem_type (Read "m",
        (λ: "id",
          let: "p" := InternalMapLookupId (Read "m", "id") in
          if: Snd "p" then "body" (Fst (Fst "p")) (Snd (Fst "p")) else (do: #()))))

end defs
end map

namespace go
section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

class MapSemantics [GoSemanticsFunctions] : Prop where
  internal_map_lookup_step (key_type : go.GoType) (dv : val) (es : List map.Entry) (k : val) :
    go.IsGoStepPureDet (InternalMapLookup key_type) (PairV (map.mapV dv es) k)
      (map.lookupExpr key_type k dv es)
  internal_map_insert_step (key_type : go.GoType) (dv : val) (es : List map.Entry) (k v : val) :
    go.IsGoStepPureDet (InternalMapInsert key_type) (PairV (PairV (map.mapV dv es) k) v)
      (map.insertExpr key_type k v dv (map.freshId k es) [] es)
  internal_map_delete_step (key_type : go.GoType) (dv : val) (es : List map.Entry) (k : val) :
    go.IsGoStepPureDet (InternalMapDelete key_type) (PairV (map.mapV dv es) k)
      (map.deleteExpr key_type k dv [] es)
  internal_map_lookup_id_step (dv : val) (es : List map.Entry) (id : val) :
    go.IsGoStepPureDet InternalMapLookupId (PairV (map.mapV dv es) id)
      (Val (map.lookupIdVal dv es id))
  /-- A map has fewer than `2^63` entries (its length is a non-negative `int`): the model
  assumes it, as `append` assumes its length does not overflow (`sumAssumeNoOverflowSigned`):
  `len` of a larger map does not return. -/
  internal_map_length_step (dv : val) (es : List map.Entry) :
    go.IsGoStepPureDet InternalMapLength (map.mapV dv es)
      (if es.length < 2 ^ 63 then Val #(W64 es.length) else App (Val assume) (Val #false))
  internal_map_for_range_step (dv : val) (es : List map.Entry) (body : val)
    (key_type elem_type : go.GoType) :
    is_go_step_pure (InternalMapForRange key_type elem_type) glv((map.mapV dv es, body)) =
    (fun (e : Expr) => ∃ ids, ids.Perm (es.map (·.id)) ∧
        e =
        List.foldr (fun (id : val) remaining_loop =>
                 gl(let: "b" := body (Val id) in
                 if: (Fst "b") =⟨go.string⟩ #"break" then (return: (do: #())) else (do: #()) ;;;
                 if: (Fst "b" =⟨go.string⟩ #"continue") ||
                     (Fst (Var "b") =⟨go.string⟩ #"execute") then
                   (λ: <>, remaining_loop : val) #()
                 else return: "b")
          ) gl(return: (do: #())) ids)
  internal_map_make_step (v : val) :
    go.IsGoStepPureDet InternalMapMake v (Val (map.mapV v []))
  internal_map_check_key_step (key_type : go.GoType) (k : val) :
    ⟦InternalMapCheckKey key_type, k⟧ ⤳ (k =⟨key_type⟩ k)

  -- special cases for equality
  is_go_op_go_equals_map_nil_l (kt vt : go.GoType) (s : GoMap) :
    ⟦GoOp GoEquals (go.MapType kt vt), (#map.nil, #s)⟧ ⤳[under] #(decide (s = map.nil))
  is_go_op_go_equals_map_nil_r (kt vt : go.GoType) (s : GoMap) :
    ⟦GoOp GoEquals (go.MapType kt vt), (#s, #map.nil)⟧ ⤳[under] #(decide (s = map.nil))

  clear_map (key_type elem_type : go.GoType) :
    FuncUnfold go.clear [go.MapType key_type elem_type]
    (λ: "m", Store "m" (Read
               (FuncResolve go.make1 [go.MapType key_type elem_type] #() #())) : val)
  delete_map (key_type elem_type : go.GoType) :
    FuncUnfold go.delete [go.MapType key_type elem_type]
    (λ: "m" "k",
       InternalMapCheckKey key_type "k" ;;
       Store "m" (InternalMapDelete key_type (Read "m", "k")) : val)
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

attribute [instance] MapSemantics.internal_map_lookup_step
  MapSemantics.internal_map_insert_step MapSemantics.internal_map_delete_step
  MapSemantics.internal_map_lookup_id_step MapSemantics.internal_map_length_step
  MapSemantics.internal_map_make_step MapSemantics.internal_map_check_key_step
  MapSemantics.is_go_op_go_equals_map_nil_l MapSemantics.is_go_op_go_equals_map_nil_r
  MapSemantics.clear_map MapSemantics.delete_map MapSemantics.make2_map MapSemantics.make1_map
  MapSemantics.len_map MapSemantics.composite_literal_map
export MapSemantics (internal_map_lookup_step internal_map_insert_step internal_map_delete_step
  internal_map_lookup_id_step internal_map_length_step internal_map_for_range_step
  internal_map_make_step internal_map_check_key_step
  is_go_op_go_equals_map_nil_l is_go_op_go_equals_map_nil_r
  clear_map delete_map make2_map make1_map len_map composite_literal_map)

end defs
end go

end Perennial
