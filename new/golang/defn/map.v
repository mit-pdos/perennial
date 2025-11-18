From New.golang.defn Require Export loop predeclared.

(* One subtlety (from https://go.dev/ref/spec#Map_types): inserting into a map
   can cause a run-time panic.

   https://go.dev/ref/spec#Comparison_operators says:
    > A comparison of two interface values with identical dynamic types causes a
    > run-time panic if that type is not comparable.
   While (not comparable → run-time panic) is true, the converse is not.
   Consider having a's dynamic type be []int (or something not comparable) in the below:
   type comparableButNotSuperComparable struct {
	   a any
   }
   So, the check "is the type comparable" is insufficient for a safe semantics.
   Some comparable types will still lead to run-time panics.

   Here's a definition that captures both what map insertion and interface
   checks need:
   Define a typed Go value (v : t) to be _super-duper comparable_ if
   - t is a boolean, integer, floating-point, complex, string, pointer, channel type
   - t is an interface, and (dyn_val : dyn_typ) is super-duper comparable where
     v = interfaceVal(dyn_typ, dyn_val)
   - t is a struct, and all of v's field values are super-duper comparable
   - t is an array, and all of v's elements are super-duper comparable.

   This does not consider "type parameters", because this is defining semantics
   of monomorphized Go programs, at which point there are no type parameters.

   Hypothesis A: in real Go, map insertion or lookup with key `k` panics iff
   (k is not super-duper comparable)
   Hypothesis B: in real Go, comparison between A and B panics iff A or B is not
   super-duper comparable. !!! WRONG: no panic if the dynamic types are
   different at some point traversing down the tree.
*)
Module map.
Section defs.
Context {ext : ffi_syntax}.

Definition lookup2 : val :=
  λ: "m" "k", InternalMapLookup (Read "m", "k").

Definition lookup1 : val :=
  λ: "m" "k", Fst (lookup2 "m" "k").

Definition insert : val :=
  λ: "m" "k" "v", Store "m" (InternalMapInsert (Read "m", "k", "v")).

(* Does not support modifications to the map during the loop. *)
Definition for_range (key_type elem_type : go.type) : val :=
  λ: "m" "body",
    let: "mv" := StartRead "m" in
    let: "ks" := InternalMapDomain "mv" in
    let: "len" := ArrayLength "ks" in
    let: "i" := GoAlloc go.int #() in
    let: "v" :=
      (for: (λ: <>, ![go.int] "i" <⟨go.int⟩ "len"); (λ: <>, "i" <-[go.int] (![go.int] "i") + #(W64 1)) :=
         (λ: <>, let: "k" := Index elem_type ("ks", "i") in
            "body" "k" (InternalMapLookup ("mv", "k")))) in
    FinishRead "m";;
    "v".

End defs.
End map.

Module go.
Class MapSemantics {ext : ffi_syntax} `{!GoContext} :=
{
  equals_map_nil_l key_type elem_type m :
    go_equals (go.MapType key_type elem_type) #m #map.nil = Some $ bool_decide (m = map.nil);
  equals_map_nil_r key_type elem_type m :
    go_equals (go.MapType key_type elem_type) #map.nil #m = Some $ bool_decide (m = map.nil);

  is_map_pure (v : val) (m : val → bool * val) : Prop;
  map_default : val → val;
  mv_empty (dv : val) : val;

  is_map_pure_flatten mv m (H : is_map_pure mv m) :
    flatten_struct mv = [mv];
  map_lookup_pure k mv m (H : is_map_pure mv m) :
    map_lookup mv k = m k;
  is_map_pure_map_insert k v mv m (H : is_map_pure mv m) :
    is_map_pure (map_insert mv k v) (λ k', if decide (k' = k) then (true, v) else m k');
  is_map_pure_map_delete k mv m (H : is_map_pure mv m) :
    is_map_pure (map_delete mv k)
      (λ k', if decide (k' = k) then (false, map_default mv) else m k');
  is_map_pure_mv_empty dv : is_map_pure (mv_empty dv) (const (false, dv));

  map_default_mv_empty dv : map_default (mv_empty dv) = dv;
  map_default_map_insert m k v : map_default (map_insert m k v) = map_default m;
  map_default_map_delete m k : map_default (map_delete m k) = map_default m;

  is_map_domain_exists mv m (H : is_map_pure mv m) : ∃ ks, is_map_domain mv ks;
  is_map_domain_mv_empty dv ks : is_map_domain (mv_empty dv) ks → ks = [];
  is_map_domain_insert mv m ks :
    is_map_pure mv m →
    is_map_domain mv ks →
    NoDup ks ∧ (∀ k, (m k).1 = true ↔ k ∈ ks);

  clear_map key_type elem_type :
    #(functions go.clear [go.TypeLit $ go.MapType key_type elem_type]) =
    (λ: "m", Store "m" $ Read $
               FuncResolve go.make1 [go.TypeLit $ go.MapType key_type elem_type] #())%V;
  delete_map key_type elem_type :
    #(functions go.delete [go.TypeLit $ go.MapType key_type elem_type]) =
    (λ: "m" "k", Store "m" $ InternalMapDelete (Read "m", "k"))%V;
  make2_map key_type elem_type :
    #(functions go.make2 [go.TypeLit $ go.MapType key_type elem_type]) =
    (λ: "len",
       ref (mv_empty (go_zero_val elem_type)))%V;
  make1_map key_type elem_type :
    #(functions go.make2 [go.TypeLit $ go.MapType key_type elem_type]) =
    (λ: <>, FuncResolve go.make2 [go.TypeLit $ go.MapType key_type elem_type] #() #(W64 0))%V;
  len_map key_type elem_type :
    #(functions go.len [go.TypeLit $ go.MapType key_type elem_type]) =
    (λ: "m", ArrayLength (InternalMapDomain (Read "m")))%V;
}.
End go.
