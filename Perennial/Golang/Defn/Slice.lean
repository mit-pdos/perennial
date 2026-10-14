module

public import Perennial.Golang.Defn.Loop
public import Perennial.Golang.Defn.Assume
public import Perennial.Golang.Defn.Predeclared

@[expose] public section

namespace Perennial

def sliceIndexRef [FfiSyntax] [GoSemanticsFunctions] (elem_type : Type) (i : Int) (s : GoSlice) :
    Loc :=
  arrayIndexRef elem_type i s.ptr

namespace slice
section goose_lang
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]

set_option linter.iris.dupNamespace false in
def slice (sl : GoSlice) (V : Type) (low high : U64) : GoSlice :=
  slice.mk (sliceIndexRef V (sint.Z low) sl) (high - low) (sl.cap - low)

def fullSlice (sl : GoSlice) (V : Type) (low high max : U64) : GoSlice :=
  slice.mk (sliceIndexRef V (sint.Z low) sl) (high - low) (max - low)

/-- only for internal use, not an external model -/
def _new_cap : val :=
  λ: "len",
    let: "extra" := ArbitraryInt in
    if: "len" <⟨go.int⟩ ("len" +⟨go.int⟩ "extra") then "len" +⟨go.int⟩ "extra"
    else "len"

/-- Copy `min(len(dst), len(src))` elements from `src` to `dst`, front to back. Only for
internal use: it is not Go's `copy` when the slices overlap with `dst` past `src` (it
then reads elements it has already overwritten); `copy` (`SliceSemantics.copy_slice`)
runs it twice, through a fresh buffer. -/
def copyForward (st elem_type : go.GoType) : val :=
  λ: "dst" "src",
    let: "i" := GoAlloc go.int (GoZeroVal go.int #()) in
    (for: (λ: <>, (![go.int] "i" <⟨go.int⟩ FuncResolve go.len [st] #() "dst") &&
             (![go.int] "i" <⟨go.int⟩ FuncResolve go.len [st] #() "src")) ; (λ: <>, #()) :=
       (λ: <>,
          do: (let: "i_val" := ![go.int] "i" in
               IndexRef st ("dst", "i_val")
                   <-[elem_type] ![elem_type] (IndexRef st ("src", "i_val")) ;;
               "i" <-[go.int] "i_val" +⟨go.int⟩ #(W64 1)))) ;;
    ![go.int] "i"

def forRange (elem_type : go.GoType) : val :=
  λ: "s" "body",
  let: "i" := GoAlloc go.int #(W64 0) in
  for: (λ: <>, (![go.int] "i") <⟨go.int⟩
          (FuncResolve go.len [go.SliceType elem_type]) #() "s") ;
                      (λ: <>, "i" <-[go.int] (![go.int] "i") +⟨go.int⟩ #(W64 1)) :=
    (λ: <>, "body" (![go.int] "i")
      (![elem_type] (IndexRef (go.SliceType elem_type) ("s", (![go.int] "i")))))

end goose_lang
end slice

attribute [irreducible] slice.forRange

namespace go
section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

def arrayLiteralSize (kvs : List keyed_element) : Int :=
  let (last, m) := (List.foldl (fun (cur_index, max_so_far) ke =>
                              match ke with
                              | KeyedElement none _ => (cur_index + 1, max_so_far)
                              | KeyedElement (some (KeyInteger cur_index')) _ =>
                                  (cur_index' + 1, Max.max cur_index max_so_far)
                              | _ => (0, 0)
                       ) ((0 : Int), (0 : Int)) kvs)
  Max.max (Max.max last m) 0

class SliceSemantics [GoSemanticsFunctions] : Prop where
  internal_len_step (s : GoSlice) :
    ⟦InternalSliceLen, #s⟧ ⤳ #(s.len)
  internal_cap_step (s : GoSlice) :
    ⟦InternalSliceCap, #s⟧ ⤳ #(s.cap)
  internal_make_slice_step (p : Loc) (l c : w64) :
    ⟦InternalMakeSlice, (#p, #l, #c)⟧ ⤳
    #(slice.mk p l c)
  internal_dynamic_array_alloc_step (et : go.GoType) (n : w64) :
    ⟦InternalDynamicArrayAlloc et, #n⟧ ⤳
    (GoAlloc (go.ArrayType (sint.Z n) et) (GoZeroVal (go.ArrayType (sint.Z n) et) #()))
  slice_slice_step_pure (elem_type : go.GoType) (s : GoSlice) (low high : w64) {V : Type}
    [ZeroVal V] [TypeRepr elem_type V] :
    ⟦Slice (go.SliceType elem_type), (#s, #low, #high)⟧ ⤳[under]
    (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ sint.Z s.cap then
       #(slice.slice s V low high)
     else Panic "slice bounds out of range")
  fullSlice_slice_step_pure (elem_type : go.GoType) (s : GoSlice) (low high max : w64) {V : Type}
    [ZeroVal V] [TypeRepr elem_type V] :
    ⟦FullSlice (go.SliceType elem_type), (#s, #low, #high, #max)⟧ ⤳[under]
    (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ sint.Z max ∧
        sint.Z max ≤ sint.Z s.cap then
       #(slice.fullSlice s V low high max)
     else Panic "slice bounds out of range")

  -- special case for slice equality
  is_go_op_go_equals_slice_nil_l (elem_type : go.GoType) (s : GoSlice) :
    ⟦GoOp GoEquals (go.SliceType elem_type), (#slice.nil, #s)⟧ ⤳[under]
      #(decide (s = slice.nil))
  is_go_op_go_equals_slice_nil_r (elem_type : go.GoType) (s : GoSlice) :
    ⟦GoOp GoEquals (go.SliceType elem_type), (#s, #slice.nil)⟧ ⤳[under]
      #(decide (s = slice.nil))

  clear_slice {elem_type st : go.GoType} [st ↓u go.SliceType elem_type] :
    FuncUnfold go.clear [st]
    (λ: "sl",
       let: "zero_sl" := FuncResolve go.make2 [st] #() (FuncResolve go.len [st] #() "sl") in
       FuncResolve go.copy [st] #() "sl" "zero_sl" ;;
    #() : val)

  /-- `copy(dst, src)` is a memmove: the two slices may overlap ("The source and
  destination may overlap", the Go spec), so all of `src` is read before `dst` is
  written, through a fresh buffer. (Copying front to back in place is wrong when `dst`
  starts past `src` in the same array, as in `copy(s[i+1:], s[i:])`: it reads elements
  it has already overwritten.) The result, the number of elements copied, is
  `min(len(dst), len(src))`, what the second `copyForward` returns. -/
  copy_slice {st elem_type : go.GoType} [st ↓u go.SliceType elem_type] :
    FuncUnfold go.copy [st]
    (λ: "dst" "src",
       let: "tmp" := FuncResolve go.make2 [st] #() (FuncResolve go.len [st] #() "src") in
       slice.copyForward st elem_type "tmp" "src" ;;
       slice.copyForward st elem_type "dst" "tmp" : val)

  make3_slice {st elem_type : go.GoType} [st ↓u go.SliceType elem_type] :
    FuncUnfold go.make3 [st]
    (λ: "len" "cap",
       if: ("cap" <⟨go.int⟩ "len") then Panic "makeslice: cap out of range" else #() ;;
       if: ("len" <⟨go.int⟩ #(W64 0)) then Panic "makeslice: len out of range" else #() ;;
       if: "cap" =⟨go.int⟩ #(W64 0) then
         -- XXX: this computes a nondeterministic unallocated address by using
         -- "(Loc 1 0) +ₗ ArbiraryInt"
         InternalMakeSlice (#(Loc.mk 1 0) +⟨go.PointerType elem_type⟩ ArbitraryInt, "len", "cap")
       else
         let: "p" := (InternalDynamicArrayAlloc elem_type) "cap" in
         InternalMakeSlice ("p", "len", "cap") : val)
  is_go_op_pointer_plus (t : go.GoType) (l : Loc) (x : w64) :
    ⟦GoOp GoPlus (go.PointerType t), (#l, #x)⟧ ⤳[under] (#(l +ₗ sint.Z x))

  make2_slice {st elem_type : go.GoType} [st ↓u go.SliceType elem_type] :
    FuncUnfold go.make2 [st]
    (λ: "sz", FuncResolve go.make3 [st] #() "sz" "sz" : val)

  index_ref_slice (elem_type : go.GoType) (i : w64) (s : GoSlice) {V : Type} [ZeroVal V]
    [TypeRepr elem_type V] :
    ⟦IndexRef (go.SliceType elem_type), (#s, #i)⟧ ⤳[under]
    (if 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len then
       #(sliceIndexRef V (sint.Z i) s)
     else Panic "slice index out of bounds")

  index_slice (elem_type : go.GoType) (i : w64) (s : GoSlice) :
    ⟦Index (go.SliceType elem_type), (#s, #i)⟧ ⤳[under]
    (GoLoad elem_type ((IndexRef (go.SliceType elem_type)) glv((#i, #s))))

  len_slice {st elem_type : go.GoType} [st ↓u go.SliceType elem_type] :
    FuncUnfold go.len [st]
    (λ: "s", InternalSliceLen "s" : val)

  cap_slice {st elem_type : go.GoType} [st ↓u go.SliceType elem_type] :
    FuncUnfold go.cap [st]
    (λ: "s", InternalSliceCap "s" : val)

  append_underlying (t : go.GoType) : functions go.append [t] = functions go.append [underlying t]
  append_slice {st elem_type : go.GoType} [st ↓u go.SliceType elem_type] :
    FuncUnfold go.append [st]
    (λ: "s" "x",
       let: "new_len" := sumAssumeNoOverflowSigned (FuncResolve go.len [st] #() "s")
                           (FuncResolve go.len [st] #() "x") in
       if: (FuncResolve go.cap [st] #() "s") ≥⟨go.int⟩ "new_len" then
         -- "grow" s to include its capacity
         let: "s_new" := Slice st ("s", #(W64 0), "new_len") in
         -- copy "x" past the original "s"
         FuncResolve go.copy [st] #() (Slice st ("s_new", FuncResolve go.len [st] #() "s", "new_len"))
           "x" ;;
         "s_new"
       else
         let: "new_cap" := slice._new_cap "new_len" in
         let: "s_new" := FuncResolve go.make3 [st] #() "new_len" "new_cap" in
         FuncResolve go.copy [st] #() "s_new" "s" ;;
         FuncResolve go.copy [st] #() (Slice st ("s_new", FuncResolve go.len [st] #() "s", "new_len"))
           "x" ;;
         "s_new" : val)

  composite_literal_slice (elem_type : go.GoType) (kvs : List keyed_element) :
    ⟦CompositeLiteral (go.SliceType elem_type), (LiteralValueV kvs)⟧ ⤳[under]
    (
      let len := arrayLiteralSize kvs
      if len < 2^63 then
        gl(let: "tmp" := GoAlloc (go.ArrayType len elem_type)
                           (GoZeroVal (go.ArrayType len elem_type) #()) in
         "tmp" <-[(go.ArrayType len elem_type)]
                  CompositeLiteral (go.ArrayType len elem_type) (LiteralValueV kvs) ;;
         Slice (go.ArrayType len elem_type) ("tmp", #(W64 0), #(W64 len)))
      else gl(AngelicExit #())
        )

  arrayIndexRef_0 (t : Type) (l : Loc) : arrayIndexRef t 0 l = l

attribute [instance] SliceSemantics.internal_len_step SliceSemantics.internal_cap_step
  SliceSemantics.internal_make_slice_step SliceSemantics.internal_dynamic_array_alloc_step
  SliceSemantics.slice_slice_step_pure SliceSemantics.fullSlice_slice_step_pure
  SliceSemantics.is_go_op_go_equals_slice_nil_l SliceSemantics.is_go_op_go_equals_slice_nil_r
  SliceSemantics.clear_slice SliceSemantics.copy_slice SliceSemantics.make3_slice
  SliceSemantics.is_go_op_pointer_plus SliceSemantics.make2_slice SliceSemantics.index_ref_slice
  SliceSemantics.index_slice SliceSemantics.len_slice SliceSemantics.cap_slice
  SliceSemantics.append_slice SliceSemantics.composite_literal_slice
export SliceSemantics (internal_len_step internal_cap_step internal_make_slice_step
  internal_dynamic_array_alloc_step slice_slice_step_pure fullSlice_slice_step_pure
  is_go_op_go_equals_slice_nil_l is_go_op_go_equals_slice_nil_r clear_slice copy_slice
  make3_slice is_go_op_pointer_plus make2_slice index_ref_slice index_slice len_slice cap_slice
  append_underlying append_slice composite_literal_slice arrayIndexRef_0)

end defs
end go

end Perennial
