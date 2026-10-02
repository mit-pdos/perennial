/-
Port of `new/golang/theory/predeclared.v`: `IntoValTypedUnderlying` instances
for the predeclared Go types (integers, `bool`, `string`, `unsafe.Pointer`,
floats, `proph_id`).
-/
import Perennial.Golang.Theory.PostLifting

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section into_val_typed_instances
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

attribute [local instance] go.tagged_internal_inst

instance into_val_typed_uint64 : IntoValTypedUnderlying (GF := GF) w64 go.uint64 := by
  solve_into_val_typed
instance into_val_typed_uint32 : IntoValTypedUnderlying (GF := GF) w32 go.uint32 := by
  solve_into_val_typed
instance into_val_typed_uint16 : IntoValTypedUnderlying (GF := GF) w16 go.uint16 := by
  solve_into_val_typed
instance into_val_typed_uint8 : IntoValTypedUnderlying (GF := GF) w8 go.uint8 := by
  solve_into_val_typed
instance into_val_typed_uint : IntoValTypedUnderlying (GF := GF) w64 go.uint := by
  solve_into_val_typed
instance into_val_typed_int64 : IntoValTypedUnderlying (GF := GF) w64 go.int64 := by
  solve_into_val_typed
instance into_val_typed_int32 : IntoValTypedUnderlying (GF := GF) w32 go.int32 := by
  solve_into_val_typed
instance into_val_typed_int16 : IntoValTypedUnderlying (GF := GF) w16 go.int16 := by
  solve_into_val_typed
instance into_val_typed_int8 : IntoValTypedUnderlying (GF := GF) w8 go.int8 := by
  solve_into_val_typed
instance into_val_typed_int : IntoValTypedUnderlying (GF := GF) w64 go.int := by
  solve_into_val_typed
instance into_val_typed_bool : IntoValTypedUnderlying (GF := GF) Bool go.bool := by
  solve_into_val_typed
instance into_val_typed_string : IntoValTypedUnderlying (GF := GF) go_string go.string := by
  solve_into_val_typed
instance into_val_typed_Pointer : IntoValTypedUnderlying (GF := GF) loc unsafe.Pointer := by
  solve_into_val_typed
instance into_val_typed_proph_id :
    IntoValTypedUnderlying (GF := GF) Perennial.proph_id go.proph_id := by
  solve_into_val_typed
instance into_val_typed_float64 : IntoValTypedUnderlying (GF := GF) w64 go.float64 := by
  solve_into_val_typed
instance into_val_typed_float32 : IntoValTypedUnderlying (GF := GF) w32 go.float32 := by
  solve_into_val_typed

end into_val_typed_instances

end Perennial
