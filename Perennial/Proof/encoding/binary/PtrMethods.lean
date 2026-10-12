/-
The methods of `*littleEndian` and `*bigEndian` on the globals `LittleEndian` and `BigEndian`
(`ptr_Uint64_unfold`, ... in the method sets of the pointer types: load the global, call the
value method), from the value methods' specs. Not Go functions of their own (goose generates
the wrappers); stated for the linked specs in `Results.lean` (`wp_LittleEndian_Uint64`, ...).
-/
module

public import Perennial.Spec.encoding.binary.littleEndian__Uint64
public import Perennial.Spec.encoding.binary.littleEndian__PutUint64
public import Perennial.Spec.encoding.binary.littleEndian__Uint32
public import Perennial.Spec.encoding.binary.littleEndian__PutUint32
public import Perennial.Spec.encoding.binary.bigEndian__Uint64
public import Perennial.Spec.encoding.binary.bigEndian__PutUint64
public import Perennial.Spec.encoding.binary.bigEndian__Uint32
public import Perennial.Spec.encoding.binary.bigEndian__PutUint32

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace encoding.binary

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

/-- `(*littleEndian).Uint64` on the global `LittleEndian` (`ptr_Uint64_unfold`:
load the global, call the value method), from the value method's spec. -/
theorem wp_LittleEndian_Uint64_of
    (wp_littleEndian_Uint64 : littleEndian.Uint64.spec (GF := GF) (hG := hG))
    (b : GoSlice) (bs : List w8) (dq : DFrac) (rem : List w8)
    (Hlen : bs.length = 8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦*{dq} (bs ++ rem) }}
      (App (Val ((globalAddr LittleEndian) @!! go.GoType.PointerType littleEndian.ty @!! go!"Uint64"))
        (Val #b))
    {{ RET #(leToU64 bs); b ↦*{dq} (bs ++ rem) }} := by
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := isPkgInit_access (PROP := IProp GF) pkg_id.encoding.binary $$ Hpkg
  wp_auto
  wp_apply wp_littleEndian_Uint64 _ b bs rem dq Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

/-- `(*littleEndian).PutUint64` on the global `LittleEndian` (`ptr_PutUint64_unfold`:
load the global, call the value method), from the value method's spec. -/
theorem wp_LittleEndian_PutUint64_of
    (wp_littleEndian_PutUint64 : littleEndian.PutUint64.spec (GF := GF) (hG := hG))
    (b : GoSlice) (space rem : List w8) (v : w64)
    (Hlen : space.length = 8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* (space ++ rem) }}
      (App (App (Val ((globalAddr LittleEndian) @!! go.GoType.PointerType littleEndian.ty @!! go!"PutUint64"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* (u64Le v ++ rem) }} := by
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := isPkgInit_access (PROP := IProp GF) pkg_id.encoding.binary $$ Hpkg
  wp_auto
  wp_apply wp_littleEndian_PutUint64 _ b space rem v Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

/-- `(*littleEndian).Uint32` on the global `LittleEndian` (`ptr_Uint32_unfold`:
load the global, call the value method), from the value method's spec. -/
theorem wp_LittleEndian_Uint32_of
    (wp_littleEndian_Uint32 : littleEndian.Uint32.spec (GF := GF) (hG := hG))
    (b : GoSlice) (bs : List w8) (dq : DFrac) (rem : List w8)
    (Hlen : bs.length = 4) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦*{dq} (bs ++ rem) }}
      (App (Val ((globalAddr LittleEndian) @!! go.GoType.PointerType littleEndian.ty @!! go!"Uint32"))
        (Val #b))
    {{ RET #(leToU32 bs); b ↦*{dq} (bs ++ rem) }} := by
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := isPkgInit_access (PROP := IProp GF) pkg_id.encoding.binary $$ Hpkg
  wp_auto
  wp_apply wp_littleEndian_Uint32 _ b bs rem dq Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

/-- `(*littleEndian).PutUint32` on the global `LittleEndian` (`ptr_PutUint32_unfold`:
load the global, call the value method), from the value method's spec. -/
theorem wp_LittleEndian_PutUint32_of
    (wp_littleEndian_PutUint32 : littleEndian.PutUint32.spec (GF := GF) (hG := hG))
    (b : GoSlice) (space rem : List w8) (v : w32)
    (Hlen : space.length = 4) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* (space ++ rem) }}
      (App (App (Val ((globalAddr LittleEndian) @!! go.GoType.PointerType littleEndian.ty @!! go!"PutUint32"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* (u32Le v ++ rem) }} := by
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := isPkgInit_access (PROP := IProp GF) pkg_id.encoding.binary $$ Hpkg
  wp_auto
  wp_apply wp_littleEndian_PutUint32 _ b space rem v Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

/-- `(*bigEndian).Uint64` on the global `BigEndian` (`ptr_Uint64_unfold`:
load the global, call the value method), from the value method's spec. -/
theorem wp_BigEndian_Uint64_of
    (wp_bigEndian_Uint64 : bigEndian.Uint64.spec (GF := GF) (hG := hG))
    (b : GoSlice) (bs : List w8) (dq : DFrac) (rem : List w8)
    (Hlen : bs.length = 8) :
    {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
      (App (Val ((globalAddr BigEndian) @!! go.GoType.PointerType bigEndian.ty @!! go!"Uint64"))
        (Val #b))
    {{ RET #(leToU64 bs.reverse); b ↦*{dq} (bs ++ rem) }} := by
  wp_start as Hb
  wp_apply (wp_load_struct_nofields (V := bigEndian)) as -
  wp_apply wp_bigEndian_Uint64 _ b bs rem dq Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

/-- `(*bigEndian).PutUint64` on the global `BigEndian` (`ptr_PutUint64_unfold`:
load the global, call the value method), from the value method's spec. -/
theorem wp_BigEndian_PutUint64_of
    (wp_bigEndian_PutUint64 : bigEndian.PutUint64.spec (GF := GF) (hG := hG))
    (b : GoSlice) (space rem : List w8) (v : w64)
    (Hlen : space.length = 8) :
    {{ (b ↦* (space ++ rem) : IProp GF) }}
      (App (App (Val ((globalAddr BigEndian) @!! go.GoType.PointerType bigEndian.ty @!! go!"PutUint64"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* ((u64Le v).reverse ++ rem) }} := by
  wp_start as Hb
  wp_apply (wp_load_struct_nofields (V := bigEndian)) as -
  wp_apply wp_bigEndian_PutUint64 _ b space rem v Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

/-- `(*bigEndian).Uint32` on the global `BigEndian` (`ptr_Uint32_unfold`:
load the global, call the value method), from the value method's spec. -/
theorem wp_BigEndian_Uint32_of
    (wp_bigEndian_Uint32 : bigEndian.Uint32.spec (GF := GF) (hG := hG))
    (b : GoSlice) (bs : List w8) (dq : DFrac) (rem : List w8)
    (Hlen : bs.length = 4) :
    {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
      (App (Val ((globalAddr BigEndian) @!! go.GoType.PointerType bigEndian.ty @!! go!"Uint32"))
        (Val #b))
    {{ RET #(leToU32 bs.reverse); b ↦*{dq} (bs ++ rem) }} := by
  wp_start as Hb
  wp_apply (wp_load_struct_nofields (V := bigEndian)) as -
  wp_apply wp_bigEndian_Uint32 _ b bs rem dq Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

/-- `(*bigEndian).PutUint32` on the global `BigEndian` (`ptr_PutUint32_unfold`:
load the global, call the value method), from the value method's spec. -/
theorem wp_BigEndian_PutUint32_of
    (wp_bigEndian_PutUint32 : bigEndian.PutUint32.spec (GF := GF) (hG := hG))
    (b : GoSlice) (space rem : List w8) (v : w32)
    (Hlen : space.length = 4) :
    {{ (b ↦* (space ++ rem) : IProp GF) }}
      (App (App (Val ((globalAddr BigEndian) @!! go.GoType.PointerType bigEndian.ty @!! go!"PutUint32"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* ((u32Le v).reverse ++ rem) }} := by
  wp_start as Hb
  wp_apply (wp_load_struct_nofields (V := bigEndian)) as -
  wp_apply wp_bigEndian_PutUint32 _ b space rem v Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

end wps

end encoding.binary

end Perennial
