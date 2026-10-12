/-
Results of `encoding/binary` derived from the linked ones, under their old names: the value
methods of `littleEndian` and `bigEndian` (`wp_littleEndian_Uint64`, ..., the Link's
`littleEndian.wp_Uint64`, ...), and the methods of `*littleEndian` and `*bigEndian` on the
globals `LittleEndian` and `BigEndian` (`wp_LittleEndian_Uint64`, ..., `wp_BigEndian_PutUint32`):
each the shared `_of` lemma of `PtrMethods.lean` applied to the linked results.
-/
module

public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.encoding.binary.PtrMethods

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace encoding.binary

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

/-- `littleEndian.wp_Uint64` under its old name. -/
theorem wp_littleEndian_Uint64 : littleEndian.Uint64.spec (GF := GF) (hG := hG) :=
  littleEndian.wp_Uint64

/-- `littleEndian.wp_PutUint64` under its old name. -/
theorem wp_littleEndian_PutUint64 : littleEndian.PutUint64.spec (GF := GF) (hG := hG) :=
  littleEndian.wp_PutUint64

/-- `littleEndian.wp_Uint32` under its old name. -/
theorem wp_littleEndian_Uint32 : littleEndian.Uint32.spec (GF := GF) (hG := hG) :=
  littleEndian.wp_Uint32

/-- `littleEndian.wp_PutUint32` under its old name. -/
theorem wp_littleEndian_PutUint32 : littleEndian.PutUint32.spec (GF := GF) (hG := hG) :=
  littleEndian.wp_PutUint32

/-- `bigEndian.wp_Uint64` under its old name. -/
theorem wp_bigEndian_Uint64 : bigEndian.Uint64.spec (GF := GF) (hG := hG) :=
  bigEndian.wp_Uint64

/-- `bigEndian.wp_PutUint64` under its old name. -/
theorem wp_bigEndian_PutUint64 : bigEndian.PutUint64.spec (GF := GF) (hG := hG) :=
  bigEndian.wp_PutUint64

/-- `bigEndian.wp_Uint32` under its old name. -/
theorem wp_bigEndian_Uint32 : bigEndian.Uint32.spec (GF := GF) (hG := hG) :=
  bigEndian.wp_Uint32

/-- `bigEndian.wp_PutUint32` under its old name. -/
theorem wp_bigEndian_PutUint32 : bigEndian.PutUint32.spec (GF := GF) (hG := hG) :=
  bigEndian.wp_PutUint32

/-- `(*littleEndian).Uint64` on the global `LittleEndian`. -/
theorem wp_LittleEndian_Uint64 (b : GoSlice) (bs : List w8) (dq : DFrac) (rem : List w8)
    (Hlen : bs.length = 8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦*{dq} (bs ++ rem) }}
      (App (Val ((globalAddr LittleEndian) @!! go.GoType.PointerType littleEndian.ty @!! go!"Uint64"))
        (Val #b))
    {{ RET #(leToU64 bs); b ↦*{dq} (bs ++ rem) }} :=
  wp_LittleEndian_Uint64_of littleEndian.wp_Uint64 b bs dq rem Hlen

/-- `(*littleEndian).PutUint64` on the global `LittleEndian`. -/
theorem wp_LittleEndian_PutUint64 (b : GoSlice) (space rem : List w8) (v : w64)
    (Hlen : space.length = 8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* (space ++ rem) }}
      (App (App (Val ((globalAddr LittleEndian) @!! go.GoType.PointerType littleEndian.ty @!! go!"PutUint64"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* (u64Le v ++ rem) }} :=
  wp_LittleEndian_PutUint64_of littleEndian.wp_PutUint64 b space rem v Hlen

/-- `(*littleEndian).Uint32` on the global `LittleEndian`. -/
theorem wp_LittleEndian_Uint32 (b : GoSlice) (bs : List w8) (dq : DFrac) (rem : List w8)
    (Hlen : bs.length = 4) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦*{dq} (bs ++ rem) }}
      (App (Val ((globalAddr LittleEndian) @!! go.GoType.PointerType littleEndian.ty @!! go!"Uint32"))
        (Val #b))
    {{ RET #(leToU32 bs); b ↦*{dq} (bs ++ rem) }} :=
  wp_LittleEndian_Uint32_of littleEndian.wp_Uint32 b bs dq rem Hlen

/-- `(*littleEndian).PutUint32` on the global `LittleEndian`. -/
theorem wp_LittleEndian_PutUint32 (b : GoSlice) (space rem : List w8) (v : w32)
    (Hlen : space.length = 4) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* (space ++ rem) }}
      (App (App (Val ((globalAddr LittleEndian) @!! go.GoType.PointerType littleEndian.ty @!! go!"PutUint32"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* (u32Le v ++ rem) }} :=
  wp_LittleEndian_PutUint32_of littleEndian.wp_PutUint32 b space rem v Hlen

/-- `(*bigEndian).Uint64` on the global `BigEndian`. -/
theorem wp_BigEndian_Uint64 (b : GoSlice) (bs : List w8) (dq : DFrac) (rem : List w8)
    (Hlen : bs.length = 8) :
    {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
      (App (Val ((globalAddr BigEndian) @!! go.GoType.PointerType bigEndian.ty @!! go!"Uint64"))
        (Val #b))
    {{ RET #(leToU64 bs.reverse); b ↦*{dq} (bs ++ rem) }} :=
  wp_BigEndian_Uint64_of bigEndian.wp_Uint64 b bs dq rem Hlen

/-- `(*bigEndian).PutUint64` on the global `BigEndian`. -/
theorem wp_BigEndian_PutUint64 (b : GoSlice) (space rem : List w8) (v : w64)
    (Hlen : space.length = 8) :
    {{ (b ↦* (space ++ rem) : IProp GF) }}
      (App (App (Val ((globalAddr BigEndian) @!! go.GoType.PointerType bigEndian.ty @!! go!"PutUint64"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* ((u64Le v).reverse ++ rem) }} :=
  wp_BigEndian_PutUint64_of bigEndian.wp_PutUint64 b space rem v Hlen

/-- `(*bigEndian).Uint32` on the global `BigEndian`. -/
theorem wp_BigEndian_Uint32 (b : GoSlice) (bs : List w8) (dq : DFrac) (rem : List w8)
    (Hlen : bs.length = 4) :
    {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
      (App (Val ((globalAddr BigEndian) @!! go.GoType.PointerType bigEndian.ty @!! go!"Uint32"))
        (Val #b))
    {{ RET #(leToU32 bs.reverse); b ↦*{dq} (bs ++ rem) }} :=
  wp_BigEndian_Uint32_of bigEndian.wp_Uint32 b bs dq rem Hlen

/-- `(*bigEndian).PutUint32` on the global `BigEndian`. -/
theorem wp_BigEndian_PutUint32 (b : GoSlice) (space rem : List w8) (v : w32)
    (Hlen : space.length = 4) :
    {{ (b ↦* (space ++ rem) : IProp GF) }}
      (App (App (Val ((globalAddr BigEndian) @!! go.GoType.PointerType bigEndian.ty @!! go!"PutUint32"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* ((u32Le v).reverse ++ rem) }} :=
  wp_BigEndian_PutUint32_of bigEndian.wp_PutUint32 b space rem v Hlen

end results

end encoding.binary

end Perennial
