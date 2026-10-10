/-
The layout of Go values in memory: a heap cell is a byte, a value of Lean representation
type `V` occupies `typeSize V` cells and is aligned to `typeAlign V`, the elements of an
array are `typeSize V` apart (`arrayIndexRef`), and the fields of a struct are at gc's
offsets (`StructLayout`), computed here from the fields' sizes and alignments as gc's
`types.CalcStructSize` does: each field at its offset rounded up to its alignment, a
struct whose last field has size 0 padded by a byte, the size rounded up to the largest
alignment.

The sizes are those of linux/amd64 (and every 64-bit gc target): `uint64`, `int`,
`uintptr`, `float64`, pointers, maps, channels and functions 8, strings and interfaces
16, slices 24. A value that is not a fixed-width integer (a pointer, slice, string,
interface, …) is one opaque cell at the start of its range; its other cells are owned
by no one (`IntoValTyped.wp_store_raw` writes only the first).
-/
module

public import Perennial.Golang.Defn.PostLang

@[expose] public section

namespace Perennial

namespace go

/-- `off` rounded up to a multiple of `al` (`al ≥ 1`). -/
def roundUp (off al : Int) : Int := (off + al - 1) / al * al

/-- The offsets of the fields `(name, size, align)` from `off` on, the end of the last,
and the largest alignment (at least `ma`). -/
def structLayoutAux : Int → Int → List (GoString × Int × Int) → List (GoString × Int) × Int × Int
  | off, ma, [] => ([], off, ma)
  | off, ma, (n, sz, al) :: fs =>
    let o := roundUp off al
    let r := structLayoutAux (o + sz) (max ma al) fs
    ((n, o) :: r.1, r.2.1, r.2.2)

/-- The layout has the fields' names, in order. -/
theorem structLayoutAux_names (off ma : Int) (fs : List (GoString × Int × Int)) :
    (structLayoutAux off ma fs).1.map Prod.fst = fs.map Prod.fst := by
  induction fs generalizing off ma with
  | nil => rfl
  | cons e fs ih => obtain ⟨n, sz, al⟩ := e; simp [structLayoutAux, ih]

/-- The offsets do not depend on the alignment so far. -/
theorem structLayoutAux_offsets_ma (off ma ma' : Int) (fs : List (GoString × Int × Int)) :
    (structLayoutAux off ma fs).1 = (structLayoutAux off ma' fs).1 := by
  induction fs generalizing off ma ma' with
  | nil => rfl
  | cons e fs ih =>
    obtain ⟨n, sz, al⟩ := e
    simp only [structLayoutAux]
    rw [ih _ _ (max ma' al)]

/-- gc's layout of a struct with fields `(name, size, align)`: the field offsets, the
size and the alignment. -/
def structLayout (fs : List (GoString × Int × Int)) : List (GoString × Int) × Int × Int :=
  let r := structLayoutAux 0 1 fs
  let size := if 0 < r.2.1 ∧ (fs.getLast?.map (·.2.1)) = some 0 then r.2.1 + 1 else r.2.1
  (r.1, roundUp size r.2.2, r.2.2)

/-- The offset of field `f` in gc's layout of `fs`. -/
def structFieldOffset (fs : List (GoString × Int × Int)) (f : GoString) : Option Int :=
  (structLayout fs).1.lookup f

theorem roundUp_ge (off al : Int) (hal : 1 ≤ al) : off ≤ roundUp off al := by
  unfold roundUp
  have hd := Int.emod_def (off + al - 1) al
  have hlt := Int.emod_lt_of_pos (off + al - 1) (by omega : 0 < al)
  have hnn := Int.emod_nonneg (off + al - 1) (by omega : al ≠ 0)
  rw [Int.mul_comm] at hd
  generalize (off + al - 1) / al * al = q at *
  generalize (off + al - 1) % al = r at *
  omega

/-- The fields' offsets are at least `off` and each field ends by the end. -/
theorem structLayoutAux_end (off ma : Int) (fs : List (GoString × Int × Int))
    (hsz : ∀ e ∈ fs, 0 ≤ e.2.1) (hal : ∀ e ∈ fs, 1 ≤ e.2.2) :
    off ≤ (structLayoutAux off ma fs).2.1 := by
  induction fs generalizing off ma with
  | nil => simp [structLayoutAux]
  | cons e fs ih =>
    obtain ⟨n, sz, al⟩ := e
    simp only [structLayoutAux]
    have h1 := roundUp_ge off al (hal _ (List.mem_cons_self ..))
    have h2 := hsz _ (List.mem_cons_self ..)
    have h3 := ih (roundUp off al + sz) (max ma al) (fun e he => hsz e (List.mem_cons_of_mem _ he))
      (fun e he => hal e (List.mem_cons_of_mem _ he))
    simp only at h2
    omega

theorem structLayout_size_ge (fs : List (GoString × Int × Int))
    (hsz : ∀ e ∈ fs, 0 ≤ e.2.1) (hal : ∀ e ∈ fs, 1 ≤ e.2.2) :
    (structLayoutAux 0 1 fs).2.1 ≤ (structLayout fs).2.1 := by
  have hma : 1 ≤ (structLayoutAux 0 1 fs).2.2 := by
    suffices ∀ off ma, 1 ≤ ma → 1 ≤ (structLayoutAux off ma fs).2.2 from this 0 1 (by omega)
    induction fs with
    | nil => intro off ma h; simpa [structLayoutAux] using h
    | cons e fs ih =>
      intro off ma h
      simp only [structLayoutAux]
      exact ih (fun e he => hsz e (List.mem_cons_of_mem _ he))
        (fun e he => hal e (List.mem_cons_of_mem _ he)) _ _ (by omega)
  simp only [structLayout]
  split
  · have := roundUp_ge ((structLayoutAux 0 1 fs).2.1 + 1) _ hma; omega
  · exact roundUp_ge _ _ hma

variable [FfiSyntax] [GoSemanticsFunctions]

/-- The struct with Lean representation `V` has fields `fs` (name, size, alignment, as
`(f, typeSize F, typeAlign F)` for a field of representation `F`), laid out as gc does.
Goose states this for every translated struct type (its `TypeAssumptions.layout`). -/
class StructLayout (V : Type) (fs : outParam (List (GoString × Int × Int))) : Prop where
  size : typeSize V = (structLayout fs).2.1
  align : typeAlign V = (structLayout fs).2.2
  field_ref : ∀ (f : GoString) (off : Int) (l : Loc), structFieldOffset fs f = some off →
    l.locCar ≠ 0 → structFieldRef V f l = l +ₗ off

/-- The sizes and alignments of the built-in representations. -/
class LayoutSemantics : Prop where
  typeSize_nonneg (V : Type) : 0 ≤ typeSize V
  typeAlign_pos (V : Type) : 1 ≤ typeAlign V
  typeSize_w8 : typeSize w8 = 1
  typeSize_w16 : typeSize w16 = 2
  typeSize_w32 : typeSize w32 = 4
  typeSize_w64 : typeSize w64 = 8
  typeSize_bool : typeSize Bool = 1
  typeSize_loc : typeSize Loc = 8
  typeSize_func : typeSize GoFunc = 8
  typeSize_string : typeSize GoString = 16
  typeSize_interface : typeSize GoInterface = 16
  typeSize_slice : typeSize GoSlice = 24
  typeSize_unit : typeSize Unit = 0
  typeSize_proph_id : typeSize proph_id = 8
  typeSize_array (V : Type) (n : Int) (h : 0 ≤ n) : typeSize (GoArray V n) = n * typeSize V
  typeAlign_w8 : typeAlign w8 = 1
  typeAlign_w16 : typeAlign w16 = 2
  typeAlign_w32 : typeAlign w32 = 4
  typeAlign_w64 : typeAlign w64 = 8
  typeAlign_bool : typeAlign Bool = 1
  typeAlign_loc : typeAlign Loc = 8
  typeAlign_func : typeAlign GoFunc = 8
  typeAlign_string : typeAlign GoString = 8
  typeAlign_interface : typeAlign GoInterface = 8
  typeAlign_slice : typeAlign GoSlice = 8
  typeAlign_unit : typeAlign Unit = 1
  typeAlign_proph_id : typeAlign proph_id = 8
  typeAlign_array (V : Type) (n : Int) : typeAlign (GoArray V n) = typeAlign V

attribute [simp] LayoutSemantics.typeSize_w8 LayoutSemantics.typeSize_w16
  LayoutSemantics.typeSize_w32 LayoutSemantics.typeSize_w64 LayoutSemantics.typeSize_bool
  LayoutSemantics.typeSize_loc LayoutSemantics.typeSize_func LayoutSemantics.typeSize_string
  LayoutSemantics.typeSize_interface LayoutSemantics.typeSize_slice LayoutSemantics.typeSize_unit
  LayoutSemantics.typeSize_proph_id LayoutSemantics.typeAlign_w8 LayoutSemantics.typeAlign_w16
  LayoutSemantics.typeAlign_w32 LayoutSemantics.typeAlign_w64 LayoutSemantics.typeAlign_bool
  LayoutSemantics.typeAlign_loc LayoutSemantics.typeAlign_func LayoutSemantics.typeAlign_string
  LayoutSemantics.typeAlign_interface LayoutSemantics.typeAlign_slice
  LayoutSemantics.typeAlign_unit LayoutSemantics.typeAlign_proph_id
  LayoutSemantics.typeAlign_array

export LayoutSemantics (typeSize_nonneg typeAlign_pos typeSize_w8 typeSize_w16 typeSize_w32
  typeSize_w64 typeSize_bool typeSize_loc typeSize_func typeSize_string typeSize_interface
  typeSize_slice typeSize_unit typeSize_proph_id typeSize_array typeAlign_w8 typeAlign_w16
  typeAlign_w32 typeAlign_w64 typeAlign_bool typeAlign_loc typeAlign_func typeAlign_string
  typeAlign_interface typeAlign_slice typeAlign_unit typeAlign_proph_id typeAlign_array)

end go

end Perennial
