/-
Method sets (https://go.dev/ref/spec#Method_sets): what the semantics knows of
`methodSet`, the function of `GoSemanticsFunctions` that `go.typeSetContains`
(`Interface.lean`) consults to decide whether a type implements an interface.

`methodSet t` maps the *id* of each method of `t` to its signature. A method's id
is Go's (`go/types.Id`): its name if it is exported, and its name qualified by its
package path (`"context.cancel"`) if not, since two unexported methods `m` of two
packages are distinct methods in Go (an interface with an unexported method can
only be implemented in its own package). goose names an interface's methods
(`go.MethodElem`) by their ids too.

The facts:
* A named type declared in a translated package: goose emits the method sets of `T`
  and of `*T` in `T.TypeAssumptions` (fields `method_set`, `ptr_method_set`), as the
  Go type checker (`go/types.NewMethodSet`) computes them: the methods declared with
  a value receiver (in both) or a pointer receiver (in `*T`'s), and those promoted
  through embedded fields, whether or not the methods' bodies are translated. They
  are `go.MethodSetIs` facts, which also say that no other method is in the set.
  For a generic type, the facts hold of every instantiation (a method set is the
  same, up to substituting the type arguments, for each one: Go does not allow
  embedding a type parameter).
* The predeclared types without methods, and the type literals whose method sets
  are empty in Go (`go.NoMethods`, below): `InterfaceSemantics.method_set_no_methods`.
* Anything else (a struct type literal with embedded fields, a type declared in a
  function body, a type of a package that is not translated) is unconstrained: the
  model knows nothing of its method set, so type-set membership is not provable
  there (it is less defined than Go, never more).
-/
module

public import Perennial.Golang.Defn.Predeclared

@[expose] public section

namespace Perennial

namespace go

/-- The entry for the method id `m` in a list of method-set entries, if any. An entry
is a method's id and its signature, or `none` for a signature goose could not write in
the package's translation (one that mentions a type of a package the translation does
not import, which an untranslated method may). -/
def methodSetLookup : List (GoString × Option go.signature) → GoString → Option (Option go.signature)
  | [], _ => none
  | (k, s) :: ms, m => if k = m then some s else methodSetLookup ms m

/-- `MethodSetIs t ms`: the method set of `t` is exactly the methods of `ms`: a method
id `m` is in it iff `ms` has an entry for `m`, with the signature of the entry when that
is known (`some sig`). goose emits these facts for the named types of a package
(`T.TypeAssumptions.method_set`, `ptr_method_set`). -/
class MethodSetIs [FfiSyntax] [GoSemanticsFunctions] (t : go.GoType)
    (ms : outParam (List (GoString × Option go.signature))) : Prop where
  method_set_is (m : GoString) :
    match methodSetLookup ms m with
    | none => methodSet t !! m = none
    | some (some sig) => methodSet t !! m = some sig
    | some none => methodSet t !! m ≠ none

export MethodSetIs (method_set_is)

/-- The predeclared types that have no methods (spec, "Method sets": only a defined
type or a pointer to one, an interface, or a struct with embedded fields has methods;
the predeclared types other than `error` have none, nor does `unsafe.Pointer`). -/
class inductive PredeclaredNoMethods : go.GoType → Prop
  | bool : PredeclaredNoMethods go.bool
  | string : PredeclaredNoMethods go.string
  | int : PredeclaredNoMethods go.int
  | int8 : PredeclaredNoMethods go.int8
  | int16 : PredeclaredNoMethods go.int16
  | int32 : PredeclaredNoMethods go.int32
  | int64 : PredeclaredNoMethods go.int64
  | uint : PredeclaredNoMethods go.uint
  | uint8 : PredeclaredNoMethods go.uint8
  | uint16 : PredeclaredNoMethods go.uint16
  | uint32 : PredeclaredNoMethods go.uint32
  | uint64 : PredeclaredNoMethods go.uint64
  | uintptr : PredeclaredNoMethods go.uintptr
  | float32 : PredeclaredNoMethods go.float32
  | float64 : PredeclaredNoMethods go.float64
  | complex64 : PredeclaredNoMethods go.complex64
  | complex128 : PredeclaredNoMethods go.complex128
  | unsafePointer : PredeclaredNoMethods unsafe.Pointer

attribute [instance] PredeclaredNoMethods.bool PredeclaredNoMethods.string
  PredeclaredNoMethods.int PredeclaredNoMethods.int8 PredeclaredNoMethods.int16
  PredeclaredNoMethods.int32 PredeclaredNoMethods.int64 PredeclaredNoMethods.uint
  PredeclaredNoMethods.uint8 PredeclaredNoMethods.uint16 PredeclaredNoMethods.uint32
  PredeclaredNoMethods.uint64 PredeclaredNoMethods.uintptr PredeclaredNoMethods.float32
  PredeclaredNoMethods.float64 PredeclaredNoMethods.complex64 PredeclaredNoMethods.complex128
  PredeclaredNoMethods.unsafePointer

/-- A struct field that is not embedded (it promotes no method). -/
class inductive NotEmbedded : go.field_decl → Prop
  | field (n : GoString) (t : go.GoType) : NotEmbedded (go.FieldDecl n t)

attribute [instance] NotEmbedded.field

/-- The types whose method set is empty in Go (spec, "Method sets": "The method set of
a defined type T consists of all methods declared with receiver type T. The method set
of a pointer to a defined type T (where T is neither a pointer nor an interface) is the
set of all methods declared with receiver *T or T", the method set of an interface type
is the intersection of the method sets of each type in its type set, and a struct type
gets the methods promoted through its embedded fields; "every type has a (possibly
empty) method set"): the predeclared types without methods and pointers to them; array,
slice, map, channel and function types; struct types without embedded fields; and
pointers to all of these and to pointers and interfaces (a pointer to an interface has
no methods). -/
class inductive NoMethods : go.GoType → Prop
  | predeclared (t : go.GoType) [PredeclaredNoMethods t] : NoMethods t
  | ptr_predeclared (t : go.GoType) [PredeclaredNoMethods t] : NoMethods (go.PointerType t)
  | array (n : Int) (t : go.GoType) : NoMethods (go.ArrayType n t)
  | slice (t : go.GoType) : NoMethods (go.SliceType t)
  | map (k v : go.GoType) : NoMethods (go.MapType k v)
  | chan (d : go.ChanDir) (t : go.GoType) : NoMethods (go.ChannelType d t)
  | func (sig : go.signature) : NoMethods (go.FunctionType sig)
  | struct (fds : List go.field_decl) [TCForall NotEmbedded fds] : NoMethods (go.StructType fds)
  | ptr_array (n : Int) (t : go.GoType) : NoMethods (go.PointerType (go.ArrayType n t))
  | ptr_slice (t : go.GoType) : NoMethods (go.PointerType (go.SliceType t))
  | ptr_map (k v : go.GoType) : NoMethods (go.PointerType (go.MapType k v))
  | ptr_chan (d : go.ChanDir) (t : go.GoType) : NoMethods (go.PointerType (go.ChannelType d t))
  | ptr_func (sig : go.signature) : NoMethods (go.PointerType (go.FunctionType sig))
  | ptr_struct (fds : List go.field_decl) [TCForall NotEmbedded fds] :
      NoMethods (go.PointerType (go.StructType fds))
  | ptr_ptr (t : go.GoType) : NoMethods (go.PointerType (go.PointerType t))
  | ptr_interface (elems : List go.InterfaceElem) :
      NoMethods (go.PointerType (go.InterfaceType elems))

attribute [instance] NoMethods.predeclared NoMethods.ptr_predeclared NoMethods.array
  NoMethods.slice NoMethods.map NoMethods.chan NoMethods.func NoMethods.struct
  NoMethods.ptr_array NoMethods.ptr_slice NoMethods.ptr_map NoMethods.ptr_chan
  NoMethods.ptr_func NoMethods.ptr_struct NoMethods.ptr_ptr NoMethods.ptr_interface

end go

end Perennial
