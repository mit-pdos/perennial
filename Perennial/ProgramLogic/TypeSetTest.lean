/-
Type-set membership from method sets (`go_type_set`, `Golang/Theory/TypeSet.lean`):
examples (regression test), with the method sets of a package's named types (its
`Assumptions`) and of the types without methods (the semantics).
-/
module

public import Perennial.Golang.Theory
public import Perennial.Code.errors
public import Perennial.Code.context
public import Perennial.Code.io
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.unittest
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.filteredimport

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace TypeSetTest

section std
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [sem : go.Semantics]

section errors
variable [errors.Assumptions]

/-- `*errors.errorString` (`Error` with a pointer receiver) implements `error`. -/
example : go.typeSetContains (go.GoType.PointerType errors.errorString.ty) go.error = true := by
  go_type_set

/-- `errors.errorString` itself does not: `Error` has a pointer receiver. -/
example : go.typeSetContains errors.errorString.ty go.error = false := by
  go_type_set

/-- `*errors.joinError`'s `Unwrap() []error` is not `Unwrap() error`. -/
example : go.typeSetContains (go.GoType.PointerType errors.joinError.ty)
    (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])]) = false := by
  go_type_set

example : go.typeSetContains (go.GoType.PointerType errors.joinError.ty)
    (go.InterfaceType [go.MethodElem go!"Unwrap"
      (go.Signature [] false [go.GoType.SliceType go.error])]) = true := by
  go_type_set

end errors

section context
variable [context.Assumptions]

/-- `context.deadlineExceededError` (value receivers) implements `error`, and so does a
pointer to it. -/
example : go.typeSetContains context.deadlineExceededError.ty go.error = true := by
  go_type_set

example : go.typeSetContains (go.GoType.PointerType context.deadlineExceededError.ty)
    go.error = true := by
  go_type_set

/-- A named interface type of the package: `*cancelCtx` implements `Context` (its methods
`Done`, `Err`, `Value` and the promoted `Deadline` of its embedded `Context`), and
`canceler`, whose unexported method `cancel` is `context`'s. -/
example : go.typeSetContains (go.GoType.PointerType context.cancelCtx.ty) context.Context.ty =
    true := by
  go_type_set

example : go.typeSetContains (go.GoType.PointerType context.cancelCtx.ty) context.canceler.ty =
    true := by
  go_type_set

/-- The value `cancelCtx` does not implement `Context`: only `Deadline` (promoted from the
embedded `Context` field) is in its method set. -/
example : go.typeSetContains context.cancelCtx.ty context.Context.ty = false := by
  go_type_set

/-- An interface with an unexported method `cancel` of another package is not implemented
by `*cancelCtx`: method ids are qualified by their package. -/
example : go.typeSetContains (go.GoType.PointerType context.cancelCtx.ty)
    (go.InterfaceType [go.MethodElem go!"otherpkg.cancel"
      (go.Signature [go.bool, go.error, go.error] false [])]) = false := by
  go_type_set

end context

section io
variable [io.Assumptions] [errors.Assumptions]

/-- An interface embedding other interfaces (`io.ReadWriter`): its type set is the
intersection, written out as their methods. -/
example : go.typeSetContains (go.GoType.PointerType errors.errorString.ty) io.ReadWriter.ty =
    false := by
  go_type_set

end io

section generics
open github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics
variable [github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Assumptions]

/-- A generic type: `Box[T]`'s method `Get() T` at each instantiation. -/
example : go.typeSetContains (Box.ty go.int)
    (go.InterfaceType [go.MethodElem go!"Get" (go.Signature [] false [go.int])]) = true := by
  go_type_set

example : go.typeSetContains (Box.ty go.int)
    (go.InterfaceType [go.MethodElem go!"Get" (go.Signature [] false [go.string])]) = false := by
  go_type_set

end generics

section filteredimport
open github_com.mit_pdos.perennial.goose.testdata.examples.filteredimport
variable [github_com.mit_pdos.perennial.goose.testdata.examples.filteredimport.Assumptions]

/-- `Getter` embeds `withDep`, whose method `Use` mentions a type of a package the translation
does not import: goose writes `Getter` as `Close`, `Get` and the type term `withDep`, whose
membership is unspecified (`interfaceTermContains`). A type lacking a written method is still
known not to implement it. -/
example : go.typeSetContains T.ty Getter.ty = false := by
  go_type_set

/-- `PlainCloser` embeds `plain`, all of whose methods are written. -/
example : go.typeSetContains (go.GoType.PointerType T.ty) PlainCloser.ty = false := by
  go_type_set

end filteredimport

end std

/-! The goose example package `unittest` (whose translation uses the disk FFI's
`FfiSyntax` instance). -/
section unittest
open github_com.mit_pdos.perennial.goose.testdata.examples.unittest
variable [GoLocalContext] [GoGlobalContext] [sem : go.Semantics]
variable [github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

/-- A user package's named interface type `Fooer`: `*concreteFooer` implements it (`Foo`
has a pointer receiver), `concreteFooer` does not. -/
example : go.typeSetContains (go.GoType.PointerType concreteFooer.ty) Fooer.ty = true := by
  go_type_set

example : go.typeSetContains concreteFooer.ty Fooer.ty = false := by
  go_type_set

/-- Promotion through an embedded field (`embedD` embeds `embedC`, which embeds `*embedB`,
...): the value `embedD` has `Foo`. -/
example : go.typeSetContains embedD.ty
    (go.InterfaceType [go.MethodElem go!"Foo" (go.Signature [] false [go.string])]) = true := by
  go_type_set

/-- `method_sets.go`: a named interface embedding another and adding an unexported method
(`msNamerTagger`), implemented by a struct embedding a pointer (`msPtrEmbed`, whose value
has the pointer-receiver `tag` of `*msLeft`); a method promoted from two fields at the same
depth is in neither's method set (`msBoth`), nor one shadowed by a field (`msShadow`). -/
example : go.typeSetContains msPtrEmbed.ty msNamerTagger.ty = true := by
  go_type_set

example : go.typeSetContains msLeft.ty msNamerTagger.ty = false := by
  go_type_set

example : go.typeSetContains (go.GoType.PointerType msLeft.ty) msNamerTagger.ty = true := by
  go_type_set

example : go.typeSetContains (go.GoType.PointerType msBoth.ty) msNamer.ty = false := by
  go_type_set

example : go.typeSetContains (go.GoType.PointerType msShadow.ty) msNamer.ty = false := by
  go_type_set

/-- Types without methods: `[]int`, `*int`, `int`. -/
example : go.typeSetContains (go.GoType.SliceType go.int) Fooer.ty = false := by
  go_type_set

example : go.typeSetContains (go.GoType.PointerType go.int) Fooer.ty = false := by
  go_type_set

/-- Every type is in `any`'s type set. -/
example : go.typeSetContains concreteFooer.ty go.any = true := by
  go_type_set

end unittest

end TypeSetTest

end Perennial
