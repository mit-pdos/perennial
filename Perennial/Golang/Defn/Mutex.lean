/-
The type `go.mutex` of the lock models (`sync.Mutex`, goose_lang/primitive's `Mutex`), laid
out as gc lays out a `sync.Mutex`; its lock is `Lock.lean`'s.
-/
module

public import Perennial.Golang.Defn.Predeclared

@[expose] public section

namespace Perennial

/-- The value of a modelled mutex (`go.mutex`): whether it is locked. -/
structure MutexState where
  locked : Bool
deriving DecidableEq, Inhabited

instance : ZeroVal MutexState := ⟨⟨false⟩⟩

namespace go

/-- The underlying type of the lock models (`sync.Mutex`, and goose_lang/primitive's
`Mutex`, a struct of one `sync.Mutex`). -/
def mutex : go.GoType := go.Named go!"mutex" []

section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

/-- A `go.mutex` occupies what gc's `sync.Mutex` does (`struct{ state int32; sema uint32 }`
inside: 8 bytes, aligned to 4), so that the offsets of the fields of a struct holding one
are gc's (`go.StructLayout`); the model keeps the lock in the first cell, as a `bool`
(`lock.lock`), and leaves the other 7 cells `LitPad`. Go's representation of the state is
not modelled: reading a mutex's bytes through `unsafe` is stuck (the first cell holds a
`bool`, not a byte), and copying a mutex copies its first cell only. -/
class MutexSemantics [GoSemanticsFunctions] : Prop where
  underlying_mutex : go.mutex ↓u go.mutex
  type_repr_mutex : TypeReprUnderlying go.mutex MutexState
  /-- A mutex's value is its `bool`'s. -/
  mutex_val (b : Bool) : #(MutexState.mk b) = #b
  typeSize_mutex : typeSize MutexState = 8
  typeAlign_mutex : typeAlign MutexState = 4
  alloc_mutex (v : val) :
    ⟦GoAlloc go.mutex, v⟧ ⤳[internalUnder]
      (Let "l" (AllocN (Val (PairV (LitV (LitInt (W64 8))) (LitV (LitInt (W64 4)))))
          (Val (LitV LitPad)))
        gl(GoStore go.bool ("l", v) ;; "l"))
  load_mutex (l : val) :
    ⟦GoLoad go.mutex, l⟧ ⤳[internalUnder] App (Val (GoInstruction (GoLoad go.bool))) (Val l)
  store_mutex (l v : val) :
    ⟦GoStore go.mutex, (l, v)⟧ ⤳[internalUnder]
      App (Val (GoInstruction (GoStore go.bool))) (Val (PairV l v))

attribute [instance] MutexSemantics.underlying_mutex MutexSemantics.type_repr_mutex
  MutexSemantics.alloc_mutex MutexSemantics.load_mutex MutexSemantics.store_mutex
attribute [simp] MutexSemantics.typeSize_mutex MutexSemantics.typeAlign_mutex
export MutexSemantics (underlying_mutex type_repr_mutex mutex_val typeSize_mutex typeAlign_mutex)

end defs

end go

end Perennial
