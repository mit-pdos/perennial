/-
The `Convert` rules on channel and pointer types (`Golang/Defn/Chan.lean`, `Golang/Defn/PostLang.lean`)
step on the conversions Go allows, found by instance search as a program proof finds them. The
conversions Go rejects that the rules used to step on (etcd-grove#59: `<-chan int` to `chan<- int`,
`chan<- int` to `<-chan int` or `chan int`, between two named channel types of different
directions, and between a named pointer type and another pointer type of the same underlying base)
have no rule; the differential harness checks the rules against Go on them
(`goose/model/reflect/harness`, `TestConvertLeanRules`).
-/
module

public import Perennial.Golang.Theory

@[expose] public section

namespace Perennial

section tests

variable [GooseExts] [GoLocalContext] [GoGlobalContext] [go.Semantics]

/-- `(<-chan E)(c)` for `c : chan E`. -/
example (e : go.GoType) (c : GoChan) :
    ⟦Convert (go.ChannelType .sendrecv e) (go.ChannelType .recvonly e), #c⟧ ⤳ #c :=
  inferInstance

/-- `(<-chan E)(c)` for `c : T`, `type T chan E`. -/
example (t e : go.GoType) [t ↓u go.ChannelType .sendrecv e] (c : GoChan) :
    ⟦Convert t (go.ChannelType .recvonly e), #c⟧ ⤳ #c :=
  inferInstance

/-- `U(c)` for `c : chan E`, `type U chan<- E`. -/
example (u e : go.GoType) [u ↓u go.ChannelType .sendonly e] (c : GoChan) :
    ⟦Convert (go.ChannelType .sendrecv e) u, #c⟧ ⤳ #c :=
  inferInstance

/-- `U(c)` for `c : T`, `type T <-chan E`, `type U <-chan E`: identical underlying types. -/
example (t u e : go.GoType) [t ↓u go.ChannelType .recvonly e] [u ↓u go.ChannelType .recvonly e]
    (c : GoChan) :
    ⟦Convert t u, #c⟧ ⤳ #c :=
  inferInstance

/-- `(*B)(p)` for `p : *A`, `A` and `B` of the same underlying type. -/
example (a b s : go.GoType) [a ↓u s] [b ↓u s] (l : Loc) :
    ⟦Convert (go.PointerType a) (go.PointerType b), #l⟧ ⤳ #l :=
  inferInstance

/-- `(*A)(p)` for `p : P`, `type P *A`: identical underlying types. -/
example (p a : go.GoType) [p ↓u go.PointerType a] (l : Loc) :
    ⟦Convert p (go.PointerType a), #l⟧ ⤳ #l :=
  inferInstance

/-- `Q(p)` for `p : P`, `type P *A`, `type Q *A`: identical underlying types. -/
example (p q a : go.GoType) [p ↓u go.PointerType a] [q ↓u go.PointerType a] (l : Loc) :
    ⟦Convert p q, #l⟧ ⤳ #l :=
  inferInstance

end tests

end Perennial
