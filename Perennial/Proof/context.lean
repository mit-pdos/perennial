/-
The proofs of the Go `context` package: the shared definitions (`Base`, `BackgroundCtx`,
`CancelCtxCells`, `CancelCtxContext`, `TimerCtx`, `PropagateCancel`, `WithCancelGen`,
`NewErrorString`), the linked results (`Link`), `context.wp_<F>` for each function `F` (and
`context.wp_initialize'`, the package's initialization), and what is derived from them, under
the old names (`Results`). See `Base.lean` for the design.
-/
module

public import Perennial.Proof.context.Base
public import Perennial.Proof.context.BackgroundCtx
public import Perennial.Proof.context.CancelCtxCells
public import Perennial.Proof.context.CancelCtxContext
public import Perennial.Proof.context.TimerCtx
public import Perennial.Proof.context.PropagateCancel
public import Perennial.Proof.context.WithCancelGen
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.context.Link
public import Perennial.Proof.context.Results

@[expose] public section
