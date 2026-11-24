/-
The proofs of the Go `fmt` package. `Sprintf`, `Errorf` and `Fprint` are the real `fmt`'s, translated
(`PrintDefs`: the vocabulary of the specs of the real printer; `OutLemmas`: `Sprintf`'s output
without methods); `errorf`, `Printf`, `Fprintf` and `pp.doPrint` are the Go model of
`goose/model/overlay/fmt`, which formats with the model printer (also translated), with
the shared definitions (`Base`: `isPkgInit`, `SprintfOut`,
the decimals of the integer directives, `ArgsWf`; `Directives`: a format's directives; `Args`:
the specs' premise on the arguments, `argsOk`, and what `Errorf` returns), the specs of the helpers
of the model printer (`SprintfModel`, `BytesModel`, `VisitModel`, `DoPrintf`; `PrintArgs`: `Fprint`'s premise on its
operands, `printArgOk`), the linked results (`Link`), `fmt.wp_<F>`
for each function `F`, and results derived from them (`Results`).
-/
module

public import Perennial.Proof.fmt.Base
public import Perennial.Proof.fmt.PrintDefs
public import Perennial.Proof.fmt.OutLemmas
public import Perennial.Proof.fmt.Directives
public import Perennial.Proof.fmt.Args
public import Perennial.Proof.fmt.SprintfModel
public import Perennial.Proof.fmt.VisitModel
public import Perennial.Proof.fmt.PrintArgs
public import Perennial.Proof.fmt.DoPrintf
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.fmt.Results

@[expose] public section
