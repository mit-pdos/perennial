/-
Port of `new/golang/theory/pre.v`: the Go theory without channels and strings
(which are built on top of it).
-/
import Perennial.GooseLang.Lang
import Perennial.Golang.Defn.Pre
import Perennial.Golang.Theory.ProofMode
import Perennial.Golang.Theory.PostLifting
import Perennial.Golang.Theory.Predeclared
import Perennial.Golang.Theory.Mem
import Perennial.Golang.Theory.Exception
import Perennial.Golang.Theory.Loop
import Perennial.Golang.Theory.Assume
import Perennial.Golang.Theory.Pkg
import Perennial.Golang.Theory.Auto
import Perennial.Golang.Theory.Defer
import Perennial.Golang.Theory.Array
