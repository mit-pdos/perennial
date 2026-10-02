/-
Port of `new/golang/theory.v`: the complete Go theory (plus the ghost-state
libraries, as in Rocq).

## Proof tactics (overview; see the docstrings for details)

Rocq tactic names are kept. Intro/cases patterns are iris-lean's
(`%x`, `#H`, `⟨H1, H2⟩`, `-`), specialization patterns are `lem $$ [H1 $H2] %x`.

| tactic | file | what it does |
|---|---|---|
| `wp_pures`, `wp_pure [e]`, `wp_pure_lc H` | ProofMode | pure steps (`PureWp`) |
| `wp_call`, `wp_call_lc H` | ProofMode | beta step of a call whose head unfolds to `rec:` |
| `wp_bind [e]` | ProofMode | focus on a subexpression (none: Rocq `wp_bind_next`) |
| `wp_apply_core lem $$ spats` | ProofMode | apply a WP spec (Texan triple) in evaluation position |
| `wp_expr_simp` | ProofMode | normalize the WP expression |
| `wp_load`, `wp_store`, `wp_alloc l as H`, `wp_alloc_auto` | Mem | typed memory (`l ↦{dq} v`, via `Access`) |
| `wp_start [as pat]`, `wp_start_folded` | Auto | begin a function/method spec proof |
| `wp_func_call`, `wp_method_call` | Auto | unfold `#(functions f ts)` / `#(methods t m v)` |
| `wp_auto`, `wp_auto_lc n` | Auto | pure steps + loads/stores/allocs of locals + cleanup |
| `wp_apply lem $$ spats as pats [--no-auto] [--lc n]` | Auto | `wp_apply_core` + `iPkgInit` + intro + `wp_auto` |
| `wp_if_destruct`, `wp_for [H]`, `wp_for_post`, `wp_end` | Auto, Loop | control flow |
| `iPkgInit`, `solve_pkg_init` | Pkg | `is_pkg_init` goals |
| `iNamed H`, `iNamed 1`, `iNamedAccu`, `iNamedPrefix/Suffix`, `iFrameNamed`, `iExactEq H` | Helpers/NamedProps | named propositions `"H" ∷ P` |
| `iCombineNamed "H*" as Hout` | Experiments/Glob | glob over hypothesis names |
| `iStructNamed H`, `solve_into_val_typed_struct`, `solve_pointsto_access_struct`, `solve_typed_pointsto_agree` | PostLifting, Auto | struct points-to |

See `Perennial/Golang/Theory/Test.lean` for worked examples.
-/
import Perennial.Golang.Defn
import Perennial.Golang.Theory.Pre
import Perennial.Ghost
