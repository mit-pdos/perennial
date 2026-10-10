/-
The complete Go theory (plus the ghost-state libraries).

## Proof tactics (overview; see the docstrings for details)

Intro/cases patterns are iris-lean's
(`%x`, `#H`, `⟨H1, H2⟩`, `-`), specialization patterns are `lem $$ [H1 $H2] %x`.

| tactic | file | what it does |
|---|---|---|
| `wp_pures`, `wp_pure [e]`, `wp_pure_lc H` | ProofMode | pure steps (`PureWp`) |
| `wp_call`, `wp_call_lc H` | ProofMode | beta step of a call whose head unfolds to `rec:` |
| `wp_bind [e]` | ProofMode | focus on a subexpression |
| `wp_apply_core lem $$ spats` | ProofMode | apply a WP spec (Texan triple) in evaluation position |
| `wp_expr_simp` | ProofMode | normalize the WP expression |
| `wp_load`, `wp_store`, `wp_alloc l as H`, `wp_alloc_auto` | Mem | typed memory (`l ↦{dq} v`, via `Access`) |
| `wp_start [as pat]`, `wp_start_folded` | Auto | begin a function/method spec proof |
| `wp_func_call`, `wp_method_call` | Auto | unfold `#(functions f ts)` / `#(methods t m v)` |
| `wp_auto`, `wp_auto_lc n` | Auto | pure steps + loads/stores/allocs of locals + cleanup |
| `wp_apply [+noauto] [(lc := n)] lem $$ spats as pats` | Auto | `wp_apply_core` + `iPkgInit` + intro + `wp_auto` |
| `wp_if_destruct`, `wp_for [H]`, `wp_for_post`, `wp_end` | Auto, Loop | control flow |
| `wp_join R with [H..] as pats`, `wp_join_done` | Join | prove the cases of an `if:` (or a case split) up to `R`, the rest of the function once |
| `iPkgInit`, `solve_pkg_init` | Pkg | `isPkgInit` goals |
| `iNamed H`, `iNamed 1`, `iNamedAccu`, `iNamedPrefix/Suffix`, `iFrameNamed`, `iExactEq H` | Helpers/NamedProps | named propositions `"H" ∷ P` |
| `s ↦*{dq} vs`, `ownSliceCap V s dq`, `mref ↦${dq} m` | Slice, Map | slice and map points-to (specs `wp_slice_*`, `wp_map_*`) |
| `iStructNamed H`, `solve_into_val_typed_struct`, `solve_pointsto_access_struct`, `solve_typed_pointsto_agree` | PostLifting, Auto | struct points-to |

See `Perennial/Golang/Theory/Test.lean` for worked examples.
-/
module

public import Perennial.Golang.Defn
public import Perennial.Golang.Theory.Pre
public import Perennial.Golang.Theory.Bytes
public import Perennial.Golang.Theory.String
public import Perennial.Golang.Theory.Join
public import Perennial.Ghost

@[expose] public section
