package glang

// Lean 4 backend for the GooseLang printer.
//
// The Lean output is the analogue of the Rocq output (same definitions with the
// same names), but GooseLang expressions are printed as plain constructor
// applications of Perennial/GooseLang/Lang.lean (`Val`, `Var`, `App`, `Lam`,
// `Let`, `If`, `Pair`, ...) rather than with notations, so that elaboration is
// fast and predictable.
//
// Every Expr can be printed in one of two modes:
//
//   - LeanTerm: a Lean term (the analogue of a Gallina term), e.g. a go.type,
//     a go_string, a val (`#x`), a list.
//   - LeanExpr: a GooseLang `expr`. Values are wrapped in `Val`, identifiers
//     become `Var "x"`, applications become `App`.
//
// Generated code lives in `namespace Perennial` and then a namespace derived
// from the full Go import path (see LeanNamespace), which is globally unique
// (Lean namespaces are global, unlike Rocq modules, so the Rocq scheme of
// naming the module after the Go package name would make e.g. crypto/rand and
// math/rand collide).

import (
	"fmt"
	"io"
	"math/big"
	"path"
	"path/filepath"
	"strings"
	"unicode/utf8"
)

// LeanFileOptions are set at the start of every generated Lean file.
const LeanFileOptions = `set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false
`

// Lean is set when generating Lean rather than Rocq. It is a global since a
// goose invocation produces only one kind of output.
var Lean bool

type LeanMode int

const (
	// A Lean term (Gallina-level object)
	LeanTerm LeanMode = iota
	// A GooseLang expr
	LeanExpr
)

// LeanKeywords are tokens that cannot be used as Lean identifiers; identifiers
// (or identifier components) equal to these are quoted with «».
var LeanKeywords = map[string]bool{}

func init() {
	// Identifier-like tokens of Lean core, iris-lean and Perennial (dumped from
	// the token table); regenerate if more notations are added.
	for _, w := range strings.Fields(`Prop RET Sort StateRefT Type WP abbrev add_decl_doc alias as
	assert_not_exists assert_not_imported assumeInstancesCommuteDummy at
	attribute aux_def axiom bif binder_predicate break builtin_cbv_simproc
	builtin_cbv_simproc_decl builtin_dsimproc builtin_dsimproc_decl
	builtin_grind_propagator builtin_initialize builtin_simproc
	builtin_simproc_decl by by_elab calc catch cbv_eval cbv_simproc
	cbv_simproc_decl class coinductive coinductive_fixpoint continue dbg_trace
	declare_bitwise_int_theorems declare_bitwise_uint_theorems
	declare_command_config_elab declare_command_config_elab_legacy
	declare_config_elab declare_config_elab_legacy declare_core_config_elab
	declare_eval_bin declare_eval_bin_bitwise declare_eval_bin_bool_pred
	declare_int_theorems declare_simp_like_tactic declare_sint_simprocs
	declare_syntax_cat declare_term_config_elab declare_uint_simprocs
	declare_uint_theorems decreasing_by def def_eval_config_item def_wanted
	delab_rule deprecated_module deprecated_syntax deriving do docs_to_verso
	dsimproc dsimproc_decl elab elab_rules elab_stx_quot else end eval_prec
	eval_prio example exists export extends finally for forall from fun
	generalizing gives grind_annotated grind_pattern grind_propagator have haveI
	hiding idbg if import in include include_str inductive inductive_fixpoint
	inferInstanceAs infix infixl infixr init_grind_norm init_quot initialize
	instance instance_wanted leading_parser let letI let_delayed let_expr
	let_fun let_tmp library_note local logNamedError logNamedErrorAt
	logNamedWarning logNamedWarningAt macro macro_rules match match_expr matches
	max_prec meta mod_cast mut mutual namespace nat_lit no_index nofun nomatch
	noncomputable nonrec norm_cast_add_elim notation omit opaque open partial
	partial_fixpoint postfix prefix private proof_wanted protected public
	recommended_spelling register_builtin_option register_error_explanation
	register_grind_attr register_label_attr register_linter_set register_option
	register_parser_alias register_simp_attr register_sym_dsimp
	register_sym_simp register_sym_simp_attr register_tactic_tag renaming repeat
	reprove return run_cmd run_elab run_meta scoped seal section semiOutParamIPM
	set_library_suggestions set_option show show_panel_widgets show_term
	show_term_elab simproc simproc_decl sorry structure suffices syntax
	tactic_alt tactic_extension tactic_name tactic_tag termination_by
	test_extern then theorem theorem_wanted throwError throwErrorAt
	throwIPMError throwIPMErrorAt throwNamedError throwNamedErrorAt
	trailing_parser try unif_hint universe unless unlock_limits unsafe unseal
	until using variable where while with with_annotate_term with_weak_namespace
	without_expected_type Π Σ λ`) {
		LeanKeywords[w] = true
	}
}

// LeanShadowNames are names that the Lean printer emits unqualified (GooseLang
// constructors and Golang/Defn definitions). A Go identifier with one of these
// names would shadow them inside the package's namespace, so (like the Rocq
// GallinaKeywords) such identifiers get a "'" suffix in the Lean output.
var LeanShadowNames = map[string]bool{}

func init() {
	for _, w := range strings.Fields(`Val Var Rec App If Pair Fst Snd Fork Lam
	Let Seq LamV RecV PairV LitV BAnon BNamed GoInstruction GoOp GoUnOp GoLoad
	GoStore GoAlloc GoZeroVal FuncResolve MethodResolve StructFieldGet
	StructFieldRef StructFieldSet GlobalVarAddr Index IndexRef Slice FullSlice
	TypeAssert TypeAssert2 Convert CompositeLiteral SelectStmt LiteralValue
	KeyedElement KeyField KeyExpression ElementExpression ElementLiteralValue
	SelectStmtClauses CommClause SendCase RecvCase UntypedNil into_val
	exception_seq do_execute do_return exception_do do_break do_continue do_for
	wrap_defer deferType none some W64 W32 W16 W8 w64 w32 w16 w8 Int Bool Unit
	List go_string val loc slice array chan interface func pkg_id under
	FuncUnfold MethodUnfold TypeRepr EqualsUnfold ZeroVal zero_val_def
	PkgInfo GoEquals GoLt GoLe GoGt GoGe GoPlus GoSub GoMul GoDiv GoRemainder
	GoAnd GoOr GoXor GoBitClear GoShiftl GoShiftr GoPos GoNeg GoNot GoComplement
	struct_field_ref`) {
		LeanShadowNames[w] = true
	}
}

// leanIdentRest reports whether r can appear in a Lean identifier without
// quoting (conservatively: ASCII only).
func leanIdentRest(r rune) bool {
	return r == '_' || r == '\'' || r == '!' || r == '?' ||
		('a' <= r && r <= 'z') || ('A' <= r && r <= 'Z') || ('0' <= r && r <= '9')
}

func leanIdentFirst(r rune) bool {
	return r == '_' || ('a' <= r && r <= 'z') || ('A' <= r && r <= 'Z')
}

// LeanQuoteComponent quotes a single identifier component with «» if needed.
func LeanQuoteComponent(s string) string {
	if s == "" || strings.HasPrefix(s, "«") {
		return s
	}
	ok := !LeanKeywords[s]
	for i, r := range s {
		if i == 0 && !leanIdentFirst(r) {
			ok = false
		}
		if !leanIdentRest(r) {
			ok = false
		}
	}
	if ok {
		return s
	}
	return "«" + s + "»"
}

// LeanQuote quotes every component of a dotted (qualified) name.
func LeanQuote(s string) string {
	parts := strings.Split(s, ".")
	for i, p := range parts {
		parts[i] = LeanQuoteComponent(p)
	}
	return strings.Join(parts, ".")
}

// leanConstructors maps the Rocq names of the go.type constructors (Rocq
// constructors are not namespaced by their inductive) to their Lean names in
// Perennial/Golang/Defn/PreLang.lean.
var leanConstructors = map[string]string{
	"go.Named":              "go.type.Named",
	"go.ArrayType":          "go.type.ArrayType",
	"go.StructType":         "go.type.StructType",
	"go.PointerType":        "go.type.PointerType",
	"go.FunctionType":       "go.type.FunctionType",
	"go.InterfaceType":      "go.type.InterfaceType",
	"go.SliceType":          "go.type.SliceType",
	"go.MapType":            "go.type.MapType",
	"go.ChannelType":        "go.type.ChannelType",
	"go.UntypedType":        "go.type.UntypedType",
	"go.sendrecv":           "go.chan_dir.sendrecv",
	"go.sendonly":           "go.chan_dir.sendonly",
	"go.recvonly":           "go.chan_dir.recvonly",
	"go.FieldDecl":          "go.field_decl.FieldDecl",
	"go.EmbeddedField":      "go.field_decl.EmbeddedField",
	"go.Signature":          "go.signature.Signature",
	"go.MethodElem":         "go.interface_elem.MethodElem",
	"go.TypeElem":           "go.interface_elem.TypeElem",
	"go.TypeTerm":           "go.type_term.TypeTerm",
	"go.TypeTermUnderlying": "go.type_term.TypeTermUnderlying",
}

// leanVerbatims maps verbatim Rocq snippets used by the translator to Lean.
var leanVerbatims = map[string]string{
	"None":           "none",
	"Some":           "some",
	"#slice.nil":     "#slice.nil",
	"#interface.nil": "#interface.t.nil",
}

// LeanIdent renders a (possibly qualified) Gallina identifier as a Lean
// identifier: applies the keyword renaming of the Rocq printer (plus
// LeanShadowNames) to the last component, and quotes components as needed.
func LeanIdent(s string) string {
	if c, ok := leanConstructors[s]; ok {
		return c
	}
	return LeanQuote(GallinaIdent(s).Coq(false))
}

// LeanNamespace is the Lean namespace for a Go package: the Rocq path of the
// package with "/" replaced by ".", e.g. "github.com/goose-lang/std" becomes
// "github_com.goose_lang.std" and "math/rand" becomes "math.rand".
func LeanNamespace(pkgPath string) string {
	return LeanQuote(strings.ReplaceAll(ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkgPath), "/", "."))
}

// LeanModule is the Lean module for a Go package under the given root (e.g.
// "Perennial.Code").
func LeanModule(root string, pkgPath string) string {
	return root + "." + LeanNamespace(pkgPath)
}

// LeanPkgId is the name of the go_string holding the package path (the Rocq
// `pkg_id.<name>`).
func LeanPkgId(pkgPath string) string {
	return "pkg_id." + LeanNamespace(pkgPath)
}

// ImportToLeanPath converts a Go import path to the relative Lean file path
func ImportToLeanPath(pkgPath string) string {
	coqPath := ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkgPath)
	p := path.Dir(coqPath)
	filename := path.Base(coqPath) + ".lean"
	return filepath.Join(p, filename)
}

// LeanStringLit renders a Go string (arbitrary bytes) as a Lean go_string.
func LeanStringLit(s string) string {
	if !utf8.ValidString(s) {
		var bs []string
		for i := 0; i < len(s); i++ {
			bs = append(bs, fmt.Sprintf("W8 %d", s[i]))
		}
		return "([" + strings.Join(bs, ", ") + "] : go_string)"
	}
	return "go!" + LeanRawString(s)
}

// LeanRawString renders a Lean String literal (s must be valid UTF-8).
func LeanRawString(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch r {
		case '\\':
			b.WriteString(`\\`)
		case '"':
			b.WriteString(`\"`)
		case '\n':
			b.WriteString(`\n`)
		case '\t':
			b.WriteString(`\t`)
		case '\r':
			b.WriteString(`\r`)
		default:
			if r < 0x20 || r == 0x7f {
				fmt.Fprintf(&b, `\x%02x`, r)
			} else if r >= 0x80 && (r < 0xa0 || r == 0x2028 || r == 0x2029 || r == 0xfeff) {
				fmt.Fprintf(&b, `\u{%x}`, r)
			} else {
				b.WriteRune(r)
			}
		}
	}
	b.WriteByte('"')
	return b.String()
}

// isAtomic reports whether s can be used as a function argument without
// parentheses.
func isAtomic(s string) bool {
	if s == "" {
		return true
	}
	if !strings.ContainsAny(s, " \n\t") {
		return true
	}
	// #(...) and go!"..." are atomic if their argument is
	if strings.HasPrefix(s, "#(") {
		return isAtomic(s[1:])
	}
	if strings.HasPrefix(s, "go!\"") && strings.Count(s, "\"") == 2 && strings.HasSuffix(s, "\"") {
		return true
	}
	// a single parenthesized/bracketed group
	open := s[0]
	var close byte
	switch open {
	case '(':
		close = ')'
	case '[':
		close = ']'
	default:
		return false
	}
	if s[len(s)-1] != close {
		return false
	}
	depth := 0
	inStr := false
	for i := 0; i < len(s); i++ {
		c := s[i]
		if inStr {
			if c == '\\' {
				i++
			} else if c == '"' {
				inStr = false
			}
			continue
		}
		switch c {
		case '"':
			inStr = true
		case '(', '[':
			depth++
		case ')', ']':
			depth--
			if depth == 0 && i != len(s)-1 {
				return false
			}
		}
	}
	return true
}

// Note on layout: everything the Lean printer emits inside a definition body is
// parenthesized, so Lean's column-sensitive application parsing does not apply
// and continuation lines need no indentation. We avoid cumulative indentation
// since GooseLang continuations nest very deeply.

func lparen(s string) string {
	if isAtomic(s) {
		return s
	}
	return "(" + s + ")"
}

// lapp renders a Lean application `f a1 ... an`, parenthesized.
func lapp(f string, args ...string) string {
	comps := []string{lparen(f)}
	for _, a := range args {
		comps = append(comps, lparen(a))
	}
	return "(" + strings.Join(comps, " ") + ")"
}

// eApp renders the GooseLang application of f to args (left-nested App).
func eApp(f string, args ...string) string {
	e := f
	for _, a := range args {
		e = lapp("App", e, a)
	}
	return e
}

func eVal(v string) string {
	return lapp("Val", v)
}

func eInstr(name string, termArgs ...string) string {
	return eVal(lapp("GoInstruction", lapp(name, termArgs...)))
}

func eInstr0(name string) string {
	return eVal(lapp("GoInstruction", name))
}

// eBlock renders `head` applied to args where the last argument goes on a new
// line (used for continuations, to keep nesting readable).
func eLetLike(head string, args []string, body string) string {
	comps := []string{head}
	for _, a := range args {
		comps = append(comps, lparen(a))
	}
	return "(" + strings.Join(comps, " ") + "\n" + lparen(body) + ")"
}

func leanBinder(name string) string {
	if name == "_" || name == "" {
		return "BAnon"
	}
	return LeanRawString(name)
}

func eLet(name string, e1, e2 string) string {
	return eLetLike("Let", []string{leanBinder(name), e1}, e2)
}

func eSeq(e1, e2 string) string {
	return eLetLike("Seq", []string{e1}, e2)
}

func eLam(names []string, body string) string {
	if len(names) == 0 {
		names = []string{"_"}
	}
	e := body
	for i := len(names) - 1; i >= 0; i-- {
		e = eLetLike("Lam", []string{leanBinder(names[i])}, e)
	}
	return e
}

// vLam is the value version of eLam (λ: in val scope)
func vLam(names []string, body string) string {
	if len(names) == 0 {
		names = []string{"_"}
	}
	e := body
	for i := len(names) - 1; i >= 1; i-- {
		e = eLetLike("Lam", []string{leanBinder(names[i])}, e)
	}
	return eLetLike("LamV", []string{leanBinder(names[0])}, e)
}

// exception sequencing `e1 ;;; e2`
func eExnSeq(e1, e2 string) string {
	return eLetLike("App", []string{lapp("App", eVal("exception_seq"), eLam(nil, e2))}, e1)
}

func ePair(es ...string) string {
	if len(es) == 0 {
		return eVal("#()")
	}
	e := es[0]
	for _, x := range es[1:] {
		e = lapp("Pair", e, x)
	}
	return e
}

func leanTermList(es []Expr) string {
	var comps []string
	for _, e := range es {
		comps = append(comps, e.Lean(LeanTerm))
	}
	return "[" + strings.Join(comps, ", ") + "]"
}

func leanComment(c string) string {
	if c == "" {
		return ""
	}
	c = strings.ReplaceAll(c, "-/", "- /")
	c = strings.ReplaceAll(c, "/-", "/ -")
	return "/-- " + indent(4, c) + " -/\n"
}

// LeanExprOf prints e as a GooseLang expr.
func LeanExprOf(e Expr) string { return e.Lean(LeanExpr) }

// LeanTermOf prints e as a Lean term.
func LeanTermOf(e Expr) string { return e.Lean(LeanTerm) }

// ---- Expr implementations ----

func (e GallinaIdent) Lean(m LeanMode) string {
	s := LeanIdent(string(e))
	if m == LeanExpr {
		return eVal(s)
	}
	return s
}

func (e VerbatimExpr) Lean(m LeanMode) string {
	s := string(e)
	if c, ok := leanConstructors[s]; ok {
		s = c
	} else if c, ok := leanVerbatims[s]; ok {
		s = c
	}
	if m == LeanExpr {
		return eVal(s)
	}
	return s
}

func (e PackageIdent) Lean(m LeanMode) string {
	s := LeanNamespace(e.Package) + "." + LeanIdent(e.Ident)
	if m == LeanExpr {
		return eVal(s)
	}
	return s
}

func (e ParenExpr) Lean(m LeanMode) string {
	return lparen(e.Inner.Lean(m))
}

func (e IdentExpr) Lean(m LeanMode) string {
	if m == LeanExpr {
		return lapp("Var", LeanRawString(string(e)))
	}
	return LeanRawString(string(e))
}

func (s GallinaString) Lean(m LeanMode) string {
	return LeanStringLit(string(s))
}

type leanHeadKind int

const (
	// go_instruction constructor applied to nTerm Gallina args, then applied
	// (GooseLang App) to the remaining args
	headInstr leanHeadKind = iota
	// Gallina function returning a val, applied to nTerm Gallina args, then
	// App to the remaining args
	headValFn
	// a val, App to all args
	headVal
	// a Lean term constructor; argModes gives the mode of each argument
	headTermCtor
	// a GooseLang expr constructor; argModes gives the mode of each argument
	headExprCtor
	headWithDefer
)

type leanHead struct {
	kind     leanHeadKind
	name     string
	nTerm    int
	argModes []LeanMode
}

var leanHeads = map[string]leanHead{
	"FuncResolve":      {kind: headInstr, name: "FuncResolve", nTerm: 2},
	"MethodResolve":    {kind: headInstr, name: "MethodResolve", nTerm: 2},
	"GoAlloc":          {kind: headInstr, name: "GoAlloc", nTerm: 1},
	"GoZeroVal":        {kind: headInstr, name: "GoZeroVal", nTerm: 1},
	"GlobalVarAddr":    {kind: headInstr, name: "GlobalVarAddr", nTerm: 1},
	"StructFieldGet":   {kind: headInstr, name: "StructFieldGet", nTerm: 2},
	"StructFieldSet":   {kind: headInstr, name: "StructFieldSet", nTerm: 2},
	"StructFieldRef":   {kind: headInstr, name: "StructFieldRef", nTerm: 2},
	"Index":            {kind: headInstr, name: "Index", nTerm: 1},
	"IndexRef":         {kind: headInstr, name: "IndexRef", nTerm: 1},
	"Slice":            {kind: headInstr, name: "Slice", nTerm: 1},
	"FullSlice":        {kind: headInstr, name: "FullSlice", nTerm: 1},
	"TypeAssert":       {kind: headInstr, name: "TypeAssert", nTerm: 1},
	"TypeAssert2":      {kind: headInstr, name: "TypeAssert2", nTerm: 1},
	"Convert":          {kind: headInstr, name: "Convert", nTerm: 2},
	"CompositeLiteral": {kind: headInstr, name: "CompositeLiteral", nTerm: 1},
	"SelectStmt":       {kind: headInstr, name: "SelectStmt", nTerm: 0},
	"chan.receive":     {kind: headValFn, name: "chan.receive", nTerm: 1},
	"chan.send":        {kind: headValFn, name: "chan.send", nTerm: 1},
	"map.lookup1":      {kind: headValFn, name: "map.lookup1", nTerm: 2},
	"map.lookup2":      {kind: headValFn, name: "map.lookup2", nTerm: 2},
	"map.insert":       {kind: headValFn, name: "map.insert", nTerm: 1},
	"package.init":     {kind: headValFn, name: "package.init", nTerm: 1},
	"go.GlobalAlloc":   {kind: headValFn, name: "go.GlobalAlloc", nTerm: 2},
	"exception_do":     {kind: headVal, name: "exception_do"},
	"with_defer:":      {kind: headWithDefer},
	"Fst":              {kind: headExprCtor, name: "Fst", argModes: []LeanMode{LeanExpr}},
	"Snd":              {kind: headExprCtor, name: "Snd", argModes: []LeanMode{LeanExpr}},
	"LiteralValue":     {kind: headExprCtor, name: "LiteralValue", argModes: []LeanMode{LeanTerm}},
	"KeyedElement":     {kind: headTermCtor, name: "KeyedElement", argModes: []LeanMode{LeanTerm, LeanTerm}},
	"Some":             {kind: headTermCtor, name: "some", argModes: []LeanMode{LeanTerm}},
	"ElementExpression": {kind: headTermCtor, name: "ElementExpression",
		argModes: []LeanMode{LeanTerm, LeanExpr}},
	"KeyField": {kind: headTermCtor, name: "KeyField", argModes: []LeanMode{LeanTerm}},
	"KeyExpression": {kind: headTermCtor, name: "KeyExpression",
		argModes: []LeanMode{LeanTerm, LeanExpr}},
	"ElementLiteralValue": {kind: headTermCtor, name: "ElementLiteralValue",
		argModes: []LeanMode{LeanTerm}},
}

func (s CallExpr) Lean(m LeanMode) string {
	if v, ok := s.MethodName.(VerbatimExpr); ok {
		if h, ok := leanHeads[string(v)]; ok {
			return h.render(s.Args, m)
		}
	}
	if m == LeanExpr {
		var args []string
		for _, a := range s.Args {
			args = append(args, a.Lean(LeanExpr))
		}
		return eApp(s.MethodName.Lean(LeanExpr), args...)
	}
	var args []string
	for _, a := range s.Args {
		args = append(args, a.Lean(LeanTerm))
	}
	return lapp(s.MethodName.Lean(LeanTerm), args...)
}

func (h leanHead) render(args []Expr, m LeanMode) string {
	switch h.kind {
	case headInstr, headValFn:
		if len(args) < h.nTerm {
			panic(fmt.Sprintf("Lean printer: %s expects %d term arguments", h.name, h.nTerm))
		}
		var termArgs []string
		for _, a := range args[:h.nTerm] {
			termArgs = append(termArgs, a.Lean(LeanTerm))
		}
		var head string
		if h.kind == headInstr {
			if h.nTerm == 0 {
				head = lapp("GoInstruction", h.name)
			} else {
				head = lapp("GoInstruction", lapp(h.name, termArgs...))
			}
		} else {
			head = lapp(h.name, termArgs...)
		}
		rest := args[h.nTerm:]
		if m == LeanTerm && len(rest) == 0 {
			return head
		}
		var restS []string
		for _, a := range rest {
			restS = append(restS, a.Lean(LeanExpr))
		}
		return eApp(eVal(head), restS...)
	case headVal:
		var restS []string
		for _, a := range args {
			restS = append(restS, a.Lean(LeanExpr))
		}
		if len(restS) == 1 {
			return eLetLike("App", []string{eVal(h.name)}, restS[0])
		}
		return eApp(eVal(h.name), restS...)
	case headWithDefer:
		if len(args) != 1 {
			panic("with_defer: expects one argument")
		}
		return eLetLike("App", []string{eVal("wrap_defer")},
			eLam([]string{"$defer"}, args[0].Lean(LeanExpr)))
	case headTermCtor, headExprCtor:
		var as []string
		for i, a := range args {
			mode := LeanTerm
			if i < len(h.argModes) {
				mode = h.argModes[i]
			}
			as = append(as, a.Lean(mode))
		}
		return lapp(h.name, as...)
	}
	panic("unreachable")
}

func (e ContinueExpr) Lean(m LeanMode) string {
	return eApp(eVal("do_continue"), eVal("#()"))
}

func (e BreakExpr) Lean(m LeanMode) string {
	return eApp(eVal("do_break"), eVal("#()"))
}

func (e ReturnExpr) Lean(m LeanMode) string {
	return eLetLike("App", []string{eVal("do_return")}, e.Value.Lean(LeanExpr))
}

func (b DoExpr) Lean(m LeanMode) string {
	return eLetLike("App", []string{eVal("do_execute")}, b.Expr.Lean(LeanExpr))
}

func (b SeqExpr) Lean(m LeanMode) string {
	if b.Cont == nil {
		return b.Expr.Lean(LeanExpr)
	}
	return eExnSeq(b.Expr.Lean(LeanExpr), b.Cont.Lean(LeanExpr))
}

func (b LetExpr) Lean(m LeanMode) string {
	if b.Cont == nil {
		if !b.isAnonymous() {
			panic("let expr with nil cont but non-anonymous binding")
		}
		return b.ValExpr.Lean(LeanExpr)
	}
	v := b.ValExpr.Lean(LeanExpr)
	cont := b.Cont.Lean(LeanExpr)
	if b.isAnonymous() {
		return eSeq(v, cont)
	}
	if len(b.Names) == 1 {
		return eLet(b.Names[0], v, cont)
	}
	// tuple destructuring, following the Rocq notation
	// let: ((a1, a2), a3) := e1 in e2
	n := len(b.Names)
	p := lapp("Var", `"__p"`)
	proj := func(i int) string {
		// a_i (0-indexed) is Fst^(n-1-i) p, followed by Snd if i > 0
		e := p
		fsts := n - 1 - i
		for range fsts {
			e = lapp("Fst", e)
		}
		if i > 0 {
			e = lapp("Snd", e)
		}
		return e
	}
	body := cont
	for i := n - 1; i >= 0; i-- {
		body = eLet(b.Names[i], proj(i), body)
	}
	return eLet("__p", v, body)
}

func (b GallinaLetExpr) Lean(m LeanMode) string {
	return "(let " + LeanIdent(b.Name) + " := " + b.ValExpr.Lean(LeanTerm) + ";\n" +
		b.Cont.Lean(LeanExpr) + ")"
}

func (sl StructLiteral) Lean(m LeanMode) string {
	vs := lapp("Var", `"$$vs"`)
	var e string = vs
	for i := len(sl.Elts) - 1; i >= 0; i-- {
		e = eLet("$$vs", eApp(eVal("go.ElementListApp"), vs, sl.Elts[i].Lean(LeanExpr)), e)
	}
	e = eLet("$$vs", eApp(eVal("go.StructElementListNil"), eVal("#()")), e)
	return eApp(eInstr("CompositeLiteral", sl.Type.Lean(LeanTerm)), e)
}

func (b GooseBoolLiteral) Lean(m LeanMode) string {
	s := "#false"
	if b {
		s = "#true"
	}
	if m == LeanExpr {
		return eVal(s)
	}
	return s
}

func (b BoolLiteral) Lean(m LeanMode) string {
	if b {
		return "true"
	}
	return "false"
}

func (tt UnitLiteral) Lean(m LeanMode) string {
	if m == LeanExpr {
		return eVal("#()")
	}
	return "#()"
}

func (z ZLiteral) Lean(m LeanMode) string {
	if z.Value.Sign() < 0 {
		return "(" + z.Value.String() + ")"
	}
	return z.Value.String()
}

func (s StringLiteral) Lean(m LeanMode) string {
	return LeanStringLit(s.Value)
}

func leanIntVal(cons string, v Expr, m LeanMode) string {
	s := "#(" + cons + " " + lparen(v.Lean(LeanTerm)) + ")"
	if m == LeanExpr {
		return eVal(s)
	}
	return s
}

func (l Int64Val) Lean(m LeanMode) string { return leanIntVal("W64", l.Value, m) }
func (l Int32Val) Lean(m LeanMode) string { return leanIntVal("W32", l.Value, m) }
func (l Int16Val) Lean(m LeanMode) string { return leanIntVal("W16", l.Value, m) }
func (l Int8Val) Lean(m LeanMode) string  { return leanIntVal("W8", l.Value, m) }

func (l ToVal) Lean(m LeanMode) string {
	var s string
	if z, ok := l.Value.(ZLiteral); ok {
		s = "#(" + z.Value.String() + " : Int)"
	} else {
		inner := l.Value.Lean(LeanTerm)
		if strings.HasPrefix(inner, "(") && isAtomic(inner) {
			s = "#" + inner
		} else {
			s = "#(" + inner + ")"
		}
	}
	if m == LeanExpr {
		return eVal(s)
	}
	return s
}

var leanBinOps = map[OpId]string{
	OpPlus:        "GoPlus",
	OpMinus:       "GoSub",
	OpEquals:      "GoEquals",
	OpNotEquals:   "GoEquals",
	OpMul:         "GoMul",
	OpQuot:        "GoDiv",
	OpRem:         "GoRemainder",
	OpLessThan:    "GoLt",
	OpGreaterThan: "GoGt",
	OpLessEq:      "GoLe",
	OpGreaterEq:   "GoGe",
	OpShl:         "GoShiftl",
	OpShr:         "GoShiftr",
	OpAnd:         "GoAnd",
	OpAndNot:      "GoBitClear",
	OpOr:          "GoOr",
	OpXor:         "GoXor",
}

func leanNot(e string) string {
	return eApp(eInstr("GoUnOp", "GoNot", "go.bool"), e)
}

func (be BinaryExpr) Lean(m LeanMode) string {
	x := be.X.Lean(LeanExpr)
	y := be.Y.Lean(LeanExpr)
	switch be.Op.OpId {
	case OpLAnd:
		return lapp("If", x, y, eVal("#false"))
	case OpLOr:
		return lapp("If", x, eVal("#true"), y)
	}
	op, ok := leanBinOps[be.Op.OpId]
	if !ok {
		panic(fmt.Sprint("unsupported op: ", be.Op))
	}
	e := eApp(eInstr("GoOp", op, be.Op.Type.Lean(LeanTerm)), ePair(x, y))
	if be.Op.OpId == OpNotEquals {
		e = leanNot(e)
	}
	return e
}

var leanUnOps = map[OpId]string{
	OpMinus: "GoNeg",
	OpPlus:  "GoPos",
	OpNot:   "GoNot",
	OpXor:   "GoComplement",
}

func (be UnaryExpr) Lean(m LeanMode) string {
	op, ok := leanUnOps[be.Op.OpId]
	if !ok {
		panic(fmt.Sprint("unsupported unary op: ", be.Op))
	}
	return eApp(eInstr("GoUnOp", op, be.Op.Type.Lean(LeanTerm)), be.X.Lean(LeanExpr))
}

func (e GallinaNotExpr) Lean(m LeanMode) string {
	return "(!" + lparen(e.X.Lean(LeanTerm)) + ")"
}

func (e NotExpr) Lean(m LeanMode) string {
	return leanNot(e.X.Lean(LeanExpr))
}

func (te TupleExpr) Lean(m LeanMode) string {
	var es []string
	for _, t := range te {
		es = append(es, t.Lean(LeanExpr))
	}
	if m == LeanTerm {
		return "(" + strings.Join(es, ", ") + ")"
	}
	return ePair(es...)
}

func (le ListExpr) Lean(m LeanMode) string {
	return leanTermList(le)
}

func (e DerefExpr) Lean(m LeanMode) string {
	return eApp(eInstr("GoLoad", e.Ty.Lean(LeanTerm)), e.X.Lean(LeanExpr))
}

func (e StoreStmt) Lean(m LeanMode) string {
	return eApp(eInstr("GoStore", e.Ty.Lean(LeanTerm)),
		ePair(e.Dst.Lean(LeanExpr), e.X.Lean(LeanExpr)))
}

func (ife IfExpr) Lean(m LeanMode) string {
	return "(If " + lparen(ife.Cond.Lean(LeanExpr)) +
		"\n" + lparen(ife.Then.Lean(LeanExpr)) +
		"\n" + lparen(ife.Else.Lean(LeanExpr)) + ")"
}

func (e ForLoopExpr) Lean(m LeanMode) string {
	return eLetLike("App", []string{
		lapp("App", lapp("App", eVal("do_for"), eLam(nil, e.Cond.Lean(LeanExpr))),
			eLam(nil, e.Body.Lean(LeanExpr)))},
		eLam(nil, e.Post.Lean(LeanExpr)))
}

func (e ForRangeSliceExpr) Lean(m LeanMode) string {
	return eLetLike("App", []string{
		lapp("App", eVal(lapp("slice.for_range", e.Ty.Lean(LeanTerm))), e.Slice.Lean(LeanExpr))},
		eLam([]string{"$key", "$value"}, e.Body.Lean(LeanExpr)))
}

func (e ForRangeChanExpr) Lean(m LeanMode) string {
	return eLetLike("App", []string{
		lapp("App", eVal(lapp("chan.for_range", e.Elem.Lean(LeanTerm))), e.Chan.Lean(LeanExpr))},
		eLam([]string{"$key"}, e.Body.Lean(LeanExpr)))
}

func (e ForRangeMapExpr) Lean(m LeanMode) string {
	return eLetLike("App", []string{
		lapp("App", eVal(lapp("map.for_range", e.KeyType.Lean(LeanTerm), e.ElemType.Lean(LeanTerm))),
			e.Map.Lean(LeanExpr))},
		eLam([]string{"$key", "$value"}, e.Body.Lean(LeanExpr)))
}

func (e SpawnExpr) Lean(m LeanMode) string {
	return eLetLike("Fork", nil, e.Body.Lean(LeanExpr))
}

func (b Binder) Lean(m LeanMode) string {
	return leanBinder(b.Name)
}

func binderNames(xs []Binder) []string {
	var names []string
	for _, a := range xs {
		names = append(names, a.Name)
	}
	return names
}

func (e FuncLit) Lean(m LeanMode) string {
	if m == LeanTerm {
		return e.LeanVal()
	}
	return eLam(binderNames(e.Args), e.Body.Lean(LeanExpr))
}

// LeanVal prints the function literal as a val (λ: in val scope).
func (e FuncLit) LeanVal() string {
	return vLam(binderNames(e.Args), e.Body.Lean(LeanExpr))
}

func (e ValueScoped) Lean(m LeanMode) string {
	if f, ok := e.Value.(FuncLit); ok {
		return f.LeanVal()
	}
	return e.Value.Lean(LeanTerm)
}

func (s SendCase) Lean(m LeanMode) string {
	return lapp("SendCase", s.ElemType.Lean(LeanTerm), s.Chan.Lean(LeanExpr), s.Value.Lean(LeanExpr))
}

func (s RecvCase) Lean(m LeanMode) string {
	return lapp("RecvCase", s.ElemType.Lean(LeanTerm), s.Chan.Lean(LeanExpr))
}

func (c CommClause) Lean(m LeanMode) string {
	return lapp("CommClause", c.Comm.Lean(LeanTerm), c.Body.Lean(LeanExpr))
}

func (s SelectStmtClauses) Lean(m LeanMode) string {
	def := "none"
	if s.Default != nil {
		def = lapp("some", s.Default.Lean(LeanExpr))
	}
	var clauses []string
	for _, c := range s.Clauses {
		clauses = append(clauses, c.Lean(LeanTerm))
	}
	return lapp("SelectStmtClauses", def, "["+strings.Join(clauses, ",\n")+"]")
}

func (d StructType) LeanFields() string {
	var comps []string
	for _, fd := range d.Fields {
		fdcons := "go.field_decl.FieldDecl"
		if fd.Embedded {
			fdcons = "go.field_decl.EmbeddedField"
		}
		comps = append(comps, lapp(fdcons, LeanStringLit(fd.Name), fd.Type.Lean(LeanTerm)))
	}
	return "[" + strings.Join(comps, ",\n") + "]"
}

func (d StructType) Lean(m LeanMode) string {
	return lapp("go.type.StructType", d.LeanFields())
}

// ---- Decls ----

// GooseLang function bodies and constants are emitted `noncomputable`: nothing runs GooseLang code, and
// compiling these definitions (which `noncomputable section` alone does not
// prevent) was the bulk of elaboration time for large packages. So are the
// go_string constants naming functions and globals. go.type definitions stay
// computable since Golang/Defn uses some of them in computable definitions.
const leanDeclParams = "[ffi_syntax] [GoGlobalContext]"

func leanTypeParams(names []GallinaIdent) string {
	if len(names) == 0 {
		return ""
	}
	var ss []string
	for _, n := range names {
		ss = append(ss, LeanIdent(string(n)))
	}
	return " (" + strings.Join(ss, " ") + " : go.type)"
}

func (d FuncDecl) LeanDecl() string {
	var names []string
	if d.RecvArg != nil {
		names = append(names, d.RecvArg.Name)
	}
	for _, a := range d.Args {
		names = append(names, a.Name)
	}
	if len(d.Args) == 0 {
		names = append(names, "_")
	}
	return leanComment(d.Comment) +
		fmt.Sprintf("noncomputable def %s %s%s : val :=\n  %s", LeanIdent(d.Name), leanDeclParams,
			leanTypeParams(d.TypeArgs), indent(2, vLam(names, d.Body.Lean(LeanExpr))))
}

func (d ConstDecl) LeanDecl() string {
	attr := ""
	if v, ok := d.Type.(VerbatimExpr); ok && v == "val" {
		// package constants are transparent in Rocq; make them visible to
		// the wp automation
		attr = "@[reducible] "
	}
	nc := "noncomputable "
	return leanComment(d.Comment) + attr +
		fmt.Sprintf("%sdef %s %s : %s :=\n  %s", nc, LeanIdent(d.Name), leanDeclParams,
			d.Type.Lean(LeanTerm), indent(2, d.Val.Lean(LeanTerm)))
}

func (e VerbatimDecl) LeanDecl() string {
	if e.LeanContent == nil {
		panic("Lean printer: VerbatimDecl without Lean content: " + e.Content)
	}
	return *e.LeanContent
}

func (d AxiomDecl) LeanDecl() string {
	return fmt.Sprintf("axiom %s %s : %s", LeanIdent(d.DeclName), leanDeclParams, d.Type.Lean(LeanTerm))
}

func (decl ImportDecl) LeanDecl() string {
	return "import " + LeanModule("Perennial.Code", decl.Path)
}

func (d TypeDecl) LeanDecl() string {
	typeParams := ""
	for _, t := range d.TypeParams {
		typeParams += fmt.Sprintf(" (%s : go.type)", LeanIdent(t))
	}
	attr := ""
	if strings.HasSuffix(d.Name, "ⁱᵐᵖˡ") {
		// unfolded by the struct tactics of the theory
		attr = "@[reducible] "
	}
	return fmt.Sprintf("%sdef %s %s%s : go.type :=\n  %s", attr, LeanIdent(d.Name), leanDeclParams, typeParams,
		indent(2, d.Body.Lean(LeanTerm)))
}

// LeanVerbatim creates a VerbatimDecl with both Rocq and Lean content.
func LeanVerbatim(coq string, lean string) VerbatimDecl {
	return VerbatimDecl{Content: coq, LeanContent: &lean}
}

// WriteLean outputs the Lean source for a File.
//
// noinspection GoUnhandledErrorResult
func (f File) WriteLean(w io.Writer) {
	fmt.Fprintf(w, "-- autogenerated from %s\n", f.PkgPath)
	// imports must come first
	for _, d := range f.PreHeaderDecls {
		if _, ok := d.(ImportDecl); ok {
			fmt.Fprintln(w, d.LeanDecl())
		}
	}
	fmt.Fprintln(w, f.LeanHeader)
	for _, d := range f.PreHeaderDecls {
		if _, ok := d.(ImportDecl); !ok {
			fmt.Fprintln(w, d.LeanDecl())
		}
	}
	fmt.Fprintln(w)
	for i, d := range f.Decls {
		fmt.Fprintln(w, d.LeanDecl())
		if i != len(f.Decls)-1 {
			fmt.Fprintln(w)
		}
	}
	fmt.Fprint(w, f.LeanFooter)
}

// LeanRocqImport translates a Rocq `From A Require Import/Export x y.` or
// `Require Import/Export A.x.` line (as found in bootstrap preludes) to Lean
// imports, mapping `New.golang.defn.slice` to `Perennial.Golang.Defn.Slice`.
func LeanRocqImport(line string) string {
	line = strings.TrimSpace(strings.TrimSuffix(strings.TrimSpace(line), "."))
	fields := strings.Fields(line)
	var prefix string
	var mods []string
	if len(fields) >= 4 && fields[0] == "From" && fields[2] == "Require" {
		prefix = fields[1]
		mods = fields[4:]
	} else if len(fields) >= 3 && fields[0] == "Require" {
		mods = fields[2:]
	} else {
		return "-- (untranslated Rocq prelude) " + line
	}
	var out []string
	for _, m := range mods {
		full := m
		if prefix != "" {
			full = prefix + "." + m
		}
		out = append(out, "import "+RocqModuleToLean(full))
	}
	return strings.Join(out, "\n")
}

// RocqModuleToLean maps a Rocq module path under New (new/) to the Lean module
// path, following PORTING.md (directories and files in UpperCamelCase).
func RocqModuleToLean(m string) string {
	parts := strings.Split(m, ".")
	if len(parts) > 0 && parts[0] == "New" {
		parts = parts[1:]
	}
	for i, p := range parts {
		parts[i] = upperCamel(p)
	}
	return "Perennial." + strings.Join(parts, ".")
}

func upperCamel(s string) string {
	var b strings.Builder
	up := true
	for _, r := range s {
		if r == '_' {
			up = true
			continue
		}
		if up {
			b.WriteString(strings.ToUpper(string(r)))
			up = false
		} else {
			b.WriteRune(r)
		}
	}
	return b.String()
}

var _ = big.NewInt
