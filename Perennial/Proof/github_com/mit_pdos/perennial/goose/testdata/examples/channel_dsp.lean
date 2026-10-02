/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_dsp.v`:
examples of dependent separation protocols (DSP) over Go channels, and an MPMC muxer.

Lean notes / deviations:
* Countability. The channel ghost state needs `Pos.Countable V` for the element type.
  Rocq gets `Countable val`/`Countable func.t` from `ffi_syntax`, which requires
  `Countable ffi_val`; the Lean `ffi_syntax` has no such field and the port has no
  `Countable val` instance. The lemmas whose channels carry `interface.t` or `streamold.t`
  (which contains a `func.t`) therefore take `[Pos.Countable val]` as an explicit
  assumption, from which the instances for `func.t`, `interface.t` and `streamold.t` are
  derived.
* The Rocq `wp_send`/`wp_recv` tactics are not ported (`DspProofmode.lean` has the Texan
  triples `tac_wp_send`/`tac_wp_recv`). Below, `wp_dsp_send0/1/2`, `wp_dsp_recv0/1/2` are
  wrappers for messages with 0, 1 or 2 binders, whose messages are found by protocol
  normalization (`ProtoNormalize`).
* `solve_proto_contractive` is not ported; contractiveness is proved by hand, and
  `ProtoUnfold` instances are replaced by explicit unfolding equations (`*_unfold`), applied
  to an endpoint with `dsp_endpoint_eq`. The `*_aux` protocol bodies are `abbrev`s so that
  `ProtoNormalize` sees through them.
* `wp_Serve`: the Go closure shares the local struct `s`; its fields are read from
  persistent field points-tos (`iStructNamed` of a persistent copy), since the memory tactics
  do not load a struct field from a persistent whole-struct points-to.
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel_examples_init
import Perennial.Golang.Theory.Chan.Idioms.Mpmc
import Perennial.Golang.Theory.Chan.Idioms.Dsp.Dsp
import Perennial.Golang.Theory.Chan.Idioms.Dsp.DspProofmode

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

/-! ## Countability -/

section countable
variable [ext : ffi_syntax] [val_countable : Pos.Countable val]

instance func_countable : Pos.Countable func.t :=
  .ofInjective (fun f => Pos.Countable.encode (val.RecV f.f f.x f.e))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

instance interface_countable : Pos.Countable interface.t :=
  .ofInjective (fun
      | .ok i => Pos.Countable.encode (val.InterfaceV (some (i.ty, i.v)))
      | .nil => Pos.Countable.encode (val.InterfaceV none))
    (by
      rintro (⟨⟨a, b⟩⟩ | _) (⟨⟨c, d⟩⟩ | _) h <;> have h := Pos.encode_inj h <;> simp_all)

instance streamold_countable : Pos.Countable streamold.t :=
  .ofInjective (fun x => Pos.Countable.encode (x.req', x.res', x.f'))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

end countable

/-! ## DSP send/receive wrappers -/

section dsp_wrappers
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

theorem wp_dsp_recv0 (γ : dsp_names) (lr_chan rl_chan : loc) (p0 : iProto GF V) (v : V)
    (P : IProp GF) (p : iProto GF V) [ProtoNormalize false p0 [] (<?> iMsg_base v P p)] :
    {{ (lr_chan, rl_chan) ↣{γ} p0 }}
      (App (Val (chan.receive t)) (Val #rl_chan))
    {{ RET (PairV #v #true); ((lr_chan, rl_chan) ↣{γ} p) ∗ P }} := by
  have h := tac_wp_recv (t := t) (TT := Tele.nil.{0}) γ lr_chan rl_chan p0 _ (ULift.up v)
    (ULift.up P) (ULift.up p) (hm := ⟨rfl⟩)
  simp only [Tele.app] at h
  iintro %Φ Hc HΦ
  wp_apply h $$ Hc as %x H
  iapply HΦ $$ H

theorem wp_dsp_recv1 {A : Type} (γ : dsp_names) (lr_chan rl_chan : loc) (p0 : iProto GF V)
    (v : A → V) (P : A → IProp GF) (p : A → iProto GF V)
    [ProtoNormalize false p0 [] (<?> iMsg_exist fun a => iMsg_base (v a) (P a) (p a))] :
    {{ (lr_chan, rl_chan) ↣{γ} p0 }}
      (App (Val (chan.receive t)) (Val #rl_chan))
    {{ (a : A), RET (PairV #(v a) #true); ((lr_chan, rl_chan) ↣{γ} p a) ∗ P a }} := by
  have h := tac_wp_recv (t := t) (TT := Tele.cons fun (_ : A) => Tele.nil) γ lr_chan rl_chan p0 _
    (fun a => ULift.up (v a)) (fun a => ULift.up (P a)) (fun a => ULift.up (p a)) (hm := ⟨rfl⟩)
  iintro %Φ Hc HΦ
  wp_apply h $$ Hc as %x H
  obtain ⟨a, ⟨⟩⟩ := x
  simp only [Tele.app]
  iapply HΦ $$ %a H

theorem wp_dsp_recv2 {A B : Type} (γ : dsp_names) (lr_chan rl_chan : loc) (p0 : iProto GF V)
    (v : A → B → V) (P : A → B → IProp GF) (p : A → B → iProto GF V)
    [ProtoNormalize false p0 []
      (<?> iMsg_exist fun a => iMsg_exist fun b => iMsg_base (v a b) (P a b) (p a b))] :
    {{ (lr_chan, rl_chan) ↣{γ} p0 }}
      (App (Val (chan.receive t)) (Val #rl_chan))
    {{ (a : A) (b : B), RET (PairV #(v a b) #true); ((lr_chan, rl_chan) ↣{γ} p a b) ∗ P a b }} := by
  have h := tac_wp_recv (t := t) (TT := Tele.cons fun (_ : A) => Tele.cons fun (_ : B) => Tele.nil)
    γ lr_chan rl_chan p0 _
    (fun a b => ULift.up (v a b)) (fun a b => ULift.up (P a b)) (fun a b => ULift.up (p a b))
    (hm := ⟨rfl⟩)
  iintro %Φ Hc HΦ
  wp_apply h $$ Hc as %x H
  obtain ⟨a, b, ⟨⟩⟩ := x
  simp only [Tele.app]
  iapply HΦ $$ %a %b H

theorem wp_dsp_send0 (γ : dsp_names) (lr_chan rl_chan : loc) (p0 : iProto GF V) (v : V)
    (P : IProp GF) (p : iProto GF V) [ProtoNormalize false p0 [] (<!> iMsg_base v P p)] :
    ⊢ ∀ Φ : val → IProp GF, ((lr_chan, rl_chan) ↣{γ} p0) -∗ P -∗
      ▷ (((lr_chan, rl_chan) ↣{γ} p) -∗ Φ #()) -∗
      WP (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #v)) {{ Φ }} := by
  have h := tac_wp_send (t := t) (TT := Tele.nil.{0}) Tele.Arg.nil γ lr_chan rl_chan p0 _
    (ULift.up v) (ULift.up P) (ULift.up p) (hm := ⟨rfl⟩)
  simp only [Tele.app] at h
  iintro %Φ Hc HP HΦ
  wp_apply h $$ [$Hc $HP] as H
  iapply HΦ $$ H

theorem wp_dsp_send1 {A : Type} (a : A) (γ : dsp_names) (lr_chan rl_chan : loc)
    (p0 : iProto GF V) (v : A → V) (P : A → IProp GF) (p : A → iProto GF V)
    [ProtoNormalize false p0 [] (<!> iMsg_exist fun a => iMsg_base (v a) (P a) (p a))] :
    ⊢ ∀ Φ : val → IProp GF, ((lr_chan, rl_chan) ↣{γ} p0) -∗ P a -∗
      ▷ (((lr_chan, rl_chan) ↣{γ} p a) -∗ Φ #()) -∗
      WP (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #(v a))) {{ Φ }} := by
  have h := tac_wp_send (t := t) (TT := Tele.cons fun (_ : A) => Tele.nil)
    (Tele.Arg.cons a Tele.Arg.nil) γ lr_chan rl_chan p0 _
    (fun a => ULift.up (v a)) (fun a => ULift.up (P a)) (fun a => ULift.up (p a)) (hm := ⟨rfl⟩)
  simp only [Tele.app] at h
  iintro %Φ Hc HP HΦ
  wp_apply h $$ [$Hc $HP] as H
  iapply HΦ $$ H

theorem wp_dsp_send2 {A B : Type} (a : A) (b : B) (γ : dsp_names) (lr_chan rl_chan : loc)
    (p0 : iProto GF V) (v : A → B → V) (P : A → B → IProp GF) (p : A → B → iProto GF V)
    [ProtoNormalize false p0 []
      (<!> iMsg_exist fun a => iMsg_exist fun b => iMsg_base (v a b) (P a b) (p a b))] :
    ⊢ ∀ Φ : val → IProp GF, ((lr_chan, rl_chan) ↣{γ} p0) -∗ P a b -∗
      ▷ (((lr_chan, rl_chan) ↣{γ} p a b) -∗ Φ #()) -∗
      WP (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #(v a b))) {{ Φ }} := by
  have h := tac_wp_send (t := t) (TT := Tele.cons fun (_ : A) => Tele.cons fun (_ : B) => Tele.nil)
    (Tele.Arg.cons a (Tele.Arg.cons b Tele.Arg.nil)) γ lr_chan rl_chan p0 _
    (fun a b => ULift.up (v a b)) (fun a b => ULift.up (P a b)) (fun a b => ULift.up (p a b))
    (hm := ⟨rfl⟩)
  simp only [Tele.app] at h
  iintro %Φ Hc HP HΦ
  wp_apply h $$ [$Hc $HP] as H
  iapply HΦ $$ H

omit [IntoValTyped (GF := GF) V t] in
/-- Rewrite the protocol of an endpoint (used to unfold recursive protocols). -/
theorem dsp_endpoint_eq {γ : dsp_names} {c : chan.t × chan.t} {p q : iProto GF V} (h : p = q) :
    (c ↣{γ} p) ⊢ (c ↣{γ} q) := h ▸ .rfl

end dsp_wrappers

/-! ## Examples -/

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

section dsp_examples
variable [val_countable : Pos.Countable val]

abbrev ref_prot : iProto GF interface.t :=
  <!> iMsg_exist fun (l : loc) => iMsg_exist fun (x : Int) =>
    iMsg_base (interface.mk_ok (go.type.PointerType go.int) #l) iprop(l ↦ W64 x)
      (<?> iMsg_base (interface.mk_ok (go.type.StructType []) #()) iprop(l ↦ (W64 x + W64 2)) END)

theorem wp_DSPExample :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! DSPExample)) (Val #()))
    {{ RET #(W64 42); True }} := by
  wp_start
  -- (`wp_auto` makes no progress on the allocation of a `chan any` local)
  wp_bind (App (Val (GoInstruction (GoAlloc _))) _)
  wp_alloc sig_ptr as Hsig
  wp_pure
  wp_pure
  wp_bind (App (Val (GoInstruction (GoAlloc _))) _)
  wp_pures
  wp_alloc c_ptr as Hc
  wp_pure
  wp_pure
  wp_apply chan.wp_make1 (V := interface.t) as %c %γ ⟨#Hic, -, Hoc⟩
  wp_apply chan.wp_make1 (V := interface.t) as %signal %γ' ⟨#Hicsignal, -, Hocsignal⟩
  imod dsp_session_init ⊤ c signal _ _ γ γ' (ref_prot (GF := GF)) (.inl rfl) (.inl rfl)
    $$ Hic Hicsignal Hoc Hocsignal with ⟨%γdsp1, %γdsp2, Hcp, Hcsignal⟩
  ipersist Hc
  ipersist Hsig
  wp_apply wp_fork $$ [Hcsignal]
  · wp_auto
    wp_apply wp_dsp_recv2 (t := go.any) γdsp2 signal c _ _ _ _ $$ Hcsignal as %l %x ⟨Hcsignal, Hl⟩
    wp_apply wp_dsp_send0 (t := go.any) γdsp2 signal c _ _ _ _ $$ Hcsignal Hl as -
    itrivial
  irename «$r0» => H40
  wp_apply wp_dsp_send2 (t := go.any) «$r0_ptr» (40 : Int) γdsp1 c signal ref_prot _ _ _ $$ Hcp [H40]
    as Hcp
  · iexact H40
  wp_apply wp_dsp_recv0 (t := go.any) γdsp1 c signal _ _ _ _ $$ Hcp as ⟨-, Hl⟩
  rw [show W64 40 + W64 2 = W64 42 from rfl]
  wp_end

end dsp_examples

section serve

abbrev service_prot_aux (Φpre : go_string → IProp GF) (Φpost : go_string → go_string → IProp GF)
    (r : iProto GF go_string) : iProto GF go_string :=
  <!> iMsg_exist fun (req : go_string) => iMsg_base req (Φpre req)
    (<?> iMsg_exist fun (res : go_string) => iMsg_base res (Φpost req res) r)

instance service_prot_contractive (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) : Contractive (service_prot_aux Φpre Φpost) where
  distLater_dist h :=
    (iProto_message_ne Send).ne (iMsg_exist_ne fun req => iMsg_contractive req .rfl
      (fun m hm => (iProto_message_ne Recv).ne (iMsg_exist_ne fun res => iMsg_ne res .rfl (h m hm))))

def service_prot (Φpre : go_string → IProp GF) (Φpost : go_string → go_string → IProp GF) :
    iProto GF go_string :=
  fixpoint (service_prot_aux Φpre Φpost)

/-- (Rocq: the `ProtoUnfold` instance `service_prot_unfold`.) -/
theorem service_prot_unfold (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) :
    service_prot Φpre Φpost = service_prot_aux Φpre Φpost (service_prot Φpre Φpost) :=
  fixpoint_unfold (service_prot_aux Φpre Φpost).toContractiveHom

theorem wp_Serve (f : func.t) (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "#Hf_spec" ∷ □ (∀ (strng : go_string), Φpre strng -∗
          WP (App (Val #f) (Val #strng)) {{ v, ∃ (s' : go_string), ⌜v = #s'⌝ ∗ Φpost strng s' }}) }}
      (App (Val (@! Serve)) (Val #f))
    {{ (strm : stream.t) (γ : dsp_names), RET #strm;
        (strm.req', strm.res') ↣{γ} service_prot Φpre Φpost }} := by
  wp_start as #Hf_spec
  wp_auto
  wp_apply chan.wp_make1 (V := go_string) as %req_ch %γreq ⟨#Hreq, -, Hown_req⟩
  wp_apply chan.wp_make1 (V := go_string) as %res_ch %γres ⟨#Hres, -, Hown_res⟩
  imod dsp_session_init ⊤ req_ch res_ch _ _ γreq γres (service_prot Φpre Φpost) (.inl rfl) (.inl rfl)
    $$ Hreq Hres Hown_req Hown_res with ⟨%γdsp1, %γdsp2, Hclient, Hserver⟩
  ipersist s
  ipersist f
  wp_apply wp_fork $$ [Hserver]
  · ihave s1 := s
    iStructNamed s1
    wp_auto
    ihave HI : ("Hprot" ∷ ((res_ch, req_ch) ↣{γdsp2} iProto_dual (service_prot Φpre Φpost)) : IProp GF)
      $$ [Hserver]
    · iexact Hserver
    wp_for HI
    icases dsp_endpoint_eq (congrArg iProto_dual (service_prot_unfold Φpre Φpost)) $$ Hprot
      with Hprot
    wp_apply wp_dsp_recv1 (t := go.string) γdsp2 res_ch req_ch _ _ _ _ $$ Hprot as %req ⟨Hprot, Hpre⟩
    wp_bind (App (Val #f) _)
    iapply wp_wand $$ (Hf_spec $$ %req Hpre)
    iintro %v ⟨%s', %Heq, HQ⟩
    subst Heq
    wp_auto
    wp_apply wp_dsp_send1 (t := go.string) s' γdsp2 res_ch req_ch _ (fun x => x) _ _ $$ Hprot [HQ]
      as Hprot
    · iexact HQ
    wp_for_post
    iframe
  wp_end

theorem wp_appWrld (s : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! appWrld)) (Val #s))
    {{ RET #(s ++ go!", World!"); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_Client :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! Client)) (Val #()))
    {{ RET #(go!"Hello, World!"); True }} := by
  wp_start
  wp_auto
  wp_apply wp_Serve _ (fun _ => iprop(True)) (fun s1 s2 => iprop(⌜s2 = s1 ++ go!", World!"⌝)) $$ []
    as %hw %γ Hc
  · imodintro
    iintro %s -
    wp_apply wp_appWrld
    iexists _
    iframe
    ipureintro; trivial
  icases dsp_endpoint_eq (service_prot_unfold _ _) $$ Hc with Hc
  wp_apply wp_dsp_send1 (t := go.string) go!"Hello" γ hw.req' hw.res' _ (fun x => x) _ _ $$ Hc []
    as Hc
  wp_apply wp_dsp_recv1 (t := go.string) γ hw.req' hw.res' _ _ _ _ $$ Hc as %res ⟨-, %Hres⟩
  subst Hres
  rw [show go!"Hello" ++ go!", World!" = go!"Hello, World!" from rfl]
  wp_end

end serve

section muxer

abbrev mapper_service_prot_aux (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) (r : iProto GF go_string) : iProto GF go_string :=
  <!> iMsg_exist fun (req : go_string) => iMsg_base req (Φpre req)
    (<?> iMsg_exist fun (res : go_string) => iMsg_base res (Φpost req res) r)

instance mapper_service_prot_contractive (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) :
    Contractive (mapper_service_prot_aux Φpre Φpost) where
  distLater_dist h :=
    (iProto_message_ne Send).ne (iMsg_exist_ne fun req => iMsg_contractive req .rfl
      (fun m hm => (iProto_message_ne Recv).ne (iMsg_exist_ne fun res => iMsg_ne res .rfl (h m hm))))

def mapper_service_prot (Φpre : go_string → IProp GF) (Φpost : go_string → go_string → IProp GF) :
    iProto GF go_string :=
  fixpoint (mapper_service_prot_aux Φpre Φpost)

/-- (Rocq: the `ProtoUnfold` instance `mapper_service_prot_unfold`.) -/
theorem mapper_service_prot_unfold (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) :
    mapper_service_prot Φpre Φpost =
      mapper_service_prot_aux Φpre Φpost (mapper_service_prot Φpre Φpost) :=
  fixpoint_unfold (mapper_service_prot_aux Φpre Φpost).toContractiveHom

def is_mapper_stream (strm : streamold.t) : IProp GF :=
  iprop(∃ (γ : dsp_names) (req_ch res_ch : loc) (f : func.t) (Φpre : go_string → IProp GF)
      (Φpost : go_string → go_string → IProp GF),
    ⌜strm = streamold.t.mk req_ch res_ch f⌝ ∗
    "Hf_spec" ∷ □ (∀ (s : go_string), Φpre s -∗
      WP (App (Val #f) (Val #s)) {{ v, ∃ (s' : go_string), ⌜v = #s'⌝ ∗ Φpost s s' }}) ∗
    ((res_ch, req_ch) ↣{γ} iProto_dual (mapper_service_prot Φpre Φpost)))

theorem wp_mkStream (f : func.t) (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "#Hf_spec" ∷ □ (∀ (strng : go_string), Φpre strng -∗
          WP (App (Val #f) (Val #strng)) {{ v, ∃ (s' : go_string), ⌜v = #s'⌝ ∗ Φpost strng s' }}) }}
      (App (Val (@! mkStream)) (Val #f))
    {{ (γ : dsp_names) (strm : streamold.t), RET #strm;
        is_mapper_stream strm ∗ ((strm.req', strm.res') ↣{γ} mapper_service_prot Φpre Φpost) }} := by
  wp_start as #Hf_spec
  wp_auto
  wp_apply chan.wp_make1 (V := go_string) as %ch1 %γ1 ⟨#His_chan1, -, Hownchan1⟩
  wp_apply_core chan.wp_make1 (V := go_string)
  iintro %ch %γ ⟨#His_chan, -, Hownchan⟩
  imod dsp_session_init ⊤ ch1 ch _ _ γ1 γ (mapper_service_prot Φpre Φpost) (.inl rfl) (.inl rfl)
    $$ His_chan1 His_chan Hownchan1 Hownchan with ⟨%γdsp1, %γdsp2, Hpl, Hpr⟩
  wp_auto
  iapply HΦ
  isplitr [Hpl]
  · unfold is_mapper_stream
    iexists γdsp2, ch1, ch, f, Φpre, Φpost
    iframe
    isplitl []
    · ipureintro; rfl
    iexact Hf_spec
  · iexact Hpl

theorem wp_MapServer (my_stream : streamold.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_mapper_stream my_stream }}
      (App (Val (@! MapServer)) (Val #my_stream))
    {{ RET #(); True }} := by
  wp_start as H
  unfold is_mapper_stream
  icases H with ⟨%γ, %req_ch, %res_ch, %f, %Φpre, %Φpost, %Heq, #Hf_spec, Hprot⟩
  subst Heq
  wp_auto
  wp_for
  icases dsp_endpoint_eq (congrArg iProto_dual (mapper_service_prot_unfold Φpre Φpost)) $$ Hprot
    with Hprot
  wp_apply wp_dsp_recv1 (t := go.string) γ res_ch req_ch _ _ _ _ $$ Hprot as %req ⟨Hprot, Hpre⟩
  wp_bind (App (Val _) (Val #req))
  iapply wp_wand $$ (Hf_spec $$ %req Hpre)
  iintro %v ⟨%s', %Heq, HQ⟩
  subst Heq
  wp_auto
  wp_apply wp_dsp_send1 (t := go.string) s' γ res_ch req_ch _ (fun x => x) _ _ $$ Hprot HQ
    as Hprot
  wp_for_post
  iframe

theorem wp_MapClient (my_stream : streamold.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_mapper_stream my_stream }}
      (App (Val (@! ClientOld)) (Val #()))
    {{ RET #(go!"Hello, World!"); True }} := by
  wp_start as -
  wp_auto
  wp_pures
  rw [recv_eq_func_mk]
  wp_apply wp_mkStream _ (fun _ => iprop(True)) (fun s1 s2 => iprop(⌜s2 = s1 ++ go!","⌝)) $$ []
    as %γ %strm ⟨Hmapper, Hstr⟩
  · imodintro
    iintro %s -
    wp_auto
    iexists _
    iframe
    ipureintro; trivial
  wp_pures
  rw [recv_eq_func_mk]
  wp_apply wp_mkStream _ (fun _ => iprop(True)) (fun s1 s2 => iprop(⌜s2 = s1 ++ go!"!"⌝)) $$ []
    as %γ' %strm' ⟨Hmapper', Hstr'⟩
  · imodintro
    iintro %s -
    wp_auto
    iexists _
    iframe
    ipureintro; trivial
  wp_apply wp_fork $$ [Hmapper]
  · wp_apply wp_MapServer $$ [$Hmapper]
    itrivial
  wp_apply wp_fork $$ [Hmapper']
  · wp_apply wp_MapServer $$ [$Hmapper']
    itrivial
  icases dsp_endpoint_eq (mapper_service_prot_unfold _ _) $$ Hstr with Hstr
  icases dsp_endpoint_eq (mapper_service_prot_unfold _ _) $$ Hstr' with Hstr'
  wp_apply wp_dsp_send1 (t := go.string) go!"Hello" γ strm.req' strm.res' _ (fun x => x) _ _
    $$ Hstr [] as Hstr
  wp_apply wp_dsp_send1 (t := go.string) go!"World" γ' strm'.req' strm'.res' _ (fun x => x) _ _
    $$ Hstr' [] as Hstr'
  wp_apply wp_dsp_recv1 (t := go.string) γ strm.req' strm.res' _ _ _ _ $$ Hstr as %r1 ⟨-, %Hr1⟩
  wp_apply wp_dsp_recv1 (t := go.string) γ' strm'.req' strm'.res' _ _ _ _ $$ Hstr' as %r2 ⟨-, %Hr2⟩
  subst Hr1 Hr2
  rw [show go!"Hello" ++ go!"," ++ go!" " ++ (go!"World" ++ go!"!") = go!"Hello, World!" from rfl]
  wp_end

section mpmc
variable [val_countable : Pos.Countable val]

theorem wp_Muxer (c : loc) (γmpmc : mpmc_names) (n_prod n_cons : Nat) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "#Hismpmc" ∷ is_mpmc γmpmc c n_prod n_cons is_mapper_stream (fun _ => iprop(True)) ∗
        "Hcons" ∷ mpmc_consumer γmpmc UCMRA.unit }}
      (App (Val (@! Muxer)) (Val #c))
    {{ RET #(); True }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave HI : (∃ (received : mset) (sv : streamold.t),
      "s" ∷ s_ptr ↦ sv ∗ "Hcons" ∷ mpmc_consumer γmpmc received : IProp GF) $$ [s Hcons]
  · iexists _, _
    iframe
  wp_for HI
  wp_apply wp_mpmc_receive (t := streamold) γmpmc c n_prod n_cons is_mapper_stream
    (fun _ => iprop(True)) received $$ [$Hismpmc $Hcons] as %v %ok H
  cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · icases H with ⟨-, Hcons, -⟩
    wp_auto
    wp_for_post
    iapply HΦ
    itrivial
  · icases H with ⟨Hdat, Hcons⟩
    wp_auto
    wp_apply wp_fork $$ [Hdat]
    · wp_apply wp_MapServer $$ [$Hdat]
      itrivial
    wp_for_post
    iframe
    iexists _, _
    iframe

theorem wp_makeGreeting :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! makeGreeting)) (Val #()))
    {{ RET #(go!"Hello, World!"); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := streamold.t) (W64 2) $$ [] as %c %γ ⟨#Hic, %Hcap, Hoc⟩
  · ipureintro; decide
  simp only [show (W64 2 = W64 0) = False from by decide, ↓reduceIte]
  imod start_mpmc c is_mapper_stream (fun _ => iprop(True)) γ 1 1 (.Buffered []) trivial
    (by decide) (by decide) $$ Hic Hoc with ⟨%γmpmc, #Hmpmc, Hprods, Hconss⟩
  simp only [List.replicate]
  icases BigSepL.bigSepL_cons.1 $$ Hprods with ⟨Hprod, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Hconss with ⟨Hcons, -⟩
  wp_apply wp_fork $$ [Hcons]
  · wp_apply wp_Muxer c γmpmc 1 1 $$ [$Hmpmc $Hcons]
    itrivial
  wp_pures
  rw [recv_eq_func_mk]
  wp_apply wp_mkStream _ (fun _ => iprop(True)) (fun s1 s2 => iprop(⌜s2 = s1 ++ go!","⌝)) $$ []
    as %γ1 %stream1 ⟨Hstream1, Hc1⟩
  · imodintro
    iintro %s -
    wp_auto
    iexists _
    iframe
    ipureintro; trivial
  wp_pures
  rw [recv_eq_func_mk]
  wp_apply wp_mkStream _ (fun _ => iprop(True)) (fun s1 s2 => iprop(⌜s2 = s1 ++ go!"!"⌝)) $$ []
    as %γ2 %stream2 ⟨Hstream2, Hc2⟩
  · imodintro
    iintro %s -
    wp_auto
    iexists _
    iframe
    ipureintro; trivial
  wp_apply wp_mpmc_send (t := streamold) γmpmc c 1 1 is_mapper_stream (fun _ => iprop(True))
    _ stream1 $$ [$Hmpmc $Hprod $Hstream1] as Hprod
  wp_apply wp_mpmc_send (t := streamold) γmpmc c 1 1 is_mapper_stream (fun _ => iprop(True))
    _ stream2 $$ [$Hmpmc $Hprod $Hstream2] as Hprod
  icases dsp_endpoint_eq (mapper_service_prot_unfold _ _) $$ Hc1 with Hc1
  icases dsp_endpoint_eq (mapper_service_prot_unfold _ _) $$ Hc2 with Hc2
  wp_apply wp_dsp_send1 (t := go.string) go!"Hello" γ1 stream1.req' stream1.res' _ (fun x => x) _ _
    $$ Hc1 [] as Hc1
  wp_apply wp_dsp_send1 (t := go.string) go!"World" γ2 stream2.req' stream2.res' _ (fun x => x) _ _
    $$ Hc2 [] as Hc2
  wp_apply wp_dsp_recv1 (t := go.string) γ1 stream1.req' stream1.res' _ _ _ _ $$ Hc1 as %r1 ⟨-, %Hr1⟩
  wp_apply wp_dsp_recv1 (t := go.string) γ2 stream2.req' stream2.res' _ _ _ _ $$ Hc2 as %r2 ⟨-, %Hr2⟩
  subst Hr1 Hr2
  rw [show go!"Hello" ++ go!"," ++ go!" " ++ (go!"World" ++ go!"!") = go!"Hello, World!" from rfl]
  wp_end

end mpmc

end muxer

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
