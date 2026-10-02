/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_dsp.v`:
examples of dependent separation protocols (DSP) over Go channels, and an MPMC muxer.

Lean notes / deviations:
* DSP sends/receives use the `wp_send`/`wp_recv` tactics of `DspProofmode.lean` (Lean syntax:
  `wp_recv (x y) as pat`, `wp_send with [$H]`). As in Rocq they do not run `wp_auto`
  afterwards; `wp_recv (?) as "->"` is written `wp_recv (_) as %rfl`.
* `ProtoUnfold` is a separate class (`*_proto_unfold` instances, from the equations
  `*_unfold`), used by `wp_send`/`wp_recv` only to unfold the head of a protocol. The `*_aux`
  protocol bodies are `abbrev`s so that `ProtoNormalize` sees through them.
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
variable [ext : ffi_syntax]

instance streamold_countable : Pos.Countable streamold.t :=
  .ofInjective (fun x => Pos.Countable.encode (x.req', x.res', x.f'))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

end countable

/-! ## Examples -/

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

section dsp_examples

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
    wp_recv (l x) as Hl
    wp_auto
    wp_send with [$Hl]
    wp_auto
    itrivial
  irename «$r0» => H40
  wp_send with [$H40]
  wp_auto
  wp_recv as Hl
  wp_auto
  rw [show W64 40 + W64 2 = W64 42 from rfl]
  wp_end

end dsp_examples

section serve

abbrev service_prot_aux (Φpre : go_string → IProp GF) (Φpost : go_string → go_string → IProp GF)
    (r : iProto GF go_string) : iProto GF go_string :=
  <!> iMsg_exist fun (req : go_string) => iMsg_base req (Φpre req)
    (<?> iMsg_exist fun (res : go_string) => iMsg_base res (Φpost req res) r)

instance service_prot_contractive (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) : Contractive (service_prot_aux Φpre Φpost) := by
  solve_proto_contractive

def service_prot (Φpre : go_string → IProp GF) (Φpost : go_string → go_string → IProp GF) :
    iProto GF go_string :=
  fixpoint (service_prot_aux Φpre Φpost)

theorem service_prot_unfold (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) :
    service_prot Φpre Φpost = service_prot_aux Φpre Φpost (service_prot Φpre Φpost) :=
  fixpoint_unfold (service_prot_aux Φpre Φpost).toContractiveHom

instance service_prot_proto_unfold (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) :
    ProtoUnfold (service_prot Φpre Φpost) (service_prot_aux Φpre Φpost (service_prot Φpre Φpost)) :=
  ⟨service_prot_unfold Φpre Φpost⟩

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
    wp_recv (req) as Hpre
    wp_auto
    wp_bind (App (Val #f) _)
    iapply wp_wand $$ (Hf_spec $$ %req Hpre)
    iintro %v ⟨%s', %Heq, HQ⟩
    subst Heq
    wp_auto
    wp_send with [$HQ]
    wp_auto
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
  wp_send with [//]
  wp_auto
  wp_recv (_) as %rfl
  wp_auto
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
    Contractive (mapper_service_prot_aux Φpre Φpost) := by
  solve_proto_contractive

def mapper_service_prot (Φpre : go_string → IProp GF) (Φpost : go_string → go_string → IProp GF) :
    iProto GF go_string :=
  fixpoint (mapper_service_prot_aux Φpre Φpost)

theorem mapper_service_prot_unfold (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) :
    mapper_service_prot Φpre Φpost =
      mapper_service_prot_aux Φpre Φpost (mapper_service_prot Φpre Φpost) :=
  fixpoint_unfold (mapper_service_prot_aux Φpre Φpost).toContractiveHom

instance mapper_service_prot_proto_unfold (Φpre : go_string → IProp GF)
    (Φpost : go_string → go_string → IProp GF) :
    ProtoUnfold (mapper_service_prot Φpre Φpost) (mapper_service_prot_aux Φpre Φpost (mapper_service_prot Φpre Φpost)) :=
  ⟨mapper_service_prot_unfold Φpre Φpost⟩

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
  wp_recv (req) as Hpre
  wp_auto
  wp_bind (App (Val _) (Val #req))
  iapply wp_wand $$ (Hf_spec $$ %req Hpre)
  iintro %v ⟨%s', %Heq, HQ⟩
  subst Heq
  wp_auto
  wp_send with [$HQ]
  wp_auto
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
  wp_send with [//]
  wp_auto
  wp_send with [//]
  wp_auto
  wp_recv (_) as %rfl
  wp_auto
  wp_recv (_) as %rfl
  wp_auto
  rw [show go!"Hello" ++ go!"," ++ go!" " ++ (go!"World" ++ go!"!") = go!"Hello, World!" from rfl]
  wp_end

section mpmc

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
  wp_send with [//]
  wp_auto
  wp_send with [//]
  wp_auto
  wp_recv (_) as %rfl
  wp_auto
  wp_recv (_) as %rfl
  wp_auto
  rw [show go!"Hello" ++ go!"," ++ go!" " ++ (go!"World" ++ go!"!") = go!"Hello, World!" from rfl]
  wp_end

end mpmc

end muxer

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
