From New.proof Require Import proof_prelude.
From New.proof Require Import sync sync.atomic strings fmt.
From New.generatedproof Require Import x.

(*
package main

import (
	"fmt"
	"strings"
	"sync"
	"sync/atomic"
)

type Worker struct {
	id    int
	queue chan string
	steal chan chan *string // reply is a pointer: nil means nothing to steal
}

func (w *Worker) run(
	neighbor *Worker,
	total *atomic.Int64,
	remaining *atomic.Int64,
	done chan struct{},
	wg *sync.WaitGroup,
) {
	defer wg.Done()
	for {
		select {
		case <-done:
			return

		case doc := <-w.queue:
			w.process(doc, total, remaining, done)

		case reply := <-w.steal:
			// A neighbor wants to steal a document from us.
			// Respond immediately: send a document if available, nil otherwise.
			select {
			case doc := <-w.queue:
				reply <- &doc
			default:
				reply <- nil
			}

		default:
			// Idle: attempt to steal from neighbor.
			// reply is buffered so the victim can always respond, even if
			// we find local work and stop listening before they reply.
			reply := make(chan *string, 1)
			select {
			case <-done:
				return
			case neighbor.steal <- reply:
				fmt.Println("stole")
				// Steal request accepted; wait for their response.
				if doc := <-reply; doc != nil {
					w.process( *doc, total, remaining, done)
				}
			case doc := <-w.queue:
				// New work arrived locally while we were trying to steal.
				w.process(doc, total, remaining, done)
			}
		}
	}
}

func (w *Worker) process(doc string, total *atomic.Int64, remaining *atomic.Int64, done chan struct{}) {
	total.Add(int64(len(strings.Fields(doc))))
	if remaining.Add(-1) == 0 {
		close(done)
	}
}

func wordCount(docs []string) int64 {
	if len(docs) == 0 {
		return 0
	}

	const numWorkers = 2
	workers := make([]*Worker, numWorkers)
	for i := range workers {
		workers[i] = &Worker{
			id:    i,
			queue: make(chan string, len(docs)),
			steal: make(chan chan *string),
		}
	}

	// All documents start on worker 0's queue — maximally unbalanced.
	for _, doc := range docs {
		workers[0].queue <- doc
	}

	var total atomic.Int64
	var remaining atomic.Int64
	remaining.Store(int64(len(docs)))
	done := make(chan struct{})

	var wg sync.WaitGroup
	for i, w := range workers {
		wg.Add(1)
		neighbor := workers[(i+1)%numWorkers]
		go w.run(neighbor, &total, &remaining, done, &wg)
	}

	wg.Wait()
	return total.Load()
}

func main() {
	docs := []string{
		"the cat sat on the mat",
		"a quick brown fox jumps over the lazy dog",
		"to be or not to be that is the question",
		"all that glitters is not gold",
		"ask not what your country can do for you",
		"one small step for man one giant leap for mankind",
		"we hold these truths to be self evident",
		"in the beginning was the word and the word was good",
	}

	got := wordCount(docs)

	want := int64(0)
	for _, doc := range docs {
		want += int64(len(strings.Fields(doc)))
	}
	fmt.Printf("word count: %d (expected %d)\n", got, want)
}
*)

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : main.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) main := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) main := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop main get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    main.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init main }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?). reflexivity. }
  iIntros "Hown". wp_auto.
Admitted.

Record γ :=
  {
    docs : list string;
  }.

(* TODO now:
- Add fragmentary ghost state representing permission to run a task `doc` once.
  An alternative that this proof DOES NOT use would be gmultiset. Because the
  same task could show up once, this needs to be auth+frag gmultiset ghost state.
 *)

Definition is_coordinator_invariant γ (total_ptr remaining_ptr : loc) : iProp Σ :=
  (* TODO now:
     owns authortative knowledge of the outstanding [docs] are remaining. In
     order to decrement remaining_ptr, ownership of the relevant doc's fragment
     will have to be returned to delete it from the gmultiset.
   *)
.

Definition is_Worker (w_ptr : loc) : iProp Σ :=
  w_ptr.[main.Worker.] ↦
.

Lemma wp_Clone sl_b dq (b : list w8) :
  {{{
    is_pkg_init bytes ∗
    "Hsl_b" ∷ sl_b ↦*{dq} b
  }}}
  @! bytes.Clone #sl_b
  {{{
    sl_b', RET #sl_b';
    "Hsl_b" ∷ sl_b ↦*{dq} b ∗
    "Hsl_b'" ∷ sl_b' ↦* b ∗
    "Hsl_b'_cap" ∷ own_slice_cap w8 sl_b' (DfracOwn 1)
  }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  wp_if_destruct.
  { iApply "HΦ".
    iDestruct (own_slice_len with "Hsl_b") as %[Hb_len ?].
    apply nil_length_inv in Hb_len. subst.
    iFrame "∗#".
    iDestruct own_slice_nil as "$".
    iDestruct own_slice_cap_nil as "$".
  }
  wp_apply wp_slice_literal as "% _".
  { iIntros. wp_auto. iFrame. }
  wp_apply (wp_slice_append with "[$Hsl_b]") as "* (?&?&?)".
  { iDestruct own_slice_empty as "$"; try done.
    iDestruct own_slice_cap_empty as "$"; try done. }
  wp_end.
Qed.

Lemma wp_Equal sl_b0 sl_b1 d0 d1 (b0 b1 : list w8) :
  {{{
    is_pkg_init bytes ∗
    "Hb0" ∷ sl_b0 ↦*{d0} b0 ∗
    "Hb1" ∷ sl_b1 ↦*{d1} b1
  }}}
  @! bytes.Equal #sl_b0 #sl_b1
  {{{
    RET #(bool_decide (b0 = b1));
    sl_b0 ↦*{d0} b0 ∗
    sl_b1 ↦*{d1} b1
  }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  wp_apply (wp_bytes_to_string with "Hb0") as "Hb0".
  wp_apply (wp_bytes_to_string with "Hb1") as "Hb1".
  iApply "HΦ". iFrame.
Qed.

End wps.
