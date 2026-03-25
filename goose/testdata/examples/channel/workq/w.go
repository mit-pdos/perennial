package workq

import (
	"strings"
	"sync/atomic"
)

type Worker struct {
	queue chan string
	steal chan chan *string // reply is a pointer: nil means nothing to steal
}

type shared struct {
	remaining *atomic.Int64
	total     *atomic.Int64
	done      chan struct{}
}

func (w *Worker) run(
	neighbor *Worker,
	sh shared,
) {
	for {
		select {
		case <-sh.done:
			return

		case doc := <-w.queue:
			w.process(doc, sh)

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
			case <-sh.done:
				return
			case neighbor.steal <- reply:
				// Steal request accepted; wait for their response.
				if doc := <-reply; doc != nil {
					w.process(*doc, sh)
				}
			case doc := <-w.queue:
				// New work arrived locally while we were trying to steal.
				w.process(doc, sh)
			}
		}
	}
}

func (w *Worker) process(doc string, sh shared) {
	sh.total.Add(int64(len(strings.Fields(doc))))
	if sh.remaining.Add(-1) == 0 {
		close(sh.done)
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
			queue: make(chan string, len(docs)),
			steal: make(chan chan *string),
		}
	}

	// All documents start on worker 0's queue — maximally unbalanced.
	for _, doc := range docs {
		workers[0].queue <- doc
	}

	sh := shared{
		remaining: new(atomic.Int64),
		total:     new(atomic.Int64),
		done:      make(chan struct{}),
	}
	sh.remaining.Store(int64(len(docs)))

	for i, w := range workers {
		neighbor := workers[(i+1)%numWorkers]
		go w.run(neighbor, sh)
	}

	<-sh.done
	return sh.total.Load()
}
