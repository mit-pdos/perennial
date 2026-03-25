package workq

import (
	"strings"
	"testing"
)

func testWorkQueue(t *testing.T, docs []string) {
	got := wordCount(docs)

	want := int64(0)
	for _, doc := range docs {
		want += int64(len(strings.Fields(doc)))
	}
	if got != want {
		t.Errorf("word count: got %d != %d", got, want)
	}
}

func TestWorkQueueParallelSearch(t *testing.T) {
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
	testWorkQueue(t, docs)
}

func TestWorkQueueNoDocs(t *testing.T) {
	testWorkQueue(t, []string{})
}
