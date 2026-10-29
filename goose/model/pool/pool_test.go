package pool

import (
	"sync"
	"testing"
)

// Each value Put is returned by at most one Get, and Get only returns values
// that were Put.
func TestPoolAtMostOnce(t *testing.T) {
	var p Pool
	const n = 1000
	for i := 1; i <= n; i++ {
		p.Put(i)
	}
	seen := make(map[int]bool)
	for range 2 * n {
		x := p.Get()
		if x == nil {
			continue
		}
		i := x.(int)
		if i < 1 || i > n || seen[i] {
			t.Fatalf("Get returned %v twice or never Put", i)
		}
		seen[i] = true
	}
}

func TestPoolConcurrent(t *testing.T) {
	var p Pool
	var wg sync.WaitGroup
	var mu sync.Mutex
	seen := make(map[int]bool)
	for g := range 8 {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := range 1000 {
				p.Put(g*1000 + i + 1)
				if x := p.Get(); x != nil {
					mu.Lock()
					if seen[x.(int)] {
						t.Errorf("Get returned %v twice", x)
					}
					seen[x.(int)] = true
					mu.Unlock()
				}
			}
		}()
	}
	wg.Wait()
}
