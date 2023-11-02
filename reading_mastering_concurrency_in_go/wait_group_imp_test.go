package concurrency

import (
	"fmt"
	"testing"
	"time"
)

func TestWaitGroupImp(t *testing.T) {
	w := new(wG)
	w.Add(2)
	go count("c0", 10, w)
	go count("c1", 10, w)
	w.Wait()
}

func count(name string, n int, w *wG) {
	for i := 0; i < n; i++ {
		fmt.Printf("%s: %d\n", name, i)
		time.Sleep(1 * time.Second)
	}
	w.Done()
}
