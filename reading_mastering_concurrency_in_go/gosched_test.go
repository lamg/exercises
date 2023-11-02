package concurrency

import (
	"runtime"
	"testing"
)

func TestNoSched(t *testing.T) {
	NoSched()
	// only prints "Bye"
}

func TestSched(t *testing.T) {
	Sched()
	//show some, since according documentation
	//runtime.Gosched allows other goroutines to run
	//which mean that maybe not all are allowed
}

func TestSchedNoParallel(t *testing.T) {
	runtime.GOMAXPROCS(1)
	Sched()
}
