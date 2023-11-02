package concurrency

import (
	"fmt"
	"runtime"
	"time"
)

// NoSched doesn't call runtime.Gosched
func NoSched() {
	for i := 0; i != 10; i++ {
		go show(i)
	}
	fmt.Println("Bye")
}

func show(i int) {
	fmt.Println(i)
	time.Sleep(10 * time.Millisecond)
}

// Sched calls runtime.Gosched
func Sched() {
	for i := 0; i != 10; i++ {
		go show(i)
	}
	runtime.Gosched()
	fmt.Println("Bye")
}
