package concurrency

import (
	"fmt"
	"sync"
	"time"
)

type job struct {
	i    int
	max  int
	text string
}

func outputText(grp *sync.WaitGroup, j *job) {
	for j.i != j.max {
		time.Sleep(time.Millisecond)
		fmt.Printf("%s: %d\n", j.text, j.i)
		j.i = j.i + 1
	}
	grp.Done()
}

func helloWaitGroup() {
	grp := new(sync.WaitGroup)
	fmt.Println("Starting...")
	hello, world := &job{
		i:    0,
		max:  5,
		text: "hello",
	}, &job{
		i:    5,
		max:  10,
		text: "world",
	}
	go outputText(grp, hello)
	go outputText(grp, world)
	grp.Add(2)
	grp.Wait()
}
