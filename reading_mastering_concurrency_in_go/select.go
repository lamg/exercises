package concurrency

import (
	"fmt"
)

func channel() {
	ch := make(chan int)
	go func() {
		for i := 0; i != 10; i++ {
			ch <- i
		}
		close(ch)
	}()
	for i := range ch {
		fmt.Println(i)
	}
}

func selectExample() {
	c0 := chanInt(3)
	c1 := chanInt(3)
	ok0, ok1 := true, true
	for ok0 || ok1 {
		var x, y int
		select {
		case x, ok0 = <-c0:
			if ok0 {
				fmt.Printf("c0: %d\n", x)
			}
		case y, ok1 = <-c1:
			if ok1 {
				fmt.Printf("c1: %d\n", y)
			}
		}
	}
}

func chanInt(n int) (c chan int) {
	c = make(chan int)
	go func() {
		for i := 0; i < n; i++ {
			c <- i
		}
		close(c)
	}()
	return
}
