package concurrency

type wG struct {
	counter uint64
}

func (w *wG) Done() {
	w.counter = w.counter - 1
}

func (w *wG) Add(n uint64) {
	w.counter = w.counter + n
}

func (w *wG) Wait() {
	for w.counter != 0 {

	}
}
