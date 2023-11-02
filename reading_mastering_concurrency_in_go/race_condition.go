package concurrency

import (
	"sync"
)

type bank struct {
	balance int
	m       *sync.RWMutex
}

func (b *bank) Deposit(amount int) {
	b.m.Lock()
	b.balance = b.balance + amount
	b.m.Unlock()
}

func (b *bank) Balance() (n int) {
	b.m.RLock()
	n = b.balance
	b.m.RUnlock()
	return
}
