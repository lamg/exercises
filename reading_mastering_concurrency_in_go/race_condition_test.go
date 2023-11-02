package concurrency

import (
	"fmt"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestBank(t *testing.T) {
	b, wg := &bank{balance: 0, m: new(sync.RWMutex)}, new(sync.WaitGroup)
	wg.Add(2)
	go func() {
		b.Deposit(200)
		fmt.Printf("Deposit: %d\n", b.Balance())
		wg.Done()
	}()
	go func() {
		b.Deposit(100)
		wg.Done()
	}()
	wg.Wait()
}

func TestIsPalindrome(t *testing.T) {
	n := 12345
	r := isPalindrome(n)
	require.False(t, r)
	n = 123321
	r = isPalindrome(n)
	require.True(t, r)
	n = 1
	r = isPalindrome(n)
	require.True(t, r)
	n = 131
	r = isPalindrome(n)
	require.True(t, r)
}
