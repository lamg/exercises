package concurrency

import (
	"fmt"
)

func isPalindrome(x int) (y bool) {
	s := fmt.Sprintf("%d", x)
	y = true
	for i := 0; y && i != len(s)/2; i++ {
		y = y && s[i] == s[len(s)-i-1]
	}
	return
}
