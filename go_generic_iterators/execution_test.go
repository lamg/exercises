package iter

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestExecUntilErr(t *testing.T) {
	r := require.New(t)
	var e error
	x := 0
	I(
		func() bool { return e == nil },
		func() { x++ },
		func() { x++ },
		func() { e = fmt.Errorf("bla") },
		func() { x++ },
	)
	r.Equal(2, x)
}

func TestExecWhileNoErr(t *testing.T) {
	r := require.New(t)
	var e error
	x := 0
	W(
		func() bool { return e == nil },
		func() { x++ },
		func() { x++ },
		func() {
			if x == 20 { // 20 ≡ 2 (mod 3)
				e = fmt.Errorf("bla")
			}
		},
		func() { x++ },
	)
	r.Equal(20, x)
}
