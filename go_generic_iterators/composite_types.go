package iter

import "strconv"

// code needed for mapping an Int to a String

type IntStr struct {
	n int
	s string
}

func (m IntStr) Int() int {
	return m.n
}

func IntToStr(a IntStr) (b IntStr) {
	b = IntStr{s: strconv.Itoa(a.n)}
	return
}

func IntStrS(ns ...int) []IntStr {
	rs := make([]IntStr, len(ns))
	for i, j := range ns {
		rs[i] = IntStr{n: j}
	}
	return rs
}

func StrIntS(ss ...string) (rs []IntStr) {
	rs = make([]IntStr, len(ss))
	for i, j := range ss {
		rs[i] = IntStr{s: j}
	}
	return
}

func NewIntStrN(n int) IntStr {
	return IntStr{n: n}
}

// code reusable for all Int instances

type Int interface {
	Int() int
}

func Gt[T Int](n int) func(T) bool {
	return func(m T) bool {
		return m.Int() > n
	}
}

func Plus[T Int](b func(int) T, n int) func(T) T {
	return func(m T) (r T) {
		return b(n + m.Int())
	}
}
