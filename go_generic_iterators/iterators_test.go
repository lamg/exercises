package iter

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestSlice(t *testing.T) {
	r := require.New(t)
	ns := []int{0, 1, 2, 3, 4, 5}
	rs := ToSlice(Slice(ns))
	r.Equal(ns, rs)
}

func TestFilter(t *testing.T) {
	r := require.New(t)
	rs := PipeS(
		[]int{0, 1, 2, 3, 4, 5},
		Filter(func(n int) bool { return n > 2 }),
	)
	r.Equal([]int{3, 4, 5}, rs)
}

func TestConcat(t *testing.T) {
	r := require.New(t)
	its := Args(Slice([]int{0, 1, 2}), Slice([]int{3, 4}), Slice([]int{5}))
	xs := ToSlice(Concat(its))
	r.Equal([]int{0, 1, 2, 3, 4, 5}, xs)
	its = Args(Slice([]int{}))
	xs = ToSlice(Concat(its))
	r.Equal([]int{}, xs)
}

func TestMap(t *testing.T) {
	r := require.New(t)
	const tail = "kkkk"
	sl := PipeS(
		[]string{"aeo", "uu"},
		Map(func(s string) string { return s + tail }),
	)
	r.Equal([]string{"aeo" + tail, "uu" + tail}, sl)
}

func TestDropLast(t *testing.T) {
	r := require.New(t)
	ts := []struct {
		xs []string
		rs []string
	}{
		{
			xs: []string{"bla"},
			rs: []string{},
		},
		{
			xs: []string{"bla", "Bli"},
			rs: []string{"bla"},
		},
		{
			xs: []string{},
			rs: []string{},
		},
	}
	for _, j := range ts {
		ms := PipeS(
			j.xs,
			DropLast[string],
		)
		r.Equal(j.rs, ms)
	}
}

func TestZip(t *testing.T) {
	r := require.New(t)
	ts := []struct {
		xs []string
		rs []string
	}{
		{xs: []string{"a"}, rs: []string{"a", ","}},
		{xs: []string{"a", "b"}, rs: []string{"a", ",", "b", ","}},
	}
	for _, j := range ts {
		ms := PipeI(
			Const(","),
			Zip(Slice(j.xs)),
		)
		r.Equal(j.rs, ToSlice(ms))
	}
}

func TestSurround(t *testing.T) {
	r := require.New(t)
	sl := PipeS(
		[]string{"aeo", "uu"},
		Surround("(", ")"),
	)
	r.Equal([]string{"(", "aeo", "uu", ")"}, sl)
}

func TestIntersperse(t *testing.T) {
	r := require.New(t)
	ts := []struct {
		xs []string
		rs []string
	}{
		{xs: []string{"a"}, rs: []string{"a"}},
		{xs: []string{"a", "b"}, rs: []string{"a", ",", "b"}},
	}
	for _, j := range ts {
		ms := PipeS(j.xs, Intersperse(","))
		r.Equal(j.rs, ms)
	}
}

func TestPipe(t *testing.T) {
	r := require.New(t)
	sl := PipeS(
		[]string{"aeo", "uu"},
		Intersperse(","),
		Surround("(", ")"),
	)
	r.Equal([]string{"(", "aeo", ",", "uu", ")"}, sl)

	rs := PipeS(
		[]int{1, 2, 3},
	)
	r.Equal([]int{1, 2, 3}, rs)
}

func TestCompositeTypePipe(t *testing.T) {
	r := require.New(t)
	rs := PipeS(
		IntStrS(1, 2, 3, 4),
		Filter(Gt[IntStr](2)),
		Map(Plus(NewIntStrN, 1)),
		Map(IntToStr),
	)
	r.Equal(StrIntS("4", "5"), rs)
}

func TestAppend(t *testing.T) {
	r := require.New(t)
	rs := PipeS(
		[]string{"a", "b"},
		Append(Args("c", "d")),
		Append(Args[string]()),
	)
	r.Equal([]string{"a", "b", "c", "d"}, rs)
}

func TestAppConc(t *testing.T) {
	r := require.New(t)
	rs := PipeS(
		[]string{"a", "b"},
		AppConc(
			Args(Args("c", "d"), Args("e", "f")),
		),
	)
	r.Equal([]string{"a", "b", "c", "d", "e", "f"}, rs)
}

func TestAppConcP(t *testing.T) {
	r := require.New(t)
	rs := PipeS(
		[]string{"a", "b"},
		AppConcP(
			Args(Args("c"), Args("e")),
			Surround(Args("x"), Args("y")),
		),
	)
	r.Equal([]string{"a", "b", "x", "c", "e", "y"}, rs)
}

func TestZipDrop(t *testing.T) {
	// checks that Zip doesn't go beyond if one iterator ends
	// and that DropLast doesn't calls Zip.Next twice
	r := require.New(t)
	s := PipeS(
		[]string{","},
		Zip(Args[string]()),
		DropLast[string],
	)
	r.Equal([]string{}, s)
}

func TestSql0(t *testing.T) {
	attrs := []string{"name", "age"}
	sqlS := PipeS(
		attrs,
		Intersperse(", "),
		Surround("(", ")"),
		Surround("INSERT INTO table ", " VALUES"),
	)
	sql := strings.Join(sqlS, "")
	t.Log("sql:", sql)
}

func TestSql1(t *testing.T) {
	tuples := [][]string{{"'X'", "'Y'"}, {"'W'", "'Z'"}}
	// a conversion from [][]string to Iterator[Iterator[string]] is needed
	// in order to use have a transformable version of the elements in tuples
	ts := Map0(Slice(tuples), Slice[string])
	sqlS := PipeI(
		ts,
		Map(
			PipeT(
				Intersperse(", "),
				Surround("(", ")"),
			),
		),
		Intersperse(Args(",")),
	)
	rs := ToSlice(Map0(sqlS, ToSlice[string]))
	t.Log("tail:", rs)
}

func TestSql(t *testing.T) {
	attrs := []string{"name", "age"}
	tuples := [][]string{{"'Ronnie'", "53"}, {"'Richie'", "23"}}
	ts := Map0(Slice(tuples), Slice[string])
	sqlS := PipeS(
		attrs,
		Intersperse(", "),
		Surround("(", ")"),
		Surround("INSERT INTO table ", " VALUES "),
		AppConcP(
			ts,
			Map(
				PipeT(
					Intersperse(", "),
					Surround("(", ")"),
				),
			),
			Intersperse(Args(",")),
		),
	)
	sql := strings.Join(sqlS, "")
	t.Log("sql:", sql)
}
