
[![Go Reference](https://pkg.go.dev/badge/github.com/lamg/iter.svg)](https://pkg.go.dev/github.com/lamg/iter)

### A library for making composable iterators

[Composability][2] is one of the main ingredients of elegance. When you have basic operations easy to understand in isolation, but allow you to solve complex problems by combining them, you're in the right track. Everything else falls into oblivion or breaks your stream of thoughts.

Let's say we have data in Go to insert in a relational database. The column names are in a string slice `attrs`. The values to be inserted are in a variable `tuples` of type `[][]string`. With that we are going to create a proper [SQL INSERT][0] statement. The basic idea for solving this problem is surrounding the elements in `attrs` with parenthesis, and intercalating commas between them, then prefixing `INSERT INTO table` and suffixing with `VALUES`. The remaining will be done later, let's solve this one first using [github.com/lamg/iter][1]:

```go
package main

import (
    "testing"
    . "github.com/lamg/iter"
)

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
```

The above code leaves in `sql` the value `"INSERT INTO table (name, age) VALUES"`. The design idea behind `PipeS` is providing a means of composing common transformations to iterators. `Intersperse` produces an iterator transformer that intercalates its parameter after each element of the supplied iterator, except the last one. `Surround` produces an iterator that surrounds an iterator with a prefix and a suffix.

You might have noticed the following equivalence,

``` go
var xs []string
si := PipeS(
    xs,
    Surround("X", "Y"),
    Surround("W", "Z"),
)
s := strings.Join(si,"")
```
=

``` go
var xs []string
PipeS(
    xs,
    Surround("WX", "YZ"),
)
s := strings.Join(si,"")
```

which is applicable in `TestSql0`. That's a good thing about having composable operations with clear semantics: we can find properties that are applicable in a whole class of situations, without testing infinite cases.

Let's continue with the problem, now focusing on producing the tail of `INSERT INTO TABLE (name, age) VALUES`. The remaining transformation consist basically in intercalating ", " between a `string` value and the next, and intercalating ", " between each `[]string` and the next. A `tuples` value like `[][]string{{"'X'", "'Y'"}, {"'W'"', "'Z'"}}` should be transformed into `"('X', 'Y'), ('W', 'Z')"`. The solution for that is:


``` go
package main

import (
    "testing"
    . "github.com/lamg/iter"
)

func TestSql1(t *testing.T) {
	tuples := [][]string{{"'X'", "'Y'"}, {"'W'", "'Z'"}}
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
```

Since all we can transform is iterators we need to convert `[][]string` to `Iterator[Iterator[string]]`, that's the reason behind the line `ts := Map0(Slice(tuples), Slice[string])`. Once we have that iterator `PipeI` is needed instead `PipeS` because the latter works with iterators instead of slices as initial element, and what we have is an iterator now. Then inside each individual tuple we intercalate "," and surround with parenthesis. `PipeT` allows us to compose two iterators transformers into a single one, and that way we can use the result as an argument to `Map`. Finally we intercalate an iterator containing "," between each iterator.

In order to see the result we convert each inner iterator to a slice, and then the outer iterator to a slice as well.

As final step we append the `Iterator[string]` from the first step (`INSERT INTO table (name, age) VALUES`) with the `Iterator[Iterator[string]]` (a sequence of rows) from the second step. But we need to flatten the `Iterator[Iterator[string]]` into an `Iterator[string]` in order to append it to the first one. `AppConcP` allows us to append, concatenate and piping an iterator into a sequence of transformers. With that the final program is: 

``` go
package main

import (
    "testing"
    . "github.com/lamg/iter"
)

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
```

The reader can embellish it with new line characters and `;` so the output is more friendly to the eye.

[0]: https://en.wikipedia.org/wiki/Insert_(SQL)
[1]: https://github.com/lamg/iter
[2]: https://github.com/hmemcpy/milewski-ctfp-pdf
