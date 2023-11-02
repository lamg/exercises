package iter

type Iterator[T any] interface {
	Current() T
	Next() bool
}

// Slice iterator definition

type slice[T any] struct {
	xs   []T
	i    int
	init bool
}

func Slice[T any](xs []T) Iterator[T] {
	return &slice[T]{xs: xs, init: true}
}

func Args[T any](xs ...T) Iterator[T] {
	return Slice(xs)
}

func (p *slice[T]) Current() (m T) {
	if p.i != len(p.xs) {
		m = p.xs[p.i]
	}
	return
}

func (p *slice[T]) Next() (ok bool) {
	if p.init {
		p.init = false
	} else if p.i != len(p.xs) {
		p.i = p.i + 1
	}
	ok = p.i != len(p.xs)
	return
}

func ToSlice[T any](p Iterator[T]) (rs []T) {
	rs = make([]T, 0)
	for p.Next() {
		rs = append(rs, p.Current())
	}
	return
}

// end

// Filter iterator definition

type filter[T any] struct {
	xs Iterator[T]
	f  func(T) bool
	m  T
}

func Filter[T any](f func(T) bool) IterT[T] {
	return func(xs Iterator[T]) Iterator[T] {
		return &filter[T]{xs: xs, f: f}
	}
}

func (b *filter[T]) Current() (m T) {
	m = b.m
	return
}

func (b *filter[T]) Next() (ok bool) {
	hasMore := b.xs.Next()
	for !ok && hasMore {
		ok = b.f(b.xs.Current())
		if !ok {
			hasMore = b.xs.Next()
		} else {
			b.m = b.xs.Current()
		}
	}
	return
}

// end

// Concat iterator definition

func Concat[T any](xs Iterator[Iterator[T]]) (c Iterator[T]) {
	it := &concat[T]{xs: xs}
	it.ok = xs.Next()
	if it.ok {
		it.curr = xs.Current()
	}
	c = it
	return
}

type concat[T any] struct {
	xs   Iterator[Iterator[T]]
	ok   bool
	curr Iterator[T]
}

func (c *concat[T]) Current() (m T) {
	if c.ok {
		m = c.curr.Current()
	}
	return
}

func (c *concat[T]) Next() (ok bool) {
	for c.ok && !ok {
		ok = c.curr.Next()
		if !ok {
			c.ok = c.xs.Next()
			if c.ok {
				c.curr = c.xs.Current()
			}
		}
	}
	return
}

// end

// Map iterator definition

type map0[T any, U any] struct {
	xs Iterator[T]
	f  func(T) U
}

func Map0[T any, U any](xs Iterator[T], f func(T) U) Iterator[U] {
	return &map0[T, U]{xs: xs, f: f}
}

func (r *map0[T, U]) Current() (m U) {
	n := r.xs.Current()
	m = r.f(n)
	return
}

func (r *map0[T, U]) Next() (ok bool) {
	ok = r.xs.Next()
	return
}

func Map[T any](f func(T) T) IterT[T] {
	return func(xs Iterator[T]) Iterator[T] {
		return Map0(xs, f)
	}
}

// end

// DropLast iterator definition

type dropLast[T any] struct {
	xs     Iterator[T]
	m0, m1 T
	ok     bool
}

func DropLast[T any](xs Iterator[T]) Iterator[T] {
	r := &dropLast[T]{xs: xs}
	r.ok = xs.Next()
	if r.ok {
		r.m1 = xs.Current()
	}
	return r
}

func (r *dropLast[T]) Current() (m T) {
	m = r.m0
	return
}

func (r *dropLast[T]) Next() (ok bool) {
	if r.ok {
		ok = r.xs.Next()
		if ok {
			r.m0 = r.m1
			r.m1 = r.xs.Current()
		}
		r.ok = ok
	}
	return
}

// end

// Zip iterator definition

type zip[T any] struct {
	a, b Iterator[T]
	ca   bool // consume from a
	ok   bool
}

func Zip[T any](a Iterator[T]) IterT[T] {
	return func(b Iterator[T]) Iterator[T] {
		return &zip[T]{a: a, b: b, ca: true, ok: true}
	}
}

func (r *zip[T]) Current() (m T) {
	if !r.ca {
		m = r.a.Current()
	} else {
		m = r.b.Current()
	}
	return
}

func (r *zip[T]) Next() (ok bool) {
	if r.ok {
		if r.ca {
			ok = r.a.Next()
		} else {
			ok = r.b.Next()
		}
		r.ok = ok
		r.ca = !r.ca
	}
	return
}

// end

// Const iterator definition
type consti[T any] struct {
	curr T
}

func Const[T any](c T) Iterator[T] {
	return &consti[T]{curr: c}
}

func (r *consti[T]) Current() (m T) {
	m = r.curr
	return
}

func (r *consti[T]) Next() (ok bool) {
	ok = true
	return
}

// end

// Surround iterator definition
type surround[T any] struct {
	xs                  Iterator[T]
	a, b                T
	init                bool
	first, middle, last bool
}

func Surround[T any](a, b T) IterT[T] {
	return func(xs Iterator[T]) Iterator[T] {
		return &surround[T]{xs: xs, a: a, b: b, init: true}
	}
}

func (p *surround[T]) Current() (m T) {
	if p.first {
		m = p.a
	} else if p.middle {
		m = p.xs.Current()
	} else if p.last {
		m = p.b
	}
	return
}

func (p *surround[T]) Next() (ok bool) {
	if p.init {
		p.first, p.init = true, false
	} else if p.first {
		p.init, p.first, p.middle = false, false, p.xs.Next()
	} else if p.middle {
		p.middle = p.xs.Next()
		p.last = !p.middle
	} else if p.last {
		p.last = false
	}
	ok = p.first || p.middle || p.last
	return
}

// end

// Intersperse iterator definition

func Intersperse[T any](x T) IterT[T] {
	return func(xs Iterator[T]) Iterator[T] {
		return PipeI(
			Const(x),
			Zip(xs),
			DropLast[T],
		)
	}
}

// end

// Pipe iterator definition

type IterT[T any] func(Iterator[T]) Iterator[T]

func PipeT[T any](fs ...IterT[T]) IterT[T] {
	return func(xs Iterator[T]) (rs Iterator[T]) {
		s := Slice(fs)
		rs = xs
		for s.Next() {
			rs = s.Current()(rs)
		}
		return
	}
}

func PipeI[T any](xs Iterator[T], fs ...IterT[T]) Iterator[T] {
	return PipeT(fs...)(xs)
}

func PipeS[T any](xs []T, fs ...IterT[T]) []T {
	rs := PipeI(
		Slice(xs),
		fs...,
	)
	return ToSlice(rs)
}

func ConcPipeI[T any](xs Iterator[Iterator[T]], fs ...IterT[Iterator[T]]) Iterator[T] {
	return Concat(PipeI(xs, fs...))
}

// end

// Append iterator end

func Append[T any](xs Iterator[T]) IterT[T] {
	return func(ps Iterator[T]) Iterator[T] {
		return Concat(Args(ps, xs))
	}
}

func AppConc[T any](xss Iterator[Iterator[T]]) IterT[T] {
	return func(ps Iterator[T]) Iterator[T] {
		return Append(Concat(xss))(ps)
	}
}

func AppConcP[T any](xs Iterator[Iterator[T]], fs ...IterT[Iterator[T]]) IterT[T] {
	return Append(ConcPipeI(xs, fs...))
}

// end
