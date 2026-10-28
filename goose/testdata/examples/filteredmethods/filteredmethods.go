// Package filteredmethods is translated with a configuration that trusts some
// methods and axiomatizes one
// (filteredmethods/github_com/.../filteredmethods.toml). A method's name in the
// configuration is `T.m`, without T's type parameters and through an alias
// receiver; the method unfoldings leave out exactly the axiomatized one.
package filteredmethods

type box[T any] struct{ v T }

// trusted as box.Get
func (b *box[T]) Get() T { return b.v }

// axiomatized as box.Set
func (b *box[T]) Set(v T) { b.v = v }

func (b box[T]) Peek() T { return b.v }

type counter struct{ n uint64 }

type alias = counter

// trusted as counter.Inc
func (c *alias) Inc() { c.n++ }

func (c counter) Value() uint64 { return c.n }
