package boolean

type Iterator[T interface{}] struct {
	slc []T
	idx int
}

func Begin(slc []T) Iterator[T] {
	return Iterator[T]{
		slc: slc,
		idx: 0,
	}
}

func (i *Iterator[T]) End() bool {
	return i.idx >= len(i.slc)
}

func (i *Iterator[T]) Next() {
	i.idx++
}

func (i *Iterator[T]) Get() T {
	return i.slc[i.idx]
}

func (i *Iterator[T]) Ptr() T {
	return &i.slc[i.idx]
}

