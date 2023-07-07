package boolean

type Cover []Cube

func NewCover(rsv int, s ...Cube) Cover {
	for _, si := range s {
		if len(si) > rsv {
			rsv = len(si)
		}
	}
	result := make(Cover, 0, rsv)
	for _, si := range s {
		result = append(result, si.Clone())
	}
	return result
}

func (c Cover) Clone() Cover {
	result := make(Cover, 0, len(c))
	for _, ci := range c {
		result = append(result, ci.Clone())
	}
	return result
}

func (c *Cover) Reserve(num int) {
	tmp := *c
	*c = make(Cover, len(tmp), len(tmp)+num)
	copy(*c, tmp)
}

func (c Cover) BackPtr() *Cube {
	return &c[len(c)-1]
}

func (c Cover) Back() Cube {
	return c[len(c)-1]
}

func (c *Cover) PushBack(s1 ...Cube) {
	*c = append(*c, s1...)
}

func (c *Cover) PopBack(n int) {
	*c = (*c)[0:len(*c)-n]
}

func (c *Cover) Clear() {
	*c = Cover{}
}

func (c *Cover) Erase(start, end int) {
	if end < 0 {
		end += len(*c)
	}
	if start < 0 {
		start += len(*c)
	}

	if end >= len(*c) {
		*c = (*c)[0:start]
	} else {
		*c = append((*c)[0:start], (*c)[end:]...)
	}
}

func (c *Cover) Cofactor(s1 Cube) *Cover {
	w := 0
	r := 0
	for ; r < len(*c); r++ {
		if len((*c)[w]) < len((*c)[r]) {
			(*c)[w].ExtendX(len((*c)[r]))
		}

		valid := true
		j := 0
		for j = 0; j < len((*c)[r]) && j < len(s1) && valid; j++ {
			b := s1[j] & (*c)[r][j]
			b = ^(b | (b >> 1)) & 0x55555555

			if b != 0 {
				valid = false
			} else {
				a := (s1[j] ^ (s1[j] >> 1)) & 0x55555555
				a = a | (a << 1)
				(*c)[w][j] = (*c)[r][j] | a
			}
		}

		if valid {
			if w != r {
				for ; j < len((*c)[r]); j++ {
					(*c)[w][j] = (*c)[r][j]
				}

				if len((*c)[w]) > len((*c)[r]) {
					(*c)[w].Trunk(len((*c)[r]))
				}
			}

			w++
		}
	}
	return c
}

func (c *Cover) CofactorLiteral(uid, val int) *Cover {
	w := 0
	r := 0
	for ; r < len(*c); r++ {
		cmp := (*c)[r].Get(uid)
		if cmp != 1-val {
			if r != w {
				(*c)[w] = (*c)[r]
			}

			(*c)[w].Set(uid, 2)
			w++
		}
	}

	if w != r {
		(*c) = (*c)[0:w]
	}
	return c
}

// get the supercube of all of the cubes in the cover. This represents the
// bounding box that entirely contains this cover.
func (c Cover) Supercube() Cube {
	result := Cube{}
	if len(c) > 0 {
		result.ExtendN(len(c[0]))

		for i := len(c)-1; i != -1; i-- {
			if len(c[i]) < len(result) {
				result.Trunk(len(c[i]))
			}

			for j := 0; j < len(result); j++ {
				result[j] |= c[i][j]
			}
		}
	} else {
		result = append(result, 0x0000_0000)
	}

	return result
}

type Rank struct {
	Neg int
	Pos int
}

// The variable with the highest binate rank is the one which appears in
// both the positive sense and negative sense, and shows up the most times.
// A variable that only appears in one sense has no binate rank.
// So, for x & y | ~x & ~z, the binate rank of x is 2. Because y and ~z
// only show up for one sense, they have binate ranks of 0.
func (c Cover) BinateRank() []Rank {
	result := []Rank{}
	for _, ci := range c {
		literals := len(ci)*16
		if len(result) < literals {
			result = append(result, make([]Rank, literals-len(result))...)
		}

		for j := 0; j < literals; j++ {
			val := ci.Get(j)
			if val == 0 {
				result[j].Neg++
			} else if val == 1 {
				result[j].Pos++
			}
		}
	}
	return result
}

func Shannon(binateRank []Rank, size int) (int, int) {
	count := -1
	pos := -1
	for i := 0; i < len(binateRank); i++ {
		// Column of all zeros
		if binateRank[i].Neg == size || binateRank[i].Pos == size {
			return -1, -1
		}
	
		rank := binateRank[i].Neg + binateRank[i].Pos
		if rank > count {
			count = rank
			pos = i
		}
	}
	return pos, count
}

// check if this cover covers all cubes
func (c Cover) IsTautology() bool {
	// Cover F is empty or only has one cube
	if len(c) == 0 {
		return false
	}

	// First, determine how many variables are used in this cover
	// Cover F includes the universal cube
	maxWidth := 0
	for _, ci := range c {
		temp := ci.MemoryWidth()
		// if we found a universal cube
		if temp == 0 {
			return true
		}

		if temp > maxWidth {
			maxWidth = temp
		}
	}

	// If there are 8 variables or fewer, then we can just do a brute-force check
	// This will use up to 2^8 or 256 bits, meaning 8x32-bit integers
	if maxWidth <= 8 {
		result := Cube{}
		if maxWidth < 5 {
			result = append(result, 0xFFFFFFFF << (1 << maxWidth))
		} else {
			result.ExtendN(1 << (maxWidth-5))
		}

		for _, ci := range c {
			result.Supercube(ci.GetCover(maxWidth))
		}

		return result.IsTautology()
	}

	// There are too many variables, so we'll use shannon expansion.
	pos, count := Shannon(c.BinateRank(), len(c))

	// Do the shannon expansion, and recurse on the cofactors
	if count > 0 {
		c0 := c.Clone()
		if !c0.CofactorLiteral(pos, 0).IsTautology() {
			return false
		}

		c1 := c.Clone()
		if !c1.CofactorLiteral(pos, 1).IsTautology() {
			return false
		}

		return true
	}

	// Function is unate
	return false
}
