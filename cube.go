package boolean

import (
	//"github.com/nbingham1/iter"
	//"bytes"
	"unsafe"
)

/*

This structure represents a four-valued logic. When it is used to
represent state information the values represent the following:

- (11)	wire is stable at either GND or VDD, but we don't know which
1 (10)	wire is stable at VDD
0 (01)	wire is stable at GND
X (00)	voltage on wire is unstable

When it is used to do boolean logic, the values represent the following:

- (11)  cube covering both 0 and 1
1 (10)  cube covering 1
0 (01)  cube covering 0
X (00)  empty cube

 */
type Cube []uint32

func min(args ...int) int {
	result := 0
	for i, arg := range args {
		if i == 0 || arg < result {
			result = arg
		}
	}
	return result
}

func max(args ...int) int {
	result := 0
	for i, arg := range args {
		if i == 0 || arg > result {
			result = arg
		}
	}
	return result
}

func (c *Cube) Cover() Cover {
	return *(*[]Cube)(unsafe.Pointer(&struct{
		addr uintptr
		len int
		cap int
	}{uintptr(unsafe.Pointer(c)),1,1}))
}

func Covers(s ...Cube) []Cover {
	result := make([]Cover, 0, len(s))
	for _, si := range s {
		result = append(result, si.Cover())
	}
	return result
}

/*

given x & y | ^x & z

variable  - x in both x&y and ^x&z is one variable.
literal   - ^x in ^x&z is one literal and x in x&y is another, both place some
            constraint on the variable x.
sense     - x in x&y is a literal with a positive sense while ^x in ^x&z is a
            literal with a negative sense.
cube      - a set of literals, x&y is one cube, ^x&z is another, they represent
            intersecting constraints on the values of the variables within
cover     - a set of cubes, x&y | ^x&z is a cover, representing the union of the
            constraints specified by the cubes within
null      - the empty set, no satisfying value assignments
tautology - the universal set, all value assignments are satisfying

*/

func NewCube(rsv int) Cube {
	return make(Cube, 0, rsv)
}

// Initialize a cube to either null (0) or tautology (1)
// val = value to set
func NewBool(val int) Cube {
	result := Cube{}
	if val == 0 {
		result = append(result, 0x0000_0000)
	}
	return result
}

// Initialize a cube with a single literal
// uid = variable id
// val = value to set (0 or 1)
func NewLiteral(uid, val int) Cube {
	result := Cube{}
	result.ExtendX(uid/16 + 1)

	w := uid/16
	i := 2*(uid%16)
	v := uint32(val+1) << i
	m := uint32(3) << i

	result[w] = (result[w] & ^m) | (v & m)
	return result
}

func (c Cube) Clone() Cube {
	result := make(Cube, 0, len(c))
	result = append(result, c...)
	return result
}

func (c *Cube) Reserve(num int) {
	tmp := *c
	*c = make(Cube, len(tmp), len(tmp)+num)
	copy(*c, tmp)
}

func (c Cube) BackPtr() *uint32 {
	return &c[len(c)-1]
}

func (c Cube) Back() uint32 {
	return c[len(c)-1]
}

func (c *Cube) PushBack(val ...uint32) {
	*c = append(*c, val...)
}

func (c *Cube) PopBack(n int) {
	*c = (*c)[0:len(*c)-n]
}

// Extends the array with tautologies
// num = the number of integers to add
func (c *Cube) ExtendX(num int) {
	for ; num >= 0; num-- {
		*c = append(*c, 0xFFFF_FFFF)
	}
}

// Extends the array with nulls
// num = the number of integers to add
func (c *Cube) ExtendN(num int) {
	for ; num >= 0; num-- {
		*c = append(*c, 0x0000_0000)
	}
}

// Removes integers from the end of the array
// size = the number of integers to remove
func (c *Cube) Trunk(size int) {
	*c = (*c)[0:size]
}

// Gets the value of a single literal
// uid = variable id
func (c Cube) Get(uid int) int {
	w := uid/16
	if w >= len(c) {
		return 2
	} else {
		return int((c[w] >> (2*(uid%16))) & 3) - 1
	}
}

// Sets the value of a single literal
// uid = variable id
// val = value to set (0, 1, or 2)
func (c *Cube) Set(uid, val int) {
	w	:= uid/16
	if w >= len(*c) {
		c.ExtendX(w+1 - len(*c))
	}

	i := 2*(uid%16)
	v := uint32(val+1) << i
	m := uint32(3) << i
	(*c)[w] = ((*c)[w] & ^m) | (v & m)
}

// Sets the value of a single literal to its union with the value
// uid = variable id
// val = value to union
func (c *Cube) SvUnion(uid, val int) {
	w := uid/16
	if w >= len(*c) {
		c.ExtendX(w+1 - len(*c))
	}
	(*c)[w] |= (uint32(val+1) << (2*(uid%16)))
}

// Sets the value of a single literal to its intersection with the value
// uid = variable id
// val = value to intersect
func (c *Cube) SvIntersect(uid, val int) {
	w := uid/16
	if w >= len(*c) {
		c.ExtendX(w+1 - len(*c))
	}

	i := 2*(uid%16)
	(*c)[w] &= (uint32(val+1) << i) | ^(uint32(3) << i)
}

// Inverts the sense of a single literal
// uid = variable id
func (c *Cube) SvInvert(uid int) {
	w := uid/16
	if w >= len(*c) {
		c.ExtendX(w+1 - len(*c))
	}

	(*c)[w] ^= uint32(3) << (2*(uid%16))
}

// Sets the value of a single literal to its boolean OR with the value
// uid = variable id
// val = value to OR
func (c *Cube) SvOr(uid, val int) {
	w := uid/16
	if w >= len(*c) {
		c.ExtendX(w+1 - len(*c))
	}

	i := 2*(uid%16)
	v := (uint32(val+1) << i) | (uint32(0x5555_5555) & ^(uint32(3) << i))
	(*c)[w] = ((((*c)[w]&(v << 1)) | ((*c)[w]&v) | (v&((*c)[w] << 1))) & 0xAAAA_AAAA) | ((*c)[w] & v & 0x5555_5555)
}

// Sets the value of a single literal to its boolean AND with the value
// uid = variable id
// val = value to AND
func (c *Cube) SvAnd(uid, val int) {
	w := uid/16
	if w >= len(*c) {
		c.ExtendX(w+1 - len(*c))
	}

	i := 2*(uid%16)
	v := (uint32(val+1) << i) | (uint32(0xAAAA_AAAA) & ^(uint32(3) << i))
	(*c)[w] = ((*c)[w] & v & 0xAAAA_AAAA) | ((((*c)[w]&(v >> 1)) | ((*c)[w]&v) | (v&((*c)[w] >> 1))) & 0x5555_5555)
}

// Sets the value of a single literal to its boolean NOT
// uid = variable id
func (c *Cube) SvNot(uid int) {
	w := uid/16
	if w >= len(*c) {
		c.ExtendX(w+1 - len(*c))
	}

	i := 2*(uid%16)
	m0 := (uint32(1) << i)
	m1 := (uint32(2) << i)
	(*c)[w] = ((*c)[w] & ^(m0 | m1)) | ((((*c)[w] & m0) << 1) & 0xFFFF_FFFE) | ((((*c)[w] & m1) >> 1) & 0x7FFF_FFFF)
}

// Returns true if the set of assignments that satisfies this is the same as or
// a subset of that which satisfies the input s
func (c Cube) IsSubsetOf(s Cover) bool {
	if len(s) == 0 {
		return false
	} else if len(s) > 1 {
		co := s.Clone()
		return co.Cofactor(c).IsTautology()
	}

	m0 := min(len(c), len(s[0]))
	i := 0
	for ; i < m0; i++ {
		if (c[i] & s[0][i]) != c[i] {
			return false
		}
	}
	for ; i < len(s[0]); i++ {
		if s[0][i] != 0xFFFF_FFFF {
			return false
		}
	}
	return true
}

// Returns true if the set of assignments that satisfies this is strictly a
// subset of that which satisfies the input cube s
func (c Cube) IsStrictSubsetOf(s Cube) bool {
	m0 := min(len(c), len(s))
	i := 0
	eq := true
	for ; i < m0; i++ {
		eq = eq && (c[i] == s[i])
		if (c[i] & s[i]) != c[i] {
			return false
		}
	}
	for ; i < len(c); i++ {
		eq = eq && (c[i] == 0xFFFF_FFFF)
	}

	return !eq
}

// Returns true if all assignments satisfy this cube
func (c Cube) IsTautology() bool {
	for i := 0; i < len(c); i++ {
		if c[i] != 0xFFFF_FFFF {
			return false
		}
	}

	return true
}

// Returns true if no assignment satisfies this cube
func (c Cube) IsNull() bool {
	for i := 0; i < len(c); i++ {
		if ((c[i]>>1) | c[i] | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}

	return false
}

func (c *Cube) Supercube(s ...Cube) *Cube {
	for _, si := range s {
		if len(si) < len(*c) {
			c.Trunk(len(si))
		}

		for j := 0; j < len(*c); j++ {
			(*c)[j] |= si[j]
		}
	}

	return c
}

// Returns the minimum number of bit pairs required to store this cube
/* TODO optimize using _BuiltinClz() or
int nlz2(x uint32) {
   var y uint32
   var n int

   n = 32
   y = x >>16;  if (y != 0) {n = n -16;  x = y;}
   y = x >> 8;  if (y != 0) {n = n - 8;  x = y;}
   y = x >> 4;  if (y != 0) {n = n - 4;  x = y;}
   y = x >> 2;  if (y != 0) {n = n - 2;  x = y;}
   y = x >> 1;  if (y != 0) return n - 2
   return n - x
}*/
func (c Cube) MemoryWidth() int {
	// This looks ugly, but its just a loop unrolled binary search
	for i := len(c)-1; i != -1; i-- {
		if c[i] != 0xFFFF_FFFF {
			if (c[i] & 0xFFFF0000) != 0xFFFF0000 {
				if (c[i] & 0xFF000000) != 0xFF000000 {
					if (c[i] & 0xF0000000) != 0xF0000000 {
						if (c[i] & 0xC0000000) != 0xC0000000 {
							return i*16 + 16
						} else {
							return i*16 + 15
						}
					} else {
						if (c[i] & 0x0C000000) != 0x0C000000 {
							return i*16 + 14
						} else {
							return i*16 + 13
						}
					}
				} else {
					if (c[i] & 0x00F00000) != 0x00F00000 {
						if (c[i] & 0x00C00000) != 0x00C00000 {
							return i*16 + 12
						} else {
							return i*16 + 11
						}
					} else {
						if (c[i] & 0x000C0000) != 0x000C0000 {
							return i*16 + 10
						} else {
							return i*16 + 9
						}
					}
				}
			} else {
				if (c[i] & 0x0000FF00) != 0x0000FF00 {
					if (c[i] & 0x0000F000) != 0x0000F000 {
						if (c[i] & 0x0000C000) != 0x0000C000 {
							return i*16 + 8
						} else {
							return i*16 + 7
						}
					} else {
						if (c[i] & 0x00000C00) != 0x00000C00 {
							return i*16 + 6
						} else {
							return i*16 + 5
						}
					}
				} else {
					if (c[i] & 0x000000F0) != 0x000000F0 {
						if (c[i] & 0x000000C0) != 0x000000C0 {
							return i*16 + 4
						} else {
							return i*16 + 3
						}
					} else {
						if (c[i] & 0x0000000C) != 0x0000000C {
							return i*16 + 2
						} else {
							return i*16 + 1
						}
					}
				}
			}
		}
	}

	return 0
}

// Returns a bit vector such that each bit represents whether a particular
// assignment of all literals with ids in [0,n) is covered by this cube. For
// example, consider the cube a & ~b. We will call this function with n=3 and
// get a result "r"
// a  b  c | r
// -----------
// 0  0  0 | 0 <-- bit 0 of r
// 0  0  1 | 0
// 0  1  0 | 0
// 0  1  1 | 0
// 1  0  0 | 1
// 1  0  1 | 1
// 1  1  0 | 0
// 1  1  1 | 0 <-- bit 7 of r
// 
// This can be used to determine whether a set of cubes taken together covers
// every assignment and is therefore a tautology. Ultimately, this is the
// brute-force approach. The memory required by this approach grows
// exponentially and therefore should be used sparingly with careful
// consideration to n. More specifically, memoryWidth() should be used to
// determine n you should verify that it is small enough for your application.
func (c Cube) GetCover(n int) Cube {
	if len(c) == 0 {
		return Cube{}
	}

	v1 := uint32(1)
	v2 := uint32(0)
	mask := uint32(1)

	i := 0
	for ; i < 5 && i < n; i++ {
		v2 = 0

		if (mask & c[0]) != 0 {
			v2 |= v1
		}

		mask <<= 1

		if (mask & c[0]) != 0 {
			v2 |= (v1 << (mask >> (i+1)))
		}

		mask <<= 1

		v1 = v2
	}

	s := 1 << max((n - 5), 0)

	c1 := Cube{}
	c1.ExtendN(s)
	c1[0] = v1

	if n <= 5 {
		return c1
	}

	c2 := Cube{}
	c2.ExtendN(s)
	maskIdx := 0
	total := 0

	for ; i < n; i++ {
		x := int(mask >> i)/32
		total += x

		if len(c) <= maskIdx || (mask & c[maskIdx]) != 0 {
			for k := total; k != -1; k-- {
				c2[k] |= c1[k]
			}
		}

		mask <<= 1

		if len(c) <= maskIdx || (mask & c[maskIdx]) != 0 {
			for k := total; k != -1 && k >= x; k-- {
				c2[k] |= c1[k-x]
			}
		}

		mask <<= 1

		if mask == 0 {
			maskIdx++
			mask = 1
		}

		c1 = c2

		for k := 0; k <= total; k++ {
			c2[k] = 0
		}
	}

	return c1
}

// Returns the number of literals in this cube
func (c Cube) Width() int {
	result := 0
	for i := 0; i < len(c); i++ {
		if c[i] != 0xFFFF_FFFF {
			x := c[i] & (c[i] >> 1) & 0x5555_5555
			x = (x & 0x3333_3333) + ((x >> 2) & 0x3333_3333)
			x = (x + (x >> 4)) & 0x0F0F_0F0F
			x += (x >> 8)
			x += (x >> 16)
			result += int(16 - (x & 0x0000_003F))
		}
	}

	return result
}

// Removes null literals from this cube
func (c *Cube) Xoutnulls() *Cube {
	for i := 0; i < len(*c); i++ {
		a := ^(*c)[i] & (^(*c)[i] >> 1) & 0x5555_5555
		(*c)[i] |= (a | (a << 1))
	}
	return c
}

