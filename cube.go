package boolean

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
type Cube struct {
	Values []uint32
}

/*

given x & y | ~x & z

variable  - x in both x&y and ~x&z is one variable.
literal   - ~x in ~x&z is one literal and x in x&y is another, both place some
            constraint on the variable x.
sense     - x in x&y is a literal with a positive sense while ~x in ~x&z is a
            literal with a negative sense.
cube      - a set of literals, x&y is one cube, ~x&z is another, they represent
            intersecting constraints on the values of the variables within
cover     - a set of cubes, x&y | ~x&z is a cover, representing the union of the
            constraints specified by the cubes within
null      - the empty set, no satisfying value assignments
tautology - the universal set, all value assignments are satisfying

*/

func NewCube(rsv int) Cube {
	return Cube{
		Values: make([]uint32, 0, rsv),
	}
}

// Initialize a cube to either null (0) or tautology (1)
// val = value to set
func NewCubeBool(val int) Cube {
	result := Cube{
		Values: []uint32{},
	}
	if val == 0 {
		result.Values = append(result.Values, 0x0000_0000)
	}
	return result
}

// Initialize a cube with a single literal
// uid = variable id
// val = value to set (0 or 1)
func NewCubeLiteral(uid, val int) Cube {
	result := Cube{
		Values: []uint32{},
	}
	result.ExtendX(uid/16 + 1)

	w := uid/16
	i := 2*(uid%16)
	v := uint32(val+1) << i
	m := uint32(3) << i

	result.Values[w] = (result.Values[w] & ~m) | (v & m)
	return result
}

func (c *Cube) Clone() Cube {
	return Cube{
		Values: append(make([]uint32, 0, len(c.Values)), c.Values...),
	}
}

func (c *Cube) Reserve(num int) {
	tmp := c.Values
	c.Values = make(c.Values, len(tmp), len(tmp)+num)
	copy(c.Values, tmp)
}

func (c *Cube) BackPtr() *uint32 {
	return &c.Values[len(c.Values)-1]
}

func (c *Cube) Back() uint32 {
	return c.Values[len(c.Values)-1]
}

func (c *Cube) PushBack(val ...uint32) {
	c.Values = append(c.Values, val...)
}

func (c *Cube) PopBack(n int) {
	c.Values = c.Values[0:len(c.Values)-n]
}

// Returns the number of integers used in the interal representation
func (c *Cube) Size() int {
	return len(c.Values)
}

// Extends the array with tautologies
// num = the number of integers to add
func (c *Cube) ExtendX(num int) {
	for ; num >= 0; num-- {
		c.Values = append(c.Values, 0xFFFF_FFFF)
	}
}

// Extends the array with nulls
// num = the number of integers to add
func (c *Cube) ExtendN(num int) {
	for ; num >= 0; num-- {
		c.Values = append(c.Values, 0x0000_0000)
	}
}

// Removes integers from the end of the array
// size = the number of integers to remove
func (c *Cube) Trunk(size int) {
	c.Values = c.Values[0:size]
}

// Gets the value of a single literal
// uid = variable id
func (c *Cube) Get(uid int) int {
	w := uid/16
	if w >= c.Size() {
		return 2
	} else {
		return ((c.Values[w] >> (2*(uid%16))) & 3) - 1
	}
}

// Sets the value of a single literal
// uid = variable id
// val = value to set (0, 1, or 2)
func (c *Cube) Set(uid, val int) {
	w	:= uid/16
	if w >= c.Size() {
		c.ExtendX(w+1 - c.Size())
	}

	i := 2*(uid%16)
	v := uint32(val+1) << i
	m := uint32(3) << i
	c.Values[w] = (c.Values[w] & ~m) | (v & m)
}

// Sets the value of a single literal to its union with the value
// uid = variable id
// val = value to union
func (c *Cube) SvUnion(uid, val int) {
	w := uid/16
	if w >= c.Size() {
		c.ExtendX(w+1 - c.Size())
	}
	c.Values[w] |= ((val+1) << (2*(uid%16)))
}

// Sets the value of a single literal to its intersection with the value
// uid = variable id
// val = value to intersect
func (c *Cube) SvIntersect(uid, val int) {
	w := uid/16
	if w >= c.Size() {
		c.ExtendX(w+1 - c.Size())
	}

	i := 2*(uid%16)
	c.Values[w] &= (uint(val+1) << i) | ~(uint(3) << i)
}

// Inverts the sense of a single literal
// uid = variable id
func (c *Cube) SvInvert(uid int) {
	w := uid/16
	if w >= c.Size() {
		c.ExtendX(w+1 - c.Size())
	}

	c.Values[w] ^= uint(3) << (2*(uid%16))
}

// Sets the value of a single literal to its boolean OR with the value
// uid = variable id
// val = value to OR
func (c *Cube) SvOr(uid, val int) {
	w := uid/16
	if w >= c.Size() {
		c.ExtendX(w+1 - c.Size())
	}

	i := 2*(uid%16)
	v := ((val+1) << i) | (0x5555_5555 & ~(3 << i))
	c.Values[w] = (((c.Values[w]&(v << 1)) | (c.Values[w]&v) | (v&(c.Values[w] << 1))) & 0xAAAA_AAAA) | (c.Values[w] & v & 0x5555_5555)
}

// Sets the value of a single literal to its boolean AND with the value
// uid = variable id
// val = value to AND
func (c *Cube) SvAnd(uid, val int) {
	w := uid/16
	if w >= c.Size() {
		c.ExtendX(w+1 - c.Size())
	}

	i := 2*(uid%16)
	v := (uint(val+1) << i) | (uint(0xAAAA_AAAA) & ~(uint(3) << i))
	c.Values[w] = (c.Values[w] & v & 0xAAAA_AAAA) | (((c.Values[w]&(v >> 1)) | (c.Values[w]&v) | (v&(c.Values[w] >> 1))) & 0x5555_5555)
}

// Sets the value of a single literal to its boolean NOT
// uid = variable id
func (c *Cube) SvNot(uid int) {
	w := uid/16
	if w >= c.Size() {
		c.ExtendX(w+1 - c.Size())
	}

	i := 2*(uid%16)
	m0 := (uint32(1) << i)
	m1 := (uint32(2) << i)
	c.Values[w] = (c.Values[w] & ~(m0 | m1)) | (((c.Values[w] & m0) << 1) & 0xFFFFFFFE) | (((c.Values[w] & m1) >> 1) & 0x7FFFFFFF)
}

// Returns true if the set of assignments that satisfies this is the same as or
// a subset of that which satisfies the input cube s
func (c *Cube) IsSubsetOf(s Cube) bool {
	m0 := min(size(), s.Size())
	i := 0
	for ; i < m0; i++ {
		if (c.Values[i] & s.Values[i]) != values[i] {
			return false
		}
	}
	for ; i < s.Size(); i++ {
		if s.Values[i] != 0xFFFF_FFFF {
			return false
		}
	}
	return true
}

// Returns true if the set of assignments that satisfies this is the same as or
// a subset of that which satisfies the input cover s
func (c *Cube) IsSubsetOfCover(s Cover) bool {
	return Cofactor(s, *c).IsTautology()
}

// Returns true if the set of assignments that satisfies this is strictly a
// subset of that which satisfies the input cube s
func (c *Cube) IsStrictSubsetOf(s Cube) bool {
	m0 := min(size(), s.Size())
	i := 0
	eq := true
	for ; i < m0; i++ {
		eq = eq && (c.Values[i] == s.Values[i])
		if (c.Values[i] & s.Values[i]) != values[i] {
			return false
		}
	}
	for ; i < c.Size(); i++ {
		eq = eq && (c.Values[i] == 0xFFFF_FFFF)
	}

	return !eq
}

// Returns true if all assignments satisfy this cube
func (c *Cube) IsTautology() bool {
	for i := 0; i < c.Size(); i++ {
		if c.Values[i] != 0xFFFF_FFFF {
			return false
		}
	}

	return true
}

// Returns true if no assignment satisfies this cube
func (c *Cube) IsNull() bool {
	for i := 0; i < c.Size(); i++ {
		if ((c.Values[i]>>1) | values[i] | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}

	return false
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
func (c *Cube) MemoryWidth() int {
	// This looks ugly, but its just a loop unrolled binary search
	for i := c.Size()-1; i != -1; i-- {
		if c.Values[i] != 0xFFFF_FFFF {
			if (c.Values[i] & 0xFFFF0000) != 0xFFFF0000 {
				if (c.Values[i] & 0xFF000000) != 0xFF000000 {
					if (c.Values[i] & 0xF0000000) != 0xF0000000 {
						if (c.Values[i] & 0xC0000000) != 0xC0000000 {
							return i*16 + 16
						} else {
							return i*16 + 15
						}
					} else {
						if (c.Values[i] & 0x0C000000) != 0x0C000000 {
							return i*16 + 14
						} else {
							return i*16 + 13
						}
					}
				} else {
					if (c.Values[i] & 0x00F00000) != 0x00F00000 {
						if (c.Values[i] & 0x00C00000) != 0x00C00000 {
							return i*16 + 12
						} else {
							return i*16 + 11
						}
					} else {
						if (c.Values[i] & 0x000C0000) != 0x000C0000 {
							return i*16 + 10
						} else {
							return i*16 + 9
						}
					}
				}
			} else {
				if (c.Values[i] & 0x0000FF00) != 0x0000FF00 {
					if (c.Values[i] & 0x0000F000) != 0x0000F000 {
						if (c.Values[i] & 0x0000C000) != 0x0000C000 {
							return i*16 + 8
						} else {
							return i*16 + 7
						}
					} else {
						if (c.Values[i] & 0x00000C00) != 0x00000C00 {
							return i*16 + 6
						} else {
							return i*16 + 5
						}
					}
				} else {
					if (c.Values[i] & 0x000000F0) != 0x000000F0 {
						if (c.Values[i] & 0x000000C0) != 0x000000C0 {
							return i*16 + 4
						} else {
							return i*16 + 3
						}
					} else {
						if (c.Values[i] & 0x0000000C) != 0x0000000C {
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

// Returns the number of literals in this cube
func (c *Cube) Width() int {
	result := 0
	for i := 0; i < c.Size(); i++ {
		if c.Values[i] != 0xFFFF_FFFF {
			x := c.Values[i] & (c.Values[i] >> 1) & 0x5555_5555
			x = (x & 0x33333333) + ((x >> 2) & 0x33333333)
			x = (x + (x >> 4)) & 0x0F0F0F0F
			x += (x >> 8)
			x += (x >> 16)
			result += (16 - (x & 0x0000003F))
		}
	}

	return result
}

// Removes null literals from this cube
func (c *Cube) Xoutnulls() Cube {
	result := c.Clone()
	for i := 0; i < result.Size(); i++ {
		a := ~result.Values[i] & (~result.Values[i] >> 1) & 0x5555_5555
		result.Values[i] |= (a | (a << 1))
	}
	return result
}

/* MASKS
A mask is stored in a cube and is applied using a modified supercube operation.
literals that are masked out are represented with tautology (11)
literals that aren't are represented by null (00)
Typically, a mask will only filter a few specific literals while a flipped mask
will filter out everything *but* a few specific literals.
*/

// creates a mask of this cube such that the literals in this cube would be
// masked out. For example, the mask of a cube x & ~y would hide any x or y
// literals when applied to another cube.
func (c *Cube) Mask() Cube {
	result := c.Clone()
	for i := 0; i < result.Size(); i++ {
		x := ((result.Values[i] >> 1) ^ result.Values[i]) & 0x5555_5555
		result.Values[i] = x | (x << 1)
	}
	return result
}

// hides all literals not equal to v. For example, if v is 1
// then the cube "x & ~y" would would be masked to "x".
func (c *Cube) ApplyMaskBool(v int) Cube {
	v = v+1
	v |= v << 2
	v |= v << 4
	v |= v << 8
	v |= v << 16

	result := Cube{
		Values: make([]uint32, len(c.Values)),
	}
	for i := 0; i < len(c.Values); i++ {
		result.Values[i] = c.Values[i] | v
	}
	return result
}

// apply a mask to this cube
func (c *Cube) ApplyMask(s Cube) Cube {
	result := c.Clone()
	if (s.Values.Size() < result.Values.Size()) {
		s.ExtendN(result.Size()-s.Size())
	}
	result.Supercube(s)
	return result
}

// apply a flipped mask to this cube
func (c *Cube) FlippedMask(s Cube) Cube {
	result := c.Clone()
	result.Supercube(s)
	return result
}

// combine two masks
func (c *Cube) CombineMask(s Cube) Cube {
	result := c.Clone()
	if (s.Size() > result.Size()) {
		result.ExtendN(s.Size()-result.Size())
	}
	if (s.Size() < result.Size()) {
		s.ExtendN(result.Size()-s.Size())
	}
	result.Supercube(s)
	return result
}

// invert all literals in this cube so x & ~y becomes ~x & y
func (c *Cube) Inverse() Cube {
	result := c.Clone()
	for i := 0; i < result.Size(); i++ {
		result.Values[i] = ((result.Values[i] << 1) & 0xAAAA_AAAA) | ((result.Values[i] >> 1) & 0x5555_5555)
	}
	return result
}

// invert the set of satisfying assignments for each literal in this cube
func (c *Cube) Flip() Cube {
	result := c.Clone()
	for i := 0; i < result.Size(); i++ {
		result.Values[i] = ~result.Values[i]
	}
	return result
}

/*
// hide all literals in this that conflict with literals in c. Literals in c
// that aren't in this are simply ignored.
func (c *Cube) Deconflict(cube c) const cube {
	cube result(*this)
	for i := 0; i < result.Size() && i < c.Size(); i++ {
	{
		// m is 1 where the literals in this are tautology (11) or null (00)
		m := ((result.Values[i] >> 1) ^ result.Values[i]) & 0x5555_5555
		m = ~(m | (m << 1))

		// m is 1 where this and c disagree (this & c == null)
		result.Values[i] &= c.Values[i] | m
		m = (result.Values[i] | (result.Values[i] >> 1)) & 0x5555_5555
		m = ~(m | (m << 1))

		// hide those literals
		result.Values[i] |= m
	}
	return result
}
*/

/* ISOCHRONIC REGIONS
In a circuit, a variable is represented by a wire. A wire by definition has at
least two endpoints, the driver and the load, though it can have any number of
loading endpoints. If there are 2 or more endpoints, then there must be a fork
somewhere in the wire. If the fork is isochronic, then updating one side of the
fork immediately updates the other side and they can be treated as a single
variable. However, if the fork is non-isochronic, then it is said that the two
loading endpoints are in different "isochronic regions" and they must be
treated as separate variables. A variable in a "remote region" will have the
same name, a different region id, and a different variable id in the cube. Each
group in the groups vector represents all the different isochronic regions of a
single wire.
*/

// This function resolves the values of all endpoints of a variable,
// intersecting their sets of satsifying assignments and copying the resulting
// value to all endpoints.
func (c *Cube) Remote(groups [][]int) Cube {
	result := c.Clone()
	for i := 0; i < len(groups); i++ {
		value := result.Get(groups[i][0])+1
		for j := 1; j < len(groups[i]); j++ {
			value &= result.Get(groups[i][j])+1
		}

		for j := 0; j < len(groups[i]); j++ {
			result.Set(groups[i][j], value-1)
		}
	}

	return result
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
func (c *Cube) GetCover(n int) Cube {
	if c.Size() == 0 {
		return Cube{}
	}

	v1 := uint32(1)
	v2 := uint32(0)
	mask := uint32(1)

	i := 0
	for ; i < 5 && i < n; i++ {
		v2 = 0

		if (mask & c.Values[0]) != 0 {
			v2 |= v1
		}

		mask <<= 1

		if (mask & c.Values[0]) != 0 {
			v2 |= (v1 << (mask >> (i+1)))
		}

		mask <<= 1

		v1 = v2
	}

	s := 1 << max((n - 5), 0)

	c1 := Cube{}
	c1.ExtendN(s)
	c1.Values[0] = v1

	if n <= 5 {
		return c1
	}

	c2 := Cube{}
	c2.ExtendN(s)
	maskIdx := 0
	total := 0

	for ; i < n; i++ {
		x := (mask >> i)/32
		total += x

		if c.Size() <= maskIdx || (mask & c.Values[maskIdx]) != 0 {
			for k := total; k != -1; k-- {
				c2.Values[k] |= c1.Values[k]
			}
		}

		mask <<= 1

		if c.Size() <= maskIdx || (mask & c.Values[maskIdx]) != 0 {
			for k := total; k != -1 && k >= x; k-- {
				c2.Values[k] |= c1.Values[k-x]
			}
		}

		mask <<= 1

		if mask == 0 {
			maskIdx++
			mask = 1
		}

		c1 = c2

		for k := 0; k <= total; k++ {
			c2.Values[k] = 0
		}
	}

	return c1
}

// Returns a cover such that each variable in uids is shannon expanded into its
// positive and negative sense. For example, given a cube a&~b and uid c, the
// resulting cover will be a&~b&~c | a&~b&c
func (c *Cube) Expand(uids []int) Cover {
	r1 := NewTerm(c)
	for i := 0; i < len(uids); i++ {
		for j := r1.Size()-1; j >= 0 && j < r1.Size(); j-- {
			if r1[j].Get(uids[i]) == 2 {
				r1.PushBack(r1[j] & NewCubeLiteral(uids[i], 0))
				r1[j] &= NewCubeLiteral(uids[i], 1)
			}
		}
	}
	return r1
}

// return the ids of all literals in this cube
func (c *Cube) Vars() []int {
	result := []int{}
	for i := 0; i < c.Size()*16; i++ {
		if c.Get(i) != 2 {
			result.PushBack(i)
		}
	}
	return result
}

// return the ids of all literals in this cube
func (c *Cube) VarsInPlace(result *[]int) {
	for i := 0; i < c.Size()*16; i++ {
		if c.Get(i) != 2 {
			*result = append(*result, i)
		}
	}
}

// reassign the variable ids based upon the input map
func (c *Cube) Refactor(uids map[int]int) Cube {
	result := Cube{}
	for first, second := range uids {
		result.Set(second, c.Get(first))
	}
	return result
}

// take the intersection of the sets of satisfying assignments of the two cubes
// For two cubes A, B, this ultimately implements A & B
func (c *Cube) IntersectBool(val int) *Cube {
	if val == 0 {
		for i := 0; i < c.Size(); i++ {
			c.Values[i] = 0x0000_0000
		}
	}

	return c
}

func (c *Cube) Intersect(s1 Cube) *Cube {
	if c.Size() < s1.Size() {
		c.ExtendX(s1.Size() - c.Size())
	}

	for i := 0; i < s1.Size(); i++ {
		c.Values[i] &= s1.Values[i]
	}

	return c
}

func (c *Cube) Intersect3(s1, s2 Cube) *Cube {
	m12 := min(s1.Size(), s2.Size())
	maxSize := max(s1.Size(), s2.Size())

	if c.Size() < maxSize {
		c.ExtendX(maxSize - c.Size())
	}

	i := 0
	for ; i < m12; i++ {
		c.Values[i] &= s1.Values[i] & s2.Values[i]
	}
	for ; i < s1.Size(); i++ {
		c.Values[i] &= s1.Values[i]
	}
	for ; i < s2.Size(); i++ {
		c.Values[i] &= s2.Values[i]
	}

	return c
}

func (c *Cube) Intersect4(s1, s2, s3 Cube) *Cube {
	m12 := min(s1.Size(), s2.Size())
	m23 := min(s2.Size(), s3.Size())
	m13 := min(s1.Size(), s3.Size())
	m123 := min(m12, s3.Size())
	maxSize := max(s1.Size(), max(s2.Size(), s3.Size()))

	if c.Size() < maxSize {
		c.ExtendX(maxSize - c.Size())
	}

	i := 0
	for ; i < m123; i++ {
		c.Values[i] &= s1.Values[i] & s2.Values[i] & s3.Values[i]
	}
	for ; i < m12; i++ {
		c.Values[i] &= s1.Values[i] & s2.Values[i]
	}
	for ; i < m23; i++ {
		c.Values[i] &= s2.Values[i] & s3.Values[i]
	}
	for ; i < m13; i++ {
		c.Values[i] &= s1.Values[i] & s3.Values[i]
	}
	for ; i < s1.Size(); i++ {
		c.Values[i] &= s1.Values[i]
	}
	for ; i < s2.Size(); i++ {
		c.Values[i] &= s2.Values[i]
	}
	for ; i < s3.Size(); i++ {
		c.Values[i] &= s3.Values[i]
	}
}

func (c *Cube) IntersectCover(s1 Cover) {
	for i := 0; i < s1.Size(); i++ {
		if s1[i].Size() > c.Size() {
			c.ExtendX(s1[i].Size() - c.Size())
		}

		for j := 0; j < s1[i].Size(); j++ {
			c.Values[j] &= s1[i].Values[j]
		}
	}

	return c
}

// take the union of the sets of satisfying assignments of the two cubes
func (c *Cube) SupercubeBool(val int) *Cube {
	if val == 1 {
		c.Values = []uint32{}
	}
	return c
}

func (c *Cube) Supercube(s1 Cube) *Cube {
	if c.Size() > s1.Size() {
		c.Trunk(s1.Size())
	}

	for i := 0; i < c.Size(); i++ {
		c.Values[i] |= s1.Values[i]
	}

	return c
}

func (c *Cube) Supercube3(s1, s2 Cube) *Cube {
	minSize := min(s1.Size(), s2.Size())
	if c.Size() > minSize {
		c.Trunk(minSize)
	}

	for i := 0; i < c.Size(); i++ {
		c.Values[i] |= s1.Values[i] | s2.Values[i]
	}

	return c
}

func (c *Cube) Supercube4(s1, s2, s3 Cube) *Cube {
	minSize := min(s1.Size(), min(s2.Size(), s3.Size()))
	if c.Size() > minSize {
		c.Trunk(minSize)
	}

	for i := 0; i < c.Size(); i++ {
		c.Values[i] |= s1.Values[i] | s2.Values[i] | s3.Values[i]
	}

	return c
}

func (c *Cube) SupercubeCover(s1 Cover) *Cube {
	for i := 0; i < s1.Size(); i++ {
		if s1[i].Size() < c.Size() {
			c.Trunk(s1[i].Size())
		}

		for j := 0; j < c.Size(); j++ {
			c.Values[j] |= s1[i].Values[j]
		}
	}

	return c
}

// remove the given literal from the cube
func (c *Cube) Hide(uid int) {
	c.Set(uid, 2)
}

// remove the listed literals from the cube
// this could also be done with a mask
func (c *Cube) HideMany(uids []int) {
	for _, uid := range uids {
		c.Set(uid, 2)
	}
}

// Returns the boolean cofactor of this cube. For use in algorithms that
// require shannon expansion. If the input value of the literal is not covered
// by this cube, then this cube is set to the null cube at the given uid.
// Otherwise, that literal is hidden.
func (c *Cube) Cofactor(uid, val int) {
	cmp := c.Get(uid)
	if cmp == 1-val {
		c.Set(uid, -1)
	} else {
		c.Set(uid, 2)
	}
}

// Returns the multivariate boolean cofactor of this cube.
func (c *Cube) CofactorCube(s1 Cube) {
	if c.Size() < s1.Size() {
		c.ExtendX(s1.Size() - c.Size())
	}

	for i := 0; i < s1.Size(); i++ {
		a := (s1.Values[i] ^ (s1.Values[i] >> 1)) & 0x5555_5555
		a = a | (a << 1)
		b := s1.Values[i] & values[i]
		b = (b | (b >> 1)) & 0x5555_5555
		b = b | (b << 1)
		c.Values[i] = (c.Values[i] | a) & b
	}
}

// assignment
func (c *Cube) Assign(val int) {
	c.Values.Clear()
	if val == 0 {
		c.Values.PushBack(0x0000_0000)
	}
}

// This implements a type of assignment. All of the literals in s (that aren't
// a tautology) are copied over. All of the literals not in s (that are a
// tautology) are left unchanged.
func (c *Cube) Stencil(s Cube) *Cube {
	if c.Size() < s.Size() {
		c.ExtendX(s.Size() - c.Size())
	}

	for i := 0; i < s.Size(); i++ {
		v := s.Values[i] & (s.Values[i] >> 1) & 0x5555_5555
		v = v | (v<<1)
		c.Values[i] = ((c.Values[i] & v) | (s.Values[i] & ~v))
	}
	return *c
}

// Compute a hash of this structure so that it can be used as a key in a
// hashmap.
func (c *Cube) Marshal(buff *bytes.Buffer) error {
	err = binary.Write(buff, binary.LittleEndian, int32(len(c.Values)))
	if err != nil {
		return err
	}
	 
	for _, value := range c.Values {
		err = binary.Write(buff, binary.LittleEndian, value)
		if err != nil {
			return err
		}
	}
	return nil
}

// Print a raw but human readable representation of this cube to the stream.
func (m *Cube) Debug() string {
	c := []string{"X", "0", "1", "-"}
	result := "["
	for i := 0; i < m.Size()*16; i++ {
		result += c[m.Get(i)+1]
	}
	result += "]"
	return result
}

// Returns the boolean inverse of this cube
func Not(s1 Cube) Cover {
	result := Cover{}
	for i := 0; i < s1.Size(); i++ {
		for j := 0; j < 16; j++ {
			val := s1.Values[i] & 3
			if val == 1 || val == 2 {
				result.PushBack(cube(i*16 + j, 2-val))
			}
			s1.Values[i] >>= 2
		}
	}

	return result
}

// Intersection of two cubes (see cube::intersect())
func IntersectBool(s1 Cube, s2 int) Cube {
	if s2 == 0 {
		return NewCubeBool(0)
	}
	return s1
}

func Intersect(s1, s2 Cube) Cube {
	result := Cube{
		Values: make([]uint32, max(s1.Size(), s2.Size())),
	}

	m12 := min(s1.Size(), s2.Size())

	i := 0
	for ; i < m12; i++ {
		result.Values[i] = s1.Values[i] & s2.Values[i]
	}
	for ; i < s1.Size(); i++ {
		result.Values[i] = s1.Values[i]
	}
	for ; i < s2.Size(); i++ {
		result.Values[i] = s2.Values[i]
	}

	return result
}

func Intersect3(s1, s2, s3 Cube) Cube {
	result := Cube{
		Values: make([]uint32, max(s1.Size(), s2.Size(), s3.Size())),
	}

	m12 := min(s1.Size(), s2.Size())
	m23 := min(s2.Size(), s3.Size())
	m13 := min(s1.Size(), s3.Size())
	m123 := min(m12, s3.Size())

	i := 0
	for ; i < m123; i++ {
		result.Value[i] = s1.Values[i] & s2.Values[i] & s3.Values[i]
	}
	for ; i < m12; i++ {
		result.Value[i] = s1.Values[i] & s2.Values[i]
	}
	for ; i < m23; i++ {
		result.Value[i] = s2.Values[i] & s3.Values[i]
	}
	for ; i < m13; i++ {
		result.Value[i] = s1.Values[i] & s3.Values[i]
	}
	for ; i < s1.Size(); i++ {
		result.Value[i] = s1.Values[i]
	}
	for ; i < s2.Size(); i++ {
		result.Value[i] = s2.Values[i]
	}
	for ; i < s3.Size(); i++ {
		result.Value[i] = s3.Values[i]
	}
	return result
}

// Check whether the two cubes cover mutually exclusive sets of assignments,
// fast implementation of s1&s2==null
func AreMutex(s1, s2 Cube) bool {
	m12 := min(s1.Size(), s2.Size())
	for i := 0; i < m12; i++ {
		v := s1.Values[i] & s2.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	return false
}

func AreMutex3(s1, s2, s3 Cube) bool {
	m12 := min(s1.Size(), s2.Size())
	m23 := min(s2.Size(), s3.Size())
	m13 := min(s1.Size(), s3.Size())
	m123 := min(m12, s3.Size())

	i := 0
	for ; i < m123; i++ {
		v := s1.Values[i] & s2.Values[i] & s3.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m12; i++ {
		v := s1.Values[i] & s2.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m23; i++ {
		v := s2.Values[i] & s3.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m13; i++ {
		v := s1.Values[i] & s3.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}

	return false
}

func AreMutex4(s1, s2, s3, s4 Cube) bool {
	m12 := min(s1.Size(), s2.Size())
	m13 := min(s1.Size(), s3.Size())
	m14 := min(s1.Size(), s4.Size())
	m23 := min(s2.Size(), s3.Size())
	m24 := min(s2.Size(), s4.Size())
	m34 := min(s3.Size(), s4.Size())
	m123 := min(m12, s3.Size())
	m124 := min(m12, s4.Size())
	m134 := min(s1.Size(), m34)
	m234 := min(s2.Size(), m34)
	m1234 := min(m12, m34)

	i := 0
	for ; i < m1234; i++ {
		v := s1.Values[i] & s2.Values[i] & s3.Values[i] & s4.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m123; i++ {
		v := s1.Values[i] & s2.Values[i] & s3.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m124; i++ {
		v := s1.Values[i] & s2.Values[i] & s4.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m134; i++ {
		v := s1.Values[i] & s3.Values[i] & s4.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m234; i++ {
		v := s2.Values[i] & s3.Values[i] & s4.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m12; i++ {
		v := s1.Values[i] & s2.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m13; i++ {
		v := s1.Values[i] & s3.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m14; i++ {
		v := s1.Values[i] & s4.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m23; i++ {
		v := s2.Values[i] & s3.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m24; i++ {
		v := s2.Values[i] & s4.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < m34; i++ {
		v := s3.Values[i] & s4.Values[i]
		if ((v>>1) | v | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return true
		}
	}

	return false
}

func AreMutexCover(s1 Cube, s2 Cover) bool {
	for i := 0; i < s2.Size(); i++ {
		if !AreMutex(s1, s2[i]) {
			return false
		}
	}

	return true
}

func Or(s1, s2 Cube) Cover {
	return Cover{
		Terms: []Cube{s1, s2},
	}
}

func OrBool(s1 Cube, s2 int) Cover {
	if s2 == 0 {
		return NewTerm(s1)
	}
	return NewCover(1)
}

// Returns the supercube (see cube::supercube())
func Supercube(s1, s2 Cube) Cube {
	result := Cube{
		Values: make([]uint32, min(s1.Size(), s2.Size())),
	}

	for i := 0; i < result.Size(); i++ {
		if ((s1.Values[i]>>1) | s1.Values[i] | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return s2
		} else if ((s2.Values[i]>>1) | s2.Values[i] | 0xAAAA_AAAA) != 0xFFFF_FFFF {
			return s1
		}
		result.Values[i] = s1.Values[i] | s2.Values[i]
	}

	return result
}

func Supercube3(s1, s2, s3 Cube) Cube {
	if s1.IsNull() {
		return Supercube(s2, s3)
	}
	if s2.IsNull() {
		return Supercube(s1, s3)
	}
	if s3.IsNull() {
		return Supercube(s1, s2)
	}
	result := Cube{
		make([]uint32, min(s1.Size(), s2.Size(), s3.Size())),
	}

	for i := 0; i < result.Size(); i++ {
		result.Values[i] = s1.Values[i] | s2.Values[i] | s3.Values[i]
	}

	return result
}

func Supercube4(s1, s2, s3, s4 Cube) Cube {
	if s1.IsNull() {
		return Supercube(s2, s3, s4)
	}
	if s2.IsNull() {
		return Supercube(s1, s3, s4)
	}
	if s3.IsNull() {
		return Supercube(s1, s2, s4)
	}
	if s4.IsNull() {
		return Supercube(s1, s2, s3)
	}
	result := Cube{
		make([]uint32, min(s1.Size(), s2.Size(), s3.Size(), s4.Size())),
	}

	for i := 0; i < result.Size(); i++ {
		result.Values[i] = s1.Values[i] | s2.Values[i] | s3.Values[i] | s4.Values[i]
	}

	return result
}

// Hide literals on which s1 and s2 disagree (in which the intersection is null)
// For example the basic consensus of "x&~y&~z" and "x&y&z" is "x" and y and z
// are hidden This can be used to merge two cubes together in the minimize or
// espresso algorithms as long as there is at most one literal in disagreement
func BasicConsensus(s1, s2 Cube) Cube {
	if s1.Size() < s2.Size() {
		s1.ExtendX(s2.Size() - s1.Size())
	}

	for i := 0; i < s2.Size(); i++ {
		// "a" will have a 1 where s1i & s2i == null (00)
		// apply before set operator of s1i & s2i
		s1.Values[i] &= s2.Values[i]
		a := ~(s1.Values[i] | (s1.Values[i] >> 1)) & 0x5555_5555
		// apply active set operator of s1i | s2i
		s1.Values[i] |= (a | (a << 1))
	}

	return s1
}

// Same as basicConsensus(), however if there is more than one literal in
// disagreement, then the null cube is returned.
func Consensus(s1, s2 Cube) Cube {
	if s1.Size() < s2.Size() {
		s1.ExtendX(s2.Size() - s1.Size())
	}

	count := 0
	for i := 0; i < s2.Size(); i++ {
		// "a" will have a 1 where s1i & s2i == null (00)
		// apply before set operator of s1i & s2i
		s1.Values[i] &= s2.Values[i]
		a := ~(s1.Values[i] | (s1.Values[i] >> 1)) & 0x5555_5555
		// count the number of bits set to 1 (derived from Hacker's Delight)
		b := (a & 0x33333333) + ((a >> 2) & 0x33333333)
		b = (b & 0x0F0F0F0F) + ((b >> 4) & 0x0F0F0F0F)
		b += (b >> 8)
		b += (b >> 16)
		count += b & 0x0000003F
		// apply active set operator of s1i | s2i
		s1.Values[i] |= (a | (a << 1))
	}

	if count > 1 {
		return NewCubeBool(0)
	}
	return s1
}

// This finds a less constrained cube that covers s1 and not s2
func Prime(s1, s2 Cube) Cube {
	if s1.Size() < s2.Size() {
		s1.ExtendX(s2.Size() - s1.Size())
	}

	for i := 0; i < s2.Size(); i++ {
		// "b" will have a 1 where s1i & s2i != null (00)
		a := s1.Values[i] & s2.Values[i]
		b := (a | (a >> 1)) & 0x5555_5555
		// apply active set operator of s1i & s2i
		// apply before set operator of s1i
		s1.Values[i] |= (b | (b << 1)) & s2.Values[i]
	}

	return s1
}

// if a literal in s1 covers an assignment not covered by s2, then remove all
// assignments of that literal that are covered by s2. This cuts the cube into
// a set of assignments that cannot be covered by just one cube.
// the result contains all of the minterms of s1 which are not contained by s2
// the resulting cubes are not guaranteed to be disjoint
func BasicSharp(s1, s2 Cube) Cover {
	result := Cover{}	
	if s1.Size() < s2.Size() {
		s1.ExtendX(s2.Size() - s1.Size())
	}

	for i := 0; i < s2.Size(); i++ {
		// "b" will have a 1 where s1i is not a subset of s2i
		a := (s1.Values[i] & s2.Values[i]) ^ s1.Values[i]
		b := (a | (a >> 1)) & 0x5555_5555

		// We need to find each of those ones
		for j := 0; b != 0; j+=2 {
			// If we found one
			if b & 1 {
				// apply the before rule s1i
				result.PushBack(s1)
				// apply the active rule s1i & ~s2i
				result.Back().Values[i] &= (~(3 << j) | (s1.Values[i] & ~s2.Values[i]))
			}
			b >>= 2
		}
	}

	return result
}

// TODO This looks to be exactly the same as above?
func Sharp(s1, s2 Cube) Cover {
	result := Cover{}
	if s1.Size() < s2.Size() {
		s1.ExtendX(s2.Size() - s1.Size())
	}

	for i := 0; i < s2.Size(); i++ {
		// b will have a 1 where s1i is not a subset of s2i
		a := (s1.Values[i] & s2.Values[i]) ^ s1.Values[i]
		b := (a | (a >> 1)) & 0x5555_5555

		// We need to find each of those 1's
		for j := 0; b != 0; j+=2 {
			// If we found one
			if b & 1 {
				// apply the before rule s1i
				result.PushBack(s1)
				// apply the active rule s1i & ~s2i
				result.Back().Values[i] &= (~(3 << j) | (s1.Values[i] & ~s2.Values[i]))
			}
			b >>= 2
		}
	}

	return result
}

// same as basicSharp, but the resulting cubes are guaranteed to be disjoint
func BasicDisjointSharp(s1, s2 Cube) Cover {
	result := Cover{}

	if s1.Size() < s2.Size() {
		s1.ExtendX(s2.Size() - s1.Size())
	}

	for i := 0; i < s2.Size(); i++ {
		// b will have a 1 where s1i is not a subset of s2i
		a := (s1.Values[i] & s2.Values[i]) ^ s1.Values[i]
		b := (a | (a >> 1)) & 0x5555_5555

		// We need to find each of those 1's
		for j := 0; b != 0; j+=2 {
			// If we found one
			if b & 1 {
				// apply the before rule s1i
				result.PushBack(s1)
				// apply the active rule s1i & ~s2i
				// apply the after rule s1i & s2i
				result.Back().Values[i] &= (~(3 << j) | (s1.Values[i] & ~s2.Values[i])) & ((0xFFFF_FFFF << j) | s2.Values[i])
				for k := i+1; k < s2.Size(); k++ {
					result.Back().Values[k] &= s2.Values[k]
				}
			}
			b >>= 2
		}
	}

	return result
}

// TODO This looks to be exactly the same as above?
func DisjointSharp(s1, s2 Cube) Cover {
	result := Cover{}

	if s1.Size() < s2.Size() {
		s1.ExtendX(s2.Size() - s1.Size())
	}

	for i := 0; i < s2.Size(); i++ {
		// b will have a 1 where s1i is not a subset of s2i
		a := (s1.Values[i] & s2.Values[i]) ^ s1.Values[i]
		b := (a | (a >> 1)) & 0x5555_5555

		// We need to find each of those 1's
		for j := 0; b != 0; j+=2 {
			// If we found one
			if b & 1 {
				// apply the before rule s1i
				result.PushBack(s1)
				// apply the active rule s1i & ~s2i
				// apply the after rule s1i & s2i
				result.Back().Values[i] &= (~(3 << j) | (s1.Values[i] & ~s2.Values[i])) & ((0xFFFF_FFFF << j) | s2.Values[i])
				for k := i+1; k < s2.Size(); k++ {
					result.Back().Values[k] &= s2.Values[k]
				}
			}
			b >>= 2
		}
	}

	return result
}

// Returns an xor sum of products representation of s1, s2
func Crosslink(s1, s2 Cube) Cover {
	result := Cover{}

	if s1.Size() < s2.Size() {
		s1.ExtendX(s2.Size() - s1.Size())
	}

	for i := 0; i < s2.Size(); i++ {
		// b will have a 1 where s1i & s2i = null
		a := ~(s1.Values[i] & s2.Values[i])
		b := a & (a >> 1) & 0x5555_5555

		// We need to find each of those 1's
		for j := 0; b != 0; j+=2 {
			// If we found one
			if b & 1 {
				// apply the before rule s1i
				result.PushBack(s1)
				// apply the active rule s1i | s2i
				// apply the after rule s2i
				result.Back().Values[i] = (s1.Values[i] & (0xFFFFFFFC << j)) | ((3 << j) & (s1.Values[i] | s2.Values[i])) | (~(0xFFFF_FFFF << j) & s2.Values[i])
				for k := i+1; k < s2.Size(); k++ {
					result.Back().Values[k] = s2.Values[k]
				}
			}
			b >>= 2
		}
	}

	return result
}

// boolean cofactor (see cube::cofactor())
func Cofactor(s1 Cube, uid, val int) Cube {
	cmp := s1.Get(uid)
	if cmp == 1-val {
		s1.Set(uid, -1)
	} else {
		s1.Set(uid, 2)
	}

	return s1
}

func CofactorCube(s1, s2 Cube) Cube {
	if s1.Size() < s2.Size() {
		s1.ExtendX(s2.Size() - s1.Size())
	}

	for i := 0; i < s2.Size(); i++ {
		a := (s2.Values[i] ^ (s2.Values[i] >> 1)) & 0x5555_5555
		a = a | (a << 1)
		b := s2.Values[i] & s1.Values[i]
		b = (b | (b >> 1)) & 0x5555_5555
		b = b | (b << 1)
		s1.Values[i] = (s1.Values[i] | a) & b
	}

	return s1
}

// Return the number of disagreeing literals (null literals in the
// intersection)
func Distance(s0, s1 Cube) int {
	size := min(s0.Size(), s1.Size())
	count := 0
	for i := 0; i < size; i++ {
		// "a" is 1 where s0i & s1i == null (00)
		// XOR to see what bits are different
		a := s0.Values[i] & s1.Values[i]
		// OR together any differences in the bit pairs (a single value)
		a = (~(a | (a >> 1))) & 0x5555_5555

		// count the number of bits set to 1 (derived from Hacker's Delight)
		a = (a & 0x33333333) + ((a >> 2) & 0x33333333)
		a = (a & 0x0F0F0F0F) + ((a >> 4) & 0x0F0F0F0F)
		a += (a >> 8)
		a += (a >> 16)
		count += a & 0x0000003F
	}

	return count
}

// Return the number of literals that are shared by s0 and s1. If s0 is x&~y&z
// and s1 is x&y&w, then this returns 1 because x is shared between s0 and s1.
func Similarity(s0, s1 Cube) int {
	size := min(s0.Size(), s1.Size())
	count := 0
	for i := 0; i < size; i++ {
		a := (s0.Values[i] ^ (s0.Values[i] >> 1)) & (s1.Values[i] ^ (s1.Values[i] >> 1)) & 0x5555_5555
		a = (a | (a << 1)) & s0.Values[i] & s1.Values[i]

		// count the number of bits set to 1 (derived from Hacker's Delight)
		a = (a & 0x33333333) + ((a >> 2) & 0x33333333)
		a = (a & 0x0F0F0F0F) + ((a >> 4) & 0x0F0F0F0F)
		a += (a >> 8)
		a += (a >> 16)
		count += a & 0x0000003F
	}

	return count
}

// Returns true if s0 and s1 share at least one literal
func SimilarityG0(s0, s1 Cube) bool {
	size := min(s0.Size(), s1.Size())
	for i := 0; i < size; i++ {
		a := (s0.Values[i] ^ (s0.Values[i] >> 1)) & (s1.Values[i] ^ (s1.Values[i] >> 1)) & 0x5555_5555
		a = (a | (a << 1)) & s0.Values[i] & s1.Values[i]

		// count the number of bits set to 1 (derived from Hacker's Delight)
		a = (a & 0x33333333) + ((a >> 2) & 0x33333333)
		a = (a & 0x0F0F0F0F) + ((a >> 4) & 0x0F0F0F0F)
		a += (a >> 8)
		a += (a >> 16)
		if (a & 0x0000003F) > 0 {
			return true
		}
	}
	return false
}

// Returns three values
// vn or "value" "not" represents the number of variables x in which s0 has the
// literal "x" and s1 has "~x" or visa versa
// xv or "X" "value" represents the number of variables x such that s0 has no literal restricting x while s1 does
// vx or "value" "X" represents the number of variables x such that s0 has a literal restricting x while s1 does not
// these three values inform the redundancy rules a&b | a&~b = a and a | a&b = a
func MergeDistances(s0, s1 Cube, vn, xv, vx *int) {
	m0 := min(s0.Size(), s1.Size())
	vnTemp := 0
	xvTemp := 0
	vxTemp := 0
	for i := 0; i < m0; i++ {
		// XOR to see what bits are different
		a := s0.Values[i] ^ s1.Values[i]
		b := s0.Values[i] & 0x5555_5555 & (s0.Values[i] >> 1)
		c := s1.Values[i] & 0x5555_5555 & (s1.Values[i] >> 1)
		d :=  b & ~c
		e := ~b &  c
		// AND together any differences in the bit pairs (a single value)
		a = (a & (a >> 1)) & 0x5555_5555

		// count the number of bits set to 1 (derived from Hacker's Delight)
		a = (a & 0x33333333) + ((a >> 2) & 0x33333333)
		a = (a & 0x0F0F0F0F) + ((a >> 4) & 0x0F0F0F0F)
		a = a + (a >> 8)
		a = a + (a >> 16)
		vnTemp += a & 0x0000003F

		d = (d & 0x33333333) + ((d >> 2) & 0x33333333)
		d = (d & 0x0F0F0F0F) + ((d >> 4) & 0x0F0F0F0F)
		d = d + (d >> 8)
		d = d + (d >> 16)
		xvTemp += d & 0x0000003F

		e = (e & 0x33333333) + ((e >> 2) & 0x33333333)
		e = (e & 0x0F0F0F0F) + ((e >> 4) & 0x0F0F0F0F)
		e = e + (e >> 8)
		e = e + (e >> 16)
		vxTemp += e & 0x0000003F
	}
	for i := m0; i < s0.Size(); i++ {
		// XOR to see what bits are different
		a := ~s0.Values[i]
		b := s0.Values[i] & 0x5555_5555 & (s0.Values[i] >> 1)
		c := 0x5555_5555
		d :=  b & ~c
		e := ~b &  c
		// AND together any differences in the bit pairs (a single value)
		a = (a & (a >> 1)) & 0x5555_5555

		// count the number of bits set to 1 (derived from Hacker's Delight)
		a = (a & 0x33333333) + ((a >> 2) & 0x33333333)
		a = (a & 0x0F0F0F0F) + ((a >> 4) & 0x0F0F0F0F)
		a = a + (a >> 8)
		a = a + (a >> 16)
		vnTemp += a & 0x0000003F

		d = (d & 0x33333333) + ((d >> 2) & 0x33333333)
		d = (d & 0x0F0F0F0F) + ((d >> 4) & 0x0F0F0F0F)
		d = d + (d >> 8)
		d = d + (d >> 16)
		xvTemp += d & 0x0000003F

		e = (e & 0x33333333) + ((e >> 2) & 0x33333333)
		e = (e & 0x0F0F0F0F) + ((e >> 4) & 0x0F0F0F0F)
		e = e + (e >> 8)
		e = e + (e >> 16)
		vxTemp += e & 0x0000003F
	}
	for i := m0; i < s1.Size(); i++ {
		// XOR to see what bits are different
		a := ~s1.Values[i]
		b := 0x5555_5555
		c := s1.Values[i] & 0x5555_5555 & (s1.Values[i] >> 1)
		d :=  b & ~c
		e := ~b &  c
		// AND together any differences in the bit pairs (a single value)
		a = (a & (a >> 1)) & 0x5555_5555

		// count the number of bits set to 1 (derived from Hacker's Delight)
		a = (a & 0x33333333) + ((a >> 2) & 0x33333333)
		a = (a & 0x0F0F0F0F) + ((a >> 4) & 0x0F0F0F0F)
		a = a + (a >> 8)
		a = a + (a >> 16)
		vnTemp += a & 0x0000003F

		d = (d & 0x33333333) + ((d >> 2) & 0x33333333)
		d = (d & 0x0F0F0F0F) + ((d >> 4) & 0x0F0F0F0F)
		d = d + (d >> 8)
		d = d + (d >> 16)
		xvTemp += d & 0x0000003F

		e = (e & 0x33333333) + ((e >> 2) & 0x33333333)
		e = (e & 0x0F0F0F0F) + ((e >> 4) & 0x0F0F0F0F)
		e = e + (e >> 8)
		e = e + (e >> 16)
		vxTemp += e & 0x0000003F
	}

	if vn != NULL {
		*vn = vnTemp
	}
	if xv != NULL {
		*xv = xvTemp
	}
	if vx != NULL {
		*vx = vxTemp
	}
}

// check the two cubes against the redundancy rules
// a&b | a&~b = a
// a | a&b = a
func Mergible(s0, s1 Cube) bool {
	vn := 0
	xv := 0
	vx := 0
	MergeDistances(s0, s1, &vn, &xv, &vx)

	return (vn + (xv > 0) + (vx > 0) <= 1)
}

// See cube::supercube() and operator~()
func SupercubeOfComplement(s Cube) Cube {
	result := Cube{
		Values: make([]uint32, s.Size()),
	}
	count := 0
	for i := 0; i < s.Size(); i++ {
		// OR together any differences in the bit pairs (a single value)
		a := (s.Values[i] ^ (s.Values[i] >> 1)) & 0x5555_5555

		// count the number of bits set to 1 (derived from Hacker's Delight)
		a = (a & 0x33333333) + ((a >> 2) & 0x33333333)
		a = (a & 0x0F0F0F0F) + ((a >> 4) & 0x0F0F0F0F)
		a += (a >> 8)
		a += (a >> 16)
		count += a & 0x0000003F

		if count > 1 {
			return Cube{}
		}

		result.Values[i] = ((s.Values[i] & 0xAAAA_AAAA) >> 1) | ((s.Values[i] & 0x5555_5555) << 1)
	}

	if count == 1 {
		return result
	}
	return NewCubeBool(0)
}

/*

encoding     assignment   stable   result
{X,0,1,-}    X            true     X
{X,0,1,-}    0            true     0
{X,0,1,-}    1            true     1

X            -            true     X
0            -            true     0
1            -            true     1
-            -            true     -

X            X,0,1        false    X
0            {X,1}        false    X
0            0            false    0
1            {X,0}        false    X
1            1            false    1
-            {X,0,1}      false    X

X            -            false    X
0            -            false    0
1            -            false    1
-            -            false    -

 */
func LocalAssign(encoding, assignment Cube, stable bool) Cube {
	result := Cube{
		Values: make([]uint32, max(encoding.Size(), assignment.Size())),
	}
	stableMask := 0x0000_0000
	if stable {
		stableMask = 0xFFFF_FFFF 
	}

	m0 := min(encoding.Size(), assignment.Size())
	i := 0
	for ; i < m0; i++ {
		// {X,0,1} to X... only - left
		v := assignment.Values[i] & (assignment.Values[i] >> 1) & 0x5555_5555
		v = v | (v<<1)
		// - where they are different
		x := encoding.Values[i] ^ assignment.Values[i]
		x = (x | (x >> 1)) & 0x5555_5555
		x = x | (x<<1)
		// X where they are different and assignment is not -, - everywhere else
		x = ~x | v

		result.Values[i] = (x | stableMask) & ((encoding.Values[i] & v) | (assignment.Values[i] & ~v))
	}
	for ; i < encoding.Size(); i++ {
		result.Values[i] = encoding.Values[i]
	}
	for ; i < assignment.Size(); i++ {
		// {X,0,1} to X... only - left
		v := assignment.Values[i] & (assignment.Values[i] >> 1) & 0x5555_5555
		v = v | (v<<1)

		result.Values[i] = (v | stableMask) & assignment.Values[i]
	}
	return result
}

/*

encoding     assignment   stable   result
{X,0,1,-}    X            true     X
X            0            true     -
X            1            true     -
X            -            true     X
0            0            true     0
0            1            true     -
0            -            true     0
1            0            true     -
1            1            true     1
1            -            true     1
-            0            true     -
-            1            true     -
-            -            true     -

{X,0,1,-}    X            false    X
{X,1,-}      0            false    X
{X,0,-}      1            false    X
0            0            false    0
1            1            false    1
X            -            false    X
0            -            false    0
1            -            false    1
-            -            false    -

 */
func RemoteAssign(encoding, assignment Cube, stable bool) Cube {
	result := Cube{
		Values: make([]uint32, max(encoding.Size(), assignment.Size())),
	}
	stableMask := 0x0000_0000
	if stable {
		stableMask = 0xFFFF_FFFF
	}

	m0 := min(encoding.Size(), assignment.Size())
	i := 0
	for ; i < m0; i++ {
		// {X,0,1} to X... only - left
		v := (assignment.Values[i] & (assignment.Values[i] >> 1)) & 0x5555_5555
		v = v | (v<<1)
		// {0,1,-} to -... only X left
		u := (assignment.Values[i] | (assignment.Values[i] >> 1)) & 0x5555_5555
		u = u | (u<<1)
		// - where they are different
		x := encoding.Values[i] ^ assignment.Values[i]
		x = (x | (x >> 1)) & 0x5555_5555
		x = x | (x<<1)
		// X where they are different and assignment is not -, - everywhere else
		x = ~x | v

		result.Values[i] = u & (x | stableMask) & ((~x & stableMask) | encoding.Values[i])
	}
	for ; i < encoding.Size(); i++ {
		result.Values[i] = encoding.Values[i]
	}
	for ; i < assignment.Size(); i++ {
		// {X,0,1} to X... only - left
		v := assignment.Values[i] & (assignment.Values[i] >> 1) & 0x5555_5555
		v = v | (v<<1)

		// {0,1,-} to -... only X left
		u := (assignment.Values[i] | (assignment.Values[i] >> 1)) & 0x5555_5555
		u = u | (u<<1)

		result.Values[i] = (v | stableMask) & (u | ~stableMask)
	}

	return result
}

/*

encoding     assignment   stable  result
X            X            true    true
0            0            true    true
1            1            true    true
{X,0,1,-}    -            true    true

X            0            true    false
X            1            true    false
0            X            true    false
0            1            true    false
1            X            true    false
1            0            true    false
-            X            true    false
-            0            true    false
-            1            true    false


X            X            false    true
X            0            false    true
X            1            false    true
0            0            false    true
1            1            false    true
{X,0,1,-}    -            false    true

0            X            false    false
0            1            false    false
1            X            false    false
1            0            false    false
-            X            false    false
-            0            false    false
-            1            false    false



All literals must be vacuous for the assignment to be vacuous

 */
func VacuousAssign(encoding, assignment Cube, stable bool) bool {
	stableMask := 0x0000_0000
	if stable {
		stableMask := 0xFFFF_FFFF
	}

	i := 0
	m0 := min(encoding.Size(), assignment.Size())
	for ; i < m0; i++ {
		// {X,0,1} to X... only - left
		v := assignment.Values[i] & (assignment.Values[i] >> 1) & 0x5555_5555
		v = v | (v<<1)
		// - where they are different
		x := encoding.Values[i] ^ assignment.Values[i]
		x = (x | (x >> 1)) & 0x5555_5555
		x = x | (x<<1)
		// X where they are different and assignment is not -, - everywhere else
		x = ~x | v

		if (encoding.Values[i] | v) != ((x|stableMask)&assignment.Values[i]) {
			return false
		}
	}
	for ; i < assignment.Size(); i++ {
		if assignment.Values[i] != 0xFFFF_FFFF {
			return false
		}
	}

	return true
}

/*

local        global       guard        result
{0,1,-}      {0,1,-}      X            -1
0            0            1            -1
1            1            0            -1

X            {X,0,1,-}    {X,0,1}      0
{0,1,-}      X            {X,0,1}      0
-            0            1            0
-            1            0            0

0            0            0            1
1            1            1            1
-            0            0            1
-            1            1            1
-            -            {0,1}        1
{X,0,1,-}    {X,0,1,-}    -            1

Take the minimum of the result over all literals

final result:
-1 means state does not pass the guard
0 means guard is unstable
1 means state passes the guard

 */
func PassesGuard(local, global, guard Cube) int {
	m0 := min(local.Size(), guard.Size())
	i := 0
	result := 1
	for ; i < m0; i++ {
		c := guard.Values[i]

		// {X,0,1} to X
		guardDashMask := (c & (c >> 1)) & 0x5555_5555
		guardDashMask = guardDashMask | (guardDashMask << 1)

		g := global.Values[i] | guardDashMask
		l := local.Values[i] | guardDashMask

		passTest := (g & l & c)
		passTest = (passTest | (passTest >> 1)) & 0x5555_5555
		passTest = passTest | (passTest << 1)

		// Handle the following cases
		//    0            0            0            1
		//    1            1            1            1
		//    -            0            0            1
		//    -            1            1            1
		//    -            -            {0,1}        1
		//    {X,0,1,-}    {X,0,1,-}    -            1
		if passTest != 0xFFFF_FFFF {
			g |= passTest
			l |= passTest
			c |= passTest

			// Handle the following cases
			//    {0,1,-}        {0,1,-}        X            -1
			// X values where there is an X in the guard
			blockTest := (c | (c >> 1)) & 0x5555_5555
			blockTest = blockTest | (blockTest << 1)

			// Handle the following cases
			//    0            0            1            -1
			//    1            1            0            -1
			// X values where global and local agree
			blockTest2 := (g ^ l) | passTest
			blockTest2 = (blockTest2 | (blockTest2 >> 1)) & 0x5555_5555
			blockTest2 = (blockTest2 | (blockTest2 << 1))

			// Filter out the following cases
			//    X            {X,0,1,-}    {X,0,1}        0
			//    {0,1,-}      X            {X,0,1}        0
			// X values where global or local has X
			unstableTest := g & l
			unstableTest = (unstableTest | (unstableTest >> 1)) & 0x5555_5555
			unstableTest = (unstableTest | (unstableTest << 1))

			if ((blockTest&blockTest2) | ~unstableTest) != 0xFFFF_FFFF {
				return -1
			}
			result = 0
		}
	}
	for ; i < guard.Size(); i++ {
		x := (guard.Values[i] | (guard.Values[i] >> 1)) & 0x5555_5555
		x |= (x << 1)
		if x != 0xFFFF_FFFF {
			return -1
		}
	}

	return result
}

// check if the current set of assignments violates the given constraint If one
// of the assignments are not covered by the constraint, then it is violated.
func ViolatesConstraint(assignments, constraint Cube) bool {
	return AreMutex(assignments.Xoutnulls(), constraint)
}

// all conflicting literals between left and right are set to null (00) in left
func Interfere(left, right Cube) Cube {
	result := Cube{}
	m0 := min(left.Size(), right.Size())
	i := 0
	for ; i < m0; i++ {
		// u masks out all tautologies (11) in "left"
		u := (left.Values[i] & (left.Values[i]>>1)) & 0x5555_5555
		u = u | (u<<1)

		// any conflicts between left and right become null
		result.Values.PushBack((left.Values[i] & right.Values[i]) | u)
	}
	for ; i < len(left.Values); i++ {
		result.Values.PushBack(left.Values[i])
	}
	return result
}

// hide all literals in left which are not exactly equal to the associated literal in right
func Difference(left, right Cube) Cube {
	result := Cube{}
	m0 := min(left.Size(), right.Size())
	i := 0
	for ; i < m0; i++ {
		// u masks out all literals between left and right that aren't exactly the same
		u := left.Values[i] ^ right.Values[i]
		u = (u | (u>>1)) & 0x5555_5555
		u = u | (u<<1)

		// extract those differences, hiding any non-differences
		result.Values.PushBack(right.Values[i] | ~u)
	}
	for ; i < right.Size(); i++ {
		result.Values.PushBack(right.Values[i])
	}
	return result
}

// check if two cubes are equal
func Equal(s1, s2 Cube) bool {
	i := 0
	size := min(s1.Size(), s2.Size())
	for ; i < size; i++ {
		if s1.Values[i] != s2.Values[i] {
			return false
		}
	}
	for ; i < s1.Size(); i++ {
		if s1.Values[i] != 0xFFFF_FFFF {
			return false
		}
	}
	for ; i < s2.Size(); i++ {
		if 0xFFFF_FFFF != s2.Values[i] {
			return false
		}
	}

	return true
}

func EqualBool(s1 Cube, s2 int) bool {
	if s2 == 0 {
		for i := 0; i < s1.Size(); i++ {
			if ((s1.Values[i]>>1) | s1.Values[i] | 0xAAAA_AAAA) != 0xFFFF_FFFF {
				return true
			}
		}

		return false
	}
	for i := 0; i < s1.Size(); i++ {
		if s1.Values[i] != 0xFFFF_FFFF {
			return false
		}
	}

	return true
}

func NotEqual(s1, s2 Cube) bool {
	i := 0
	size := min(s1.Size(), s2.Size())
	for ; i < size; i++ {
		if s1.Values[i] != s2.Values[i] {
			return true
		}
	}
	for ; i < s1.Size(); i++ {
		if s1.Values[i] != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i < s2.Size(); i++ {
		if 0xFFFF_FFFF != s2.Values[i] {
			return true
		}
	}

	return false
}

func NotEqualBool(s1 Cube, s2 int) bool {
	if s2 == 0 {
		for i := 0; i < s1.Size(); i++ {
			if ((s1.Values[i]>>1) | s1.Values[i] | 0xAAAA_AAAA) != 0xFFFF_FFFF {
				return false
			}
		}

		return true
	}

	for i := 0; i < s1.Size(); i++ {
		if s1.Values[i] != 0xFFFF_FFFF {
			return true
		}
	}

	return false
}

// For use in sorting. Given cubes s1 and s2, s1 < s2 if:
// s1 has fewer literals than s2 or
// (they have the same number of literals but
// the literal in s1 with the largest variable id has a smaller variable id than that of s2
// or the next largest or ... or
// (their literals cover all of the same variables but
// the largest literal in s1 covers an assignment of 0 while s2 covers 1
// or the next largest or ...))
func Less(s1, s2 Cube) bool {
	m0 := min(s1.Size(), s2.Size())
	i := 0
	count0 := 0
	count1 := 0
	for ; i < m0; i++ {
		count0 += countOnes(s1.Values[i])
		count1 += countOnes(s2.Values[i])
	}
	for ; i < s1.Size(); i++ {
		count0 += countOnes(s1.Values[i])
		count1 += 32
	}
	for ; i < s2.Size(); i++ {
		count0 += 32
		count1 += countOnes(s2.Values[i])
	}

	if count0 > count1 {
		return true
	} else if count1 > count0 {
		return false
	}

	i--

	for ; i >= s1.Size(); i-- {
		if 0xFFFF_FFFF != s2.Values[i] {
			return false
		}
	}
	for ; i >= s2.Size(); i-- {
		if s1.Values[i] != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i >= 0; i-- {
		if s1.Values[i] != s2.Values[i] {
			return (s1.Values[i] < s2.Values[i])
		}
	}

	return false
}

func Greater(s1, s2 Cube) bool {
	m0 := min(s1.Size(), s2.Size())
	i := 0
	count0 := 0
	count1 := 0
	for ; i < m0; i++ {
		count0 += countOnes(s1.Values[i])
		count1 += countOnes(s2.Values[i])
	}
	for ; i < s1.Size(); i++ {
		count0 += countOnes(s1.Values[i])
		count1 += 32
	}
	for ; i < s2.Size(); i++ {
		count0 += 32
		count1 += countOnes(s2.Values[i])
	}

	if count0 > count1 {
		return false
	} else if count1 > count0 {
		return true
	}

	for ; i >= s1.Size(); i-- {
		if 0xFFFF_FFFF != s2.Values[i] {
			return true
		}
	}
	for ; i >= s2.Size(); i-- {
		if s1.Values[i] != 0xFFFF_FFFF {
			return false
		}
	}
	for ; i >= 0; i-- {
		if s1.Values[i] != s2.Values[i] {
			return (s1.Values[i] > s2.Values[i])
		}
	}

	return false
}

func LessOrEqual(s1, s2 Cube) bool {
	m0 := min(s1.Size(), s2.Size())
	i := 0
	count0 := 0
	count1 := 0
	for ; i < m0; i++ {
		count0 += countOnes(s1.Values[i])
		count1 += countOnes(s2.Values[i])
	}
	for ; i < s1.Size(); i++ {
		count0 += countOnes(s1.Values[i])
		count1 += 32
	}
	for ; i < s2.Size(); i++ {
		count0 += 32
		count1 += countOnes(s2.Values[i])
	}

	if count0 > count1 {
		return true
	} else if count1 > count0 {
		return false
	}

	for ; i >= s1.Size(); i-- {
		if 0xFFFF_FFFF != s2.Values[i] {
			return false
		}
	}
	for ; i >= s2.Size(); i-- {
		if s1.Values[i] != 0xFFFF_FFFF {
			return true
		}
	}
	for ; i >= 0; i-- {
		if s1.Values[i] != s2.Values[i] {
			return (s1.Values[i] < s2.Values[i])
		}
	}

	return true
}

func GreaterOrEqual(s1, s2 Cube) bool {
	m0 := min(s1.Size(), s2.Size())
	i := 0
	count0 := 0
	count1 := 0
	for ; i < m0; i++ {
		count0 += countOnes(s1.Values[i])
		count1 += countOnes(s2.Values[i])
	}
	for ; i < s1.Size(); i++ {
		count0 += countOnes(s1.Values[i])
		count1 += 32
	}
	for ; i < s2.Size(); i++ {
		count0 += 32
		count1 += countOnes(s2.Values[i])
	}

	if count0 > count1 {
		return false
	} else if count1 > count0 {
		return true
	}

	for ; i >= s1.Size(); i-- {
		if 0xFFFF_FFFF != s2.Values[i] {
			return true
		}
	}
	for ; i >= s2.Size(); i-- {
		if s1.Values[i] != 0xFFFF_FFFF {
			return false
		}
	}
	for ; i >= 0; i-- {
		if s1.Values[i] != s2.Values[i] {
			return (s1.Values[i] > s2.Values[i])
		}
	}

	return true
}

