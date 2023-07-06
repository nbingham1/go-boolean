package boolean

import (
	"github.com/mpvl/unique"
)

type Cover struct {
	Cubes []Cube
}

func NewCover(rsv int) Cover {
	return Cover{
		Cubes: make([]Cube, 0, rsv),
	}
}

func NewCoverBool(val int) Cover {
	if val == 1 {
		return Cover{
			Cubes: []Cube{Cube{}},
		}
	}
	return Cover{}
}

func NewCoverLiteral(uid, val int) Cover {
	return Cover{
		Cubes: []Cube{NewCubeLiteral(uid, val)},
	}
}

func NewCoverCube(s ...Cube) Cover {
	return Cover{
		Cubes: append(make([]Cube, 0, len(s)), s...),
	}
}

func (c *Cover) Begin() Iterator[Cube] {
	return Iterator[Cube]{
		slc: Cubes,
		idx: 0,
	}
}

func (c *Cover) Size() int {
	return len(c.Cubes)
}

func (c *Cover) Reserve(num int) {
	tmp := c.Cubes
	c.Cubes = make(c.Cubes, len(tmp), len(tmp)+num)
	copy(c.Cubes, tmp)
}

func (c *Cover) BackPtr() *Cube {
	return &c.Cubes[len(c.Cubes)-1]
}

func (c *Cover) Back() Cube {
	return c.Cubes[len(c.Cubes)-1]
}

func (c *Cover) PushBack(s1 ...Cube) {
	c.Cubes = append(c.Cubes, s1...)
}

func (c *Cover) PopBack(n int) {
	c.Cubes = c.Cubes[0:len(c.Cubes)-n]
}

func (c *Cover) Clear() {
	c.Cubes = []Cube{}
}

func (c *Cover) Erase(start, end int) {
	if end < 0 {
		end += len(c.Cubes)
	}
	if start < 0 {
		start += len(c.Cubes)
	}

	if end >= len(c.Cubes) {
		c.Cubes = c.Cubes[0:start]
	} else {
		c.Cubes = append(c.Cubes[0:start], c.Cubes[end:])
	}
}

func (c *Cover) IsSubsetOfCube(s Cube) bool {
	for i := 0; i < len(c.Cubes); i++ {
		if !cubes[i].IsSubsetOf(s) {
			return false
		}
	}

	return true
}

func (c *Cover) IsSubsetOf(s Cover) bool {
	for i := 0; i < len(c.Cubes); i++ {
		if !c.Cubes[i].IsSubsetOfCover(s) {
			return false
		}
	}

	return true
}

type rank struct {
	first int
	fecond int
}

// check if this cover covers all cubes
func (c *Cover) IsTautology() bool {
	// Cover F is empty
	if c.Size() == 0 {
		return false
	}

	// First, determine how many variables are used in this cover
	// Cover F includes the universal cube
	maxWidth := 0
	for i := 0; i < c.Size(); i++ {
		temp := cubes[i].MemoryWidth()
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
			result.Values = append(result.Values, 0xFFFFFFFF << (1 << max_width))
		} else {
			result.ExtendN(1 << (max_width-5))
		}

		for i := 0; i < c.Size(); i++ {
			result.Supercube(c.Cubes[i].GetCover(maxWidth))
		}

		return result.IsTautology()
	}

	// There are too many variables, so we'll use shannon expansion.
	// The variable with the highest binate rank is the one which appears in
	// both the positive sense and negative sense, and shows up the most times.
	// A variable that only appears in one sense has no binate rank.
	// So, for x & y | ~x & ~z, the binate rank of x is 2. Because y and ~z
	// only show up for one sense, they have binate ranks of 0.
	binateRank := []rank{}
	for i := 0; i < c.Size(); i++ {
		if len(binateRank) < len(c.Cubes[i])*16 {
			binateRank = append(binateRank, make([]rank, c.Cubes[i].Size()*16-len(binateRank))...)
		}

		for j := 0; j < len(c.Cubes[i])*16; j++ {
			val := c.Cubes[i].Get(j)
			if val == 0 {
				binateRank[j].first++
			} else if val == 1 {
				binateRank[j].second++
			}
		}
	}

	for i := 0; i < len(binateRank); i++ {
		// Column of all zeros
		if binateRank[i].first == c.Size() || binateRank[i].second == c.Size() {
			return false
		} else if binateRank[i].first > 0 && binateRank[i].second > 0 {
			binateRank[i].first += binateRank[i].second
			binateRank[i].second = i
		} else {
			binateRank[i].first = 0
			binateRank[i].second = i
		}
	}

	// Select a binate variable
	pair<int, int> uid = *MaxElement(binateRank.begin(), binateRank.end())

	// Do the shannon expansion, and recurse on the cofactors
	if uid.first > 0 {
		if !Cofactor(c, uid.second, 0).IsTautology() {
			return false
		}

		if !Cofactor(c, uid.second, 1).IsTautology() {
			return false
		}

		return true
	}

	// Function is unate
	return false
}

// Check if this cover is empty. This happens if there are no cubes in the
// cover or if all of the cubes contain a null literal.
func (c *Cover) IsNull() bool {
	for i := 0; i < len(c.Cubes); i++ {
		if !c.Cubes[i].IsNull() {
			return false
		}
	}

	return true
}

func (c *Cover) Area() int {
	result := 0
	for i := 0; i < c.Size(); i++ {
		result += c.Cubes[i].Width()
	}

	return result
}

// Returns a list of variable ids, one for each variable used in the cover.
func (c *Cover) Vars() []int {
	result := []int{}
	for i := 0; i < len(c.Cubes); i++ {
		cubes[i].Vars(&result)
	}
	unique.Sort(result)
	return result
}

// Same as above, but doesn't result in the allocation of a new vector.
func (c *Cover) VarsInPlace(result *[]int) {
	for i := 0; i < len(c.Cubes); i++ {
		c.Cubes[i].VarsInPlace(result)
	}
	unique.Sort(result)
}

// Shuffle the variables around. So if we have a & b represented as v0 & v1
// (a has an id of 0 and b has an id of 1)
// Then we can swap them so that we have a & b represented as v1 & v0
// (a has an id of 1 and b has an id of 0).
//
// uids: a list of id -> id mappings
func (c *Cover) Refactor(uids map[int]int) Cover {
	result := NewCover(len(c.Cubes))
	for i := 0; i < len(c.Cubes); i++ {
		result.Cubes = append(result.Cubes, c.Cubes[i].Refactor(uids))
	}

	return result
}

func (c *Cover) Remote(groups [][]int) Cover {
	result := NewCover(len(c.Cubes))
	for i := 0; i < len(this.Cubes); i++ {
		result.Cubes = append(result.Cubes, c.Cubes[i].Remote(groups))
	}
	return result
}

// get the supercube of all of the cubes in the cover. This represents the
// bounding box that entirely contains this cover.
func (c *Cover) Supercube() Cube {
	result := Cube{}
	if size() > 0 {
		result.ExtendN(c.Cubes[0].Size())

		for i := c.Size()-1; i != -1; i-- {
			if c.Cubes[i].Size() < result.Size() {
				result.Trunk(c.Cubes[i].Size())
			}

			for j := 0; j < result.Size(); j++ {
				result.Values[j] |= c.Cubes[i].Values[j]
			}
		}
	} else {
		result.Values = append(result.Values, 0x0000_0000)
	}

	return result
}

func (c *Cover) Mask() Cube {
	result := Cube{}
	for i := 0; i < len(this.Cubes); i++ {
		result = result.CombineMask(c.Cubes[i].Mask())
	}
	return result
}

func (c *Cover) Mask(v int) Cover {
	v = v+1
	v |= v << 2
	v |= v << 4
	v |= v << 8
	v |= v << 16

	result := NewCover(len(c.Cubes))
	for i := 0; i < len(c.Cubes); i++ {
		n := Cube{
			Values: make([]uint32, 0, len(c.Cubes[i].Values)),
		}
		for j := 0; j < len(c.Cubes[i].Values); j++ {
			n.Values = append(n.Values, c.Cubes[i].Values[j] | v)
		}
		result.Cubes = append(result.Cubes, n)
	}
	return result
}

func (c *Cover) ApplyMask(m Cube) Cover {
	result := NewCover(len(c.Cubes))
	for i := 0; i < len(c.Cubes); i++ {
		result.Cubes = append(result.Cubes, c.Cubes[i].ApplyMask(m))
	}
	return result
}

func (c *Cover) FlippedMask(cube m) cover {
	result := NewCover(len(c.Cubes))
	for i := 0; i < len(c.Cubes); i++ {
		result.Cubes = append(result.Cubes, c.Cubes[i].FlippedMask(m))
	}
	return result
}

func (c *Cover) Hide(uid int) {
	for i := 0; i < len(c.Cubes); i++ {
		c.cubes[i].Hide(uid)
	}
}

func (c *Cover) HideMany(uids []int) {
	for i := 0; i < len(c.Cubes); i++ {
		c.Cubes[i].HideMany(uids)
	}
}

func (c *Cover) Cofactor(s1 Cube) {
	w := 0
	r := 0
	for ; r < c.Size(); r++ {
		if c.Cubes[w].Size() < c.Cubes[r].Size() {
			c.Cubes[w].ExtendX(c.Cubes[r].Size())
		}

		valid := true
		j := 0
		for j = 0; j < cubes[r].size() && j < s1.size() && valid; j++ {
			b := s1.values[j] & cubes[r].values[j]
			b = ~(b | (b >> 1)) & 0x55555555

			if b != 0 {
				valid = false
			} else {
				a := (s1.values[j] ^ (s1.values[j] >> 1)) & 0x55555555
				a = a | (a << 1)
				cubes[w].values[j] = cubes[r].values[j] | a
			}
		}

		if valid {
			if w != r {
				for ; j < cubes[r].size(); j++ {
					cubes[w].values[j] = cubes[r].values[j]
				}

				if cubes[w].size() > cubes[r].size() {
					cubes[w].trunk(cubes[r].size())
				}
			}

			w++
		}
	}
}

func (c *Cover) Cofactor(int uid, int val) {
	w := 0
	r := 0
	for ; r < c.Size(); r++ {
		cmp := c.Cubes[r].Get(uid)
		if cmp != 1-val {
			if r != w {
				c.Cubes[w] = c.Cubes[r]
			}

			c.Cubes[w].Set(uid, 2)
			w++
		}
	}

	if w != r {
		c.Cubes = c.Cubes[0:w]
	}
}

type arc struct {
	left, right int
	weight float32
}

type node struct {
	indices []int
	arcs []int
}

func (c *Cover) Partition(left, right Cover) float32 {
	if c.Cubes.size() <= 1 {
		left = *c
		right = Cover{}
		return math.Inf(1)
	}

	if c.IsTautology() {
		left = 1
		right = Cover{}
		return math.Inf(1)
	}

	nodes := []node{}
	arcs := []arc{}

	// Build a weighted undirected graph in which the weights are the similarity
	// between a given pair of cubes. The similarity is the number of literals
	// shared by the two cubes. Arcs connect groups of cubes, but we start with
	// each arc connecting only single cubes.
	for i := 0; i < len(c.Cubes); i++ {
		nodes = append(nodes, Node{
			indices: []int{i},
		})
	}

	for i, n0 := range nodes {
		for j, n1 := range nodes {
			l := n0.indices[0]
			r := n1.indices[0]
			w := Similarity(c.Cubes[l], c.Cubes[r])
			nodes[i].arcs = append(nodes[i].arcs, len(arcs))
			nodes[j].arcs = append(nodes[j].arcs, len(arcs))
			arcs = append(arcs, arc{
				left: i,
				right: j,
				// We cannot remove zero weighted edges here because we need to be able
				// to split on one. This algorithm ultimately must return an *edge*.
				weight: w*w/(c.Cubes[l].Width()*c.Cubes[r].Width()),
			})
		}
	}

	// We want to consecutively merge the heaviest arcs
	for len(arcs) > 1 {
		// grab the heaviest arc
		m := 0 // index into arcs
		var mhi, mlo int
		if len(nodes[arcs[m].left].indices) > len(nodes[arcs[m].right].indices) {
			mhi = len(nodes[arcs[m].left].indices)
			mlo = len(nodes[arcs[m].right].indices)
		} else {
			mhi = len(nodes[arcs[m].right].indices)
			mlo = len(nodes[arcs[m].left].indices)
		}
		for a := 1; i < len(arcs); a++ {
			var ahi, alo int
			if len(nodes[arcs[a].left].indices) > len(nodes[arcs[a].right].indices) {
				ahi = len(nodes[arcs[a].left].indices)
				alo = len(nodes[arcs[a].right].indices)
			} else {
				ahi = len(nodes[arcs[a].right].indices)
				alo = len(nodes[arcs[a].left].indices)
			}
			if (ahi < mhi || (ahi == mhi && (alo < mlo || (alo == mlo && arcs[a].weight > arcs[m].weight)))) {
				m = a
				mhi = ahi
				mlo = alo
			}
		}
		
		l := arcs[m].left
		r := arcs[m].right
		// merge the right node into the left node, updating any arcs along the way
		nodes[l].indices = append(nodes[l].indices, nodes[r].indices...)
		for a := 0; a < len(nodes[r].arcs); a++ {
			if nodes[nodes[r].arcs[a]].left == r {
				nodes[nodes[r].arcs[a]].left = l
			}
			if nodes[nodes[r].arcs[a]].right == r {
				nodes[nodes[r].arcs[a]].right = l
			}
		}
		nodes[l].arcs = append(nodes[l].arcs, nodes[r].arcs...)
		nodes = append(nodes[0:r], nodes[r+1:]...)
		
		// remove looping and duplicate arcs
		toErase := map[int]bool
		for a := 0; a < len(nodes[l].arcs); {
			if nodes[l].arcs[a].left == nodes[l].arcs[a].right {
				if _, ok := toErase[a]; !ok {
					toErase[a] = true
				}
				nodes[l].arcs = append(nodes[l].arcs[0:a], nodes[l].arcs[a+1:]...)
			} else {
				for b := a+1; b < len(nodes[l].arcs); {
					if (nodes[l].arcs[a].left == nodes[l].arcs[b].left && nodes[l].arcs[a].right == nodes[l].arcs[b].right) ||
					   (nodes[l].arcs[a].left == nodes[l].arcs[b].right && nodes[l].arcs[a].right == nodes[l].arcs[b].left) {
						nodes[l].arcs[a].weight += nodes[l].arcs[b].weight
						if _, ok := toErase[b]; !ok {
							toErase[b] = true
						}
		
						if nodes[l].arcs[b].left == l {
							for c := len(nodes[nodes[l].arcs[b].right].arcs)-1; c >= 0; c-- {
								if nodes[nodes[l].arcs[b].right].arcs[c] == b {
									 nodes[nodes[l].arcs[b].right].arcs = append(nodes[nodes[l].arcs[b].right].arcs[0:c], nodes[nodes[l].arcs[b].right].arcs[c+1:]...)
								}
							}
						} else {
							for c := len(nodes[nodes[l].arcs[b].left].arcs)-1; c >= 0; c-- {
								if nodes[nodes[l].arcs[b].left].arcs[c] == b {
									 nodes[nodes[l].arcs[b].left].arcs = append(nodes[nodes[l].arcs[b].left].arcs[0:c], nodes[nodes[l].arcs[b].left].arcs[c+1:]...)
								}
							}
						}
						nodes[l].arcs = append(nodes[l].arcs[0:b], nodes[l].arcs[b+1:])
					} else {
						b++
					}
				}
				a++
			}
		}

		for a := len(arcs)-1; a >= 0; a-- {
			if _, ok := toErase[a]; ok {
				arcs = append(arcs[0:a], arcs[a+1:]...)
			}
		}
	}

	if len(arcs) == 0 {
		return 0.0
	}

	left.Cubes = []Cube{}
	right.Cubes = []Cube{}

	a := arcs[len(arcs)-1]
	for i := 0; i < len(nodes[a.left].indices); i++ {
		left.Cubes = append(left.Cubes, c.Cubes[nodes[a.left].indices[i]])
	}
	for i := 0; i < len(nodes[a.right].indices); i++ {
		right.Cubes = append(right.Cubes, c.Cubes[nodes[a.right].indices[i]])
	}

	return a.weight
}

func (c *Cover) Espresso() {
	Espresso(c, Cover{}, Not(c))
}

func (c *Cover) Minimize() {
	// Remove nulls, check for tautology
	for i := len(c.Cubes)-1; i >= 0; i-- {
		if c.Cubes[i].IsNull() {
			c.Cubes = append(c.Cubes[0:i], c.Cubes[i+1:]...)
		} else if cubes[i].is_tautology() {
			c.Cubes = []Cube{Cube{}}
			return
		}
	}

	done := false
	for !done {
		done = true
		for i := len(c.Cubes) - 1; i >= 0 ; i-- {
			for j := i-1; j >= 0; j-- {
				if Mergible(c.Cubes[i], c.Cubes[j]) {
					c.Cubes[i].Supercube(c.Cubes[j])
					c.Cubes = append(c.Cubes[0:j], c.Cubes[j+1:]...)
					i--
					done = false
				}
			}
		}
	}
}

func (c *Cover) Clone() Cover {
	result := Cover{}
	for _, cube := range c.Cubes {
		result.Cubes = append(result.Cubes, cube.Clone())
	}
	return result 
}

func (c *Cover) Intersect(s1 Cover) *Cover {
	if s1.IsNull() || c.IsNull() {
		c.Cubes := []Cube{}
	} else {
		*c := Intersect(*c, s1)
	}

	return c
}

func (c *Cover) IntersectCube(s1 Cube) *Cover {
	for i := 0; i < len(c.Cubes); i++ {
		c.Cubes[i].Intersect(s1)
	}

	return c
}

func (c *Cover) IntersectBool(val int) *Cover {
	if val == 0 {
		c.Cubes = []Cube{}
	}

	return c
}

func (c *Cover) Union(s1 Cover) *Cover {
	c.Cubes = append(c.Cubes, s1.Cubes...)
	c.Minimize()
	return c
}

func (c *Cover) UnionCube(s1 Cube) *Cover {
	c.Cubes = append(c.Cubes, s1)
	c.Minimize()
	return c
}

func (c *Cover) UnionBool(val int) *Cover {
	if val == 1 {
		c.Cubes = []Cube{NewCubeBool(1)}
	}

	return c
}

func (c *Cover) Xor(s1 Cover) *Cover {
	*c = Xor(*c, s1)
	return c
}

func (c *Cover) XorCube(s1 Cube) *Cover {
	*c = XorCube(*c, s1)
	return c
}

func (c *Cover) XorBool(val int) *Cover {
	*c = XorBool(*c, val)
	return c
}

func (c *Cover) Marshal(buff *bytes.Buffer) error {
	for _, s := range c.Cubes {
		s.Marshal(buff)
	}
}

func (m *Cover) Debug() string {
	result := ""
	for i := 0; i < m.size(); i++ {
		if i != 0 {
			result += " "
		}
		result += m.Cubes[i].Debug()
	}
	if len(m.Cubes) == 0 {
		result += "0"
	}

	return result
}

// Run the espresso minimization heuristic algorithm.
func Espresso(F, D, R *Cover) {
	always := R.Supercube()
	for i := 0; i < always.Size(); i++ {
		always.values[i] = ~always.values[i]
	}

	Expand(F, R, always)
	Irredundant(F)
	cost := F.Area()
	oldCost := -1
	for oldCost < 0 || cost < oldCost {
		Reduce(F)
		expand(F, R, always)
		Irredundant(F)

		oldCost = cost
		cost = F.Area()
	}
}

func Expand(F, R *Cover, always *Cube) {
	weight := Weights(F)
	sort.Sort(weight)

	for i := 0; i < len(weight); i++ {
		// TODO any time we expand the cube, we need to mark the newly covered cubes as completely redundant, ignore them throughout the expand step and remove them at the end.

		free := Cube{}
		feasibleCube := F[weight[i].second]
		first := true
		for first || guided(F, weight[i].second, free) {
			free = Essential(F, R, weight[i].second, always)

			for feasibleCube.Size() > 0 {
				F[weight[i].second] = feasibleCube
				free = Essential(F, R, weight[i].second, always)
				feasibleCube = Feasible(F, R, weight[i].second, free)
			}

			free = Essential(F, R, weight[i].second, always)
			first = false
		}
	}
}

type weight struct {
	first uint32
	second uint32
}

func weights(F *Cover) []weight {
	result := make([]weight, F.Size())

	for i := 0; i < F.Size(); i++ {
		result[i].second = i

		for j := i; j < F.Size(); j++ {
			count := uint32(0)
			size := min(F[i].Size(), F[j].Size())
			k := 0
			for ; k < size; k++ {
				count += CountOnes(F[i].values[k] & F[j].values[k])
			}
			for ; k < F[i].Size(); k++ {
				count += CountOnes(F[i].values[k])
			}
			for ; k < F[j].Size(); k++ {
				count += CountOnes(F[j].values[k])
			}

			if i == j {
				result[i].first += count
			} else {
				result[i].first += count
				result[j].first += count
			}
		}
	}

	return result
}

func Essential(F, R *Cover, c int, always *Cube) {
	free := Cube{
		Values: make([]uint32, F.Cubes[c].Size()),
	}
	for j := 0; j < F.Cubes[c].Size() && j < always.Size(); j++ {
		/* any part which does not appear in any cube in the inverse may
		 * always be raised in the one we are expanding. So raise those parts
		 * and remove them from the free list.
		 */
		free.Values[j] = ~F.Cubes[c].Values[j] & ~always.Values[j]
		F.Cubes[c].Values[j] |= always.Values[j]
	}
	for j := always.Size(); j < F[c].Size(); j++ {
		free.Values[j] = ~F.Cubes[c].Values[j]
	}

	// Find parts that can never be raised
	for j := 0; j < R.size(); j++ {
		// if any cube in the inverse is distance 1 from the cube we are
		// expanding, then all of the parts of the conflicting variable which
		// are one in that cube may never be raised in the one we are expanding.
		size := min(free.size(), R[j].size())
		conflict := 0
		mask := uint32(0)
		count := 0
		for k := 0; k < size && count < 2; k++ {
			// AND to get the intersection
			a := ~free.values[k] & R[j].values[k]
			// OR to find any pairs that are both 0
			a = (~(a | (a >> 1))) & 0x55555555

			if a > 0 {
				// Save the location of the conflicting 1's
				mask = (a | (a << 1)) & R[j].values[k]
				conflict = k

				// count the number of bits set to 1 (derived from Hacker's Delight)
				a = (a & 0x33333333) + ((a >> 2) & 0x33333333)
				a = (a & 0x0F0F0F0F) + ((a >> 4) & 0x0F0F0F0F)
				a += (a >> 8)
				a += (a >> 16)
				count += a & 0x0000003F
			}
		}

		// distance is 1, we need to remove the conflicting 1's from the free set.
		if count == 1 {
			free.values[conflict] &= ~mask
		}
	}

	return free
}

func Feasible(F, R *Cube, c int, free *Cube) Cube {
	overexpanded := Supercube(F.Cubes[c], free)

	feasiblyCovered := Cover{}
	for j := 0; j < F.size(); j++ {
		if j != c && F.Cubes[j].IsSubsetOf(overexpanded) && !F.Cubes[j].IsSubsetOf(F.Cubes[c]) {
			test := Supercube(F.Cubes[j], F.Cubes[c])
			if AreMutex(test, R) {
				feasiblyCovered.Cubes = append(feasiblyCovered.Cubes, test)
			}
		}
	}

	maxCoverCount := 0
	maxFeasibleIndex := 0
	for j := 0; j < feasiblyCovered.Size(); j++ {
		coverCount := 0
		for k := 0; k < feasiblyCovered.Size(); k++ {
			if j != k && feasiblyCovered.Cubes[k].IsSubsetOf(feasiblyCovered[j]) {
				coverCount++
			}
		}

		if coverCount > maxCoverCount {
			maxCoverCount = coverCount
			maxFeasibleIndex = j
		}
	}

	if feasiblyCovered.Size() > 0 {
		return feasiblyCovered[maxFeasibleIndex]
	}
	return Cube{}
}

func Guided(F *Cover, c int, free *Cube) bool {
	overexpanded := Supercube(F.Cubes[c], free)

	covered := make([]int, F.Size())
	for j := 0; j < F.size(); j++ {
		if F.Cubes[j].IsSubsetOf(overexpanded) {
			covered[j] = j
		}
	}

	if len(covered) > 0 {
		maxCovered := 0
		maxCoveredMask := uint32(0)
		maxCoveredCount := 0
		for j := 0; j < free.Size(); j++ {
			if free.Values[j] != 0 {
				// TODO I'm sure there is a faster way to do this than just scanning all 32 or 64 bits... look at the log2i function for an example
				for k := uint32(1); k > 0; k <<= 1 {
					if (k & free.values[j]) != 0 {
						covered_count := 0
						for l := 0; l < len(covered); l++ {
							if j >= F.Cubes[covered[l]].Size() || (k & F.Cubes[covered[l]].Values[j]) > 0 {
								coveredCount++
							}
						}

						if coveredCount > maxCoveredCount {
							maxCovered = j
							maxCoveredMask = k
							maxCoveredCount = coveredCount
						}
					}
				}
			}
		}

		if maxCoveredCount > 0 {
			F.Cubes[c].Values[maxCovered] |= maxCoveredMask
			return true
		}
		return false
	}
	return false
}

func Reduce(F *Cover) {
	if F.Cubes.size() > 0 {
		random_shuffle(F.begin(), F.end())

		c := F.Cubes[len(F.Cubes)-1]
		F.Cubes = F.Cubes[0:len(F.Cubes)-1]

		for i := 0; i < F.Size(); i++ {
			s := F.Cubes[i]
			F.Cubes[i] = Intersect(c, SupercubeOfComplement(CofactorCube(F, c)))
			c = s
		}

		F.Cubes = append(F.Cubes, Intersect(c, SupercubeOfComplement(CofactorCube(F, c))))
	}
}

func Irredundant(F *Cover) {
	if len(F.Cubes) > 1 {
		relativelyEssential := Cover{}
		relativelyRedundant = []int{}

		test := F.Clone()
		test.Cubes = test.Cubes[0:len(test.Cubes)-1]

		for i := F.Size()-1; i >= 0; i-- {
			if F.Cubes[i].IsSubsetOf(test) {
				relativelyRedundant = append(relativelyRedundant, i)
			} else {
				relativelyEssential = append(relativelyEssential, F.Cubes[i].Clone())
			}

			if i != 0 {
				test.Cubes[i-1] = F.Cubes[i].Clone()
			}
		}

		for i := 0; i < len(relativelyRedundant); i++ {
			if !F[relatively_redundant[i]].IsSubsetOf(relativelyEssential) {
				relativelyEssential.Cubes = append(relativelyEssential.Cubes, F.Cubes[relativelyRedundant[i]])
			}
		}

		*F = relativelyEssential
	}
}

func Mergible(c1, c2 *Cover) bool {
	for i := 0; i < len(c1.Cubes); i++ {
		for j := 0; j < len(c2.Cubes); j++ {
			if Mergible(c1.Cubes[i], c2.Cubes[j]) {
				return true
			}
		}
	}

	return false
}

func LocalAssign(s1 *Cover, s2 *Cube, stable bool) Cover {
	result := NewCover(s1.Size())
	for i := 0; i < s1.Size(); i++ {
		result.PushBack(LocalAssign(s1.Cubes[i], s2, stable))
	}

	return result
}

func LocalAssign(s1 *Cube, s2 *Cover, stable bool) Cover {
	result := NewCover(s2.Size())
	for i := 0; i < s2.size(); i++ {
		result.PushBack(LocalAssign(s1, s2.cubes[i], stable))
	}

	return result
}

func LocalAssign(s1 *Cover, s2 *Cover, stable bool) Cover {
	result := NewCover(s1.Size()*s2.Size())
	for i := 0; i < s1.size(); i++ {
		for j := 0; j < s2.size(); j++ {
			result.PushBack(LocalAssign(s1.cubes[i], s2.cubes[j], stable))
		}
	}

	return result
}

func RemoteAssign(s1 *Cover, s2 *Cube, stable bool) Cover {
	result := Cover{
		Cubes: make([]Cube, s1.Size()),
	}
	for i := 0; i < s1.Size(); i++ {
		result.Cubes[i] = RemoteAssign(s1.Cubes[i], s2, stable)
	}

	return result
}

func RemoteAssign(s1 *Cube, s2 *Cover, stable bool) Cover {
	result := Cover{
		Cubes: make([]Cube, s2.Size()),
	}
	for i := 0; i < s2.size(); i++ {
		result.Cubes[i] = RemoteAssign(s1, s2.cubes[i], stable)
	}

	return result
}

func RemoteAssign(s1 *Cover, s2 *Cover, stable bool) Cover {
	result := Cover{
		Cubes: make([]Cube, s1.Size()*s2.Size()),
	}

	for i := 0; i < s1.size(); i++ {
		for j := 0; j < s2.size(); j++ {
			result.Cubes[i*s2.Size() + j] = RemoteAssign(s1.cubes[i], s2.cubes[j], stable)
		}
	}

	return result
}

func PassesGuard(encoding, global *Cube, guard *Cover, total *Cube) int {
	result := Cube{}
	pass := -1
	for i := 0; i < len(guard.Cubes); i++ {
		temp := PassesGuard(encoding, global, guard.Cubes[i])
		if temp > pass {
			result = guard.Cubes[i]
			pass = temp
		} else if temp == pass && temp != -1 {
			result &= guard.Cubes[i]
		}
	}

	if total != NULL {
		*total = result.Xoutnulls()
	}

	return pass
}

func ViolatesConstraint(encoding *Cube, constraint *Cover) bool {
	return AreMutex(encoding.Xoutnulls(), constraint)
}

func PassesConstraint(encoding, constraint *Cover) []int {
	pass := []int{}
	for i := 0; i < encoding.Size(); i++ {
		if !ViolatesConstraint(encoding.Cubes[i], constraint) {
			pass = append(pass, i)
		}
	}
	return pass
}

func VacuousAssign(encoding *Cube, assignment *Cover, stable bool) bool {
	for i := 0; i < assignment.Size(); i++ {
		if VacuousAssign(encoding, assignment.Cubes[i], stable) {
			return true
		}
	}

	return false
}

func Not(s1 Cover) Cover {
	// Check for empty function
	if s1.IsNull() {
		return NewCoverBool(1)
	}

	// Check for universal cube
	for i := 0; i < s1.Size(); i++ {
		if s1[i].IsTautology() {
			return Cover{}
		}
	}

	// DeMorgans if only one cube
	if s1.Size() == 1 {
		return Not(s1[0])
	}

	binateRank := []rank{}
	for i := 0; i < s1.size(); i++ {
		if len(binateRank) < s1[i].size()*16 {
			binateRank = append(binateRank, make([]rank, s1[i].Size()*16-len(binateRank))...)
		}

		for j := 0; j < s1[i].Size()*16; j++ {
			val := s1[i].Get(j)
			if val == 0 {
				binateRank[j].first++
			} else if val == 1 {
				binateRank[j].second++
			}
		}
	}

	for i := 0; i < len(binateRank); i++ {
		// Column of all zeros
		if binateRank[i].first == s1.Size() {
			Fc := Not(Cofactor(s1, i, 0))
			Fc.Cubes = append(Fc.Cubes, NewCubeLiteral(i, 1))
			sort.Sort(Fc.Cubes)
			return Fc
		} else if binateRank[i].second == s1.Size() {
			Fc := Not(Cofactor(s1, i, 1))
			Fc.Cubes = append(Fc.Cubes, NewCubeLiteral(i, 0))
			sort.Sort(Fc.Cubes)
			return Fc
		} else {
			binateRank[i].first += binateRank[i].second
			binateRank[i].second = i
		}
	}

	Fc1 := Cover{}
	Fc2 := Cover{}
	uid := MaxElement(binateRank)

	Fc1 = Not(Cofactor(s1, uid.second, 0))
	Fc2 = Not(Cofactor(s1, uid.second, 1))

	sort.Sort(Fc1.Cubes)
	sort.Sort(Fc2.Cubes)

	if (Fc1.Size() + Fc2.Size())*s1.Size() <= Fc1.Size()*Fc2.Size() {
		return MergeComplementA2(uid.second, Fc1, Fc2, s1)
	}
	return MergeComplementA1(uid.second, Fc1, Fc2, s1)
}

func MergeComplementA1(uid int, s0, s1, F *Cover) Cover {
	result := Cover{}

	i := 0
	j := 0
	for i < s0.Size() || j < s1.Size() {
		if j >= s1.size() || (i < s0.size() && s0[i] < s1[j]) {
			subsetFound = AreMutex(s0[i], F)
			for k := j; k < s1.Size() && !subsetFound; k++ {
				subsetFound = s0[i].IsSubsetOf(s1[k])
			}

			result.Cubes = append(result.Cubes, s0[i])

			if !subset_found {
				result.Cubes[len(result.Cubes)-1].Set(uid, 0)
			}
			i++
		} else if i >= s0.Size() || (j < s1.Size() && s1[j] < s0[i]) {
			subsetFound := AreMutex(s1[j], F)
			for k := i; k < s0.size() && !subset_found; k++ {
				subsetFound = s1[j].IsSubsetOf(s0[k])
			}

			result.Cubes = append(result.Cubes, s1[j])

			if !subsetFound {
				result.Cubes[len(result.Cubes)-1].set(uid, 1)
			}
			j++
		} else {
			result.push_back(s0[i])
			i++
			j++
		}
	}

	return result
}

func MergeComplementA2(uid int, s0, s1, F *Cover) Cover {
	result := Cover{}

	i := 0
	j := 0
	for i < s0.size() || j < s1.size() {
		if j >= s1.size() || (i < s0.size() && s0[i] < s1[j]) {
			restriction := Cube{}
			set := false
			for k := 0; k < F.Size(); k++ {
				if Distance(s0[i], F[k]) == 1 {
					if set {
						restriction.Supercube(F.Cubes[k])
					} else {
						restriction = F.Cubes[k].Clone()
						set = true
					}
				}
			}

			if !set {
				return NewCoverBool(1)
			}

			toadd := s0.Cubes[i].Clone()
			if toadd.size() > restriction.size() {
				restriction.ExtendX(toadd.Size() - restriction.Size())
			}

			for k := 0; k < restriction.size(); k++ {
				restriction.Values[k] = ~restriction.Values[k]
			}

			toadd.Supercube(restriction)
			toadd.Set(uid, 0)

			result.Cubes = append(result.Cubes, toadd)
			i++
		} else if i >= s0.size() || (j < s1.size() && s1[j] < s0[i]) {
			restriction := Cube{}
			set := false
			for k := 0; k < F.size(); k++ {
				if distance(s1.Cubes[j], F.Cubes[k]) == 1 {
					if set {
						restriction.Supercube(F.Cubes[k])
					} else {
						restriction = F.Cubes[k]
						set = true
					}
				}
			}

			if !set {
				return NewCoverBool(1)
			}

			toadd := s1.Cubes[j].Clone()
			if toadd.size() > restriction.size() {
				restriction.ExtendX(toadd.Size() - restriction.Size())
			}

			for k := 0; k < restriction.Size(); k++ {
				restriction.Values[k] = ~restriction.Values[k]
			}

			toadd.Supercube(restriction)
			toadd.Set(uid, 1)
			result.Cubes = append(result.Cubes, toadd)
			j++
		} else {
			result.Cubes = append(result.Cubes, s0.Cubes[i].Clone())
			i++
			j++
		}
	}

	return result
}

func Intersect(s1, s2 Cover) Cover {
	result := Cover{
		Cubes: make([]Cube, 0, s1.Size()*s2.Size()),
	}
	for i := 0; i < s1.Size(); i++ {
		for j := 0; j < s2.Size(); j++ {
			result.Cubes = append(result.Cubes, Cube{
				Values: make([]uint32, 0, max(s1[i].Size(), s2[j].Size())),
			})

			valid := true
			m0 := min(s1[i].size(), s2[j].size())
			for k := 0; k < m0 && valid; k++ {
				result.BackPtr().PushBack(s1[i].Values[k] & s2[j].Values[k])
				valid = ((result.Back().Back() | (result.Back().Back() >> 1)) | 0xAAAA_AAAA) == 0xFFFF_FFFF
			}

			if valid {
				for k := m0; k < s1[i].Size(); k++ {
					result.BackPtr().PushBack(s1[i].values[k])
				}
				for k := m0; k < s2[j].Size(); k++ {
					result.BackPtr().PushBack(s2[j].values[k])
				}
			} else {
				result.PopBack(1)
			}

			if result.size() >= 128 {
				result.Minimize()
			}
		}
	}

	result.Minimize()

	return result
}

func Intersect(s1 Cover, s2 Cube) Cover {
	for i := 0; i < s1.Size(); i++ {
		s1[i].Intersect(s2)
	}
	return s1
}

func Intersect(s1 Cube, s2 Cover) Cover {
	for i := 0; i < s2.size(); i++ {
		s2[i].Intersect(s1)
	}
	return s2
}

func Itersect(s1 Cover, s2 int) Cover {
	if s2 == 1 {
		return s1
	}
	return Cover{}
}

func Intersect(s1 int, s2 Cover) Cover {
	if s1 == 1 {
		return s2
	}
	return Cover{}
}

func AreMutex(s1 Cover, s2 Cube) bool {
	for i := 0; i < s1.Size(); i++ {
		if !AreMutex(s1[i], s2) {
			return false
		}
	}

	return true
}

func AreMutex(s1, s2 Cover) bool {
	for i := 0; i < s1.Size(); i++ {
		for j := 0; j < s2.Size(); j++ {
			if !AreMutex(s1[i], s2[j]) {
				return false
			}
		}
	}

	return true
}

func AreMutex(s1, s2, s3 Cover) bool {
	for i := 0; i < s1.size(); i++ {
		for j := 0; j < s2.size(); j++ {
			for k := 0; k < s3.size(); k++ {
				if !AreMutex(s1[i], s2[j], s3[k]) {
					return false
				}
			}
		}
	}

	return true
}

func AreMutex(s1, s2, s3, s4 Cover) bool {
	for i := 0; i < s1.size(); i++ {
		for j := 0; j < s2.size(); j++ {
			for k := 0; k < s3.size(); k++ {
				for l := 0; l < s4.size(); l++ {
					if !AreMutex(s1[i], s2[j], s3[k], s4[l]) {
						return false
					}
				}
			}
		}
	}

	return true
}

func Union(s1, s2 Cover) Cover {
	s1.PushBack(s2.Cubes...)
	s1.Minimize()
	return s1
}

func Union(s1 Cover, s2 Cube) Cover {
	s1.PushBack(s2)
	s1.Minimize()
	return s1
}

func Union(s1 Cube, s2 Cover) Cover {
	s2.PushBack(s1)
	s2.Minimize()
	return s2
}

func Union(s1 Cover, s2 int) Cover {
	if s2 == 0 {
		return s1
	}
	return NewCoverBool(1)
}

func Union(s1 int, s2 Cover) Cover {
	if s1 == 0 {
		return s2
	}
	return NewCoverBool(1)
}

func Xor(s1, s2 Cover) Cover {
	return Union(Intersect(s1, Not(s2)), Intersect(Not(s1), s2))
}

func Xor(s1 Cover, s2 Cube) Cover {
	return Union(Intersect(s1, Not(s2)), Intersect(Not(s1), s2))
}

func Xor(s1 Cube, s2 Cover) Cover {
	return Union(Intersect(s1, Not(s2)), Intersect(Not(s1), s2))
}

func Xor(s1 Cover, s2 int) Cover {
	return Union(Intersect(s1, Not(s2)), Intersect(Not(s1), s2))
}

func Xor(s1 int, s2 Cover) Cover {
	return Union(Intersect(s1, Not(s2)), Intersect(Not(s1), s2))
}

func Cofactor(s1 Cover, uid, val int) Cover {
	result := Cover{
		Cubes: make([]Cube, 0, s1.Size()),
	}
	for i := 0; i < s1.size(); i++ {
		cmp := s1[i].Get(uid)
		if cmp != 1-val {
			result.PushBack(s1[i])
			result.BackPtr().Set(uid, 2)
		}
	}

	return result
}

func Cofactor(s1 Cover, s2 Cube) Cover {
	result := Cover{
		Cubes: make([]Cube, 0, s1.Size()),
	}

	for i := 0; i < s1.size(); i++ {
		entry := Cube{
			Values: make([]uint32, 0, s1[i].Size()),
		}

		valid := true
		j := 0
		for j = 0; j < s1[i].size() && j < s2.size() && valid; j++ {
			b := s2.values[j] & s1[i].values[j]
			b = ~(b | (b >> 1)) & 0x55555555

			if b != 0 {
				valid = false
			} else {
				a := (s2.values[j] ^ (s2.values[j] >> 1)) & 0x55555555
				a = a | (a << 1)
				entry.PushBack(s1[i].values[j] | a)
			}
		}

		if valid {
			for ; j < s1[i].size(); j++ {
				entry.PushBack(s1[i].values[j])
			}
			result.PushBack(entry)
		}
	}

	return result
}

func SupercubeOfComplement(s Cover) Cube {
	// Check for empty function
	if s.size() == 0 {
		return Cube{}
	}

	// Check for universal cube
	for i := 0; i < s.Size(); i++ {
		if s[i].is_tautology() {
			return NewCubeBool(0)
		}
	}

	// only one cube
	if s.Size() == 1 {
		return SupercubeOfComplement(s[0])
	}

	binateRank := []rank{}
	for i := 0; i < s.Size(); i++ {
		if len(binateRank) < len(s.Cubes[i])*16 {
			binateRank = append(binateRank, make([]rank, s.Cubes[i].Size()*16-len(binateRank))...)
		}

		for j := 0; j < len(s.Cubes[i])*16; j++ {
			val := s.Cubes[i].Get(j)
			if val == 0 {
				binateRank[j].first++
			} else if val == 1 {
				binateRank[j].second++
			}
		}
	}

	columns := []rank{}
	for i := 0; i < len(binateRank); i++ {
		// Column of all zeros
		if binateRank[i].first == s.size() {
			columns = append(column, rank{i, 0})
		} else if binateRank[i].second == s.size() {
			columns = append(column, rank{i, 1})
		}

		binateRank[i].first += binateRank[i].second
		binateRank[i].second = i
	}

	if columns.size() > 1 {
		return Cube{}
	}

	uid := MaxElement(binate_rank.begin(), binate_rank.end())

	if uid.first > 0 {
		Fc1 := SupercubeOfComplement(Cofactor(s, uid.second, 0))
		Fc2 := SupercubeOfComplement(Cofactor(s, uid.second, 1))

		Fc1.SvIntersect(uid.second, 0)
		Fc2.SvIntersect(uid.second, 1)

		return Supercube(Fc1, Fc2)
	}

	result := Cube{}
	for i := 0; i < s.size(); i++ {
		result.Intersect(SupercubeOfComplement(s[i]))
	}

	return result
}

func Equal(s1 Cover, s2 Cover) bool {
	return AreMutex(s1, Not(s2)) && AreMutex(Not(s1), s2)
}

func Equal(s1 Cover, s2 Cube) bool {
	return AreMutex(s1, Not(s2)) && AreMutex(Not(s1), s2)
}

func Equal(s1 Cube, s2 Cover) bool {
	return AreMutex(s1, Not(s2)) && AreMutex(Not(s1), s2)
}

func Equal(s1 Cover, s2 int) bool {
	return (s2 == 0 && s1.IsNull()) || (s2 == 1 && s1.IsTautology())
}

func Equal(s1 int, s2 Cover) bool {
	return (s1 == 0 && s2.IsNull()) || (s1 == 1 && s2.IsTautology())
}

func NotEqual(s1, s2 Cover) bool {
	return !AreMutex(s1, Not(s2)) || !AreMutex(Not(s1), s2)
}

func NotEqual(s1 Cover, s2 Cube) bool {
	return !AreMutex(s1, Not(s2)) || !AreMutex(Not(s1), s2)
}

func NotEqual(s1 Cube, s2 Cover) bool {
	return !AreMutex(s1, Not(s2)) || !AreMutex(Not(s1), s2)
}

func NotEqual(s1 Cover, s2 int) bool {
	return !(s2 == 0 && s1.IsNull()) && !(s2 == 1 && s1.IsTautology())
}

func NotEqual(s1 int, s2 Cover) bool {
	return !(s1 == 0 && s2.IsNull()) && !(s1 == 1 && s2.IsTautology())
}

