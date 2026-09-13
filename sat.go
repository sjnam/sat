//line sat.w:50
package sat

import (
	"fmt"
	"iter"
	"strconv"
)

//line sat.w:72
type Lit uint32

//line sat.w:103
type Solver struct {

//line sat.w:113
	names []string       // |names[v]|는 변수 |v|의 이름
	index map[string]int // 이름에서 변수 번호로

//line sat.w:132
	cells []Lit // 받아들인 모든 절의 리터럴
	start int   // 지금 쌓는 절이 |cells|에서 시작하는 자리

//line sat.w:141
	stamp  []int // 변수가 절 |serial|에 나왔으면 $\pm$|serial|
	serial int   // 지금까지 시작한 절의 수

//line sat.w:153
	clauses  int  // 받아들인 절의 수
	unaries  int  // 그 가운데 리터럴이 하나인 절의 수
	binaries int  // 리터럴이 둘인 절의 수
	empty    bool // 빈 절을 받았는가

//line sat.w:105
}

//line sat.w:124
const (
	firstLit Lit = 1 << 31   // 절의 첫 리터럴에 붙이는 표
	maxVar       = 1<<30 - 1 // 변수 번호의 상한
)

//line sat.w:77
func Pos(v int) Lit { return Lit(v) << 1 }

func Neg(v int) Lit { return Lit(v)<<1 | 1 }

//line sat.w:84
func (l Lit) Var() int { return int(l >> 1) }

func (l Lit) Not() Lit { return l ^ 1 }

func (l Lit) IsNeg() bool { return l&1 != 0 }

//line sat.w:161
func New() *Solver {
	return &Solver{names: []string{""}, stamp: []int{0}, index: map[string]int{}}
}

//line sat.w:169
func (s *Solver) NewVar() Lit {
	v := len(s.names)
	if v > maxVar {
		panic("sat: 변수가 너무 많다")
	}
	s.names = append(s.names, "")
	s.stamp = append(s.stamp, 0)
	return Pos(v)
}

//line sat.w:183
func (s *Solver) Lookup(name string) Lit {
	if v, ok := s.index[name]; ok {
		return Pos(v)
	}

//line sat.w:200
	if name == "" || name[0] == '~' {
		panic(fmt.Sprintf("sat: 쓸 수 없는 이름 %q", name))
	}
	for i := 0; i < len(name); i++ {
		if name[i] <= ' ' || name[i] > '~' {
			panic(fmt.Sprintf("sat: 쓸 수 없는 이름 %q", name))
		}
	}

//line sat.w:188
	l := s.NewVar()
	s.names[l.Var()] = name
	s.index[name] = l.Var()
	return l
}

//line sat.w:212
func (s *Solver) NumVars() int { return len(s.names) - 1 }

func (s *Solver) NumClauses() int { return s.clauses }

func (s *Solver) NumLiterals() int { return len(s.cells) }

//line sat.w:222
func (s *Solver) Name(v int) string {
	if s.names[v] == "" {
		return "#" + strconv.Itoa(v)
	}
	return s.names[v]
}

func (s *Solver) LitName(l Lit) string {
	if l.IsNeg() {
		return "~" + s.Name(l.Var())
	}
	return s.Name(l.Var())
}

//line sat.w:249
func (s *Solver) beginClause() {
	s.serial++
	s.start = len(s.cells)
}

//line sat.w:263
func (s *Solver) addLit(l Lit) bool {
	v := l.Var()
	if st := s.stamp[v]; st == s.serial || st == -s.serial {
		if (st > 0) == l.IsNeg() {
			s.cells = s.cells[:s.start]
			return false
		}
		return true
	}

//line sat.w:277
	if l.IsNeg() {
		s.stamp[v] = -s.serial
	} else {
		s.stamp[v] = s.serial
	}
	if len(s.cells) == s.start {
		l |= firstLit
	}
	s.cells = append(s.cells, l)

//line sat.w:273
	return true
}

//line sat.w:290
func (s *Solver) endClause() {
	switch len(s.cells) - s.start {
	case 0:
		s.empty = true
		return
	case 1:
		s.unaries++
	case 2:
		s.binaries++
	}
	s.clauses++
}

//line sat.w:307
func (s *Solver) AddClause(lits ...Lit) {
	s.beginClause()
	for _, l := range lits {

//line sat.w:322
		if v := l.Var(); v == 0 || v >= len(s.names) {
			panic(fmt.Sprintf("sat: 없는 변수의 리터럴 %d", uint32(l)))
		}

//line sat.w:311
		if !s.addLit(l) {
			return
		}
	}
	s.endClause()
}

//line sat.w:330
func (s *Solver) Clauses() iter.Seq[[]Lit] {
	return func(yield func([]Lit) bool) {
		for i := 0; i < len(s.cells); {
			j := i + 1
			for j < len(s.cells) && s.cells[j]&firstLit == 0 {
				j++
			}
			c := make([]Lit, j-i)
			for k := range c {
				c[k] = s.cells[i+k] &^ firstLit
			}
			if !yield(c) {
				return
			}
			i = j
		}
	}
}
