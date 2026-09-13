//line sat.w:58
package sat

import (
	"fmt"
	"iter"
	"strconv"
)

//line sat.w:80
type Lit uint32

//line sat.w:112
type Solver struct {

//line sat.w:122
	names []string       // |names[v]|는 변수 |v|의 이름
	index map[string]int // 이름에서 변수 번호로

//line sat.w:141
	cells []Lit // 받아들인 모든 절의 리터럴
	start int   // 지금 쌓는 절이 |cells|에서 시작하는 자리

//line sat.w:150
	stamp  []int // 변수가 절 |serial|에 나왔으면 $\pm$|serial|
	serial int   // 지금까지 시작한 절의 수

//line sat.w:162
	clauses  int  // 받아들인 절의 수
	unaries  int  // 그 가운데 리터럴이 하나인 절의 수
	binaries int  // 리터럴이 둘인 절의 수
	empty    bool // 빈 절을 받았는가

//line sat.w:171
	Params Params     // 푸는 방식을 정하는 매개변수
	stats  Stats      // 마지막 풀이의 통계
	model  []Lit      // 마지막 풀이에서 찾은 해, 트레일 차례대로
	truth  []bool     // |truth[v]|는 그 해에서 변수 |v|의 값
	failed []Lit      // 마지막 풀이를 만족할 수 없게 한 가정들
	state  *cdclState // 풀이 사이에 간직하는 상태, 없으면 nil

//line sat.w:183
	SimplifyParams SimplifyParams // 전처리의 매개변수
	simpStats      SimplifyStats  // 마지막 전처리의 통계
	pre            *preprocessed  // 전처리 결과, 없으면 nil

//line sat.w:114
}

//line sat.w:133
const (
	firstLit Lit = 1 << 31   // 절의 첫 리터럴에 붙이는 표
	maxVar       = 1<<30 - 1 // 변수 번호의 상한
)

//line sat.w:85
func Pos(v int) Lit { return Lit(v) << 1 }

func Neg(v int) Lit { return Lit(v)<<1 | 1 }

//line sat.w:92
func (l Lit) Var() int { return int(l >> 1) }

func (l Lit) Not() Lit { return l ^ 1 }

func (l Lit) IsNeg() bool { return l&1 != 0 }

//line sat.w:191
func New() *Solver {
	return &Solver{names: []string{""}, stamp: []int{0}, index: map[string]int{},
		Params: defaultParams, SimplifyParams: defaultSimplifyParams}
}

//line sat.w:200
func (s *Solver) NewVar() Lit {
	v := len(s.names)
	if v > maxVar {
		panic("sat: 변수가 너무 많다")
	}
	s.names = append(s.names, "")
	s.stamp = append(s.stamp, 0)
	return Pos(v)
}

//line sat.w:214
func (s *Solver) Lookup(name string) Lit {
	if v, ok := s.index[name]; ok {
		return Pos(v)
	}

//line sat.w:231
	if name == "" || name[0] == '~' {
		panic(fmt.Sprintf("sat: 쓸 수 없는 이름 %q", name))
	}
	for i := 0; i < len(name); i++ {
		if name[i] <= ' ' || name[i] > '~' {
			panic(fmt.Sprintf("sat: 쓸 수 없는 이름 %q", name))
		}
	}

//line sat.w:219
	l := s.NewVar()
	s.names[l.Var()] = name
	s.index[name] = l.Var()
	return l
}

//line sat.w:243
func (s *Solver) NumVars() int { return len(s.names) - 1 }

func (s *Solver) NumClauses() int { return s.clauses }

func (s *Solver) NumLiterals() int { return len(s.cells) }

//line sat.w:253
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

//line sat.w:283
func (s *Solver) beginClause() {
	s.pre = nil
	s.serial++
	s.start = len(s.cells)
}

//line sat.w:298
func (s *Solver) addLit(l Lit) bool {
	v := l.Var()
	if st := s.stamp[v]; st == s.serial || st == -s.serial {
		if (st > 0) == l.IsNeg() {
			s.cells = s.cells[:s.start]
			return false
		}
		return true
	}

//line sat.w:312
	if l.IsNeg() {
		s.stamp[v] = -s.serial
	} else {
		s.stamp[v] = s.serial
	}
	if len(s.cells) == s.start {
		l |= firstLit
	}
	s.cells = append(s.cells, l)

//line sat.w:308
	return true
}

//line sat.w:325
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

//line sat.w:342
func (s *Solver) AddClause(lits ...Lit) {
	s.beginClause()
	for _, l := range lits {

//line sat.w:357
		if v := l.Var(); v == 0 || v >= len(s.names) {
			panic(fmt.Sprintf("sat: 없는 변수의 리터럴 %d", uint32(l)))
		}

//line sat.w:346
		if !s.addLit(l) {
			return
		}
	}
	s.endClause()
}

//line sat.w:365
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
