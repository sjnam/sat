\input kotexgweb

\def\title{SAT}

@* 들어가며.
크누스는 {\sl The Art of Computer Programming\/} 7.2.2.2절 ``만족 가능성''을
준비하면서 SAT 풀이기를 한 벌 짰다. 번호가 \.{SAT0}에서 \.{SAT13}까지 붙은 그
프로그램들을 그는 ``제 공부를 위해'' 모은다고 했다. 모두 같은 입력을 받아 같은
형식으로 답하게 해 놓고, 여러 방법이 실제로 어떻게 도는지 나란히 재어 보려는
것이다. 논문을 대체로 나온 차례대로 읽으며 한 판씩 새로 썼기에, 번호를 따라
읽으면 SAT 풀이의 반세기가 지나간다. 1960년대식 되추적(\.{SAT0})이 있고,
감시 리터럴(\.{SAT0W}, \.{SAT10})과 미리보기(\.{SAT11})가 있고, 마지막에
충돌에서 배우는 절(\.{SAT13})이 온다.
@^Knuth, Donald Ervin@>

그는 \.{SAT13}에 ``행운의 번호''라는 말을 붙이며 이것이 대부분의 문제에서 가장
빠르기를 바랐고, 그 바람은 이루어졌다. 책의 알고리즘~7.2.2.2C가 된 이 프로그램은
E\'en과 S\"orensson의 MiniSat, Biere의 PicoSat을 본보기로 삼은 CDCL(conflict driven
clause learning) 풀이기다. 최신 풀이기의 온갖 장식까지 갖추지는 않았지만 CDCL의
큰 줄기는 모두 들어 있다.
@^SAT13@>

@ 문제는 크누스의 프로그램이 하나같이 {\it 명령\/}이라는 데 있다. 절을 표준
입력으로 받아 답을 표준 출력에 찍고 끝난다. 상태는 모두 전역 변수에 있고, 알맹이는
거대한 |main| 하나에 |goto|로 엮여 있다. 다른 프로그램이 제 문제를 절로 옮겨
풀려면 글자로 적어 파이프에 흘려 넣는 수밖에 없다.

나는 SAT 풀이기를 {\it 꾸러미\/}로 갖고 싶다. 조합 문제든 회로 검증이든, 절을
짓는 쪽이 \GO/ 값으로 절을 넘기고 \GO/ 값으로 답을 받는 꾸러미 말이다. 그래서
2026년 9월에 \.{SAT13}을 \GO/로 옮기기 시작했다.

원칙은 하나다. {\it mem 수가 원본과 똑같이 나오게 옮긴다.} 크누스의 프로그램은
64비트 낱말 하나를 읽거나 쓸 때마다 mem을 하나씩 센다. 같은 입력과 같은 매개변수에서
\CEE/ 원본과 mem 수가 하나도 틀리지 않는다면, 옮긴 것이 맞다는 증거로 그보다 강한
것을 찾기 어렵다. 이 원칙은 뜻밖의 곳까지 손을 뻗는다. 변수에 번호를 매기는 차례,
절을 쌓는 차례까지 원본과 같아야 하기 때문이다. 이 글의 절 쌓기가 조금 유난스러워
보인다면 그 까닭이다.

@ 꾸러미는 세 편의 글로 짓는다.
\smallskip
\item{$\bullet$} 첫째 글 \.{sat.w}는 지금 읽는 이 글이다. 리터럴을 적는 법과, 절을
받아 쌓아 두는 풀이기의 겉모습을 담는다.
\item{$\bullet$} 둘째 글 \.{io.w}는 크누스의 절 형식과 DIMACS 형식을 읽는다.
\item{$\bullet$} 셋째 글 \.{cdcl.w}는 \.{SAT13}의 알맹이다. 쌓아 둔 절로 진짜
자료 구조를 짓고 푼다. (다음 차례다.)
\smallskip\noindent
어느 글이나 혼자 읽을 수 있게 썼다. 이 글의 뼈대는 다음과 같다.

@c
package sat

import (
	"fmt"
	"iter"
	"strconv"
)

@<자료 구조@>

@<함수들@>

@* 리터럴.
변수에는 1부터 차례로 번호를 붙인다. 크누스를 따라, 번호가 $k$인 변수의 두
리터럴을 정수 $2k$와 $2k+1$로 적는다. 앞의 것이 $v$이고 뒤의 것이 $\bar v$다.

이렇게 적으면 좋은 점이 셋 있다. 부정은 맨 아래 비트를 뒤집는 일이고, 변수는
오른쪽으로 한 칸 미는 일이다. 리터럴을 그대로 배열의 첨자로 쓸 수 있다. 그리고
0과 1은 어떤 리터럴도 아니므로 0을 ``없음''의 표시로 마음 놓고 쓸 수 있다.
\.{SAT13}은 이 세 가지를 모두 요긴하게 쓴다.

@<자료 구조@>=
type Lit uint32

@ 변수 번호에서 리터럴을 얻는 두 문.

@<함수들@>=
func Pos(v int) Lit { return Lit(v) << 1 }

func Neg(v int) Lit { return Lit(v)<<1 | 1 }

@ 거꾸로 리터럴에서 변수 번호와 부호를 얻는 문, 그리고 리터럴을 뒤집는 문.

@<함수들@>=
func (l Lit) Var() int { return int(l >> 1) }

func (l Lit) Not() Lit { return l ^ 1 }

func (l Lit) IsNeg() bool { return l&1 != 0 }

@* 풀이기.
크누스의 입출력 껍데기는 두 단계로 일한다. 먼저 절을 모두 읽어 ``임시 표''에
쌓아 두고, 다 읽은 다음에야 그 표를 거꾸로 되감으며(unwinding) 진짜 자료 구조를
짓는다. 입력이 얼마나 클지 모르니 \CEE/에서는 이렇게 할 수밖에 없다. 임시 표는
작은 덩어리(chunk)를 필요할 때마다 |malloc|해서 이어 붙인 사슬이다.

\GO/의 조각(slice)은 저절로 자라므로 덩어리 사슬이 필요 없다. 그러나 두 단계로
나누는 짜임새는 그대로 둔다. 되감기 때문에 절이 입력의 {\it 거꾸로\/} 쌓이고,
그 차례가 mem 수에 그대로 드러나기 때문이다. 그래서 이 글의 풀이기는 임시 표만
들고 있고, 진짜 자료 구조는 푸는 순간에 \.{cdcl.w}가 짓는다. 한 번 풀고 난 뒤에
절을 더 보태는 일(점진적 풀이)은 나중에 생각한다.

@<자료 구조@>=
type Solver struct {
	@<|Solver|의 필드@>
}

@ 변수마다 이름이 있을 수 있다. 크누스의 입력에서는 모든 변수가 이름으로만
나타나고, 이름이 처음 나온 차례가 곧 변수 번호다. 원본은 여기에 손수 짠 해시
표를 쓰지만 \GO/에는 사전(map)이 있다. 이름 없이 만든 변수는 빈 문자열을 이름으로
갖고 사전에는 오르지 않는다. 번호가 0인 변수는 없으므로 |names[0]|은 비워 둔다.

@<|Solver|의 필드@>=
names []string       // |names[v]|는 변수 |v|의 이름
index map[string]int // 이름에서 변수 번호로

@ 받아들인 절의 리터럴은 모두 |cells| 하나에 입력 차례대로 늘어놓는다. 절과 절의
경계는 첫 리터럴에 붙인 표 비트 |firstLit|로 안다. 원본도 똑같이 한다. 거기서는
포인터의 낮은 두 비트에 ``부정''과 ``절의 첫 리터럴''을 숨겨 두는데, 우리
리터럴은 이미 맨 아래 비트에 부호를 담고 있으니 맨 위 비트 하나만 빌리면 된다.
그 비트를 빌리는 값으로 변수 번호는 $2^{30}$보다 작아야 한다. 원본의 한계는
$2^{31}$이었다.

@<자료 구조@>=
const (
	firstLit Lit = 1 << 31   // 절의 첫 리터럴에 붙이는 표
	maxVar       = 1<<30 - 1 // 변수 번호의 상한
)

@ 지금 쌓고 있는 절은 |cells[start:]|에 있다.

@<|Solver|의 필드@>=
cells []Lit // 받아들인 모든 절의 리터럴
start int   // 지금 쌓는 절이 |cells|에서 시작하는 자리

@ 한 절 안에 같은 변수가 두 번 나오면 알아차려야 한다. 크누스는 변수마다 도장을
하나씩 두고, 절에 번호를 매겨 그 번호를 찍는다. 양의 리터럴로 나오면 절 번호를,
음의 리터럴로 나오면 그 음수를 찍는다. 절 번호가 늘 새로우니 도장을 지울 필요가
없다.

@<|Solver|의 필드@>=
stamp  []int // 변수가 절 |serial|에 나왔으면 $\pm$|serial|
serial int   // 지금까지 시작한 절의 수

@ 원본은 절을 읽으면서 몇 가지를 센다. 리터럴이 하나인 절과 둘인 절의 수는
\.{SAT13}이 |mem|의 크기를 정할 때 쓴다. 빈 절에 대해서는 크누스와 조금 다르게
한다. 원본은 빈 줄을 ``엄밀히 말하면 만족할 수 없는 절''이라 적어 놓고도 그냥
건너뛰는데, 사람이 손으로 쓰는 입력에서는 빈 줄이 흔하기 때문이다. 크누스 형식을
읽을 때는 나도 빈 줄을 건너뛴다. 하지만 |AddClause|를 인자 없이 부르거나 DIMACS
입력에 빈 절이 있다면, 그것은 누군가 일부러 넣은 빈 절이다. 그런 절이 하나라도
들어오면 식은 만족할 수 없고, 그 사실을 |empty|에 적어 둔다.

@<|Solver|의 필드@>=
clauses  int  // 받아들인 절의 수
unaries  int  // 그 가운데 리터럴이 하나인 절의 수
binaries int  // 리터럴이 둘인 절의 수
empty    bool // 빈 절을 받았는가

@ 새 풀이기를 만드는 문. 번호 0짜리 자리를 미리 채워 둔다.

@<함수들@>=
func New() *Solver {
	return &Solver{names: []string{""}, stamp: []int{0}, index: map[string]int{}}
}

@ 이름 없는 변수를 새로 만들고 그 양의 리터럴을 돌려주는 문. 조합 문제를 절로
옮기는 프로그램은 대개 이 문으로 변수를 만든다.

@<함수들@>=
func (s *Solver) NewVar() Lit {
	v := len(s.names)
	if v > maxVar {
		panic("sat: 변수가 너무 많다")
	}
	s.names = append(s.names, "")
	s.stamp = append(s.stamp, 0)
	return Pos(v)
}

@ 이름으로 변수를 찾되, 없으면 새로 만드는 문. 크누스의 해시 표가 하던 일이다.
돌려주는 것은 양의 리터럴이다.

@<함수들@>=
func (s *Solver) Lookup(name string) Lit {
	if v, ok := s.index[name]; ok {
		return Pos(v)
	}
	@<|name|을 이름으로 쓸 수 있는지 확인한다@>
	l := s.NewVar()
	s.names[l.Var()] = name
	s.index[name] = l.Var()
	return l
}

@ 이름은 크누스의 형식으로 다시 적을 수 있어야 한다. 그러니 빈칸이나 제어 문자가
끼면 안 되고, 부정 표시 \.{\~}로 시작해서도 안 된다. 원본은 이름을 여덟 글자로
묶어 두지만(64비트 낱말 하나에 담으려고) 여기서는 길이를 따지지 않는다. 글자는
원본처럼 ASCII로 한정한다.

@<|name|을 이름으로 쓸 수 있는지 확인한다@>=
if name == "" || name[0] == '~' {
	panic(fmt.Sprintf("sat: 쓸 수 없는 이름 %q", name))
}
for i := 0; i < len(name); i++ {
	if name[i] <= ' ' || name[i] > '~' {
		panic(fmt.Sprintf("sat: 쓸 수 없는 이름 %q", name))
	}
}

@ 몇 가지를 알려 주는 문들. 리터럴의 수는 겹친 리터럴을 걸러 낸 뒤의 수다.

@<함수들@>=
func (s *Solver) NumVars() int { return len(s.names) - 1 }

func (s *Solver) NumClauses() int { return s.clauses }

func (s *Solver) NumLiterals() int { return len(s.cells) }

@ 변수와 리터럴의 이름을 알려 주는 문. 이름 없는 변수는 \.{\#}에 번호를 붙여
부른다. 크누스의 입력에서 \.{\#}로 시작하는 이름은 본 적이 없다.

@<함수들@>=
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

@* 절 쌓기.
절은 세 걸음으로 쌓는다. 절을 시작하고, 리터럴을 하나씩 보태고, 절을 마친다.
한 번에 넘기면 될 것을 굳이 셋으로 나눈 까닭은 원본의 한 가지 버릇 때문이다.

리터럴을 보태다가 절이 늘 참이라는 것이 드러나면(가령 $x\lor\bar x$), 원본은
그 자리에서 |goto|로 빠져나가 줄의 나머지를 {\it 읽지도 않는다}. 그러면 그
뒤에 처음 나오는 이름은 변수로 만들어지지 않는다. 변수 번호는 이름이 처음 나온
차례로 매겨지므로, 번호를 원본과 맞추려면 이 버릇까지 따라야 한다. 그래서 글자를
읽는 쪽이 리터럴을 하나 만들 때마다 곧바로 보태고, 절이 늘 참이 되었다는 답을
받으면 곧바로 읽기를 멈춘다. 이 세 걸음은 |AddClause|, 그리고 \.{io.w}의 두 읽개가
함께 쓴다.

@<함수들@>=
func (s *Solver) beginClause() {
	s.serial++
	s.start = len(s.cells)
}

@ 리터럴 |l|을 지금 쌓는 절에 보태는 문. 절이 늘 참이 되어 버렸으면 절을 통째로
걷어 내고 |false|를 돌려준다. 이때는 |endClause|를 부르면 안 된다.

변수에 이 절의 도장이 이미 찍혀 있다면 두 경우가 있다. 부호가 같으면 겹친 리터럴이니
조용히 버린다. 부호가 다르면 절이 늘 참이다. 도장이 양수인데 |l|이 음이거나,
도장이 음수인데 |l|이 양이면 부호가 다른 것이다. 곧 ``도장이 양수인가''와
``|l|이 음인가''가 같은 답을 내면 부호가 다르다.

@<함수들@>=
func (s *Solver) addLit(l Lit) bool {
	v := l.Var()
	if st := s.stamp[v]; st == s.serial || st == -s.serial {
		if (st > 0) == l.IsNeg() {
			s.cells = s.cells[:s.start]
			return false
		}
		return true
	}
	@<변수 |v|에 도장을 찍고 |l|을 |cells|에 넣는다@>
	return true
}

@ @<변수 |v|에 도장을 찍고...@>=
if l.IsNeg() {
	s.stamp[v] = -s.serial
} else {
	s.stamp[v] = s.serial
}
if len(s.cells) == s.start {
	l |= firstLit
}
s.cells = append(s.cells, l)

@ 절을 마치는 문. 리터럴이 하나도 남지 않았으면 빈 절이다.

@<함수들@>=
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

@ 이제 바깥에 내놓는 문을 쓸 수 있다. 리터럴들 |lits|로 이루어진 절을 보태는 문이다.
겹친 리터럴은 하나만 남기고, 늘 참인 절은 버리고, 인자가 없으면 빈 절로 친다.

@<함수들@>=
func (s *Solver) AddClause(lits ...Lit) {
	s.beginClause()
	for _, l := range lits {
		@<|l|이 이 풀이기의 리터럴인지 확인한다@>
		if !s.addLit(l) {
			return
		}
	}
	s.endClause()
}

@ 남의 풀이기에서 만든 리터럴이나 0 같은 값이 들어오면 여기서 걸린다. 표 비트가
섞인 값도 변수 번호가 터무니없이 커지므로 함께 걸린다.

@<|l|이 이 풀이기의 리터럴인지 확인한다@>=
if v := l.Var(); v == 0 || v >= len(s.names) {
	panic(fmt.Sprintf("sat: 없는 변수의 리터럴 %d", uint32(l)))
}

@ 쌓인 절을 입력 차례대로 하나씩 내놓는 문. 절마다 새 조각을 만들어 주므로 받는
쪽이 마음대로 고쳐도 된다. 절을 다른 형식으로 적어 내거나 시험할 때 쓴다.

@<함수들@>=
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

@* 시험.
시험은 \.{sat\_test.go}로 따로 짜낸다.

@(sat_test.go@>=
package sat

import (
	"slices"
	"testing"
)

@<시험들@>

@ 첫째 시험은 리터럴을 적는 법이 크누스와 같은지 본다. 변수 5의 두 리터럴은
10과 11이어야 한다.

@<시험들@>=
func TestLit(t *testing.T) {
	l := Pos(5)
	if l != 10 || Neg(5) != 11 || l.Not() != Neg(5) || l.Not().Not() != l {
		t.Errorf("리터럴 %d, %d가 10, 11이 아니다", l, Neg(5))
	}
	if l.Var() != 5 || Neg(5).Var() != 5 || l.IsNeg() || !Neg(5).IsNeg() {
		t.Error("리터럴에서 변수나 부호를 잘못 읽었다")
	}
}

@ 둘째 시험은 절 쌓기의 규칙을 본다. 겹친 리터럴은 하나만 남고, 늘 참인 절은
사라지며, 빈 절은 |empty|에 적힌다.

@<시험들@>=
func TestAddClause(t *testing.T) {
	s := New()
	a, b, c := s.NewVar(), s.NewVar(), s.NewVar()
	s.AddClause(a, b.Not(), a)
	s.AddClause(b, c, b.Not())
	s.AddClause(c)
	@<쌓인 절이 기대와 같은지 본다@>
	if s.empty {
		t.Error("빈 절을 넣지 않았는데 빈 절이 있다고 한다")
	}
	s.AddClause()
	if !s.empty || s.NumClauses() != 2 {
		t.Error("빈 절을 제대로 적지 못했다")
	}
}

@ @<쌓인 절이 기대와 같은지 본다@>=
want := [][]Lit{{a, b.Not()}, {c}}
got := slices.Collect(s.Clauses())
if !slices.EqualFunc(got, want, slices.Equal[[]Lit]) {
	t.Errorf("절이 %v인데 %v여야 한다", got, want)
}
if s.NumClauses() != 2 || s.unaries != 1 || s.binaries != 1 || s.NumLiterals() != 3 {
	t.Errorf("수가 틀렸다: 절 %d, 리터럴 %d", s.NumClauses(), s.NumLiterals())
}

@ 셋째 시험은 이름을 본다. 같은 이름은 같은 변수를 주어야 하고, 이름 없는 변수와
섞여도 번호가 차례대로 붙어야 한다. 잘못된 이름과 남의 리터럴은 |panic|을 일으켜야
한다.

@<시험들@>=
func TestNames(t *testing.T) {
	s := New()
	x := s.Lookup("x")
	u := s.NewVar()
	if s.Lookup("x") != x || x.Var() != 1 || u.Var() != 2 {
		t.Error("이름에서 변수를 잘못 찾았다")
	}
	if s.LitName(x.Not()) != "~x" || s.LitName(u) != "#2" {
		t.Errorf("이름이 %s, %s로 나왔다", s.LitName(x.Not()), s.LitName(u))
	}
	@<잘못 쓰면 |panic|이 나는지 본다@>
}

@ @<잘못 쓰면 |panic|이 나는지 본다@>=
mustPanic := func(what string, fn func()) {
	defer func() {
		if recover() == nil {
			t.Errorf("%s인데 panic이 나지 않았다", what)
		}
	}()
	fn()
}
mustPanic("빈칸이 낀 이름", func() { s.Lookup("a b") })
mustPanic("~로 시작하는 이름", func() { s.Lookup("~a") })
mustPanic("없는 변수", func() { s.AddClause(Pos(3)) })
mustPanic("리터럴 0", func() { s.AddClause(0) })

@* 색인.
