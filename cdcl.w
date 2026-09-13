\input kotexgweb

\def\title{CDCL}

@s context.Context int
@s gbflip.RNG int
@s testing.T int
@s Lit int
@s Solver int
@s cdclState int

@* 들어가며.
이 글은 크누스의 \.{SAT13}, 곧 {\sl TAOCP\/} 알고리즘~7.2.2.2C를 \GO/로 옮긴
것이다. 옆집 \.{sat.w}가 절을 받아 임시 표에 쌓아 두면, 이 글의 |Solve|가 그 표로
진짜 자료 구조를 짓고 충돌에서 절을 배우며 푼다.
@^Knuth, Donald Ervin@>
@^SAT13@>

크누스는 \.{SAT13}을 E\'en과 S\"orensson의 MiniSat, Biere의 PicoSat을 본보기로
삼아 썼다. 그 뼈대를 한 문단으로 줄이면 이렇다. 참으로 둔 리터럴들의 줄
``트레일''을 늘여 간다. 어떤 절이 리터럴 하나만 빼고 모두 거짓이면 그 하나를
참으로 강제하고(그 절이 그 리터럴의 ``까닭''이다), 강제할 것이 없으면 활동도가
가장 높은 변수를 골라 결정한다. 어떤 절이 모두 거짓이 되면 충돌이다. 충돌한 절을
트레일의 오른쪽부터 까닭들과 차례로 분해(resolution)하면 지금 수준의 리터럴이
하나만 남은 절이 나온다. 그 절을 배우고, 그 절이 강제하는 수준까지 되돌아간다.
빈 절을 배우면 만족할 수 없고, 모든 변수에 값이 붙으면 해를 찾은 것이다.

@ 옮기는 원칙은 \.{sat.w}에서 말한 대로 {\it mem 수가 원본과 똑같이 나오게\/}이다.
그래서 이 글은 크누스의 절을 거의 하나씩 따라간다. 절의 이름도 되도록 원본의 뜻을
살렸다. 원본을 곁에 두고 읽는 이는 \.{knuth/sat13.w}에서 같은 자리를 쉽게 찾을
것이다.

크누스는 메모리에 한 번 닿을 때마다 매크로 |o|, |oo|, |ooo|로 mem을 센다. 여기서는
그것을 |mems++|, |mems += 2|, |mems += 3|으로 적고, 되도록 그 접근이 일어나는 문장
바로 앞, 같은 줄에 둔다. 원본이 조건식 안에서 쉼표 연산자로 세는 곳, 가령
|if (o,isknown(l))|는 \GO/에 쉼표 연산자가 없으므로 |if| 바로 앞에서 센다.
짧은 회로 평가 뒤에 숨은 셈은 |if|를 둘로 쪼개어 원본과 같은 때에만 세게 했다.

두 가지는 옮기지 않았다. 하나는 |verbose|로 켜는 진단 출력과 온전성 검사다. 이것들은
mem을 세지 않으므로 빼도 수가 달라지지 않는다. 다른 하나는 파일로 해를 막는 절이나
배운 절, 극성을 적고 읽는 선택들(\.x, \.l, \.L, \.z, \.Z)이다. 꾸러미에서는
다른 모양으로 내놓는 편이 낫겠다고 생각해서 나중으로 미뤘다.

거꾸로 원본에 없는 것도 둘 보탰다. 하나는 MiniSat식 가정 리터럴이고, 다른 하나는
풀이 사이에 배운 절과 활동도를 간직하는 점진적 풀이다. 둘 다 끝의 두 별표 절에 모았다.
가정 없이 처음 푸는 풀이는 이것들 때문에 mem이 하나도 달라지지 않는다.

@c
package sat

import (
	"context"
	"errors"
	"fmt"
	"math"
	"slices"
	"strconv"
	"strings"

	"github.com/sjnam/go-sgb/gbflip"
)

@<자료 구조@>

@<함수들@>

@* 겉모습.
먼저 바깥에서 보이는 것들을 정해 둔다. 풀이의 답은 셋 가운데 하나다.

@<자료 구조@>=
type Status int

const (
	Unknown Status = iota // 답을 내지 못했다
	Sat                   // 만족할 수 있다
	Unsat                 // 만족할 수 없다
)

@ @<함수들@>=
func (st Status) String() string {
	switch st {
	case Sat:
		return "SAT"
	case Unsat:
		return "UNSAT"
	}
	return "UNKNOWN"
}

@ 답을 내지 못하는 까닭은 넷이다. 크누스의 \.T 선택으로 정한 mem 한도에 이르렀거나,
\.D 선택으로 정한 배운 절의 수(``doomsday'')에 이르렀거나, |mem| 배열이
모자라거나, 부른 쪽이 |context|를 거두었을 때다. 마지막 것은 |ctx.Err()|를 그대로
돌려준다.

@<자료 구조@>=
var (
	ErrTimeout  = errors.New("sat: mem 한도에 이르렀다")
	ErrDoomsday = errors.New("sat: 배운 절의 수가 doomsday에 이르렀다")
	ErrMemory   = errors.New("sat: mem 배열이 모자란다")
)

@ 매개변수들은 크누스가 명령 줄 선택으로 받던 것들이다. 주석의 글자는 원본의 선택
글자이고, 괄호 안은 기본값이다. 실수 매개변수를 |float32|로 둔 것은 원본이
|float|로 두기 때문이다. 원본은 이 값들을 |double|과 섞어 계산하는데, 같은
비트가 나오게 하려면 먼저 같은 정밀도로 반올림되어 있어야 한다.

@<자료 구조@>=
type Params struct {
	Seed               int     // \.s: 난수 씨앗 (0)
	MemLog             int     // \.m: |mem| 칸 수의 이진 로그 (26)
	TrivialLimit       int     // \.t: 자명한 절로 바꾸는 문턱 (10)
	Warmups            int     // \.w: 다시 시작한 뒤의 전체 달리기 수 (0)
	RecycleBump        uint64  // \.j: 첫 재활용까지의 충돌 수 (1000)
	RecycleInc         uint64  // \.J: 재활용 간격이 느는 양 (500)
	RestartPsiFraction float32 // \.f: 다시 시작하는 agility 문턱 (0.05)
	Alpha              float32 // \.a: 절 점수에서 거짓 수준의 무게 (0.4)
	VarRho             float32 // \.r: 변수 활동도의 감쇠 (0.9)
	ClauseRho          float32 // \.R: 절 활동도의 감쇠 (0.9995)
	RandProb           float32 // \.p: 결정 변수를 무작위로 고를 확률 (0.02)
	TrueProb           float32 // \.P: 처음 값을 참으로 둘 확률 (0.5)
	Timeout            uint64  // \.T: mem 한도
	Doomsday           uint64  // \.D: 배운 절 수의 한도
}

@ \.{sat.w}의 |New|는 풀이기를 이 기본값으로 채운다.

@<자료 구조@>=
var defaultParams = Params{
	MemLog:             26,
	TrivialLimit:       10,
	RecycleBump:        1000,
	RecycleInc:         500,
	RestartPsiFraction: 0.05,
	Alpha:              0.4,
	VarRho:             0.9,
	ClauseRho:          0.9995,
	RandProb:           0.02,
	TrueProb:           0.5,
	Timeout:            0x1fffffffffffffff,
	Doomsday:           0x8000000000000000,
}

@ 크누스식 선택 하나, 가령 \.{s3}이나 \.{a0.1}을 매개변수에 반영하는 문. 명령 줄
프로그램과 시험이 함께 쓴다. 결과에 영향이 없는 선택(\.v, \.c, \.H, \.h, \.b,
\.d)은 받아 두기만 한다. 원본의 명령을 부르던 스크립트를 그대로 쓸 수 있게 하려는
것이다.

@<함수들@>=
func (p *Params) Set(opt string) error {
	if opt == "" {
		return errors.New("sat: 빈 선택")
	}
	arg := opt[1:]
	var err error
	switch opt[0] {
	@<정수 선택을 읽는다@>
	@<실수 선택을 읽는다@>
	case 'v', 'c', 'H', 'h', 'b', 'd':
		_, err = strconv.ParseInt(arg, 10, 64)
	default:
		return fmt.Errorf("sat: 모르거나 지원하지 않는 선택 %q", opt)
	}
	if err != nil {
		return fmt.Errorf("sat: 선택 %q: %v", opt, err)
	}
	return nil
}

@ @<정수 선택을 읽는다@>=
case 's':
	p.Seed, err = strconv.Atoi(arg)
case 'm':
	p.MemLog, err = strconv.Atoi(arg)
case 't':
	p.TrivialLimit, err = strconv.Atoi(arg)
case 'w':
	p.Warmups, err = strconv.Atoi(arg)
case 'j':
	p.RecycleBump, err = strconv.ParseUint(arg, 10, 64)
case 'J':
	p.RecycleInc, err = strconv.ParseUint(arg, 10, 64)
case 'T':
	p.Timeout, err = strconv.ParseUint(arg, 10, 64)
case 'D':
	p.Doomsday, err = strconv.ParseUint(arg, 10, 64)

@ 원본은 |sscanf|의 \.{\%f}로 |float| 변수에 곧바로 읽는다. |strconv.ParseFloat|에
32를 주면 똑같이 가장 가까운 |float32|로 반올림한다.

@<실수 선택을 읽는다@>=
case 'f', 'a', 'r', 'R', 'p', 'P':
	var x float64
	x, err = strconv.ParseFloat(arg, 32)
	switch opt[0] {
	case 'f':
		p.RestartPsiFraction = float32(x)
	case 'a':
		p.Alpha = float32(x)
	case 'r':
		p.VarRho = float32(x)
	case 'R':
		p.ClauseRho = float32(x)
	case 'p':
		p.RandProb = float32(x)
	case 'P':
		p.TrueProb = float32(x)
	}

@ 풀이가 끝나면 원본이 작별 인사로 찍던 수들을 모아 둔다. 준비에 든 mem(|IMems|)과
푸는 데 든 mem(|Mems|)을 따로 센다. 원본처럼 입력을 읽는 데 든 것은 어느 쪽에도
넣지 않는다.

@<자료 구조@>=
type Stats struct {
	IMems, Mems     uint64  // 준비와 풀이에 든 mem
	Bytes           uint64  // 주 자료 구조의 바이트 수 (원본의 크기로 셈)
	Nodes           uint64  // 결정한 횟수
	Learned         uint64  // 배운 절의 수
	CellsPrelearned float64 // 줄이기 전 배운 절들의 길이 합
	CellsLearned    float64 // 줄인 뒤의 길이 합
	MemCells        int     // |mem|에서 쓴 칸 수의 최댓값
	Trivials        uint64  // 자명한 절로 바꾼 수
	Discards        uint64  // 곧바로 버린 배운 절의 수
	Subsumptions    uint64  // 즉석에서 포섭한 절의 수
	Restarts        uint64  // 실제로 다시 시작한 수
}

@ @<함수들@>=
func (s *Solver) Stats() Stats { return s.stats }

@ 통계를 원본의 작별 인사와 한 글자도 다르지 않게 적는 문. 원본과 나란히 돌려
견줄 때 쓴다.

@<함수들@>=
func (st Stats) String() string {
	var b strings.Builder
	fmt.Fprintf(&b, "Altogether %d+%d mems, %d bytes, %d node%s,",
		st.IMems, st.Mems, st.Bytes, st.Nodes, plural(st.Nodes, "", "s"))
	fmt.Fprintf(&b, " %d clauses learned", st.Learned)
	if st.Learned != 0 {
		fmt.Fprintf(&b, " (ave %.1f->%.1f)", st.CellsPrelearned/float64(st.Learned),
			st.CellsLearned/float64(st.Learned))
	}
	fmt.Fprintf(&b, ", %d memcells.", st.MemCells)
	@<덧붙이는 통계 줄들을 적는다@>
	return b.String()
}

@ @<덧붙이는 통계 줄들을 적는다@>=
if st.Trivials != 0 {
	fmt.Fprintf(&b, "\n(%d learned clause%s trivial.)", st.Trivials, plural(st.Trivials, " was", "s were"))
}
if st.Discards != 0 {
	fmt.Fprintf(&b, "\n(%d learned clause%s discarded.)", st.Discards, plural(st.Discards, " was", "s were"))
}
if st.Subsumptions != 0 {
	fmt.Fprintf(&b, "\n(%d clause%s subsumed on-the-fly.)", st.Subsumptions,
		plural(st.Subsumptions, " was", "s were"))
}
fmt.Fprintf(&b, "\n(%d restart%s.)", st.Restarts, plural(st.Restarts, "", "s"))

@ 영어의 단수와 복수를 가르는 문. 여러 곳에서 부른다.

@<함수들@>=
func plural(n uint64, one, many string) string {
	if n == 1 {
		return one
	}
	return many
}

@ 해를 찾았으면 두 가지로 알려 준다. |Model|은 참인 리터럴들을 원본이 찍는 차례,
곧 트레일의 차례로 준다. |Value|는 리터럴 하나가 해에서 참인지 알려 준다.

@<함수들@>=
func (s *Solver) Model() []Lit { return slices.Clone(s.model) }

func (s *Solver) Value(l Lit) bool {
	if s.truth == nil {
		panic("sat: 찾은 해가 없다")
	}
	return s.truth[l.Var()] != l.IsNeg()
}

@* 풀이의 뼈대.
이제 |Solve|를 쓴다. 원본에서 가장 먼저 부딪히는 것은 |goto|다. \.{SAT13}의 |main|은
레이블 스무 개 남짓 사이를 |goto|로 오간다. \GO/에도 |goto|가 있지만 제약이
둘 있다. 블록 {\it 안으로\/} 뛰어들 수 없고, 변수 선언을 건너뛸 수 없다.

두 번째 제약은 쉽게 풀린다. 크누스는 레지스터 변수 |h|, |j|, |k|, |l|, \dots를
|main| 머리에 한꺼번에 선언하고 전역 변수는 파일 머리에 둔다. 나는 그 둘을 모두
|Solve|의 머리에 지역 변수로 선언한다. 그러면 함수 몸통 어디에도 새 선언이 없다.
전역 변수를 지역 변수로 옮기니 풀이기 여럿이 동시에 돌아도 서로 밟지 않는다는 덤도
생긴다.

첫 번째 제약은 레이블을 함수 몸통의 맨 바깥에 두면 풀린다. 안쪽 블록에서 바깥
레이블로 뛰쳐나가는 것은 괜찮기 때문이다. 원본에서 블록 안에 숨어 있던 레이블
넷(|prep_clause|, |store_clause|, |its_true|, |test1|)은 그 자리에 가서
하나씩 펴 놓았다. 원본에 있지만 아무도 뛰어가지 않는 레이블(|square_one|,
|newlevel|, |launch|)은 \GO/에서 잘못이 되므로 뺐다.

뼈대에는 원본에 없는 갈래도 있다. 가정 리터럴을 받아 거짓인 가정을 만나면 |failed|로
가고, 지난 풀이의 상태가 있으면 짓는 대신 그것을 이어 쓴다. 이 둘은 뒤의 별표 절
``가정 리터럴''과 ``풀이 사이에 간직하기''에서 설명한다.

@<함수들@>=
func (s *Solver) Solve(ctx context.Context, assumptions ...Lit) (Status, error) {
	@<|Solve|의 지역 변수@>
	@<가정 리터럴들을 확인한다@>
	@<전처리 결과나 빈 절이 있으면 곧바로 답한다@>
	@<매개변수를 검사한다@>
	if s.state != nil && s.state.key == key {
		@<간직한 상태로 풀이를 준비한다@>
	} else {
		@<난수 발생기를 맞춘다@>
		@<주 자료 구조를 짓는다@>
		imems, mems = mems, 0
		@<초기화를 마친다@>
	}
	@<문제를 푼다@>
unsat:
	status, unsatisfiable = Unsat, true
	goto allDone
failed:
	@<실패한 가정 |l|에 책임이 있는 가정들을 모은다@>
	status = Unsat
	goto allDone
satisfied:
	status = Sat
	@<찾은 해를 적어 둔다@>
allDone:
	@<통계를 적어 둔다@>
	@<풀이의 상태를 간직한다@>
	return status, err
}

@ 전처리 결과가 있으면 줄인 절을 푸는 \.{simplify.w}의 문으로 넘긴다. 빈 절을 받았으면
풀 것도 없다.

@<전처리 결과나 빈 절이...@>=
if s.pre != nil {
	if len(assumptions) != 0 {
		return Unknown, errors.New("sat: 전처리한 풀이기에는 가정을 줄 수 없다")
	}
	return s.solvePreprocessed(ctx)
}
if s.empty {
	s.model, s.truth, s.stats, s.state = nil, nil, Stats{}, nil
	return Unsat, nil
}

@ 크누스의 레지스터 변수들. 원본의 |s|는 받는 쪽 이름 |s|와 부딪히므로, 절의 크기로
쓸 때는 |sz|, 도장 값으로 쓸 때는 |st|로 나눴다. 그 밖에는 원본의 이름 그대로다.
원본의 |int|와 |uint|는 모두 \GO/의 |int|(64비트)로 옮겼다. 원본이 32비트
넘침에 기대는 곳은 |agility| 하나뿐이라, 그것만 |uint32|로 둔다.

@<|Solve|의 지역 변수@>=
var (
	h, hp, i, j, jj, k, kk int
	l, ll, lll, p, q, r    int
	sz, st, t, u, v        int
	c, cc, endc            int
	au, av                 float64
)

@ @<|Solve|의 지역 변수@>=
var (
	status                    Status
	err                       error
	par                       Params      // 매개변수의 사본
	rng                       *gbflip.RNG // 원본의 |gb_flip|과 같은 난수열
	vars, clauses, cells      int         // 변수, 절, 리터럴의 수
	imems, mems, bytes, nodes uint64
)

@ 원본은 매개변수가 범위를 벗어나면 사용법을 찍고 끝낸다. |key|는 뒤에서 간직한
상태를 이어 쓸 수 있는지 가를 때 쓴다.

@<매개변수를 검사한다@>=
par = s.Params
if par.MemLog < 2 || par.MemLog > 31 || par.TrivialLimit <= 0 || par.Alpha < 0 ||
	par.Alpha > 1 || par.RandProb < 0 || par.TrueProb < 0 || par.VarRho <= 0 ||
	par.ClauseRho <= 0 {
	return Unknown, errors.New("sat: 매개변수가 범위를 벗어났다")
}
key = par
key.Timeout, key.Doomsday = 0, 0

@ 난수 발생기는 원본과 같은 자리에서 시작해야 한다. 원본은 입력을 읽기 전에
|gb_init_rand|로 씨앗을 뿌리고, 해시 함수에 쓸 난수 표 |hash_bits[92..1][0..7]|을
채우느라 난수를 $92\times8=736$개 먼저 뽑는다. 우리 읽개는 해시 표가 필요 없지만
그 736개는 버려야 한다. 그래야 뒤의 무작위 선택들이 원본과 같아진다. Stanford
GraphBase의 |gb_flip|은 \.{github.com/sjnam/go-sgb/gbflip}으로 이미 옮겨 두었다.

@<난수 발생기를 맞춘다@>=
vars, clauses, cells = s.NumVars(), s.clauses, len(s.cells)
rng = gbflip.New(int64(par.Seed))
for k = 0; k < 736; k++ {
	rng.Next()
}

@ 원본은 해를 찾으면 트레일의 리터럴을 차례로 찍는데, 찍으면서 mem을 하나씩 센다.
그러니 우리도 센다.

@<찾은 해를 적어 둔다@>=
s.model = make([]Lit, vars)
s.truth = make([]bool, vars+1)
for k = 0; k < vars; k++ {
	mems++; s.model[k] = Lit(trail[k])
	s.truth[trail[k]>>1] = trail[k]&1 == 0
}

@ @<통계를 적어 둔다@>=
if status != Sat {
	s.model, s.truth = nil, nil
}
s.stats = Stats{IMems: imems, Mems: mems, Bytes: bytes, Nodes: nodes,
	Learned: totalLearned - learnedBase, CellsPrelearned: cellsPrelearned, CellsLearned: cellsLearned,
	MemCells: maxCellsUsed, Trivials: trivials, Discards: discards,
	Subsumptions: subsumptions, Restarts: actualRestarts}

@* 자료 구조.
원본이 쓰는 자료 구조를 하나씩 들여다본다. 가장 큰 것은 32비트 칸들의 배열 |mem|이다.
길이가 3 이상인 입력 절과 배운 절이 모두 여기 산다. 절 |c|의 리터럴은 |mem[c]|,
|mem[c+1]|, \dots이고, 앞의 둘이 그 절을 ``감시''한다. 절 앞에는 머리 칸들이 붙는다.
$$\vbox{\halign{\quad\hfil#&\quad#\hfil\cr
|mem[c-1]|&절의 크기 |size(c)|\cr
|mem[c-2]|&첫째 감시 리터럴의 목록에서 다음 절 |link0(c)|\cr
|mem[c-3]|&둘째 감시 리터럴의 목록에서 다음 절 |link1(c)|\cr
|mem[c-4]|&배운 절에만: 재활용 점수 |range(c)|\cr
|mem[c-5]|&배운 절에만: 활동도 |activ(c)|, |float32|의 비트 그대로\cr}}$$
원본의 이 매크로들은 \GO/에 없으므로 코드에서는 |mem[c-1]|처럼 첨자를 그대로 쓴다.
감시 목록을 절 머리의 연결로 엮는 방법은 PicoSat에서 왔다. 크누스는 요즘 풀이기들이
쓰는 ``막는 리터럴''(blocking literal) 대신 이 방법을 고집한다고 적었다. 동적인
배열 할당이 필요 없고 메모리 접근도 적기 때문이다.
@^Biere, Armin@>

입력 절들이 |mem|의 앞쪽 |clauseExtra| 이상 |minLearned| 미만을 차지하고, 배운
절은 |firstLearned|부터 |maxLearned| 앞까지 쌓인다. 절에서 영영 거짓이 된
리터럴을 지울 때는 그 칸에 |signBit|를 더해 절 끝으로 옮기고 크기를 줄인다. 그러니
지워진 리터럴이 아닌 칸에는 부호 비트가 없어야 하고, 마지막 절 뒤에는 0인 칸이 하나
있어야 한다. 그래야 끝의 쓰레기를 지워진 리터럴로 착각하지 않는다.

@<자료 구조@>=
const (
	clauseExtra       = 3          // 모든 절의 머리 칸 수
	learnedSupplement = 2          // 배운 절에 더 붙는 머리 칸 수
	learnedExtra      = 5          // 배운 절의 머리 칸 수
	signBit           = 0x80000000 // 지워진 리터럴의 표
	unset             = 0xffffffff // 값이 없는 변수의 |value|
)

@ @<|Solve|의 지역 변수@>=
var (
	mem                      []uint32 // 절들의 큰 배열
	memsize                  int      // |mem|이 자랄 수 있는 한도
	minLearned, firstLearned int      // 입력 절과 배운 절의 경계
	maxLearned               int      // |mem|에서 아직 쓰지 않은 첫 자리
	maxCellsUsed             int      // |mem|에서 쓴 칸 수의 최댓값
	maxLit                   int      // 가장 큰 리터럴
)

@ 이진 절 $u\lor v$는 |mem|에 두지 않는다. $\bar u$의 목록에 $v$를, $\bar v$의
목록에 $u$를 넣은 ``이진 함의'' 배열 |bmem|에 한 번 적어 두면 끝이다. 강제는 대부분
이진 절에서 일어나므로 이 길이 빨라야 한다. 풀다가 배운 이진 절은 |mem|에 보통의
절로 들어간다.

리터럴마다 두는 것은 |lmem|에 있다. 그 리터럴을 참으로 만든 까닭 |reason|(이진
절이면 음수, 결정이면 0), 그 리터럴이 감시하는 첫 절 |watch|, 그리고 |bmem|에서
이진 함의가 놓인 구간이다. 변수마다 두는 것은 |vmem|에 있다. 활동도, 값, 트레일에서의
자리, 힙에서의 자리, 옛 값, 도장이다.

값 |value|는 수준까지 담는다. 변수가 수준~$d$에서 리터럴 $l$로 참이 되면 |value|는
$2d+(l\bmod2)$다. 그러니 |value^l|의 맨 아래 비트가 1이면 리터럴 |l|은 거짓이고,
|value&^1|은 수준의 두 배다. 원본은 수준을 늘 두 배로 들고 다닌다(|llevel|).

@<자료 구조@>=
type literal struct {
	reason    int // 까닭: 절 번호, 이진 절이면 $-$(참인 리터럴), 결정이면 0
	watch     int // 이 리터럴이 감시하는 첫 절
	bimpStart int // |bmem|에서 이진 함의가 시작하는 곳
	bimpEnd   int // 끝나는 곳 (없으면 0)
}

type variable struct {
	activity float64 // 활동도
	value    int     // $2\times$수준$+$부호, 값이 없으면 |unset|
	tloc     int     // 트레일에서의 자리
	hloc     int     // 힙에서의 자리, 힙에 없으면 $-1$
	oldval   int     // 지난번 값 (``위상 저장'')
	stamp    int     // 충돌 분석에 쓰는 도장
}

@ 원본의 구조체는 변수 하나에 40바이트, 리터럴 하나에 16바이트다. \GO/의 것은 그보다
크지만, |Bytes| 통계는 원본의 크기로 센다. 원본과 견주려는 수이기 때문이다.

@<|Solve|의 지역 변수@>=
var (
	bmem    []uint32   // 이진 함의
	lmem    []literal  // 리터럴마다
	vmem    []variable // 변수마다
	heap    []int      // 활동도의 최대 힙
	hn      int        // 힙에 든 변수의 수
	trail   []int      // 참으로 둔 리터럴들
	eptr    int        // 트레일의 끝
	ebptr   int        // 이진 함의를 아직 보지 않은 곳
	lptr    int        // 긴 절 함의를 아직 보지 않은 곳
	lbptr   int        // 이진 함의를 훑는 자리
	llevel  int        // 지금 수준의 두 배
	leveldat []int     // 수준마다 트레일의 시작 자리, 그리고 충돌 자료
)

@* 진짜 자료 구조 짓기.
임시 표를 진짜 자료 구조로 옮긴다. 순서는 원본과 같다. mem 수를 세는 문장이 여기에도
있어서, 준비에 든 mem(|IMems|)도 원본과 같아야 한다. 이 순서가 중요한 까닭이
하나 더 있다. 입력에 서로 어긋나는 단위 절이 있으면 원본은 옮기는 도중에 곧바로
|unsat|으로 뛰고, 그때까지 센 mem이 그대로 남는다.

@<주 자료 구조를 짓는다@>=
@<|vmem|과 |heap|을 마련한다@>
@<힙을 무작위로 채운다@>
@<다른 주 배열들을 마련한다@>
@<임시 칸들을 |mem|, |bmem|, |trail|로 옮긴다@>
@<변수들의 도장을 지운다@>
@<보조 배열들을 마련한다@>

@ @<|vmem|과 |heap|을 마련한다@>=
vmem = make([]variable, vars+1)
bytes += uint64(vars+1) * 40
for k = 1; k <= vars; k++ {
	mems++; vmem[k].value = unset; vmem[k].tloc = -1
}
heap = make([]int, vars)
bytes += uint64(vars) * 4

@ 처음에는 활동도가 모두 0이다. 크누스는 변화를 주려고 힙의 변수들을 무작위로
섞는다. 처음 값은 확률 |TrueProb|로 참이다. 원본에서 31비트 난수 하나는 mem 넷이다.

@<힙을 무작위로 채운다@>=
@<|trueProbThresh|를 정한다@>
for k = 1; k <= vars; k++ {
	mems++; heap[k-1] = k
}
for hn = vars; hn > 1; {
	@<|hn|보다 작은 난수 |h|를 고른다@>
	hn--
	if h != hn {
		mems++; k = heap[h]
		mems += 3; heap[h] = heap[hn]; heap[hn] = k
	}
}
@<힙의 변수들에 자리와 처음 값을 준다@>

@ 뒤에서 새로 들어온 변수에 처음 값을 줄 때도 이 문턱을 쓴다.

@<|trueProbThresh|를 정한다@>=
if par.TrueProb >= 1.0 {
	trueProbThresh = 0x80000000
} else {
	trueProbThresh = int(float64(par.TrueProb) * 2147483648.0)
}

@ @<힙의 변수들에 자리와...@>=
for h = 0; h < vars; h++ {
	mems++; v = heap[h]
	mems++; vmem[v].hloc = h
	vmem[v].oldval = 1
	if trueProbThresh != 0 {
		mems += 4
		if int(rng.Next()) < trueProbThresh {
			vmem[v].oldval = 0
		}
	}
	mems++; vmem[v].activity = 0
}
hn = vars

@ 원본은 $m$ 미만의 고른 난수를 얻을 때 $2^{31}$을 $m$으로 나눈 나머지만큼 위쪽을
버린다. |gbflip|의 |Unif|와 같은 방법이지만, 뽑을 때마다 mem을 세야 하므로 손수
적는다. 결정할 변수를 무작위로 고를 때도 이 절을 쓴다.

@<|hn|보다 작은 난수 |h|를...@>=
t = 0x80000000 - 0x80000000%hn
for {
	mems += 4; r = int(rng.Next())
	if r < t {
		break
	}
}
h = r % hn

@ @<|Solve|의 지역 변수@>=
var (
	trueProbThresh int // $2^{31}\times$|TrueProb|
	cur            int // 임시 칸을 되감는 자리
)

@ |mem|의 크기는 입력 절들에 머리 칸을 붙인 만큼으로 시작한다. 준비하는 동안에는 배운
절이 들어갈 자리 일부를 빌려 이진 절을 잠시 적어 둔다. 원본은 $2^{|MemLog|}$칸을
한꺼번에 |malloc|하지만(쓰지 않은 페이지는 운영체제가 실제로 내주지 않는다), \GO/는
잡는 즉시 0으로 채우므로 필요한 만큼으로 시작해 모자랄 때 두 배씩 늘린다. 한도는
원본과 같다.

@<다른 주 배열들을 마련한다@>=
minLearned = (clauses-s.unaries-s.binaries)*clauseExtra +
	(cells - s.unaries - 2*s.binaries) + clauseExtra
maxCellsUsed = minLearned + 2*s.binaries + 2
firstLearned = minLearned + learnedSupplement
maxLearned = firstLearned
memsize = 1 << par.MemLog
if maxCellsUsed > memsize || maxCellsUsed+learnedSupplement >= 0x80000000 {
	err = ErrMemory
	goto allDone
}
mem = make([]uint32, min(memsize, max(2*maxCellsUsed, 1<<16)))
bytes += uint64(maxCellsUsed) * 4
@<나머지 주 배열들을 마련한다@>

@ 원본은 |history| 배열도 잡는다. 진단 출력에만 쓰므로 여기서는 잡지 않고 바이트
수만 센다.

@<나머지 주 배열들을...@>=
maxLit = vars + vars + 1
lmem = make([]literal, maxLit+1)
bytes += uint64(maxLit+1) * 16
trail = make([]int, vars)
bytes += uint64(vars) * 4
bmem = make([]uint32, 2*s.binaries)
bytes += uint64(2*s.binaries)*4 + uint64(vars)

@ 배운 절이 |mem|의 끝을 넘어서려 할 때 부르는 곳이다. 이때 |maxCellsUsed|는
|memsize|보다 작다는 것이 이미 확인되어 있다.

@<|mem|을 |maxCellsUsed|칸 이상으로 늘린다@>=
if maxCellsUsed > len(mem) {
	grown := make([]uint32, min(memsize, max(2*len(mem), maxCellsUsed)))
	copy(grown, mem)
	mem = grown
}

@ 이제 임시 칸들을 되감는다. 절은 입력의 거꾸로, 절 안의 리터럴도 거꾸로 나온다.
길이가 3 이상인 절은 |mem|에 넣고 앞의 두 리터럴의 감시 목록에 엮는다. 짧은 절은
따로 다룬다. 원본의 임시 칸 값은 우리 리터럴과 인코딩이 같으므로, 절의 첫 리터럴
표만 떼면 된다.

@<임시 칸들을 |mem|, |bmem|, |trail|로 옮긴다@>=
eptr = 0
for l = 2; l <= maxLit; l++ {
	mems += 2; lmem[l].reason = 0; lmem[l].watch = 0; lmem[l].bimpEnd = 0
}
cur = cells
for c, j, jj = clauseExtra, clauses, minLearned+2; j != 0; j-- {
	@<절 |c|의 리터럴들을 되감아 넣는다@>
	if k <= 2 {
		@<단위 절과 이진 절을 따로 다룬다@>
	} else {
		mems++; mem[c-1] = uint32(k)
		l = int(mem[c])
		mems += 3; mem[c-2] = uint32(lmem[l].watch); lmem[l].watch = c
		l = int(mem[c+1])
		mems += 3; mem[c-3] = uint32(lmem[l].watch); lmem[l].watch = c
		c += k + clauseExtra
	}
}
mems++; mem[c-clauseExtra] = 0
@<이진 함의를 제자리로 옮긴다@>

@ @<절 |c|의 리터럴들을 되감아 넣는다@>=
for k = 0; ; {
	cur--
	i = int(s.cells[cur])
	mems++; mem[c+k] = uint32(i &^ int(firstLit)); k++
	if i&int(firstLit) != 0 {
		break
	}
}

@ 단위 절은 곧바로 수준 0의 트레일에 올린다. 입력에 같은 단위 절이 두 번 있을 수도,
서로 어긋나는 단위 절이 있을 수도 있다. 이진 절은 리터럴마다 함의의 개수만 세고,
두 리터럴을 배운 절 자리에 잠시 적어 둔다. 어느 쪽이든 |c|는 그대로이므로 다음 절이
그 자리를 덮어쓴다.

@<단위 절과 이진 절을...@>=
if k < 2 {
	l = int(mem[c])
	@<리터럴 |l|을 수준 0의 트레일에 올린다; 어긋나면 |goto unsat|@>
} else {
	l, ll = int(mem[c]), int(mem[c+1])
	mems += 2; lmem[l^1].bimpEnd++
	mems += 2; lmem[ll^1].bimpEnd++
	mems++; mem[jj] = uint32(l); mem[jj+1] = uint32(ll); jj += 2
}

@ 이 절은 뒤에서 간직해 둔 리터럴들을 트레일에 되돌릴 때도 쓴다.

@<리터럴 |l|을 수준 0의 트레일에 올린다...@>=
v = l >> 1
mems++
if vmem[v].value == unset {
	mems++; vmem[v].value = l & 1; vmem[v].tloc = eptr
	mems++; trail[eptr] = l; eptr++
} else if vmem[v].value != l&1 {
	goto unsat
}

@ 센 개수로 리터럴마다 |bmem|의 구간을 정하고, 잠시 적어 둔 이진 절들을 거기
채운다. 여기까지 오면 |bimpEnd|는 다시 구간의 끝을 가리킨다.

@<이진 함의를 제자리로...@>=
for l, jj = 2, 0; l <= maxLit; l++ {
	mems++; k = lmem[l].bimpEnd
	if k != 0 {
		mems++; lmem[l].bimpStart = jj; lmem[l].bimpEnd = jj; jj += k
	}
}
for jj, j = minLearned+2, s.binaries; j != 0; j-- {
	mems++; l = int(mem[jj]); ll = int(mem[jj+1]); jj += 2
	mems += 3; k = lmem[l^1].bimpEnd; bmem[k] = uint32(ll); lmem[l^1].bimpEnd = k + 1
	mems += 3; k = lmem[ll^1].bimpEnd; bmem[k] = uint32(l); lmem[ll^1].bimpEnd = k + 1
}

@ 원본은 여기서 임시 변수의 이름을 |vmem|으로 옮기고 도장을 지운다. 이름은
\.{sat.w}의 풀이기에 이미 있으니 도장만 지우지만, mem은 원본처럼 둘씩 센다.

@<변수들의 도장을 지운다@>=
for c = vars; c != 0; c-- {
	mems += 2; vmem[c].stamp = 0
}

@ 보조 배열들. 원본은 수준마다 두 칸씩 쓰는 배열들을 $2n$칸으로 잡는데, 모든 변수가
결정이 되는 드문 경우에는 수준 $n$의 다음 칸까지 닿는다. \CEE/에서는 할당의 여유
덕에 넘어가지만 \GO/는 첨자를 검사하므로 네 칸을 더 잡는다. 바이트 수는 원본대로 센다.

@<보조 배열들을 마련한다@>=
leveldat = make([]int, 2*vars+4)
learn = make([]int, vars)
stack = make([]int, 2*vars+4)
conflictdat = make([]int, 2*vars+4)
levstamp = make([]int, 2*vars+4)
bytes += uint64(vars)*(8+4+8+8+8) + buckets*4
for k = 0; k < vars; k++ {
	mems++; levstamp[k+k] = 0
}
rangedist = make([]int, buckets+1) // 끝의 한 칸은 늘 0
for k = 0; k+k < buckets; k++ {
	mems++; rangedist[k+k] = 0; rangedist[k+k+1] = 0
}
clauseHeapSize = int(par.RecycleBump >> 1)
clauseHeap = make([]uint64, clauseHeapSize)
bytes += uint64(clauseHeapSize) * 8

@* 강제.
이 프로그램은 대부분의 시간을 트레일에 리터럴을 보태는 데 쓴다. 앞서 참이 된
리터럴들 때문에 참이 될 수밖에 없는 리터럴들이다. 원본은 이것을 ``강제''(forcing)라
부르고, 흔히 말하는 단위 전파(unit propagation)와 같은 뜻이다.

가장 안쪽 반복은 트레일의 리터럴 |l|에서 이진 함의를 따라간다. 여기 들어올 때
|lat|에는 |lmem[l].bimpEnd|가 이미 들어 있고 0이 아니다. 새로 강제한 리터럴의 이진
함의도 곧바로 따라가야 하므로, 트레일의 |lbptr|부터 끝까지 이진 함의가 있는
리터럴을 찾아 계속한다. 크누스는 두 겹의 반복을 한꺼번에 빠져나가려고 |l|을 0으로
두는 ``꼼수''를 쓰고 이 어색한 짜임새를 사과했다. ``안쪽 반복에서 mem 몇 개를
아끼려고 너무 애쓰지 말아야 할지도 모르겠다. 그런데 나는 그런 사람이다.'' 이 절은
두 곳에 끼워 넣으므로 레이블 붙은 |break|를 쓸 수 없어 꼼수를 그대로 따른다.

@<|l|의 이진 함의를 전파한다; 충돌이면 |goto confl|@>=
for lbptr = eptr; ; {
	for la = lmem[l].bimpStart; la < lat; la++ {
		mems++; ll = int(bmem[la])
		mems++
		if vmem[ll>>1].value != unset {
			if (vmem[ll>>1].value^ll)&1 != 0 {
				@<이진 충돌을 다룬다@>
			}
		} else {
			@<|ll|을 |l|의 이진 함의로 트레일에 올린다@>
		}
	}
	for {
		if lbptr == eptr {
			l = 0
			break
		}
		mems++; l = trail[lbptr]; lbptr++
		mems++; lat = lmem[l].bimpEnd
		if lat != 0 {
			break
		}
	}
	if l == 0 {
		break
	}
}

@ 트레일에 올릴 때마다 |agility|를 고친다. 이것은 ``값이 옛 값과 달라지는 일''의
매끄럽게 한 확률로, 32비트 고정 소수점으로 적는다. 감쇠율은 $1-2^{-13}$이다. 옛 값
|oldval|과 반대로 강제되면 $2^{19}$를 더한다. 이 값은 다시 시작할지 정할 때 쓴다.

@<|ll|을 |l|의 이진 함의로...@>=
mems++; trail[eptr] = ll
mems++; lmem[ll].reason = -l
mems++; vmem[ll>>1].value = llevel + ll&1; vmem[ll>>1].tloc = eptr; eptr++
agility -= agility >> 13
mems++
if (vmem[ll>>1].oldval+ll)&1 != 0 {
	agility += 1 << 19
}

@ @<|Solve|의 지역 변수@>=
var (
	lt, lat    int    // 트레일의 리터럴과 그 |bimpEnd|
	la         int    // |bmem|을 훑는 자리
	wa, nextWa int    // 감시 목록의 절과 그다음 절
	agility    uint32 // 값이 뒤집히는 매끄러운 확률
)

@ 그다음 안쪽 반복은 트레일에 올라간 리터럴 |lt| 때문에 거짓이 된 $\bar{lt}$의
감시 목록을 훑는다. 감시하는 두 리터럴 가운데 $\bar{lt}$가 둘째가 되도록 필요하면
앞의 둘을 맞바꾼다. 그러면 첫째 |ll|이 다른 감시자다.

mem 세기가 조금 까다롭다. 절 |c|의 |mem[c]|와 |mem[c+1]|, 또는 |link0(c)|와
|link1(c)|, 둘 중 한 쌍만 같은 64비트 낱말에 들어간다고 보고, 넷을 모두 읽거나 쓸
때 mem을 셋으로 센다.

@<|lt|의 긴 절 함의를 전파한다; 충돌이면 |goto confl|@>=
mems++; wa = lmem[lt^1].watch
if wa != 0 {
	for q = 0; wa != 0; wa = nextWa {
		@<|lt^1|이 |wa|의 둘째 감시자가 되게 하고 |nextWa|를 얻는다@>
		@<절 |wa|가 |ll|로 참이면 감시 목록에 두고 |continue|@>
		@<|wa|의 셋째 리터럴부터 거짓이 아닌 |l|을 찾는다@>
		if j > wa+1 {
			@<|wa|를 |l|의 감시 목록으로 옮기고 |continue|@>
		}
		@<|wa|를 감시 목록에 둔다@>
		@<필요하면 |ll|을 강제하고, 충돌이면 |goto confl|@>
	}
	@<|wa|를 감시 목록에 둔다@>
}

@ @<|lt^1|이 |wa|의 둘째...@>=
mems++; ll = int(mem[wa])
if ll == lt^1 {
	mems++; ll = int(mem[wa+1])
	mems += 2; mem[wa] = uint32(ll); mem[wa+1] = uint32(lt ^ 1)
	mems++; nextWa = int(mem[wa-2])
	mems++; mem[wa-2] = mem[wa-3]; mem[wa-3] = uint32(nextWa)
} else {
	mems++; nextWa = int(mem[wa-3])
}

@ |ll|이 이미 참이면 절은 만족되었다. $\bar{lt}$가 거짓인데도 절을 그 감시 목록에
그냥 둬도 된다. 되추적이 |lt|를 풀어 줄 때까지 절은 계속 만족되어 있을 것이기 때문이다.

@<절 |wa|가 |ll|로 참이면...@>=
mems++
if vmem[ll>>1].value != unset && (vmem[ll>>1].value^ll)&1 == 0 {
	@<|wa|를 감시 목록에 둔다@>
	continue
}

@ 감시 목록은 절 머리의 |link1|로 이어져 있다. |q|는 목록에 남긴 마지막 절이다.
반복을 마친 뒤 한 번 더 부르면 |wa|가 0이므로 목록 끝을 닫는다. 전체 달리기에서는
절이 통째로 거짓이 되어도 그대로 둔다. 그런 절의 두 감시자는 그 절의 가장 높은
수준에서 거짓이 된 것들이다.

@<|wa|를 감시 목록에 둔다@>=
if q == 0 {
	mems++; lmem[lt^1].watch = wa
} else {
	mems++; mem[q-3] = uint32(wa)
}
q = wa

@ 셋째 리터럴부터 끝에서 앞으로 훑으며 거짓이 아닌 것을 찾는다. 훑다가 수준 0에서
거짓이 된 리터럴을 만나면 이 기회에 절에서 지운다. 이렇게 지워 두는 것은 나중에
``즉석 포섭''을 할 때 중요해진다. 수준 0에서는 지우지 않는다.

@<|wa|의 셋째 리터럴부터...@>=
mems++; sz = int(mem[wa-1])
for j = wa + sz - 1; j > wa+1; j-- {
	mems++; l = int(mem[j])
	mems++
	if vmem[l>>1].value == unset || (vmem[l>>1].value^l)&1 == 0 {
		break
	}
	if vmem[l>>1].value < 2 && llevel != 0 {
		@<|l|을 절 |wa|에서 지운다@>
	}
}

@ @<|l|을 절 |wa|에서...@>=
mems++; sz--; mem[wa-1] = uint32(sz)
if j != wa+sz {
	mems += 2; mem[j] = mem[wa+sz]
}
mems++; mem[wa+sz] = uint32(l) + signBit

@ @<|wa|를 |l|의 감시 목록으로...@>=
mems += 2; mem[wa+1] = uint32(l); mem[j] = uint32(lt ^ 1)
mems++; mem[wa-3] = uint32(lmem[l].watch)
mems++; lmem[l].watch = wa
continue

@ 여기까지 왔으면 첫째 리터럴 |ll| 말고는 모두 거짓이고, |ll|은 참이 아니다.
|ll|이 거짓이면 충돌이고, 값이 없으면 지금 수준에서 참으로 강제한다. 강제한 리터럴에
이진 함의가 있으면 곧바로 따라간다.

@<필요하면 |ll|을 강제하고...@>=
if vmem[ll>>1].value != unset {
	@<긴 충돌을 다룬다@>
} else {
	mems++; trail[eptr] = ll
	mems++; vmem[ll>>1].tloc = eptr; eptr++
	vmem[ll>>1].value = llevel + ll&1
	agility -= agility >> 13
	mems++
	if (vmem[ll>>1].oldval+ll)&1 != 0 {
		agility += 1 << 19
	}
	mems++; lmem[ll].reason = wa
	mems++; lat = lmem[ll].bimpEnd
	if lat != 0 {
		l = ll
		@<|l|의 이진 함의를 전파한다...@>
	}
}

@ 이진 절 $\bar u\lor\bar v$에서 충돌이 났다. 여기서 $u=|l|$이고 $\bar v=|ll|$이다.
이 절은 |mem|에 없으므로 ``절 번호''를 |-l|로 삼는다. 보통은 곧바로 충돌을 풀러
가지만, 전체 달리기 중이면 기록만 하고 계속 나아간다.

@<이진 충돌을 다룬다@>=
if fullRun && llevel != 0 {
	if !conflictSeen {
		conflictSeen = true
		mems++; leveldat[llevel+1] = -l
		mems++; conflictdat[llevel+1] = ll
		conflictdat[llevel] = conflictLevel; conflictLevel = llevel
	}
} else {
	c = -l
	goto confl
}

@ @<긴 충돌을 다룬다@>=
if fullRun && llevel != 0 {
	if !conflictSeen {
		conflictSeen = true
		mems++; leveldat[llevel+1] = wa
		mems++; conflictdat[llevel] = conflictLevel; conflictLevel = llevel
	}
} else {
	c = wa
	goto confl
}

@ ``전체 달리기''(full run)에서는 충돌을 만나도 멈추지 않고 모든 변수에 값이 붙을
때까지 나아간다. 수준마다 처음 만난 충돌 하나만 기억해 두는데, 그 절 번호는
|leveldat[llevel+1]|에, 이진 충돌이면 |ll|을 |conflictdat[llevel+1]|에 둔다. 충돌이
난 수준들은 |conflictdat|의 짝수 칸으로 엮은 더미로 쌓이고, 그 꼭대기가
|conflictLevel|이다.

@<|Solve|의 지역 변수@>=
var (
	fullRun       bool  // 전체 달리기 중인가
	conflictSeen  bool  // 이 수준에서 충돌을 보았는가
	conflictLevel int   // 기록된 충돌 더미의 꼭대기
	conflictdat   []int // 전체 달리기의 충돌 자료
)

@* 활동도.
경험에 따르면 최근의 충돌에 자주 끼어든 변수로 가르는 것이 대개 좋다. 변수 $v$의
활동도는 $\{\rho^t\mid v$가 끝에서 $t$번째 충돌에 끼었다$\}$의 합에 비례하게 한다.
이것은 $\{\rho^{-t}\mid v$가 $t$번째 충돌에 끼었다$\}$의 합에도 비례하므로, 충돌에
낀 변수에 |varBump|를 더하고 충돌마다 |varBump|를 $\rho$로 나누면 된다. 값이 너무
커지면 모두를 같은 비율로 줄인다. 이 방법은 2005년판 MiniSat에서 E\'en이 쓴 것으로,
Chaff의 VSIDS를 다듬은 것이다.
@^E\'en, Niklas@>

@<리터럴 |l|의 활동도를 올린다@>=
v = l >> 1
mems++; av = vmem[v].activity + varBump
mems++; vmem[v].activity = av
if av >= 1e100 {
	@<모든 변수의 활동도를 줄인다@>
}
mems++; h = vmem[v].hloc
if h > 0 {
	@<|v|를 힙에서 끌어올린다@>
}

@ 힙에는 변수 |hn|개가 들어 있고, |x=heap[h]|이고 |y|가 |heap[2h+1]|이나
|heap[2h+2]|이면 |x|의 활동도가 |y|의 것보다 작지 않다. 그러니 |heap[0]|이 활동도가
가장 큰 변수다. 여기서는 |av|가 |v|의 활동도라고 가정한다. 끌어올리면 |j|를 1로 둔다.

@<|v|를 힙에서 끌어올린다@>=
hp = (h - 1) >> 1
mems++; u = heap[hp]
mems++
if vmem[u].activity < av {
	for {
		mems++; heap[h] = u
		mems++; vmem[u].hloc = h
		h = hp
		if h == 0 {
			break
		}
		hp = (h - 1) >> 1
		mems++; u = heap[hp]
		mems++
		if vmem[u].activity >= av {
			break
		}
	}
	mems++; heap[h] = v
	mems++; vmem[v].hloc = h
	j = 1
}

@ @<|v|를 힙에 넣는다@>=
mems++; av = vmem[v].activity
h = hn; hn++; j = 0
if h > 0 {
	@<|v|를 힙에서 끌어올린다@>
}
if j == 0 {
	mems += 2; heap[h] = v; vmem[v].hloc = h
}

@ 여기서는 |v=heap[0]|이라고 가정한다. 맨 끝의 변수 |u|를 뿌리의 빈자리로 옮기고
내려보낸다.

@<|v|를 힙에서 지운다@>=
mems++; vmem[v].hloc = -1
hn--
if hn != 0 {
	mems++; u = heap[hn]
	mems++; au = vmem[u].activity
	for h, hp = 0, 1; hp < hn; h, hp = hp, 2*hp+1 {
		@<|hp|를 두 자식 가운데 활동도가 큰 쪽으로 정하고 |av|에 그 값을 둔다@>
		if au >= av {
			break
		}
		mems++; heap[h] = heap[hp]
		mems++; vmem[heap[hp]].hloc = h
	}
	mems++; heap[h] = u
	mems++; vmem[u].hloc = h
}

@ @<|hp|를 두 자식...@>=
mems += 2; av = vmem[heap[hp]].activity
if hp+1 < hn {
	mems += 2
	if vmem[heap[hp+1]].activity > av {
		hp++; av = vmem[heap[hp]].activity
	}
}

@ 결정할 변수를 고른다. 확률 |RandProb|로 힙에서 무작위로 하나를 고르고(판에 박히지
않으려는 궁리다), 아니면 꼭대기를 고른다. 힙에는 값이 이미 붙은 변수도 들어 있을
수 있으므로, 고른 변수에 값이 있으면 꼭대기에서 값이 없는 변수가 나올 때까지 꺼낸다.
무작위로 고른 변수는 힙에서 꺼내지 않는다는 점에 주의하자. 부호는 옛 값
|oldval|에서 가져온다. 예전 실험에서 좋았던 값은 대개 계속 좋기 때문이다.

@<다음 결정 리터럴 |l|을 고른다@>=
h = 0
if randProbThresh != 0 {
	mems += 4; h = int(rng.Next())
	if h < randProbThresh {
		@<|hn|보다 작은 난수 |h|를...@>
		mems++; v = heap[h]
		mems++
		if vmem[v].value != unset {
			h = 0
		}
	} else {
		h = 0
	}
}
if h == 0 {
	for {
		mems++; v = heap[0]
		@<|v|를 힙에서 지운다@>
		mems++
		if vmem[v].value == unset {
			break
		}
	}
}
mems++; l = v + v + vmem[v].oldval&1

@ 0이 아닌 활동도를 줄일 때는 0이 되지 않게 조심한다. 한 번이라도 활발했던 변수가
전혀 활발하지 않았던 변수보다 뒤로 밀리지 않게 하려는 것이다. 크누스는 이것이
그리 중요한지 모르겠지만 E\'en이 권했다고 적었다. 바깥의 |v|와 |av|를 건드리지
않도록 따로 변수를 쓴다. 원본도 블록 안에서 새로 선언한다.

@<모든 변수의 활동도를 줄인다@>=
for vv := 1; vv <= vars; vv++ {
	mems++; a := vmem[vv].activity
	if a != 0 {
		mems++; vmem[vv].activity = max(a*1e-100, tiny)
	}
}
varBump *= 1e-100

@ 배운 절에도 활동도가 있다. 변수의 활동도만큼 자주 쓰지는 않고, 배운 절이 너무
많아졌을 때 무엇을 남길지 정하는 데만 쓴다. 원본은 이것을 |float|로 둔다.

@<절 |c|의 활동도를 올린다@>=
mems++; ac = math.Float32frombits(mem[c-5]) + clauseBump
mems++; mem[c-5] = math.Float32bits(ac)
if ac >= 1e20 {
	@<모든 절의 활동도를 줄인다@>
}

@ @<모든 절의 활동도를...@>=
for c2 := firstLearned; c2 < maxLearned; {
	mems++; e2 := c2 + int(mem[c2-1])
	mems++; a := float64(math.Float32frombits(mem[c2-5]))
	if a != 0 {
		mems++; mem[c2-5] = math.Float32bits(float32(max(a*1e-20, singleTiny)))
	}
	for {
		mems++
		if mem[e2]&signBit == 0 {
			break
		}
		e2++
	}
	c2 = e2 + learnedExtra
}
clauseBump = float32(float64(clauseBump) * 1e-20)

@ 충돌을 하나 풀 때마다 올릴 몫을 키운다.

@<올릴 몫을 키운다@>=
varBump *= varBumpFactor
clauseBump *= clauseBumpFactor

@ 두 문턱 값은 가장 작은 정규화된 |double|과 |float|, 곧 $2^{-1022}$와 $2^{-126}$이다.
|max(a*1e-100, tiny)|는 원본의 |(a*1e-100<tiny? tiny: a*1e-100)|와 같다. 둘 다
NaN이 아니기 때문이다.

@<자료 구조@>=
const (
	tiny       = 2.225073858507201383e-308
	singleTiny = 1.1754943508222875080e-38
)

@ @<|Solve|의 지역 변수@>=
var (
	varBump          float64 = 1.0
	clauseBump       float32 = 1.0
	varBumpFactor    float64 // $1/|VarRho|$
	clauseBumpFactor float32 // $1/|ClauseRho|$
	ac               float32 // 절 활동도
	randProbThresh   int     // $2^{31}\times$|RandProb|
)

@* 충돌에서 배우기.
어떤 절의 리터럴이 모두 거짓이 되면 충돌이다. 지금 수준에서 값이 붙은 리터럴을
``새'' 리터럴, 그 전에 붙은 것을 ``헌'' 리터럴이라 하자. 충돌한 절에는 새 리터럴이
적어도 둘 있다. 모든 만족되지 않은 절이 값 없는 리터럴 둘로 감시되기 전에는 새 수준을
시작하지 않기 때문이다.

충돌한 절 $c$에 $\bar l$이 있고 $c'$가 $l$의 까닭이면, $c$와 $c'$를 분해해 새 절
$c''$을 얻는다. $c''$도 모든 리터럴이 거짓이니 여전히 충돌이다. 트레일의 차례로 가장
오른쪽 리터럴을 거듭 분해해 없애면, 새 리터럴이 딱 하나 남은 절 $c_0$에 이른다.
$c_0$를 배우고, 그 헌 리터럴들의 수준 가운데 가장 높은 수준 $d$로 돌아가면 새 리터럴의
부정이 그 수준에서 강제된다.

실제로는 도장 |stamp|로 충돌 절과 거기서 나온 절들에 든 리터럴을 표시한다. 방금
표시한 변수는 도장이 |curstamp|와 같다. 헌 리터럴은 |learn| 배열에 모으고, 새
리터럴은 개수 |xnew|만 센다. 여기 올 때 |llevel|은 0이 아니다.

@<충돌 절 |c|를 다룬다@>=
oldptr, jumplev, xnew, clevels = 0, 0, 0, 0
@<|curstamp|를 새 값으로 올린다@>
if c < 0 {
	@<이진 충돌에서 시작한다@>
} else {
	@<긴 충돌에서 시작한다@>
}
@<|xnew|를 0으로 줄인다@>
for {
	mems++; l = trail[tl]; tl--
	mems++
	if vmem[l>>1].stamp == curstamp {
		break
	}
}
lll = l ^ 1

@ 크누스는 전체 달리기 중에는 첫 리터럴 |mem[c]|가 새 것이 아니라 헌 것일 수도
있다는 미묘한 점을 오랫동안 몰랐다고 고백한다. 그래서 절의 모든 리터럴을 똑같이
다룬다. |xnew|를 $-1$에서 시작하는 것은 새 리터럴 가운데 하나는 분해로 없애지 않고
남길 것이기 때문이다.

@<긴 충돌에서 시작한다@>=
tl, xnew = 0, -1
if c >= firstLearned && c < maxLearned {
	@<절 |c|의 활동도를 올린다@>
}
mems++; sz = int(mem[c-1])
for k = c + sz - 1; k >= c; k-- {
	mems++; l = int(mem[k]) ^ 1
	j = vmem[l>>1].tloc
	if j > tl {
		tl = j
	}
	@<|l|을 충돌 절의 식구로 도장 찍는다@>
}

@ 이진 충돌은 참인 |l=-c|가 거짓인 |ll|을 함의한다는 것이다. 두 리터럴은 모두 지금
수준의 것이다.

@<이진 충돌에서 시작한다@>=
mems++; tl = vmem[ll>>1].tloc
mems++; vmem[ll>>1].stamp = curstamp
l = ll
@<리터럴 |l|의 활동도를 올린다@>
l = -c
mems++
if vmem[l>>1].tloc > tl {
	tl = vmem[l>>1].tloc
}
mems++; vmem[l>>1].stamp = curstamp
@<리터럴 |l|의 활동도를 올린다@>
xnew = 1

@ 뒤에서 |curstamp|, |curstamp+1|, |curstamp+2|를 모두 쓴다.

@<|curstamp|를 새 값으로...@>=
if curstamp >= 0xfffffffe {
	for k = 1; k <= vars; k++ {
		mems += 2; vmem[k].stamp = 0; levstamp[k+k-2] = 0
	}
	curstamp = 1
} else {
	curstamp += 3
}

@ @<|Solve|의 지역 변수@>=
var (
	curstamp        int   // 표시에 쓰는 새 값
	learn           []int // 배울 절의 헌 리터럴들
	oldptr          int   // 지금까지 모은 헌 리터럴의 수
	jumplev         int   // 배운 뒤 돌아갈 수준의 두 배
	tl              int   // 표시한 리터럴을 찾는 트레일의 자리
	xnew            int   // 충돌 절에 남은 여분의 새 리터럴 수
	clevels         int   // 충돌 절에 든 수준의 수
	learnedSize     int   // 배울 절의 리터럴 수
	prelearnedSize  int   // 줄이기 전의 |learnedSize|
	trivialLearning bool  // 배울 절을 결정들로만 이룬 절로 바꾸었는가
)

@ 트레일을 오른쪽에서 왼쪽으로 훑으며 표시된 리터럴을 만날 때마다 그 까닭과
분해한다. 이 순간의 충돌 절은 |j<=tl|이고 도장이 |curstamp|인 |trail[j]|들의 부정과
$\bar l$로 이루어져 있다. 헌 리터럴들은 |learn|에 있고, $\bar l$ 말고도 새 리터럴이
|xnew+1|개 있다. $\bar l$을 |l|의 까닭에 든 다른 리터럴들로 바꾼다.

@<|xnew|를 0으로...@>=
for xnew != 0 {
	for {
		mems++; l = trail[tl]; tl--
		mems++
		if vmem[l>>1].stamp == curstamp {
			break
		}
	}
	xnew--
	@<|l|의 까닭과 분해한다@>
}

@ @<|l|의 까닭과 분해한다@>=
mems++; c = lmem[l].reason
if c < 0 {
	l = -c
	mems++
	if vmem[l>>1].stamp != curstamp {
		@<|l|을 충돌 절의 식구로...@>
	}
} else if c != 0 {
	if c >= firstLearned {
		@<절 |c|의 활동도를 올린다@>
	}
	mems++; sz = int(mem[c-1])
	for k = c + sz - 1; k > c; k-- {
		mems++; l = int(mem[k]) ^ 1
		mems++
		if vmem[l>>1].stamp != curstamp {
			@<|l|을 충돌 절의 식구로...@>
		}
	}
	if xnew+oldptr+1 < sz && xnew != 0 {
		@<첫 리터럴을 떼어 절 |c|를 포섭한다@>
	}
}

@ 표시하면서 활동도를 올린다. 지금 수준의 리터럴이면 새 것으로 세고, 아니면 헌 것으로
|learn|에 넣으며 돌아갈 수준을 고친다. |levstamp|의 짝수 칸에는 수준마다 표시를
남긴다. 수준 $t$에 헌 리터럴이 하나뿐이면 |levstamp[2t]|를 |curstamp|로, 둘
이상이면 |curstamp+1|로 둔다. 뒤에서 배울 절을 줄일 때 이것이 쓸모 있다.

@<|l|을 충돌 절의 식구로...@>=
mems++; jj = vmem[l>>1].value &^ 1
mems++; vmem[l>>1].stamp = curstamp
@<리터럴 |l|의 활동도를 올린다@>
if jj >= llevel {
	xnew++
} else {
	if jj > jumplev {
		jumplev = jj
	}
	mems++; learn[oldptr] = l ^ 1; oldptr++
	mems++
	if levstamp[jj] < curstamp {
		mems++; levstamp[jj] = curstamp; clevels++
	} else if levstamp[jj] == curstamp {
		mems++; levstamp[jj] = curstamp + 1
	}
}

@ 배열 |stack|과 |conflictdat|은 최악의 경우 변수 수의 두 배만큼 칸이 필요하다.
|levstamp|도 같은 크기로, 짝수 칸은 배울 때, 홀수 칸은 재활용할 때 쓴다.

@<|Solve|의 지역 변수@>=
var (
	stack    []int // 손수 다루는 재귀의 더미
	stackptr int   // 더미에 든 것의 수
	levstamp []int // 수준마다의 표시
)

@ ``즉석 포섭''(on-the-fly subsumption)이다. 방금 분해한 절 |c|가 지금의 충돌 절을
품고 있으면 |c|를 줄일 수 있다. 2009년에 미국에서는 Han과 Somenzi가, 유럽에서는
Hamadi, Jabbour, Sa\"\i s가 따로 찾아낸 기법이다.
@^Han, Hyojung@>
@^Somenzi, Fabio@>

지금의 충돌 절은 어떤 절을 |c|와 분해하고 수준 0에서 거짓인 리터럴을 지운 것이다.
|c|에서도 그런 리터럴은 이미 지웠다. 그러니 충돌 절은 |c|에서 첫 리터럴(참이었고 분해로
없어진 것)을 뺀 것과 같다. 첫 리터럴을 떼어 절 끝에 지운 표를 달고, 지금 수준에서
거짓인 리터럴 하나를 찾아 새 첫째 감시자로 삼는다. |xnew>0|이므로 그런 리터럴은
|mem[c+1]|보다 뒤에 반드시 있다.

@<첫 리터럴을 떼어...@>=
l = int(mem[c])
mems++; sz--; mem[c-1] = uint32(sz); subsumptions++
mems++; r = int(mem[c-2])
@<절 |c|를 |l|의 감시 목록에서 뺀다@>
mems++; ll = int(mem[c+sz])
for lll, k = ll, c+sz; ; k-- {
	mems++; r = vmem[lll>>1].value &^ 1
	if r == llevel {
		break
	}
	mems++; lll = int(mem[k-1])
}
if k == c+1 {
	panic("sat: 이럴 수는 없다 (on-the-fly subsumption)")
}
if lll != ll {
	mems++; mem[k] = uint32(ll)
}
mems += 2; mem[c+sz] = uint32(l) + signBit; mem[c] = uint32(lll)
mems += 3; mem[c-2] = uint32(lmem[lll].watch); lmem[lll].watch = c

@ 절 |c|를 리터럴 |l|의 감시 목록에서 빼는 곳. 여기 올 때 |r|에는 목록에서 |c|의
다음 절이 들어 있다.

@<절 |c|를 |l|의 감시 목록에서 뺀다@>=
mems++
for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
	mems++; p = int(mem[wa])
	mems++
	if p == l {
		nextWa = int(mem[wa-2])
	} else {
		nextWa = int(mem[wa-3])
	}
}
if q == 0 {
	mems++; lmem[l].watch = r
} else if p == l {
	mems++; mem[q-2] = uint32(r)
} else {
	mems++; mem[q-3] = uint32(r)
}

@ @<|Solve|의 지역 변수@>=
var subsumptions uint64 // 즉석 포섭의 수

@* 배울 절 줄이기.
배울 절이 $\bar l\lor\bar a_1\lor\cdots\lor\bar a_k$라 하자. 몇 번의 분해로 없앨 수
있는 군더더기 $\bar a_j$가 흔히 섞여 있다. 가령 $a_4$의 까닭이 $a_4\lor\bar
a_1\lor\bar b_1$이고, $b_1$의 까닭이 $b_1\lor\bar a_2\lor\bar b_2$이고, $b_2$의
까닭이 $b_2\lor\bar a_1\lor\bar a_3$이면 $\bar a_4$는 군더더기다. MiniSat을 쓴
S\"orensson은 이렇게 줄이면 배운 절이 대개 30\%쯤 짧아진다는 것을 알아냈다.
@^S\"orensson, Niklas@>

$\bar a$가 군더더기일 필요충분조건은 그 까닭의 다른 리터럴들이 모두 배울 절에
있거나 (재귀적으로) 군더더기인 것이다. 크누스는 기억을 곁들여 위에서 아래로
따진다. 리터럴 $b$에 $\bar b$가 군더더기로 밝혀지면 도장 |curstamp+1|을, 군더더기가
아니라고 밝혀지면 |curstamp+2|를 찍는다. S\"orensson의 요령도 하나 쓴다. 결정이 아닌
리터럴은 같은 수준의 다른 리터럴에 늘 기대므로, $\bar a_j$는 배울 절에서 같은 수준의
다른 $\bar a_i$가 있을 때만 군더더기일 수 있다. 앞에서 |levstamp|에 남긴 표시가 바로
그것을 알려 준다.

@<배울 절을 줄인다@>=
learnedSize = oldptr + 1
cellsPrelearned += float64(learnedSize); prelearnedSize = learnedSize
for kk = 0; kk < oldptr; kk++ {
	mems++; l = learn[kk] ^ 1
	mems += 2; st = levstamp[vmem[l>>1].value&^1]
	if st < curstamp+1 {
		continue
	}
	@<$\bar l$이 군더더기면 |goto redundant|@>
	continue
redundant:
	learnedSize--
}
@<배울 절이 너무 길면 자명한 절로 바꾼다@>

@ 재귀 대신 명시적인 더미를 쓴다. 크누스는 mem 세기를 손에 쥐고 논리 구조를 살리려고
그렇게 했고, 이 반복이 ``재귀와 되풀이가 어떻게 이어지는지 보여 주는 좋은 예''라고
적었다. 원본에서는 더미에서 꺼낸 뒤 |for| 반복의 한가운데로 |goto test1|로 뛰어들어
갔다. \GO/는 반복 블록 안으로 뛰어들 수 없으므로, 절의 리터럴을 훑는 반복을 레이블
|scan|과 |next|로 풀어 적었다. 하는 일은 원본과 한 걸음씩 같다. 나올 때는 처음의 |l|이
|ll|에 들어 있다.

@<$\bar l$이 군더더기면...@>=
if stackptr != 0 {
	panic("sat: 이럴 수는 없다 (stack)")
}
test:
	ll = l
	mems++
	if vmem[l>>1].value&^1 == 0 {
		goto isRed
	}
	mems++; c = lmem[l].reason
	if c == 0 {
		goto clearStack
	}
	if c < 0 {
		@<이진 까닭을 따진다@>
	}
	mems++; k = c + int(mem[c-1]) - 1
@<까닭 절의 리터럴들을 |k|부터 따진다@>
@<군더더기로 밝혀진 것을 적고 더미를 푼다@>

@ 수준 0의 리터럴은 늘 군더더기이고, 결정 리터럴은 결코 군더더기가 아니다.

이진 까닭에서 원본은 |l=bar(-c)|로 옮겨 간다. 참인 리터럴은 |-c|이므로, 내가
읽기로는 |l=-c|가 뜻한 바였을 것이다. 도장과 수준은 변수에만 매이니 앞의 몇 줄에는
차이가 없다. 하지만 더미에 넣고 |test|로 돌아가면 거짓인 리터럴의 |reason|을 읽게
되고, 그것은 늘 0이므로 ``군더더기가 아님''으로 끝난다. 틀린 답이 나오지는 않고 절이
덜 줄어들 뿐이다. mem 수를 맞추려면 이것도 그대로 따라야 한다.

@<이진 까닭을 따진다@>=
l = -c ^ 1
mems++; st = vmem[l>>1].stamp
if st >= curstamp {
	if st == curstamp+2 {
		goto clearStack
	}
} else {
	mems++; stack[stackptr] = ll; stackptr++
	goto test
}
goto isRed

@ 까닭 절의 둘째 리터럴부터 따진다. 이미 도장이 찍혀 있으면 배울 절에 있거나 결과를
아는 것이다. 수준이 0이면 군더더기이고, 그 수준에 배울 절의 리터럴이 없으면 군더더기가
아니다. 셋 다 아니면 더미에 넣고 그 리터럴부터 따진다.

@<까닭 절의 리터럴들을 |k|부터...@>=
scan:
	if k <= c {
		goto isRed
	}
	mems += 2; l = int(mem[k]) ^ 1; st = vmem[l>>1].stamp
	if st >= curstamp {
		if st == curstamp+2 {
			goto clearStack
		}
		goto next
	}
	mems++; st = vmem[l>>1].value &^ 1
	if st == 0 {
		goto next
	}
	mems++; st = levstamp[st]
	if st < curstamp {
		mems++; vmem[l>>1].stamp = curstamp + 2
		goto clearStack
	}
	mems++; stack[stackptr] = k; stack[stackptr+1] = ll; stackptr += 2
	goto test
next:
	k--
	goto scan

@ |ll|이 군더더기로 밝혀졌다. 더미가 비었으면 처음 물은 리터럴이 군더더기다. 아니면
더미에서 꺼내 하던 일로 돌아간다. 이진 까닭이었으면 그 리터럴도 곧바로 군더더기이고,
긴 까닭이었으면 훑던 자리 |k|를 꺼내 이어 훑는다.

@<군더더기로 밝혀진...@>=
isRed:
	mems++; vmem[ll>>1].stamp = curstamp + 1
	if stackptr != 0 {
		mems += 2; stackptr--; ll = stack[stackptr]; c = lmem[ll].reason
		if c < 0 {
			goto isRed
		}
		mems++; stackptr--; k = stack[stackptr]
		goto next
	}
	goto redundant
@<더미를 비운다@>

@ 따지다가 군더더기가 아닌 리터럴을 만나면, 지금 따지던 |ll|도, 더미에 쌓인 것들도
모두 군더더기가 아니다. 더미의 맨 밑은 배울 절의 리터럴이므로 도장을 |curstamp|로
남기고, 나머지에는 |curstamp+2|를 찍는다.

@<더미를 비운다@>=
clearStack:
	if stackptr != 0 {
		mems++; vmem[ll>>1].stamp = curstamp + 2
		mems++; stackptr--; ll = stack[stackptr]
		mems++; c = lmem[ll].reason
		if c > 0 {
			stackptr--
		}
		goto clearStack
	}

@ 줄이고도 절이 쓸데없이 길 때가 있다. 가령 수준 1의 결정 리터럴은 절에 없는데 다른
리터럴들이 모두 그것에 기대는 경우다. 배울 절의 크기가 돌아갈 수준에 |TrivialLimit|를
더한 것보다 크면, 결정 리터럴들로만 이룬 ``자명한'' 절로 바꾼다. 그럴 때는 보통의
되추적보다 나을 것이 없는 셈이다.

@<배울 절이 너무 길면...@>=
if learnedSize <= (jumplev>>1)+par.TrivialLimit {
	trivialLearning = false
} else {
	trivialLearning = true
	clevels = jumplev >> 1; learnedSize = clevels + 1; trivials++
}
cellsLearned += float64(learnedSize); totalLearned++

@ @<|Solve|의 지역 변수@>=
var (
	prevLearned                   int     // 가장 최근에 배운 절
	cellsPrelearned, cellsLearned float64 // 배운 절들의 길이 합
	totalLearned                  uint64  // 배운 절의 수
	trivials, discards            uint64  // 자명한 절, 버린 절의 수
)

@ 이 절은 |learnedSize>1|일 때만 쓴다. 새 절은 두 리터럴로 감시해야 한다. 하나는
거짓이었다가 참이 될 |lll|이다. 다른 하나는 나머지(모두 거짓) 가운데 가장 높은 수준의
것이어야 한다. 그러지 않으면 되추적으로 내려간 수준에서 이 절이 강제할 차례가 되어도
알아차리지 못한다.

@<줄인 절을 배운다@>=
@<배운 절의 자리 |c|를 정한다@>
@<배운 절 |c|를 적는다@>
prevLearned = c

@ 크누스는 초기 실험에서 방금 배운 절이 곧바로 다음 절에 포섭되는 일을 여러 번
보았다. 앞서 배운 절이 사라지는 수준의 리터럴의 까닭이었을 때 일어나는 일이었다.
그래서 이 경우를 따로 살핀다. 되추적이 그 리터럴의 까닭을 이미 0으로 지워 두었다.

\GO/에서는 |mem|을 필요할 때 늘리므로, 원본과 달리 끝의 0을 적기 전에 자리를
확보한다. 세는 mem은 같다.

@<배운 절의 자리 |c|를...@>=
if prevLearned != 0 {
	mems++; l = int(mem[prevLearned])
	if !trivialLearning {
		mems++
		if lmem[l].reason == 0 {
			mems++
			if vmem[l>>1].value == unset {
				@<앞서 배운 절이 이번 절에 포섭되면 버린다@>
			}
		}
	}
}
c = maxLearned
maxLearned += learnedSize + learnedExtra
if maxLearned > maxCellsUsed {
	if maxLearned >= memsize {
		err = ErrMemory
		goto allDone
	}
	bytes += uint64(maxLearned-maxCellsUsed) * 4
	maxCellsUsed = maxLearned
	@<|mem|을 |maxCellsUsed|칸 이상으로...@>
}
mems++; mem[c+learnedSize] = 0

@ 앞서 배운 절의 첫 리터럴은 값이 없으므로 충돌 절에 들지 않는다. 이번에 배울 절의
리터럴이 모두 앞의 절의 {\it 다른\/} 리터럴들 가운데 있으면 앞의 절을 버린다. 원본은
|r|을 부호 없는 수로 바꿔 견주는데, 값이 없는 변수에서는 |r|이 매우 커서 견줌이
거짓이 된다. \GO/의 |int|에서도 똑같다.

@<앞서 배운 절이 이번...@>=
mems++
for k, q = int(mem[prevLearned-1])-1, learnedSize; q != 0 && k >= q; k-- {
	mems += 2; l = int(mem[prevLearned+k]); r = vmem[l>>1].value &^ 1
	if l == lll || r <= jumplev {
		mems++
		if vmem[l>>1].stamp == curstamp {
			q--
		}
	}
}
if q == 0 {
	maxLearned = prevLearned
	discards++
	c = prevLearned; mems++; mem[c-5] = 0
	mems++; l = int(mem[c]); r = int(mem[c-2])
	@<절 |c|를 |l|의 감시 목록에서 뺀다@>
	mems += 2; l = int(mem[c+1]); r = int(mem[c-3])
	@<절 |c|를 |l|의 감시 목록에서 뺀다@>
}

@ 자명한 절은 돌아갈 수준까지의 결정 리터럴들을 부정해 모은 것이다. 보통의 절이면
|learn|에서 군더더기가 아닌 것(도장이 |curstamp|인 것)만 옮기되, 돌아갈 수준의
리터럴을 처음 만나면 둘째 감시자 자리에 둔다.

@<배운 절 |c|를 적는다@>=
if mem[c-5] != 0 {
	panic("sat: 이럴 수는 없다 (bumps)")
}
mem[c-1] = uint32(learnedSize)
mems++; mem[c] = uint32(lll)
mems += 2; mem[c-2] = uint32(lmem[lll].watch)
mems++; lmem[lll].watch = c
if trivialLearning {
	for j, k = 1, jumplev; k != 0; j, k = j+1, k-2 {
		mems += 2; l = trail[leveldat[k]] ^ 1
		if j == 1 {
			mems += 3; mem[c-3] = uint32(lmem[l].watch); lmem[l].watch = c
		}
		mems++; mem[c+j] = uint32(l)
	}
} else {
	@<군더더기가 아닌 리터럴들을 절 |c|에 옮긴다@>
}

@ @<군더더기가 아닌 리터럴들을...@>=
for k, j, jj = 1, 0, 1; k < learnedSize; j++ {
	mems++; l = learn[j]
	mems++
	if vmem[l>>1].stamp == curstamp {
		mems++; r = vmem[l>>1].value
		if jj != 0 && r >= jumplev {
			mems++; mem[c+1] = uint32(l)
			mems += 2; mem[c-3] = uint32(lmem[l].watch)
			mems++; lmem[l].watch = c
			jj = 0
		} else {
			mems++; mem[c+k+jj] = uint32(l)
		}
		k++
	}
}

@* 절 재활용.
충돌이 수천 번 나면 배운 절도 수천 개가 된다. 배운 절은 헛된 길을 피하게 해 주지만
감시해야 하니 강제를 느리게 한다. 그래서 가끔 쌓인 절에 순위를 매겨 도움보다 해가
많아 보이는 것들을 솎아 낸다.

크누스는 Audemard와 Simon의 착상을 빌려 점수를 매긴다. 절 |c|의 리터럴들이 트레일의
서로 다른 수준 $p+q$개에 걸쳐 있고, 그 가운데 $p$개 수준에는 참인 리터럴이 있고
$q$개 수준의 리터럴은 모두 거짓이라 하자. 그러면 |c|의 ``범위''(range)는
$p+\alpha q$다. $\alpha=1$이면 이것은 둘이 말한 LBD(literal block distance)다.
지금 트레일의 어떤 리터럴의 까닭인 절은 반드시 남겨야 하므로 범위를 0으로 둔다.
@^Audemard, Gilles@>
@^Simon, Laurent@>

배운 절이 $h$개면 $h/2$개로 줄이되, 범위가 중앙값보다 작은 것을 남긴다. 중앙값을
정확히 구할 필요는 없다. 범위를 $\min(\lfloor16(p+\alpha q)\rfloor,255)$로 8비트
눈금에 올리면 분포를 세어 작은 것들을 쉽게 고를 수 있다.

@<자료 구조@>=
const (
	buckets  = 256  // 눈금에 올린 범위의 가짓수
	badlevel = 16.0 // 이보다 큰 범위는 사실상 무한
)

@ @<|Solve|의 지역 변수@>=
var (
	rangedist        []int    // 눈금마다 절의 수
	asserts          int      // 남겨야 하는 까닭 절의 수
	minrange         int      // 이번에 본 가장 작은 눈금
	maxrange         int      // 가장 큰 눈금
	recyclePoint     int      // 이번 전체 달리기 뒤에 배운 첫 절
	budget           int      // 재활용 뒤에 남길 절의 수
	clauseHeap       []uint64 // 활동도로 일부 정렬하는 힙
	clauseHeapSize   int      // 그 크기
	accum            uint64   // 힙에 넣을 값
	nextRecycle      uint64   // 이만큼 배우면 재활용한다
	recycleBump      uint64   // 다음 재활용까지의 간격
)

@ 절 |c|의 눈금을 매긴다. |levstamp|의 홀수 칸으로 이미 본 수준을 가려낸다. 여기 올 때
홀수 칸은 모두 |c|보다 작다. 수준 0에서 참인 리터럴이 있는 절은 영영 만족되므로 눈금
|buckets+1|을 준다. 원본은 여기서 반복 밖에서 반복 안의 레이블 |its_true|로 뛰어드는데,
\GO/에서는 안 되므로 그 두 줄을 까닭 절 쪽에 한 번 더 적었다.

곱셈과 덧셈을 한 연산으로 합치는 FMA가 끼면 부동소수점 결과가 달라질 수 있다.
\GO/는 명시적인 형 변환이 있는 곳에서는 합치지 않으므로 곱을 |float32(...)|로 감쌌다.

@<절 |c|의 눈금을 매긴다@>=
mems++; l = int(mem[c])
mems++
if lmem[l].reason == c {
	mems++
	if vmem[l>>1].value&^1 != 0 {
		mems++; mem[c-4] = 0; asserts++
	} else {
		v = buckets + 1
		mems++; mem[c-4] = buckets + 1
		goto rangeSet
	}
} else {
	@<절 |c|의 수준들을 세어 |p|와 |q|를 얻는다@>
	v = int(buckets / badlevel * float64(float32(p)+float32(par.Alpha*float32(q-p))))
	if v >= buckets {
		v = buckets - 1
	}
	mems++; mem[c-4] = uint32(v)
	minrange, maxrange = min(minrange, v), max(maxrange, v)
	mems += 2; rangedist[v]++
}
rangeSet:

@ 여기의 |q|는 앞에서 말한 $p+q$다.

@<절 |c|의 수준들을 세어...@>=
p, q = 0, 0
for k = c + int(mem[c-1]) - 1; k >= c; k-- {
	mems += 2; l = int(mem[k]); v = vmem[l>>1].value
	if v < 2 {
		if (v^l)&1 != 0 {
			continue
		}
		v = buckets + 1
		mems++; mem[c-4] = buckets + 1
		goto rangeSet
	}
	mems++
	if levstamp[(v&^1)+1] < c {
		mems++; levstamp[(v&^1)+1] = c; q++
	}
	if levstamp[(v&^1)+1] == c && (l^v)&1 == 0 {
		mems++; levstamp[(v&^1)+1] = c + 1; p++
	}
}

@ 재활용은 봄맞이 대청소 같은 큰일이다. 먼저 전체 달리기로 모든 변수에 수준과 값을
붙인다. 그다음 절마다 눈금을 매기고, 수준 0으로 되돌아가면서 새로 배운 절(|c>=recyclePoint|,
눈금이 없으므로 까닭 절처럼 친다)도 받는다. 마지막으로 배운 절을 크게 줄이면서
영영 만족된 절과 영영 거짓인 리터럴을 치우고, 감시 목록을 다시 짓는다.

@<재활용할 눈금들을 매긴다@>=
recyclePoint = maxLearned
minrange, maxrange = buckets, 0
asserts = 0
for k = 0; k < vars; k++ {
	mems++; levstamp[k+k+1] = 0
}
for h, c = 0, firstLearned; c < maxLearned; h, c = h+1, endc+learnedExtra {
	mems++; endc = c + int(mem[c-1])
	@<절 |c|의 눈금을 매긴다@>
	@<|endc|를 지워진 리터럴들 너머로 옮긴다@>
}
budget = h / 2
prevLearned = 0

@ 절을 훑을 때마다 쓰는 짧은 반복.

@<|endc|를 지워진 리터럴들...@>=
for {
	mems++
	if mem[endc]&signBit == 0 {
		break
	}
	endc++
}

@ @<배운 절의 절반을 재활용한다@>=
@<데이터베이스를 압축한다@>
@<감시 목록을 모두 다시 짓는다@>
recyclePoint = 0

@ 눈금 |j| 이하의 절이 |budget|개를 넘도록 |j|를 정한다. 문턱 눈금에서 남는 몫은
활동도로 가린다.

원본의 이 자리에는 버그가 있다. 배운 절이 모두 까닭 절이거나 수준 0에서 만족되면
눈금을 받은 절이 없어 |minrange|가 |buckets| 그대로 남는다. 그러면 원본은 |buckets|칸짜리
|rangedist|의 끝 너머 |rangedist[buckets]|를 읽는다(\.{knuth/sat13.w}의 2722행).
주소 검사기(AddressSanitizer)를 붙여 빌드한 원본에 문제 \.{queen-5x5-5}와 선택 \.{j1}을
주면 곧바로 잡힌다. 그래서 |rangedist|에 늘 0인 칸 하나를 붙여 잡았다.

@<데이터베이스를 압축한다@>=
mems++; j = minrange; sz = asserts + rangedist[j]
for sz < budget && j < maxrange {
	j++; mems++; sz += rangedist[j]
}
if sz > budget {
	@<문턱에서 |t=sz-budget|개의 절을 떨어뜨린다@>
}
for k = minrange >> 1; k+k <= maxrange; k++ {
	mems++; rangedist[k+k] = 0; rangedist[k+k+1] = 0
}
for h, cc, c = 0, firstLearned, firstLearned; c < maxLearned; c = endc + learnedExtra {
	@<절 |c|를 |cc|로 옮기거나 버린다@>
}
maxLearned = cc; prevLearned = 0
mems++; mem[maxLearned-learnedExtra] = 0

@ 절을 앞으로 당겨 옮기면서 수준 0에서 거짓인 리터럴은 빼고, 수준 0에서 참인
리터럴이 있는 절은 통째로 버린다. 지워진 리터럴 칸들도 여기서 0으로 지운다.

@<절 |c|를 |cc|로...@>=
mems++; endc = c + int(mem[c-1]); jj = endc
for {
	mems++
	if mem[endc]&signBit == 0 {
		break
	}
	mems++; mem[endc] = 0; endc++
}
if c < recyclePoint {
	mems++
	if int(mem[c-4]) > j {
		continue
	}
}
for kk, k = cc, c; k < jj; k++ {
	mems++; l = int(mem[k])
	mems++; v = vmem[l>>1].value
	if v != unset {
		if (v^l)&1 != 0 {
			continue
		}
		break
	}
	mems++; mem[kk] = uint32(l); kk++
}
if k < jj {
	continue
}
h++
@<절 |cc|를 마무리한다@>

@ 활동도 점수는 동점을 가를 때만 쓴다. 그러니 그것을 계산하고 가려내는 수고가
값어치가 있느냐고 물을 만하다. 크누스는 중앙 눈금에 절이 꽤 몰리는 문제가 적지만
분명히 있다는 Biere의 말을 따랐다.

원본은 여기서 |jj|가 양수라고 믿는다. 재활용 간격이 아주 짧으면 그 믿음이 깨진다. 눈금
|j=minrange|에서 남겨야 하는 까닭 절의 수 |asserts|가 |budget| 이상이면
|t>=rangedist[j]|여서 |jj|가 0 이하가 된다. 선택 \.{j1}을 주면 |clauseHeapSize|가 0이라
늘 그렇다. 음수인 |jj|로는 원본의 힙 세우기 반복이 음수 첨자로 절 힙의 배열 밖을
읽는다(\.{knuth/sat13.w}의 2793행, 문제 \.{mutex-fourbits-lemmas-1}에 \.{j2 J1}). 0인
|jj|로는 빈 힙의 초기화되지 않은 |clause_heap[0]|과 견주고, 그 값에서 나온 주소에 눈금을
쓴다(2816행과 2820행). 이것은 배열 안쪽이라 주소 검사기도 잡지 못한다. 문제
\.{poset-nomax-b-12-minus-one}에 \.{j2 J1}을 주면 |asserts=budget=3|,
|t=rangedist[j]=1|에서 여기에 들고, 최적화해 빌드한 원본은 세그폴트로 죽는다.

그런 때는 힙을 쓰지 않고 |j|를 하나 줄여 문턱 눈금의 절을 모두 떨어뜨린다. 대개는 그것이
곧 |t|개이고, 힙 크기가 0일 때만 필요보다 많이 버린다. 원본이 제대로 도는 경우에는 이
갈래로 들어오지 않으므로 mem 수는 그대로다. 간격이 짧아도 원본이 이 조건에 들지 않은
실행, 가령 벤치마크 셋에 \.{j10 J5}를 준 실행은 원본과 mem이 같았다.

@<문턱에서 |t=sz-budget|개의...@>=
t = sz - budget
jj = min(rangedist[j]-t, clauseHeapSize)
if jj <= 0 {
	j--
} else {
	@<눈금이 |j|인 절 |jj|개를 절 힙에 넣는다@>
	@<절 힙을 힙 차례로 세운다@>
	@<눈금이 |j|인 절 |t|개의 눈금을 |j+1|로 올린다@>
}

@ 절 힙의 값은 활동도가 먼저, 자리가 다음으로 정렬되게 묶는다. 활동도가 똑같이
낮으면 활발해질 시간이 더 많았던 쪽, 곧 먼저 배운 쪽을 잊는다. 음이 아닌 |float|는
비트를 정수로 보고 견주어도 크기 차례가 같다.

@<눈금이 |j|인 절 |jj|개를...@>=
for h, c = 0, firstLearned; h < jj; c = endc + learnedExtra {
	if c >= recyclePoint {
		panic("sat: 이럴 수는 없다 (rangedist1)")
	}
	mems++; endc = c + int(mem[c-1])
	@<|endc|를 지워진 리터럴들...@>
	mems++
	if int(mem[c-4]) == j {
		clauseHeap[h] = uint64(mem[c-5])<<32 + uint64(c); h++
	}
}

@ @<절 힙을 힙 차례로...@>=
for h = jj >> 1; h != 0; {
	q = h + h; h--; p = h
	mems++; accum = clauseHeap[p]
	@<|accum|을 절 힙의 |p|에서 내려보낸다@>
}

@ 여기 올 때 |q=p+p+2|다. 이 힙은 뿌리에 가장 {\it 큰\/} 값이 온다.

@<|accum|을 절 힙의...@>=
for q <= jj {
	if q == jj {
		q--
	} else {
		mems += 2
		if clauseHeap[q-1] < clauseHeap[q] {
			q--
		}
	}
	if accum <= clauseHeap[q] {
		break
	}
	mems++; clauseHeap[p] = clauseHeap[q]
	p, q = q, q+q+2
}
mems++; clauseHeap[p] = accum

@ 힙에 넣고 멈춘 곳부터 이어서 눈금이 |j|인 절을 더 찾는다. 새로 만난 절이 힙의
뿌리보다 작으면 그 절을, 아니면 뿌리의 절을 떨어뜨리고 새 절을 힙에 넣는다.

@<눈금이 |j|인 절 |t|개의...@>=
for ; ; c = endc + learnedExtra {
	if c >= recyclePoint {
		panic("sat: 이럴 수는 없다 (rangedist2)")
	}
	mems++
	if int(mem[c-4]) == j {
		mems++; accum = uint64(mem[c-5])<<32 + uint64(c)
		mems++
		if accum < clauseHeap[0] {
			mems++; mem[c-4] = uint32(j + 1)
			if t--; t == 0 {
				break
			}
		} else {
			mems++; mem[int(clauseHeap[0]&0xffffffff)-4] = uint32(j + 1)
			if t--; t == 0 {
				break
			}
			p, q = 0, 2
			@<|accum|을 절 힙의...@>
		}
	}
	mems++; endc = c + int(mem[c-1])
	@<|endc|를 지워진 리터럴들...@>
}

@ 여기서는 수준 0에 있다. 남길 절의 리터럴을 |mem[cc]|부터 |mem[kk-1]|까지 옮겼다.
드물게는 줄이고 나니 크기가 1이 되거나, 0이 되기도 한다. 크기가 1이면 수준 0에서
강제하고, 0이면 만족할 수 없다. 원본은 크기와 활동도를 이 차례로 적는다. 앞으로 당긴
칸이 |c|의 머리를 덮었을 수도 있으니 차례를 바꾸면 안 된다.

@<절 |cc|를 마무리한다@>=
if kk >= cc+2 {
	mems += 3; mem[cc-1] = uint32(kk - cc); mem[cc-5] = mem[c-5]; cc = kk + learnedExtra
} else if kk == cc {
	goto unsat
} else {
	mems++; l = int(mem[cc])
	mems++; vmem[l>>1].value = l & 1; vmem[l>>1].tloc = eptr
	mems++; trail[eptr] = l; eptr++
}

@ 감시 목록을 처음부터 다시 짓는다. 입력 절에는 지워진 리터럴이 남아 있을 수 있으므로
그 너머로 건너뛴다. 원본은 |mem[c+1]|을 읽을 때와 |link1(c)|에 쓸 때 가운데 한 번의
접근을 아낀다고 보고 셈을 맞춘다.

@<감시 목록을 모두...@>=
for l = 2; l <= maxLit; l++ {
	mems++; lmem[l].watch = 0
}
for c = clauseExtra; c < minLearned; c = endc + clauseExtra {
	mems++; endc = c + int(mem[c-1])
	@<절 |c|의 앞 두 리터럴로 감시한다@>
	@<|endc|를 지워진 리터럴들...@>
}
for c = firstLearned; c < maxLearned; c = endc + learnedExtra {
	mems++; endc = c + int(mem[c-1])
	@<절 |c|의 앞 두 리터럴로 감시한다@>
}

@ @<절 |c|의 앞 두 리터럴로...@>=
mems++; l = int(mem[c])
mems += 3; mem[c-2] = uint32(lmem[l].watch); lmem[l].watch = c
l = int(mem[c+1])
mems += 3; mem[c-3] = uint32(lmem[l].watch); lmem[l].watch = c

@* 모두 엮기.
필요한 장치는 다 갖췄다. 이제 알맞은 때에 움직이게 하면 된다. 원본의 레이블
|startup|, |proceed|, |confl|, |unsat|, |satisfied|, |all_done|은 이름만 \GO/식으로
바꿔 그대로 둔다. 원본에서 블록 안에 있던 |prep_clause|와 |store_clause|를 바깥으로
꺼내려고, 전체 달리기를 마무리하는 코드를 |eptr==vars|를 따지는 블록 밖으로 옮겨
레이블 |finishFull|을 붙였다.

@<문제를 푼다@>=
startup:
	conflictLevel = 0
	fullRun = warmupCycles < par.Warmups
proceed:
	conflictSeen = false
	@<지금 수준을 마무리한다; 충돌이면 |goto confl|@>
	@<한도에 이르렀으면 |goto allDone|@>
	if eptr == vars {
		if conflictLevel == 0 {
			@<아직 참이 아닌 가정 리터럴 |l|을 찾는다; 거짓이면 |goto failed|@>
			goto satisfied
		}
		goto finishFull
	}
	if conflictLevel == 0 {
		@<doomsday와 재활용과 다시 시작을 살핀다@>
	}
	@<새 수준을 열고 결정 리터럴을 올린다@>
	goto proceed
@<전체 달리기를 마무리한다@>
@<지금의 충돌을 푼다@>

@ 트레일에 충돌한 리터럴이 없을 때만 이것들을 살핀다.

@<doomsday와 재활용과...@>=
if totalLearned >= doomsday {
	err = ErrDoomsday
	goto allDone
}
if totalLearned >= nextRecycle {
	fullRun = true
} else if totalLearned >= nextRestart {
	@<|agility|가 높지 않으면 다시 시작한다@>
}

@ 결정 리터럴은 까닭이 0이다. 여기 올 때 |lptr|은 |eptr|과 같으므로, 트레일에 올린
뒤의 |lptr|은 새 리터럴의 자리다. 아직 값이 없는 가정 리터럴이 있으면 그것이 먼저
결정된다.

@<새 수준을 열고...@>=
@<아직 참이 아닌 가정 리터럴 |l|을 찾는다...@>
llevel += 2
if l == 0 {
	@<다음 결정 리터럴 |l|을 고른다@>
}
mems++; lmem[l].reason = 0
nodes++
mems++; leveldat[llevel] = eptr
mems++; trail[eptr] = l; eptr++
mems++; vmem[l>>1].tloc = lptr
vmem[l>>1].value = llevel + l&1
agility -= agility >> 13

@ 원본은 mem이 한도에 이르렀는지 여기서만 살핀다. 부른 쪽이 |context|를 거두었는지도
여기서 살피되, 매번 묻지 않고 mem이 $2^{22}$쯤 늘 때마다 묻는다. 이것은 mem을 세지
않으므로 원본과의 셈에 끼어들지 않는다.

@<한도에 이르렀으면...@>=
if mems >= par.Timeout {
	err = ErrTimeout
	goto allDone
}
if mems >= nextCheck {
	nextCheck = mems + checkEvery
	if e := ctx.Err(); e != nil {
		err = e
		goto allDone
	}
}

@ @<자료 구조@>=
const checkEvery = 1 << 22 // |context|를 묻는 mem 간격

@ 처음 풀 때만 하는 초기화다. 풀이마다 새로 정하는 값들은 따로 떼어 두었다. 원본에서는
두 무리가 섞여 있지만 mem을 세는 것은 |leveldat|을 비우는 반복뿐이라, 차례를 바꾸어도
수가 같다.

@<초기화를 마친다@>=
@<풀이마다 새로 정하는 값들을 정한다@>
recycleBump = par.RecycleBump
nextRecycle = min(recycleBump, doomsday)
restartU, restartV, nextRestart = 1, 1, 1
@<|leveldat|을 비워 둔다@>
llevel, warmupCycles, lptr = 0, 0, 0

@ |Doomsday|는 이번 풀이에서 배운 절의 수로 따진다. 처음 풀 때는 |totalLearned|가
0이니 원본과 같다.

@<풀이마다 새로 정하는 값들을 정한다@>=
if par.RandProb >= 1.0 {
	randProbThresh = 0x80000000
} else {
	randProbThresh = int(float64(par.RandProb) * 2147483648.0)
}
varBumpFactor = 1.0 / float64(par.VarRho)
clauseBumpFactor = float32(1.0 / float64(par.ClauseRho))
restartPsi = uint64(4294967296.0 * float64(par.RestartPsiFraction))
nextCheck = checkEvery
learnedBase = totalLearned
doomsday = totalLearned + min(par.Doomsday, math.MaxUint64-totalLearned)

@ @<|leveldat|을 비워 둔다@>=
for k = 0; k < vars; k++ {
	mems++; leveldat[k+k] = -1; leveldat[k+k+1] = 0
}

@ 트레일에서 아직 보지 않은 리터럴마다 이진 함의와 긴 절 함의를 따라간다. 이진
함의는 새로 올라온 리터럴에 대해 이미 곧바로 따라갔으므로, |ebptr| 뒤의 것은 다시
보지 않는다.

@<지금 수준을 마무리한다...@>=
ebptr = eptr
for lptr < eptr {
	mems++; lt = trail[lptr]; lptr++
	if lptr <= ebptr {
		mems++; lat = lmem[lt].bimpEnd
		if lat != 0 {
			l = lt
			@<|l|의 이진 함의를 전파한다...@>
		}
	}
	@<|lt|의 긴 절 함의를 전파한다...@>
}

@ 되추적은 수준 |jumplev| 위의 리터럴들을 트레일에서 걷어 낸다. 값은 |oldval|에
남겨 두고(위상 저장), 까닭을 지우고, 힙에서 빠진 변수는 다시 넣는다. 아직 긴 절
함의를 보지 않은 리터럴(|eptr>=lptr|)은 결정할 때 힙에서 꺼낸 적이 없다.

@<|jumplev|로 되추적한다@>=
mems++; k = leveldat[jumplev+2]
for eptr > k {
	eptr--; mems++; l = trail[eptr]; v = l >> 1
	mems += 2; vmem[v].oldval = vmem[v].value
	mems++; vmem[v].value = unset
	mems++; lmem[l].reason = 0
	if eptr < lptr {
		mems++
		if vmem[v].hloc < 0 {
			@<|v|를 힙에 넣는다@>
		}
	}
}
lptr = eptr
llevel = jumplev

@ 충돌을 푼다. 수준 0의 충돌이면 만족할 수 없다. 아니면 절을 배우고, 돌아갈 수준으로
되추적한 뒤, 거짓이던 |lll|을 참으로 올린다. 배운 절이 단위 절이면 까닭 없이 수준 0에
올라간다. 원본은 이 |agility| 갱신에 32비트 넘침이 이론상 가능한 ``벌레''가 있다고
적었다. 실제로는 일어나지 않고, 일어나도 큰 해가 없다고 한다.

@<지금의 충돌을 푼다@>=
confl:
	if llevel == 0 {
		goto unsat
	}
prepClause:
	@<충돌 절 |c|를 다룬다@>
	@<배울 절을 줄인다@>
	if fullRun {
		goto storeClause
	}
	@<|jumplev|로 되추적한다@>
	if learnedSize > 1 {
		@<줄인 절을 배운다@>
		mems++; lmem[lll].reason = c
	}
	mems++; vmem[lll>>1].value = llevel + lll&1; vmem[lll>>1].tloc = eptr
	mems++; trail[eptr] = lll; eptr++
	agility -= agility >> 13
	agility += 1 << 19
	@<올릴 몫을 키운다@>
	goto proceed

@ 전체 달리기로 모든 변수에 값이 붙었으면, 기록해 둔 충돌들에서 차례로 배운다. 수준
$l_i$에서 배운 절 $c_i$는 거기서 거짓이던 리터럴 $u_i$를 더 낮은 수준 $l'_i$에서
참으로 만든다. 그 가운데 가장 낮은 수준 |minjumplev|로 되추적한다.

원본은 충돌마다 |goto prep_clause|로 충돌을 풀러 갔다가 |goto store_clause|로
반복 한가운데로 돌아온다. 여기서는 그 반복을 레이블 |learnFull|로 풀어 적었다.

@<전체 달리기를 마무리한다@>=
finishFull:
	if totalLearned >= nextRecycle {
		@<재활용할 눈금들을 매긴다@>
	} else {
		warmupCycles++
	}
	mems++; leveldat[llevel+2] = eptr
	minjumplev = maxLit
learnFull:
	if conflictLevel == 0 {
		goto learnedFull
	}
	mems++; jumplev = conflictLevel; conflictLevel = conflictdat[conflictLevel]
	@<|jumplev|로 되추적한다@>
	mems++; c = leveldat[llevel+1]
	if c < 0 {
		mems++; l = -c; ll = conflictdat[llevel+1]
	}
	goto prepClause
storeClause:
	@<전체 달리기에서 배운 절을 간수한다@>
	goto learnFull
learnedFull:
	@<전체 달리기의 뒷정리를 한다@>
	goto startup

@ 전체 달리기에서 나온 자명한 절은 첫 충돌 수준의 것이 아니면 버린다. 더 높은
수준에서는 쓸모가 없기 때문이다. |minjumplev|에서 배운 리터럴들은 |conflictdat|
안의 더미로 엮어 둔다. 그 꼭대기가 |nextLearned|다.

@<전체 달리기에서 배운 절을...@>=
if trivialLearning && conflictLevel != 0 {
	cellsPrelearned -= float64(prelearnedSize)
	cellsLearned -= float64(learnedSize); totalLearned--; trivials--
} else {
	if jumplev <= minjumplev {
		if jumplev < minjumplev {
			minjumplev = jumplev; nextLearned = 0
		}
		mems++; conflictdat[llevel] = nextLearned; conflictdat[llevel+1] = lll
		nextLearned = llevel
	}
	if learnedSize == 1 {
		mems++; leveldat[llevel+1] = 0
	} else {
		@<줄인 절을 배운다@>
		mems++; leveldat[llevel+1] = c
	}
}

@ 재활용하는 길이었으면 수준 0까지 내려간다.

@<전체 달리기의 뒷정리를...@>=
if recyclePoint != 0 {
	jumplev = 0
} else {
	jumplev = minjumplev
}
@<|jumplev|로 되추적한다@>
if jumplev == minjumplev {
	@<|minjumplev|에서 배운 리터럴들을 트레일 끝에 놓는다@>
}
@<올릴 몫을 키운다@>
if recyclePoint != 0 {
	@<배운 절의 절반을 재활용한다@>
	recycleBump += par.RecycleInc
	nextRecycle = min(totalLearned+recycleBump, doomsday)
}

@ @<|minjumplev|에서 배운 리터럴들을...@>=
for nextLearned != 0 {
	mems++; lll = conflictdat[nextLearned+1]
	mems++; c = leveldat[nextLearned+1]
	nextLearned = conflictdat[nextLearned]
	mems++; vmem[lll>>1].value = llevel + lll&1; vmem[lll>>1].tloc = eptr
	mems++; lmem[lll].reason = c
	mems++; trail[eptr] = lll; eptr++
}

@ Biere의 권고를 따라, 값이 최근에 많이 뒤집히면(|agility|가 높으면) 다시 시작하지
않는다. 다음 다시 시작까지가 멀수록 문턱이 높다. 간격은 Knuth와 Luby의 ``주저하는
두 배'' 수열 $1,1,2,1,1,2,4,1,\ldots$을 따른다. |restartU|와 |restartV|가 그 수열을
만든다.
@^Biere, Armin@>

@<|agility|가 높지 않으면...@>=
if restartU&-restartU == restartV {
	restartU++; restartV = 1; restartThresh = restartPsi
} else {
	restartV <<= 1; restartThresh += restartThresh >> 4
}
nextRestart = min(totalLearned+uint64(restartV), doomsday)
if uint64(agility) <= restartThresh {
	@<리터럴들을 흘려보낸다@>
}

@ 수준 0까지 다 되돌리는 대신 van der Tak, Ramos, Heule의 권고를 따른다. 새 변수가
트레일에 들어갈 첫 수준으로만 돌아간다. 그 새 변수는 값이 없는 변수 가운데 활동도가
가장 큰 것이다. 되추적할 필요가 아예 없을 때도 있다. 크누스는 책에서 이것을 ``다시
시작''이 아니라 ``흘려보내기''(flushing)라 부르기로 했다.
@^Heule, Marijn Johannes Hendrikus@>

@<리터럴들을 흘려보낸다@>=
actualRestarts++
if llevel != 0 {
	for {
		mems++; v = heap[0]
		mems++
		if vmem[v].value == unset {
			break
		}
		@<|v|를 힙에서 지운다@>
	}
	mems++; av = vmem[v].activity
	for jumplev = 0; jumplev < llevel; jumplev += 2 {
		mems += 2; v = trail[leveldat[jumplev+2]] >> 1
		mems++
		if vmem[v].activity < av {
			break
		}
	}
	if jumplev < llevel {
		@<|jumplev|로 되추적한다@>
	}
}
warmupCycles = 0
goto startup

@ @<|Solve|의 지역 변수@>=
var (
	warmupCycles              int    // 다시 시작한 뒤의 전체 달리기 수
	nextLearned               int    // |minjumplev|에서 배운 리터럴 더미의 꼭대기
	minjumplev                int    // 전체 달리기 뒤 돌아갈 수준
	restartU, restartV        int    // 주저하는 두 배 수열
	restartThresh, restartPsi uint64 // 다시 시작하는 |agility| 문턱
	nextRestart               uint64 // 이만큼 배우면 다시 시작을 살핀다
	actualRestarts            uint64 // 실제로 다시 시작한 수
	nextCheck                 uint64 // 다음에 |context|를 물을 mem
)

@* 가정 리터럴.
여기서부터는 원본에 없는 것이다. 점진적 풀이를 쓰는 프로그램은 흔히 같은 절들에 조건을
조금씩 바꿔 가며 묻는다. ``$x$가 참이고 $y$가 거짓이면 만족할 수 있는가?'' 조건을 단위
절로 보태면 다음 물음에서 거둘 수가 없다. 그래서 E\'en과 S\"orensson은 MiniSat에
{\it 가정 리터럴\/}(assumption)을 두었다. 가정은 절이 아니라, 푸는 동안 맨 아래
수준들에서 억지로 내리는 결정이다. 결정일 뿐이니 배운 절은 가정에 기대지 않고, 다음
물음에서도 그대로 쓸 수 있다.
@^E\'en, Niklas@>
@^S\"orensson, Niklas@>

|Solve|는 가변 인자로 가정들을 받는다. 가정 아래에서 만족할 수 없으면 |Unsat|을 돌려주고,
|Failed|는 주어진 가정들 가운데 그 결론에 책임이 있는 것들을 알려 준다. |Failed|가
비어 있으면 가정과 상관없이 만족할 수 없다는 뜻이다. 거꾸로는 아니다. 절만으로 만족할 수
없음을 증명하기 전에 거짓인 가정을 먼저 만나면 그 가정을 탓하기 때문이다.

mem은 원본과 같은 방식으로 센다. 견줄 원본은 없지만 |Timeout|이 같은 잣대로 들어야 하기
때문이다. 가정이 없으면 여기 보탠 코드는 mem을 하나도 세지 않는다.

@<함수들@>=
func (s *Solver) Failed() []Lit { return slices.Clone(s.failed) }

@ 가정도 절의 리터럴처럼 이 풀이기의 것이어야 한다.

@<가정 리터럴들을 확인한다@>=
s.failed = nil
for _, a := range assumptions {
	if v := a.Var(); v == 0 || v >= len(s.names) {
		panic(fmt.Sprintf("sat: 없는 변수의 가정 %d", uint32(a)))
	}
}
asm, ai, acheck = assumptions, 0, make([]int, len(assumptions))

@ @<|Solve|의 지역 변수@>=
var (
	asm    []Lit // 가정들
	ai     int   // 살핀 가정의 수
	acheck []int // 가정들이 모두 참이 된 수준
)

@ 가정은 결정 리터럴을 고르기 직전에 살핀다. 가정을 차례로 보되, 이미 참이면 건너뛰고,
값이 없으면 그것을 결정 리터럴로 삼고, 거짓이면 가정 아래에서 만족할 수 없다.

MiniSat은 이미 참인 가정에도 빈 수준을 하나씩 열어 수준 번호와 가정 번호를 맞춘다.
여기서는 그럴 수 없다. \.{SAT13}은 수준마다 첫 리터럴이 결정이라고 믿기
때문이다(자명한 절과 흘려보내기가 |trail[leveldat[k]]|를 읽는다). 그래서 따로 적어 둔다.
|acheck[i]|는 가정 |asm[0]|부터 |asm[i]|까지가 모두 참이 된 가장 높은 수준의 두 배다.
|ai|개를 살핀 뒤 되추적이 그 가운데 몇을 풀어 주었다면 |acheck[ai-1]|이 지금 수준보다
높을 것이니, |ai|를 줄여 다시 살핀다.

그러면 가정을 살피는 동안 트레일의 결정은 모두 가정이다. 가정이 아닌 결정은 가정을 모두
살핀 뒤에야 내리고, 그 뒤로 |ai|가 줄어드는 것은 그 결정보다 낮게 되추적했을 때뿐이기
때문이다. 책임질 가정을 모을 때 이 성질을 쓴다.

@<아직 참이 아닌 가정 리터럴 |l|을 찾는다; 거짓이면 |goto failed|@>=
l = 0
for ai > 0 && acheck[ai-1] > llevel {
	ai--
}
for ; ai < len(asm); ai++ {
	@<가정 |asm[ai]|를 살핀다; 값이 없으면 |l|에 두고 |break|@>
}

@ 전체 달리기에서 충돌을 이미 기록했다면(|conflictLevel!=0|) 트레일이 어긋나 있을 수
있다. 그때 거짓인 가정은 믿을 수 없으니 건너뛰고 지금 수준을 적어 둔다. 전체 달리기가
끝나면 첫 충돌 수준보다 낮게 되추적하므로 그 가정은 다시 살피게 된다.

@<가정 |asm[ai]|를...@>=
t = 0
if ai > 0 {
	t = acheck[ai-1]
}
mems++; u = int(asm[ai]); v = vmem[u>>1].value
if v == unset {
	l, acheck[ai] = u, llevel+2
	ai++
	break
}
if (v^u)&1 == 0 {
	acheck[ai] = max(t, v&^1)
} else if conflictLevel == 0 {
	l = u
	goto failed
} else {
	acheck[ai] = max(t, llevel)
}

@ 가정 |l|이 거짓으로 드러났다. $\bar l$의 까닭을 트레일에서 거슬러 올라가며 거기 쓰인
결정들을 모으면, 그것이 책임이 있는 가정들이다. MiniSat의 |analyzeFinal|과 같은 일이다.
충돌에서 배울 때의 도장을 빌려 쓰되 분해한 절은 만들지 않는다. 수준 0의 리터럴은 가정
없이도 참이니 따라가지 않는다.

@<실패한 가정 |l|에...@>=
@<|curstamp|를 새 값으로...@>
mems++; vmem[l>>1].stamp = curstamp
if llevel != 0 {
	mems++; t = leveldat[2]
	for j = eptr - 1; j >= t; j-- {
		mems++; ll = trail[j]
		mems++
		if vmem[ll>>1].stamp != curstamp {
			continue
		}
		@<|ll|의 까닭에 든 리터럴들에 도장을 찍는다@>
	}
}
@<도장이 찍힌 가정들을 |s.failed|에 모은다@>

@ 결정이면 도장을 |curstamp+1|로 바꾸어 책임이 있다는 표를 남긴다.

@<|ll|의 까닭에 든...@>=
mems++; c = lmem[ll].reason
if c == 0 {
	mems++; vmem[ll>>1].stamp = curstamp + 1
} else if c < 0 {
	lll = -c
	@<수준 0이 아니면 |lll|의 변수에 도장을 찍는다@>
} else {
	mems++; sz = int(mem[c-1])
	for k = c + sz - 1; k > c; k-- {
		mems++; lll = int(mem[k])
		@<수준 0이 아니면...@>
	}
}

@ @<수준 0이 아니면...@>=
mems++
if vmem[lll>>1].value&^1 != 0 {
	mems++; vmem[lll>>1].stamp = curstamp
}

@ 주어진 차례대로 모으고, 같은 가정이 두 번 있으면 한 번만 넣는다. 거짓으로 드러난 |l|
자신은 늘 들어간다. 같은 수의 두 리터럴을 함께 가정했다면 둘 다 들어간다.

@<도장이 찍힌 가정들을...@>=
for i = 0; i < len(asm); i++ {
	u = int(asm[i]); v = u >> 1
	mems++
	if u == l {
		l = 0
	} else if vmem[v].stamp == curstamp+1 && (vmem[v].value^u)&1 == 0 {
		mems++; vmem[v].stamp = curstamp + 2
	} else {
		continue
	}
	s.failed = append(s.failed, Lit(u))
}

@* 풀이 사이에 간직하기.
|Solve|를 다시 부르면 처음부터 새로 짓지 않고 지난 풀이의 상태를 이어 쓴다. 배운 절,
변수의 활동도와 옛 값, 수준 0에서 참이 된 리터럴, 재활용과 다시 시작의 일정, 난수열이
모두 이어진다. 배운 절과 수준 0의 리터럴은 입력 절만으로 따라 나오는 것이니 절을 더
보태도 여전히 참이다. 가정은 결정일 뿐이므로 거기에 기댄 것도 없다.

그래서 풀이기는 풀고 난 뒤 크누스의 전역 변수들을 |cdclState|에 담아 두고, 다음 |Solve|는
그것들을 지역 변수로 도로 불러온다. 조각(slice)은 참조이므로 담고 부르는 품이 작다.
원본의 코드가 지역 변수를 그대로 쓰니 손댈 곳도 없다. 필드를 곧바로 쓰지 않는 까닭이
하나 더 있다. \GO/ 컴파일러는 지역 변수를 레지스터에 둘 수 있지만, 필드에 닿으려면 늘
포인터를 거쳐야 한다.

@<자료 구조@>=
type cdclState struct {
	key                  Params // |Timeout|과 |Doomsday|를 0으로 둔 매개변수
	unsat                bool   // 가정 없이도 만족할 수 없는가
	rng                  *gbflip.RNG
	vars, clauses, cells int
	bytes                uint64
	@<|cdclState|의 필드@>
}

@ 나머지 필드는 |Solve|의 같은 이름의 지역 변수를 담는다.

@<|cdclState|의 필드@>=
mem, bmem                             []uint32
memsize, minLearned, firstLearned     int
maxLearned, maxCellsUsed, maxLit      int
lmem                                  []literal
vmem                                  []variable
heap, trail, leveldat, conflictdat    []int
learn, stack, levstamp, rangedist     []int
hn, eptr, lptr, llevel                int
agility                               uint32
varBump                               float64
clauseBump                            float32
curstamp, prevLearned, clauseHeapSize int
totalLearned, nextRecycle, recycleBump uint64
clauseHeap                            []uint64
warmupCycles, restartU, restartV      int
restartThresh, nextRestart            uint64

@ @<|Solve|의 지역 변수@>=
var (
	key           Params // 상태를 이어 쓸 수 있는지 가르는 매개변수
	unsatisfiable bool   // 가정 없이도 만족할 수 없는가
	learnedBase   uint64 // 이번 풀이를 시작할 때의 |totalLearned|
	doomsday      uint64 // 이번 풀이에서 배운 절 수의 한도
)

@ 간직한 상태를 버리고 처음부터 짓는 때가 둘 있다. |mem|이 모자랐으면 상태가 반쯤 고쳐진
채일 수 있으니 버린다. 매개변수를 바꾸었어도 버린다(|Solve|의 뼈대가 |key|를 견준다).
다만 |Timeout|과 |Doomsday|는 풀이마다 새로 정하는 한도이므로 바꾸어도 이어 쓴다.
그러니 다른 매개변수를 한 번 바꾸었다 되돌리면 원본과 같은 mem 수를 다시 볼 수 있다.

@<풀이의 상태를 간직한다@>=
if err == ErrMemory {
	s.state = nil
} else {
	s.state = &cdclState{key: key, unsat: unsatisfiable, rng: rng,
		vars: vars, clauses: clauses, cells: cells, bytes: bytes,
		@<|cdclState|의 필드를 채운다@>
	}
}

@ @<|cdclState|의 필드를 채운다@>=
mem: mem, bmem: bmem, memsize: memsize, minLearned: minLearned,
firstLearned: firstLearned, maxLearned: maxLearned,
maxCellsUsed: maxCellsUsed, maxLit: maxLit, lmem: lmem, vmem: vmem,
heap: heap, trail: trail, leveldat: leveldat, conflictdat: conflictdat,
learn: learn, stack: stack, levstamp: levstamp, rangedist: rangedist,
hn: hn, eptr: eptr, lptr: lptr, llevel: llevel, agility: agility,
varBump: varBump, clauseBump: clauseBump, curstamp: curstamp,
prevLearned: prevLearned, clauseHeapSize: clauseHeapSize,
totalLearned: totalLearned, nextRecycle: nextRecycle,
recycleBump: recycleBump, clauseHeap: clauseHeap,
warmupCycles: warmupCycles, restartU: restartU, restartV: restartV,
restartThresh: restartThresh, nextRestart: nextRestart,

@ 이어 쓸 때는 상태를 불러오고, 수준 0으로 되돌아가고, 절이나 변수가 새로 들어왔으면
다시 짓는다. 만족할 수 없음이 이미 드러났으면 절을 더 보태도 마찬가지이니 곧바로 답한다.

@<간직한 상태로 풀이를 준비한다@>=
@<간직한 상태를 불러온다@>
if unsatisfiable {
	goto unsat
}
@<수준 0으로 되돌아간다@>
if vars != s.NumVars() || cells != len(s.cells) {
	@<새 절과 새 변수를 들여 다시 짓는다@>
}
imems, mems = mems, 0
@<풀이마다 새로 정하는 값들을 정한다@>

@ @<간직한 상태를 불러온다@>=
d := s.state
unsatisfiable, rng, vars, clauses, cells = d.unsat, d.rng, d.vars, d.clauses, d.cells
bytes, mem, bmem, memsize = d.bytes, d.mem, d.bmem, d.memsize
minLearned, firstLearned, maxLearned = d.minLearned, d.firstLearned, d.maxLearned
maxCellsUsed, maxLit, lmem, vmem = d.maxCellsUsed, d.maxLit, d.lmem, d.vmem
heap, trail, leveldat, conflictdat = d.heap, d.trail, d.leveldat, d.conflictdat
learn, stack, levstamp, rangedist = d.learn, d.stack, d.levstamp, d.rangedist
hn, eptr, lptr, llevel, agility = d.hn, d.eptr, d.lptr, d.llevel, d.agility
varBump, clauseBump, curstamp = d.varBump, d.clauseBump, d.curstamp
prevLearned, clauseHeapSize, clauseHeap = d.prevLearned, d.clauseHeapSize, d.clauseHeap
totalLearned, nextRecycle, recycleBump = d.totalLearned, d.nextRecycle, d.recycleBump
warmupCycles, restartU, restartV = d.warmupCycles, d.restartU, d.restartV
restartThresh, nextRestart = d.restartThresh, d.nextRestart

@ 지난 풀이는 어느 수준에서든 멈췄을 수 있다. 멈추는 곳은 늘 강제를 마친 뒤이므로 수준
0의 리터럴은 모두 전파되어 있다. 해를 찾았다면 모든 변수에 값이 있는데, 수준 0으로
되추적하면 그 값들이 |oldval|에 남는다. 그러니 다음 풀이는 지난 해 가까이에서 찾기
시작한다. 해를 하나씩 막는 절을 더해 가며 모두 세는 프로그램에 딱 맞는 성질이다.

@<수준 0으로 되돌아간다@>=
if llevel != 0 {
	jumplev = 0
	@<|jumplev|로 되추적한다@>
}

@ 절이나 변수가 새로 들어왔으면 다시 짓는다. 이진 함의 |bmem|은 리터럴마다 빈틈 없이
붙은 구간이라 사이에 끼워 넣을 수 없다. 입력 절은 |mem|에서 배운 절보다 앞에 있어야
재활용이 건드리지 않는다. 그러니 가장 곧은 길은 원본의 짓는 절들을 한 번 더 돌리는 것이다.
활동도와 옛 값, 힙의 차례는 그대로 두고, 배운 절은 새 |mem|의 뒤쪽으로 옮겨 심고, 수준
0의 리터럴은 트레일에 되돌린다. 조금씩 보태며 자주 푼다면 짓는 품이 들지만, 원본의
코드를 그대로 쓸 수 있다는 값어치가 더 크다고 보았다.

되돌린 리터럴은 |lptr=0|부터 모두 다시 전파한다. 새 입력 절이 그 리터럴들의 부정을
감시하고 있을지도 모르기 때문이다.

@<새 절과 새 변수를 들여 다시 짓는다@>=
zero = append(zero[:0], trail[:eptr]...)
for _, l = range zero {
	mems++; vmem[l>>1].value = unset
}
oldMem, oldFirst, oldMax = mem, firstLearned, maxLearned
vars, clauses, cells = s.NumVars(), s.clauses, len(s.cells)
bytes = uint64(vars+1)*40 + uint64(vars)*4
@<새 변수들을 |vmem|과 힙에 들인다@>
@<다른 주 배열들을 마련한다@>
@<임시 칸들을 |mem|, |bmem|, |trail|로 옮긴다@>
@<보조 배열들을 마련한다@>
@<|leveldat|을 비워 둔다@>
for _, l = range zero {
	@<리터럴 |l|을 수준 0의 트레일에 올린다...@>
}
@<간직한 배운 절들을 새 |mem|에 옮겨 심는다@>
lptr, prevLearned = 0, 0

@ @<|Solve|의 지역 변수@>=
var (
	zero             []int    // 떼어 둔 수준 0의 리터럴들
	oldMem           []uint32 // 옮겨 심을 배운 절이 든 옛 |mem|
	oldFirst, oldMax int      // 옛 |mem|에서 배운 절의 구간
)

@ 새 변수는 원본이 처음에 하던 대로 활동도 0과 무작위 처음 값으로 힙에 넣는다. 활동도가
0이니 힙의 맨 끝에 붙는다.

@<새 변수들을 |vmem|과 힙에 들인다@>=
@<|trueProbThresh|를 정한다@>
for k = len(vmem); k <= vars; k++ {
	mems++; vmem = append(vmem, variable{value: unset, tloc: -1, oldval: 1})
	heap = append(heap, 0)
	v = k
	if trueProbThresh != 0 {
		mems += 4
		if int(rng.Next()) < trueProbThresh {
			vmem[v].oldval = 0
		}
	}
	@<|v|를 힙에 넣는다@>
}

@ 배운 절을 하나씩 새 |mem|의 뒤에 옮긴다. 재활용의 압축과 같은 방법으로, 수준 0에서
거짓인 리터럴은 빼고 참인 리터럴이 있는 절은 버린다. 크기가 1로 줄면 수준 0에서
강제하고, 0이 되면 만족할 수 없다. 활동도는 그대로 옮기고, 범위는 다음 재활용이 새로
매긴다.

@<간직한 배운 절들을...@>=
for q = oldFirst; q < oldMax; q = endc + learnedExtra {
	mems++; endc = q + int(oldMem[q-1]); jj = endc
	for {
		mems++
		if oldMem[endc]&signBit == 0 {
			break
		}
		endc++
	}
	@<옛 절 |q|를 |maxLearned|에 옮기거나 버린다@>
}
mems++; mem[maxLearned-learnedExtra] = 0

@ @<옛 절 |q|를...@>=
c = maxLearned
@<|mem|에 절 |q|가 들어갈 자리를 마련한다@>
for kk, k = c, q; k < jj; k++ {
	mems++; l = int(oldMem[k])
	mems++; v = vmem[l>>1].value
	if v != unset {
		if (v^l)&1 != 0 {
			continue
		}
		break
	}
	mems++; mem[kk] = uint32(l); kk++
}
if k < jj {
	continue
}
if kk >= c+2 {
	mems += 3; mem[c-1] = uint32(kk - c); mem[c-5] = oldMem[q-5]; mem[c-4] = 0
	@<절 |c|의 앞 두 리터럴로 감시한다@>
	maxLearned = kk + learnedExtra
} else if kk == c {
	goto unsat
} else {
	mems++; l = int(mem[c])
	@<리터럴 |l|을 수준 0의 트레일에 올린다...@>
}

@ 배운 절을 적을 때와 같은 방법으로 자리를 늘린다.

@<|mem|에 절 |q|가...@>=
t = c + jj - q + learnedExtra
if t > maxCellsUsed {
	if t >= memsize {
		err = ErrMemory
		goto allDone
	}
	bytes += uint64(t-maxCellsUsed) * 4
	maxCellsUsed = t
	@<|mem|을 |maxCellsUsed|칸 이상으로...@>
}

@* 시험.
시험은 \.{cdcl\_test.go}로 따로 짜낸다. 가장 중요한 시험은 원본과의 대조다. 수들은
\CEE/ 원본 \.{SAT13}을 |ctangle|로 짜내어 FMA 없이(\.{-ffp-contract=off}) 컴파일하고
돌려서 받아 적었다. FMA를 켜고 돌려도 수가 같았다.

@(cdcl_test.go@>=
package sat

import (
	"context"
	"errors"
	"math/rand/v2"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

@<시험들@>

@<시험에 쓰는 함수들@>

@ 첫째 시험은 Rivest의 여덟 절이다. 만족할 수 없고, mem은 301+668이어야 한다.
마지막 절을 빼면 만족할 수 있고, 원본은 \.{\ x4\ \~x2\ x3\ \~x1}을 찍는다.

@<시험들@>=
func TestSolveRivest(t *testing.T) {
	const rivest = "x2 x3 ~x4\nx1 x3 x4\n~x1 x2 x4\n~x1 ~x2 x3\n" +
		"~x2 ~x3 x4\n~x1 ~x3 ~x4\nx1 ~x2 ~x4\nx1 x2 ~x3\n"
	s := solveText(t, rivest, "", Unsat, nil)
	wantLine(t, "rivest", s, "Altogether 301+668 mems, 5804 bytes, 3 nodes,"+
		" 3 clauses learned (ave 1.3->1.3), 60 memcells.")
	seven := rivest[:strings.LastIndex(rivest[:len(rivest)-1], "\n")+1]
	s = solveText(t, seven, "", Sat, nil)
	wantLine(t, "rivest7", s, "Altogether 291+142 mems, 5752 bytes, 2 nodes,"+
		" 0 clauses learned, 47 memcells.")
	var names []string
	for _, l := range s.Model() {
		names = append(names, s.LitName(l))
	}
	if got := strings.Join(names, " "); got != "x4 ~x2 x3 ~x1" {
		t.Errorf("해가 %s로 나왔다", got)
	}
}

@ 둘째 시험은 \.{testdata}의 여섯 문제를 여러 매개변수로 푼다. 매개변수를 바꿔 가며
돌리는 까닭은 전체 달리기(\.w, \.j), 무작위 선택(\.p, \.P), 자명한 절(\.t),
다시 시작과 감쇠(\.f, \.a, \.r, \.R) 같은 드문 길을 모두 지나게 하려는 것이다.
mem이 $10^8$을 넘는 것은 \.{-short}에서 건너뛴다.

대조할 수는 \.{testdata/sat13-runs.golden}에 있다. 한 줄에 한 번씩, 문제 이름,
선택들, 원본이 찍은 답, 작별 인사의 첫 줄을 \.{\char124}로 갈라 적었다. 이 줄들을
코드 안에 두면 조판할 때 줄이 넘치므로 파일로 뺐다.

@<시험들@>=
func TestSolveGolden(t *testing.T) {
	for _, row := range goldenRows(t, "sat13-runs.golden") {
		file, opts, status, line := row[0], row[1], row[2], row[3]
		_, m, _ := strings.Cut(strings.Fields(line)[1], "+")
		if testing.Short() && len(m) > 8 {
			continue
		}
		s := readFile(t, filepath.Join("testdata", file+".sat"))
		solveSolver(t, s, opts, knuthStatus[status], nil)
		wantLine(t, file+" ["+opts+"]", s, line)
	}
}

@ 황금 파일을 읽어 줄마다 \.{\char124}로 가른 칸들을 주는 문. 원본이 찍는 답의
낱말을 |Status|로 바꾸는 표도 여기 둔다.

@<시험에 쓰는 함수들@>=
func goldenRows(t *testing.T, name string) [][]string {
	data, err := os.ReadFile(filepath.Join("testdata", name))
	if err != nil {
		t.Fatal(err)
	}
	var rows [][]string
	for _, row := range strings.Split(strings.TrimSpace(string(data)), "\n") {
		rows = append(rows, strings.Split(row, "|"))
	}
	return rows
}

var knuthStatus = map[string]Status{"!SAT!": Sat, "UNSAT": Unsat, "TIMEOUT!": Unknown}

@ 셋째 시험은 크누스의 벤치마크 113개 전부를 mem $10^8$에서 끊어 원본과 견준다.
\.{testdata/sat13-T1e8.golden}의 줄은 이름, 원본이 찍은 답, 작별 인사의 첫 줄을
\.{\char124}로 가른 것이다. 벤치마크는 저장소에 없으므로 \.{SATEXAMPLES}를 주어야
돈다.

@<시험들@>=
func TestSolveSATexamples(t *testing.T) {
	dir := os.Getenv("SATEXAMPLES")
	if dir == "" {
		t.Skip("SATEXAMPLES가 비어 있다")
	}
	for _, fields := range goldenRows(t, "sat13-T1e8.golden") {
		@<황금 줄 |fields|의 문제를 풀어 견준다@>
	}
}

@ 원본이 mem 한도에서 멈췄으면 우리도 |ErrTimeout|과 함께 멈춰야 한다.

@<황금 줄 |fields|의 문제를...@>=
path, _ := filepath.Glob(filepath.Join(dir, "benchmarks-*", fields[0]+".sat"))
if len(path) != 1 {
	t.Errorf("%s: 파일을 찾지 못했다", fields[0])
	continue
}
s := readFile(t, path[0])
want := knuthStatus[fields[1]]
var wantErr error
if want == Unknown {
	wantErr = ErrTimeout
}
solveSolver(t, s, "T100000000", want, wantErr)
wantLine(t, fields[0], s, fields[2])

@ 넷째 시험은 꾸러미로 쓰는 길이다. 비둘기 넷을 구멍 셋에 넣는 문제는 만족할 수 없고,
빈 절이 들면 만족할 수 없고, 절이 없으면 만족할 수 있다.

@<시험들@>=
func TestSolveAPI(t *testing.T) {
	s := New()
	var x [4][3]Lit
	for p := range x {
		for h := range x[p] {
			x[p][h] = s.NewVar()
		}
		s.AddClause(x[p][:]...)
	}
	@<두 비둘기가 한 구멍에 들지 않게 한다@>
	solveSolver(t, s, "", Unsat, nil)
	s.AddClause()
	solveSolver(t, s, "", Unsat, nil)
	s = New()
	s.NewVar()
	solveSolver(t, s, "", Sat, nil)
}

@ @<두 비둘기가 한 구멍에...@>=
for h := 0; h < 3; h++ {
	for p := 0; p < 4; p++ {
		for q := p + 1; q < 4; q++ {
			s.AddClause(x[p][h].Not(), x[q][h].Not())
		}
	}
}

@ 다섯째 시험은 거둔 |context|다. 오래 걸리는 문제를 거둔 |context|로 풀면 첫 검사
때 멈춰야 한다. 매개변수의 잘못도 여기서 본다.

@<시험들@>=
func TestSolveCancelAndParams(t *testing.T) {
	s := readFile(t, filepath.Join("testdata", "langfordprime-10.sat"))
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	if st, err := s.Solve(ctx); st != Unknown || !errors.Is(err, context.Canceled) {
		t.Errorf("거둔 context로 %v, %v가 나왔다", st, err)
	}
	if s.Stats().Mems > 2*checkEvery {
		t.Errorf("mem %d까지 멈추지 않았다", s.Stats().Mems)
	}
	var p Params
	if p.Set("x3") == nil || p.Set("a") == nil || p.Set("a0.1") != nil || p.Alpha != float32(0.1) {
		t.Error("Params.Set이 잘못 읽었다")
	}
	s.Params.Alpha = 2
	if _, err := s.Solve(context.Background()); err == nil {
		t.Error("범위 밖의 매개변수를 받아들였다")
	}
}

@ 여섯째 시험부터는 원본에 없는 가정과 점진적 풀이를 본다. 견줄 원본이 없으니 답이
옳은지를 본다. 먼저 변수 열둘의 무작위 3-SAT 식이다. 한 풀이기에 절을 다섯 개씩 보태 가며
그때마다 무작위 가정을 주어 풀고, 모든 배정을 따지는 무식한 방법과 견준다. 전체 달리기와
재활용, 자명한 절, 무작위 결정이 잦도록 매개변수를 바꾼 판도 돌린다.

@<시험들@>=
func TestSolveAssumptions(t *testing.T) {
	const n = 12
	rng := rand.New(rand.NewPCG(7, 13))
	for _, opts := range []string{"", "w1 j3 J1 t1 p0.3 f0.9"} {
		for range 30 {
			s := New()
			for range n {
				s.NewVar()
			}
			setOpts(t, s, opts)
			var cls [][]Lit
			for range 12 {
				@<무작위 3-절 다섯을 |s|와 |cls|에 보탠다@>
				@<무작위 가정으로 풀고 무식한 방법과 견준다@>
			}
		}
	}
}

@ @<무작위 3-절 다섯을...@>=
for range 5 {
	c := make([]Lit, 3)
	for i := range c {
		c[i] = randomLit(rng, n)
	}
	s.AddClause(c...)
	cls = append(cls, c)
}

@ @<무작위 가정으로 풀고...@>=
asm := make([]Lit, rng.IntN(4))
for i := range asm {
	asm[i] = randomLit(rng, n)
}
st, err := s.Solve(context.Background(), asm...)
if err != nil || (st == Sat) != bruteSat(n, cls, asm) {
	t.Fatalf("[%s] 가정 %v에서 %v, %v가 나왔다", opts, asm, st, err)
}
checkAnswer(t, s, st, cls, asm, func(units []Lit) bool { return bruteSat(n, cls, units) })

@ 일곱째 시험은 큰 문제를 조금씩 쌓아 가며 푼다. \.{testdata}의 문제 넷을 절 차례대로
넷으로 나눠 보태며 그때마다 무작위 가정 셋을 주어 풀고, 마지막에는 가정 없이 푼다. 마지막
답은 원본의 답과 같아야 한다. 중간에 나온 |Unsat|은 새 풀이기로 그때까지의 절과 |Failed|를
풀어 확인한다. 재활용과 전체 달리기가 잦도록 \.{j50 J20 w1}을 준다.

@<시험들@>=
func TestSolveIncremental(t *testing.T) {
	rng := rand.New(rand.NewPCG(3, 5))
	for _, name := range []string{"queen-5x5-5", "poset-nomax-b-12-minus-one",
		"mutex-fourbits-lemmas-1", "mutilated-10-10"} {
		full := readFile(t, filepath.Join("testdata", name+".sat"))
		all, n := slices.Collect(full.Clauses()), full.NumVars()
		s := New()
		setOpts(t, s, "j50 J20 w1")
		for range n {
			s.NewVar()
		}
		for part := 1; part <= 4; part++ {
			@<절의 |part|/4까지를 보태고 무작위 가정으로 풀어 본다@>
		}
		@<가정 없이 풀어 원본의 답과 견준다@>
	}
}

@ @<절의 |part|/4까지를...@>=
cls := all[:len(all)*part/4]
for _, c := range all[len(all)*(part-1)/4 : len(cls)] {
	s.AddClause(c...)
}
asm := []Lit{randomLit(rng, n), randomLit(rng, n), randomLit(rng, n)}
st, err := s.Solve(context.Background(), asm...)
if err != nil {
	t.Fatal(err)
}
checkAnswer(t, s, st, cls, asm, func(units []Lit) bool { return freshSat(t, n, cls, units) })

@ @<가정 없이 풀어...@>=
want := Unknown
for _, row := range goldenRows(t, "sat13-runs.golden") {
	if row[0] == name && row[1] == "" {
		want = knuthStatus[row[2]]
	}
}
st, err := s.Solve(context.Background())
if err != nil || st != want || (st == Unsat && s.Failed() != nil) {
	t.Errorf("%s: %v, %v, %v인데 %v여야 한다", name, st, err, s.Failed(), want)
}
if st == Sat {
	checkAnswer(t, s, st, all, nil, nil)
}

@ 여덟째 시험은 이어 쓰기의 규칙이다. Rivest의 일곱 절을 다시 풀면 짓지 않고 이어 쓰니
준비에 드는 mem이 처음보다 적어야 한다. 매개변수를 바꾸었다가 되돌리면 처음부터 다시
지으니 원본과 같은 작별 인사가 나와야 한다.

@<시험들@>=
func TestSolveResume(t *testing.T) {
	const seven = "x2 x3 ~x4\nx1 x3 x4\n~x1 x2 x4\n~x1 ~x2 x3\n" +
		"~x2 ~x3 x4\n~x1 ~x3 ~x4\nx1 ~x2 ~x4\n"
	s := solveText(t, seven, "", Sat, nil)
	solveSolver(t, s, "", Sat, nil)
	if s.Stats().IMems >= 291 {
		t.Errorf("다시 풀면서 %d mem을 들여 지었다", s.Stats().IMems)
	}
	solveSolver(t, s, "s1", Sat, nil)
	solveSolver(t, s, "s0", Sat, nil)
	wantLine(t, "rivest7", s, "Altogether 291+142 mems, 5752 bytes, 2 nodes,"+
		" 0 clauses learned, 47 memcells.")
	@<책임이 있는 가정들을 본다@>
	@<전처리한 풀이기에 가정을 주어 본다@>
}

@ $x_1$과 $\bar x_1$을 함께 가정하면 둘 다 책임이 있다. 일곱 절에 $x_1$을 더하면 만족할
수 없으니, $x_1$만 가정하면 $x_1$이 책임을 진다. 이때 풀이기는 $\bar x_1$을 배워 수준 0에
두므로, 그다음에 $\bar x_2$를 곁들여 가정해도 책임은 $x_1$에게만 있다. 여덟째 절을 보태고
가정 없이 풀면 만족할 수 없고 |Failed|가 비어야 한다. 그 뒤로는 가정을 주어도 곧바로 같은
답이 나온다.

@<책임이 있는 가정들을...@>=
x1, x2, x3 := s.Lookup("x1"), s.Lookup("x2"), s.Lookup("x3")
for _, tc := range [][2][]Lit{{{x1, x1.Not()}, {x1, x1.Not()}}, {{x1}, {x1}},
	{{x2.Not(), x1}, {x1}}} {
	if st, _ := s.Solve(context.Background(), tc[0]...); st != Unsat ||
		!slices.Equal(s.Failed(), tc[1]) {
		t.Errorf("가정 %v에서 %v, %v가 나왔다", tc[0], st, s.Failed())
	}
}
s.AddClause(x1, x2, x3.Not())
solveSolver(t, s, "", Unsat, nil)
if st, _ := s.Solve(context.Background(), x1); st != Unsat || s.Failed() != nil {
	t.Errorf("여덟 절에서 %v, %v가 나왔다", st, s.Failed())
}

@ @<전처리한 풀이기에...@>=
s = New()
if err := s.ReadKnuth(strings.NewReader(seven)); err != nil {
	t.Fatal(err)
}
if _, err := s.Simplify(context.Background()); err != nil {
	t.Fatal(err)
}
if _, err := s.Solve(context.Background(), s.Lookup("x1")); err == nil {
	t.Error("전처리한 풀이기가 가정을 받았다")
}

@ 글자로 적힌 문제를 읽어 푸는 문.

@<시험에 쓰는 함수들@>=
func solveText(t *testing.T, text, opts string, want Status, wantErr error) *Solver {
	t.Helper()
	s := New()
	if err := s.ReadKnuth(strings.NewReader(text)); err != nil {
		t.Fatal(err)
	}
	solveSolver(t, s, opts, want, wantErr)
	return s
}

@ 선택들을 매개변수에 반영하고 풀어서 답을 견주는 문. 해가 나오면 모든 절을
만족하는지도 본다.

@<시험에 쓰는 함수들@>=
func solveSolver(t *testing.T, s *Solver, opts string, want Status, wantErr error) {
	t.Helper()
	setOpts(t, s, opts)
	st, err := s.Solve(context.Background())
	if st != want || !errors.Is(err, wantErr) {
		t.Errorf("[%s] %v, %v인데 %v, %v여야 한다", opts, st, err, want, wantErr)
		return
	}
	if st == Sat {
		@<해가 모든 절을 만족하는지 본다@>
	}
}

@ @<해가 모든 절을...@>=
for c := range s.Clauses() {
	ok := false
	for _, l := range c {
		ok = ok || s.Value(l)
	}
	if !ok {
		t.Errorf("[%s] 해가 절 %v를 만족하지 않는다", opts, c)
		return
	}
}

@ 작별 인사의 첫 줄을 견주는 문.

@<시험에 쓰는 함수들@>=
func wantLine(t *testing.T, name string, s *Solver, want string) {
	t.Helper()
	got, _, _ := strings.Cut(s.Stats().String(), "\n")
	if got != want {
		t.Errorf("%s:\n  %s\n인데\n  %s\n여야 한다", name, got, want)
	}
}

@ 크누스식 선택들을 매개변수에 반영하는 문.

@<시험에 쓰는 함수들@>=
func setOpts(t *testing.T, s *Solver, opts string) {
	t.Helper()
	for _, o := range strings.Fields(opts) {
		if err := s.Params.Set(o); err != nil {
			t.Fatal(err)
		}
	}
}

@ 변수 $1..n$ 가운데 하나의 리터럴을 무작위로 고르는 문.

@<시험에 쓰는 함수들@>=
func randomLit(rng *rand.Rand, n int) Lit {
	return Pos(1+rng.IntN(n)) | Lit(rng.IntN(2))
}

@ 가정 아래에서 나온 답을 따지는 문. 해가 나오면 절 |cls|와 가정 |asm|을 모두 만족해야
한다. |Unsat|이면 |Failed|가 가정의 일부여야 하고, 그것만 가정해도 만족할 수 없다는 것을
|sat|으로 확인한다. |Failed|가 비었으면 절만으로 만족할 수 없어야 한다는 뜻이 된다.

@<시험에 쓰는 함수들@>=
func checkAnswer(t *testing.T, s *Solver, st Status, cls [][]Lit, asm []Lit,
	sat func([]Lit) bool) {
	t.Helper()
	switch st {
	case Sat:
		@<해가 절 |cls|와 가정 |asm|을 모두 만족하는지 본다@>
	case Unsat:
		failed := s.Failed()
		for _, a := range failed {
			if !slices.Contains(asm, a) {
				t.Fatalf("책임진 가정 %v가 가정 %v에 없다", failed, asm)
			}
		}
		if sat(failed) {
			t.Fatalf("가정 %v 가운데 %v만으로는 만족할 수 없어야 한다", asm, failed)
		}
	}
}

@ @<해가 절 |cls|와...@>=
for _, c := range cls {
	if !slices.ContainsFunc(c, s.Value) {
		t.Fatalf("해가 절 %v를 만족하지 않는다", c)
	}
}
for _, a := range asm {
	if !s.Value(a) {
		t.Fatalf("해가 가정 %v를 어긴다", a)
	}
}

@ 변수 $n\le 32$개의 절들에 단위 절 |units|를 더한 식을 만족하는 배정이 있는지, 모든
배정을 따져 보는 문. 절마다 양의 리터럴과 음의 리터럴의 비트 마스크를 만들어 두면 배정
|x|가 절을 만족하는지는 비트 연산 한 번이다.

@<시험에 쓰는 함수들@>=
func bruteSat(n int, cls [][]Lit, units []Lit) bool {
	var masks [][2]uint32
	for _, c := range cls {
		var m [2]uint32
		for _, l := range c {
			m[l&1] |= 1 << (l.Var() - 1)
		}
		masks = append(masks, m)
	}
	for _, u := range units {
		var m [2]uint32
		m[u&1] = 1 << (u.Var() - 1)
		masks = append(masks, m)
	}
next:
	for x := uint64(0); x < 1<<n; x++ {
		for _, m := range masks {
			if uint32(x)&m[0]|^uint32(x)&m[1] == 0 {
				continue next
			}
		}
		return true
	}
	return false
}

@ 새 풀이기로 절들과 단위 절들을 풀어 만족할 수 있는지 알려 주는 문.

@<시험에 쓰는 함수들@>=
func freshSat(t *testing.T, n int, cls [][]Lit, units []Lit) bool {
	s := New()
	for range n {
		s.NewVar()
	}
	for _, c := range cls {
		s.AddClause(c...)
	}
	for _, u := range units {
		s.AddClause(u)
	}
	st, err := s.Solve(context.Background())
	if err != nil {
		t.Fatal(err)
	}
	return st == Sat
}

@* 색인.
