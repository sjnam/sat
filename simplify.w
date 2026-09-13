\input kotexgweb

\def\title{전처리}

@s context.Context int
@s gbflip.RNG int
@s io.Writer int
@s testing.T int
@s Lit int
@s Solver int
@s Status int
@s Stats int

@* 들어가며.
이 글은 크누스의 \.{SAT12}와 \.{SAT12-ERP}를 \GO/로 옮긴 것이다. 앞의 것은 풀이기가
아니라 {\it 전처리기\/}다. 절들을 받아 뜻을 바꾸지 않고 줄인 다음 진짜 풀이기에게
넘긴다. 뒤의 것은 그 거꾸로다. 줄인 절의 해를 받아, 전처리가 없애 버린 변수들의 값을
되찾아 원래 절의 해로 만든다.
@^Knuth, Donald Ervin@>
@^SAT12@>

크누스가 쓰는 변환은 네 가지다. 단위 절이 강제하는 값을 박아 넣고, 한 부호로만 나오는
``순수 리터럴''을 없앤다. 다른 절에 포섭되는 절을 지우고(subsumption), 거의
포섭되는 절에서는 리터럴 하나를 떼어 낸다(strengthening, self-subsumption). 그리고
가장 힘센 것으로, 변수를 분해로 {\it 소거\/}한다. 변수 $x$가 양으로 $a$번, 음으로
$b$번 나오면 그 $a+b$개의 절을 분해한 절 $ab$개로 바꿀 수 있다. 크누스는 E\'en과
Biere의 논문을 따라, 분해한 절이 원래보다 많지 않을 때만 소거한다.
@^E\'en, Niklas@>
@^Biere, Armin@>

@ 원칙은 이번에도 같다. {\it mem 수가 원본과 똑같이 나오게 옮긴다.} 그리고 줄인 절을
|Solve|로 풀면 그 mem 수도 원본 파이프라인 `\.{sat12 < foo \char124\ sat13}'과 같아야 한다.

원본은 줄인 절을 표준 출력에, 되돌리는 정보를 \.{/tmp/erp} 파일에 쓴다. 파이프라인
세 단계 사이를 파일로 잇는 셈이다. 꾸러미에서는 그럴 까닭이 없다. |Simplify|는 줄인
절과 erp 자료를 풀이기 안에 들고 있고, 뒤이어 부르는 |Solve|는 줄인 절을 풀고 erp를
되짚어 원래 변수 모두의 값을 채운다. 부르는 쪽에서 보면 |Simplify|를 한 줄 더
불렀을 뿐, |Value|와 |Model|은 여전히 원래 변수들로 답한다.

@c
package sat

import (
	"context"
	"errors"
	"fmt"
	"io"
	"strconv"
	"strings"

	"github.com/sjnam/go-sgb/gbflip"
)

@<자료 구조@>

@<함수들@>

@* 겉모습.
매개변수는 크누스의 명령 줄 선택들이다. 풀이기의 |Params|와 글자가 겹치므로(가령
\.m과 \.T) 따로 둔다.

@<자료 구조@>=
type SimplifyParams struct {
	Seed      int    // \.s: 난수 씨앗 (0)
	MemMax    uint64 // \.m: |mem| 칸 수의 하한 (100000)
	Cutoff    int    // \.c: 두 부호가 모두 이보다 많이 나오면 소거하지 않는다 (10)
	Optimism  uint64 // \.C: $ab$가 $a+b$보다 이만큼 넘게 크면 소거하지 않는다 (25)
	Buckets   int    // \.B: 소거 후보를 가르는 차수의 상한 (32)
	MaxRounds int    // \.t: 소거를 되풀이하는 횟수의 상한
	Timeout   uint64 // \.T: mem 한도
}

@ @<자료 구조@>=
var defaultSimplifyParams = SimplifyParams{
	MemMax:    100000,
	Cutoff:    10,
	Optimism:  25,
	Buckets:   32,
	MaxRounds: 0x7fffffff,
	Timeout:   0x1fffffffffffffff,
}

@ 크누스식 선택 하나를 반영하는 문. 결과에 영향이 없는 \.v, \.h, \.b는 받아 두기만
한다. erp 파일 이름을 주는 \.e는 꾸러미에 파일이 없으므로 받지 않는다.

@<함수들@>=
func (p *SimplifyParams) Set(opt string) error {
	if opt == "" {
		return errors.New("sat: 빈 선택")
	}
	arg := opt[1:]
	var err error
	switch opt[0] {
	case 's':
		p.Seed, err = strconv.Atoi(arg)
	case 'm':
		p.MemMax, err = strconv.ParseUint(arg, 10, 64)
	case 'c':
		p.Cutoff, err = strconv.Atoi(arg)
	case 'C':
		p.Optimism, err = strconv.ParseUint(arg, 10, 64)
	case 'B':
		p.Buckets, err = strconv.Atoi(arg)
	case 't':
		p.MaxRounds, err = strconv.Atoi(arg)
	case 'T':
		p.Timeout, err = strconv.ParseUint(arg, 10, 64)
	case 'v', 'h', 'b':
		_, err = strconv.Atoi(arg)
	default:
		return fmt.Errorf("sat: 모르거나 지원하지 않는 선택 %q", opt)
	}
	if err != nil {
		return fmt.Errorf("sat: 선택 %q: %v", opt, err)
	}
	return nil
}

@ 전처리가 끝나면 원본이 찍던 수들을 모아 둔다.

@<자료 구조@>=
type SimplifyStats struct {
	IMems, Mems                uint64 // 준비와 전처리에 든 mem
	Bytes                      uint64 // 자료 구조의 바이트 수 (원본의 크기로 셈)
	Cells                      uint32 // |mem|에서 쓴 칸 수
	Subsumptions               uint32 // 포섭으로 지운 절의 수
	Strengthenings             uint32 // 강화한 절의 수
	SubTries, SubFalse         uint64 // 포섭 시도와 헛짚음
	StrTries, StrFalse         uint64 // 강화 시도와 헛짚음
	ElimTries, FuncDeps        uint64 // 소거 시도와 함수적 종속을 찾은 수
	Vars, VarsGone             uint32 // 변수의 수와 없앤 변수의 수
	ClausesGone                uint32 // 없앤 절의 수
	Rounds                     uint32 // 소거를 되풀이한 횟수
	Unsat                      bool   // 만족할 수 없음을 밝혔는가
}

@ @<함수들@>=
func (s *Solver) SimplifyStats() SimplifyStats { return s.simpStats }

@ 통계를 원본의 출력과 같은 꼴로 적는 문. 첫 줄은 무엇을 없앴는지, 둘째 줄은
작별 인사다.

@<함수들@>=
func (st SimplifyStats) String() string {
	var b strings.Builder
	switch {
	case st.Unsat:
		b.WriteString("The clauses are unsatisfiable.")
	case st.VarsGone == st.Vars:
		b.WriteString("No clauses remain.")
	default:
		fmt.Fprintf(&b, "%d variable%s and %d clause%s removed (%d round%s).",
			st.VarsGone, plural(uint64(st.VarsGone), "", "s"),
			st.ClausesGone, plural(uint64(st.ClausesGone), "", "s"),
			st.Rounds, plural(uint64(st.Rounds), "", "s"))
	}
	fmt.Fprintf(&b, "\nAltogether %d+%d mems, %d bytes, %d cells;", st.IMems, st.Mems, st.Bytes, st.Cells)
	@<전처리 통계의 나머지 줄들을 적는다@>
	return b.String()
}

@ @<전처리 통계의 나머지...@>=
if st.Subsumptions+st.Strengthenings != 0 {
	fmt.Fprintf(&b, "\n %d subsumption%s, %d strengthening%s.",
		st.Subsumptions, plural(uint64(st.Subsumptions), "", "s"),
		st.Strengthenings, plural(uint64(st.Strengthenings), "", "s"))
}
fmt.Fprintf(&b, "\n false hit rates %.3f of %d, %.3f of %d.",
	ratio(st.SubFalse, st.SubTries), st.SubTries, ratio(st.StrFalse, st.StrTries), st.StrTries)
if st.ElimTries != 0 {
	fmt.Fprintf(&b, "\n %.3f functional dependencies among %d trials.",
		ratio(st.FuncDeps, st.ElimTries), st.ElimTries)
}

@ 원본은 시도가 없으면 비율을 0으로 찍는다. 두 곳에서 부른다.

@<함수들@>=
func ratio(a, b uint64) float64 {
	if b == 0 {
		return 0
	}
	return float64(a) / float64(b)
}

@ 풀이기에 달리는 전처리의 결과. 줄인 절은 |cells|에 \.{sat.w}의 임시 표와 같은 꼴로
담고, erp 자료는 |erp|에 담는다. erp의 칸마다 리터럴 하나와 표가 붙는다. 표
|erpFirst|는 절의 첫 리터럴, |erpDef|는 값을 정할 리터럴이다.

@<자료 구조@>=
type preprocessed struct {
	cells []Lit      // 줄인 절들
	erp   []erpCell  // 되돌리는 자료
	unsat bool       // 만족할 수 없음을 밝혔는가
}

type erpCell struct {
	lit  Lit
	flag uint8
}

const (
	erpFirst = 1 // 절의 첫 리터럴
	erpDef   = 2 // 값을 정할 리터럴
)

@* 전처리의 뼈대.
|Simplify|가 돌려주는 답의 뜻은 이렇다. 만족할 수 없음을 밝혔으면 |Unsat|이다. 절이
모두 사라졌으면 |Sat|이다. 이때는 풀 것이 없고 erp 자료만으로 해가 나온다. 절이 남아
있으면 |Unknown|이다. 뒤이어 |Solve|를 부르라는 뜻이다. |mem| 칸이 모자라면
|ErrMemory|를 돌려주고 전처리한 것을 버린다. mem 한도에 이르거나 |context|를 거두면
원본처럼 그때까지 줄인 것을 남기고 |ErrTimeout|이나 |ctx.Err()|를 돌려준다.

\.{cdcl.w}의 |Solve|처럼 크누스의 전역 변수와 레지스터 변수를 모두 지역 변수로 두고,
레이블은 함수 몸통 바깥에 둔다. 원본의 레지스터는 |uint|이고 32비트 부호 없는 산술에
기대는 곳이 있으므로 여기서도 |uint32|로 옮겼다.

@<함수들@>=
func (s *Solver) Simplify(ctx context.Context) (Status, error) {
	@<|Simplify|의 지역 변수@>
	s.pre, s.simpStats = nil, SimplifyStats{}
	if s.empty {
		s.pre, s.simpStats.Unsat = &preprocessed{unsat: true}, true
		return Unsat, nil
	}
	if s.clauses == 0 {
		return Unknown, nil
	}
	@<전처리 매개변수를 받고 난수 발생기를 맞춘다@>
	@<전처리의 자료 구조를 짓는다@>
	imems, mems = mems, 0
	@<더는 바뀌지 않을 때까지 전처리한다@>
finishUp:
	@<줄인 절을 적어 둔다@>
	goto record
unsat:
	status, pre.unsat = Unsat, true
record:
	@<전처리 결과와 통계를 적어 둔다@>
	return status, err
}

@ 레지스터 변수들. 원본의 |s|는 여기서도 받는 쪽 이름과 부딪히므로 |sz|로 부른다.
원본에서 블록 안에 새로 선언해 바깥 변수를 가리던 것들은 이름을 따로 붙였다. 할 일
더미를 비울 때의 |c|는 |cd|, 값을 박을 때의 |k|는 |kv|, 서명을 다시 셈할 때의
|bits|와 |t|는 |bits2|와 |t2|다.

@<|Simplify|의 지역 변수@>=
var (
	b, c, cc, j, k, l, ll, p, pp, q, qq, r uint32
	sz, u, uu, v, vv, w, x                 uint32
	kv, cd, csave, t2, rbits, progress     uint32
	bits, bits2, ubits, ccbits, stbits     uint64
	specialcase                            int
	cur                                    int
)

@ @<|Simplify|의 지역 변수@>=
var (
	status               Status
	err                  error
	par                  SimplifyParams
	rng                  *gbflip.RNG
	pre                  *preprocessed // 결과
	vars, clauses, cells uint32
	imems, mems, bytes   uint64
)

@ 원본처럼 난수 736개를 먼저 버린다. 이 프로그램은 리터럴의 서명을 만들 때 난수를 쓴다.

@<전처리 매개변수를 받고...@>=
par = s.SimplifyParams
if par.Cutoff < 0 || par.MaxRounds < 0 {
	return Unknown, errors.New("sat: 전처리 매개변수가 범위를 벗어났다")
}
vars, clauses, cells = uint32(s.NumVars()), uint32(s.clauses), uint32(len(s.cells))
rng = gbflip.New(int64(par.Seed))
for k = 0; k < 736; k++ {
	rng.Next()
}
pre = &preprocessed{}

@* 자료 구조.
크누스는 모든 절 정보를 춤추는 링크처럼 네 겹으로 이은 구조에 둔다. 칸마다 절 하나의
리터럴 하나가 들어 있다. 그 칸은 같은 리터럴의 칸들을 잇는 세로 목록(|up|, |down|)과
같은 절의 칸들을 잇는 가로 목록(|left|, |right|)에 함께 걸린다. 크누스는 여기에
64비트 ``서명''을 곁들인다. 리터럴마다 무작위 비트 두 개를 켠 서명을 주고, 절의 서명은
그 리터럴 서명들의 OR다. 절 $C$가 $C'$에 포함되려면 $C$의 서명이 $C'$의 서명에
포함되어야 하므로, 포섭을 따지기 전에 대부분의 경우를 비트 연산 한 번으로 걸러 낸다.

|mem[0]|과 |mem[1]|은 특별한 쓰임이 있다. |mem[2]|부터 |mem[2n+1]|까지는 리터럴
목록의 머리이고, 그다음 $m$칸은 절 목록의 머리다. 나머지는 절의 칸이거나 빈칸이다.
머리 칸에서는 필드의 뜻이 달라진다.
$$\vbox{\halign{\quad#\hfil&\quad#\hfil&\quad#\hfil\cr
&리터럴 머리 $l$&절 머리 $c$\cr
|lit|&그 리터럴이 든 절의 수 |occurs(l)|&마지막으로 온전히 쓴 때 |clstime(c)|\cr
|cls|&가장 최근에 새 절에 든 때 |littime(l)|&절의 크기 |size(c)|\cr
|sig|&리터럴의 서명 |litsig(l)|&절의 서명 |clssig(c)|\cr}}$$
원본은 32비트 필드 둘과 64비트 필드 하나를 공용체로 겹쳐 두지만, 한 칸에서 둘을 함께
쓰는 일은 없으므로 \GO/에서는 필드를 따로 둔다. 칸은 원본보다 8바이트 크지만
|Bytes| 통계는 원본의 크기로 센다.

@<자료 구조@>=
type simpCell struct {
	lit, cls              uint32 // 리터럴과 절 (머리에서는 표 참고)
	up, down, left, right uint32 // 세로와 가로의 이웃
	sig                   uint64 // 머리의 서명
}

@ 변수마다 두는 것. |status|가 0이 아니면 할 일 더미에 올라 있거나 이미 없어진
변수다. |stable|은 최근의 변환에 끼지 않았다는 표시다.

@<자료 구조@>=
type simpVar struct {
	link   uint32 // 할 일 더미의 다음
	status uint8  // 지금의 처지
	stable uint8  // 최근에 건드리지 않았는가
	blink  uint32 // 소거 후보 바구니의 다음
}

type simpClause struct {
	link uint32 // 강화된 절 더미의 다음, 더미에 없으면 0
	size uint32 // 포섭과 강화를 따질 때 쓰는 자료
}

const (
	varNorm     = 0 // 보통
	elimQuiet   = 1 // 조용히 없앤다
	elimRes     = 2 // 분해로 소거했다
	forcedTrue  = 3 // 참으로 박는다
	forcedFalse = 4 // 거짓으로 박는다
	sentinel    = 1 // 강화된 절 더미의 바닥
)

@ @<|Simplify|의 지역 변수@>=
var (
	mem                    []simpCell
	memMax                 uint64 // |mem|의 칸 수
	litHeadTop, clsHeadTop uint32 // 리터럴 머리와 절 머리가 끝나는 곳
	xcells                 uint32 // 한 번이라도 쓴 칸 수
	avail                  uint32 // 빈칸 더미의 꼭대기
	toDo                   uint32 // 할 일 더미의 꼭대기
	strengthened           uint32 // 강화된 절 더미의 꼭대기
	vmem                   []simpVar
	lmem                   []uint64     // 리터럴마다 소거에 쓰는 도장
	cmem                   []simpClause // 절마다, 첨자는 절 번호에서 |litHeadTop|을 뺀 것
	varsGone, clausesGone  uint32
	round                  uint32 // 소거를 되풀이한 횟수, 원본의 |time|
	bucket                 []uint32
)

@* 진짜 자료 구조 짓기.
@<전처리의 자료 구조를 짓는다@>=
@<주 배열들을 마련한다@>
@<임시 칸들을 |mem|으로 옮긴다@>
@<변수들의 처지를 지운다@>
@<칸들의 연결을 마저 짓는다@>
@<보조 배열들을 마련한다@>

@ 칸이 몇 개나 필요할지는 미리 알 수 없다. 절이 줄어드는 사이에 절의 크기는 지수적으로
커질 수 있기 때문이다. 원본은 입력 칸 수의 두 배와 |MemMax| 가운데 큰 것을 잡는다.

@<주 배열들을...@>=
litHeadTop = vars + vars + 2
clsHeadTop = litHeadTop + clauses
xcells = clsHeadTop + cells + 1
memMax = par.MemMax
if uint64(xcells)+uint64(cells) > memMax {
	memMax = uint64(xcells) + uint64(cells)
}
if memMax >= 0x100000000 {
	memMax = 0xffffffff
}
mem = make([]simpCell, memMax)
bytes = memMax*24 + uint64(vars+1)*24
vmem = make([]simpVar, vars+1)

@ 임시 칸들을 되감는다. 절 |c|의 칸들은 절 머리 |c+litHeadTop-1|에 속하고, 리터럴
목록마다 맨 위에 끼워진다.

@<임시 칸들을 |mem|으로...@>=
for l = 2; l < litHeadTop; l++ {
	mems++; mem[l].down = l
}
cur = len(s.cells)
for c, j = clauses, clsHeadTop; c != 0; c-- {
	cc = c + litHeadTop - 1
	for {
		cur--
		x = uint32(s.cells[cur])
		p = x &^ uint32(firstLit)
		mems++; mem[j].lit = p; mem[j].cls = cc
		mems += 3; mem[j].down = mem[p].down; mem[p].down = j; j++
		if x&uint32(firstLit) != 0 {
			break
		}
	}
	mems++; mem[cc].left = cc
}
if j != clsHeadTop+cells {
	panic("sat: 이럴 수는 없다 (cells)")
}

@ 원본은 여기서 이름을 옮기며 mem을 하나, 처지를 지우며 하나 센다.

@<변수들의 처지를...@>=
for c = vars; c != 0; c-- {
	mems += 2; vmem[c].stable = 0; vmem[c].status = varNorm
}

@ 리터럴 목록을 차례로 훑으며 |up| 연결을 짓고 칸들을 절의 가로 목록에 끼운다. 리터럴을
작은 것부터 훑으므로, 끼우고 나면 절마다 리터럴이 왼쪽에서 오른쪽으로 커지는 차례로
늘어선다. 이 차례는 포섭을 따지거나 분해할 때 크게 도움이 된다.

@<칸들의 연결을...@>=
for l = 2; l < litHeadTop; l++ {
	@<리터럴 |l|의 |up| 연결과 그 칸들의 |left| 연결을 짓는다@>
}
for c = l; c < clsHeadTop; c++ {
	@<절 |c|의 |right| 연결과 서명과 크기를 짓는다@>
}

@ 원본의 |for| 머리에서 되풀이할 때마다 세는 mem은 \GO/의 |for| 뒷문장에서 |mems|를
함께 늘려 센다.

@<리터럴 |l|의 |up| 연결...@>=
for j, k, sz = l, mem[l].down, 0; k >= litHeadTop; mems, j, k = mems+1, k, mem[k].down {
	mems++; mem[k].up = j
	mems++; c = mem[k].cls
	mems += 3; mem[k].left = mem[c].left; mem[c].left = k
	sz++
}
if k != l {
	panic("sat: 이럴 수는 없다 (lit init)")
}
mems++; mem[l].lit = sz; mem[l].cls = 0
mems++; mem[l].up = j
if sz == 0 {
	w = l
	@<리터럴 |w|가 이미 정해지지 않았으면 거짓으로 둔다@>
} else {
	@<|l|의 서명을 만든다@>
}

@ 크누스는 실험해 보니 비트를 하나보다 둘 켜는 편이 거의 늘 나았다고 적었다. 난수
31비트를 얻는 데 mem 넷을 센다.

@<|l|의 서명을...@>=
if rbits < 0x40 {
	mems += 4; rbits = uint32(rng.Next()) | 1<<30
}
mems++; mem[l].sig = 1 << (rbits & 0x3f)
rbits >>= 6
if rbits < 0x40 {
	mems += 4; rbits = uint32(rng.Next()) | 1<<30
}
mems++; mem[l].sig |= 1 << (rbits & 0x3f)
rbits >>= 6

@ @<절 |c|의 |right| 연결과...@>=
bits = 0
for j, k, sz = c, mem[c].left, 0; k >= clsHeadTop; mems, j, k = mems+1, k, mem[k].left {
	mems++; mem[k].right = j
	mems++; w = mem[k].lit
	mems++; bits |= mem[w].sig
	sz++
}
if k != c {
	panic("sat: 이럴 수는 없다 (cls init)")
}
mems++; mem[c].cls = sz; mem[c].lit = 0
mems += 2; mem[c].sig = bits; mem[c].right = j
if sz <= 1 {
	@<리터럴 |w|를 참으로 박는다@>
}

@ 단위 절이 생겼다. 그 리터럴 |w|의 변수는 아직 없어지지 않았다고 가정한다. 할 일
더미에 올린 뒤에도 변수를 건드릴 수 있으므로 아직 |stable|이라 할 수는 없다.

@<리터럴 |w|를 참으로 박는다@>=
kv = w >> 1
mems++
if w&1 != 0 {
	if vmem[kv].status == varNorm {
		mems++; vmem[kv].status = forcedFalse; vmem[kv].link = toDo; toDo = kv
	} else if vmem[kv].status == forcedTrue {
		goto unsat
	}
} else {
	if vmem[kv].status == varNorm {
		mems++; vmem[kv].status = forcedTrue; vmem[kv].link = toDo; toDo = kv
	} else if vmem[kv].status == forcedFalse {
		goto unsat
	}
}

@ 이번에는 값을 강제하는 것이 아니다. |w|가 처음부터 어느 절에도 없었거나 마지막으로
나오던 절이 사라졌다. $\bar w$마저 이미 모두 사라졌다면(그 변수는 벌써 할 일 더미에
올라 |w|가 참으로 박힐 참이다) 조용히 없애기만 하면 된다. 그 변수는 참이든 거짓이든
상관없다.

@<리터럴 |w|가 이미 정해지지...@>=
kv = w >> 1
mems++
if vmem[kv].status == varNorm {
	mems++
	if w&1 != 0 {
		vmem[kv].status = forcedTrue
	} else {
		vmem[kv].status = forcedFalse
	}
	vmem[kv].link = toDo; toDo = kv
} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
	mems++; vmem[kv].status = elimQuiet; vmem[kv].stable = 1
}

@ 리터럴마다 두는 도장, 절마다 두는 자료, 그리고 소거 후보를 가를 바구니다.

@<보조 배열들을...@>=
lmem = make([]uint64, litHeadTop)
for l = 0; l < litHeadTop; l++ {
	mems++; lmem[l] = 0
}
cmem = make([]simpClause, clauses)
if par.Buckets < 2 {
	par.Buckets = 2
}
bucket = make([]uint32, par.Buckets+1)
bytes += uint64(litHeadTop)*8 + uint64(clauses)*8 + uint64(par.Buckets+1)*4

@* 할 일 더미 비우기.
몸풀기로 가장 기본적인 일부터 한다. 할 일 더미에 오른 변수에 값을 박고, 그 결과로
뻔히 강제되는 것들을 끝까지 따라간다. 값을 박을 때마다 erp 자료에 ``이 리터럴은
참이다''(원본의 erp 파일에서는 `\.{l <-0}' 한 줄)를 적는다.

원본에서 이 블록은 |c|를 새로 선언해 바깥의 |c|를 가린다. 이 블록은 강화된 절 더미를
비우는 도중에도 불리고, 거기서는 바깥의 |c|가 살아 있어야 한다. 그래서 여기서는
|cd|를 쓴다.

@<할 일 더미를 비운다@>=
for toDo != 0 {
	k = toDo
	mems++; toDo = vmem[k].link
	if vmem[k].status != elimQuiet {
		if vmem[k].status == forcedTrue {
			l = k + k
		} else {
			l = k + k + 1
		}
		pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
		mems++; vmem[k].stable = 1
		@<|l|이 든 절을 모두 지운다@>
		@<모든 절에서 $\bar l$을 지운다@>
	}
	varsGone++
}
@<mem 한도에 이르렀으면 |goto finishUp|@>

@ 원본은 mem 한도를 여기서만 살핀다. |context|도 여기서 살피되 mem이
|checkEvery|만큼 늘 때마다 한 번씩만 묻는다.

@<mem 한도에 이르렀으면...@>=
if mems > par.Timeout {
	err = ErrTimeout
	goto finishUp
}
if mems >= nextCheck {
	nextCheck = mems + checkEvery
	if e := ctx.Err(); e != nil {
		err = e
		goto finishUp
	}
}

@ @<|Simplify|의 지역 변수@>=
var nextCheck uint64 = checkEvery

@ $\bar l$을 지우고 나서 절이 리터럴 하나만 남으면 그 리터럴을 박는다. 줄어든 절은
다른 절을 포섭하거나 강화할 새 기회가 생기므로 강화된 절 더미에 올린다. 칸을 빈칸
더미에 돌려줄 때 |down| 연결은 건드리지 않으므로 목록을 계속 따라갈 수 있다.

@<모든 절에서 $\bar l$을...@>=
for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
	mems++; cd = mem[ll].cls
	mems++; p, q = mem[ll].left, mem[ll].right
	mems += 2; mem[p].right = q; mem[q].left = p
	mems++; mem[ll].left = avail; avail = ll
	mems++; j = mem[cd].cls - 1
	mems++; mem[cd].cls = j
	if j == 1 {
		mems++
		if p == cd {
			w = mem[q].lit
		} else {
			w = mem[p].lit
		}
		@<리터럴 |w|를 참으로...@>
	}
	@<절 |cd|의 서명을 다시 셈한다@>
	@<절 |cd|를 강화된 절 더미에 올린다@>
}

@ @<절 |cd|의 서명을...@>=
bits2 = 0
for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
	mems += 2; bits2 |= mem[mem[t2].lit].sig
}
mems++; mem[cd].sig = bits2

@ @<절 |cd|를 강화된...@>=
mems++
if cmem[cd-litHeadTop].link == 0 {
	mems++; cmem[cd-litHeadTop].link = strengthened; strengthened = cd
}

@ |l|이 든 절은 만족되었으니 통째로 지운다. 그 절의 다른 리터럴들은 목록에서 빼고
``건드렸다''고 표시한다. 어떤 리터럴이 마지막 절을 잃으면 순수 리터럴이 된 것이다.

@<|l|이 든 절을 모두...@>=
for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
	mems++; cd = mem[ll].cls
	for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
		if p != ll {
			mems++; w = mem[p].lit
			@<칸 |p|를 그 리터럴의 세로 목록에서 빼고 |w|가 사라졌는지 본다@>
		}
	}
	mems++; mem[mem[cd].right].left = avail; avail = mem[cd].left
	mems++; mem[cd].cls = 0; clausesGone++
}

@ 칸들을 한꺼번에 빈칸 더미에 돌려줄 때 원본의 |free_cells(k,kk)|는 가로 목록의
|left| 연결을 그대로 더미의 연결로 쓴다. 가장 오른쪽 칸 |k|의 |left|만 옛 더미에
이으면 |kk|부터 |k|까지가 한 줄로 더미에 얹힌다.

변수를 ``건드리는'' 것은 |stable|을 지워 소거 후보로 되살리는 일이다.

@<칸 |p|를 그 리터럴의 세로...@>=
mems++; q, r = mem[p].up, mem[p].down
mems += 2; mem[q].down = r; mem[r].up = q
mems++; vmem[w>>1].stable = 0
mems += 2; mem[w].lit--
if mem[w].lit == 0 {
	@<리터럴 |w|가 이미 정해지지...@>
}

@* 포섭.
Biere가 제안한 알고리즘을 쓰면 주어진 절 $C$에 포섭되는 절을 모두 찾아 지우기 쉽다.
$C$의 리터럴 $l$ 하나를 골라, $l$이 든 절 $C'$를 모두 훑는다. $C$가 $C'$에 포함되지
않는 경우는 대부분 크기와 서명만 보고 곧바로 걸러진다. $l$로는 가장 적은 절에 든
리터럴을 고른다.
@^Biere, Armin@>

@<절 |c|에 포섭되는 절을 지운다@>=
@<|c|에서 가장 드문 리터럴 |l|을 고른다@>
mems += 3; sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
for mems, pp = mems+1, mem[l].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
	mems++; cc = mem[pp].cls
	if cc == c {
		continue
	}
	subTries++
	mems++
	if bits&^mem[cc].sig != 0 {
		continue
	}
	mems++
	if mem[cc].cls < sz {
		continue
	}
	@<|c|가 |cc|에 포함되면 |l<=ll|로 만든다@>
	if l > ll {
		subFalse++
	} else {
		@<포섭된 절 |cc|를 지운다@>
	}
}

@ @<|c|에서 가장 드문...@>=
mems += 3; p = mem[c].right; l = mem[p].lit; k = mem[l].lit
for mems, p = mems+1, mem[p].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
	mems++; ll = mem[p].lit
	mems++
	if mem[ll].lit < k {
		k, l = mem[ll].lit, ll
	}
}

@ 두 절 모두 리터럴이 커지는 차례로 늘어서 있으므로 오른쪽 끝에서부터 나란히 걸으면
된다. 끝나면 |l<ll|이거나 |l>ll|이다. 앞의 것이 포함된다는 뜻이다.

@<|c|가 |cc|에 포함되면 |l<=ll|로...@>=
mems++; q, qq = v, mem[cc].left
for {
	mems += 2; l, ll = mem[q].lit, mem[qq].lit
	@<|l|을 만날 때까지 |cc| 쪽을 왼쪽으로 옮긴다@>
	if l > ll {
		break
	}
	mems++; q = mem[q].left
	if q < clsHeadTop {
		l = 0
		break
	}
	mems++; qq = mem[qq].left
	if qq < clsHeadTop {
		ll = 0
		break
	}
}

@ @<|l|을 만날 때까지...@>=
for l < ll {
	mems++; qq = mem[qq].left
	if qq < clsHeadTop {
		ll = 0
	} else {
		mems++; ll = mem[qq].lit
	}
}

@ @<포섭된 절 |cc|를...@>=
subTotal++
for mems, p = mems+1, mem[cc].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
	mems++; w = mem[p].lit
	@<칸 |p|를 그 리터럴의 세로...@>
}
mems++; mem[mem[cc].right].left = avail; avail = mem[cc].left
mems++; mem[cc].cls = 0; clausesGone++

@ 원본에서는 칸을 세로 목록에서 빼기 전에 리터럴을 읽는다. 앞의 절과 차례가 반대지만
세는 mem은 같다.

@<|Simplify|의 지역 변수@>=
var (
	subTotal, strTotal                     uint32
	subTries, subFalse, strTries, strFalse uint64
)

@* 강화.
비슷한 알고리즘으로, 주어진 절 $C$와 분해하면 {\it 짧아지는\/} 절 $C'$를 찾는다. $C$의
리터럴 $u$를 $\bar u$로 바꾸었을 때 $C$가 $C'$를 포섭한다면 $C'$에서 $\bar u$를 뗄
수 있다. E\'en과 Biere의 기법이다. 원본의 앞 알고리즘에서 |l|이라 부르던 것을 여기서는
|u|라 부른다.

@<절 |c|로 강화할 수 있는 절을 강화한다@>=
mems += 3; sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
for mems, vv = mems+1, v; vv >= clsHeadTop; mems, vv = mems+1, mem[vv].left {
	mems++; u = mem[vv].lit
	if specialcase != 0 {
		@<특별한 조건에 맞지 않으면 |u|를 버린다@>
	}
	mems++; ubits = bits &^ mem[u].sig
	for mems, pp = mems+1, mem[u^1].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
		strTries++
		mems++; cc = mem[pp].cls
		mems++
		if ubits&^mem[cc].sig != 0 {
			continue
		}
		mems++
		if mem[cc].cls < sz {
			continue
		}
		@<|u|를 빼면 |c|가 |cc|에 포함될 때 |l<=ll|로 만든다@>
		if l > ll {
			strFalse++
		} else {
			@<|cc|에서 $\bar u$를 뗀다@>
		}
	}
}

@ @<|u|를 빼면 |c|가...@>=
mems++; q, qq = v, mem[cc].left
for {
	mems += 2; l, ll = mem[q].lit, mem[qq].lit
	if l == u {
		l ^= 1
	}
	@<|l|을 만날 때까지...@>
	if l > ll {
		break
	}
	mems++; q = mem[q].left
	if q < clsHeadTop {
		l = 0
		break
	}
	mems++; qq = mem[qq].left
	if qq < clsHeadTop {
		ll = 0
		break
	}
}

@ $\bar u$의 칸을 찾아 두 목록에서 빼고, 그 앞뒤의 리터럴로 서명을 다시 셈한다. 원본은
찾아가는 동안 지나는 리터럴을 모두 건드린다.

@<|cc|에서 $\bar u$를...@>=
ccbits = 0
strTotal++
for mems, p = mems+1, mem[cc].right; ; mems, p = mems+1, mem[p].right {
	mems++; w = mem[p].lit
	mems++; vmem[w>>1].stable = 0
	if w == u^1 {
		break
	}
	mems++; ccbits |= mem[w].sig
}
mems += 2; mem[w].lit--
if mem[w].lit == 0 {
	@<리터럴 |w|가 이미 정해지지...@>
}
@<칸 |p|를 두 목록에서 빼고 빈칸 더미에 돌려준다@>
for p = q; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
	mems++; q = mem[p].lit
	mems++; vmem[q>>1].stable = 0
	mems++; ccbits |= mem[q].sig
}
mems++; mem[cc].sig = ccbits
@<|cc|의 크기를 줄인다@>
mems++
if cmem[cc-litHeadTop].link == 0 {
	mems++; cmem[cc-litHeadTop].link = strengthened; strengthened = cc
}

@ 여기서 나올 때 |q|는 |p|의 오른쪽 이웃이다.

@<칸 |p|를 두 목록에서...@>=
mems++; q, w = mem[p].up, mem[p].down
mems += 2; mem[q].down = w; mem[w].up = q
mems++; q, w = mem[p].right, mem[p].left
mems += 2; mem[q].left = w; mem[w].right = q
mems++; mem[p].left = avail; avail = p

@ |cc|가 여기서 비는 일은 없다. 그러려면 |c|가 단위 절이어야 하는데, 단위 절은 이런
복잡한 길 대신 할 일 더미로 다룬다.

@<|cc|의 크기를 줄인다@>=
mems += 2; mem[cc].cls--
if mem[cc].cls <= 1 {
	if mem[cc].cls == 0 {
		panic("sat: 이럴 수는 없다 (strengthening)")
	}
	mems += 2; w = mem[mem[cc].right].lit
	@<리터럴 |w|를 참으로...@>
}

@* 강화된 절 더미 비우기.
절이 짧아질 때마다 다른 절을 포섭하거나 강화할 새 기회가 생긴다. 그런 기회는 모두
곧바로 잡는다.

원본에서는 이 블록도 |c|를 새로 선언한다. 이 블록을 부르는 곳 가운데 하나(새 절들로
포섭과 강화를 한 바퀴 도는 곳)는 바깥의 |c|를 반복 변수로 쓰고 있으므로, 들어올 때
|c|를 |csave|에 두었다가 나갈 때 되돌린다. 이 블록은 제 안에서 다시 불리지 않으므로
그것으로 넉넉하다.

@<강화된 절 더미를 비운다@>=
csave = c
@<할 일 더미를 비운다@>
for strengthened != sentinel {
	c = strengthened
	mems++; strengthened = cmem[c-litHeadTop].link
	mems++
	if mem[c].cls != 0 {
		mems++; cmem[c-litHeadTop].link = 0
		@<절 |c|에 포섭되는 절을...@>
		@<할 일 더미를 비운다@>
		@<아직 |c|가 남았으면 강화에 쓴다@>
	}
}
c = csave

@ @<아직 |c|가 남았으면...@>=
mems++
if mem[c].cls != 0 {
	specialcase = 0
	@<절 |c|로 강화할 수 있는...@>
	@<할 일 더미를 비운다@>
	mems++; mem[c].lit = round
	mems++; cmem[c-litHeadTop].size = 0
}

@* 변수 소거.
만족 가능성은 본디 $\exists x\,\exists y\,f(x,y)$를 따지는 일이다. $x$는 변수 하나이고
$y$는 나머지 변수들이다. $f$를 $\bigl(x\lor\alpha(y)\bigr)\land\bigl(\bar
x\lor\beta(y)\bigr)\land\gamma(y)$로 적으면 $\exists x\,f(x,y)=f(0,y)\lor f(1,y)$이므로
$x$를 없앤 문제 $\exists y\,\bigl(\alpha(y)\lor\beta(y)\bigr)\land\gamma(y)$를 얻는다.
곧 $x$나 $\bar x$가 든 절을 모두 $\alpha\lor\beta$의 절들로 바꾸면 된다.
$\alpha=\alpha_1\land\cdots\land\alpha_a$이고 $\beta=\beta_1\land\cdots\land\beta_b$이면 그
절들은 분해 결과 $\alpha_i\lor\beta_j$들이다.

코드로는 |l|이 든 절 |c|와 $\bar l$이 든 절 |cc|의 분해를 셈한다. 결과가 늘 참(어떤
$y$와 $\bar y$를 함께 품음)이면 |p|를 0으로 둔다. 아니면 분해 결과의 칸들이
|p|, \dots, |left(left(1))|, |left(1)|이 된다. 이 칸들은 |left|로만 잠정적으로 이어
두고 아직 큰 구조에 넣지 않는다.

@<|c|와 |cc|를 |l|에 대해 분해한다@>=
p = 1
mems += 2; v = mem[c].left; u = mem[v].lit
mems += 2; vv = mem[cc].left; uu = mem[vv].lit
for u+uu != 0 {
	if u == uu {
		@<|u|를 옮겨 적는다@>
		@<|v|를 왼쪽으로 옮긴다@>
		@<|vv|를 왼쪽으로 옮긴다@>
	} else if u == uu^1 {
		if u != l {
			@<늘 참인 분해 결과를 버리고 |break|@>
		}
		@<|v|를 왼쪽으로 옮긴다@>
		@<|vv|를 왼쪽으로 옮긴다@>
	} else if u > uu {
		@<|u|를 옮겨 적는다@>
		@<|v|를 왼쪽으로 옮긴다@>
	} else {
		@<|uu|를 옮겨 적는다@>
		@<|vv|를 왼쪽으로 옮긴다@>
	}
}

@ @<|v|를 왼쪽으로...@>=
mems++; v = mem[v].left
if v < clsHeadTop {
	u = 0
} else {
	mems++; u = mem[v].lit
}

@ @<|vv|를 왼쪽으로...@>=
mems++; vv = mem[vv].left
if vv < clsHeadTop {
	uu = 0
} else {
	mems++; uu = mem[vv].lit
}

@ 새 칸은 빈칸 더미에서 꺼내고, 더미가 비었으면 아직 쓰지 않은 칸을 쓴다. 그것마저
없으면 원본은 끝나 버리고, 꾸러미는 |ErrMemory|를 돌려준다.

@<|u|를 옮겨...@>=
q = p
@<새 칸 |p|를 얻는다@>
mems += 2; mem[q].left = p; mem[p].lit = u

@ @<|uu|를 옮겨...@>=
q = p
@<새 칸 |p|를 얻는다@>
mems += 2; mem[q].left = p; mem[p].lit = uu

@ @<새 칸 |p|를...@>=
if avail != 0 {
	p = avail
	mems++; avail = mem[p].left
} else {
	if uint64(xcells) == memMax {
		err = ErrMemory
		goto record
	}
	p = xcells
	xcells++
}

@ @<늘 참인 분해 결과를...@>=
if p != 1 {
	mems += 2; mem[p].left = avail; avail = mem[1].left
}
p = 0
break

@ E\'en과 Biere는 $x$가 다른 변수들에 의해 온전히 정해질 때 크게 줄일 수 있다는 것을
알아챘다. 절들을 $\alpha=\alpha^{(0)}\lor\alpha^{(1)}$, $\beta=\beta^{(0)}\lor\beta^{(1)}$로
가르되 $\alpha^{(0)}=\lnot\beta^{(0)}$이 되게 할 수 있으면, 곧 $x=\beta^{(0)}$가 함수적으로
정해지면, 같은 빛깔끼리의 분해 결과 $\alpha^{(0)}\land\beta^{(0)}$과
$\alpha^{(1)}\land\beta^{(1)}$은 셈할 필요가 없다. 다른 빛깔끼리의 분해 결과가 그것들을
함의하기 때문이다.

이 프로그램은 $\alpha^{(0)}$가 단위 절 $l_1\land\cdots\land l_k$이고 $\beta^{(0)}$가 절 하나
$\bar l_1\lor\cdots\lor\bar l_k$인 간단한 경우, 곧 AND, OR, NAND, NOR 종속만 찾는다.
찾으면 |beta0|를 절 $\bar x\lor\bar l_1\lor\cdots\lor\bar l_k$로 두고 $\bar l_i$마다
|lmem|에 새 도장 |stamp|를 찍는다. 못 찾으면 |beta0|는 0이다.

@<간단한 함수적 종속이 있으면 $\alpha$와 $\beta$를 가른다@>=
stbits = 0; beta0 = 0; stamp++
ll = l ^ 1
@<|l|과 함께 이진 절에 든 리터럴에 모두 도장을 찍는다@>
if stbits != 0 {
	mems++; stbits |= mem[ll].sig
	for mems, p = mems+1, mem[ll].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
		mems++; c = mem[p].cls
		mems++
		if mem[c].sig&^stbits == 0 {
			@<|c|의 다른 리터럴의 부정에 모두 도장이 있으면 |beta0=c|로 두고 |break|@>
		}
	}
}
if beta0 != 0 {
	stamp++
	@<절 |beta0|의 리터럴들에 도장을 찍는다@>
}

@ @<|l|과 함께 이진 절에...@>=
for mems, p = mems+1, mem[l].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
	mems += 2
	if mem[mem[p].cls].cls == 2 {
		mems++; q = mem[p].right
		if q < clsHeadTop {
			mems++; q = mem[p].left
		}
		mems += 2; lmem[mem[q].lit] = stamp
		mems++; stbits |= mem[mem[q].lit^1].sig
	}
}

@ @<|c|의 다른 리터럴의...@>=
for mems, q = mems+1, mem[p].left; q != p; mems, q = mems+1, mem[q].left {
	if q < clsHeadTop {
		continue
	}
	mems += 2
	if lmem[mem[q].lit^1] != stamp {
		break
	}
}
if q == p {
	beta0 = c
	break
}

@ @<절 |beta0|의 리터럴들에...@>=
if mem[p].cls != beta0 || mem[p].lit != ll {
	panic("sat: 이럴 수는 없다 (partitioning)")
}
for mems, q = mems+1, mem[p].left; q != p; mems, q = mems+1, mem[q].left {
	if q < clsHeadTop {
		continue
	}
	mems += 2; lmem[mem[q].lit^1] = stamp
}

@ @<|Simplify|의 지역 변수@>=
var (
	stamp        uint64 // 한 번에 하나뿐인 도장
	beta0        uint32 // 좋은 가르기의 $\beta^{(0)}$ 절
	alpha0       bool   // |c|가 $\alpha^{(0)}$에 드는가
	lastNew      uint32 // 마지막으로 만든 분해 결과의 첫 칸
	alf, bet     uint32 // $\alpha_i$와 $\beta_j$를 훑는 칸
	clausesSaved int    // |x|를 없애면 줄어드는 절의 수
	elimTries    uint64
	funcTotal    uint64
)

@ 이제 변수 |x|를 없앨 만한지 따지는 곳이다. |x|와 $\bar x$가 모두 |Cutoff|보다 많은 절에
나오면 따지지도 않는다. 없애면 절이 거의 틀림없이 늘 것이기 때문이다.

분해 결과들은 |left|로 이은 줄들이고, 줄끼리는 |down|으로 |down(0)|부터 |lastNew|까지
이어 둔다. 결과가 줄일 절의 수보다 많아지면 모두 버린다.

@<|x|를 없앨 분해 결과를 만들거나 |goto elimDone|@>=
l = x + x
mems += 2; clausesSaved = int(mem[l].lit + mem[l+1].lit)
if mem[l].lit > uint32(par.Cutoff) && mem[l+1].lit > uint32(par.Cutoff) {
	goto elimDone
}
if uint64(mem[l].lit)*uint64(mem[l+1].lit) > uint64(mem[l].lit+mem[l+1].lit)+par.Optimism {
	goto elimDone
}
elimTries++
@<간단한 함수적 종속이...@>
if beta0 == 0 {
	l++
	@<간단한 함수적 종속이...@>
}
if beta0 != 0 {
	funcTotal++
}
lastNew = 0
@<같은 빛깔이 아닌 $\alpha_i$와 $\beta_j$를 모두 분해한다@>
mems++; mem[lastNew].down = 0

@ 원본은 새 분해 결과의 첫 칸에 진단용으로 |c|와 |cc|를 적어 둔다. mem을 세지 않고
어디서도 읽지 않으므로 옮기지 않았다.

@<같은 빛깔이 아닌...@>=
for mems, alf = mems+1, mem[l].down; alf >= litHeadTop; mems, alf = mems+1, mem[alf].down {
	mems++; c = mem[alf].cls
	@<|c|가 $\alpha^{(0)}$에 드는지 정한다@>
	for mems, bet = mems+1, mem[ll].down; bet >= litHeadTop; mems, bet = mems+1, mem[bet].down {
		mems++; cc = mem[bet].cls
		if cc == beta0 && alpha0 || cc != beta0 && !alpha0 {
			continue
		}
		@<|c|와 |cc|를 |l|에 대해...@>
		if p != 0 {
			mems++; mem[p].left = 0
			mems += 2; mem[lastNew].down = mem[1].left
			mems++; lastNew = mem[1].left; mem[lastNew].right = p
			if clausesSaved--; clausesSaved < 0 {
				@<새 분해 결과를 버리고 |goto elimDone|@>
			}
		}
	}
}

@ @<|c|가 $\alpha^{(0)}$에...@>=
if beta0 == 0 {
	alpha0 = true
} else {
	alpha0 = false
	mems++
	if mem[c].cls == 2 {
		mems++; q = mem[c].right
		if q == alf {
			q = mem[c].left
		}
		mems += 2
		if lmem[mem[q].lit] == stamp {
			alpha0 = true
		}
	}
}

@ 아쉽게도 분해 결과가 바꿀 절보다 많아졌다.

@<새 분해 결과를 버리고...@>=
for mems, p = mems+1, mem[0].down; ; mems, p = mems+1, mem[p].down {
	mems += 2; mem[mem[p].right].left = avail; avail = p
	if p == lastNew {
		break
	}
}
goto elimDone

@ 한 바퀴의 소거. 먼저 후보들을 차수(두 부호가 나오는 절 수의 합)에 따라 바구니에 담고,
차수가 작은 바구니부터 꺼내 따진다. 최근에 건드리지 않은 변수는 볼 필요가 없다.

@<변수들을 없애 본다@>=
@<소거 후보를 바구니에 담는다@>
for b = 2; b <= uint32(par.Buckets); b++ {
	mems++
	if bucket[b] != 0 {
		for x = bucket[b]; x != 0; mems, x = mems+1, vmem[x].blink {
			mems++
			if vmem[x].stable == 0 {
				@<|x|를 없앨 분해 결과를...@>
				@<|x|를 없애고 그 절들을 분해 결과로 바꾼다@>
				@<강화된 절 더미를 비운다@>
			elimDone:
				mems++; vmem[x].stable = 1
			}
		}
	}
}

@ @<소거 후보를 바구니에...@>=
for b = 2; b <= uint32(par.Buckets); b++ {
	mems++; bucket[b] = 0
}
for x = vars; x != 0; x-- {
	mems++
	if vmem[x].stable != 0 {
		continue
	}
	if vmem[x].status != varNorm {
		panic("sat: 이럴 수는 없다 (touched and eliminated)")
	}
	l = x + x
	mems += 2; p, q = mem[l].lit, mem[l+1].lit
	if p > uint32(par.Cutoff) && q > uint32(par.Cutoff) {
		goto reject
	}
	b = p + q
	if uint64(p)*uint64(q) > uint64(b)+par.Optimism {
		goto reject
	}
	b = min(b, uint32(par.Buckets))
	mems += 2; vmem[x].blink = bucket[b]
	mems++; bucket[b] = x
	continue
reject:
	mems++; vmem[x].stable = 1
}

@ 옛 칸들은 새 칸을 모두 끼운 {\it 뒤에야\/} 치운다. 그러지 않으면 순수 리터럴이 아닌데
순수 리터럴로 잘못 볼 수 있다. 하지만 옛 칸들을 옛 절 머리에서 떼어 두는 것은 괜찮다.

@<|x|를 없애고 그 절들을...@>=
@<erp에 |x|를 없앤 기록을 적는다@>
mems += 2; mem[lastNew].down = 0; lastNew = mem[0].down
v = x + x
@<|v|의 절들을 새 분해 결과로 바꾼다@>
v++
@<|v|의 절들을 새 분해 결과로 바꾼다@>
@<|v|가 든 절의 칸들을 치운다@>
v--
@<|v|가 든 절의 칸들을 치운다@>
mems++; vmem[x].status = elimRes; varsGone++
clausesGone += uint32(clausesSaved)

@ 함수적 종속을 찾았으면 ``$l$은 절 $\beta^{(0)}\setminus\bar l$이 만족될 때 참이다''를
적는다. 아니면 두 부호 가운데 적게 나오는 리터럴 $v$를 골라 ``$\bar v$는 $v$가 든 절들이
$v$ 없이 모두 만족될 때 참이다''를 적는다. $v$가 든 절이 하나라도 $v$ 없이 만족되지
않으면 $v$가 참이어야 하기 때문이다.

@<erp에 |x|를 없앤 기록을...@>=
if beta0 != 0 {
	pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
	flag := uint8(erpFirst)
	for mems, q = mems+1, mem[beta0].right; q >= clsHeadTop; mems, q = mems+1, mem[q].right {
		mems++
		if mem[q].lit != ll {
			pre.erp = append(pre.erp, erpCell{Lit(mem[q].lit), flag})
			flag = 0
		}
	}
} else {
	@<적게 나오는 리터럴 |v|의 절들을 erp에 적는다@>
}

@ @<적게 나오는 리터럴 |v|의...@>=
mems++; k, v = mem[l].lit, l
mems++
if k > mem[ll].lit {
	k, v = mem[ll].lit, ll
}
pre.erp = append(pre.erp, erpCell{Lit(v ^ 1), erpDef})
for mems, p = mems+1, mem[v].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
	flag := uint8(erpFirst)
	for mems, q = mems+1, mem[p].right; q != p; mems, q = mems+1, mem[q].right {
		if q >= clsHeadTop {
			mems++; pre.erp = append(pre.erp, erpCell{Lit(mem[q].lit), flag})
			flag = 0
		}
	}
}

@ 절 |c|를 머리에서 떼어 내고 그 자리에 새 분해 결과를 앉힌다. 분해 결과가 떨어지면
남은 옛 절 자리는 비운다.

@<|v|의 절들을 새...@>=
for mems, p = mems+1, mem[v].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
	mems++; c = mem[p].cls
	mems++; q, r = mem[c].right, mem[c].left
	mems += 2; mem[q].left = r; mem[r].right = q
	if lastNew != 0 {
		mems++; pp = mem[lastNew].down
		@<|lastNew|를 절 자리 |c|에 앉힌다@>
		mems++; cmem[c-litHeadTop].size = 1
		mems++; lastNew = pp
	} else {
		mems++; mem[c].cls = 0
	}
}

@ 분해 결과의 칸들은 |left|로 이어져 있다. 칸마다 리터럴 목록의 맨 아래에 끼우고
|right| 연결과 서명과 크기를 짓는다. 크기가 1이면 단위 절이다.

@<|lastNew|를 절 자리...@>=
for q, r, sz, bits = lastNew, c, 0, 0; q != 0; mems, r, q = mems+1, q, mem[q].left {
	mems++; u = mem[q].lit
	mems += 2; mem[u].lit++
	mems++; w = mem[u].up
	mems += 2; mem[u].up = q; mem[w].down = q
	mems++; mem[q].up = w; mem[q].down = u
	mems++; bits |= mem[u].sig
	mems++; mem[q].right = r
	mems++; mem[q].cls = c
	sz++
}
mems += 2; mem[c].cls = sz; mem[c].sig = bits
mems += 2; mem[c].left = lastNew; mem[c].right = r; mem[r].left = c
if sz == 1 {
	mems++; w = mem[r].lit
	@<리터럴 |w|를 참으로...@>
}

@ 분해한 절들에 든 리터럴은 옛 절을 치울 때 모두 건드린다. 이 리터럴들이 이번 바퀴에
새 절에 들었다는 표시(|littime|)도 여기서 남긴다.

@<|v|가 든 절의 칸들을...@>=
for mems, p = mems+1, mem[v].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
	for mems, q = mems+1, mem[p].right; q != p; mems, q = mems+1, mem[q].right {
		mems++; r, w = mem[q].up, mem[q].down
		mems += 2; mem[r].down = w; mem[w].up = r
		mems++; w = mem[q].lit
		mems++; vmem[w>>1].stable = 0
		mems += 2; mem[w].lit--; mem[w].cls = round
		if mem[w].lit == 0 {
			@<리터럴 |w|가 이미 정해지지...@>
		}
	}
	mems++; mem[mem[p].right].left = avail; avail = p
}

@* 대단원.
전처리의 큰 흐름은 짧다. 처음에는 모든 절을 ``강화된'' 것으로 쳐서 더미에 올린다. 모든
절이 다른 절을 포섭하고 강화할 기회를 한 번씩 얻게 하려는 것이다. 더미를 비운 다음에는
변수 소거를 한 바퀴씩 되풀이한다. 한 바퀴에 없앤 변수가 없거나 변수가 모두 사라지면
멈춘다. 바퀴 사이에는 새로 생긴 절들로 포섭과 강화를 한 번 더 한다.

@<더는 바뀌지 않을 때까지...@>=
@<모든 절을 강화된 절 더미에 올린다@>
@<강화된 절 더미를 비운다@>
for round = 1; round <= uint32(par.MaxRounds); round++ {
	progress = varsGone
	@<변수들을 없애 본다@>
	if progress == varsGone || varsGone == vars {
		break
	}
	@<새 절들로 포섭과 강화를 한 바퀴 돈다@>
}
round = min(round, uint32(par.MaxRounds))

@ @<모든 절을 강화된...@>=
mems++; cmem[0].link = sentinel; cmem[0].size = 0
for c = litHeadTop + 1; c < clsHeadTop; c++ {
	mems++; cmem[c-litHeadTop].link = c - 1; cmem[c-litHeadTop].size = 0
}
strengthened = c - 1

@ 강화된 절은 이미 온전히 쓰였다. 하지만 다른 옛 절들도 지난 바퀴의 소거가 만든 새 절을
포섭할 수 있다. 그러려면 그 옛 절의 리터럴이 모두 새 절에 한 번은 나와야 한다. 새 절을
강화할 수도 있다.

여기서 절 |c|의 |size| 자료(원본의 |newsize|)는 |c|가 새 절이면 1, 아니면 0이다. 그리고
리터럴 |l|은 이번 바퀴의 새 절에 나왔으면 |littime(l)|가 |round|다. 그런 리터럴마다, 그
리터럴이 든 절의 |newsize|에 4를 더하고 그 부정이 든 절의 |newsize|에 2를 OR한다.
그러면 옛 절이 쓸 만한지 빠르게 가늠할 수 있다. 없어진 변수는 건너뛴다.

@<새 절들로 포섭과 강화를...@>=
for l = 2; l < litHeadTop; l++ {
	if l&1 == 0 {
		mems++
		if vmem[l>>1].status != varNorm {
			l++
			continue
		}
	}
	mems++
	if mem[l].cls == round {
		@<|l|의 절들의 |newsize|를 고친다@>
	}
}
for c = litHeadTop; c < clsHeadTop; c++ {
	mems++
	if mem[c].cls != 0 {
		if mem[c].lit < round {
			@<최근에 쓰지 않은 절 |c|로 포섭과 강화를 해 본다@>
		}
		mems++; cmem[c-litHeadTop].size = 0
	}
}

@ @<|l|의 절들의 |newsize|를...@>=
for mems, p = mems+1, mem[l].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
	mems++; c = mem[p].cls
	mems += 2; cmem[c-litHeadTop].size += 4
}
for mems, p = mems+1, mem[l^1].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
	mems++; c = mem[p].cls
	mems += 2; cmem[c-litHeadTop].size |= 2
}

@ 절의 리터럴이 모두 새 절에 나왔으면(|newsize|의 4의 몫이 크기와 같으면) 포섭을 해 본다.

@<최근에 쓰지 않은 절 |c|로...@>=
mems++
if mem[c].cls == cmem[c-litHeadTop].size>>2 {
	@<절 |c|에 포섭되는 절을...@>
	@<강화된 절 더미를 비운다@>
} else if cmem[c-litHeadTop].size&1 != 0 {
	panic("sat: 이럴 수는 없다 (new clause not all new)")
}
if cmem[c-litHeadTop].size&3 != 0 {
	@<어쩌면 |c|로 강화해 본다@>
}

@ 새 절이면 제한 없이 강화에 쓴다. 옛 절이면, 리터럴 하나만 빼고 모두 새 절에 나왔을
때만 쓰고 그 하나를 |u|로 삼는다. 원본은 |size(c)-1|을 부호 없는 수로 셈한다. |c|가
그새 사라져 크기가 0이면 이것이 매우 큰 수가 되어 |specialcase|가 $-1$이 된다.
|uint32| 산술이 그 동작을 그대로 옮긴다.

@<어쩌면 |c|로 강화해...@>=
switch {
case cmem[c-litHeadTop].size&1 != 0:
	specialcase = 0
case cmem[c-litHeadTop].size>>2 < mem[c].cls-1:
	specialcase = -1
default:
	specialcase = 1
}
if specialcase >= 0 {
	@<절 |c|로 강화할 수 있는...@>
	@<강화된 절 더미를 비운다@>
}

@ $\bar u$가 새 절에 나오지 않았거나, |c|의 다른 리터럴이 모두 새 절에 나오지 않았으면
|u|를 버린다.

@<특별한 조건에 맞지...@>=
mems++
if mem[u^1].cls != round {
	continue
}
t2 = mem[c].cls
if mem[u].cls != round {
	t2--
}
mems++
if cmem[c-litHeadTop].size>>2 != t2 {
	continue
}

@ 줄인 절을 적어 둔다. 원본은 여기서 표준 출력에 찍는데, 찍으면서 mem을 센다.

@<줄인 절을 적어...@>=
for c = litHeadTop; c < clsHeadTop; c++ {
	mems++
	if mem[c].cls != 0 {
		first := firstLit
		for mems, p = mems+1, mem[c].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
			mems++; pre.cells = append(pre.cells, Lit(mem[p].lit)|first)
			first = 0
		}
	}
}
switch {
case varsGone == vars:
	if clausesGone != clauses {
		panic("sat: 이럴 수는 없다 (vars gone but not clauses)")
	}
	status = Sat
case clausesGone == clauses:
	panic("sat: 이럴 수는 없다 (clauses gone but not vars)")
default:
	status = Unknown
}

@ |mem| 칸이 모자라 멈췄으면 반쯤 된 결과는 버린다.

@<전처리 결과와 통계를...@>=
if err == ErrMemory {
	status = Unknown
} else {
	s.pre = pre
}
s.simpStats = SimplifyStats{IMems: imems, Mems: mems, Bytes: bytes, Cells: xcells,
	Subsumptions: subTotal, Strengthenings: strTotal, SubTries: subTries, SubFalse: subFalse,
	StrTries: strTries, StrFalse: strFalse, ElimTries: elimTries, FuncDeps: funcTotal,
	Vars: vars, VarsGone: varsGone, ClausesGone: clausesGone, Rounds: round,
	Unsat: status == Unsat}

@* 줄인 절 풀기와 되돌리기.
|Simplify| 뒤에 |Solve|를 부르면 \.{cdcl.w}의 |Solve|가 곧바로 이 문으로 넘어온다.
줄인 절로 풀이기를 새로 지어 풀고, 해가 나오면 erp 자료로 원래 변수 모두의 값을 채운다.
파일 경계를 넘어 부르므로 이름 있는 절 대신 문으로 두었다.

@<함수들@>=
func (s *Solver) solvePreprocessed(ctx context.Context) (Status, error) {
	pre := s.pre
	s.model, s.truth, s.stats = nil, nil, Stats{}
	if pre.unsat {
		return Unsat, nil
	}
	var sol []Lit
	if len(pre.cells) > 0 {
		@<줄인 절로 풀이기 |red|를 짓는다@>
		@<|red|를 풀고 해를 원래 변수로 옮긴다@>
	}
	@<erp를 거꾸로 되짚어 해를 채운다@>
	return Sat, nil
}

@ 원본 파이프라인에서 \.{SAT13}은 줄인 절을 글자로 읽으므로, 변수 번호가 줄인 절에 처음
나온 차례로 새로 매겨진다. 그 차례를 따라야 mem 수가 같다. |renum|은 원래 변수 번호에서
새 번호로, |old|는 그 거꾸로 간다.

@<줄인 절로 풀이기 |red|를...@>=
red := New()
red.Params = s.Params
renum, old := make([]int, s.NumVars()+1), []int{0}
var clause []Lit
for i, l := range pre.cells {
	if l&firstLit != 0 && i > 0 {
		red.AddClause(clause...)
		clause = clause[:0]
	}
	l &^= firstLit
	@<리터럴 |l|을 새 번호로 옮겨 |clause|에 보탠다@>
}
red.AddClause(clause...)

@ @<리터럴 |l|을 새 번호로...@>=
if renum[l.Var()] == 0 {
	renum[l.Var()] = red.NewVar().Var()
	old = append(old, l.Var())
}
nl := Pos(renum[l.Var()])
if l.IsNeg() {
	nl = nl.Not()
}
clause = append(clause, nl)

@ @<|red|를 풀고...@>=
st, err := red.Solve(ctx)
s.stats = red.stats
if st != Sat {
	return st, err
}
for _, l := range red.model {
	ol := Pos(old[l.Var()])
	if l.IsNeg() {
		ol = ol.Not()
	}
	sol = append(sol, ol)
}

@ \.{SAT12-ERP}을 따라 한다. 리터럴마다 참(1), 거짓($-1$), 모름(0)을 적는 표 |val|을
두고, 먼저 받은 해를 적는다. 원본은 해를 임시 칸에 넣었다가 되감으며 읽으므로 해가
{\it 거꾸로\/} 적힌다. |Model|의 차례를 원본의 출력과 맞추려고 여기서도 거꾸로 적는다.

@<erp를 거꾸로...@>=
val := make([]int8, 2*s.NumVars()+2)
model := make([]Lit, 0, s.NumVars())
for i := len(sol) - 1; i >= 0; i-- {
	model = append(model, sol[i])
	val[sol[i]], val[sol[i]^1] = 1, -1
}
@<erp 칸들을 거꾸로 되짚는다@>
s.model = model
s.truth = make([]bool, s.NumVars()+1)
for _, l := range model {
	s.truth[l.Var()] = !l.IsNeg()
}

@ erp 자료를 뒤에서부터 절 하나씩 읽는다. 절마다 참인 리터럴이 있는지(|vv|) 보고, 한
무리의 절이 모두 만족되는지(|v|)를 모은다. 절에 값을 모르는 리터럴이 있으면 멋대로 그
리터럴을 참으로 둔다. 무리의 머리, 곧 값을 정할 리터럴에 이르면 |v|가 그 값이다. 그
리터럴은 뒤에 오는 절들에 쓰인 변수들보다 나중에 없어졌으므로, 뒤에서부터 읽으면 쓸 값이
늘 먼저 정해져 있다.

@<erp 칸들을 거꾸로...@>=
v := true
for i := len(pre.erp); i > 0; {
	vv := false
	var e erpCell
	for {
		i--
		e = pre.erp[i]
		if e.flag == erpDef {
			break
		}
		@<칸 |e|의 리터럴을 절 평가에 보탠다@>
		if e.flag == erpFirst {
			break
		}
	}
	@<절을 마쳤으면 |v|에 반영하고, 머리면 값을 정한다@>
}

@ @<칸 |e|의 리터럴을...@>=
if val[e.lit] == 0 {
	model = append(model, e.lit)
	val[e.lit], val[e.lit^1] = 1, -1
}
if val[e.lit] == 1 {
	vv = true
}

@ @<절을 마쳤으면...@>=
if e.flag != erpDef {
	v = v && vv
	continue
}
if v {
	val[e.lit], val[e.lit^1] = 1, -1
	model = append(model, e.lit)
} else {
	val[e.lit], val[e.lit^1] = -1, 1
	model = append(model, e.lit^1)
}
v = true

@* 원본의 꼴로 적기.
줄인 절과 erp 자료를 원본이 쓰는 글자 꼴 그대로 적는 문 둘. 원본 파이프라인의 다른
프로그램에 넘기거나 원본과 견줄 때 쓴다. 전처리하지 않았으면 잘못을 돌려준다.

@<함수들@>=
func (s *Solver) WriteSimplified(w io.Writer) error {
	if s.pre == nil {
		return errors.New("sat: 전처리한 결과가 없다")
	}
	var b strings.Builder
	for i, l := range s.pre.cells {
		if l&firstLit != 0 && i > 0 {
			b.WriteByte('\n')
		}
		b.WriteByte(' ')
		b.WriteString(s.LitName(l &^ firstLit))
	}
	if len(s.pre.cells) > 0 {
		b.WriteByte('\n')
	}
	_, err := io.WriteString(w, b.String())
	return err
}

@ erp 파일은 무리마다 `리터럴 \.{<-}$k$' 한 줄과 절 $k$줄로 이루어진다.

@<함수들@>=
func (s *Solver) WriteERP(w io.Writer) error {
	if s.pre == nil {
		return errors.New("sat: 전처리한 결과가 없다")
	}
	var b strings.Builder
	erp := s.pre.erp
	for i := 0; i < len(erp); {
		@<|erp[i]|에서 시작하는 무리 하나를 적는다@>
	}
	_, err := io.WriteString(w, b.String())
	return err
}

@ @<|erp[i]|에서 시작하는...@>=
j, k := i+1, 0
for ; j < len(erp) && erp[j].flag != erpDef; j++ {
	if erp[j].flag == erpFirst {
		k++
	}
}
fmt.Fprintf(&b, "%s <-%d\n", s.LitName(erp[i].lit), k)
for t := i + 1; t < j; t++ {
	if erp[t].flag == erpFirst && t > i+1 {
		b.WriteByte('\n')
	}
	b.WriteByte(' ')
	b.WriteString(s.LitName(erp[t].lit))
}
if k > 0 {
	b.WriteByte('\n')
}
i = j

@* 시험.
@(simplify_test.go@>=
package sat

import (
	"context"
	"crypto/md5"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

@<시험들@>

@<시험에 쓰는 함수들@>

@ 첫째 시험은 \CEE/ 원본과의 대조다. \.{testdata/sat12-runs.golden}의 줄마다 문제 이름,
선택, 원본의 종료 코드, 작별 인사, 없앤 것의 요약, 줄인 절과 erp 파일의 MD5, 줄인 절을
\.{SAT13}으로 푼 작별 인사, \.{SAT12-ERP}이 되살린 해의 MD5가 있다. 원본은
\.{-std=gnu89 -ffp-contract=off}로 컴파일했다. Rivest의 절 여덟 개는 만족할 수 없음이,
일곱 개는 절이 모두 사라짐이 전처리에서 곧바로 드러난다.

@<시험들@>=
func TestSimplifyGolden(t *testing.T) {
	for _, f := range goldenRows(t, "sat12-runs.golden") {
		name := f[0] + " [" + f[1] + "]"
		s := readFile(t, filepath.Join("testdata", f[0]+".sat"))
		for _, o := range strings.Fields(f[1]) {
			if err := s.SimplifyParams.Set(o); err != nil {
				t.Fatal(err)
			}
		}
		st, err := s.Simplify(context.Background())
		@<전처리 결과를 원본과 견준다@>
		@<줄인 절을 풀어 원본 파이프라인과 견준다@>
	}
}

@ 원본이 칸이 모자라 끝났으면 우리도 |ErrMemory|여야 한다.

@<전처리 결과를 원본과...@>=
if f[2] != "0" {
	if !errors.Is(err, ErrMemory) {
		t.Errorf("%s: ErrMemory여야 하는데 %v", name, err)
	}
	continue
}
if err != nil {
	t.Fatalf("%s: %v", name, err)
}
lines := strings.Split(s.SimplifyStats().String(), "\n")
if lines[0] != f[4] || lines[1] != f[3] {
	t.Errorf("%s:\n  %s\n  %s\n인데\n  %s\n  %s\n여야 한다", name, lines[0], lines[1], f[4], f[3])
}
var pre, erp strings.Builder
s.WriteSimplified(&pre)
s.WriteERP(&erp)
if md5hex(pre.String()) != f[5] || md5hex(erp.String()) != f[6] {
	t.Errorf("%s: 줄인 절이나 erp가 원본과 다르다", name)
}

@ 원본 파이프라인에서 \.{SAT13}을 돌리지 않은 경우(줄인 절이 없는 경우)에는 작별 인사
칸이 비어 있다.

@<줄인 절을 풀어 원본...@>=
st2, err := s.Solve(context.Background())
if err != nil {
	t.Fatalf("%s: %v", name, err)
}
if st == Unsat && st2 != Unsat {
	t.Errorf("%s: 전처리가 UNSAT인데 풀이가 %v", name, st2)
}
if f[7] != "" {
	wantLine(t, name, s, f[7])
}
if st2 == Sat {
	@<되살린 해가 원래 절을 만족하고 원본과 같은지 본다@>
}

@ @<되살린 해가 원래...@>=
var b strings.Builder
for _, l := range s.Model() {
	fmt.Fprintf(&b, " %s", s.LitName(l))
}
if md5hex(b.String()+"\n") != f[8] {
	t.Errorf("%s: 되살린 해가 원본과 다르다:%s", name, b.String())
}
for c := range s.Clauses() {
	if !s.satisfied(c) {
		t.Errorf("%s: 되살린 해가 절 %v를 만족하지 않는다", name, c)
		break
	}
}

@ 둘째 시험은 크누스의 벤치마크 113개 전부를 기본 매개변수로 전처리해 원본과 견준다.
\.{queens-100} 하나에만 원본으로 90초가 걸리므로 \.{SATEXAMPLES}를 줄 때만 돈다.

@<시험들@>=
func TestSimplifySATexamples(t *testing.T) {
	dir := os.Getenv("SATEXAMPLES")
	if dir == "" {
		t.Skip("SATEXAMPLES가 비어 있다")
	}
	for _, f := range goldenRows(t, "sat12-examples.golden") {
		path, _ := filepath.Glob(filepath.Join(dir, "benchmarks-*", f[0]+".sat"))
		s := readFile(t, path[0])
		if _, err := s.Simplify(context.Background()); err != nil {
			t.Fatalf("%s: %v", f[0], err)
		}
		@<벤치마크의 전처리 결과를 견준다@>
	}
}

@ @<벤치마크의 전처리 결과를...@>=
alt := strings.Split(s.SimplifyStats().String(), "\n")[1]
var pre, erp strings.Builder
s.WriteSimplified(&pre)
s.WriteERP(&erp)
if alt != f[2] || md5hex(pre.String()) != f[3] || md5hex(erp.String()) != f[4] {
	t.Errorf("%s:\n  %s\n인데\n  %s\n여야 한다 (또는 출력이 다르다)", f[0], alt, f[2])
}

@ 셋째 시험은 꾸러미로 쓰는 길이다. 전처리 뒤에 절을 보태면 전처리 결과는 버려져야 한다.

@<시험들@>=
func TestSimplifyAPI(t *testing.T) {
	s := New()
	a, b, c := s.NewVar(), s.NewVar(), s.NewVar()
	s.AddClause(a, b)
	s.AddClause(a.Not(), c)
	s.AddClause(b.Not(), c)
	if _, err := s.Simplify(context.Background()); err != nil || s.pre == nil {
		t.Fatalf("전처리가 되지 않았다: %v", err)
	}
	if st, _ := s.Solve(context.Background()); st != Sat || !s.Value(c) {
		t.Errorf("풀이가 %v, c=%v", st, s.Value(c))
	}
	s.AddClause(c.Not())
	if s.pre != nil {
		t.Error("절을 보탰는데 전처리 결과가 남았다")
	}
	if st, _ := s.Solve(context.Background()); st != Unsat {
		t.Errorf("풀이가 %v인데 UNSAT이어야 한다", st)
	}
}

@ @<시험에 쓰는 함수들@>=
func md5hex(s string) string { return fmt.Sprintf("%x", md5.Sum([]byte(s))) }

func (s *Solver) satisfied(c []Lit) bool {
	for _, l := range c {
		if s.Value(l) {
			return true
		}
	}
	return false
}

@* 색인.
