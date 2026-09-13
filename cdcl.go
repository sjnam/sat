//line cdcl.w:44
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

//line cdcl.w:66
type Status int

const (
	Unknown Status = iota // 답을 내지 못했다
	Sat                   // 만족할 수 있다
	Unsat                 // 만족할 수 없다
)

//line cdcl.w:91
var (
	ErrTimeout  = errors.New("sat: mem 한도에 이르렀다")
	ErrDoomsday = errors.New("sat: 배운 절의 수가 doomsday에 이르렀다")
	ErrMemory   = errors.New("sat: mem 배열이 모자란다")

//line cdcl.w:95
)

//line cdcl.w:103
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

//line cdcl.w:123
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

//line cdcl.w:209
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

//line cdcl.w:410
const (
	clauseExtra       = 3          // 모든 절의 머리 칸 수
	learnedSupplement = 2          // 배운 절에 더 붙는 머리 칸 수
	learnedExtra      = 5          // 배운 절의 머리 칸 수
	signBit           = 0x80000000 // 지워진 리터럴의 표
	unset             = 0xffffffff // 값이 없는 변수의 |value|
)

//line cdcl.w:443
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

//line cdcl.w:1100
const (
	tiny       = 2.225073858507201383e-308
	singleTiny = 1.1754943508222875080e-38

//line cdcl.w:1103
)

//line cdcl.w:1645
const (
	buckets  = 256  // 눈금에 올린 범위의 가짓수
	badlevel = 16.0 // 이보다 큰 범위는 사실상 무한
)

//line cdcl.w:2012
const checkEvery = 1 << 22 // |context|를 묻는 mem 간격

//line cdcl.w:75
func (st Status) String() string {
	switch st {
	case Sat:
		return "SAT"
	case Unsat:
		return "UNSAT"
	}
	return "UNKNOWN"
}

//line cdcl.w:144
func (p *Params) Set(opt string) error {
	if opt == "" {
		return errors.New("sat: 빈 선택")
	}
	arg := opt[1:]
	var err error
	switch opt[0] {

//line cdcl.w:165
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

//line cdcl.w:152

//line cdcl.w:186
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

//line cdcl.w:153
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

//line cdcl.w:224
func (s *Solver) Stats() Stats { return s.stats }

//line cdcl.w:230
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

//line cdcl.w:245
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

//line cdcl.w:241
	return b.String()
}

//line cdcl.w:260
func plural(n uint64, one, many string) string {
	if n == 1 {
		return one
	}
	return many
}

//line cdcl.w:271
func (s *Solver) Model() []Lit { return slices.Clone(s.model) }

func (s *Solver) Value(l Lit) bool {
	if s.truth == nil {
		panic("sat: 찾은 해가 없다")
	}
	return s.truth[l.Var()] != l.IsNeg()
}

//line cdcl.w:298
func (s *Solver) Solve(ctx context.Context) (Status, error) {

//line cdcl.w:328
	var (
		h, hp, i, j, jj, k, kk int
		l, ll, lll, p, q, r    int
		sz, st, t, u, v        int
		c, cc, endc            int
		au, av                 float64
	)

//line cdcl.w:337
	var (
		status                    Status
		err                       error
		par                       Params      // 매개변수의 사본
		rng                       *gbflip.RNG // 원본의 |gb_flip|과 같은 난수열
		vars, clauses, cells      int         // 변수, 절, 리터럴의 수
		imems, mems, bytes, nodes uint64
	)

//line cdcl.w:419
	var (
		mem                      []uint32 // 절들의 큰 배열
		memsize                  int      // |mem|이 자랄 수 있는 한도
		minLearned, firstLearned int      // 입력 절과 배운 절의 경계
		maxLearned               int      // |mem|에서 아직 쓰지 않은 첫 자리
		maxCellsUsed             int      // |mem|에서 쓴 칸 수의 최댓값
		maxLit                   int      // 가장 큰 리터럴
	)

//line cdcl.w:463
	var (
		bmem     []uint32   // 이진 함의
		lmem     []literal  // 리터럴마다
		vmem     []variable // 변수마다
		heap     []int      // 활동도의 최대 힙
		hn       int        // 힙에 든 변수의 수
		trail    []int      // 참으로 둔 리터럴들
		eptr     int        // 트레일의 끝
		ebptr    int        // 이진 함의를 아직 보지 않은 곳
		lptr     int        // 긴 절 함의를 아직 보지 않은 곳
		lbptr    int        // 이진 함의를 훑는 자리
		llevel   int        // 지금 수준의 두 배
		leveldat []int      // 수준마다 트레일의 시작 자리, 그리고 충돌 자료
	)

//line cdcl.w:553
	var (
		trueProbThresh int // $2^{31}\times$|TrueProb|
		cur            int // 임시 칸을 되감는 자리
	)

//line cdcl.w:763
	var (
		lt, lat    int    // 트레일의 리터럴과 그 |bimpEnd|
		la         int    // |bmem|을 훑는 자리
		wa, nextWa int    // 감시 목록의 절과 그다음 절
		agility    uint32 // 값이 뒤집히는 매끄러운 확률
	)

//line cdcl.w:918
	var (
		fullRun       bool  // 전체 달리기 중인가
		conflictSeen  bool  // 이 수준에서 충돌을 보았는가
		conflictLevel int   // 기록된 충돌 더미의 꼭대기
		conflictdat   []int // 전체 달리기의 충돌 자료
	)

//line cdcl.w:1106
	var (
		varBump          float64 = 1.0
		clauseBump       float32 = 1.0
		varBumpFactor    float64 // $1/|VarRho|$
		clauseBumpFactor float32 // $1/|ClauseRho|$
		ac               float32 // 절 활동도
		randProbThresh   int     // $2^{31}\times$|RandProb|
	)

//line cdcl.w:1199
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

//line cdcl.w:1283
	var (
		stack    []int // 손수 다루는 재귀의 더미
		stackptr int   // 더미에 든 것의 수
		levstamp []int // 수준마다의 표시
	)

//line cdcl.w:1346
	var subsumptions uint64 // 즉석 포섭의 수

//line cdcl.w:1509
	var (
		prevLearned                   int     // 가장 최근에 배운 절
		cellsPrelearned, cellsLearned float64 // 배운 절들의 길이 합
		totalLearned                  uint64  // 배운 절의 수
		trivials, discards            uint64  // 자명한 절, 버린 절의 수
	)

//line cdcl.w:1651
	var (
		rangedist      []int    // 눈금마다 절의 수
		asserts        int      // 남겨야 하는 까닭 절의 수
		minrange       int      // 이번에 본 가장 작은 눈금
		maxrange       int      // 가장 큰 눈금
		recyclePoint   int      // 이번 전체 달리기 뒤에 배운 첫 절
		budget         int      // 재활용 뒤에 남길 절의 수
		clauseHeap     []uint64 // 활동도로 일부 정렬하는 힙
		clauseHeapSize int      // 그 크기
		accum          uint64   // 힙에 넣을 값
		nextRecycle    uint64   // 이만큼 배우면 재활용한다
		recycleBump    uint64   // 다음 재활용까지의 간격
	)

//line cdcl.w:2235
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

//line cdcl.w:300
	if s.pre != nil {
		return s.solvePreprocessed(ctx)
	}
	if s.empty {
		s.model, s.truth, s.stats = nil, nil, Stats{}
		return Unsat, nil
	}

//line cdcl.w:355
	par = s.Params
	if par.MemLog < 2 || par.MemLog > 31 || par.TrivialLimit <= 0 || par.Alpha < 0 ||
		par.Alpha > 1 || par.RandProb < 0 || par.TrueProb < 0 || par.VarRho <= 0 ||
		par.ClauseRho <= 0 {
		return Unknown, errors.New("sat: 매개변수가 범위를 벗어났다")
	}
	vars, clauses, cells = s.NumVars(), s.clauses, len(s.cells)
	rng = gbflip.New(int64(par.Seed))
	for k = 0; k < 736; k++ {
		rng.Next()
	}

//line cdcl.w:308

//line cdcl.w:493
	vmem = make([]variable, vars+1)
	bytes += uint64(vars+1) * 40
	for k = 1; k <= vars; k++ {
		mems++
		vmem[k].value = unset
		vmem[k].tloc = -1
//line cdcl.w:497
	}
	heap = make([]int, vars)
	bytes += uint64(vars) * 4

//line cdcl.w:505
	if par.TrueProb >= 1.0 {
		trueProbThresh = 0x80000000
	} else {
		trueProbThresh = int(float64(par.TrueProb) * 2147483648.0)
	}
	for k = 1; k <= vars; k++ {
		mems++
		heap[k-1] = k
//line cdcl.w:512
	}
	for hn = vars; hn > 1; {

//line cdcl.w:543
		t = 0x80000000 - 0x80000000%hn
		for {
			mems += 4
			r = int(rng.Next())
//line cdcl.w:546
			if r < t {
				break
			}
		}
		h = r % hn

//line cdcl.w:515
		hn--
		if h != hn {
			mems++
			k = heap[h]
//line cdcl.w:518
			mems += 3
			heap[h] = heap[hn]
			heap[hn] = k
//line cdcl.w:519
		}
	}

//line cdcl.w:524
	for h = 0; h < vars; h++ {
		mems++
		v = heap[h]
//line cdcl.w:526
		mems++
		vmem[v].hloc = h
//line cdcl.w:527
		vmem[v].oldval = 1
		if trueProbThresh != 0 {
			mems += 4
			if int(rng.Next()) < trueProbThresh {
				vmem[v].oldval = 0
			}
		}
		mems++
		vmem[v].activity = 0
//line cdcl.w:535
	}
	hn = vars

//line cdcl.w:565
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

//line cdcl.w:583
	maxLit = vars + vars + 1
	lmem = make([]literal, maxLit+1)
	bytes += uint64(maxLit+1) * 16
	trail = make([]int, vars)
	bytes += uint64(vars) * 4
	bmem = make([]uint32, 2*s.binaries)
	bytes += uint64(2*s.binaries)*4 + uint64(vars)

//line cdcl.w:607
	eptr = 0
	for l = 2; l <= maxLit; l++ {
		mems += 2
		lmem[l].reason = 0
		lmem[l].watch = 0
		lmem[l].bimpEnd = 0
//line cdcl.w:610
	}
	cur = cells
	for c, j, jj = clauseExtra, clauses, minLearned+2; j != 0; j-- {

//line cdcl.w:629
		for k = 0; ; {
			cur--
			i = int(s.cells[cur])
			mems++
			mem[c+k] = uint32(i &^ int(firstLit))
			k++
//line cdcl.w:633
			if i&int(firstLit) != 0 {
				break
			}
		}

//line cdcl.w:614
		if k <= 2 {

//line cdcl.w:644
			if k < 2 {
				l = int(mem[c])
				v = l >> 1
//line cdcl.w:646
				mems++
				if vmem[v].value == unset {
					mems++
					vmem[v].value = l & 1
					vmem[v].tloc = eptr
//line cdcl.w:649
					mems++
					trail[eptr] = l
					eptr++
//line cdcl.w:650
				} else if vmem[v].value != l&1 {
					goto unsat
				}
			} else {
				l, ll = int(mem[c]), int(mem[c+1])
				mems += 2
				lmem[l^1].bimpEnd++
//line cdcl.w:656
				mems += 2
				lmem[ll^1].bimpEnd++
//line cdcl.w:657
				mems++
				mem[jj] = uint32(l)
				mem[jj+1] = uint32(ll)
				jj += 2
//line cdcl.w:658
			}

//line cdcl.w:616
		} else {
			mems++
			mem[c-1] = uint32(k)
//line cdcl.w:618
			l = int(mem[c])
			mems += 3
			mem[c-2] = uint32(lmem[l].watch)
			lmem[l].watch = c
//line cdcl.w:620
			l = int(mem[c+1])
			mems += 3
			mem[c-3] = uint32(lmem[l].watch)
			lmem[l].watch = c
//line cdcl.w:622
			c += k + clauseExtra
		}
	}
	mems++
	mem[c-clauseExtra] = 0

//line cdcl.w:664
	for l, jj = 2, 0; l <= maxLit; l++ {
		mems++
		k = lmem[l].bimpEnd
//line cdcl.w:666
		if k != 0 {
			mems++
			lmem[l].bimpStart = jj
			lmem[l].bimpEnd = jj
			jj += k
//line cdcl.w:668
		}
	}
	for jj, j = minLearned+2, s.binaries; j != 0; j-- {
		mems++
		l = int(mem[jj])
		ll = int(mem[jj+1])
		jj += 2
//line cdcl.w:672
		mems += 3
		k = lmem[l^1].bimpEnd
		bmem[k] = uint32(ll)
		lmem[l^1].bimpEnd = k + 1
//line cdcl.w:673
		mems += 3
		k = lmem[ll^1].bimpEnd
		bmem[k] = uint32(l)
		lmem[ll^1].bimpEnd = k + 1
//line cdcl.w:674
	}

//line cdcl.w:680
	for c = vars; c != 0; c-- {
		mems += 2
		vmem[c].stamp = 0
//line cdcl.w:682
	}

//line cdcl.w:689
	leveldat = make([]int, 2*vars+4)
	learn = make([]int, vars)
	stack = make([]int, 2*vars+4)
	conflictdat = make([]int, 2*vars+4)
	levstamp = make([]int, 2*vars+4)
	bytes += uint64(vars)*(8+4+8+8+8) + buckets*4
	for k = 0; k < vars; k++ {
		mems++
		levstamp[k+k] = 0
//line cdcl.w:697
	}
	rangedist = make([]int, buckets)
	for k = 0; k+k < buckets; k++ {
		mems++
		rangedist[k+k] = 0
		rangedist[k+k+1] = 0
//line cdcl.w:701
	}
	clauseHeapSize = int(par.RecycleBump >> 1)
	clauseHeap = make([]uint64, clauseHeapSize)
	bytes += uint64(clauseHeapSize) * 8

//line cdcl.w:309
	imems, mems = mems, 0

//line cdcl.w:2015
	if par.RandProb >= 1.0 {
		randProbThresh = 0x80000000
	} else {
		randProbThresh = int(float64(par.RandProb) * 2147483648.0)
	}
	varBumpFactor = 1.0 / float64(par.VarRho)
	clauseBumpFactor = float32(1.0 / float64(par.ClauseRho))
	recycleBump = par.RecycleBump
	nextRecycle = min(recycleBump, par.Doomsday)
	restartPsi = uint64(4294967296.0 * float64(par.RestartPsiFraction))
	restartU, restartV, nextRestart = 1, 1, 1
	nextCheck = checkEvery
	for k = 0; k < vars; k++ {
		mems++
		leveldat[k+k] = -1
		leveldat[k+k+1] = 0
//line cdcl.w:2029
	}

//line cdcl.w:1945
	llevel, warmupCycles, lptr = 0, 0, 0
startup:
	conflictLevel = 0
	fullRun = warmupCycles < par.Warmups
proceed:
	conflictSeen = false

//line cdcl.w:2036
	ebptr = eptr
	for lptr < eptr {
		mems++
		lt = trail[lptr]
		lptr++
//line cdcl.w:2039
		if lptr <= ebptr {
			mems++
			lat = lmem[lt].bimpEnd
//line cdcl.w:2041
			if lat != 0 {
				l = lt

//line cdcl.w:720
				for lbptr = eptr; ; {
					for la = lmem[l].bimpStart; la < lat; la++ {
						mems++
						ll = int(bmem[la])
//line cdcl.w:723
						mems++
						if vmem[ll>>1].value != unset {
							if (vmem[ll>>1].value^ll)&1 != 0 {

//line cdcl.w:887
								if fullRun && llevel != 0 {
									if !conflictSeen {
										conflictSeen = true
										mems++
										leveldat[llevel+1] = -l
//line cdcl.w:891
										mems++
										conflictdat[llevel+1] = ll
//line cdcl.w:892
										conflictdat[llevel] = conflictLevel
										conflictLevel = llevel
//line cdcl.w:893
									}
								} else {
									c = -l
									goto confl
								}

//line cdcl.w:727
							}
						} else {

//line cdcl.w:753
							mems++
							trail[eptr] = ll
//line cdcl.w:754
							mems++
							lmem[ll].reason = -l
//line cdcl.w:755
							mems++
							vmem[ll>>1].value = llevel + ll&1
							vmem[ll>>1].tloc = eptr
							eptr++
//line cdcl.w:756
							agility -= agility >> 13
							mems++
							if (vmem[ll>>1].oldval+ll)&1 != 0 {
								agility += 1 << 19
							}

//line cdcl.w:730
						}
					}
					for {
						if lbptr == eptr {
							l = 0
							break
						}
						mems++
						l = trail[lbptr]
						lbptr++
//line cdcl.w:738
						mems++
						lat = lmem[l].bimpEnd
//line cdcl.w:739
						if lat != 0 {
							break
						}
					}
					if l == 0 {
						break
					}
				}

//line cdcl.w:2044
			}
		}

//line cdcl.w:779
		mems++
		wa = lmem[lt^1].watch
//line cdcl.w:780
		if wa != 0 {
			for q = 0; wa != 0; wa = nextWa {

//line cdcl.w:795
				mems++
				ll = int(mem[wa])
//line cdcl.w:796
				if ll == lt^1 {
					mems++
					ll = int(mem[wa+1])
//line cdcl.w:798
					mems += 2
					mem[wa] = uint32(ll)
					mem[wa+1] = uint32(lt ^ 1)
//line cdcl.w:799
					mems++
					nextWa = int(mem[wa-2])
//line cdcl.w:800
					mems++
					mem[wa-2] = mem[wa-3]
					mem[wa-3] = uint32(nextWa)
//line cdcl.w:801
				} else {
					mems++
					nextWa = int(mem[wa-3])
//line cdcl.w:803
				}

//line cdcl.w:783

//line cdcl.w:809
				mems++
				if vmem[ll>>1].value != unset && (vmem[ll>>1].value^ll)&1 == 0 {

//line cdcl.w:821
					if q == 0 {
						mems++
						lmem[lt^1].watch = wa
//line cdcl.w:823
					} else {
						mems++
						mem[q-3] = uint32(wa)
//line cdcl.w:825
					}
					q = wa

//line cdcl.w:812
					continue
				}

//line cdcl.w:784

//line cdcl.w:833
				mems++
				sz = int(mem[wa-1])
//line cdcl.w:834
				for j = wa + sz - 1; j > wa+1; j-- {
					mems++
					l = int(mem[j])
//line cdcl.w:836
					mems++
					if vmem[l>>1].value == unset || (vmem[l>>1].value^l)&1 == 0 {
						break
					}
					if vmem[l>>1].value < 2 && llevel != 0 {

//line cdcl.w:846
						mems++
						sz--
						mem[wa-1] = uint32(sz)
//line cdcl.w:847
						if j != wa+sz {
							mems += 2
							mem[j] = mem[wa+sz]
//line cdcl.w:849
						}
						mems++
						mem[wa+sz] = uint32(l) + signBit

//line cdcl.w:842
					}
				}

//line cdcl.w:785
				if j > wa+1 {

//line cdcl.w:853
					mems += 2
					mem[wa+1] = uint32(l)
					mem[j] = uint32(lt ^ 1)
//line cdcl.w:854
					mems++
					mem[wa-3] = uint32(lmem[l].watch)
//line cdcl.w:855
					mems++
					lmem[l].watch = wa
//line cdcl.w:856
					continue

//line cdcl.w:787
				}

//line cdcl.w:821
				if q == 0 {
					mems++
					lmem[lt^1].watch = wa
//line cdcl.w:823
				} else {
					mems++
					mem[q-3] = uint32(wa)
//line cdcl.w:825
				}
				q = wa

//line cdcl.w:789

//line cdcl.w:863
				if vmem[ll>>1].value != unset {

//line cdcl.w:900
					if fullRun && llevel != 0 {
						if !conflictSeen {
							conflictSeen = true
							mems++
							leveldat[llevel+1] = wa
//line cdcl.w:904
							mems++
							conflictdat[llevel] = conflictLevel
							conflictLevel = llevel
//line cdcl.w:905
						}
					} else {
						c = wa
						goto confl
					}

//line cdcl.w:865
				} else {
					mems++
					trail[eptr] = ll
//line cdcl.w:867
					mems++
					vmem[ll>>1].tloc = eptr
					eptr++
//line cdcl.w:868
					vmem[ll>>1].value = llevel + ll&1
					agility -= agility >> 13
					mems++
					if (vmem[ll>>1].oldval+ll)&1 != 0 {
						agility += 1 << 19
					}
					mems++
					lmem[ll].reason = wa
//line cdcl.w:875
					mems++
					lat = lmem[ll].bimpEnd
//line cdcl.w:876
					if lat != 0 {
						l = ll

//line cdcl.w:720
						for lbptr = eptr; ; {
							for la = lmem[l].bimpStart; la < lat; la++ {
								mems++
								ll = int(bmem[la])
//line cdcl.w:723
								mems++
								if vmem[ll>>1].value != unset {
									if (vmem[ll>>1].value^ll)&1 != 0 {

//line cdcl.w:887
										if fullRun && llevel != 0 {
											if !conflictSeen {
												conflictSeen = true
												mems++
												leveldat[llevel+1] = -l
//line cdcl.w:891
												mems++
												conflictdat[llevel+1] = ll
//line cdcl.w:892
												conflictdat[llevel] = conflictLevel
												conflictLevel = llevel
//line cdcl.w:893
											}
										} else {
											c = -l
											goto confl
										}

//line cdcl.w:727
									}
								} else {

//line cdcl.w:753
									mems++
									trail[eptr] = ll
//line cdcl.w:754
									mems++
									lmem[ll].reason = -l
//line cdcl.w:755
									mems++
									vmem[ll>>1].value = llevel + ll&1
									vmem[ll>>1].tloc = eptr
									eptr++
//line cdcl.w:756
									agility -= agility >> 13
									mems++
									if (vmem[ll>>1].oldval+ll)&1 != 0 {
										agility += 1 << 19
									}

//line cdcl.w:730
								}
							}
							for {
								if lbptr == eptr {
									l = 0
									break
								}
								mems++
								l = trail[lbptr]
								lbptr++
//line cdcl.w:738
								mems++
								lat = lmem[l].bimpEnd
//line cdcl.w:739
								if lat != 0 {
									break
								}
							}
							if l == 0 {
								break
							}
						}

//line cdcl.w:879
					}
				}

//line cdcl.w:790
			}

//line cdcl.w:821
			if q == 0 {
				mems++
				lmem[lt^1].watch = wa
//line cdcl.w:823
			} else {
				mems++
				mem[q-3] = uint32(wa)
//line cdcl.w:825
			}
			q = wa

//line cdcl.w:792
		}

//line cdcl.w:2047
	}

//line cdcl.w:1952

//line cdcl.w:1999
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

//line cdcl.w:1953
	if eptr == vars {
		if conflictLevel == 0 {
			goto satisfied
		}
		goto finishFull
	}
	if conflictLevel == 0 {

//line cdcl.w:1970
		if totalLearned >= par.Doomsday {
			err = ErrDoomsday
			goto allDone
		}
		if totalLearned >= nextRecycle {
			fullRun = true
		} else if totalLearned >= nextRestart {

//line cdcl.w:2192
			if restartU&-restartU == restartV {
				restartU++
				restartV = 1
				restartThresh = restartPsi
//line cdcl.w:2194
			} else {
				restartV <<= 1
				restartThresh += restartThresh >> 4
//line cdcl.w:2196
			}
			nextRestart = min(totalLearned+uint64(restartV), par.Doomsday)
			if uint64(agility) <= restartThresh {

//line cdcl.w:2209
				actualRestarts++
				if llevel != 0 {
					for {
						mems++
						v = heap[0]
//line cdcl.w:2213
						mems++
						if vmem[v].value == unset {
							break
						}

//line cdcl.w:988
						mems++
						vmem[v].hloc = -1
//line cdcl.w:989
						hn--
						if hn != 0 {
							mems++
							u = heap[hn]
//line cdcl.w:992
							mems++
							au = vmem[u].activity
//line cdcl.w:993
							for h, hp = 0, 1; hp < hn; h, hp = hp, 2*hp+1 {

//line cdcl.w:1006
								mems += 2
								av = vmem[heap[hp]].activity
//line cdcl.w:1007
								if hp+1 < hn {
									mems += 2
									if vmem[heap[hp+1]].activity > av {
										hp++
										av = vmem[heap[hp]].activity
//line cdcl.w:1011
									}
								}

//line cdcl.w:995
								if au >= av {
									break
								}
								mems++
								heap[h] = heap[hp]
//line cdcl.w:999
								mems++
								vmem[heap[hp]].hloc = h
//line cdcl.w:1000
							}
							mems++
							heap[h] = u
//line cdcl.w:1002
							mems++
							vmem[u].hloc = h
//line cdcl.w:1003
						}

//line cdcl.w:2218
					}
					mems++
					av = vmem[v].activity
//line cdcl.w:2220
					for jumplev = 0; jumplev < llevel; jumplev += 2 {
						mems += 2
						v = trail[leveldat[jumplev+2]] >> 1
//line cdcl.w:2222
						mems++
						if vmem[v].activity < av {
							break
						}
					}
					if jumplev < llevel {

//line cdcl.w:2054
						mems++
						k = leveldat[jumplev+2]
//line cdcl.w:2055
						for eptr > k {
							eptr--
							mems++
							l = trail[eptr]
							v = l >> 1
//line cdcl.w:2057
							mems += 2
							vmem[v].oldval = vmem[v].value
//line cdcl.w:2058
							mems++
							vmem[v].value = unset
//line cdcl.w:2059
							mems++
							lmem[l].reason = 0
//line cdcl.w:2060
							if eptr < lptr {
								mems++
								if vmem[v].hloc < 0 {

//line cdcl.w:975
									mems++
									av = vmem[v].activity
//line cdcl.w:976
									h = hn
									hn++
									j = 0
//line cdcl.w:977
									if h > 0 {

//line cdcl.w:951
										hp = (h - 1) >> 1
										mems++
										u = heap[hp]
//line cdcl.w:953
										mems++
										if vmem[u].activity < av {
											for {
												mems++
												heap[h] = u
//line cdcl.w:957
												mems++
												vmem[u].hloc = h
//line cdcl.w:958
												h = hp
												if h == 0 {
													break
												}
												hp = (h - 1) >> 1
												mems++
												u = heap[hp]
//line cdcl.w:964
												mems++
												if vmem[u].activity >= av {
													break
												}
											}
											mems++
											heap[h] = v
//line cdcl.w:970
											mems++
											vmem[v].hloc = h
//line cdcl.w:971
											j = 1
										}

//line cdcl.w:979
									}
									if j == 0 {
										mems += 2
										heap[h] = v
										vmem[v].hloc = h
//line cdcl.w:982
									}

//line cdcl.w:2064
								}
							}
						}
						lptr = eptr
						llevel = jumplev

//line cdcl.w:2229
					}
				}
				warmupCycles = 0
				goto startup

//line cdcl.w:2200
			}

//line cdcl.w:1978
		}

//line cdcl.w:1961
	}

//line cdcl.w:1984
	llevel += 2

//line cdcl.w:1021
	h = 0
	if randProbThresh != 0 {
		mems += 4
		h = int(rng.Next())
//line cdcl.w:1024
		if h < randProbThresh {

//line cdcl.w:543
			t = 0x80000000 - 0x80000000%hn
			for {
				mems += 4
				r = int(rng.Next())
//line cdcl.w:546
				if r < t {
					break
				}
			}
			h = r % hn

//line cdcl.w:1026
			mems++
			v = heap[h]
//line cdcl.w:1027
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
			mems++
			v = heap[0]
//line cdcl.w:1038

//line cdcl.w:988
			mems++
			vmem[v].hloc = -1
//line cdcl.w:989
			hn--
			if hn != 0 {
				mems++
				u = heap[hn]
//line cdcl.w:992
				mems++
				au = vmem[u].activity
//line cdcl.w:993
				for h, hp = 0, 1; hp < hn; h, hp = hp, 2*hp+1 {

//line cdcl.w:1006
					mems += 2
					av = vmem[heap[hp]].activity
//line cdcl.w:1007
					if hp+1 < hn {
						mems += 2
						if vmem[heap[hp+1]].activity > av {
							hp++
							av = vmem[heap[hp]].activity
//line cdcl.w:1011
						}
					}

//line cdcl.w:995
					if au >= av {
						break
					}
					mems++
					heap[h] = heap[hp]
//line cdcl.w:999
					mems++
					vmem[heap[hp]].hloc = h
//line cdcl.w:1000
				}
				mems++
				heap[h] = u
//line cdcl.w:1002
				mems++
				vmem[u].hloc = h
//line cdcl.w:1003
			}

//line cdcl.w:1039
			mems++
			if vmem[v].value == unset {
				break
			}
		}
	}
	mems++
	l = v + v + vmem[v].oldval&1

//line cdcl.w:1986
	mems++
	lmem[l].reason = 0
//line cdcl.w:1987
	nodes++
	mems++
	leveldat[llevel] = eptr
//line cdcl.w:1989
	mems++
	trail[eptr] = l
	eptr++
//line cdcl.w:1990
	mems++
	vmem[l>>1].tloc = lptr
//line cdcl.w:1991
	vmem[l>>1].value = llevel + l&1
	agility -= agility >> 13

//line cdcl.w:1963
	goto proceed

//line cdcl.w:2106
finishFull:
	if totalLearned >= nextRecycle {

//line cdcl.w:1726
		recyclePoint = maxLearned
		minrange, maxrange = buckets, 0
		asserts = 0
		for k = 0; k < vars; k++ {
			mems++
			levstamp[k+k+1] = 0
//line cdcl.w:1731
		}
		for h, c = 0, firstLearned; c < maxLearned; h, c = h+1, endc+learnedExtra {
			mems++
			endc = c + int(mem[c-1])
//line cdcl.w:1734

//line cdcl.w:1674
			mems++
			l = int(mem[c])
//line cdcl.w:1675
			mems++
			if lmem[l].reason == c {
				mems++
				if vmem[l>>1].value&^1 != 0 {
					mems++
					mem[c-4] = 0
					asserts++
//line cdcl.w:1680
				} else {
					v = buckets + 1
					mems++
					mem[c-4] = buckets + 1
//line cdcl.w:1683
					goto rangeSet
				}
			} else {

//line cdcl.w:1700
				p, q = 0, 0
				for k = c + int(mem[c-1]) - 1; k >= c; k-- {
					mems += 2
					l = int(mem[k])
					v = vmem[l>>1].value
//line cdcl.w:1703
					if v < 2 {
						if (v^l)&1 != 0 {
							continue
						}
						v = buckets + 1
						mems++
						mem[c-4] = buckets + 1
//line cdcl.w:1709
						goto rangeSet
					}
					mems++
					if levstamp[(v&^1)+1] < c {
						mems++
						levstamp[(v&^1)+1] = c
						q++
//line cdcl.w:1714
					}
					if levstamp[(v&^1)+1] == c && (l^v)&1 == 0 {
						mems++
						levstamp[(v&^1)+1] = c + 1
						p++
//line cdcl.w:1717
					}
				}

//line cdcl.w:1687
				v = int(buckets / badlevel * float64(float32(p)+float32(par.Alpha*float32(q-p))))
				if v >= buckets {
					v = buckets - 1
				}
				mems++
				mem[c-4] = uint32(v)
//line cdcl.w:1692
				minrange, maxrange = min(minrange, v), max(maxrange, v)
				mems += 2
				rangedist[v]++
//line cdcl.w:1694
			}
		rangeSet:

//line cdcl.w:1735

//line cdcl.w:1743
			for {
				mems++
				if mem[endc]&signBit == 0 {
					break
				}
				endc++
			}

//line cdcl.w:1736
		}
		budget = h / 2
		prevLearned = 0

//line cdcl.w:2109
	} else {
		warmupCycles++
	}
	mems++
	leveldat[llevel+2] = eptr
//line cdcl.w:2113
	minjumplev = maxLit
learnFull:
	if conflictLevel == 0 {
		goto learnedFull
	}
	mems++
	jumplev = conflictLevel
	conflictLevel = conflictdat[conflictLevel]
//line cdcl.w:2119

//line cdcl.w:2054
	mems++
	k = leveldat[jumplev+2]
//line cdcl.w:2055
	for eptr > k {
		eptr--
		mems++
		l = trail[eptr]
		v = l >> 1
//line cdcl.w:2057
		mems += 2
		vmem[v].oldval = vmem[v].value
//line cdcl.w:2058
		mems++
		vmem[v].value = unset
//line cdcl.w:2059
		mems++
		lmem[l].reason = 0
//line cdcl.w:2060
		if eptr < lptr {
			mems++
			if vmem[v].hloc < 0 {

//line cdcl.w:975
				mems++
				av = vmem[v].activity
//line cdcl.w:976
				h = hn
				hn++
				j = 0
//line cdcl.w:977
				if h > 0 {

//line cdcl.w:951
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:953
					mems++
					if vmem[u].activity < av {
						for {
							mems++
							heap[h] = u
//line cdcl.w:957
							mems++
							vmem[u].hloc = h
//line cdcl.w:958
							h = hp
							if h == 0 {
								break
							}
							hp = (h - 1) >> 1
							mems++
							u = heap[hp]
//line cdcl.w:964
							mems++
							if vmem[u].activity >= av {
								break
							}
						}
						mems++
						heap[h] = v
//line cdcl.w:970
						mems++
						vmem[v].hloc = h
//line cdcl.w:971
						j = 1
					}

//line cdcl.w:979
				}
				if j == 0 {
					mems += 2
					heap[h] = v
					vmem[v].hloc = h
//line cdcl.w:982
				}

//line cdcl.w:2064
			}
		}
	}
	lptr = eptr
	llevel = jumplev

//line cdcl.w:2120
	mems++
	c = leveldat[llevel+1]
//line cdcl.w:2121
	if c < 0 {
		mems++
		l = -c
		ll = conflictdat[llevel+1]
//line cdcl.w:2123
	}
	goto prepClause
storeClause:

//line cdcl.w:2137
	if trivialLearning && conflictLevel != 0 {
		cellsPrelearned -= float64(prelearnedSize)
		cellsLearned -= float64(learnedSize)
		totalLearned--
		trivials--
//line cdcl.w:2140
	} else {
		if jumplev <= minjumplev {
			if jumplev < minjumplev {
				minjumplev = jumplev
				nextLearned = 0
//line cdcl.w:2144
			}
			mems++
			conflictdat[llevel] = nextLearned
			conflictdat[llevel+1] = lll
//line cdcl.w:2146
			nextLearned = llevel
		}
		if learnedSize == 1 {
			mems++
			leveldat[llevel+1] = 0
//line cdcl.w:2150
		} else {

//line cdcl.w:1534
			if prevLearned != 0 {
				mems++
				l = int(mem[prevLearned])
//line cdcl.w:1536
				if !trivialLearning {
					mems++
					if lmem[l].reason == 0 {
						mems++
						if vmem[l>>1].value == unset {

//line cdcl.w:1565
							mems++
							for k, q = int(mem[prevLearned-1])-1, learnedSize; q != 0 && k >= q; k-- {
								mems += 2
								l = int(mem[prevLearned+k])
								r = vmem[l>>1].value &^ 1
//line cdcl.w:1568
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
								c = prevLearned
								mems++
								mem[c-5] = 0
//line cdcl.w:1579
								mems++
								l = int(mem[c])
								r = int(mem[c-2])
//line cdcl.w:1580

//line cdcl.w:1327
								mems++
								for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
									mems++
									p = int(mem[wa])
//line cdcl.w:1330
									mems++
									if p == l {
										nextWa = int(mem[wa-2])
									} else {
										nextWa = int(mem[wa-3])
									}
								}
								if q == 0 {
									mems++
									lmem[l].watch = r
//line cdcl.w:1339
								} else if p == l {
									mems++
									mem[q-2] = uint32(r)
//line cdcl.w:1341
								} else {
									mems++
									mem[q-3] = uint32(r)
//line cdcl.w:1343
								}

//line cdcl.w:1581
								mems += 2
								l = int(mem[c+1])
								r = int(mem[c-3])
//line cdcl.w:1582

//line cdcl.w:1327
								mems++
								for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
									mems++
									p = int(mem[wa])
//line cdcl.w:1330
									mems++
									if p == l {
										nextWa = int(mem[wa-2])
									} else {
										nextWa = int(mem[wa-3])
									}
								}
								if q == 0 {
									mems++
									lmem[l].watch = r
//line cdcl.w:1339
								} else if p == l {
									mems++
									mem[q-2] = uint32(r)
//line cdcl.w:1341
								} else {
									mems++
									mem[q-3] = uint32(r)
//line cdcl.w:1343
								}

//line cdcl.w:1583
							}

//line cdcl.w:1542
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

//line cdcl.w:595
				if maxCellsUsed > len(mem) {
					grown := make([]uint32, min(memsize, max(2*len(mem), maxCellsUsed)))
					copy(grown, mem)
					mem = grown
				}

//line cdcl.w:1556
			}
			mems++
			mem[c+learnedSize] = 0

//line cdcl.w:1590
			if mem[c-5] != 0 {
				panic("sat: 이럴 수는 없다 (bumps)")
			}
			mem[c-1] = uint32(learnedSize)
			mems++
			mem[c] = uint32(lll)
//line cdcl.w:1595
			mems += 2
			mem[c-2] = uint32(lmem[lll].watch)
//line cdcl.w:1596
			mems++
			lmem[lll].watch = c
//line cdcl.w:1597
			if trivialLearning {
				for j, k = 1, jumplev; k != 0; j, k = j+1, k-2 {
					mems += 2
					l = trail[leveldat[k]] ^ 1
//line cdcl.w:1600
					if j == 1 {
						mems += 3
						mem[c-3] = uint32(lmem[l].watch)
						lmem[l].watch = c
//line cdcl.w:1602
					}
					mems++
					mem[c+j] = uint32(l)
//line cdcl.w:1604
				}
			} else {

//line cdcl.w:1610
				for k, j, jj = 1, 0, 1; k < learnedSize; j++ {
					mems++
					l = learn[j]
//line cdcl.w:1612
					mems++
					if vmem[l>>1].stamp == curstamp {
						mems++
						r = vmem[l>>1].value
//line cdcl.w:1615
						if jj != 0 && r >= jumplev {
							mems++
							mem[c+1] = uint32(l)
//line cdcl.w:1617
							mems += 2
							mem[c-3] = uint32(lmem[l].watch)
//line cdcl.w:1618
							mems++
							lmem[l].watch = c
//line cdcl.w:1619
							jj = 0
						} else {
							mems++
							mem[c+k+jj] = uint32(l)
//line cdcl.w:1622
						}
						k++
					}
				}

//line cdcl.w:1607
			}

//line cdcl.w:1524
			prevLearned = c

//line cdcl.w:2152
			mems++
			leveldat[llevel+1] = c
//line cdcl.w:2153
		}
	}

//line cdcl.w:2127
	goto learnFull
learnedFull:

//line cdcl.w:2159
	if recyclePoint != 0 {
		jumplev = 0
	} else {
		jumplev = minjumplev
	}

//line cdcl.w:2054
	mems++
	k = leveldat[jumplev+2]
//line cdcl.w:2055
	for eptr > k {
		eptr--
		mems++
		l = trail[eptr]
		v = l >> 1
//line cdcl.w:2057
		mems += 2
		vmem[v].oldval = vmem[v].value
//line cdcl.w:2058
		mems++
		vmem[v].value = unset
//line cdcl.w:2059
		mems++
		lmem[l].reason = 0
//line cdcl.w:2060
		if eptr < lptr {
			mems++
			if vmem[v].hloc < 0 {

//line cdcl.w:975
				mems++
				av = vmem[v].activity
//line cdcl.w:976
				h = hn
				hn++
				j = 0
//line cdcl.w:977
				if h > 0 {

//line cdcl.w:951
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:953
					mems++
					if vmem[u].activity < av {
						for {
							mems++
							heap[h] = u
//line cdcl.w:957
							mems++
							vmem[u].hloc = h
//line cdcl.w:958
							h = hp
							if h == 0 {
								break
							}
							hp = (h - 1) >> 1
							mems++
							u = heap[hp]
//line cdcl.w:964
							mems++
							if vmem[u].activity >= av {
								break
							}
						}
						mems++
						heap[h] = v
//line cdcl.w:970
						mems++
						vmem[v].hloc = h
//line cdcl.w:971
						j = 1
					}

//line cdcl.w:979
				}
				if j == 0 {
					mems += 2
					heap[h] = v
					vmem[v].hloc = h
//line cdcl.w:982
				}

//line cdcl.w:2064
			}
		}
	}
	lptr = eptr
	llevel = jumplev

//line cdcl.w:2165
	if jumplev == minjumplev {

//line cdcl.w:2176
		for nextLearned != 0 {
			mems++
			lll = conflictdat[nextLearned+1]
//line cdcl.w:2178
			mems++
			c = leveldat[nextLearned+1]
//line cdcl.w:2179
			nextLearned = conflictdat[nextLearned]
			mems++
			vmem[lll>>1].value = llevel + lll&1
			vmem[lll>>1].tloc = eptr
//line cdcl.w:2181
			mems++
			lmem[lll].reason = c
//line cdcl.w:2182
			mems++
			trail[eptr] = lll
			eptr++
//line cdcl.w:2183
		}

//line cdcl.w:2167
	}

//line cdcl.w:1092
	varBump *= varBumpFactor
	clauseBump *= clauseBumpFactor

//line cdcl.w:2169
	if recyclePoint != 0 {

//line cdcl.w:1760
		mems++
		j = minrange
		sz = asserts + rangedist[j]
//line cdcl.w:1761
		for sz < budget && j < maxrange {
			j++
			mems++
			sz += rangedist[j]
//line cdcl.w:1763
		}
		if sz > budget {

//line cdcl.w:1816
			t = sz - budget
			jj = min(rangedist[j]-t, clauseHeapSize)

//line cdcl.w:1827
			for h, c = 0, firstLearned; h < jj; c = endc + learnedExtra {
				if c >= recyclePoint {
					panic("sat: 이럴 수는 없다 (rangedist1)")
				}
				mems++
				endc = c + int(mem[c-1])
//line cdcl.w:1832

//line cdcl.w:1743
				for {
					mems++
					if mem[endc]&signBit == 0 {
						break
					}
					endc++
				}

//line cdcl.w:1833
				mems++
				if int(mem[c-4]) == j {
					clauseHeap[h] = uint64(mem[c-5])<<32 + uint64(c)
					h++
//line cdcl.w:1836
				}
			}

//line cdcl.w:1840
			for h = jj >> 1; h != 0; {
				q = h + h
				h--
				p = h
//line cdcl.w:1842
				mems++
				accum = clauseHeap[p]
//line cdcl.w:1843

//line cdcl.w:1849
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
					mems++
					clauseHeap[p] = clauseHeap[q]
//line cdcl.w:1862
					p, q = q, q+q+2
				}
				mems++
				clauseHeap[p] = accum

//line cdcl.w:1844
			}

//line cdcl.w:1870
			for ; ; c = endc + learnedExtra {
				if c >= recyclePoint {
					panic("sat: 이럴 수는 없다 (rangedist2)")
				}
				mems++
				if int(mem[c-4]) == j {
					mems++
					accum = uint64(mem[c-5])<<32 + uint64(c)
//line cdcl.w:1877
					mems++
					if accum < clauseHeap[0] {
						mems++
						mem[c-4] = uint32(j + 1)
//line cdcl.w:1880
						if t--; t == 0 {
							break
						}
					} else {
						mems++
						mem[int(clauseHeap[0]&0xffffffff)-4] = uint32(j + 1)
//line cdcl.w:1885
						if t--; t == 0 {
							break
						}
						p, q = 0, 2

//line cdcl.w:1849
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
							mems++
							clauseHeap[p] = clauseHeap[q]
//line cdcl.w:1862
							p, q = q, q+q+2
						}
						mems++
						clauseHeap[p] = accum

//line cdcl.w:1890
					}
				}
				mems++
				endc = c + int(mem[c-1])
//line cdcl.w:1893

//line cdcl.w:1743
				for {
					mems++
					if mem[endc]&signBit == 0 {
						break
					}
					endc++
				}

//line cdcl.w:1894
			}

//line cdcl.w:1766
		}
		for k = minrange >> 1; k+k <= maxrange; k++ {
			mems++
			rangedist[k+k] = 0
			rangedist[k+k+1] = 0
//line cdcl.w:1769
		}
		for h, cc, c = 0, firstLearned, firstLearned; c < maxLearned; c = endc + learnedExtra {

//line cdcl.w:1780
			mems++
			endc = c + int(mem[c-1])
			jj = endc
//line cdcl.w:1781
			for {
				mems++
				if mem[endc]&signBit == 0 {
					break
				}
				mems++
				mem[endc] = 0
				endc++
//line cdcl.w:1787
			}
			if c < recyclePoint {
				mems++
				if int(mem[c-4]) > j {
					continue
				}
			}
			for kk, k = cc, c; k < jj; k++ {
				mems++
				l = int(mem[k])
//line cdcl.w:1796
				mems++
				v = vmem[l>>1].value
//line cdcl.w:1797
				if v != unset {
					if (v^l)&1 != 0 {
						continue
					}
					break
				}
				mems++
				mem[kk] = uint32(l)
				kk++
//line cdcl.w:1804
			}
			if k < jj {
				continue
			}
			h++

//line cdcl.w:1902
			if kk >= cc+2 {
				mems += 3
				mem[cc-1] = uint32(kk - cc)
				mem[cc-5] = mem[c-5]
				cc = kk + learnedExtra
//line cdcl.w:1904
			} else if kk == cc {
				goto unsat
			} else {
				mems++
				l = int(mem[cc])
//line cdcl.w:1908
				mems++
				vmem[l>>1].value = l & 1
				vmem[l>>1].tloc = eptr
//line cdcl.w:1909
				mems++
				trail[eptr] = l
				eptr++
//line cdcl.w:1910
			}

//line cdcl.w:1772
		}
		maxLearned = cc
		prevLearned = 0
//line cdcl.w:1774
		mems++
		mem[maxLearned-learnedExtra] = 0

//line cdcl.w:1917
		for l = 2; l <= maxLit; l++ {
			mems++
			lmem[l].watch = 0
//line cdcl.w:1919
		}
		for c = clauseExtra; c < minLearned; c = endc + clauseExtra {
			mems++
			endc = c + int(mem[c-1])
//line cdcl.w:1922

//line cdcl.w:1931
			mems++
			l = int(mem[c])
//line cdcl.w:1932
			mems += 3
			mem[c-2] = uint32(lmem[l].watch)
			lmem[l].watch = c
//line cdcl.w:1933
			l = int(mem[c+1])
			mems += 3
			mem[c-3] = uint32(lmem[l].watch)
			lmem[l].watch = c

//line cdcl.w:1923

//line cdcl.w:1743
			for {
				mems++
				if mem[endc]&signBit == 0 {
					break
				}
				endc++
			}

//line cdcl.w:1924
		}
		for c = firstLearned; c < maxLearned; c = endc + learnedExtra {
			mems++
			endc = c + int(mem[c-1])
//line cdcl.w:1927

//line cdcl.w:1931
			mems++
			l = int(mem[c])
//line cdcl.w:1932
			mems += 3
			mem[c-2] = uint32(lmem[l].watch)
			lmem[l].watch = c
//line cdcl.w:1933
			l = int(mem[c+1])
			mems += 3
			mem[c-3] = uint32(lmem[l].watch)
			lmem[l].watch = c

//line cdcl.w:1928
		}

//line cdcl.w:1754
		recyclePoint = 0

//line cdcl.w:2171
		recycleBump += par.RecycleInc
		nextRecycle = min(totalLearned+recycleBump, par.Doomsday)
	}

//line cdcl.w:2130
	goto startup

//line cdcl.w:2076
confl:
	if llevel == 0 {
		goto unsat
	}
prepClause:

//line cdcl.w:1132
	oldptr, jumplev, xnew, clevels = 0, 0, 0, 0

//line cdcl.w:1189
	if curstamp >= 0xfffffffe {
		for k = 1; k <= vars; k++ {
			mems += 2
			vmem[k].stamp = 0
			levstamp[k+k-2] = 0
//line cdcl.w:1192
		}
		curstamp = 1
	} else {
		curstamp += 3
	}

//line cdcl.w:1134
	if c < 0 {

//line cdcl.w:1173
		mems++
		tl = vmem[ll>>1].tloc
//line cdcl.w:1174
		mems++
		vmem[ll>>1].stamp = curstamp
//line cdcl.w:1175
		l = ll

//line cdcl.w:935
		v = l >> 1
		mems++
		av = vmem[v].activity + varBump
//line cdcl.w:937
		mems++
		vmem[v].activity = av
//line cdcl.w:938
		if av >= 1e100 {

//line cdcl.w:1053
			for vv := 1; vv <= vars; vv++ {
				mems++
				a := vmem[vv].activity
//line cdcl.w:1055
				if a != 0 {
					mems++
					vmem[vv].activity = max(a*1e-100, tiny)
//line cdcl.w:1057
				}
			}
			varBump *= 1e-100

//line cdcl.w:940
		}
		mems++
		h = vmem[v].hloc
//line cdcl.w:942
		if h > 0 {

//line cdcl.w:951
			hp = (h - 1) >> 1
			mems++
			u = heap[hp]
//line cdcl.w:953
			mems++
			if vmem[u].activity < av {
				for {
					mems++
					heap[h] = u
//line cdcl.w:957
					mems++
					vmem[u].hloc = h
//line cdcl.w:958
					h = hp
					if h == 0 {
						break
					}
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:964
					mems++
					if vmem[u].activity >= av {
						break
					}
				}
				mems++
				heap[h] = v
//line cdcl.w:970
				mems++
				vmem[v].hloc = h
//line cdcl.w:971
				j = 1
			}

//line cdcl.w:944
		}

//line cdcl.w:1177
		l = -c
		mems++
		if vmem[l>>1].tloc > tl {
			tl = vmem[l>>1].tloc
		}
		mems++
		vmem[l>>1].stamp = curstamp

//line cdcl.w:935
		v = l >> 1
		mems++
		av = vmem[v].activity + varBump
//line cdcl.w:937
		mems++
		vmem[v].activity = av
//line cdcl.w:938
		if av >= 1e100 {

//line cdcl.w:1053
			for vv := 1; vv <= vars; vv++ {
				mems++
				a := vmem[vv].activity
//line cdcl.w:1055
				if a != 0 {
					mems++
					vmem[vv].activity = max(a*1e-100, tiny)
//line cdcl.w:1057
				}
			}
			varBump *= 1e-100

//line cdcl.w:940
		}
		mems++
		h = vmem[v].hloc
//line cdcl.w:942
		if h > 0 {

//line cdcl.w:951
			hp = (h - 1) >> 1
			mems++
			u = heap[hp]
//line cdcl.w:953
			mems++
			if vmem[u].activity < av {
				for {
					mems++
					heap[h] = u
//line cdcl.w:957
					mems++
					vmem[u].hloc = h
//line cdcl.w:958
					h = hp
					if h == 0 {
						break
					}
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:964
					mems++
					if vmem[u].activity >= av {
						break
					}
				}
				mems++
				heap[h] = v
//line cdcl.w:970
				mems++
				vmem[v].hloc = h
//line cdcl.w:971
				j = 1
			}

//line cdcl.w:944
		}

//line cdcl.w:1184
		xnew = 1

//line cdcl.w:1136
	} else {

//line cdcl.w:1155
		tl, xnew = 0, -1
		if c >= firstLearned && c < maxLearned {

//line cdcl.w:1065
			mems++
			ac = math.Float32frombits(mem[c-5]) + clauseBump
//line cdcl.w:1066
			mems++
			mem[c-5] = math.Float32bits(ac)
//line cdcl.w:1067
			if ac >= 1e20 {

//line cdcl.w:1072
				for c2 := firstLearned; c2 < maxLearned; {
					mems++
					e2 := c2 + int(mem[c2-1])
//line cdcl.w:1074
					mems++
					a := float64(math.Float32frombits(mem[c2-5]))
//line cdcl.w:1075
					if a != 0 {
						mems++
						mem[c2-5] = math.Float32bits(float32(max(a*1e-20, singleTiny)))
//line cdcl.w:1077
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

//line cdcl.w:1069
			}

//line cdcl.w:1158
		}
		mems++
		sz = int(mem[c-1])
//line cdcl.w:1160
		for k = c + sz - 1; k >= c; k-- {
			mems++
			l = int(mem[k]) ^ 1
//line cdcl.w:1162
			j = vmem[l>>1].tloc
			if j > tl {
				tl = j
			}

//line cdcl.w:1261
			mems++
			jj = vmem[l>>1].value &^ 1
//line cdcl.w:1262
			mems++
			vmem[l>>1].stamp = curstamp

//line cdcl.w:935
			v = l >> 1
			mems++
			av = vmem[v].activity + varBump
//line cdcl.w:937
			mems++
			vmem[v].activity = av
//line cdcl.w:938
			if av >= 1e100 {

//line cdcl.w:1053
				for vv := 1; vv <= vars; vv++ {
					mems++
					a := vmem[vv].activity
//line cdcl.w:1055
					if a != 0 {
						mems++
						vmem[vv].activity = max(a*1e-100, tiny)
//line cdcl.w:1057
					}
				}
				varBump *= 1e-100

//line cdcl.w:940
			}
			mems++
			h = vmem[v].hloc
//line cdcl.w:942
			if h > 0 {

//line cdcl.w:951
				hp = (h - 1) >> 1
				mems++
				u = heap[hp]
//line cdcl.w:953
				mems++
				if vmem[u].activity < av {
					for {
						mems++
						heap[h] = u
//line cdcl.w:957
						mems++
						vmem[u].hloc = h
//line cdcl.w:958
						h = hp
						if h == 0 {
							break
						}
						hp = (h - 1) >> 1
						mems++
						u = heap[hp]
//line cdcl.w:964
						mems++
						if vmem[u].activity >= av {
							break
						}
					}
					mems++
					heap[h] = v
//line cdcl.w:970
					mems++
					vmem[v].hloc = h
//line cdcl.w:971
					j = 1
				}

//line cdcl.w:944
			}

//line cdcl.w:1264
			if jj >= llevel {
				xnew++
			} else {
				if jj > jumplev {
					jumplev = jj
				}
				mems++
				learn[oldptr] = l ^ 1
				oldptr++
//line cdcl.w:1271
				mems++
				if levstamp[jj] < curstamp {
					mems++
					levstamp[jj] = curstamp
					clevels++
//line cdcl.w:1274
				} else if levstamp[jj] == curstamp {
					mems++
					levstamp[jj] = curstamp + 1
//line cdcl.w:1276
				}
			}

//line cdcl.w:1167
		}

//line cdcl.w:1138
	}

//line cdcl.w:1218
	for xnew != 0 {
		for {
			mems++
			l = trail[tl]
			tl--
//line cdcl.w:1221
			mems++
			if vmem[l>>1].stamp == curstamp {
				break
			}
		}
		xnew--

//line cdcl.w:1231
		mems++
		c = lmem[l].reason
//line cdcl.w:1232
		if c < 0 {
			l = -c
			mems++
			if vmem[l>>1].stamp != curstamp {

//line cdcl.w:1261
				mems++
				jj = vmem[l>>1].value &^ 1
//line cdcl.w:1262
				mems++
				vmem[l>>1].stamp = curstamp

//line cdcl.w:935
				v = l >> 1
				mems++
				av = vmem[v].activity + varBump
//line cdcl.w:937
				mems++
				vmem[v].activity = av
//line cdcl.w:938
				if av >= 1e100 {

//line cdcl.w:1053
					for vv := 1; vv <= vars; vv++ {
						mems++
						a := vmem[vv].activity
//line cdcl.w:1055
						if a != 0 {
							mems++
							vmem[vv].activity = max(a*1e-100, tiny)
//line cdcl.w:1057
						}
					}
					varBump *= 1e-100

//line cdcl.w:940
				}
				mems++
				h = vmem[v].hloc
//line cdcl.w:942
				if h > 0 {

//line cdcl.w:951
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:953
					mems++
					if vmem[u].activity < av {
						for {
							mems++
							heap[h] = u
//line cdcl.w:957
							mems++
							vmem[u].hloc = h
//line cdcl.w:958
							h = hp
							if h == 0 {
								break
							}
							hp = (h - 1) >> 1
							mems++
							u = heap[hp]
//line cdcl.w:964
							mems++
							if vmem[u].activity >= av {
								break
							}
						}
						mems++
						heap[h] = v
//line cdcl.w:970
						mems++
						vmem[v].hloc = h
//line cdcl.w:971
						j = 1
					}

//line cdcl.w:944
				}

//line cdcl.w:1264
				if jj >= llevel {
					xnew++
				} else {
					if jj > jumplev {
						jumplev = jj
					}
					mems++
					learn[oldptr] = l ^ 1
					oldptr++
//line cdcl.w:1271
					mems++
					if levstamp[jj] < curstamp {
						mems++
						levstamp[jj] = curstamp
						clevels++
//line cdcl.w:1274
					} else if levstamp[jj] == curstamp {
						mems++
						levstamp[jj] = curstamp + 1
//line cdcl.w:1276
					}
				}

//line cdcl.w:1237
			}
		} else if c != 0 {
			if c >= firstLearned {

//line cdcl.w:1065
				mems++
				ac = math.Float32frombits(mem[c-5]) + clauseBump
//line cdcl.w:1066
				mems++
				mem[c-5] = math.Float32bits(ac)
//line cdcl.w:1067
				if ac >= 1e20 {

//line cdcl.w:1072
					for c2 := firstLearned; c2 < maxLearned; {
						mems++
						e2 := c2 + int(mem[c2-1])
//line cdcl.w:1074
						mems++
						a := float64(math.Float32frombits(mem[c2-5]))
//line cdcl.w:1075
						if a != 0 {
							mems++
							mem[c2-5] = math.Float32bits(float32(max(a*1e-20, singleTiny)))
//line cdcl.w:1077
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

//line cdcl.w:1069
				}

//line cdcl.w:1241
			}
			mems++
			sz = int(mem[c-1])
//line cdcl.w:1243
			for k = c + sz - 1; k > c; k-- {
				mems++
				l = int(mem[k]) ^ 1
//line cdcl.w:1245
				mems++
				if vmem[l>>1].stamp != curstamp {

//line cdcl.w:1261
					mems++
					jj = vmem[l>>1].value &^ 1
//line cdcl.w:1262
					mems++
					vmem[l>>1].stamp = curstamp

//line cdcl.w:935
					v = l >> 1
					mems++
					av = vmem[v].activity + varBump
//line cdcl.w:937
					mems++
					vmem[v].activity = av
//line cdcl.w:938
					if av >= 1e100 {

//line cdcl.w:1053
						for vv := 1; vv <= vars; vv++ {
							mems++
							a := vmem[vv].activity
//line cdcl.w:1055
							if a != 0 {
								mems++
								vmem[vv].activity = max(a*1e-100, tiny)
//line cdcl.w:1057
							}
						}
						varBump *= 1e-100

//line cdcl.w:940
					}
					mems++
					h = vmem[v].hloc
//line cdcl.w:942
					if h > 0 {

//line cdcl.w:951
						hp = (h - 1) >> 1
						mems++
						u = heap[hp]
//line cdcl.w:953
						mems++
						if vmem[u].activity < av {
							for {
								mems++
								heap[h] = u
//line cdcl.w:957
								mems++
								vmem[u].hloc = h
//line cdcl.w:958
								h = hp
								if h == 0 {
									break
								}
								hp = (h - 1) >> 1
								mems++
								u = heap[hp]
//line cdcl.w:964
								mems++
								if vmem[u].activity >= av {
									break
								}
							}
							mems++
							heap[h] = v
//line cdcl.w:970
							mems++
							vmem[v].hloc = h
//line cdcl.w:971
							j = 1
						}

//line cdcl.w:944
					}

//line cdcl.w:1264
					if jj >= llevel {
						xnew++
					} else {
						if jj > jumplev {
							jumplev = jj
						}
						mems++
						learn[oldptr] = l ^ 1
						oldptr++
//line cdcl.w:1271
						mems++
						if levstamp[jj] < curstamp {
							mems++
							levstamp[jj] = curstamp
							clevels++
//line cdcl.w:1274
						} else if levstamp[jj] == curstamp {
							mems++
							levstamp[jj] = curstamp + 1
//line cdcl.w:1276
						}
					}

//line cdcl.w:1248
				}
			}
			if xnew+oldptr+1 < sz && xnew != 0 {

//line cdcl.w:1302
				l = int(mem[c])
				mems++
				sz--
				mem[c-1] = uint32(sz)
				subsumptions++
//line cdcl.w:1304
				mems++
				r = int(mem[c-2])

//line cdcl.w:1327
				mems++
				for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
					mems++
					p = int(mem[wa])
//line cdcl.w:1330
					mems++
					if p == l {
						nextWa = int(mem[wa-2])
					} else {
						nextWa = int(mem[wa-3])
					}
				}
				if q == 0 {
					mems++
					lmem[l].watch = r
//line cdcl.w:1339
				} else if p == l {
					mems++
					mem[q-2] = uint32(r)
//line cdcl.w:1341
				} else {
					mems++
					mem[q-3] = uint32(r)
//line cdcl.w:1343
				}

//line cdcl.w:1306
				mems++
				ll = int(mem[c+sz])
//line cdcl.w:1307
				for lll, k = ll, c+sz; ; k-- {
					mems++
					r = vmem[lll>>1].value &^ 1
//line cdcl.w:1309
					if r == llevel {
						break
					}
					mems++
					lll = int(mem[k-1])
//line cdcl.w:1313
				}
				if k == c+1 {
					panic("sat: 이럴 수는 없다 (on-the-fly subsumption)")
				}
				if lll != ll {
					mems++
					mem[k] = uint32(ll)
//line cdcl.w:1319
				}
				mems += 2
				mem[c+sz] = uint32(l) + signBit
				mem[c] = uint32(lll)
//line cdcl.w:1321
				mems += 3
				mem[c-2] = uint32(lmem[lll].watch)
				lmem[lll].watch = c

//line cdcl.w:1252
			}
		}

//line cdcl.w:1228
	}

//line cdcl.w:1140
	for {
		mems++
		l = trail[tl]
		tl--
//line cdcl.w:1142
		mems++
		if vmem[l>>1].stamp == curstamp {
			break
		}
	}
	lll = l ^ 1

//line cdcl.w:2082

//line cdcl.w:1365
	learnedSize = oldptr + 1
	cellsPrelearned += float64(learnedSize)
	prelearnedSize = learnedSize
//line cdcl.w:1367
	for kk = 0; kk < oldptr; kk++ {
		mems++
		l = learn[kk] ^ 1
//line cdcl.w:1369
		mems += 2
		st = levstamp[vmem[l>>1].value&^1]
//line cdcl.w:1370
		if st < curstamp+1 {
			continue
		}

//line cdcl.w:1388
		if stackptr != 0 {
			panic("sat: 이럴 수는 없다 (stack)")
		}
	test:
		ll = l
		mems++
		if vmem[l>>1].value&^1 == 0 {
			goto isRed
		}
		mems++
		c = lmem[l].reason
//line cdcl.w:1398
		if c == 0 {
			goto clearStack
		}
		if c < 0 {

//line cdcl.w:1417
			l = -c ^ 1
			mems++
			st = vmem[l>>1].stamp
//line cdcl.w:1419
			if st >= curstamp {
				if st == curstamp+2 {
					goto clearStack
				}
			} else {
				mems++
				stack[stackptr] = ll
				stackptr++
//line cdcl.w:1425
				goto test
			}
			goto isRed

//line cdcl.w:1403
		}
		mems++
		k = c + int(mem[c-1]) - 1

//line cdcl.w:1434
	scan:
		if k <= c {
			goto isRed
		}
		mems += 2
		l = int(mem[k]) ^ 1
		st = vmem[l>>1].stamp
//line cdcl.w:1439
		if st >= curstamp {
			if st == curstamp+2 {
				goto clearStack
			}
			goto next
		}
		mems++
		st = vmem[l>>1].value &^ 1
//line cdcl.w:1446
		if st == 0 {
			goto next
		}
		mems++
		st = levstamp[st]
//line cdcl.w:1450
		if st < curstamp {
			mems++
			vmem[l>>1].stamp = curstamp + 2
//line cdcl.w:1452
			goto clearStack
		}
		mems++
		stack[stackptr] = k
		stack[stackptr+1] = ll
		stackptr += 2
//line cdcl.w:1455
		goto test
	next:
		k--
		goto scan

//line cdcl.w:1465
	isRed:
		mems++
		vmem[ll>>1].stamp = curstamp + 1
//line cdcl.w:1467
		if stackptr != 0 {
			mems += 2
			stackptr--
			ll = stack[stackptr]
			c = lmem[ll].reason
//line cdcl.w:1469
			if c < 0 {
				goto isRed
			}
			mems++
			stackptr--
			k = stack[stackptr]
//line cdcl.w:1473
			goto next
		}
		goto redundant

//line cdcl.w:1483
	clearStack:
		if stackptr != 0 {
			mems++
			vmem[ll>>1].stamp = curstamp + 2
//line cdcl.w:1486
			mems++
			stackptr--
			ll = stack[stackptr]
//line cdcl.w:1487
			mems++
			c = lmem[ll].reason
//line cdcl.w:1488
			if c > 0 {
				stackptr--
			}
			goto clearStack
		}

//line cdcl.w:1374
		continue
	redundant:
		learnedSize--
	}

//line cdcl.w:1500
	if learnedSize <= (jumplev>>1)+par.TrivialLimit {
		trivialLearning = false
	} else {
		trivialLearning = true
		clevels = jumplev >> 1
		learnedSize = clevels + 1
		trivials++
//line cdcl.w:1505
	}
	cellsLearned += float64(learnedSize)
	totalLearned++

//line cdcl.w:2083
	if fullRun {
		goto storeClause
	}

//line cdcl.w:2054
	mems++
	k = leveldat[jumplev+2]
//line cdcl.w:2055
	for eptr > k {
		eptr--
		mems++
		l = trail[eptr]
		v = l >> 1
//line cdcl.w:2057
		mems += 2
		vmem[v].oldval = vmem[v].value
//line cdcl.w:2058
		mems++
		vmem[v].value = unset
//line cdcl.w:2059
		mems++
		lmem[l].reason = 0
//line cdcl.w:2060
		if eptr < lptr {
			mems++
			if vmem[v].hloc < 0 {

//line cdcl.w:975
				mems++
				av = vmem[v].activity
//line cdcl.w:976
				h = hn
				hn++
				j = 0
//line cdcl.w:977
				if h > 0 {

//line cdcl.w:951
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:953
					mems++
					if vmem[u].activity < av {
						for {
							mems++
							heap[h] = u
//line cdcl.w:957
							mems++
							vmem[u].hloc = h
//line cdcl.w:958
							h = hp
							if h == 0 {
								break
							}
							hp = (h - 1) >> 1
							mems++
							u = heap[hp]
//line cdcl.w:964
							mems++
							if vmem[u].activity >= av {
								break
							}
						}
						mems++
						heap[h] = v
//line cdcl.w:970
						mems++
						vmem[v].hloc = h
//line cdcl.w:971
						j = 1
					}

//line cdcl.w:979
				}
				if j == 0 {
					mems += 2
					heap[h] = v
					vmem[v].hloc = h
//line cdcl.w:982
				}

//line cdcl.w:2064
			}
		}
	}
	lptr = eptr
	llevel = jumplev

//line cdcl.w:2087
	if learnedSize > 1 {

//line cdcl.w:1534
		if prevLearned != 0 {
			mems++
			l = int(mem[prevLearned])
//line cdcl.w:1536
			if !trivialLearning {
				mems++
				if lmem[l].reason == 0 {
					mems++
					if vmem[l>>1].value == unset {

//line cdcl.w:1565
						mems++
						for k, q = int(mem[prevLearned-1])-1, learnedSize; q != 0 && k >= q; k-- {
							mems += 2
							l = int(mem[prevLearned+k])
							r = vmem[l>>1].value &^ 1
//line cdcl.w:1568
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
							c = prevLearned
							mems++
							mem[c-5] = 0
//line cdcl.w:1579
							mems++
							l = int(mem[c])
							r = int(mem[c-2])
//line cdcl.w:1580

//line cdcl.w:1327
							mems++
							for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
								mems++
								p = int(mem[wa])
//line cdcl.w:1330
								mems++
								if p == l {
									nextWa = int(mem[wa-2])
								} else {
									nextWa = int(mem[wa-3])
								}
							}
							if q == 0 {
								mems++
								lmem[l].watch = r
//line cdcl.w:1339
							} else if p == l {
								mems++
								mem[q-2] = uint32(r)
//line cdcl.w:1341
							} else {
								mems++
								mem[q-3] = uint32(r)
//line cdcl.w:1343
							}

//line cdcl.w:1581
							mems += 2
							l = int(mem[c+1])
							r = int(mem[c-3])
//line cdcl.w:1582

//line cdcl.w:1327
							mems++
							for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
								mems++
								p = int(mem[wa])
//line cdcl.w:1330
								mems++
								if p == l {
									nextWa = int(mem[wa-2])
								} else {
									nextWa = int(mem[wa-3])
								}
							}
							if q == 0 {
								mems++
								lmem[l].watch = r
//line cdcl.w:1339
							} else if p == l {
								mems++
								mem[q-2] = uint32(r)
//line cdcl.w:1341
							} else {
								mems++
								mem[q-3] = uint32(r)
//line cdcl.w:1343
							}

//line cdcl.w:1583
						}

//line cdcl.w:1542
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

//line cdcl.w:595
			if maxCellsUsed > len(mem) {
				grown := make([]uint32, min(memsize, max(2*len(mem), maxCellsUsed)))
				copy(grown, mem)
				mem = grown
			}

//line cdcl.w:1556
		}
		mems++
		mem[c+learnedSize] = 0

//line cdcl.w:1590
		if mem[c-5] != 0 {
			panic("sat: 이럴 수는 없다 (bumps)")
		}
		mem[c-1] = uint32(learnedSize)
		mems++
		mem[c] = uint32(lll)
//line cdcl.w:1595
		mems += 2
		mem[c-2] = uint32(lmem[lll].watch)
//line cdcl.w:1596
		mems++
		lmem[lll].watch = c
//line cdcl.w:1597
		if trivialLearning {
			for j, k = 1, jumplev; k != 0; j, k = j+1, k-2 {
				mems += 2
				l = trail[leveldat[k]] ^ 1
//line cdcl.w:1600
				if j == 1 {
					mems += 3
					mem[c-3] = uint32(lmem[l].watch)
					lmem[l].watch = c
//line cdcl.w:1602
				}
				mems++
				mem[c+j] = uint32(l)
//line cdcl.w:1604
			}
		} else {

//line cdcl.w:1610
			for k, j, jj = 1, 0, 1; k < learnedSize; j++ {
				mems++
				l = learn[j]
//line cdcl.w:1612
				mems++
				if vmem[l>>1].stamp == curstamp {
					mems++
					r = vmem[l>>1].value
//line cdcl.w:1615
					if jj != 0 && r >= jumplev {
						mems++
						mem[c+1] = uint32(l)
//line cdcl.w:1617
						mems += 2
						mem[c-3] = uint32(lmem[l].watch)
//line cdcl.w:1618
						mems++
						lmem[l].watch = c
//line cdcl.w:1619
						jj = 0
					} else {
						mems++
						mem[c+k+jj] = uint32(l)
//line cdcl.w:1622
					}
					k++
				}
			}

//line cdcl.w:1607
		}

//line cdcl.w:1524
		prevLearned = c

//line cdcl.w:2089
		mems++
		lmem[lll].reason = c
//line cdcl.w:2090
	}
	mems++
	vmem[lll>>1].value = llevel + lll&1
	vmem[lll>>1].tloc = eptr
//line cdcl.w:2092
	mems++
	trail[eptr] = lll
	eptr++
//line cdcl.w:2093
	agility -= agility >> 13
	agility += 1 << 19

//line cdcl.w:1092
	varBump *= varBumpFactor
	clauseBump *= clauseBumpFactor

//line cdcl.w:2096
	goto proceed

//line cdcl.w:311
unsat:
	status = Unsat
	goto allDone
satisfied:
	status = Sat

//line cdcl.w:371
	s.model = make([]Lit, vars)
	s.truth = make([]bool, vars+1)
	for k = 0; k < vars; k++ {
		mems++
		s.model[k] = Lit(trail[k])
//line cdcl.w:375
		s.truth[trail[k]>>1] = trail[k]&1 == 0
	}

//line cdcl.w:317
allDone:

//line cdcl.w:379
	if status != Sat {
		s.model, s.truth = nil, nil
	}
	s.stats = Stats{IMems: imems, Mems: mems, Bytes: bytes, Nodes: nodes,
		Learned: totalLearned, CellsPrelearned: cellsPrelearned, CellsLearned: cellsLearned,
		MemCells: maxCellsUsed, Trivials: trivials, Discards: discards,
		Subsumptions: subsumptions, Restarts: actualRestarts}

//line cdcl.w:319
	return status, err
}
