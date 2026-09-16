//line cdcl.w:53
package sat

import (
	"context"
	"errors"
	"fmt"
	"io"
	"math"
	"slices"
	"strconv"
	"strings"

	"github.com/sjnam/go-sgb/gbflip"
)

//line cdcl.w:76
type Status int

const (
	Unknown Status = iota // 답을 내지 못했다
	Sat                   // 만족할 수 있다
	Unsat                 // 만족할 수 없다
)

//line cdcl.w:101
var (
	ErrTimeout  = errors.New("sat: mem 한도에 이르렀다")
	ErrDoomsday = errors.New("sat: 배운 절의 수가 doomsday에 이르렀다")
	ErrMemory   = errors.New("sat: mem 배열이 모자란다")

//line cdcl.w:105
)

//line cdcl.w:113
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
	LearnSave          int     // \.K: 증서에 적을 절 길이의 문턱 (10000)
}

//line cdcl.w:134
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
	LearnSave:          10000,
}

//line cdcl.w:223
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

//line cdcl.w:497
const (
	clauseExtra       = 3          // 모든 절의 머리 칸 수
	learnedSupplement = 2          // 배운 절에 더 붙는 머리 칸 수
	learnedExtra      = 5          // 배운 절의 머리 칸 수
	signBit           = 0x80000000 // 지워진 리터럴의 표
	unset             = 0xffffffff // 값이 없는 변수의 |value|
)

//line cdcl.w:530
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

//line cdcl.w:1198
const (
	tiny       = 2.225073858507201383e-308
	singleTiny = 1.1754943508222875080e-38

//line cdcl.w:1201
)

//line cdcl.w:1749
const (
	buckets  = 256  // 눈금에 올린 범위의 가짓수
	badlevel = 16.0 // 이보다 큰 범위는 사실상 무한
)

//line cdcl.w:2157
const checkEvery = 1 << 22 // |context|를 묻는 mem 간격

//line cdcl.w:2572
type cdclState struct {
	key                  Params // |Timeout|과 |Doomsday|를 0으로 둔 매개변수
	unsat                bool   // 가정 없이도 만족할 수 없는가
	rng                  *gbflip.RNG
	vars, clauses, cells int
	bytes                uint64

//line cdcl.w:2584
	mem, bmem                              []uint32
	memsize, minLearned, firstLearned      int
	maxLearned, maxCellsUsed, maxLit       int
	lmem                                   []literal
	vmem                                   []variable
	heap, trail, leveldat, conflictdat     []int
	learn, stack, levstamp, rangedist      []int
	hn, eptr, lptr, llevel                 int
	agility                                uint32
	varBump                                float64
	clauseBump                             float32
	curstamp, prevLearned, clauseHeapSize  int
	totalLearned, nextRecycle, recycleBump uint64
	clauseHeap                             []uint64
	warmupCycles, restartU, restartV       int
	restartThresh, nextRestart             uint64

//line cdcl.w:2579
}

//line cdcl.w:85
func (st Status) String() string {
	switch st {
	case Sat:
		return "SAT"
	case Unsat:
		return "UNSAT"
	}
	return "UNKNOWN"
}

//line cdcl.w:156
func (p *Params) Set(opt string) error {
	if opt == "" {
		return errors.New("sat: 빈 선택")
	}
	arg := opt[1:]
	var err error
	switch opt[0] {

//line cdcl.w:177
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
	case 'K':
		p.LearnSave, err = strconv.Atoi(arg)

//line cdcl.w:164

//line cdcl.w:200
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

//line cdcl.w:165
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

//line cdcl.w:238
func (s *Solver) Stats() Stats { return s.stats }

//line cdcl.w:244
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

//line cdcl.w:259
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

//line cdcl.w:255
	return b.String()
}

//line cdcl.w:274
func plural(n uint64, one, many string) string {
	if n == 1 {
		return one
	}
	return many
}

//line cdcl.w:285
func (s *Solver) Model() []Lit { return slices.Clone(s.model) }

func (s *Solver) Value(l Lit) bool {
	if s.truth == nil {
		panic("sat: 찾은 해가 없다")
	}
	return s.truth[l.Var()] != l.IsNeg()
}

//line cdcl.w:304
func (s *Solver) SetProof(w io.Writer) { s.proof = w }

//line cdcl.w:318
func (s *Solver) SetTrace(f func(level int, trail []Lit)) { s.trace = f }

//line cdcl.w:324
func (s *Solver) writeProof(lits []uint32, subsumer bool) {
	var b strings.Builder
	if subsumer {
		b.WriteByte(' ')
	}
	for _, l := range lits {
		b.WriteByte(' ')
		b.WriteString(s.LitName(Lit(l)))
	}
	b.WriteByte('\n')
	io.WriteString(s.proof, b.String())
}

//line cdcl.w:359
func (s *Solver) Solve(ctx context.Context, assumptions ...Lit) (Status, error) {

//line cdcl.w:410
	var (
		h, hp, i, j, jj, k, kk int
		l, ll, lll, p, q, r    int
		sz, st, t, u, v        int
		c, cc, endc            int
		au, av                 float64
	)

//line cdcl.w:419
	var (
		status                    Status
		err                       error
		par                       Params      // 매개변수의 사본
		rng                       *gbflip.RNG // 원본의 |gb_flip|과 같은 난수열
		vars, clauses, cells      int         // 변수, 절, 리터럴의 수
		imems, mems, bytes, nodes uint64
	)

//line cdcl.w:506
	var (
		mem                      []uint32 // 절들의 큰 배열
		memsize                  int      // |mem|이 자랄 수 있는 한도
		minLearned, firstLearned int      // 입력 절과 배운 절의 경계
		maxLearned               int      // |mem|에서 아직 쓰지 않은 첫 자리
		maxCellsUsed             int      // |mem|에서 쓴 칸 수의 최댓값
		maxLit                   int      // 가장 큰 리터럴
	)

//line cdcl.w:550
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

//line cdcl.w:645
	var (
		trueProbThresh int // $2^{31}\times$|TrueProb|
		cur            int // 임시 칸을 되감는 자리
	)

//line cdcl.w:861
	var (
		lt, lat    int    // 트레일의 리터럴과 그 |bimpEnd|
		la         int    // |bmem|을 훑는 자리
		wa, nextWa int    // 감시 목록의 절과 그다음 절
		agility    uint32 // 값이 뒤집히는 매끄러운 확률
	)

//line cdcl.w:1016
	var (
		fullRun       bool  // 전체 달리기 중인가
		conflictSeen  bool  // 이 수준에서 충돌을 보았는가
		conflictLevel int   // 기록된 충돌 더미의 꼭대기
		conflictdat   []int // 전체 달리기의 충돌 자료
	)

//line cdcl.w:1204
	var (
		varBump          float64 = 1.0
		clauseBump       float32 = 1.0
		varBumpFactor    float64 // $1/|VarRho|$
		clauseBumpFactor float32 // $1/|ClauseRho|$
		ac               float32 // 절 활동도
		randProbThresh   int     // $2^{31}\times$|RandProb|
	)

//line cdcl.w:1297
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

//line cdcl.w:1381
	var (
		stack    []int // 손수 다루는 재귀의 더미
		stackptr int   // 더미에 든 것의 수
		levstamp []int // 수준마다의 표시
	)

//line cdcl.w:1447
	var subsumptions uint64 // 즉석 포섭의 수

//line cdcl.w:1610
	var (
		prevLearned                   int     // 가장 최근에 배운 절
		cellsPrelearned, cellsLearned float64 // 배운 절들의 길이 합
		totalLearned                  uint64  // 배운 절의 수
		trivials, discards            uint64  // 자명한 절, 버린 절의 수
	)

//line cdcl.w:1755
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

//line cdcl.w:2401
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

//line cdcl.w:2445
	var (
		asm    []Lit // 가정들
		ai     int   // 살핀 가정의 수
		acheck []int // 가정들이 모두 참이 된 수준
	)

//line cdcl.w:2602
	var (
		key           Params // 상태를 이어 쓸 수 있는지 가르는 매개변수
		unsatisfiable bool   // 가정 없이도 만족할 수 없는가
		learnedBase   uint64 // 이번 풀이를 시작할 때의 |totalLearned|
		doomsday      uint64 // 이번 풀이에서 배운 절 수의 한도
	)

//line cdcl.w:2709
	var (
		zero             []int    // 떼어 둔 수준 0의 리터럴들
		oldMem           []uint32 // 옮겨 심을 배운 절이 든 옛 |mem|
		oldFirst, oldMax int      // 옛 |mem|에서 배운 절의 구간
	)

//line cdcl.w:361

//line cdcl.w:2436
	s.failed = nil
	for _, a := range assumptions {
		if v := a.Var(); v == 0 || v >= len(s.names) {
			panic(fmt.Sprintf("sat: 없는 변수의 가정 %d", uint32(a)))
		}
	}
	asm, ai, acheck = assumptions, 0, make([]int, len(assumptions))

//line cdcl.w:362

//line cdcl.w:393
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

//line cdcl.w:363

//line cdcl.w:432
	par = s.Params
	if par.MemLog < 2 || par.MemLog > 31 || par.TrivialLimit <= 0 || par.Alpha < 0 ||
		par.Alpha > 1 || par.RandProb < 0 || par.TrueProb < 0 || par.VarRho <= 0 ||
		par.ClauseRho <= 0 {
		return Unknown, errors.New("sat: 매개변수가 범위를 벗어났다")
	}
	key = par
	key.Timeout, key.Doomsday = 0, 0

//line cdcl.w:364
	if s.state != nil && s.state.key == key {

//line cdcl.w:2654
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

//line cdcl.w:2643
		if unsatisfiable {
			goto unsat
		}

//line cdcl.w:2674
		if llevel != 0 {
			jumplev = 0

//line cdcl.w:2215
			mems++
			k = leveldat[jumplev+2]
//line cdcl.w:2216
			for eptr > k {
				eptr--
				mems++
				l = trail[eptr]
				v = l >> 1
//line cdcl.w:2218
				mems += 2
				vmem[v].oldval = vmem[v].value
//line cdcl.w:2219
				mems++
				vmem[v].value = unset
//line cdcl.w:2220
				mems++
				lmem[l].reason = 0
//line cdcl.w:2221
				if eptr < lptr {
					mems++
					if vmem[v].hloc < 0 {

//line cdcl.w:1073
						mems++
						av = vmem[v].activity
//line cdcl.w:1074
						h = hn
						hn++
						j = 0
//line cdcl.w:1075
						if h > 0 {

//line cdcl.w:1049
							hp = (h - 1) >> 1
							mems++
							u = heap[hp]
//line cdcl.w:1051
							mems++
							if vmem[u].activity < av {
								for {
									mems++
									heap[h] = u
//line cdcl.w:1055
									mems++
									vmem[u].hloc = h
//line cdcl.w:1056
									h = hp
									if h == 0 {
										break
									}
									hp = (h - 1) >> 1
									mems++
									u = heap[hp]
//line cdcl.w:1062
									mems++
									if vmem[u].activity >= av {
										break
									}
								}
								mems++
								heap[h] = v
//line cdcl.w:1068
								mems++
								vmem[v].hloc = h
//line cdcl.w:1069
								j = 1
							}

//line cdcl.w:1077
						}
						if j == 0 {
							mems += 2
							heap[h] = v
							vmem[v].hloc = h
//line cdcl.w:1080
						}

//line cdcl.w:2225
					}
				}
			}
			lptr = eptr
			llevel = jumplev

//line cdcl.w:2677
		}

//line cdcl.w:2647
		if vars != s.NumVars() || cells != len(s.cells) {

//line cdcl.w:2690
			zero = append(zero[:0], trail[:eptr]...)
			for _, l = range zero {
				mems++
				vmem[l>>1].value = unset
//line cdcl.w:2693
			}
			oldMem, oldFirst, oldMax = mem, firstLearned, maxLearned
			vars, clauses, cells = s.NumVars(), s.clauses, len(s.cells)
			bytes = uint64(vars+1)*40 + uint64(vars)*4

//line cdcl.w:609
			if par.TrueProb >= 1.0 {
				trueProbThresh = 0x80000000
			} else {
				trueProbThresh = int(float64(par.TrueProb) * 2147483648.0)
			}

//line cdcl.w:2720
			for k = len(vmem); k <= vars; k++ {
				mems++
				vmem = append(vmem, variable{value: unset, tloc: -1, oldval: 1})
//line cdcl.w:2722
				heap = append(heap, 0)
				v = k
				if trueProbThresh != 0 {
					mems += 4
					if int(rng.Next()) < trueProbThresh {
						vmem[v].oldval = 0
					}
				}

//line cdcl.w:1073
				mems++
				av = vmem[v].activity
//line cdcl.w:1074
				h = hn
				hn++
				j = 0
//line cdcl.w:1075
				if h > 0 {

//line cdcl.w:1049
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:1051
					mems++
					if vmem[u].activity < av {
						for {
							mems++
							heap[h] = u
//line cdcl.w:1055
							mems++
							vmem[u].hloc = h
//line cdcl.w:1056
							h = hp
							if h == 0 {
								break
							}
							hp = (h - 1) >> 1
							mems++
							u = heap[hp]
//line cdcl.w:1062
							mems++
							if vmem[u].activity >= av {
								break
							}
						}
						mems++
						heap[h] = v
//line cdcl.w:1068
						mems++
						vmem[v].hloc = h
//line cdcl.w:1069
						j = 1
					}

//line cdcl.w:1077
				}
				if j == 0 {
					mems += 2
					heap[h] = v
					vmem[v].hloc = h
//line cdcl.w:1080
				}

//line cdcl.w:2731
			}

//line cdcl.w:657
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

//line cdcl.w:675
			maxLit = vars + vars + 1
			lmem = make([]literal, maxLit+1)
			bytes += uint64(maxLit+1) * 16
			trail = make([]int, vars)
			bytes += uint64(vars) * 4
			bmem = make([]uint32, 2*s.binaries)
			bytes += uint64(2*s.binaries)*4 + uint64(vars)

//line cdcl.w:699
			eptr = 0
			for l = 2; l <= maxLit; l++ {
				mems += 2
				lmem[l].reason = 0
				lmem[l].watch = 0
				lmem[l].bimpEnd = 0
//line cdcl.w:702
			}
			cur = cells
			for c, j, jj = clauseExtra, clauses, minLearned+2; j != 0; j-- {

//line cdcl.w:721
				for k = 0; ; {
					cur--
					i = int(s.cells[cur])
					mems++
					mem[c+k] = uint32(i &^ int(firstLit))
					k++
//line cdcl.w:725
					if i&int(firstLit) != 0 {
						break
					}
				}

//line cdcl.w:706
				if k <= 2 {

//line cdcl.w:736
					if k < 2 {
						l = int(mem[c])

//line cdcl.w:749
						v = l >> 1
						mems++
						if vmem[v].value == unset {
							mems++
							vmem[v].value = l & 1
							vmem[v].tloc = eptr
//line cdcl.w:753
							mems++
							trail[eptr] = l
							eptr++
//line cdcl.w:754
						} else if vmem[v].value != l&1 {
							goto unsat
						}

//line cdcl.w:739
					} else {
						l, ll = int(mem[c]), int(mem[c+1])
						mems += 2
						lmem[l^1].bimpEnd++
//line cdcl.w:742
						mems += 2
						lmem[ll^1].bimpEnd++
//line cdcl.w:743
						mems++
						mem[jj] = uint32(l)
						mem[jj+1] = uint32(ll)
						jj += 2
//line cdcl.w:744
					}

//line cdcl.w:708
				} else {
					mems++
					mem[c-1] = uint32(k)
//line cdcl.w:710
					l = int(mem[c])
					mems += 3
					mem[c-2] = uint32(lmem[l].watch)
					lmem[l].watch = c
//line cdcl.w:712
					l = int(mem[c+1])
					mems += 3
					mem[c-3] = uint32(lmem[l].watch)
					lmem[l].watch = c
//line cdcl.w:714
					c += k + clauseExtra
				}
			}
			mems++
			mem[c-clauseExtra] = 0

//line cdcl.w:762
			for l, jj = 2, 0; l <= maxLit; l++ {
				mems++
				k = lmem[l].bimpEnd
//line cdcl.w:764
				if k != 0 {
					mems++
					lmem[l].bimpStart = jj
					lmem[l].bimpEnd = jj
					jj += k
//line cdcl.w:766
				}
			}
			for jj, j = minLearned+2, s.binaries; j != 0; j-- {
				mems++
				l = int(mem[jj])
				ll = int(mem[jj+1])
				jj += 2
//line cdcl.w:770
				mems += 3
				k = lmem[l^1].bimpEnd
				bmem[k] = uint32(ll)
				lmem[l^1].bimpEnd = k + 1
//line cdcl.w:771
				mems += 3
				k = lmem[ll^1].bimpEnd
				bmem[k] = uint32(l)
				lmem[ll^1].bimpEnd = k + 1
//line cdcl.w:772
			}

//line cdcl.w:787
			leveldat = make([]int, 2*vars+4)
			learn = make([]int, vars)
			stack = make([]int, 2*vars+4)
			conflictdat = make([]int, 2*vars+4)
			levstamp = make([]int, 2*vars+4)
			bytes += uint64(vars)*(8+4+8+8+8) + buckets*4
			for k = 0; k < vars; k++ {
				mems++
				levstamp[k+k] = 0
//line cdcl.w:795
			}
			rangedist = make([]int, buckets+1) // 끝의 한 칸은 늘 0
			for k = 0; k+k < buckets; k++ {
				mems++
				rangedist[k+k] = 0
				rangedist[k+k+1] = 0
//line cdcl.w:799
			}
			clauseHeapSize = int(par.RecycleBump >> 1)
			clauseHeap = make([]uint64, clauseHeapSize)
			bytes += uint64(clauseHeapSize) * 8

//line cdcl.w:2188
			for k = 0; k < vars; k++ {
				mems++
				leveldat[k+k] = -1
				leveldat[k+k+1] = 0
//line cdcl.w:2190
			}

//line cdcl.w:2702
			for _, l = range zero {

//line cdcl.w:749
				v = l >> 1
				mems++
				if vmem[v].value == unset {
					mems++
					vmem[v].value = l & 1
					vmem[v].tloc = eptr
//line cdcl.w:753
					mems++
					trail[eptr] = l
					eptr++
//line cdcl.w:754
				} else if vmem[v].value != l&1 {
					goto unsat
				}

//line cdcl.w:2704
			}

//line cdcl.w:2739
			for q = oldFirst; q < oldMax; q = endc + learnedExtra {
				mems++
				endc = q + int(oldMem[q-1])
				jj = endc
//line cdcl.w:2741
				for {
					mems++
					if oldMem[endc]&signBit == 0 {
						break
					}
					endc++
				}

//line cdcl.w:2753
				c = maxLearned

//line cdcl.w:2783
				t = c + jj - q + learnedExtra
				if t > maxCellsUsed {
					if t >= memsize {
						err = ErrMemory
						goto allDone
					}
					bytes += uint64(t-maxCellsUsed) * 4
					maxCellsUsed = t

//line cdcl.w:687
					if maxCellsUsed > len(mem) {
						grown := make([]uint32, min(memsize, max(2*len(mem), maxCellsUsed)))
						copy(grown, mem)
						mem = grown
					}

//line cdcl.w:2792
				}

//line cdcl.w:2755
				for kk, k = c, q; k < jj; k++ {
					mems++
					l = int(oldMem[k])
//line cdcl.w:2757
					mems++
					v = vmem[l>>1].value
//line cdcl.w:2758
					if v != unset {
						if (v^l)&1 != 0 {
							continue
						}
						break
					}
					mems++
					mem[kk] = uint32(l)
					kk++
//line cdcl.w:2765
				}
				if k < jj {
					continue
				}
				if kk >= c+2 {
					mems += 3
					mem[c-1] = uint32(kk - c)
					mem[c-5] = oldMem[q-5]
					mem[c-4] = 0
//line cdcl.w:2771

//line cdcl.w:2060
					mems++
					l = int(mem[c])
//line cdcl.w:2061
					mems += 3
					mem[c-2] = uint32(lmem[l].watch)
					lmem[l].watch = c
//line cdcl.w:2062
					l = int(mem[c+1])
					mems += 3
					mem[c-3] = uint32(lmem[l].watch)
					lmem[l].watch = c

//line cdcl.w:2772
					maxLearned = kk + learnedExtra
				} else if kk == c {
					goto unsat
				} else {
					mems++
					l = int(mem[c])
//line cdcl.w:2777

//line cdcl.w:749
					v = l >> 1
					mems++
					if vmem[v].value == unset {
						mems++
						vmem[v].value = l & 1
						vmem[v].tloc = eptr
//line cdcl.w:753
						mems++
						trail[eptr] = l
						eptr++
//line cdcl.w:754
					} else if vmem[v].value != l&1 {
						goto unsat
					}

//line cdcl.w:2778
				}

//line cdcl.w:2749
			}
			mems++
			mem[maxLearned-learnedExtra] = 0

//line cdcl.w:2706
			lptr, prevLearned = 0, 0

//line cdcl.w:2649
		}
		imems, mems = mems, 0

//line cdcl.w:2175
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

//line cdcl.w:366
	} else {

//line cdcl.w:448
		vars, clauses, cells = s.NumVars(), s.clauses, len(s.cells)
		rng = gbflip.New(int64(par.Seed))
		for k = 0; k < 736; k++ {
			rng.Next()
		}

//line cdcl.w:368

//line cdcl.w:580
		vmem = make([]variable, vars+1)
		bytes += uint64(vars+1) * 40
		for k = 1; k <= vars; k++ {
			mems++
			vmem[k].value = unset
			vmem[k].tloc = -1
//line cdcl.w:584
		}
		heap = make([]int, vars)
		bytes += uint64(vars) * 4

//line cdcl.w:609
		if par.TrueProb >= 1.0 {
			trueProbThresh = 0x80000000
		} else {
			trueProbThresh = int(float64(par.TrueProb) * 2147483648.0)
		}

//line cdcl.w:593
		for k = 1; k <= vars; k++ {
			mems++
			heap[k-1] = k
//line cdcl.w:595
		}
		for hn = vars; hn > 1; {

//line cdcl.w:635
			t = 0x80000000 - 0x80000000%hn
			for {
				mems += 4
				r = int(rng.Next())
//line cdcl.w:638
				if r < t {
					break
				}
			}
			h = r % hn

//line cdcl.w:598
			hn--
			if h != hn {
				mems++
				k = heap[h]
//line cdcl.w:601
				mems += 3
				heap[h] = heap[hn]
				heap[hn] = k
//line cdcl.w:602
			}
		}

//line cdcl.w:616
		for h = 0; h < vars; h++ {
			mems++
			v = heap[h]
//line cdcl.w:618
			mems++
			vmem[v].hloc = h
//line cdcl.w:619
			vmem[v].oldval = 1
			if trueProbThresh != 0 {
				mems += 4
				if int(rng.Next()) < trueProbThresh {
					vmem[v].oldval = 0
				}
			}
			mems++
			vmem[v].activity = 0
//line cdcl.w:627
		}
		hn = vars

//line cdcl.w:657
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

//line cdcl.w:675
		maxLit = vars + vars + 1
		lmem = make([]literal, maxLit+1)
		bytes += uint64(maxLit+1) * 16
		trail = make([]int, vars)
		bytes += uint64(vars) * 4
		bmem = make([]uint32, 2*s.binaries)
		bytes += uint64(2*s.binaries)*4 + uint64(vars)

//line cdcl.w:699
		eptr = 0
		for l = 2; l <= maxLit; l++ {
			mems += 2
			lmem[l].reason = 0
			lmem[l].watch = 0
			lmem[l].bimpEnd = 0
//line cdcl.w:702
		}
		cur = cells
		for c, j, jj = clauseExtra, clauses, minLearned+2; j != 0; j-- {

//line cdcl.w:721
			for k = 0; ; {
				cur--
				i = int(s.cells[cur])
				mems++
				mem[c+k] = uint32(i &^ int(firstLit))
				k++
//line cdcl.w:725
				if i&int(firstLit) != 0 {
					break
				}
			}

//line cdcl.w:706
			if k <= 2 {

//line cdcl.w:736
				if k < 2 {
					l = int(mem[c])

//line cdcl.w:749
					v = l >> 1
					mems++
					if vmem[v].value == unset {
						mems++
						vmem[v].value = l & 1
						vmem[v].tloc = eptr
//line cdcl.w:753
						mems++
						trail[eptr] = l
						eptr++
//line cdcl.w:754
					} else if vmem[v].value != l&1 {
						goto unsat
					}

//line cdcl.w:739
				} else {
					l, ll = int(mem[c]), int(mem[c+1])
					mems += 2
					lmem[l^1].bimpEnd++
//line cdcl.w:742
					mems += 2
					lmem[ll^1].bimpEnd++
//line cdcl.w:743
					mems++
					mem[jj] = uint32(l)
					mem[jj+1] = uint32(ll)
					jj += 2
//line cdcl.w:744
				}

//line cdcl.w:708
			} else {
				mems++
				mem[c-1] = uint32(k)
//line cdcl.w:710
				l = int(mem[c])
				mems += 3
				mem[c-2] = uint32(lmem[l].watch)
				lmem[l].watch = c
//line cdcl.w:712
				l = int(mem[c+1])
				mems += 3
				mem[c-3] = uint32(lmem[l].watch)
				lmem[l].watch = c
//line cdcl.w:714
				c += k + clauseExtra
			}
		}
		mems++
		mem[c-clauseExtra] = 0

//line cdcl.w:762
		for l, jj = 2, 0; l <= maxLit; l++ {
			mems++
			k = lmem[l].bimpEnd
//line cdcl.w:764
			if k != 0 {
				mems++
				lmem[l].bimpStart = jj
				lmem[l].bimpEnd = jj
				jj += k
//line cdcl.w:766
			}
		}
		for jj, j = minLearned+2, s.binaries; j != 0; j-- {
			mems++
			l = int(mem[jj])
			ll = int(mem[jj+1])
			jj += 2
//line cdcl.w:770
			mems += 3
			k = lmem[l^1].bimpEnd
			bmem[k] = uint32(ll)
			lmem[l^1].bimpEnd = k + 1
//line cdcl.w:771
			mems += 3
			k = lmem[ll^1].bimpEnd
			bmem[k] = uint32(l)
			lmem[ll^1].bimpEnd = k + 1
//line cdcl.w:772
		}

//line cdcl.w:778
		for c = vars; c != 0; c-- {
			mems += 2
			vmem[c].stamp = 0
//line cdcl.w:780
		}

//line cdcl.w:787
		leveldat = make([]int, 2*vars+4)
		learn = make([]int, vars)
		stack = make([]int, 2*vars+4)
		conflictdat = make([]int, 2*vars+4)
		levstamp = make([]int, 2*vars+4)
		bytes += uint64(vars)*(8+4+8+8+8) + buckets*4
		for k = 0; k < vars; k++ {
			mems++
			levstamp[k+k] = 0
//line cdcl.w:795
		}
		rangedist = make([]int, buckets+1) // 끝의 한 칸은 늘 0
		for k = 0; k+k < buckets; k++ {
			mems++
			rangedist[k+k] = 0
			rangedist[k+k+1] = 0
//line cdcl.w:799
		}
		clauseHeapSize = int(par.RecycleBump >> 1)
		clauseHeap = make([]uint64, clauseHeapSize)
		bytes += uint64(clauseHeapSize) * 8

//line cdcl.w:369
		imems, mems = mems, 0

//line cdcl.w:2175
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

//line cdcl.w:2165
		recycleBump = par.RecycleBump
		nextRecycle = min(recycleBump, doomsday)
		restartU, restartV, nextRestart = 1, 1, 1

//line cdcl.w:2188
		for k = 0; k < vars; k++ {
			mems++
			leveldat[k+k] = -1
			leveldat[k+k+1] = 0
//line cdcl.w:2190
		}

//line cdcl.w:2169
		llevel, warmupCycles, lptr = 0, 0, 0

//line cdcl.w:371
	}

//line cdcl.w:2073
startup:
	conflictLevel = 0
	fullRun = warmupCycles < par.Warmups
proceed:
	conflictSeen = false

//line cdcl.w:2197
	ebptr = eptr
	for lptr < eptr {
		mems++
		lt = trail[lptr]
		lptr++
//line cdcl.w:2200
		if lptr <= ebptr {
			mems++
			lat = lmem[lt].bimpEnd
//line cdcl.w:2202
			if lat != 0 {
				l = lt

//line cdcl.w:818
				for lbptr = eptr; ; {
					for la = lmem[l].bimpStart; la < lat; la++ {
						mems++
						ll = int(bmem[la])
//line cdcl.w:821
						mems++
						if vmem[ll>>1].value != unset {
							if (vmem[ll>>1].value^ll)&1 != 0 {

//line cdcl.w:985
								if fullRun && llevel != 0 {
									if !conflictSeen {
										conflictSeen = true
										mems++
										leveldat[llevel+1] = -l
//line cdcl.w:989
										mems++
										conflictdat[llevel+1] = ll
//line cdcl.w:990
										conflictdat[llevel] = conflictLevel
										conflictLevel = llevel
//line cdcl.w:991
									}
								} else {
									c = -l
									goto confl
								}

//line cdcl.w:825
							}
						} else {

//line cdcl.w:851
							mems++
							trail[eptr] = ll
//line cdcl.w:852
							mems++
							lmem[ll].reason = -l
//line cdcl.w:853
							mems++
							vmem[ll>>1].value = llevel + ll&1
							vmem[ll>>1].tloc = eptr
							eptr++
//line cdcl.w:854
							agility -= agility >> 13
							mems++
							if (vmem[ll>>1].oldval+ll)&1 != 0 {
								agility += 1 << 19
							}

//line cdcl.w:828
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
//line cdcl.w:836
						mems++
						lat = lmem[l].bimpEnd
//line cdcl.w:837
						if lat != 0 {
							break
						}
					}
					if l == 0 {
						break
					}
				}

//line cdcl.w:2205
			}
		}

//line cdcl.w:877
		mems++
		wa = lmem[lt^1].watch
//line cdcl.w:878
		if wa != 0 {
			for q = 0; wa != 0; wa = nextWa {

//line cdcl.w:893
				mems++
				ll = int(mem[wa])
//line cdcl.w:894
				if ll == lt^1 {
					mems++
					ll = int(mem[wa+1])
//line cdcl.w:896
					mems += 2
					mem[wa] = uint32(ll)
					mem[wa+1] = uint32(lt ^ 1)
//line cdcl.w:897
					mems++
					nextWa = int(mem[wa-2])
//line cdcl.w:898
					mems++
					mem[wa-2] = mem[wa-3]
					mem[wa-3] = uint32(nextWa)
//line cdcl.w:899
				} else {
					mems++
					nextWa = int(mem[wa-3])
//line cdcl.w:901
				}

//line cdcl.w:881

//line cdcl.w:907
				mems++
				if vmem[ll>>1].value != unset && (vmem[ll>>1].value^ll)&1 == 0 {

//line cdcl.w:919
					if q == 0 {
						mems++
						lmem[lt^1].watch = wa
//line cdcl.w:921
					} else {
						mems++
						mem[q-3] = uint32(wa)
//line cdcl.w:923
					}
					q = wa

//line cdcl.w:910
					continue
				}

//line cdcl.w:882

//line cdcl.w:931
				mems++
				sz = int(mem[wa-1])
//line cdcl.w:932
				for j = wa + sz - 1; j > wa+1; j-- {
					mems++
					l = int(mem[j])
//line cdcl.w:934
					mems++
					if vmem[l>>1].value == unset || (vmem[l>>1].value^l)&1 == 0 {
						break
					}
					if vmem[l>>1].value < 2 && llevel != 0 {

//line cdcl.w:944
						mems++
						sz--
						mem[wa-1] = uint32(sz)
//line cdcl.w:945
						if j != wa+sz {
							mems += 2
							mem[j] = mem[wa+sz]
//line cdcl.w:947
						}
						mems++
						mem[wa+sz] = uint32(l) + signBit

//line cdcl.w:940
					}
				}

//line cdcl.w:883
				if j > wa+1 {

//line cdcl.w:951
					mems += 2
					mem[wa+1] = uint32(l)
					mem[j] = uint32(lt ^ 1)
//line cdcl.w:952
					mems++
					mem[wa-3] = uint32(lmem[l].watch)
//line cdcl.w:953
					mems++
					lmem[l].watch = wa
//line cdcl.w:954
					continue

//line cdcl.w:885
				}

//line cdcl.w:919
				if q == 0 {
					mems++
					lmem[lt^1].watch = wa
//line cdcl.w:921
				} else {
					mems++
					mem[q-3] = uint32(wa)
//line cdcl.w:923
				}
				q = wa

//line cdcl.w:887

//line cdcl.w:961
				if vmem[ll>>1].value != unset {

//line cdcl.w:998
					if fullRun && llevel != 0 {
						if !conflictSeen {
							conflictSeen = true
							mems++
							leveldat[llevel+1] = wa
//line cdcl.w:1002
							mems++
							conflictdat[llevel] = conflictLevel
							conflictLevel = llevel
//line cdcl.w:1003
						}
					} else {
						c = wa
						goto confl
					}

//line cdcl.w:963
				} else {
					mems++
					trail[eptr] = ll
//line cdcl.w:965
					mems++
					vmem[ll>>1].tloc = eptr
					eptr++
//line cdcl.w:966
					vmem[ll>>1].value = llevel + ll&1
					agility -= agility >> 13
					mems++
					if (vmem[ll>>1].oldval+ll)&1 != 0 {
						agility += 1 << 19
					}
					mems++
					lmem[ll].reason = wa
//line cdcl.w:973
					mems++
					lat = lmem[ll].bimpEnd
//line cdcl.w:974
					if lat != 0 {
						l = ll

//line cdcl.w:818
						for lbptr = eptr; ; {
							for la = lmem[l].bimpStart; la < lat; la++ {
								mems++
								ll = int(bmem[la])
//line cdcl.w:821
								mems++
								if vmem[ll>>1].value != unset {
									if (vmem[ll>>1].value^ll)&1 != 0 {

//line cdcl.w:985
										if fullRun && llevel != 0 {
											if !conflictSeen {
												conflictSeen = true
												mems++
												leveldat[llevel+1] = -l
//line cdcl.w:989
												mems++
												conflictdat[llevel+1] = ll
//line cdcl.w:990
												conflictdat[llevel] = conflictLevel
												conflictLevel = llevel
//line cdcl.w:991
											}
										} else {
											c = -l
											goto confl
										}

//line cdcl.w:825
									}
								} else {

//line cdcl.w:851
									mems++
									trail[eptr] = ll
//line cdcl.w:852
									mems++
									lmem[ll].reason = -l
//line cdcl.w:853
									mems++
									vmem[ll>>1].value = llevel + ll&1
									vmem[ll>>1].tloc = eptr
									eptr++
//line cdcl.w:854
									agility -= agility >> 13
									mems++
									if (vmem[ll>>1].oldval+ll)&1 != 0 {
										agility += 1 << 19
									}

//line cdcl.w:828
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
//line cdcl.w:836
								mems++
								lat = lmem[l].bimpEnd
//line cdcl.w:837
								if lat != 0 {
									break
								}
							}
							if l == 0 {
								break
							}
						}

//line cdcl.w:977
					}
				}

//line cdcl.w:888
			}

//line cdcl.w:919
			if q == 0 {
				mems++
				lmem[lt^1].watch = wa
//line cdcl.w:921
			} else {
				mems++
				mem[q-3] = uint32(wa)
//line cdcl.w:923
			}
			q = wa

//line cdcl.w:890
		}

//line cdcl.w:2208
	}

//line cdcl.w:2079

//line cdcl.w:2144
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

//line cdcl.w:2080
	if eptr == vars {
		if conflictLevel == 0 {

//line cdcl.w:2466
			l = 0
			for ai > 0 && acheck[ai-1] > llevel {
				ai--
			}
			for ; ai < len(asm); ai++ {

//line cdcl.w:2479
				t = 0
				if ai > 0 {
					t = acheck[ai-1]
				}
				mems++
				u = int(asm[ai])
				v = vmem[u>>1].value
//line cdcl.w:2484
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

//line cdcl.w:2472
			}

//line cdcl.w:2083
			goto satisfied
		}
		goto finishFull
	}
	if conflictLevel == 0 {

//line cdcl.w:2098
		if totalLearned >= doomsday {
			err = ErrDoomsday
			goto allDone
		}
		if totalLearned >= nextRecycle {
			fullRun = true
		} else if totalLearned >= nextRestart {

//line cdcl.w:2358
			if restartU&-restartU == restartV {
				restartU++
				restartV = 1
				restartThresh = restartPsi
//line cdcl.w:2360
			} else {
				restartV <<= 1
				restartThresh += restartThresh >> 4
//line cdcl.w:2362
			}
			nextRestart = min(totalLearned+uint64(restartV), doomsday)
			if uint64(agility) <= restartThresh {

//line cdcl.w:2375
				actualRestarts++
				if llevel != 0 {
					for {
						mems++
						v = heap[0]
//line cdcl.w:2379
						mems++
						if vmem[v].value == unset {
							break
						}

//line cdcl.w:1086
						mems++
						vmem[v].hloc = -1
//line cdcl.w:1087
						hn--
						if hn != 0 {
							mems++
							u = heap[hn]
//line cdcl.w:1090
							mems++
							au = vmem[u].activity
//line cdcl.w:1091
							for h, hp = 0, 1; hp < hn; h, hp = hp, 2*hp+1 {

//line cdcl.w:1104
								mems += 2
								av = vmem[heap[hp]].activity
//line cdcl.w:1105
								if hp+1 < hn {
									mems += 2
									if vmem[heap[hp+1]].activity > av {
										hp++
										av = vmem[heap[hp]].activity
//line cdcl.w:1109
									}
								}

//line cdcl.w:1093
								if au >= av {
									break
								}
								mems++
								heap[h] = heap[hp]
//line cdcl.w:1097
								mems++
								vmem[heap[hp]].hloc = h
//line cdcl.w:1098
							}
							mems++
							heap[h] = u
//line cdcl.w:1100
							mems++
							vmem[u].hloc = h
//line cdcl.w:1101
						}

//line cdcl.w:2384
					}
					mems++
					av = vmem[v].activity
//line cdcl.w:2386
					for jumplev = 0; jumplev < llevel; jumplev += 2 {
						mems += 2
						v = trail[leveldat[jumplev+2]] >> 1
//line cdcl.w:2388
						mems++
						if vmem[v].activity < av {
							break
						}
					}
					if jumplev < llevel {

//line cdcl.w:2215
						mems++
						k = leveldat[jumplev+2]
//line cdcl.w:2216
						for eptr > k {
							eptr--
							mems++
							l = trail[eptr]
							v = l >> 1
//line cdcl.w:2218
							mems += 2
							vmem[v].oldval = vmem[v].value
//line cdcl.w:2219
							mems++
							vmem[v].value = unset
//line cdcl.w:2220
							mems++
							lmem[l].reason = 0
//line cdcl.w:2221
							if eptr < lptr {
								mems++
								if vmem[v].hloc < 0 {

//line cdcl.w:1073
									mems++
									av = vmem[v].activity
//line cdcl.w:1074
									h = hn
									hn++
									j = 0
//line cdcl.w:1075
									if h > 0 {

//line cdcl.w:1049
										hp = (h - 1) >> 1
										mems++
										u = heap[hp]
//line cdcl.w:1051
										mems++
										if vmem[u].activity < av {
											for {
												mems++
												heap[h] = u
//line cdcl.w:1055
												mems++
												vmem[u].hloc = h
//line cdcl.w:1056
												h = hp
												if h == 0 {
													break
												}
												hp = (h - 1) >> 1
												mems++
												u = heap[hp]
//line cdcl.w:1062
												mems++
												if vmem[u].activity >= av {
													break
												}
											}
											mems++
											heap[h] = v
//line cdcl.w:1068
											mems++
											vmem[v].hloc = h
//line cdcl.w:1069
											j = 1
										}

//line cdcl.w:1077
									}
									if j == 0 {
										mems += 2
										heap[h] = v
										vmem[v].hloc = h
//line cdcl.w:1080
									}

//line cdcl.w:2225
								}
							}
						}
						lptr = eptr
						llevel = jumplev

//line cdcl.w:2395
					}
				}
				warmupCycles = 0
				goto startup

//line cdcl.w:2366
			}

//line cdcl.w:2106
		}

//line cdcl.w:2089
	}

//line cdcl.w:2113
	if s.trace != nil {

//line cdcl.w:2133
		t := make([]Lit, eptr)
		for i := 0; i < eptr; i++ {
			t[i] = Lit(trail[i])
		}
		s.trace(llevel>>1, t)

//line cdcl.w:2115
	}

//line cdcl.w:2466
	l = 0
	for ai > 0 && acheck[ai-1] > llevel {
		ai--
	}
	for ; ai < len(asm); ai++ {

//line cdcl.w:2479
		t = 0
		if ai > 0 {
			t = acheck[ai-1]
		}
		mems++
		u = int(asm[ai])
		v = vmem[u>>1].value
//line cdcl.w:2484
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

//line cdcl.w:2472
	}

//line cdcl.w:2117
	llevel += 2
	if l == 0 {

//line cdcl.w:1119
		h = 0
		if randProbThresh != 0 {
			mems += 4
			h = int(rng.Next())
//line cdcl.w:1122
			if h < randProbThresh {

//line cdcl.w:635
				t = 0x80000000 - 0x80000000%hn
				for {
					mems += 4
					r = int(rng.Next())
//line cdcl.w:638
					if r < t {
						break
					}
				}
				h = r % hn

//line cdcl.w:1124
				mems++
				v = heap[h]
//line cdcl.w:1125
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
//line cdcl.w:1136

//line cdcl.w:1086
				mems++
				vmem[v].hloc = -1
//line cdcl.w:1087
				hn--
				if hn != 0 {
					mems++
					u = heap[hn]
//line cdcl.w:1090
					mems++
					au = vmem[u].activity
//line cdcl.w:1091
					for h, hp = 0, 1; hp < hn; h, hp = hp, 2*hp+1 {

//line cdcl.w:1104
						mems += 2
						av = vmem[heap[hp]].activity
//line cdcl.w:1105
						if hp+1 < hn {
							mems += 2
							if vmem[heap[hp+1]].activity > av {
								hp++
								av = vmem[heap[hp]].activity
//line cdcl.w:1109
							}
						}

//line cdcl.w:1093
						if au >= av {
							break
						}
						mems++
						heap[h] = heap[hp]
//line cdcl.w:1097
						mems++
						vmem[heap[hp]].hloc = h
//line cdcl.w:1098
					}
					mems++
					heap[h] = u
//line cdcl.w:1100
					mems++
					vmem[u].hloc = h
//line cdcl.w:1101
				}

//line cdcl.w:1137
				mems++
				if vmem[v].value == unset {
					break
				}
			}
		}
		mems++
		l = v + v + vmem[v].oldval&1

//line cdcl.w:2120
	}
	mems++
	lmem[l].reason = 0
//line cdcl.w:2122
	nodes++
	mems++
	leveldat[llevel] = eptr
//line cdcl.w:2124
	mems++
	trail[eptr] = l
	eptr++
//line cdcl.w:2125
	mems++
	vmem[l>>1].tloc = lptr
//line cdcl.w:2126
	vmem[l>>1].value = llevel + l&1
	agility -= agility >> 13

//line cdcl.w:2091
	goto proceed

//line cdcl.w:2269
finishFull:
	if totalLearned >= nextRecycle {

//line cdcl.w:1830
		recyclePoint = maxLearned
		minrange, maxrange = buckets, 0
		asserts = 0
		for k = 0; k < vars; k++ {
			mems++
			levstamp[k+k+1] = 0
//line cdcl.w:1835
		}
		for h, c = 0, firstLearned; c < maxLearned; h, c = h+1, endc+learnedExtra {
			mems++
			endc = c + int(mem[c-1])
//line cdcl.w:1838

//line cdcl.w:1778
			mems++
			l = int(mem[c])
//line cdcl.w:1779
			mems++
			if lmem[l].reason == c {
				mems++
				if vmem[l>>1].value&^1 != 0 {
					mems++
					mem[c-4] = 0
					asserts++
//line cdcl.w:1784
				} else {
					v = buckets + 1
					mems++
					mem[c-4] = buckets + 1
//line cdcl.w:1787
					goto rangeSet
				}
			} else {

//line cdcl.w:1804
				p, q = 0, 0
				for k = c + int(mem[c-1]) - 1; k >= c; k-- {
					mems += 2
					l = int(mem[k])
					v = vmem[l>>1].value
//line cdcl.w:1807
					if v < 2 {
						if (v^l)&1 != 0 {
							continue
						}
						v = buckets + 1
						mems++
						mem[c-4] = buckets + 1
//line cdcl.w:1813
						goto rangeSet
					}
					mems++
					if levstamp[(v&^1)+1] < c {
						mems++
						levstamp[(v&^1)+1] = c
						q++
//line cdcl.w:1818
					}
					if levstamp[(v&^1)+1] == c && (l^v)&1 == 0 {
						mems++
						levstamp[(v&^1)+1] = c + 1
						p++
//line cdcl.w:1821
					}
				}

//line cdcl.w:1791
				v = int(buckets / badlevel * float64(float32(p)+float32(par.Alpha*float32(q-p))))
				if v >= buckets {
					v = buckets - 1
				}
				mems++
				mem[c-4] = uint32(v)
//line cdcl.w:1796
				minrange, maxrange = min(minrange, v), max(maxrange, v)
				mems += 2
				rangedist[v]++
//line cdcl.w:1798
			}
		rangeSet:

//line cdcl.w:1839

//line cdcl.w:1847
			for {
				mems++
				if mem[endc]&signBit == 0 {
					break
				}
				endc++
			}

//line cdcl.w:1840
		}
		budget = h / 2
		prevLearned = 0

//line cdcl.w:2272
	} else {
		warmupCycles++
	}
	mems++
	leveldat[llevel+2] = eptr
//line cdcl.w:2276
	minjumplev = maxLit
learnFull:
	if conflictLevel == 0 {
		goto learnedFull
	}
	mems++
	jumplev = conflictLevel
	conflictLevel = conflictdat[conflictLevel]
//line cdcl.w:2282

//line cdcl.w:2215
	mems++
	k = leveldat[jumplev+2]
//line cdcl.w:2216
	for eptr > k {
		eptr--
		mems++
		l = trail[eptr]
		v = l >> 1
//line cdcl.w:2218
		mems += 2
		vmem[v].oldval = vmem[v].value
//line cdcl.w:2219
		mems++
		vmem[v].value = unset
//line cdcl.w:2220
		mems++
		lmem[l].reason = 0
//line cdcl.w:2221
		if eptr < lptr {
			mems++
			if vmem[v].hloc < 0 {

//line cdcl.w:1073
				mems++
				av = vmem[v].activity
//line cdcl.w:1074
				h = hn
				hn++
				j = 0
//line cdcl.w:1075
				if h > 0 {

//line cdcl.w:1049
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:1051
					mems++
					if vmem[u].activity < av {
						for {
							mems++
							heap[h] = u
//line cdcl.w:1055
							mems++
							vmem[u].hloc = h
//line cdcl.w:1056
							h = hp
							if h == 0 {
								break
							}
							hp = (h - 1) >> 1
							mems++
							u = heap[hp]
//line cdcl.w:1062
							mems++
							if vmem[u].activity >= av {
								break
							}
						}
						mems++
						heap[h] = v
//line cdcl.w:1068
						mems++
						vmem[v].hloc = h
//line cdcl.w:1069
						j = 1
					}

//line cdcl.w:1077
				}
				if j == 0 {
					mems += 2
					heap[h] = v
					vmem[v].hloc = h
//line cdcl.w:1080
				}

//line cdcl.w:2225
			}
		}
	}
	lptr = eptr
	llevel = jumplev

//line cdcl.w:2283
	mems++
	c = leveldat[llevel+1]
//line cdcl.w:2284
	if c < 0 {
		mems++
		l = -c
		ll = conflictdat[llevel+1]
//line cdcl.w:2286
	}
	goto prepClause
storeClause:

//line cdcl.w:2300
	if trivialLearning && conflictLevel != 0 {
		cellsPrelearned -= float64(prelearnedSize)
		cellsLearned -= float64(learnedSize)
		totalLearned--
		trivials--
//line cdcl.w:2303
	} else {
		if jumplev <= minjumplev {
			if jumplev < minjumplev {
				minjumplev = jumplev
				nextLearned = 0
//line cdcl.w:2307
			}
			mems++
			conflictdat[llevel] = nextLearned
			conflictdat[llevel+1] = lll
//line cdcl.w:2309
			nextLearned = llevel
		}
		if learnedSize == 1 {
			mems++
			leveldat[llevel+1] = 0
//line cdcl.w:2313
			if s.proof != nil {
				s.writeProof([]uint32{uint32(lll)}, false)
			}
		} else {

//line cdcl.w:1638
			if prevLearned != 0 {
				mems++
				l = int(mem[prevLearned])
//line cdcl.w:1640
				if !trivialLearning {
					mems++
					if lmem[l].reason == 0 {
						mems++
						if vmem[l>>1].value == unset {

//line cdcl.w:1669
							mems++
							for k, q = int(mem[prevLearned-1])-1, learnedSize; q != 0 && k >= q; k-- {
								mems += 2
								l = int(mem[prevLearned+k])
								r = vmem[l>>1].value &^ 1
//line cdcl.w:1672
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
//line cdcl.w:1683
								mems++
								l = int(mem[c])
								r = int(mem[c-2])
//line cdcl.w:1684

//line cdcl.w:1428
								mems++
								for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
									mems++
									p = int(mem[wa])
//line cdcl.w:1431
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
//line cdcl.w:1440
								} else if p == l {
									mems++
									mem[q-2] = uint32(r)
//line cdcl.w:1442
								} else {
									mems++
									mem[q-3] = uint32(r)
//line cdcl.w:1444
								}

//line cdcl.w:1685
								mems += 2
								l = int(mem[c+1])
								r = int(mem[c-3])
//line cdcl.w:1686

//line cdcl.w:1428
								mems++
								for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
									mems++
									p = int(mem[wa])
//line cdcl.w:1431
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
//line cdcl.w:1440
								} else if p == l {
									mems++
									mem[q-2] = uint32(r)
//line cdcl.w:1442
								} else {
									mems++
									mem[q-3] = uint32(r)
//line cdcl.w:1444
								}

//line cdcl.w:1687
							}

//line cdcl.w:1646
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

//line cdcl.w:687
				if maxCellsUsed > len(mem) {
					grown := make([]uint32, min(memsize, max(2*len(mem), maxCellsUsed)))
					copy(grown, mem)
					mem = grown
				}

//line cdcl.w:1660
			}
			mems++
			mem[c+learnedSize] = 0

//line cdcl.w:1694
			if mem[c-5] != 0 {
				panic("sat: 이럴 수는 없다 (bumps)")
			}
			mem[c-1] = uint32(learnedSize)
			mems++
			mem[c] = uint32(lll)
//line cdcl.w:1699
			mems += 2
			mem[c-2] = uint32(lmem[lll].watch)
//line cdcl.w:1700
			mems++
			lmem[lll].watch = c
//line cdcl.w:1701
			if trivialLearning {
				for j, k = 1, jumplev; k != 0; j, k = j+1, k-2 {
					mems += 2
					l = trail[leveldat[k]] ^ 1
//line cdcl.w:1704
					if j == 1 {
						mems += 3
						mem[c-3] = uint32(lmem[l].watch)
						lmem[l].watch = c
//line cdcl.w:1706
					}
					mems++
					mem[c+j] = uint32(l)
//line cdcl.w:1708
				}
			} else {

//line cdcl.w:1714
				for k, j, jj = 1, 0, 1; k < learnedSize; j++ {
					mems++
					l = learn[j]
//line cdcl.w:1716
					mems++
					if vmem[l>>1].stamp == curstamp {
						mems++
						r = vmem[l>>1].value
//line cdcl.w:1719
						if jj != 0 && r >= jumplev {
							mems++
							mem[c+1] = uint32(l)
//line cdcl.w:1721
							mems += 2
							mem[c-3] = uint32(lmem[l].watch)
//line cdcl.w:1722
							mems++
							lmem[l].watch = c
//line cdcl.w:1723
							jj = 0
						} else {
							mems++
							mem[c+k+jj] = uint32(l)
//line cdcl.w:1726
						}
						k++
					}
				}

//line cdcl.w:1711
			}

//line cdcl.w:1625
			prevLearned = c
			if s.proof != nil && learnedSize <= par.LearnSave {
				s.writeProof(mem[c:c+learnedSize], false)
			}

//line cdcl.w:2318
			mems++
			leveldat[llevel+1] = c
//line cdcl.w:2319
		}
	}

//line cdcl.w:2290
	goto learnFull
learnedFull:

//line cdcl.w:2325
	if recyclePoint != 0 {
		jumplev = 0
	} else {
		jumplev = minjumplev
	}

//line cdcl.w:2215
	mems++
	k = leveldat[jumplev+2]
//line cdcl.w:2216
	for eptr > k {
		eptr--
		mems++
		l = trail[eptr]
		v = l >> 1
//line cdcl.w:2218
		mems += 2
		vmem[v].oldval = vmem[v].value
//line cdcl.w:2219
		mems++
		vmem[v].value = unset
//line cdcl.w:2220
		mems++
		lmem[l].reason = 0
//line cdcl.w:2221
		if eptr < lptr {
			mems++
			if vmem[v].hloc < 0 {

//line cdcl.w:1073
				mems++
				av = vmem[v].activity
//line cdcl.w:1074
				h = hn
				hn++
				j = 0
//line cdcl.w:1075
				if h > 0 {

//line cdcl.w:1049
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:1051
					mems++
					if vmem[u].activity < av {
						for {
							mems++
							heap[h] = u
//line cdcl.w:1055
							mems++
							vmem[u].hloc = h
//line cdcl.w:1056
							h = hp
							if h == 0 {
								break
							}
							hp = (h - 1) >> 1
							mems++
							u = heap[hp]
//line cdcl.w:1062
							mems++
							if vmem[u].activity >= av {
								break
							}
						}
						mems++
						heap[h] = v
//line cdcl.w:1068
						mems++
						vmem[v].hloc = h
//line cdcl.w:1069
						j = 1
					}

//line cdcl.w:1077
				}
				if j == 0 {
					mems += 2
					heap[h] = v
					vmem[v].hloc = h
//line cdcl.w:1080
				}

//line cdcl.w:2225
			}
		}
	}
	lptr = eptr
	llevel = jumplev

//line cdcl.w:2331
	if jumplev == minjumplev {

//line cdcl.w:2342
		for nextLearned != 0 {
			mems++
			lll = conflictdat[nextLearned+1]
//line cdcl.w:2344
			mems++
			c = leveldat[nextLearned+1]
//line cdcl.w:2345
			nextLearned = conflictdat[nextLearned]
			mems++
			vmem[lll>>1].value = llevel + lll&1
			vmem[lll>>1].tloc = eptr
//line cdcl.w:2347
			mems++
			lmem[lll].reason = c
//line cdcl.w:2348
			mems++
			trail[eptr] = lll
			eptr++
//line cdcl.w:2349
		}

//line cdcl.w:2333
	}

//line cdcl.w:1190
	varBump *= varBumpFactor
	clauseBump *= clauseBumpFactor

//line cdcl.w:2335
	if recyclePoint != 0 {

//line cdcl.w:1870
		mems++
		j = minrange
		sz = asserts + rangedist[j]
//line cdcl.w:1871
		for sz < budget && j < maxrange {
			j++
			mems++
			sz += rangedist[j]
//line cdcl.w:1873
		}
		if sz > budget {

//line cdcl.w:1941
			t = sz - budget
			jj = min(rangedist[j]-t, clauseHeapSize)
			if jj <= 0 {
				j--
			} else {

//line cdcl.w:1956
				for h, c = 0, firstLearned; h < jj; c = endc + learnedExtra {
					if c >= recyclePoint {
						panic("sat: 이럴 수는 없다 (rangedist1)")
					}
					mems++
					endc = c + int(mem[c-1])
//line cdcl.w:1961

//line cdcl.w:1847
					for {
						mems++
						if mem[endc]&signBit == 0 {
							break
						}
						endc++
					}

//line cdcl.w:1962
					mems++
					if int(mem[c-4]) == j {
						clauseHeap[h] = uint64(mem[c-5])<<32 + uint64(c)
						h++
//line cdcl.w:1965
					}
				}

//line cdcl.w:1947

//line cdcl.w:1969
				for h = jj >> 1; h != 0; {
					q = h + h
					h--
					p = h
//line cdcl.w:1971
					mems++
					accum = clauseHeap[p]
//line cdcl.w:1972

//line cdcl.w:1978
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
//line cdcl.w:1991
						p, q = q, q+q+2
					}
					mems++
					clauseHeap[p] = accum

//line cdcl.w:1973
				}

//line cdcl.w:1948

//line cdcl.w:1999
				for ; ; c = endc + learnedExtra {
					if c >= recyclePoint {
						panic("sat: 이럴 수는 없다 (rangedist2)")
					}
					mems++
					if int(mem[c-4]) == j {
						mems++
						accum = uint64(mem[c-5])<<32 + uint64(c)
//line cdcl.w:2006
						mems++
						if accum < clauseHeap[0] {
							mems++
							mem[c-4] = uint32(j + 1)
//line cdcl.w:2009
							if t--; t == 0 {
								break
							}
						} else {
							mems++
							mem[int(clauseHeap[0]&0xffffffff)-4] = uint32(j + 1)
//line cdcl.w:2014
							if t--; t == 0 {
								break
							}
							p, q = 0, 2

//line cdcl.w:1978
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
//line cdcl.w:1991
								p, q = q, q+q+2
							}
							mems++
							clauseHeap[p] = accum

//line cdcl.w:2019
						}
					}
					mems++
					endc = c + int(mem[c-1])
//line cdcl.w:2022

//line cdcl.w:1847
					for {
						mems++
						if mem[endc]&signBit == 0 {
							break
						}
						endc++
					}

//line cdcl.w:2023
				}

//line cdcl.w:1949
			}

//line cdcl.w:1876
		}
		for k = minrange >> 1; k+k <= maxrange; k++ {
			mems++
			rangedist[k+k] = 0
			rangedist[k+k+1] = 0
//line cdcl.w:1879
		}
		for h, cc, c = 0, firstLearned, firstLearned; c < maxLearned; c = endc + learnedExtra {

//line cdcl.w:1890
			mems++
			endc = c + int(mem[c-1])
			jj = endc
//line cdcl.w:1891
			for {
				mems++
				if mem[endc]&signBit == 0 {
					break
				}
				mems++
				mem[endc] = 0
				endc++
//line cdcl.w:1897
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
//line cdcl.w:1906
				mems++
				v = vmem[l>>1].value
//line cdcl.w:1907
				if v != unset {
					if (v^l)&1 != 0 {
						continue
					}
					break
				}
				mems++
				mem[kk] = uint32(l)
				kk++
//line cdcl.w:1914
			}
			if k < jj {
				continue
			}
			h++

//line cdcl.w:2031
			if kk >= cc+2 {
				mems += 3
				mem[cc-1] = uint32(kk - cc)
				mem[cc-5] = mem[c-5]
				cc = kk + learnedExtra
//line cdcl.w:2033
			} else if kk == cc {
				goto unsat
			} else {
				mems++
				l = int(mem[cc])
//line cdcl.w:2037
				mems++
				vmem[l>>1].value = l & 1
				vmem[l>>1].tloc = eptr
//line cdcl.w:2038
				mems++
				trail[eptr] = l
				eptr++
//line cdcl.w:2039
			}

//line cdcl.w:1882
		}
		maxLearned = cc
		prevLearned = 0
//line cdcl.w:1884
		mems++
		mem[maxLearned-learnedExtra] = 0

//line cdcl.w:2046
		for l = 2; l <= maxLit; l++ {
			mems++
			lmem[l].watch = 0
//line cdcl.w:2048
		}
		for c = clauseExtra; c < minLearned; c = endc + clauseExtra {
			mems++
			endc = c + int(mem[c-1])
//line cdcl.w:2051

//line cdcl.w:2060
			mems++
			l = int(mem[c])
//line cdcl.w:2061
			mems += 3
			mem[c-2] = uint32(lmem[l].watch)
			lmem[l].watch = c
//line cdcl.w:2062
			l = int(mem[c+1])
			mems += 3
			mem[c-3] = uint32(lmem[l].watch)
			lmem[l].watch = c

//line cdcl.w:2052

//line cdcl.w:1847
			for {
				mems++
				if mem[endc]&signBit == 0 {
					break
				}
				endc++
			}

//line cdcl.w:2053
		}
		for c = firstLearned; c < maxLearned; c = endc + learnedExtra {
			mems++
			endc = c + int(mem[c-1])
//line cdcl.w:2056

//line cdcl.w:2060
			mems++
			l = int(mem[c])
//line cdcl.w:2061
			mems += 3
			mem[c-2] = uint32(lmem[l].watch)
			lmem[l].watch = c
//line cdcl.w:2062
			l = int(mem[c+1])
			mems += 3
			mem[c-3] = uint32(lmem[l].watch)
			lmem[l].watch = c

//line cdcl.w:2057
		}

//line cdcl.w:1858
		recyclePoint = 0

//line cdcl.w:2337
		recycleBump += par.RecycleInc
		nextRecycle = min(totalLearned+recycleBump, doomsday)
	}

//line cdcl.w:2293
	goto startup

//line cdcl.w:2237
confl:
	if llevel == 0 {
		goto unsat
	}
prepClause:

//line cdcl.w:1230
	oldptr, jumplev, xnew, clevels = 0, 0, 0, 0

//line cdcl.w:1287
	if curstamp >= 0xfffffffe {
		for k = 1; k <= vars; k++ {
			mems += 2
			vmem[k].stamp = 0
			levstamp[k+k-2] = 0
//line cdcl.w:1290
		}
		curstamp = 1
	} else {
		curstamp += 3
	}

//line cdcl.w:1232
	if c < 0 {

//line cdcl.w:1271
		mems++
		tl = vmem[ll>>1].tloc
//line cdcl.w:1272
		mems++
		vmem[ll>>1].stamp = curstamp
//line cdcl.w:1273
		l = ll

//line cdcl.w:1033
		v = l >> 1
		mems++
		av = vmem[v].activity + varBump
//line cdcl.w:1035
		mems++
		vmem[v].activity = av
//line cdcl.w:1036
		if av >= 1e100 {

//line cdcl.w:1151
			for vv := 1; vv <= vars; vv++ {
				mems++
				a := vmem[vv].activity
//line cdcl.w:1153
				if a != 0 {
					mems++
					vmem[vv].activity = max(a*1e-100, tiny)
//line cdcl.w:1155
				}
			}
			varBump *= 1e-100

//line cdcl.w:1038
		}
		mems++
		h = vmem[v].hloc
//line cdcl.w:1040
		if h > 0 {

//line cdcl.w:1049
			hp = (h - 1) >> 1
			mems++
			u = heap[hp]
//line cdcl.w:1051
			mems++
			if vmem[u].activity < av {
				for {
					mems++
					heap[h] = u
//line cdcl.w:1055
					mems++
					vmem[u].hloc = h
//line cdcl.w:1056
					h = hp
					if h == 0 {
						break
					}
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:1062
					mems++
					if vmem[u].activity >= av {
						break
					}
				}
				mems++
				heap[h] = v
//line cdcl.w:1068
				mems++
				vmem[v].hloc = h
//line cdcl.w:1069
				j = 1
			}

//line cdcl.w:1042
		}

//line cdcl.w:1275
		l = -c
		mems++
		if vmem[l>>1].tloc > tl {
			tl = vmem[l>>1].tloc
		}
		mems++
		vmem[l>>1].stamp = curstamp

//line cdcl.w:1033
		v = l >> 1
		mems++
		av = vmem[v].activity + varBump
//line cdcl.w:1035
		mems++
		vmem[v].activity = av
//line cdcl.w:1036
		if av >= 1e100 {

//line cdcl.w:1151
			for vv := 1; vv <= vars; vv++ {
				mems++
				a := vmem[vv].activity
//line cdcl.w:1153
				if a != 0 {
					mems++
					vmem[vv].activity = max(a*1e-100, tiny)
//line cdcl.w:1155
				}
			}
			varBump *= 1e-100

//line cdcl.w:1038
		}
		mems++
		h = vmem[v].hloc
//line cdcl.w:1040
		if h > 0 {

//line cdcl.w:1049
			hp = (h - 1) >> 1
			mems++
			u = heap[hp]
//line cdcl.w:1051
			mems++
			if vmem[u].activity < av {
				for {
					mems++
					heap[h] = u
//line cdcl.w:1055
					mems++
					vmem[u].hloc = h
//line cdcl.w:1056
					h = hp
					if h == 0 {
						break
					}
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:1062
					mems++
					if vmem[u].activity >= av {
						break
					}
				}
				mems++
				heap[h] = v
//line cdcl.w:1068
				mems++
				vmem[v].hloc = h
//line cdcl.w:1069
				j = 1
			}

//line cdcl.w:1042
		}

//line cdcl.w:1282
		xnew = 1

//line cdcl.w:1234
	} else {

//line cdcl.w:1253
		tl, xnew = 0, -1
		if c >= firstLearned && c < maxLearned {

//line cdcl.w:1163
			mems++
			ac = math.Float32frombits(mem[c-5]) + clauseBump
//line cdcl.w:1164
			mems++
			mem[c-5] = math.Float32bits(ac)
//line cdcl.w:1165
			if ac >= 1e20 {

//line cdcl.w:1170
				for c2 := firstLearned; c2 < maxLearned; {
					mems++
					e2 := c2 + int(mem[c2-1])
//line cdcl.w:1172
					mems++
					a := float64(math.Float32frombits(mem[c2-5]))
//line cdcl.w:1173
					if a != 0 {
						mems++
						mem[c2-5] = math.Float32bits(float32(max(a*1e-20, singleTiny)))
//line cdcl.w:1175
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

//line cdcl.w:1167
			}

//line cdcl.w:1256
		}
		mems++
		sz = int(mem[c-1])
//line cdcl.w:1258
		for k = c + sz - 1; k >= c; k-- {
			mems++
			l = int(mem[k]) ^ 1
//line cdcl.w:1260
			j = vmem[l>>1].tloc
			if j > tl {
				tl = j
			}

//line cdcl.w:1359
			mems++
			jj = vmem[l>>1].value &^ 1
//line cdcl.w:1360
			mems++
			vmem[l>>1].stamp = curstamp

//line cdcl.w:1033
			v = l >> 1
			mems++
			av = vmem[v].activity + varBump
//line cdcl.w:1035
			mems++
			vmem[v].activity = av
//line cdcl.w:1036
			if av >= 1e100 {

//line cdcl.w:1151
				for vv := 1; vv <= vars; vv++ {
					mems++
					a := vmem[vv].activity
//line cdcl.w:1153
					if a != 0 {
						mems++
						vmem[vv].activity = max(a*1e-100, tiny)
//line cdcl.w:1155
					}
				}
				varBump *= 1e-100

//line cdcl.w:1038
			}
			mems++
			h = vmem[v].hloc
//line cdcl.w:1040
			if h > 0 {

//line cdcl.w:1049
				hp = (h - 1) >> 1
				mems++
				u = heap[hp]
//line cdcl.w:1051
				mems++
				if vmem[u].activity < av {
					for {
						mems++
						heap[h] = u
//line cdcl.w:1055
						mems++
						vmem[u].hloc = h
//line cdcl.w:1056
						h = hp
						if h == 0 {
							break
						}
						hp = (h - 1) >> 1
						mems++
						u = heap[hp]
//line cdcl.w:1062
						mems++
						if vmem[u].activity >= av {
							break
						}
					}
					mems++
					heap[h] = v
//line cdcl.w:1068
					mems++
					vmem[v].hloc = h
//line cdcl.w:1069
					j = 1
				}

//line cdcl.w:1042
			}

//line cdcl.w:1362
			if jj >= llevel {
				xnew++
			} else {
				if jj > jumplev {
					jumplev = jj
				}
				mems++
				learn[oldptr] = l ^ 1
				oldptr++
//line cdcl.w:1369
				mems++
				if levstamp[jj] < curstamp {
					mems++
					levstamp[jj] = curstamp
					clevels++
//line cdcl.w:1372
				} else if levstamp[jj] == curstamp {
					mems++
					levstamp[jj] = curstamp + 1
//line cdcl.w:1374
				}
			}

//line cdcl.w:1265
		}

//line cdcl.w:1236
	}

//line cdcl.w:1316
	for xnew != 0 {
		for {
			mems++
			l = trail[tl]
			tl--
//line cdcl.w:1319
			mems++
			if vmem[l>>1].stamp == curstamp {
				break
			}
		}
		xnew--

//line cdcl.w:1329
		mems++
		c = lmem[l].reason
//line cdcl.w:1330
		if c < 0 {
			l = -c
			mems++
			if vmem[l>>1].stamp != curstamp {

//line cdcl.w:1359
				mems++
				jj = vmem[l>>1].value &^ 1
//line cdcl.w:1360
				mems++
				vmem[l>>1].stamp = curstamp

//line cdcl.w:1033
				v = l >> 1
				mems++
				av = vmem[v].activity + varBump
//line cdcl.w:1035
				mems++
				vmem[v].activity = av
//line cdcl.w:1036
				if av >= 1e100 {

//line cdcl.w:1151
					for vv := 1; vv <= vars; vv++ {
						mems++
						a := vmem[vv].activity
//line cdcl.w:1153
						if a != 0 {
							mems++
							vmem[vv].activity = max(a*1e-100, tiny)
//line cdcl.w:1155
						}
					}
					varBump *= 1e-100

//line cdcl.w:1038
				}
				mems++
				h = vmem[v].hloc
//line cdcl.w:1040
				if h > 0 {

//line cdcl.w:1049
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:1051
					mems++
					if vmem[u].activity < av {
						for {
							mems++
							heap[h] = u
//line cdcl.w:1055
							mems++
							vmem[u].hloc = h
//line cdcl.w:1056
							h = hp
							if h == 0 {
								break
							}
							hp = (h - 1) >> 1
							mems++
							u = heap[hp]
//line cdcl.w:1062
							mems++
							if vmem[u].activity >= av {
								break
							}
						}
						mems++
						heap[h] = v
//line cdcl.w:1068
						mems++
						vmem[v].hloc = h
//line cdcl.w:1069
						j = 1
					}

//line cdcl.w:1042
				}

//line cdcl.w:1362
				if jj >= llevel {
					xnew++
				} else {
					if jj > jumplev {
						jumplev = jj
					}
					mems++
					learn[oldptr] = l ^ 1
					oldptr++
//line cdcl.w:1369
					mems++
					if levstamp[jj] < curstamp {
						mems++
						levstamp[jj] = curstamp
						clevels++
//line cdcl.w:1372
					} else if levstamp[jj] == curstamp {
						mems++
						levstamp[jj] = curstamp + 1
//line cdcl.w:1374
					}
				}

//line cdcl.w:1335
			}
		} else if c != 0 {
			if c >= firstLearned {

//line cdcl.w:1163
				mems++
				ac = math.Float32frombits(mem[c-5]) + clauseBump
//line cdcl.w:1164
				mems++
				mem[c-5] = math.Float32bits(ac)
//line cdcl.w:1165
				if ac >= 1e20 {

//line cdcl.w:1170
					for c2 := firstLearned; c2 < maxLearned; {
						mems++
						e2 := c2 + int(mem[c2-1])
//line cdcl.w:1172
						mems++
						a := float64(math.Float32frombits(mem[c2-5]))
//line cdcl.w:1173
						if a != 0 {
							mems++
							mem[c2-5] = math.Float32bits(float32(max(a*1e-20, singleTiny)))
//line cdcl.w:1175
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

//line cdcl.w:1167
				}

//line cdcl.w:1339
			}
			mems++
			sz = int(mem[c-1])
//line cdcl.w:1341
			for k = c + sz - 1; k > c; k-- {
				mems++
				l = int(mem[k]) ^ 1
//line cdcl.w:1343
				mems++
				if vmem[l>>1].stamp != curstamp {

//line cdcl.w:1359
					mems++
					jj = vmem[l>>1].value &^ 1
//line cdcl.w:1360
					mems++
					vmem[l>>1].stamp = curstamp

//line cdcl.w:1033
					v = l >> 1
					mems++
					av = vmem[v].activity + varBump
//line cdcl.w:1035
					mems++
					vmem[v].activity = av
//line cdcl.w:1036
					if av >= 1e100 {

//line cdcl.w:1151
						for vv := 1; vv <= vars; vv++ {
							mems++
							a := vmem[vv].activity
//line cdcl.w:1153
							if a != 0 {
								mems++
								vmem[vv].activity = max(a*1e-100, tiny)
//line cdcl.w:1155
							}
						}
						varBump *= 1e-100

//line cdcl.w:1038
					}
					mems++
					h = vmem[v].hloc
//line cdcl.w:1040
					if h > 0 {

//line cdcl.w:1049
						hp = (h - 1) >> 1
						mems++
						u = heap[hp]
//line cdcl.w:1051
						mems++
						if vmem[u].activity < av {
							for {
								mems++
								heap[h] = u
//line cdcl.w:1055
								mems++
								vmem[u].hloc = h
//line cdcl.w:1056
								h = hp
								if h == 0 {
									break
								}
								hp = (h - 1) >> 1
								mems++
								u = heap[hp]
//line cdcl.w:1062
								mems++
								if vmem[u].activity >= av {
									break
								}
							}
							mems++
							heap[h] = v
//line cdcl.w:1068
							mems++
							vmem[v].hloc = h
//line cdcl.w:1069
							j = 1
						}

//line cdcl.w:1042
					}

//line cdcl.w:1362
					if jj >= llevel {
						xnew++
					} else {
						if jj > jumplev {
							jumplev = jj
						}
						mems++
						learn[oldptr] = l ^ 1
						oldptr++
//line cdcl.w:1369
						mems++
						if levstamp[jj] < curstamp {
							mems++
							levstamp[jj] = curstamp
							clevels++
//line cdcl.w:1372
						} else if levstamp[jj] == curstamp {
							mems++
							levstamp[jj] = curstamp + 1
//line cdcl.w:1374
						}
					}

//line cdcl.w:1346
				}
			}
			if xnew+oldptr+1 < sz && xnew != 0 {

//line cdcl.w:1400
				l = int(mem[c])
				mems++
				sz--
				mem[c-1] = uint32(sz)
				subsumptions++
//line cdcl.w:1402
				if s.proof != nil && sz <= par.LearnSave {
					s.writeProof(mem[c+1:c+sz+1], true)
				}
				mems++
				r = int(mem[c-2])

//line cdcl.w:1428
				mems++
				for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
					mems++
					p = int(mem[wa])
//line cdcl.w:1431
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
//line cdcl.w:1440
				} else if p == l {
					mems++
					mem[q-2] = uint32(r)
//line cdcl.w:1442
				} else {
					mems++
					mem[q-3] = uint32(r)
//line cdcl.w:1444
				}

//line cdcl.w:1407
				mems++
				ll = int(mem[c+sz])
//line cdcl.w:1408
				for lll, k = ll, c+sz; ; k-- {
					mems++
					r = vmem[lll>>1].value &^ 1
//line cdcl.w:1410
					if r == llevel {
						break
					}
					mems++
					lll = int(mem[k-1])
//line cdcl.w:1414
				}
				if k == c+1 {
					panic("sat: 이럴 수는 없다 (on-the-fly subsumption)")
				}
				if lll != ll {
					mems++
					mem[k] = uint32(ll)
//line cdcl.w:1420
				}
				mems += 2
				mem[c+sz] = uint32(l) + signBit
				mem[c] = uint32(lll)
//line cdcl.w:1422
				mems += 3
				mem[c-2] = uint32(lmem[lll].watch)
				lmem[lll].watch = c

//line cdcl.w:1350
			}
		}

//line cdcl.w:1326
	}

//line cdcl.w:1238
	for {
		mems++
		l = trail[tl]
		tl--
//line cdcl.w:1240
		mems++
		if vmem[l>>1].stamp == curstamp {
			break
		}
	}
	lll = l ^ 1

//line cdcl.w:2243

//line cdcl.w:1466
	learnedSize = oldptr + 1
	cellsPrelearned += float64(learnedSize)
	prelearnedSize = learnedSize
//line cdcl.w:1468
	for kk = 0; kk < oldptr; kk++ {
		mems++
		l = learn[kk] ^ 1
//line cdcl.w:1470
		mems += 2
		st = levstamp[vmem[l>>1].value&^1]
//line cdcl.w:1471
		if st < curstamp+1 {
			continue
		}

//line cdcl.w:1489
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
//line cdcl.w:1499
		if c == 0 {
			goto clearStack
		}
		if c < 0 {

//line cdcl.w:1518
			l = -c ^ 1
			mems++
			st = vmem[l>>1].stamp
//line cdcl.w:1520
			if st >= curstamp {
				if st == curstamp+2 {
					goto clearStack
				}
			} else {
				mems++
				stack[stackptr] = ll
				stackptr++
//line cdcl.w:1526
				goto test
			}
			goto isRed

//line cdcl.w:1504
		}
		mems++
		k = c + int(mem[c-1]) - 1

//line cdcl.w:1535
	scan:
		if k <= c {
			goto isRed
		}
		mems += 2
		l = int(mem[k]) ^ 1
		st = vmem[l>>1].stamp
//line cdcl.w:1540
		if st >= curstamp {
			if st == curstamp+2 {
				goto clearStack
			}
			goto next
		}
		mems++
		st = vmem[l>>1].value &^ 1
//line cdcl.w:1547
		if st == 0 {
			goto next
		}
		mems++
		st = levstamp[st]
//line cdcl.w:1551
		if st < curstamp {
			mems++
			vmem[l>>1].stamp = curstamp + 2
//line cdcl.w:1553
			goto clearStack
		}
		mems++
		stack[stackptr] = k
		stack[stackptr+1] = ll
		stackptr += 2
//line cdcl.w:1556
		goto test
	next:
		k--
		goto scan

//line cdcl.w:1566
	isRed:
		mems++
		vmem[ll>>1].stamp = curstamp + 1
//line cdcl.w:1568
		if stackptr != 0 {
			mems += 2
			stackptr--
			ll = stack[stackptr]
			c = lmem[ll].reason
//line cdcl.w:1570
			if c < 0 {
				goto isRed
			}
			mems++
			stackptr--
			k = stack[stackptr]
//line cdcl.w:1574
			goto next
		}
		goto redundant

//line cdcl.w:1584
	clearStack:
		if stackptr != 0 {
			mems++
			vmem[ll>>1].stamp = curstamp + 2
//line cdcl.w:1587
			mems++
			stackptr--
			ll = stack[stackptr]
//line cdcl.w:1588
			mems++
			c = lmem[ll].reason
//line cdcl.w:1589
			if c > 0 {
				stackptr--
			}
			goto clearStack
		}

//line cdcl.w:1475
		continue
	redundant:
		learnedSize--
	}

//line cdcl.w:1601
	if learnedSize <= (jumplev>>1)+par.TrivialLimit {
		trivialLearning = false
	} else {
		trivialLearning = true
		clevels = jumplev >> 1
		learnedSize = clevels + 1
		trivials++
//line cdcl.w:1606
	}
	cellsLearned += float64(learnedSize)
	totalLearned++

//line cdcl.w:2244
	if fullRun {
		goto storeClause
	}

//line cdcl.w:2215
	mems++
	k = leveldat[jumplev+2]
//line cdcl.w:2216
	for eptr > k {
		eptr--
		mems++
		l = trail[eptr]
		v = l >> 1
//line cdcl.w:2218
		mems += 2
		vmem[v].oldval = vmem[v].value
//line cdcl.w:2219
		mems++
		vmem[v].value = unset
//line cdcl.w:2220
		mems++
		lmem[l].reason = 0
//line cdcl.w:2221
		if eptr < lptr {
			mems++
			if vmem[v].hloc < 0 {

//line cdcl.w:1073
				mems++
				av = vmem[v].activity
//line cdcl.w:1074
				h = hn
				hn++
				j = 0
//line cdcl.w:1075
				if h > 0 {

//line cdcl.w:1049
					hp = (h - 1) >> 1
					mems++
					u = heap[hp]
//line cdcl.w:1051
					mems++
					if vmem[u].activity < av {
						for {
							mems++
							heap[h] = u
//line cdcl.w:1055
							mems++
							vmem[u].hloc = h
//line cdcl.w:1056
							h = hp
							if h == 0 {
								break
							}
							hp = (h - 1) >> 1
							mems++
							u = heap[hp]
//line cdcl.w:1062
							mems++
							if vmem[u].activity >= av {
								break
							}
						}
						mems++
						heap[h] = v
//line cdcl.w:1068
						mems++
						vmem[v].hloc = h
//line cdcl.w:1069
						j = 1
					}

//line cdcl.w:1077
				}
				if j == 0 {
					mems += 2
					heap[h] = v
					vmem[v].hloc = h
//line cdcl.w:1080
				}

//line cdcl.w:2225
			}
		}
	}
	lptr = eptr
	llevel = jumplev

//line cdcl.w:2248
	if learnedSize > 1 {

//line cdcl.w:1638
		if prevLearned != 0 {
			mems++
			l = int(mem[prevLearned])
//line cdcl.w:1640
			if !trivialLearning {
				mems++
				if lmem[l].reason == 0 {
					mems++
					if vmem[l>>1].value == unset {

//line cdcl.w:1669
						mems++
						for k, q = int(mem[prevLearned-1])-1, learnedSize; q != 0 && k >= q; k-- {
							mems += 2
							l = int(mem[prevLearned+k])
							r = vmem[l>>1].value &^ 1
//line cdcl.w:1672
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
//line cdcl.w:1683
							mems++
							l = int(mem[c])
							r = int(mem[c-2])
//line cdcl.w:1684

//line cdcl.w:1428
							mems++
							for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
								mems++
								p = int(mem[wa])
//line cdcl.w:1431
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
//line cdcl.w:1440
							} else if p == l {
								mems++
								mem[q-2] = uint32(r)
//line cdcl.w:1442
							} else {
								mems++
								mem[q-3] = uint32(r)
//line cdcl.w:1444
							}

//line cdcl.w:1685
							mems += 2
							l = int(mem[c+1])
							r = int(mem[c-3])
//line cdcl.w:1686

//line cdcl.w:1428
							mems++
							for wa, q = lmem[l].watch, 0; wa != c; q, wa = wa, nextWa {
								mems++
								p = int(mem[wa])
//line cdcl.w:1431
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
//line cdcl.w:1440
							} else if p == l {
								mems++
								mem[q-2] = uint32(r)
//line cdcl.w:1442
							} else {
								mems++
								mem[q-3] = uint32(r)
//line cdcl.w:1444
							}

//line cdcl.w:1687
						}

//line cdcl.w:1646
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

//line cdcl.w:687
			if maxCellsUsed > len(mem) {
				grown := make([]uint32, min(memsize, max(2*len(mem), maxCellsUsed)))
				copy(grown, mem)
				mem = grown
			}

//line cdcl.w:1660
		}
		mems++
		mem[c+learnedSize] = 0

//line cdcl.w:1694
		if mem[c-5] != 0 {
			panic("sat: 이럴 수는 없다 (bumps)")
		}
		mem[c-1] = uint32(learnedSize)
		mems++
		mem[c] = uint32(lll)
//line cdcl.w:1699
		mems += 2
		mem[c-2] = uint32(lmem[lll].watch)
//line cdcl.w:1700
		mems++
		lmem[lll].watch = c
//line cdcl.w:1701
		if trivialLearning {
			for j, k = 1, jumplev; k != 0; j, k = j+1, k-2 {
				mems += 2
				l = trail[leveldat[k]] ^ 1
//line cdcl.w:1704
				if j == 1 {
					mems += 3
					mem[c-3] = uint32(lmem[l].watch)
					lmem[l].watch = c
//line cdcl.w:1706
				}
				mems++
				mem[c+j] = uint32(l)
//line cdcl.w:1708
			}
		} else {

//line cdcl.w:1714
			for k, j, jj = 1, 0, 1; k < learnedSize; j++ {
				mems++
				l = learn[j]
//line cdcl.w:1716
				mems++
				if vmem[l>>1].stamp == curstamp {
					mems++
					r = vmem[l>>1].value
//line cdcl.w:1719
					if jj != 0 && r >= jumplev {
						mems++
						mem[c+1] = uint32(l)
//line cdcl.w:1721
						mems += 2
						mem[c-3] = uint32(lmem[l].watch)
//line cdcl.w:1722
						mems++
						lmem[l].watch = c
//line cdcl.w:1723
						jj = 0
					} else {
						mems++
						mem[c+k+jj] = uint32(l)
//line cdcl.w:1726
					}
					k++
				}
			}

//line cdcl.w:1711
		}

//line cdcl.w:1625
		prevLearned = c
		if s.proof != nil && learnedSize <= par.LearnSave {
			s.writeProof(mem[c:c+learnedSize], false)
		}

//line cdcl.w:2250
		mems++
		lmem[lll].reason = c
//line cdcl.w:2251
	} else if s.proof != nil {
		s.writeProof([]uint32{uint32(lll)}, false)
	}
	mems++
	vmem[lll>>1].value = llevel + lll&1
	vmem[lll>>1].tloc = eptr
//line cdcl.w:2255
	mems++
	trail[eptr] = lll
	eptr++
//line cdcl.w:2256
	agility -= agility >> 13
	agility += 1 << 19

//line cdcl.w:1190
	varBump *= varBumpFactor
	clauseBump *= clauseBumpFactor

//line cdcl.w:2259
	goto proceed

//line cdcl.w:373
unsat:
	status, unsatisfiable = Unsat, true
	goto allDone
failed:

//line cdcl.w:1287
	if curstamp >= 0xfffffffe {
		for k = 1; k <= vars; k++ {
			mems += 2
			vmem[k].stamp = 0
			levstamp[k+k-2] = 0
//line cdcl.w:1290
		}
		curstamp = 1
	} else {
		curstamp += 3
	}

//line cdcl.w:2505
	mems++
	vmem[l>>1].stamp = curstamp
//line cdcl.w:2506
	if llevel != 0 {
		mems++
		t = leveldat[2]
//line cdcl.w:2508
		for j = eptr - 1; j >= t; j-- {
			mems++
			ll = trail[j]
//line cdcl.w:2510
			mems++
			if vmem[ll>>1].stamp != curstamp {
				continue
			}

//line cdcl.w:2522
			mems++
			c = lmem[ll].reason
//line cdcl.w:2523
			if c == 0 {
				mems++
				vmem[ll>>1].stamp = curstamp + 1
//line cdcl.w:2525
			} else if c < 0 {
				lll = -c

//line cdcl.w:2537
				mems++
				if vmem[lll>>1].value&^1 != 0 {
					mems++
					vmem[lll>>1].stamp = curstamp
//line cdcl.w:2540
				}

//line cdcl.w:2528
			} else {
				mems++
				sz = int(mem[c-1])
//line cdcl.w:2530
				for k = c + sz - 1; k > c; k-- {
					mems++
					lll = int(mem[k])
//line cdcl.w:2532

//line cdcl.w:2537
					mems++
					if vmem[lll>>1].value&^1 != 0 {
						mems++
						vmem[lll>>1].stamp = curstamp
//line cdcl.w:2540
					}

//line cdcl.w:2533
				}
			}

//line cdcl.w:2515
		}
	}

//line cdcl.w:2546
	for i = 0; i < len(asm); i++ {
		u = int(asm[i])
		v = u >> 1
//line cdcl.w:2548
		mems++
		if u == l {
			l = 0
		} else if vmem[v].stamp == curstamp+1 && (vmem[v].value^u)&1 == 0 {
			mems++
			vmem[v].stamp = curstamp + 2
//line cdcl.w:2553
		} else {
			continue
		}
		s.failed = append(s.failed, Lit(u))
	}

//line cdcl.w:378
	status = Unsat
	goto allDone
satisfied:
	status = Sat

//line cdcl.w:458
	s.model = make([]Lit, vars)
	s.truth = make([]bool, vars+1)
	for k = 0; k < vars; k++ {
		mems++
		s.model[k] = Lit(trail[k])
//line cdcl.w:462
		s.truth[trail[k]>>1] = trail[k]&1 == 0
	}

//line cdcl.w:383
allDone:

//line cdcl.w:466
	if status != Sat {
		s.model, s.truth = nil, nil
	}
	s.stats = Stats{IMems: imems, Mems: mems, Bytes: bytes, Nodes: nodes,
		Learned: totalLearned - learnedBase, CellsPrelearned: cellsPrelearned, CellsLearned: cellsLearned,
		MemCells: maxCellsUsed, Trivials: trivials, Discards: discards,
		Subsumptions: subsumptions, Restarts: actualRestarts}

//line cdcl.w:385

//line cdcl.w:2615
	if err == ErrMemory {
		s.state = nil
	} else {
		s.state = &cdclState{key: key, unsat: unsatisfiable, rng: rng,
			vars: vars, clauses: clauses, cells: cells, bytes: bytes,

//line cdcl.w:2625
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

//line cdcl.w:2621
		}
	}

//line cdcl.w:386
	return status, err
}

//line cdcl.w:2431
func (s *Solver) Failed() []Lit { return slices.Clone(s.failed) }
