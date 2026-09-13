//line simplify.w:41
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

//line simplify.w:63
type SimplifyParams struct {
	Seed      int    // \.s: 난수 씨앗 (0)
	MemMax    uint64 // \.m: |mem| 칸 수의 하한 (100000)
	Cutoff    int    // \.c: 두 부호가 모두 이보다 많이 나오면 소거하지 않는다 (10)
	Optimism  uint64 // \.C: $ab$가 $a+b$보다 이만큼 넘게 크면 소거하지 않는다 (25)
	Buckets   int    // \.B: 소거 후보를 가르는 차수의 상한 (32)
	MaxRounds int    // \.t: 소거를 되풀이하는 횟수의 상한
	Timeout   uint64 // \.T: mem 한도
}

//line simplify.w:74
var defaultSimplifyParams = SimplifyParams{
	MemMax:    100000,
	Cutoff:    10,
	Optimism:  25,
	Buckets:   32,
	MaxRounds: 0x7fffffff,
	Timeout:   0x1fffffffffffffff,
}

//line simplify.w:122
type SimplifyStats struct {
	IMems, Mems         uint64 // 준비와 전처리에 든 mem
	Bytes               uint64 // 자료 구조의 바이트 수 (원본의 크기로 셈)
	Cells               uint32 // |mem|에서 쓴 칸 수
	Subsumptions        uint32 // 포섭으로 지운 절의 수
	Strengthenings      uint32 // 강화한 절의 수
	SubTries, SubFalse  uint64 // 포섭 시도와 헛짚음
	StrTries, StrFalse  uint64 // 강화 시도와 헛짚음
	ElimTries, FuncDeps uint64 // 소거 시도와 함수적 종속을 찾은 수
	Vars, VarsGone      uint32 // 변수의 수와 없앤 변수의 수
	ClausesGone         uint32 // 없앤 절의 수
	Rounds              uint32 // 소거를 되풀이한 횟수
	Unsat               bool   // 만족할 수 없음을 밝혔는가
}

//line simplify.w:190
type preprocessed struct {
	cells []Lit     // 줄인 절들
	erp   []erpCell // 되돌리는 자료
	unsat bool      // 만족할 수 없음을 밝혔는가
}

type erpCell struct {
	lit  Lit
	flag uint8
}

const (
	erpFirst = 1 // 절의 첫 리터럴
	erpDef   = 2 // 값을 정할 리터럴
)

//line simplify.w:303
type simpCell struct {
	lit, cls              uint32 // 리터럴과 절 (머리에서는 표 참고)
	up, down, left, right uint32 // 세로와 가로의 이웃
	sig                   uint64 // 머리의 서명
}

//line simplify.w:313
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

//line simplify.w:87
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

//line simplify.w:138
func (s *Solver) SimplifyStats() SimplifyStats { return s.simpStats }

//line simplify.w:144
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

//line simplify.w:163
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

//line simplify.w:159
	return b.String()
}

//line simplify.w:178
func ratio(a, b uint64) float64 {
	if b == 0 {
		return 0
	}
	return float64(a) / float64(b)
}

//line simplify.w:218
func (s *Solver) Simplify(ctx context.Context) (Status, error) {

//line simplify.w:248
	var (
		b, c, cc, j, k, l, ll, p, pp, q, qq, r uint32
		sz, u, uu, v, vv, w, x                 uint32
		kv, cd, csave, t2, rbits, progress     uint32
		bits, bits2, ubits, ccbits, stbits     uint64
		specialcase                            int
		cur                                    int
	)

//line simplify.w:258
	var (
		status               Status
		err                  error
		par                  SimplifyParams
		rng                  *gbflip.RNG
		pre                  *preprocessed // 결과
		vars, clauses, cells uint32
		imems, mems, bytes   uint64
	)

//line simplify.w:335
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

//line simplify.w:575
	var nextCheck uint64 = checkEvery

//line simplify.w:734
	var (
		subTotal, strTotal                     uint32
		subTries, subFalse, strTries, strFalse uint64
	)

//line simplify.w:1042
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

//line simplify.w:220
	s.pre, s.simpStats = nil, SimplifyStats{}
	if s.empty {
		s.pre, s.simpStats.Unsat = &preprocessed{unsat: true}, true
		return Unsat, nil
	}
	if s.clauses == 0 {
		return Unknown, nil
	}

//line simplify.w:271
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

//line simplify.w:229

//line simplify.w:363
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

//line simplify.w:381
	for l = 2; l < litHeadTop; l++ {
		mems++
		mem[l].down = l
//line simplify.w:383
	}
	cur = len(s.cells)
	for c, j = clauses, clsHeadTop; c != 0; c-- {
		cc = c + litHeadTop - 1
		for {
			cur--
			x = uint32(s.cells[cur])
			p = x &^ uint32(firstLit)
			mems++
			mem[j].lit = p
			mem[j].cls = cc
//line simplify.w:392
			mems += 3
			mem[j].down = mem[p].down
			mem[p].down = j
			j++
//line simplify.w:393
			if x&uint32(firstLit) != 0 {
				break
			}
		}
		mems++
		mem[cc].left = cc
//line simplify.w:398
	}
	if j != clsHeadTop+cells {
		panic("sat: 이럴 수는 없다 (cells)")
	}

//line simplify.w:406
	for c = vars; c != 0; c-- {
		mems += 2
		vmem[c].stable = 0
		vmem[c].status = varNorm
//line simplify.w:408
	}

//line simplify.w:415
	for l = 2; l < litHeadTop; l++ {

//line simplify.w:426
		for j, k, sz = l, mem[l].down, 0; k >= litHeadTop; mems, j, k = mems+1, k, mem[k].down {
			mems++
			mem[k].up = j
//line simplify.w:428
			mems++
			c = mem[k].cls
//line simplify.w:429
			mems += 3
			mem[k].left = mem[c].left
			mem[c].left = k
//line simplify.w:430
			sz++
		}
		if k != l {
			panic("sat: 이럴 수는 없다 (lit init)")
		}
		mems++
		mem[l].lit = sz
		mem[l].cls = 0
//line simplify.w:436
		mems++
		mem[l].up = j
//line simplify.w:437
		if sz == 0 {
			w = l

//line simplify.w:502
			kv = w >> 1
			mems++
			if vmem[kv].status == varNorm {
				mems++
				if w&1 != 0 {
					vmem[kv].status = forcedTrue
				} else {
					vmem[kv].status = forcedFalse
				}
				vmem[kv].link = toDo
				toDo = kv
//line simplify.w:512
			} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
				mems++
				vmem[kv].status = elimQuiet
				vmem[kv].stable = 1
//line simplify.w:514
			}

//line simplify.w:440
		} else {

//line simplify.w:448
			if rbits < 0x40 {
				mems += 4
				rbits = uint32(rng.Next()) | 1<<30
//line simplify.w:450
			}
			mems++
			mem[l].sig = 1 << (rbits & 0x3f)
//line simplify.w:452
			rbits >>= 6
			if rbits < 0x40 {
				mems += 4
				rbits = uint32(rng.Next()) | 1<<30
//line simplify.w:455
			}
			mems++
			mem[l].sig |= 1 << (rbits & 0x3f)
//line simplify.w:457
			rbits >>= 6

//line simplify.w:442
		}

//line simplify.w:417
	}
	for c = l; c < clsHeadTop; c++ {

//line simplify.w:460
		bits = 0
		for j, k, sz = c, mem[c].left, 0; k >= clsHeadTop; mems, j, k = mems+1, k, mem[k].left {
			mems++
			mem[k].right = j
//line simplify.w:463
			mems++
			w = mem[k].lit
//line simplify.w:464
			mems++
			bits |= mem[w].sig
//line simplify.w:465
			sz++
		}
		if k != c {
			panic("sat: 이럴 수는 없다 (cls init)")
		}
		mems++
		mem[c].cls = sz
		mem[c].lit = 0
//line simplify.w:471
		mems += 2
		mem[c].sig = bits
		mem[c].right = j
//line simplify.w:472
		if sz <= 1 {

//line simplify.w:480
			kv = w >> 1
			mems++
			if w&1 != 0 {
				if vmem[kv].status == varNorm {
					mems++
					vmem[kv].status = forcedFalse
					vmem[kv].link = toDo
					toDo = kv
//line simplify.w:485
				} else if vmem[kv].status == forcedTrue {
					goto unsat
				}
			} else {
				if vmem[kv].status == varNorm {
					mems++
					vmem[kv].status = forcedTrue
					vmem[kv].link = toDo
					toDo = kv
//line simplify.w:491
				} else if vmem[kv].status == forcedFalse {
					goto unsat
				}
			}

//line simplify.w:474
		}

//line simplify.w:420
	}

//line simplify.w:519
	lmem = make([]uint64, litHeadTop)
	for l = 0; l < litHeadTop; l++ {
		mems++
		lmem[l] = 0
//line simplify.w:522
	}
	cmem = make([]simpClause, clauses)
	if par.Buckets < 2 {
		par.Buckets = 2
	}
	bucket = make([]uint32, par.Buckets+1)
	bytes += uint64(litHeadTop)*8 + uint64(clauses)*8 + uint64(par.Buckets+1)*4

//line simplify.w:230
	imems, mems = mems, 0

//line simplify.w:1315
	mems++
	cmem[0].link = sentinel
	cmem[0].size = 0
//line simplify.w:1316
	for c = litHeadTop + 1; c < clsHeadTop; c++ {
		mems++
		cmem[c-litHeadTop].link = c - 1
		cmem[c-litHeadTop].size = 0
//line simplify.w:1318
	}
	strengthened = c - 1

//line simplify.w:859
	csave = c

//line simplify.w:540
	for toDo != 0 {
		k = toDo
		mems++
		toDo = vmem[k].link
//line simplify.w:543
		if vmem[k].status != elimQuiet {
			if vmem[k].status == forcedTrue {
				l = k + k
			} else {
				l = k + k + 1
			}
			pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
			mems++
			vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
			for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
				mems++
				cd = mem[ll].cls
//line simplify.w:621
				for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
					if p != ll {
						mems++
						w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
						mems++
						q, r = mem[p].up, mem[p].down
//line simplify.w:639
						mems += 2
						mem[q].down = r
						mem[r].up = q
//line simplify.w:640
						mems++
						vmem[w>>1].stable = 0
//line simplify.w:641
						mems += 2
						mem[w].lit--
//line simplify.w:642
						if mem[w].lit == 0 {

//line simplify.w:502
							kv = w >> 1
							mems++
							if vmem[kv].status == varNorm {
								mems++
								if w&1 != 0 {
									vmem[kv].status = forcedTrue
								} else {
									vmem[kv].status = forcedFalse
								}
								vmem[kv].link = toDo
								toDo = kv
//line simplify.w:512
							} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
								mems++
								vmem[kv].status = elimQuiet
								vmem[kv].stable = 1
//line simplify.w:514
							}

//line simplify.w:644
						}

//line simplify.w:625
					}
				}
				mems++
				mem[mem[cd].right].left = avail
				avail = mem[cd].left
//line simplify.w:628
				mems++
				mem[cd].cls = 0
				clausesGone++
//line simplify.w:629
			}

//line simplify.w:552

//line simplify.w:582
			for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
				mems++
				cd = mem[ll].cls
//line simplify.w:584
				mems++
				p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
				mems += 2
				mem[p].right = q
				mem[q].left = p
//line simplify.w:586
				mems++
				mem[ll].left = avail
				avail = ll
//line simplify.w:587
				mems++
				j = mem[cd].cls - 1
//line simplify.w:588
				mems++
				mem[cd].cls = j
//line simplify.w:589
				if j == 1 {
					mems++
					if p == cd {
						w = mem[q].lit
					} else {
						w = mem[p].lit
					}

//line simplify.w:480
					kv = w >> 1
					mems++
					if w&1 != 0 {
						if vmem[kv].status == varNorm {
							mems++
							vmem[kv].status = forcedFalse
							vmem[kv].link = toDo
							toDo = kv
//line simplify.w:485
						} else if vmem[kv].status == forcedTrue {
							goto unsat
						}
					} else {
						if vmem[kv].status == varNorm {
							mems++
							vmem[kv].status = forcedTrue
							vmem[kv].link = toDo
							toDo = kv
//line simplify.w:491
						} else if vmem[kv].status == forcedFalse {
							goto unsat
						}
					}

//line simplify.w:597
				}

//line simplify.w:603
				bits2 = 0
				for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
					mems += 2
					bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
				}
				mems++
				mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
				mems++
				if cmem[cd-litHeadTop].link == 0 {
					mems++
					cmem[cd-litHeadTop].link = strengthened
					strengthened = cd
//line simplify.w:613
				}

//line simplify.w:600
			}

//line simplify.w:553
		}
		varsGone++
	}

//line simplify.w:562
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

//line simplify.w:861
	for strengthened != sentinel {
		c = strengthened
		mems++
		strengthened = cmem[c-litHeadTop].link
//line simplify.w:864
		mems++
		if mem[c].cls != 0 {
			mems++
			cmem[c-litHeadTop].link = 0
//line simplify.w:867

//line simplify.w:679
			mems += 3
			p = mem[c].right
			l = mem[p].lit
			k = mem[l].lit
//line simplify.w:680
			for mems, p = mems+1, mem[p].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
				mems++
				ll = mem[p].lit
//line simplify.w:682
				mems++
				if mem[ll].lit < k {
					k, l = mem[ll].lit, ll
				}
			}

//line simplify.w:655
			mems += 3
			sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
//line simplify.w:656
			for mems, pp = mems+1, mem[l].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
				mems++
				cc = mem[pp].cls
//line simplify.w:658
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

//line simplify.w:692
				mems++
				q, qq = v, mem[cc].left
//line simplify.w:693
				for {
					mems += 2
					l, ll = mem[q].lit, mem[qq].lit
//line simplify.w:695

//line simplify.w:712
					for l < ll {
						mems++
						qq = mem[qq].left
//line simplify.w:714
						if qq < clsHeadTop {
							ll = 0
						} else {
							mems++
							ll = mem[qq].lit
//line simplify.w:718
						}
					}

//line simplify.w:696
					if l > ll {
						break
					}
					mems++
					q = mem[q].left
//line simplify.w:700
					if q < clsHeadTop {
						l = 0
						break
					}
					mems++
					qq = mem[qq].left
//line simplify.w:705
					if qq < clsHeadTop {
						ll = 0
						break
					}
				}

//line simplify.w:671
				if l > ll {
					subFalse++
				} else {

//line simplify.w:722
					subTotal++
					for mems, p = mems+1, mem[cc].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
						mems++
						w = mem[p].lit
//line simplify.w:725

//line simplify.w:638
						mems++
						q, r = mem[p].up, mem[p].down
//line simplify.w:639
						mems += 2
						mem[q].down = r
						mem[r].up = q
//line simplify.w:640
						mems++
						vmem[w>>1].stable = 0
//line simplify.w:641
						mems += 2
						mem[w].lit--
//line simplify.w:642
						if mem[w].lit == 0 {

//line simplify.w:502
							kv = w >> 1
							mems++
							if vmem[kv].status == varNorm {
								mems++
								if w&1 != 0 {
									vmem[kv].status = forcedTrue
								} else {
									vmem[kv].status = forcedFalse
								}
								vmem[kv].link = toDo
								toDo = kv
//line simplify.w:512
							} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
								mems++
								vmem[kv].status = elimQuiet
								vmem[kv].stable = 1
//line simplify.w:514
							}

//line simplify.w:644
						}

//line simplify.w:726
					}
					mems++
					mem[mem[cc].right].left = avail
					avail = mem[cc].left
//line simplify.w:728
					mems++
					mem[cc].cls = 0
					clausesGone++

//line simplify.w:675
				}
			}

//line simplify.w:868

//line simplify.w:540
			for toDo != 0 {
				k = toDo
				mems++
				toDo = vmem[k].link
//line simplify.w:543
				if vmem[k].status != elimQuiet {
					if vmem[k].status == forcedTrue {
						l = k + k
					} else {
						l = k + k + 1
					}
					pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
					mems++
					vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
					for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
						mems++
						cd = mem[ll].cls
//line simplify.w:621
						for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
							if p != ll {
								mems++
								w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
								mems++
								q, r = mem[p].up, mem[p].down
//line simplify.w:639
								mems += 2
								mem[q].down = r
								mem[r].up = q
//line simplify.w:640
								mems++
								vmem[w>>1].stable = 0
//line simplify.w:641
								mems += 2
								mem[w].lit--
//line simplify.w:642
								if mem[w].lit == 0 {

//line simplify.w:502
									kv = w >> 1
									mems++
									if vmem[kv].status == varNorm {
										mems++
										if w&1 != 0 {
											vmem[kv].status = forcedTrue
										} else {
											vmem[kv].status = forcedFalse
										}
										vmem[kv].link = toDo
										toDo = kv
//line simplify.w:512
									} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
										mems++
										vmem[kv].status = elimQuiet
										vmem[kv].stable = 1
//line simplify.w:514
									}

//line simplify.w:644
								}

//line simplify.w:625
							}
						}
						mems++
						mem[mem[cd].right].left = avail
						avail = mem[cd].left
//line simplify.w:628
						mems++
						mem[cd].cls = 0
						clausesGone++
//line simplify.w:629
					}

//line simplify.w:552

//line simplify.w:582
					for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
						mems++
						cd = mem[ll].cls
//line simplify.w:584
						mems++
						p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
						mems += 2
						mem[p].right = q
						mem[q].left = p
//line simplify.w:586
						mems++
						mem[ll].left = avail
						avail = ll
//line simplify.w:587
						mems++
						j = mem[cd].cls - 1
//line simplify.w:588
						mems++
						mem[cd].cls = j
//line simplify.w:589
						if j == 1 {
							mems++
							if p == cd {
								w = mem[q].lit
							} else {
								w = mem[p].lit
							}

//line simplify.w:480
							kv = w >> 1
							mems++
							if w&1 != 0 {
								if vmem[kv].status == varNorm {
									mems++
									vmem[kv].status = forcedFalse
									vmem[kv].link = toDo
									toDo = kv
//line simplify.w:485
								} else if vmem[kv].status == forcedTrue {
									goto unsat
								}
							} else {
								if vmem[kv].status == varNorm {
									mems++
									vmem[kv].status = forcedTrue
									vmem[kv].link = toDo
									toDo = kv
//line simplify.w:491
								} else if vmem[kv].status == forcedFalse {
									goto unsat
								}
							}

//line simplify.w:597
						}

//line simplify.w:603
						bits2 = 0
						for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
							mems += 2
							bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
						}
						mems++
						mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
						mems++
						if cmem[cd-litHeadTop].link == 0 {
							mems++
							cmem[cd-litHeadTop].link = strengthened
							strengthened = cd
//line simplify.w:613
						}

//line simplify.w:600
					}

//line simplify.w:553
				}
				varsGone++
			}

//line simplify.w:562
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

//line simplify.w:869

//line simplify.w:875
			mems++
			if mem[c].cls != 0 {
				specialcase = 0

//line simplify.w:746
				mems += 3
				sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
//line simplify.w:747
				for mems, vv = mems+1, v; vv >= clsHeadTop; mems, vv = mems+1, mem[vv].left {
					mems++
					u = mem[vv].lit
//line simplify.w:749
					if specialcase != 0 {

//line simplify.w:1401
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

//line simplify.w:751
					}
					mems++
					ubits = bits &^ mem[u].sig
//line simplify.w:753
					for mems, pp = mems+1, mem[u^1].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
						strTries++
						mems++
						cc = mem[pp].cls
//line simplify.w:756
						mems++
						if ubits&^mem[cc].sig != 0 {
							continue
						}
						mems++
						if mem[cc].cls < sz {
							continue
						}

//line simplify.w:774
						mems++
						q, qq = v, mem[cc].left
//line simplify.w:775
						for {
							mems += 2
							l, ll = mem[q].lit, mem[qq].lit
//line simplify.w:777
							if l == u {
								l ^= 1
							}

//line simplify.w:712
							for l < ll {
								mems++
								qq = mem[qq].left
//line simplify.w:714
								if qq < clsHeadTop {
									ll = 0
								} else {
									mems++
									ll = mem[qq].lit
//line simplify.w:718
								}
							}

//line simplify.w:781
							if l > ll {
								break
							}
							mems++
							q = mem[q].left
//line simplify.w:785
							if q < clsHeadTop {
								l = 0
								break
							}
							mems++
							qq = mem[qq].left
//line simplify.w:790
							if qq < clsHeadTop {
								ll = 0
								break
							}
						}

//line simplify.w:765
						if l > ll {
							strFalse++
						} else {

//line simplify.w:800
							ccbits = 0
							strTotal++
							for mems, p = mems+1, mem[cc].right; ; mems, p = mems+1, mem[p].right {
								mems++
								w = mem[p].lit
//line simplify.w:804
								mems++
								vmem[w>>1].stable = 0
//line simplify.w:805
								if w == u^1 {
									break
								}
								mems++
								ccbits |= mem[w].sig
//line simplify.w:809
							}
							mems += 2
							mem[w].lit--
//line simplify.w:811
							if mem[w].lit == 0 {

//line simplify.w:502
								kv = w >> 1
								mems++
								if vmem[kv].status == varNorm {
									mems++
									if w&1 != 0 {
										vmem[kv].status = forcedTrue
									} else {
										vmem[kv].status = forcedFalse
									}
									vmem[kv].link = toDo
									toDo = kv
//line simplify.w:512
								} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
									mems++
									vmem[kv].status = elimQuiet
									vmem[kv].stable = 1
//line simplify.w:514
								}

//line simplify.w:813
							}

//line simplify.w:830
							mems++
							q, w = mem[p].up, mem[p].down
//line simplify.w:831
							mems += 2
							mem[q].down = w
							mem[w].up = q
//line simplify.w:832
							mems++
							q, w = mem[p].right, mem[p].left
//line simplify.w:833
							mems += 2
							mem[q].left = w
							mem[w].right = q
//line simplify.w:834
							mems++
							mem[p].left = avail
							avail = p

//line simplify.w:815
							for p = q; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
								mems++
								q = mem[p].lit
//line simplify.w:817
								mems++
								vmem[q>>1].stable = 0
//line simplify.w:818
								mems++
								ccbits |= mem[q].sig
//line simplify.w:819
							}
							mems++
							mem[cc].sig = ccbits

//line simplify.w:840
							mems += 2
							mem[cc].cls--
//line simplify.w:841
							if mem[cc].cls <= 1 {
								if mem[cc].cls == 0 {
									panic("sat: 이럴 수는 없다 (strengthening)")
								}
								mems += 2
								w = mem[mem[cc].right].lit
//line simplify.w:846

//line simplify.w:480
								kv = w >> 1
								mems++
								if w&1 != 0 {
									if vmem[kv].status == varNorm {
										mems++
										vmem[kv].status = forcedFalse
										vmem[kv].link = toDo
										toDo = kv
//line simplify.w:485
									} else if vmem[kv].status == forcedTrue {
										goto unsat
									}
								} else {
									if vmem[kv].status == varNorm {
										mems++
										vmem[kv].status = forcedTrue
										vmem[kv].link = toDo
										toDo = kv
//line simplify.w:491
									} else if vmem[kv].status == forcedFalse {
										goto unsat
									}
								}

//line simplify.w:847
							}

//line simplify.w:822
							mems++
							if cmem[cc-litHeadTop].link == 0 {
								mems++
								cmem[cc-litHeadTop].link = strengthened
								strengthened = cc
//line simplify.w:825
							}

//line simplify.w:769
						}
					}
				}

//line simplify.w:879

//line simplify.w:540
				for toDo != 0 {
					k = toDo
					mems++
					toDo = vmem[k].link
//line simplify.w:543
					if vmem[k].status != elimQuiet {
						if vmem[k].status == forcedTrue {
							l = k + k
						} else {
							l = k + k + 1
						}
						pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
						mems++
						vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
						for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
							mems++
							cd = mem[ll].cls
//line simplify.w:621
							for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
								if p != ll {
									mems++
									w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
									mems++
									q, r = mem[p].up, mem[p].down
//line simplify.w:639
									mems += 2
									mem[q].down = r
									mem[r].up = q
//line simplify.w:640
									mems++
									vmem[w>>1].stable = 0
//line simplify.w:641
									mems += 2
									mem[w].lit--
//line simplify.w:642
									if mem[w].lit == 0 {

//line simplify.w:502
										kv = w >> 1
										mems++
										if vmem[kv].status == varNorm {
											mems++
											if w&1 != 0 {
												vmem[kv].status = forcedTrue
											} else {
												vmem[kv].status = forcedFalse
											}
											vmem[kv].link = toDo
											toDo = kv
//line simplify.w:512
										} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
											mems++
											vmem[kv].status = elimQuiet
											vmem[kv].stable = 1
//line simplify.w:514
										}

//line simplify.w:644
									}

//line simplify.w:625
								}
							}
							mems++
							mem[mem[cd].right].left = avail
							avail = mem[cd].left
//line simplify.w:628
							mems++
							mem[cd].cls = 0
							clausesGone++
//line simplify.w:629
						}

//line simplify.w:552

//line simplify.w:582
						for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
							mems++
							cd = mem[ll].cls
//line simplify.w:584
							mems++
							p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
							mems += 2
							mem[p].right = q
							mem[q].left = p
//line simplify.w:586
							mems++
							mem[ll].left = avail
							avail = ll
//line simplify.w:587
							mems++
							j = mem[cd].cls - 1
//line simplify.w:588
							mems++
							mem[cd].cls = j
//line simplify.w:589
							if j == 1 {
								mems++
								if p == cd {
									w = mem[q].lit
								} else {
									w = mem[p].lit
								}

//line simplify.w:480
								kv = w >> 1
								mems++
								if w&1 != 0 {
									if vmem[kv].status == varNorm {
										mems++
										vmem[kv].status = forcedFalse
										vmem[kv].link = toDo
										toDo = kv
//line simplify.w:485
									} else if vmem[kv].status == forcedTrue {
										goto unsat
									}
								} else {
									if vmem[kv].status == varNorm {
										mems++
										vmem[kv].status = forcedTrue
										vmem[kv].link = toDo
										toDo = kv
//line simplify.w:491
									} else if vmem[kv].status == forcedFalse {
										goto unsat
									}
								}

//line simplify.w:597
							}

//line simplify.w:603
							bits2 = 0
							for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
								mems += 2
								bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
							}
							mems++
							mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
							mems++
							if cmem[cd-litHeadTop].link == 0 {
								mems++
								cmem[cd-litHeadTop].link = strengthened
								strengthened = cd
//line simplify.w:613
							}

//line simplify.w:600
						}

//line simplify.w:553
					}
					varsGone++
				}

//line simplify.w:562
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

//line simplify.w:880
				mems++
				mem[c].lit = round
//line simplify.w:881
				mems++
				cmem[c-litHeadTop].size = 0
//line simplify.w:882
			}

//line simplify.w:870
		}
	}
	c = csave

//line simplify.w:1304
	for round = 1; round <= uint32(par.MaxRounds); round++ {
		progress = varsGone

//line simplify.w:1156
		for b = 2; b <= uint32(par.Buckets); b++ {
			mems++
			bucket[b] = 0
//line simplify.w:1158
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
			mems += 2
			p, q = mem[l].lit, mem[l+1].lit
//line simplify.w:1169
			if p > uint32(par.Cutoff) && q > uint32(par.Cutoff) {
				goto reject
			}
			b = p + q
			if uint64(p)*uint64(q) > uint64(b)+par.Optimism {
				goto reject
			}
			b = min(b, uint32(par.Buckets))
			mems += 2
			vmem[x].blink = bucket[b]
//line simplify.w:1178
			mems++
			bucket[b] = x
//line simplify.w:1179
			continue
		reject:
			mems++
			vmem[x].stable = 1
//line simplify.w:1182
		}

//line simplify.w:1139
		for b = 2; b <= uint32(par.Buckets); b++ {
			mems++
			if bucket[b] != 0 {
				for x = bucket[b]; x != 0; mems, x = mems+1, vmem[x].blink {
					mems++
					if vmem[x].stable == 0 {

//line simplify.w:1060
						l = x + x
						mems += 2
						clausesSaved = int(mem[l].lit + mem[l+1].lit)
//line simplify.w:1062
						if mem[l].lit > uint32(par.Cutoff) && mem[l+1].lit > uint32(par.Cutoff) {
							goto elimDone
						}
						if uint64(mem[l].lit)*uint64(mem[l+1].lit) > uint64(mem[l].lit+mem[l+1].lit)+par.Optimism {
							goto elimDone
						}
						elimTries++

//line simplify.w:984
						stbits = 0
						beta0 = 0
						stamp++
//line simplify.w:985
						ll = l ^ 1

//line simplify.w:1003
						for mems, p = mems+1, mem[l].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
							mems += 2
							if mem[mem[p].cls].cls == 2 {
								mems++
								q = mem[p].right
//line simplify.w:1007
								if q < clsHeadTop {
									mems++
									q = mem[p].left
//line simplify.w:1009
								}
								mems += 2
								lmem[mem[q].lit] = stamp
//line simplify.w:1011
								mems++
								stbits |= mem[mem[q].lit^1].sig
//line simplify.w:1012
							}
						}

//line simplify.w:987
						if stbits != 0 {
							mems++
							stbits |= mem[ll].sig
//line simplify.w:989
							for mems, p = mems+1, mem[ll].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
								mems++
								c = mem[p].cls
//line simplify.w:991
								mems++
								if mem[c].sig&^stbits == 0 {

//line simplify.w:1016
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

//line simplify.w:994
								}
							}
						}
						if beta0 != 0 {
							stamp++

//line simplify.w:1031
							if mem[p].cls != beta0 || mem[p].lit != ll {
								panic("sat: 이럴 수는 없다 (partitioning)")
							}
							for mems, q = mems+1, mem[p].left; q != p; mems, q = mems+1, mem[q].left {
								if q < clsHeadTop {
									continue
								}
								mems += 2
								lmem[mem[q].lit^1] = stamp
//line simplify.w:1039
							}

//line simplify.w:1000
						}

//line simplify.w:1070
						if beta0 == 0 {
							l++

//line simplify.w:984
							stbits = 0
							beta0 = 0
							stamp++
//line simplify.w:985
							ll = l ^ 1

//line simplify.w:1003
							for mems, p = mems+1, mem[l].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
								mems += 2
								if mem[mem[p].cls].cls == 2 {
									mems++
									q = mem[p].right
//line simplify.w:1007
									if q < clsHeadTop {
										mems++
										q = mem[p].left
//line simplify.w:1009
									}
									mems += 2
									lmem[mem[q].lit] = stamp
//line simplify.w:1011
									mems++
									stbits |= mem[mem[q].lit^1].sig
//line simplify.w:1012
								}
							}

//line simplify.w:987
							if stbits != 0 {
								mems++
								stbits |= mem[ll].sig
//line simplify.w:989
								for mems, p = mems+1, mem[ll].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
									mems++
									c = mem[p].cls
//line simplify.w:991
									mems++
									if mem[c].sig&^stbits == 0 {

//line simplify.w:1016
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

//line simplify.w:994
									}
								}
							}
							if beta0 != 0 {
								stamp++

//line simplify.w:1031
								if mem[p].cls != beta0 || mem[p].lit != ll {
									panic("sat: 이럴 수는 없다 (partitioning)")
								}
								for mems, q = mems+1, mem[p].left; q != p; mems, q = mems+1, mem[q].left {
									if q < clsHeadTop {
										continue
									}
									mems += 2
									lmem[mem[q].lit^1] = stamp
//line simplify.w:1039
								}

//line simplify.w:1000
							}

//line simplify.w:1073
						}
						if beta0 != 0 {
							funcTotal++
						}
						lastNew = 0

//line simplify.w:1085
						for mems, alf = mems+1, mem[l].down; alf >= litHeadTop; mems, alf = mems+1, mem[alf].down {
							mems++
							c = mem[alf].cls
//line simplify.w:1087

//line simplify.w:1106
							if beta0 == 0 {
								alpha0 = true
							} else {
								alpha0 = false
								mems++
								if mem[c].cls == 2 {
									mems++
									q = mem[c].right
//line simplify.w:1113
									if q == alf {
										q = mem[c].left
									}
									mems += 2
									if lmem[mem[q].lit] == stamp {
										alpha0 = true
									}
								}
							}

//line simplify.w:1088
							for mems, bet = mems+1, mem[ll].down; bet >= litHeadTop; mems, bet = mems+1, mem[bet].down {
								mems++
								cc = mem[bet].cls
//line simplify.w:1090
								if cc == beta0 && alpha0 || cc != beta0 && !alpha0 {
									continue
								}

//line simplify.w:899
								p = 1
								mems += 2
								v = mem[c].left
								u = mem[v].lit
//line simplify.w:901
								mems += 2
								vv = mem[cc].left
								uu = mem[vv].lit
//line simplify.w:902
								for u+uu != 0 {
									if u == uu {

//line simplify.w:942
										q = p

//line simplify.w:952
										if avail != 0 {
											p = avail
											mems++
											avail = mem[p].left
//line simplify.w:955
										} else {
											if uint64(xcells) == memMax {
												err = ErrMemory
												goto record
											}
											p = xcells
											xcells++
										}

//line simplify.w:944
										mems += 2
										mem[q].left = p
										mem[p].lit = u

//line simplify.w:905

//line simplify.w:923
										mems++
										v = mem[v].left
//line simplify.w:924
										if v < clsHeadTop {
											u = 0
										} else {
											mems++
											u = mem[v].lit
//line simplify.w:928
										}

//line simplify.w:906

//line simplify.w:931
										mems++
										vv = mem[vv].left
//line simplify.w:932
										if vv < clsHeadTop {
											uu = 0
										} else {
											mems++
											uu = mem[vv].lit
//line simplify.w:936
										}

//line simplify.w:907
									} else if u == uu^1 {
										if u != l {

//line simplify.w:965
											if p != 1 {
												mems += 2
												mem[p].left = avail
												avail = mem[1].left
//line simplify.w:967
											}
											p = 0
											break

//line simplify.w:910
										}

//line simplify.w:923
										mems++
										v = mem[v].left
//line simplify.w:924
										if v < clsHeadTop {
											u = 0
										} else {
											mems++
											u = mem[v].lit
//line simplify.w:928
										}

//line simplify.w:912

//line simplify.w:931
										mems++
										vv = mem[vv].left
//line simplify.w:932
										if vv < clsHeadTop {
											uu = 0
										} else {
											mems++
											uu = mem[vv].lit
//line simplify.w:936
										}

//line simplify.w:913
									} else if u > uu {

//line simplify.w:942
										q = p

//line simplify.w:952
										if avail != 0 {
											p = avail
											mems++
											avail = mem[p].left
//line simplify.w:955
										} else {
											if uint64(xcells) == memMax {
												err = ErrMemory
												goto record
											}
											p = xcells
											xcells++
										}

//line simplify.w:944
										mems += 2
										mem[q].left = p
										mem[p].lit = u

//line simplify.w:915

//line simplify.w:923
										mems++
										v = mem[v].left
//line simplify.w:924
										if v < clsHeadTop {
											u = 0
										} else {
											mems++
											u = mem[v].lit
//line simplify.w:928
										}

//line simplify.w:916
									} else {

//line simplify.w:947
										q = p

//line simplify.w:952
										if avail != 0 {
											p = avail
											mems++
											avail = mem[p].left
//line simplify.w:955
										} else {
											if uint64(xcells) == memMax {
												err = ErrMemory
												goto record
											}
											p = xcells
											xcells++
										}

//line simplify.w:949
										mems += 2
										mem[q].left = p
										mem[p].lit = uu

//line simplify.w:918

//line simplify.w:931
										mems++
										vv = mem[vv].left
//line simplify.w:932
										if vv < clsHeadTop {
											uu = 0
										} else {
											mems++
											uu = mem[vv].lit
//line simplify.w:936
										}

//line simplify.w:919
									}
								}

//line simplify.w:1094
								if p != 0 {
									mems++
									mem[p].left = 0
//line simplify.w:1096
									mems += 2
									mem[lastNew].down = mem[1].left
//line simplify.w:1097
									mems++
									lastNew = mem[1].left
									mem[lastNew].right = p
//line simplify.w:1098
									if clausesSaved--; clausesSaved < 0 {

//line simplify.w:1126
										for mems, p = mems+1, mem[0].down; ; mems, p = mems+1, mem[p].down {
											mems += 2
											mem[mem[p].right].left = avail
											avail = p
//line simplify.w:1128
											if p == lastNew {
												break
											}
										}
										goto elimDone

//line simplify.w:1100
									}
								}
							}
						}

//line simplify.w:1079
						mems++
						mem[lastNew].down = 0

//line simplify.w:1146

//line simplify.w:1206
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

//line simplify.w:1221
							mems++
							k, v = mem[l].lit, l
//line simplify.w:1222
							mems++
							if k > mem[ll].lit {
								k, v = mem[ll].lit, ll
							}
							pre.erp = append(pre.erp, erpCell{Lit(v ^ 1), erpDef})
							for mems, p = mems+1, mem[v].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
								flag := uint8(erpFirst)
								for mems, q = mems+1, mem[p].right; q != p; mems, q = mems+1, mem[q].right {
									if q >= clsHeadTop {
										mems++
										pre.erp = append(pre.erp, erpCell{Lit(mem[q].lit), flag})
//line simplify.w:1232
										flag = 0
									}
								}
							}

//line simplify.w:1218
						}

//line simplify.w:1189
						mems += 2
						mem[lastNew].down = 0
						lastNew = mem[0].down
//line simplify.w:1190
						v = x + x

//line simplify.w:1241
						for mems, p = mems+1, mem[v].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
							mems++
							c = mem[p].cls
//line simplify.w:1243
							mems++
							q, r = mem[c].right, mem[c].left
//line simplify.w:1244
							mems += 2
							mem[q].left = r
							mem[r].right = q
//line simplify.w:1245
							if lastNew != 0 {
								mems++
								pp = mem[lastNew].down
//line simplify.w:1247

//line simplify.w:1259
								for q, r, sz, bits = lastNew, c, 0, 0; q != 0; mems, r, q = mems+1, q, mem[q].left {
									mems++
									u = mem[q].lit
//line simplify.w:1261
									mems += 2
									mem[u].lit++
//line simplify.w:1262
									mems++
									w = mem[u].up
//line simplify.w:1263
									mems += 2
									mem[u].up = q
									mem[w].down = q
//line simplify.w:1264
									mems++
									mem[q].up = w
									mem[q].down = u
//line simplify.w:1265
									mems++
									bits |= mem[u].sig
//line simplify.w:1266
									mems++
									mem[q].right = r
//line simplify.w:1267
									mems++
									mem[q].cls = c
//line simplify.w:1268
									sz++
								}
								mems += 2
								mem[c].cls = sz
								mem[c].sig = bits
//line simplify.w:1271
								mems += 2
								mem[c].left = lastNew
								mem[c].right = r
								mem[r].left = c
//line simplify.w:1272
								if sz == 1 {
									mems++
									w = mem[r].lit
//line simplify.w:1274

//line simplify.w:480
									kv = w >> 1
									mems++
									if w&1 != 0 {
										if vmem[kv].status == varNorm {
											mems++
											vmem[kv].status = forcedFalse
											vmem[kv].link = toDo
											toDo = kv
//line simplify.w:485
										} else if vmem[kv].status == forcedTrue {
											goto unsat
										}
									} else {
										if vmem[kv].status == varNorm {
											mems++
											vmem[kv].status = forcedTrue
											vmem[kv].link = toDo
											toDo = kv
//line simplify.w:491
										} else if vmem[kv].status == forcedFalse {
											goto unsat
										}
									}

//line simplify.w:1275
								}

//line simplify.w:1248
								mems++
								cmem[c-litHeadTop].size = 1
//line simplify.w:1249
								mems++
								lastNew = pp
//line simplify.w:1250
							} else {
								mems++
								mem[c].cls = 0
//line simplify.w:1252
							}
						}

//line simplify.w:1192
						v++

//line simplify.w:1241
						for mems, p = mems+1, mem[v].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
							mems++
							c = mem[p].cls
//line simplify.w:1243
							mems++
							q, r = mem[c].right, mem[c].left
//line simplify.w:1244
							mems += 2
							mem[q].left = r
							mem[r].right = q
//line simplify.w:1245
							if lastNew != 0 {
								mems++
								pp = mem[lastNew].down
//line simplify.w:1247

//line simplify.w:1259
								for q, r, sz, bits = lastNew, c, 0, 0; q != 0; mems, r, q = mems+1, q, mem[q].left {
									mems++
									u = mem[q].lit
//line simplify.w:1261
									mems += 2
									mem[u].lit++
//line simplify.w:1262
									mems++
									w = mem[u].up
//line simplify.w:1263
									mems += 2
									mem[u].up = q
									mem[w].down = q
//line simplify.w:1264
									mems++
									mem[q].up = w
									mem[q].down = u
//line simplify.w:1265
									mems++
									bits |= mem[u].sig
//line simplify.w:1266
									mems++
									mem[q].right = r
//line simplify.w:1267
									mems++
									mem[q].cls = c
//line simplify.w:1268
									sz++
								}
								mems += 2
								mem[c].cls = sz
								mem[c].sig = bits
//line simplify.w:1271
								mems += 2
								mem[c].left = lastNew
								mem[c].right = r
								mem[r].left = c
//line simplify.w:1272
								if sz == 1 {
									mems++
									w = mem[r].lit
//line simplify.w:1274

//line simplify.w:480
									kv = w >> 1
									mems++
									if w&1 != 0 {
										if vmem[kv].status == varNorm {
											mems++
											vmem[kv].status = forcedFalse
											vmem[kv].link = toDo
											toDo = kv
//line simplify.w:485
										} else if vmem[kv].status == forcedTrue {
											goto unsat
										}
									} else {
										if vmem[kv].status == varNorm {
											mems++
											vmem[kv].status = forcedTrue
											vmem[kv].link = toDo
											toDo = kv
//line simplify.w:491
										} else if vmem[kv].status == forcedFalse {
											goto unsat
										}
									}

//line simplify.w:1275
								}

//line simplify.w:1248
								mems++
								cmem[c-litHeadTop].size = 1
//line simplify.w:1249
								mems++
								lastNew = pp
//line simplify.w:1250
							} else {
								mems++
								mem[c].cls = 0
//line simplify.w:1252
							}
						}

//line simplify.w:1281
						for mems, p = mems+1, mem[v].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
							for mems, q = mems+1, mem[p].right; q != p; mems, q = mems+1, mem[q].right {
								mems++
								r, w = mem[q].up, mem[q].down
//line simplify.w:1284
								mems += 2
								mem[r].down = w
								mem[w].up = r
//line simplify.w:1285
								mems++
								w = mem[q].lit
//line simplify.w:1286
								mems++
								vmem[w>>1].stable = 0
//line simplify.w:1287
								mems += 2
								mem[w].lit--
								mem[w].cls = round
//line simplify.w:1288
								if mem[w].lit == 0 {

//line simplify.w:502
									kv = w >> 1
									mems++
									if vmem[kv].status == varNorm {
										mems++
										if w&1 != 0 {
											vmem[kv].status = forcedTrue
										} else {
											vmem[kv].status = forcedFalse
										}
										vmem[kv].link = toDo
										toDo = kv
//line simplify.w:512
									} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
										mems++
										vmem[kv].status = elimQuiet
										vmem[kv].stable = 1
//line simplify.w:514
									}

//line simplify.w:1290
								}
							}
							mems++
							mem[mem[p].right].left = avail
							avail = p
//line simplify.w:1293
						}

//line simplify.w:1195
						v--

//line simplify.w:1281
						for mems, p = mems+1, mem[v].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
							for mems, q = mems+1, mem[p].right; q != p; mems, q = mems+1, mem[q].right {
								mems++
								r, w = mem[q].up, mem[q].down
//line simplify.w:1284
								mems += 2
								mem[r].down = w
								mem[w].up = r
//line simplify.w:1285
								mems++
								w = mem[q].lit
//line simplify.w:1286
								mems++
								vmem[w>>1].stable = 0
//line simplify.w:1287
								mems += 2
								mem[w].lit--
								mem[w].cls = round
//line simplify.w:1288
								if mem[w].lit == 0 {

//line simplify.w:502
									kv = w >> 1
									mems++
									if vmem[kv].status == varNorm {
										mems++
										if w&1 != 0 {
											vmem[kv].status = forcedTrue
										} else {
											vmem[kv].status = forcedFalse
										}
										vmem[kv].link = toDo
										toDo = kv
//line simplify.w:512
									} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
										mems++
										vmem[kv].status = elimQuiet
										vmem[kv].stable = 1
//line simplify.w:514
									}

//line simplify.w:1290
								}
							}
							mems++
							mem[mem[p].right].left = avail
							avail = p
//line simplify.w:1293
						}

//line simplify.w:1197
						mems++
						vmem[x].status = elimRes
						varsGone++
//line simplify.w:1198
						clausesGone += uint32(clausesSaved)

//line simplify.w:1147

//line simplify.w:859
						csave = c

//line simplify.w:540
						for toDo != 0 {
							k = toDo
							mems++
							toDo = vmem[k].link
//line simplify.w:543
							if vmem[k].status != elimQuiet {
								if vmem[k].status == forcedTrue {
									l = k + k
								} else {
									l = k + k + 1
								}
								pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
								mems++
								vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
								for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
									mems++
									cd = mem[ll].cls
//line simplify.w:621
									for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
										if p != ll {
											mems++
											w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
											mems++
											q, r = mem[p].up, mem[p].down
//line simplify.w:639
											mems += 2
											mem[q].down = r
											mem[r].up = q
//line simplify.w:640
											mems++
											vmem[w>>1].stable = 0
//line simplify.w:641
											mems += 2
											mem[w].lit--
//line simplify.w:642
											if mem[w].lit == 0 {

//line simplify.w:502
												kv = w >> 1
												mems++
												if vmem[kv].status == varNorm {
													mems++
													if w&1 != 0 {
														vmem[kv].status = forcedTrue
													} else {
														vmem[kv].status = forcedFalse
													}
													vmem[kv].link = toDo
													toDo = kv
//line simplify.w:512
												} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
													mems++
													vmem[kv].status = elimQuiet
													vmem[kv].stable = 1
//line simplify.w:514
												}

//line simplify.w:644
											}

//line simplify.w:625
										}
									}
									mems++
									mem[mem[cd].right].left = avail
									avail = mem[cd].left
//line simplify.w:628
									mems++
									mem[cd].cls = 0
									clausesGone++
//line simplify.w:629
								}

//line simplify.w:552

//line simplify.w:582
								for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
									mems++
									cd = mem[ll].cls
//line simplify.w:584
									mems++
									p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
									mems += 2
									mem[p].right = q
									mem[q].left = p
//line simplify.w:586
									mems++
									mem[ll].left = avail
									avail = ll
//line simplify.w:587
									mems++
									j = mem[cd].cls - 1
//line simplify.w:588
									mems++
									mem[cd].cls = j
//line simplify.w:589
									if j == 1 {
										mems++
										if p == cd {
											w = mem[q].lit
										} else {
											w = mem[p].lit
										}

//line simplify.w:480
										kv = w >> 1
										mems++
										if w&1 != 0 {
											if vmem[kv].status == varNorm {
												mems++
												vmem[kv].status = forcedFalse
												vmem[kv].link = toDo
												toDo = kv
//line simplify.w:485
											} else if vmem[kv].status == forcedTrue {
												goto unsat
											}
										} else {
											if vmem[kv].status == varNorm {
												mems++
												vmem[kv].status = forcedTrue
												vmem[kv].link = toDo
												toDo = kv
//line simplify.w:491
											} else if vmem[kv].status == forcedFalse {
												goto unsat
											}
										}

//line simplify.w:597
									}

//line simplify.w:603
									bits2 = 0
									for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
										mems += 2
										bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
									}
									mems++
									mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
									mems++
									if cmem[cd-litHeadTop].link == 0 {
										mems++
										cmem[cd-litHeadTop].link = strengthened
										strengthened = cd
//line simplify.w:613
									}

//line simplify.w:600
								}

//line simplify.w:553
							}
							varsGone++
						}

//line simplify.w:562
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

//line simplify.w:861
						for strengthened != sentinel {
							c = strengthened
							mems++
							strengthened = cmem[c-litHeadTop].link
//line simplify.w:864
							mems++
							if mem[c].cls != 0 {
								mems++
								cmem[c-litHeadTop].link = 0
//line simplify.w:867

//line simplify.w:679
								mems += 3
								p = mem[c].right
								l = mem[p].lit
								k = mem[l].lit
//line simplify.w:680
								for mems, p = mems+1, mem[p].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
									mems++
									ll = mem[p].lit
//line simplify.w:682
									mems++
									if mem[ll].lit < k {
										k, l = mem[ll].lit, ll
									}
								}

//line simplify.w:655
								mems += 3
								sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
//line simplify.w:656
								for mems, pp = mems+1, mem[l].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
									mems++
									cc = mem[pp].cls
//line simplify.w:658
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

//line simplify.w:692
									mems++
									q, qq = v, mem[cc].left
//line simplify.w:693
									for {
										mems += 2
										l, ll = mem[q].lit, mem[qq].lit
//line simplify.w:695

//line simplify.w:712
										for l < ll {
											mems++
											qq = mem[qq].left
//line simplify.w:714
											if qq < clsHeadTop {
												ll = 0
											} else {
												mems++
												ll = mem[qq].lit
//line simplify.w:718
											}
										}

//line simplify.w:696
										if l > ll {
											break
										}
										mems++
										q = mem[q].left
//line simplify.w:700
										if q < clsHeadTop {
											l = 0
											break
										}
										mems++
										qq = mem[qq].left
//line simplify.w:705
										if qq < clsHeadTop {
											ll = 0
											break
										}
									}

//line simplify.w:671
									if l > ll {
										subFalse++
									} else {

//line simplify.w:722
										subTotal++
										for mems, p = mems+1, mem[cc].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
											mems++
											w = mem[p].lit
//line simplify.w:725

//line simplify.w:638
											mems++
											q, r = mem[p].up, mem[p].down
//line simplify.w:639
											mems += 2
											mem[q].down = r
											mem[r].up = q
//line simplify.w:640
											mems++
											vmem[w>>1].stable = 0
//line simplify.w:641
											mems += 2
											mem[w].lit--
//line simplify.w:642
											if mem[w].lit == 0 {

//line simplify.w:502
												kv = w >> 1
												mems++
												if vmem[kv].status == varNorm {
													mems++
													if w&1 != 0 {
														vmem[kv].status = forcedTrue
													} else {
														vmem[kv].status = forcedFalse
													}
													vmem[kv].link = toDo
													toDo = kv
//line simplify.w:512
												} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
													mems++
													vmem[kv].status = elimQuiet
													vmem[kv].stable = 1
//line simplify.w:514
												}

//line simplify.w:644
											}

//line simplify.w:726
										}
										mems++
										mem[mem[cc].right].left = avail
										avail = mem[cc].left
//line simplify.w:728
										mems++
										mem[cc].cls = 0
										clausesGone++

//line simplify.w:675
									}
								}

//line simplify.w:868

//line simplify.w:540
								for toDo != 0 {
									k = toDo
									mems++
									toDo = vmem[k].link
//line simplify.w:543
									if vmem[k].status != elimQuiet {
										if vmem[k].status == forcedTrue {
											l = k + k
										} else {
											l = k + k + 1
										}
										pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
										mems++
										vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
										for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
											mems++
											cd = mem[ll].cls
//line simplify.w:621
											for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
												if p != ll {
													mems++
													w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
													mems++
													q, r = mem[p].up, mem[p].down
//line simplify.w:639
													mems += 2
													mem[q].down = r
													mem[r].up = q
//line simplify.w:640
													mems++
													vmem[w>>1].stable = 0
//line simplify.w:641
													mems += 2
													mem[w].lit--
//line simplify.w:642
													if mem[w].lit == 0 {

//line simplify.w:502
														kv = w >> 1
														mems++
														if vmem[kv].status == varNorm {
															mems++
															if w&1 != 0 {
																vmem[kv].status = forcedTrue
															} else {
																vmem[kv].status = forcedFalse
															}
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:512
														} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
															mems++
															vmem[kv].status = elimQuiet
															vmem[kv].stable = 1
//line simplify.w:514
														}

//line simplify.w:644
													}

//line simplify.w:625
												}
											}
											mems++
											mem[mem[cd].right].left = avail
											avail = mem[cd].left
//line simplify.w:628
											mems++
											mem[cd].cls = 0
											clausesGone++
//line simplify.w:629
										}

//line simplify.w:552

//line simplify.w:582
										for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
											mems++
											cd = mem[ll].cls
//line simplify.w:584
											mems++
											p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
											mems += 2
											mem[p].right = q
											mem[q].left = p
//line simplify.w:586
											mems++
											mem[ll].left = avail
											avail = ll
//line simplify.w:587
											mems++
											j = mem[cd].cls - 1
//line simplify.w:588
											mems++
											mem[cd].cls = j
//line simplify.w:589
											if j == 1 {
												mems++
												if p == cd {
													w = mem[q].lit
												} else {
													w = mem[p].lit
												}

//line simplify.w:480
												kv = w >> 1
												mems++
												if w&1 != 0 {
													if vmem[kv].status == varNorm {
														mems++
														vmem[kv].status = forcedFalse
														vmem[kv].link = toDo
														toDo = kv
//line simplify.w:485
													} else if vmem[kv].status == forcedTrue {
														goto unsat
													}
												} else {
													if vmem[kv].status == varNorm {
														mems++
														vmem[kv].status = forcedTrue
														vmem[kv].link = toDo
														toDo = kv
//line simplify.w:491
													} else if vmem[kv].status == forcedFalse {
														goto unsat
													}
												}

//line simplify.w:597
											}

//line simplify.w:603
											bits2 = 0
											for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
												mems += 2
												bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
											}
											mems++
											mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
											mems++
											if cmem[cd-litHeadTop].link == 0 {
												mems++
												cmem[cd-litHeadTop].link = strengthened
												strengthened = cd
//line simplify.w:613
											}

//line simplify.w:600
										}

//line simplify.w:553
									}
									varsGone++
								}

//line simplify.w:562
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

//line simplify.w:869

//line simplify.w:875
								mems++
								if mem[c].cls != 0 {
									specialcase = 0

//line simplify.w:746
									mems += 3
									sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
//line simplify.w:747
									for mems, vv = mems+1, v; vv >= clsHeadTop; mems, vv = mems+1, mem[vv].left {
										mems++
										u = mem[vv].lit
//line simplify.w:749
										if specialcase != 0 {

//line simplify.w:1401
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

//line simplify.w:751
										}
										mems++
										ubits = bits &^ mem[u].sig
//line simplify.w:753
										for mems, pp = mems+1, mem[u^1].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
											strTries++
											mems++
											cc = mem[pp].cls
//line simplify.w:756
											mems++
											if ubits&^mem[cc].sig != 0 {
												continue
											}
											mems++
											if mem[cc].cls < sz {
												continue
											}

//line simplify.w:774
											mems++
											q, qq = v, mem[cc].left
//line simplify.w:775
											for {
												mems += 2
												l, ll = mem[q].lit, mem[qq].lit
//line simplify.w:777
												if l == u {
													l ^= 1
												}

//line simplify.w:712
												for l < ll {
													mems++
													qq = mem[qq].left
//line simplify.w:714
													if qq < clsHeadTop {
														ll = 0
													} else {
														mems++
														ll = mem[qq].lit
//line simplify.w:718
													}
												}

//line simplify.w:781
												if l > ll {
													break
												}
												mems++
												q = mem[q].left
//line simplify.w:785
												if q < clsHeadTop {
													l = 0
													break
												}
												mems++
												qq = mem[qq].left
//line simplify.w:790
												if qq < clsHeadTop {
													ll = 0
													break
												}
											}

//line simplify.w:765
											if l > ll {
												strFalse++
											} else {

//line simplify.w:800
												ccbits = 0
												strTotal++
												for mems, p = mems+1, mem[cc].right; ; mems, p = mems+1, mem[p].right {
													mems++
													w = mem[p].lit
//line simplify.w:804
													mems++
													vmem[w>>1].stable = 0
//line simplify.w:805
													if w == u^1 {
														break
													}
													mems++
													ccbits |= mem[w].sig
//line simplify.w:809
												}
												mems += 2
												mem[w].lit--
//line simplify.w:811
												if mem[w].lit == 0 {

//line simplify.w:502
													kv = w >> 1
													mems++
													if vmem[kv].status == varNorm {
														mems++
														if w&1 != 0 {
															vmem[kv].status = forcedTrue
														} else {
															vmem[kv].status = forcedFalse
														}
														vmem[kv].link = toDo
														toDo = kv
//line simplify.w:512
													} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
														mems++
														vmem[kv].status = elimQuiet
														vmem[kv].stable = 1
//line simplify.w:514
													}

//line simplify.w:813
												}

//line simplify.w:830
												mems++
												q, w = mem[p].up, mem[p].down
//line simplify.w:831
												mems += 2
												mem[q].down = w
												mem[w].up = q
//line simplify.w:832
												mems++
												q, w = mem[p].right, mem[p].left
//line simplify.w:833
												mems += 2
												mem[q].left = w
												mem[w].right = q
//line simplify.w:834
												mems++
												mem[p].left = avail
												avail = p

//line simplify.w:815
												for p = q; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
													mems++
													q = mem[p].lit
//line simplify.w:817
													mems++
													vmem[q>>1].stable = 0
//line simplify.w:818
													mems++
													ccbits |= mem[q].sig
//line simplify.w:819
												}
												mems++
												mem[cc].sig = ccbits

//line simplify.w:840
												mems += 2
												mem[cc].cls--
//line simplify.w:841
												if mem[cc].cls <= 1 {
													if mem[cc].cls == 0 {
														panic("sat: 이럴 수는 없다 (strengthening)")
													}
													mems += 2
													w = mem[mem[cc].right].lit
//line simplify.w:846

//line simplify.w:480
													kv = w >> 1
													mems++
													if w&1 != 0 {
														if vmem[kv].status == varNorm {
															mems++
															vmem[kv].status = forcedFalse
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:485
														} else if vmem[kv].status == forcedTrue {
															goto unsat
														}
													} else {
														if vmem[kv].status == varNorm {
															mems++
															vmem[kv].status = forcedTrue
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:491
														} else if vmem[kv].status == forcedFalse {
															goto unsat
														}
													}

//line simplify.w:847
												}

//line simplify.w:822
												mems++
												if cmem[cc-litHeadTop].link == 0 {
													mems++
													cmem[cc-litHeadTop].link = strengthened
													strengthened = cc
//line simplify.w:825
												}

//line simplify.w:769
											}
										}
									}

//line simplify.w:879

//line simplify.w:540
									for toDo != 0 {
										k = toDo
										mems++
										toDo = vmem[k].link
//line simplify.w:543
										if vmem[k].status != elimQuiet {
											if vmem[k].status == forcedTrue {
												l = k + k
											} else {
												l = k + k + 1
											}
											pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
											mems++
											vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
											for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
												mems++
												cd = mem[ll].cls
//line simplify.w:621
												for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
													if p != ll {
														mems++
														w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
														mems++
														q, r = mem[p].up, mem[p].down
//line simplify.w:639
														mems += 2
														mem[q].down = r
														mem[r].up = q
//line simplify.w:640
														mems++
														vmem[w>>1].stable = 0
//line simplify.w:641
														mems += 2
														mem[w].lit--
//line simplify.w:642
														if mem[w].lit == 0 {

//line simplify.w:502
															kv = w >> 1
															mems++
															if vmem[kv].status == varNorm {
																mems++
																if w&1 != 0 {
																	vmem[kv].status = forcedTrue
																} else {
																	vmem[kv].status = forcedFalse
																}
																vmem[kv].link = toDo
																toDo = kv
//line simplify.w:512
															} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
																mems++
																vmem[kv].status = elimQuiet
																vmem[kv].stable = 1
//line simplify.w:514
															}

//line simplify.w:644
														}

//line simplify.w:625
													}
												}
												mems++
												mem[mem[cd].right].left = avail
												avail = mem[cd].left
//line simplify.w:628
												mems++
												mem[cd].cls = 0
												clausesGone++
//line simplify.w:629
											}

//line simplify.w:552

//line simplify.w:582
											for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
												mems++
												cd = mem[ll].cls
//line simplify.w:584
												mems++
												p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
												mems += 2
												mem[p].right = q
												mem[q].left = p
//line simplify.w:586
												mems++
												mem[ll].left = avail
												avail = ll
//line simplify.w:587
												mems++
												j = mem[cd].cls - 1
//line simplify.w:588
												mems++
												mem[cd].cls = j
//line simplify.w:589
												if j == 1 {
													mems++
													if p == cd {
														w = mem[q].lit
													} else {
														w = mem[p].lit
													}

//line simplify.w:480
													kv = w >> 1
													mems++
													if w&1 != 0 {
														if vmem[kv].status == varNorm {
															mems++
															vmem[kv].status = forcedFalse
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:485
														} else if vmem[kv].status == forcedTrue {
															goto unsat
														}
													} else {
														if vmem[kv].status == varNorm {
															mems++
															vmem[kv].status = forcedTrue
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:491
														} else if vmem[kv].status == forcedFalse {
															goto unsat
														}
													}

//line simplify.w:597
												}

//line simplify.w:603
												bits2 = 0
												for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
													mems += 2
													bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
												}
												mems++
												mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
												mems++
												if cmem[cd-litHeadTop].link == 0 {
													mems++
													cmem[cd-litHeadTop].link = strengthened
													strengthened = cd
//line simplify.w:613
												}

//line simplify.w:600
											}

//line simplify.w:553
										}
										varsGone++
									}

//line simplify.w:562
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

//line simplify.w:880
									mems++
									mem[c].lit = round
//line simplify.w:881
									mems++
									cmem[c-litHeadTop].size = 0
//line simplify.w:882
								}

//line simplify.w:870
							}
						}
						c = csave

//line simplify.w:1148
					elimDone:
						mems++
						vmem[x].stable = 1
//line simplify.w:1150
					}
				}
			}
		}

//line simplify.w:1307
		if progress == varsGone || varsGone == vars {
			break
		}

//line simplify.w:1331
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

//line simplify.w:1355
				for mems, p = mems+1, mem[l].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
					mems++
					c = mem[p].cls
//line simplify.w:1357
					mems += 2
					cmem[c-litHeadTop].size += 4
//line simplify.w:1358
				}
				for mems, p = mems+1, mem[l^1].down; p >= litHeadTop; mems, p = mems+1, mem[p].down {
					mems++
					c = mem[p].cls
//line simplify.w:1361
					mems += 2
					cmem[c-litHeadTop].size |= 2
//line simplify.w:1362
				}

//line simplify.w:1342
			}
		}
		for c = litHeadTop; c < clsHeadTop; c++ {
			mems++
			if mem[c].cls != 0 {
				if mem[c].lit < round {

//line simplify.w:1367
					mems++
					if mem[c].cls == cmem[c-litHeadTop].size>>2 {

//line simplify.w:679
						mems += 3
						p = mem[c].right
						l = mem[p].lit
						k = mem[l].lit
//line simplify.w:680
						for mems, p = mems+1, mem[p].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
							mems++
							ll = mem[p].lit
//line simplify.w:682
							mems++
							if mem[ll].lit < k {
								k, l = mem[ll].lit, ll
							}
						}

//line simplify.w:655
						mems += 3
						sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
//line simplify.w:656
						for mems, pp = mems+1, mem[l].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
							mems++
							cc = mem[pp].cls
//line simplify.w:658
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

//line simplify.w:692
							mems++
							q, qq = v, mem[cc].left
//line simplify.w:693
							for {
								mems += 2
								l, ll = mem[q].lit, mem[qq].lit
//line simplify.w:695

//line simplify.w:712
								for l < ll {
									mems++
									qq = mem[qq].left
//line simplify.w:714
									if qq < clsHeadTop {
										ll = 0
									} else {
										mems++
										ll = mem[qq].lit
//line simplify.w:718
									}
								}

//line simplify.w:696
								if l > ll {
									break
								}
								mems++
								q = mem[q].left
//line simplify.w:700
								if q < clsHeadTop {
									l = 0
									break
								}
								mems++
								qq = mem[qq].left
//line simplify.w:705
								if qq < clsHeadTop {
									ll = 0
									break
								}
							}

//line simplify.w:671
							if l > ll {
								subFalse++
							} else {

//line simplify.w:722
								subTotal++
								for mems, p = mems+1, mem[cc].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
									mems++
									w = mem[p].lit
//line simplify.w:725

//line simplify.w:638
									mems++
									q, r = mem[p].up, mem[p].down
//line simplify.w:639
									mems += 2
									mem[q].down = r
									mem[r].up = q
//line simplify.w:640
									mems++
									vmem[w>>1].stable = 0
//line simplify.w:641
									mems += 2
									mem[w].lit--
//line simplify.w:642
									if mem[w].lit == 0 {

//line simplify.w:502
										kv = w >> 1
										mems++
										if vmem[kv].status == varNorm {
											mems++
											if w&1 != 0 {
												vmem[kv].status = forcedTrue
											} else {
												vmem[kv].status = forcedFalse
											}
											vmem[kv].link = toDo
											toDo = kv
//line simplify.w:512
										} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
											mems++
											vmem[kv].status = elimQuiet
											vmem[kv].stable = 1
//line simplify.w:514
										}

//line simplify.w:644
									}

//line simplify.w:726
								}
								mems++
								mem[mem[cc].right].left = avail
								avail = mem[cc].left
//line simplify.w:728
								mems++
								mem[cc].cls = 0
								clausesGone++

//line simplify.w:675
							}
						}

//line simplify.w:1370

//line simplify.w:859
						csave = c

//line simplify.w:540
						for toDo != 0 {
							k = toDo
							mems++
							toDo = vmem[k].link
//line simplify.w:543
							if vmem[k].status != elimQuiet {
								if vmem[k].status == forcedTrue {
									l = k + k
								} else {
									l = k + k + 1
								}
								pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
								mems++
								vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
								for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
									mems++
									cd = mem[ll].cls
//line simplify.w:621
									for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
										if p != ll {
											mems++
											w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
											mems++
											q, r = mem[p].up, mem[p].down
//line simplify.w:639
											mems += 2
											mem[q].down = r
											mem[r].up = q
//line simplify.w:640
											mems++
											vmem[w>>1].stable = 0
//line simplify.w:641
											mems += 2
											mem[w].lit--
//line simplify.w:642
											if mem[w].lit == 0 {

//line simplify.w:502
												kv = w >> 1
												mems++
												if vmem[kv].status == varNorm {
													mems++
													if w&1 != 0 {
														vmem[kv].status = forcedTrue
													} else {
														vmem[kv].status = forcedFalse
													}
													vmem[kv].link = toDo
													toDo = kv
//line simplify.w:512
												} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
													mems++
													vmem[kv].status = elimQuiet
													vmem[kv].stable = 1
//line simplify.w:514
												}

//line simplify.w:644
											}

//line simplify.w:625
										}
									}
									mems++
									mem[mem[cd].right].left = avail
									avail = mem[cd].left
//line simplify.w:628
									mems++
									mem[cd].cls = 0
									clausesGone++
//line simplify.w:629
								}

//line simplify.w:552

//line simplify.w:582
								for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
									mems++
									cd = mem[ll].cls
//line simplify.w:584
									mems++
									p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
									mems += 2
									mem[p].right = q
									mem[q].left = p
//line simplify.w:586
									mems++
									mem[ll].left = avail
									avail = ll
//line simplify.w:587
									mems++
									j = mem[cd].cls - 1
//line simplify.w:588
									mems++
									mem[cd].cls = j
//line simplify.w:589
									if j == 1 {
										mems++
										if p == cd {
											w = mem[q].lit
										} else {
											w = mem[p].lit
										}

//line simplify.w:480
										kv = w >> 1
										mems++
										if w&1 != 0 {
											if vmem[kv].status == varNorm {
												mems++
												vmem[kv].status = forcedFalse
												vmem[kv].link = toDo
												toDo = kv
//line simplify.w:485
											} else if vmem[kv].status == forcedTrue {
												goto unsat
											}
										} else {
											if vmem[kv].status == varNorm {
												mems++
												vmem[kv].status = forcedTrue
												vmem[kv].link = toDo
												toDo = kv
//line simplify.w:491
											} else if vmem[kv].status == forcedFalse {
												goto unsat
											}
										}

//line simplify.w:597
									}

//line simplify.w:603
									bits2 = 0
									for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
										mems += 2
										bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
									}
									mems++
									mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
									mems++
									if cmem[cd-litHeadTop].link == 0 {
										mems++
										cmem[cd-litHeadTop].link = strengthened
										strengthened = cd
//line simplify.w:613
									}

//line simplify.w:600
								}

//line simplify.w:553
							}
							varsGone++
						}

//line simplify.w:562
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

//line simplify.w:861
						for strengthened != sentinel {
							c = strengthened
							mems++
							strengthened = cmem[c-litHeadTop].link
//line simplify.w:864
							mems++
							if mem[c].cls != 0 {
								mems++
								cmem[c-litHeadTop].link = 0
//line simplify.w:867

//line simplify.w:679
								mems += 3
								p = mem[c].right
								l = mem[p].lit
								k = mem[l].lit
//line simplify.w:680
								for mems, p = mems+1, mem[p].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
									mems++
									ll = mem[p].lit
//line simplify.w:682
									mems++
									if mem[ll].lit < k {
										k, l = mem[ll].lit, ll
									}
								}

//line simplify.w:655
								mems += 3
								sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
//line simplify.w:656
								for mems, pp = mems+1, mem[l].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
									mems++
									cc = mem[pp].cls
//line simplify.w:658
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

//line simplify.w:692
									mems++
									q, qq = v, mem[cc].left
//line simplify.w:693
									for {
										mems += 2
										l, ll = mem[q].lit, mem[qq].lit
//line simplify.w:695

//line simplify.w:712
										for l < ll {
											mems++
											qq = mem[qq].left
//line simplify.w:714
											if qq < clsHeadTop {
												ll = 0
											} else {
												mems++
												ll = mem[qq].lit
//line simplify.w:718
											}
										}

//line simplify.w:696
										if l > ll {
											break
										}
										mems++
										q = mem[q].left
//line simplify.w:700
										if q < clsHeadTop {
											l = 0
											break
										}
										mems++
										qq = mem[qq].left
//line simplify.w:705
										if qq < clsHeadTop {
											ll = 0
											break
										}
									}

//line simplify.w:671
									if l > ll {
										subFalse++
									} else {

//line simplify.w:722
										subTotal++
										for mems, p = mems+1, mem[cc].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
											mems++
											w = mem[p].lit
//line simplify.w:725

//line simplify.w:638
											mems++
											q, r = mem[p].up, mem[p].down
//line simplify.w:639
											mems += 2
											mem[q].down = r
											mem[r].up = q
//line simplify.w:640
											mems++
											vmem[w>>1].stable = 0
//line simplify.w:641
											mems += 2
											mem[w].lit--
//line simplify.w:642
											if mem[w].lit == 0 {

//line simplify.w:502
												kv = w >> 1
												mems++
												if vmem[kv].status == varNorm {
													mems++
													if w&1 != 0 {
														vmem[kv].status = forcedTrue
													} else {
														vmem[kv].status = forcedFalse
													}
													vmem[kv].link = toDo
													toDo = kv
//line simplify.w:512
												} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
													mems++
													vmem[kv].status = elimQuiet
													vmem[kv].stable = 1
//line simplify.w:514
												}

//line simplify.w:644
											}

//line simplify.w:726
										}
										mems++
										mem[mem[cc].right].left = avail
										avail = mem[cc].left
//line simplify.w:728
										mems++
										mem[cc].cls = 0
										clausesGone++

//line simplify.w:675
									}
								}

//line simplify.w:868

//line simplify.w:540
								for toDo != 0 {
									k = toDo
									mems++
									toDo = vmem[k].link
//line simplify.w:543
									if vmem[k].status != elimQuiet {
										if vmem[k].status == forcedTrue {
											l = k + k
										} else {
											l = k + k + 1
										}
										pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
										mems++
										vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
										for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
											mems++
											cd = mem[ll].cls
//line simplify.w:621
											for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
												if p != ll {
													mems++
													w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
													mems++
													q, r = mem[p].up, mem[p].down
//line simplify.w:639
													mems += 2
													mem[q].down = r
													mem[r].up = q
//line simplify.w:640
													mems++
													vmem[w>>1].stable = 0
//line simplify.w:641
													mems += 2
													mem[w].lit--
//line simplify.w:642
													if mem[w].lit == 0 {

//line simplify.w:502
														kv = w >> 1
														mems++
														if vmem[kv].status == varNorm {
															mems++
															if w&1 != 0 {
																vmem[kv].status = forcedTrue
															} else {
																vmem[kv].status = forcedFalse
															}
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:512
														} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
															mems++
															vmem[kv].status = elimQuiet
															vmem[kv].stable = 1
//line simplify.w:514
														}

//line simplify.w:644
													}

//line simplify.w:625
												}
											}
											mems++
											mem[mem[cd].right].left = avail
											avail = mem[cd].left
//line simplify.w:628
											mems++
											mem[cd].cls = 0
											clausesGone++
//line simplify.w:629
										}

//line simplify.w:552

//line simplify.w:582
										for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
											mems++
											cd = mem[ll].cls
//line simplify.w:584
											mems++
											p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
											mems += 2
											mem[p].right = q
											mem[q].left = p
//line simplify.w:586
											mems++
											mem[ll].left = avail
											avail = ll
//line simplify.w:587
											mems++
											j = mem[cd].cls - 1
//line simplify.w:588
											mems++
											mem[cd].cls = j
//line simplify.w:589
											if j == 1 {
												mems++
												if p == cd {
													w = mem[q].lit
												} else {
													w = mem[p].lit
												}

//line simplify.w:480
												kv = w >> 1
												mems++
												if w&1 != 0 {
													if vmem[kv].status == varNorm {
														mems++
														vmem[kv].status = forcedFalse
														vmem[kv].link = toDo
														toDo = kv
//line simplify.w:485
													} else if vmem[kv].status == forcedTrue {
														goto unsat
													}
												} else {
													if vmem[kv].status == varNorm {
														mems++
														vmem[kv].status = forcedTrue
														vmem[kv].link = toDo
														toDo = kv
//line simplify.w:491
													} else if vmem[kv].status == forcedFalse {
														goto unsat
													}
												}

//line simplify.w:597
											}

//line simplify.w:603
											bits2 = 0
											for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
												mems += 2
												bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
											}
											mems++
											mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
											mems++
											if cmem[cd-litHeadTop].link == 0 {
												mems++
												cmem[cd-litHeadTop].link = strengthened
												strengthened = cd
//line simplify.w:613
											}

//line simplify.w:600
										}

//line simplify.w:553
									}
									varsGone++
								}

//line simplify.w:562
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

//line simplify.w:869

//line simplify.w:875
								mems++
								if mem[c].cls != 0 {
									specialcase = 0

//line simplify.w:746
									mems += 3
									sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
//line simplify.w:747
									for mems, vv = mems+1, v; vv >= clsHeadTop; mems, vv = mems+1, mem[vv].left {
										mems++
										u = mem[vv].lit
//line simplify.w:749
										if specialcase != 0 {

//line simplify.w:1401
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

//line simplify.w:751
										}
										mems++
										ubits = bits &^ mem[u].sig
//line simplify.w:753
										for mems, pp = mems+1, mem[u^1].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
											strTries++
											mems++
											cc = mem[pp].cls
//line simplify.w:756
											mems++
											if ubits&^mem[cc].sig != 0 {
												continue
											}
											mems++
											if mem[cc].cls < sz {
												continue
											}

//line simplify.w:774
											mems++
											q, qq = v, mem[cc].left
//line simplify.w:775
											for {
												mems += 2
												l, ll = mem[q].lit, mem[qq].lit
//line simplify.w:777
												if l == u {
													l ^= 1
												}

//line simplify.w:712
												for l < ll {
													mems++
													qq = mem[qq].left
//line simplify.w:714
													if qq < clsHeadTop {
														ll = 0
													} else {
														mems++
														ll = mem[qq].lit
//line simplify.w:718
													}
												}

//line simplify.w:781
												if l > ll {
													break
												}
												mems++
												q = mem[q].left
//line simplify.w:785
												if q < clsHeadTop {
													l = 0
													break
												}
												mems++
												qq = mem[qq].left
//line simplify.w:790
												if qq < clsHeadTop {
													ll = 0
													break
												}
											}

//line simplify.w:765
											if l > ll {
												strFalse++
											} else {

//line simplify.w:800
												ccbits = 0
												strTotal++
												for mems, p = mems+1, mem[cc].right; ; mems, p = mems+1, mem[p].right {
													mems++
													w = mem[p].lit
//line simplify.w:804
													mems++
													vmem[w>>1].stable = 0
//line simplify.w:805
													if w == u^1 {
														break
													}
													mems++
													ccbits |= mem[w].sig
//line simplify.w:809
												}
												mems += 2
												mem[w].lit--
//line simplify.w:811
												if mem[w].lit == 0 {

//line simplify.w:502
													kv = w >> 1
													mems++
													if vmem[kv].status == varNorm {
														mems++
														if w&1 != 0 {
															vmem[kv].status = forcedTrue
														} else {
															vmem[kv].status = forcedFalse
														}
														vmem[kv].link = toDo
														toDo = kv
//line simplify.w:512
													} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
														mems++
														vmem[kv].status = elimQuiet
														vmem[kv].stable = 1
//line simplify.w:514
													}

//line simplify.w:813
												}

//line simplify.w:830
												mems++
												q, w = mem[p].up, mem[p].down
//line simplify.w:831
												mems += 2
												mem[q].down = w
												mem[w].up = q
//line simplify.w:832
												mems++
												q, w = mem[p].right, mem[p].left
//line simplify.w:833
												mems += 2
												mem[q].left = w
												mem[w].right = q
//line simplify.w:834
												mems++
												mem[p].left = avail
												avail = p

//line simplify.w:815
												for p = q; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
													mems++
													q = mem[p].lit
//line simplify.w:817
													mems++
													vmem[q>>1].stable = 0
//line simplify.w:818
													mems++
													ccbits |= mem[q].sig
//line simplify.w:819
												}
												mems++
												mem[cc].sig = ccbits

//line simplify.w:840
												mems += 2
												mem[cc].cls--
//line simplify.w:841
												if mem[cc].cls <= 1 {
													if mem[cc].cls == 0 {
														panic("sat: 이럴 수는 없다 (strengthening)")
													}
													mems += 2
													w = mem[mem[cc].right].lit
//line simplify.w:846

//line simplify.w:480
													kv = w >> 1
													mems++
													if w&1 != 0 {
														if vmem[kv].status == varNorm {
															mems++
															vmem[kv].status = forcedFalse
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:485
														} else if vmem[kv].status == forcedTrue {
															goto unsat
														}
													} else {
														if vmem[kv].status == varNorm {
															mems++
															vmem[kv].status = forcedTrue
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:491
														} else if vmem[kv].status == forcedFalse {
															goto unsat
														}
													}

//line simplify.w:847
												}

//line simplify.w:822
												mems++
												if cmem[cc-litHeadTop].link == 0 {
													mems++
													cmem[cc-litHeadTop].link = strengthened
													strengthened = cc
//line simplify.w:825
												}

//line simplify.w:769
											}
										}
									}

//line simplify.w:879

//line simplify.w:540
									for toDo != 0 {
										k = toDo
										mems++
										toDo = vmem[k].link
//line simplify.w:543
										if vmem[k].status != elimQuiet {
											if vmem[k].status == forcedTrue {
												l = k + k
											} else {
												l = k + k + 1
											}
											pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
											mems++
											vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
											for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
												mems++
												cd = mem[ll].cls
//line simplify.w:621
												for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
													if p != ll {
														mems++
														w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
														mems++
														q, r = mem[p].up, mem[p].down
//line simplify.w:639
														mems += 2
														mem[q].down = r
														mem[r].up = q
//line simplify.w:640
														mems++
														vmem[w>>1].stable = 0
//line simplify.w:641
														mems += 2
														mem[w].lit--
//line simplify.w:642
														if mem[w].lit == 0 {

//line simplify.w:502
															kv = w >> 1
															mems++
															if vmem[kv].status == varNorm {
																mems++
																if w&1 != 0 {
																	vmem[kv].status = forcedTrue
																} else {
																	vmem[kv].status = forcedFalse
																}
																vmem[kv].link = toDo
																toDo = kv
//line simplify.w:512
															} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
																mems++
																vmem[kv].status = elimQuiet
																vmem[kv].stable = 1
//line simplify.w:514
															}

//line simplify.w:644
														}

//line simplify.w:625
													}
												}
												mems++
												mem[mem[cd].right].left = avail
												avail = mem[cd].left
//line simplify.w:628
												mems++
												mem[cd].cls = 0
												clausesGone++
//line simplify.w:629
											}

//line simplify.w:552

//line simplify.w:582
											for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
												mems++
												cd = mem[ll].cls
//line simplify.w:584
												mems++
												p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
												mems += 2
												mem[p].right = q
												mem[q].left = p
//line simplify.w:586
												mems++
												mem[ll].left = avail
												avail = ll
//line simplify.w:587
												mems++
												j = mem[cd].cls - 1
//line simplify.w:588
												mems++
												mem[cd].cls = j
//line simplify.w:589
												if j == 1 {
													mems++
													if p == cd {
														w = mem[q].lit
													} else {
														w = mem[p].lit
													}

//line simplify.w:480
													kv = w >> 1
													mems++
													if w&1 != 0 {
														if vmem[kv].status == varNorm {
															mems++
															vmem[kv].status = forcedFalse
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:485
														} else if vmem[kv].status == forcedTrue {
															goto unsat
														}
													} else {
														if vmem[kv].status == varNorm {
															mems++
															vmem[kv].status = forcedTrue
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:491
														} else if vmem[kv].status == forcedFalse {
															goto unsat
														}
													}

//line simplify.w:597
												}

//line simplify.w:603
												bits2 = 0
												for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
													mems += 2
													bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
												}
												mems++
												mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
												mems++
												if cmem[cd-litHeadTop].link == 0 {
													mems++
													cmem[cd-litHeadTop].link = strengthened
													strengthened = cd
//line simplify.w:613
												}

//line simplify.w:600
											}

//line simplify.w:553
										}
										varsGone++
									}

//line simplify.w:562
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

//line simplify.w:880
									mems++
									mem[c].lit = round
//line simplify.w:881
									mems++
									cmem[c-litHeadTop].size = 0
//line simplify.w:882
								}

//line simplify.w:870
							}
						}
						c = csave

//line simplify.w:1371
					} else if cmem[c-litHeadTop].size&1 != 0 {
						panic("sat: 이럴 수는 없다 (new clause not all new)")
					}
					if cmem[c-litHeadTop].size&3 != 0 {

//line simplify.w:1384
						switch {
						case cmem[c-litHeadTop].size&1 != 0:
							specialcase = 0
						case cmem[c-litHeadTop].size>>2 < mem[c].cls-1:
							specialcase = -1
						default:
							specialcase = 1
						}
						if specialcase >= 0 {

//line simplify.w:746
							mems += 3
							sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
//line simplify.w:747
							for mems, vv = mems+1, v; vv >= clsHeadTop; mems, vv = mems+1, mem[vv].left {
								mems++
								u = mem[vv].lit
//line simplify.w:749
								if specialcase != 0 {

//line simplify.w:1401
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

//line simplify.w:751
								}
								mems++
								ubits = bits &^ mem[u].sig
//line simplify.w:753
								for mems, pp = mems+1, mem[u^1].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
									strTries++
									mems++
									cc = mem[pp].cls
//line simplify.w:756
									mems++
									if ubits&^mem[cc].sig != 0 {
										continue
									}
									mems++
									if mem[cc].cls < sz {
										continue
									}

//line simplify.w:774
									mems++
									q, qq = v, mem[cc].left
//line simplify.w:775
									for {
										mems += 2
										l, ll = mem[q].lit, mem[qq].lit
//line simplify.w:777
										if l == u {
											l ^= 1
										}

//line simplify.w:712
										for l < ll {
											mems++
											qq = mem[qq].left
//line simplify.w:714
											if qq < clsHeadTop {
												ll = 0
											} else {
												mems++
												ll = mem[qq].lit
//line simplify.w:718
											}
										}

//line simplify.w:781
										if l > ll {
											break
										}
										mems++
										q = mem[q].left
//line simplify.w:785
										if q < clsHeadTop {
											l = 0
											break
										}
										mems++
										qq = mem[qq].left
//line simplify.w:790
										if qq < clsHeadTop {
											ll = 0
											break
										}
									}

//line simplify.w:765
									if l > ll {
										strFalse++
									} else {

//line simplify.w:800
										ccbits = 0
										strTotal++
										for mems, p = mems+1, mem[cc].right; ; mems, p = mems+1, mem[p].right {
											mems++
											w = mem[p].lit
//line simplify.w:804
											mems++
											vmem[w>>1].stable = 0
//line simplify.w:805
											if w == u^1 {
												break
											}
											mems++
											ccbits |= mem[w].sig
//line simplify.w:809
										}
										mems += 2
										mem[w].lit--
//line simplify.w:811
										if mem[w].lit == 0 {

//line simplify.w:502
											kv = w >> 1
											mems++
											if vmem[kv].status == varNorm {
												mems++
												if w&1 != 0 {
													vmem[kv].status = forcedTrue
												} else {
													vmem[kv].status = forcedFalse
												}
												vmem[kv].link = toDo
												toDo = kv
//line simplify.w:512
											} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
												mems++
												vmem[kv].status = elimQuiet
												vmem[kv].stable = 1
//line simplify.w:514
											}

//line simplify.w:813
										}

//line simplify.w:830
										mems++
										q, w = mem[p].up, mem[p].down
//line simplify.w:831
										mems += 2
										mem[q].down = w
										mem[w].up = q
//line simplify.w:832
										mems++
										q, w = mem[p].right, mem[p].left
//line simplify.w:833
										mems += 2
										mem[q].left = w
										mem[w].right = q
//line simplify.w:834
										mems++
										mem[p].left = avail
										avail = p

//line simplify.w:815
										for p = q; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
											mems++
											q = mem[p].lit
//line simplify.w:817
											mems++
											vmem[q>>1].stable = 0
//line simplify.w:818
											mems++
											ccbits |= mem[q].sig
//line simplify.w:819
										}
										mems++
										mem[cc].sig = ccbits

//line simplify.w:840
										mems += 2
										mem[cc].cls--
//line simplify.w:841
										if mem[cc].cls <= 1 {
											if mem[cc].cls == 0 {
												panic("sat: 이럴 수는 없다 (strengthening)")
											}
											mems += 2
											w = mem[mem[cc].right].lit
//line simplify.w:846

//line simplify.w:480
											kv = w >> 1
											mems++
											if w&1 != 0 {
												if vmem[kv].status == varNorm {
													mems++
													vmem[kv].status = forcedFalse
													vmem[kv].link = toDo
													toDo = kv
//line simplify.w:485
												} else if vmem[kv].status == forcedTrue {
													goto unsat
												}
											} else {
												if vmem[kv].status == varNorm {
													mems++
													vmem[kv].status = forcedTrue
													vmem[kv].link = toDo
													toDo = kv
//line simplify.w:491
												} else if vmem[kv].status == forcedFalse {
													goto unsat
												}
											}

//line simplify.w:847
										}

//line simplify.w:822
										mems++
										if cmem[cc-litHeadTop].link == 0 {
											mems++
											cmem[cc-litHeadTop].link = strengthened
											strengthened = cc
//line simplify.w:825
										}

//line simplify.w:769
									}
								}
							}

//line simplify.w:1394

//line simplify.w:859
							csave = c

//line simplify.w:540
							for toDo != 0 {
								k = toDo
								mems++
								toDo = vmem[k].link
//line simplify.w:543
								if vmem[k].status != elimQuiet {
									if vmem[k].status == forcedTrue {
										l = k + k
									} else {
										l = k + k + 1
									}
									pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
									mems++
									vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
									for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
										mems++
										cd = mem[ll].cls
//line simplify.w:621
										for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
											if p != ll {
												mems++
												w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
												mems++
												q, r = mem[p].up, mem[p].down
//line simplify.w:639
												mems += 2
												mem[q].down = r
												mem[r].up = q
//line simplify.w:640
												mems++
												vmem[w>>1].stable = 0
//line simplify.w:641
												mems += 2
												mem[w].lit--
//line simplify.w:642
												if mem[w].lit == 0 {

//line simplify.w:502
													kv = w >> 1
													mems++
													if vmem[kv].status == varNorm {
														mems++
														if w&1 != 0 {
															vmem[kv].status = forcedTrue
														} else {
															vmem[kv].status = forcedFalse
														}
														vmem[kv].link = toDo
														toDo = kv
//line simplify.w:512
													} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
														mems++
														vmem[kv].status = elimQuiet
														vmem[kv].stable = 1
//line simplify.w:514
													}

//line simplify.w:644
												}

//line simplify.w:625
											}
										}
										mems++
										mem[mem[cd].right].left = avail
										avail = mem[cd].left
//line simplify.w:628
										mems++
										mem[cd].cls = 0
										clausesGone++
//line simplify.w:629
									}

//line simplify.w:552

//line simplify.w:582
									for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
										mems++
										cd = mem[ll].cls
//line simplify.w:584
										mems++
										p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
										mems += 2
										mem[p].right = q
										mem[q].left = p
//line simplify.w:586
										mems++
										mem[ll].left = avail
										avail = ll
//line simplify.w:587
										mems++
										j = mem[cd].cls - 1
//line simplify.w:588
										mems++
										mem[cd].cls = j
//line simplify.w:589
										if j == 1 {
											mems++
											if p == cd {
												w = mem[q].lit
											} else {
												w = mem[p].lit
											}

//line simplify.w:480
											kv = w >> 1
											mems++
											if w&1 != 0 {
												if vmem[kv].status == varNorm {
													mems++
													vmem[kv].status = forcedFalse
													vmem[kv].link = toDo
													toDo = kv
//line simplify.w:485
												} else if vmem[kv].status == forcedTrue {
													goto unsat
												}
											} else {
												if vmem[kv].status == varNorm {
													mems++
													vmem[kv].status = forcedTrue
													vmem[kv].link = toDo
													toDo = kv
//line simplify.w:491
												} else if vmem[kv].status == forcedFalse {
													goto unsat
												}
											}

//line simplify.w:597
										}

//line simplify.w:603
										bits2 = 0
										for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
											mems += 2
											bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
										}
										mems++
										mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
										mems++
										if cmem[cd-litHeadTop].link == 0 {
											mems++
											cmem[cd-litHeadTop].link = strengthened
											strengthened = cd
//line simplify.w:613
										}

//line simplify.w:600
									}

//line simplify.w:553
								}
								varsGone++
							}

//line simplify.w:562
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

//line simplify.w:861
							for strengthened != sentinel {
								c = strengthened
								mems++
								strengthened = cmem[c-litHeadTop].link
//line simplify.w:864
								mems++
								if mem[c].cls != 0 {
									mems++
									cmem[c-litHeadTop].link = 0
//line simplify.w:867

//line simplify.w:679
									mems += 3
									p = mem[c].right
									l = mem[p].lit
									k = mem[l].lit
//line simplify.w:680
									for mems, p = mems+1, mem[p].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
										mems++
										ll = mem[p].lit
//line simplify.w:682
										mems++
										if mem[ll].lit < k {
											k, l = mem[ll].lit, ll
										}
									}

//line simplify.w:655
									mems += 3
									sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
//line simplify.w:656
									for mems, pp = mems+1, mem[l].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
										mems++
										cc = mem[pp].cls
//line simplify.w:658
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

//line simplify.w:692
										mems++
										q, qq = v, mem[cc].left
//line simplify.w:693
										for {
											mems += 2
											l, ll = mem[q].lit, mem[qq].lit
//line simplify.w:695

//line simplify.w:712
											for l < ll {
												mems++
												qq = mem[qq].left
//line simplify.w:714
												if qq < clsHeadTop {
													ll = 0
												} else {
													mems++
													ll = mem[qq].lit
//line simplify.w:718
												}
											}

//line simplify.w:696
											if l > ll {
												break
											}
											mems++
											q = mem[q].left
//line simplify.w:700
											if q < clsHeadTop {
												l = 0
												break
											}
											mems++
											qq = mem[qq].left
//line simplify.w:705
											if qq < clsHeadTop {
												ll = 0
												break
											}
										}

//line simplify.w:671
										if l > ll {
											subFalse++
										} else {

//line simplify.w:722
											subTotal++
											for mems, p = mems+1, mem[cc].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
												mems++
												w = mem[p].lit
//line simplify.w:725

//line simplify.w:638
												mems++
												q, r = mem[p].up, mem[p].down
//line simplify.w:639
												mems += 2
												mem[q].down = r
												mem[r].up = q
//line simplify.w:640
												mems++
												vmem[w>>1].stable = 0
//line simplify.w:641
												mems += 2
												mem[w].lit--
//line simplify.w:642
												if mem[w].lit == 0 {

//line simplify.w:502
													kv = w >> 1
													mems++
													if vmem[kv].status == varNorm {
														mems++
														if w&1 != 0 {
															vmem[kv].status = forcedTrue
														} else {
															vmem[kv].status = forcedFalse
														}
														vmem[kv].link = toDo
														toDo = kv
//line simplify.w:512
													} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
														mems++
														vmem[kv].status = elimQuiet
														vmem[kv].stable = 1
//line simplify.w:514
													}

//line simplify.w:644
												}

//line simplify.w:726
											}
											mems++
											mem[mem[cc].right].left = avail
											avail = mem[cc].left
//line simplify.w:728
											mems++
											mem[cc].cls = 0
											clausesGone++

//line simplify.w:675
										}
									}

//line simplify.w:868

//line simplify.w:540
									for toDo != 0 {
										k = toDo
										mems++
										toDo = vmem[k].link
//line simplify.w:543
										if vmem[k].status != elimQuiet {
											if vmem[k].status == forcedTrue {
												l = k + k
											} else {
												l = k + k + 1
											}
											pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
											mems++
											vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
											for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
												mems++
												cd = mem[ll].cls
//line simplify.w:621
												for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
													if p != ll {
														mems++
														w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
														mems++
														q, r = mem[p].up, mem[p].down
//line simplify.w:639
														mems += 2
														mem[q].down = r
														mem[r].up = q
//line simplify.w:640
														mems++
														vmem[w>>1].stable = 0
//line simplify.w:641
														mems += 2
														mem[w].lit--
//line simplify.w:642
														if mem[w].lit == 0 {

//line simplify.w:502
															kv = w >> 1
															mems++
															if vmem[kv].status == varNorm {
																mems++
																if w&1 != 0 {
																	vmem[kv].status = forcedTrue
																} else {
																	vmem[kv].status = forcedFalse
																}
																vmem[kv].link = toDo
																toDo = kv
//line simplify.w:512
															} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
																mems++
																vmem[kv].status = elimQuiet
																vmem[kv].stable = 1
//line simplify.w:514
															}

//line simplify.w:644
														}

//line simplify.w:625
													}
												}
												mems++
												mem[mem[cd].right].left = avail
												avail = mem[cd].left
//line simplify.w:628
												mems++
												mem[cd].cls = 0
												clausesGone++
//line simplify.w:629
											}

//line simplify.w:552

//line simplify.w:582
											for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
												mems++
												cd = mem[ll].cls
//line simplify.w:584
												mems++
												p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
												mems += 2
												mem[p].right = q
												mem[q].left = p
//line simplify.w:586
												mems++
												mem[ll].left = avail
												avail = ll
//line simplify.w:587
												mems++
												j = mem[cd].cls - 1
//line simplify.w:588
												mems++
												mem[cd].cls = j
//line simplify.w:589
												if j == 1 {
													mems++
													if p == cd {
														w = mem[q].lit
													} else {
														w = mem[p].lit
													}

//line simplify.w:480
													kv = w >> 1
													mems++
													if w&1 != 0 {
														if vmem[kv].status == varNorm {
															mems++
															vmem[kv].status = forcedFalse
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:485
														} else if vmem[kv].status == forcedTrue {
															goto unsat
														}
													} else {
														if vmem[kv].status == varNorm {
															mems++
															vmem[kv].status = forcedTrue
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:491
														} else if vmem[kv].status == forcedFalse {
															goto unsat
														}
													}

//line simplify.w:597
												}

//line simplify.w:603
												bits2 = 0
												for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
													mems += 2
													bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
												}
												mems++
												mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
												mems++
												if cmem[cd-litHeadTop].link == 0 {
													mems++
													cmem[cd-litHeadTop].link = strengthened
													strengthened = cd
//line simplify.w:613
												}

//line simplify.w:600
											}

//line simplify.w:553
										}
										varsGone++
									}

//line simplify.w:562
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

//line simplify.w:869

//line simplify.w:875
									mems++
									if mem[c].cls != 0 {
										specialcase = 0

//line simplify.w:746
										mems += 3
										sz, bits, v = mem[c].cls, mem[c].sig, mem[c].left
//line simplify.w:747
										for mems, vv = mems+1, v; vv >= clsHeadTop; mems, vv = mems+1, mem[vv].left {
											mems++
											u = mem[vv].lit
//line simplify.w:749
											if specialcase != 0 {

//line simplify.w:1401
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

//line simplify.w:751
											}
											mems++
											ubits = bits &^ mem[u].sig
//line simplify.w:753
											for mems, pp = mems+1, mem[u^1].down; pp >= litHeadTop; mems, pp = mems+1, mem[pp].down {
												strTries++
												mems++
												cc = mem[pp].cls
//line simplify.w:756
												mems++
												if ubits&^mem[cc].sig != 0 {
													continue
												}
												mems++
												if mem[cc].cls < sz {
													continue
												}

//line simplify.w:774
												mems++
												q, qq = v, mem[cc].left
//line simplify.w:775
												for {
													mems += 2
													l, ll = mem[q].lit, mem[qq].lit
//line simplify.w:777
													if l == u {
														l ^= 1
													}

//line simplify.w:712
													for l < ll {
														mems++
														qq = mem[qq].left
//line simplify.w:714
														if qq < clsHeadTop {
															ll = 0
														} else {
															mems++
															ll = mem[qq].lit
//line simplify.w:718
														}
													}

//line simplify.w:781
													if l > ll {
														break
													}
													mems++
													q = mem[q].left
//line simplify.w:785
													if q < clsHeadTop {
														l = 0
														break
													}
													mems++
													qq = mem[qq].left
//line simplify.w:790
													if qq < clsHeadTop {
														ll = 0
														break
													}
												}

//line simplify.w:765
												if l > ll {
													strFalse++
												} else {

//line simplify.w:800
													ccbits = 0
													strTotal++
													for mems, p = mems+1, mem[cc].right; ; mems, p = mems+1, mem[p].right {
														mems++
														w = mem[p].lit
//line simplify.w:804
														mems++
														vmem[w>>1].stable = 0
//line simplify.w:805
														if w == u^1 {
															break
														}
														mems++
														ccbits |= mem[w].sig
//line simplify.w:809
													}
													mems += 2
													mem[w].lit--
//line simplify.w:811
													if mem[w].lit == 0 {

//line simplify.w:502
														kv = w >> 1
														mems++
														if vmem[kv].status == varNorm {
															mems++
															if w&1 != 0 {
																vmem[kv].status = forcedTrue
															} else {
																vmem[kv].status = forcedFalse
															}
															vmem[kv].link = toDo
															toDo = kv
//line simplify.w:512
														} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
															mems++
															vmem[kv].status = elimQuiet
															vmem[kv].stable = 1
//line simplify.w:514
														}

//line simplify.w:813
													}

//line simplify.w:830
													mems++
													q, w = mem[p].up, mem[p].down
//line simplify.w:831
													mems += 2
													mem[q].down = w
													mem[w].up = q
//line simplify.w:832
													mems++
													q, w = mem[p].right, mem[p].left
//line simplify.w:833
													mems += 2
													mem[q].left = w
													mem[w].right = q
//line simplify.w:834
													mems++
													mem[p].left = avail
													avail = p

//line simplify.w:815
													for p = q; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
														mems++
														q = mem[p].lit
//line simplify.w:817
														mems++
														vmem[q>>1].stable = 0
//line simplify.w:818
														mems++
														ccbits |= mem[q].sig
//line simplify.w:819
													}
													mems++
													mem[cc].sig = ccbits

//line simplify.w:840
													mems += 2
													mem[cc].cls--
//line simplify.w:841
													if mem[cc].cls <= 1 {
														if mem[cc].cls == 0 {
															panic("sat: 이럴 수는 없다 (strengthening)")
														}
														mems += 2
														w = mem[mem[cc].right].lit
//line simplify.w:846

//line simplify.w:480
														kv = w >> 1
														mems++
														if w&1 != 0 {
															if vmem[kv].status == varNorm {
																mems++
																vmem[kv].status = forcedFalse
																vmem[kv].link = toDo
																toDo = kv
//line simplify.w:485
															} else if vmem[kv].status == forcedTrue {
																goto unsat
															}
														} else {
															if vmem[kv].status == varNorm {
																mems++
																vmem[kv].status = forcedTrue
																vmem[kv].link = toDo
																toDo = kv
//line simplify.w:491
															} else if vmem[kv].status == forcedFalse {
																goto unsat
															}
														}

//line simplify.w:847
													}

//line simplify.w:822
													mems++
													if cmem[cc-litHeadTop].link == 0 {
														mems++
														cmem[cc-litHeadTop].link = strengthened
														strengthened = cc
//line simplify.w:825
													}

//line simplify.w:769
												}
											}
										}

//line simplify.w:879

//line simplify.w:540
										for toDo != 0 {
											k = toDo
											mems++
											toDo = vmem[k].link
//line simplify.w:543
											if vmem[k].status != elimQuiet {
												if vmem[k].status == forcedTrue {
													l = k + k
												} else {
													l = k + k + 1
												}
												pre.erp = append(pre.erp, erpCell{Lit(l), erpDef})
												mems++
												vmem[k].stable = 1
//line simplify.w:551

//line simplify.w:619
												for mems, ll = mems+1, mem[l].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
													mems++
													cd = mem[ll].cls
//line simplify.w:621
													for mems, p = mems+1, mem[cd].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
														if p != ll {
															mems++
															w = mem[p].lit
//line simplify.w:624

//line simplify.w:638
															mems++
															q, r = mem[p].up, mem[p].down
//line simplify.w:639
															mems += 2
															mem[q].down = r
															mem[r].up = q
//line simplify.w:640
															mems++
															vmem[w>>1].stable = 0
//line simplify.w:641
															mems += 2
															mem[w].lit--
//line simplify.w:642
															if mem[w].lit == 0 {

//line simplify.w:502
																kv = w >> 1
																mems++
																if vmem[kv].status == varNorm {
																	mems++
																	if w&1 != 0 {
																		vmem[kv].status = forcedTrue
																	} else {
																		vmem[kv].status = forcedFalse
																	}
																	vmem[kv].link = toDo
																	toDo = kv
//line simplify.w:512
																} else if w&1 != 0 && vmem[kv].status == forcedFalse || w&1 == 0 && vmem[kv].status == forcedTrue {
																	mems++
																	vmem[kv].status = elimQuiet
																	vmem[kv].stable = 1
//line simplify.w:514
																}

//line simplify.w:644
															}

//line simplify.w:625
														}
													}
													mems++
													mem[mem[cd].right].left = avail
													avail = mem[cd].left
//line simplify.w:628
													mems++
													mem[cd].cls = 0
													clausesGone++
//line simplify.w:629
												}

//line simplify.w:552

//line simplify.w:582
												for mems, ll = mems+1, mem[l^1].down; ll >= litHeadTop; mems, ll = mems+1, mem[ll].down {
													mems++
													cd = mem[ll].cls
//line simplify.w:584
													mems++
													p, q = mem[ll].left, mem[ll].right
//line simplify.w:585
													mems += 2
													mem[p].right = q
													mem[q].left = p
//line simplify.w:586
													mems++
													mem[ll].left = avail
													avail = ll
//line simplify.w:587
													mems++
													j = mem[cd].cls - 1
//line simplify.w:588
													mems++
													mem[cd].cls = j
//line simplify.w:589
													if j == 1 {
														mems++
														if p == cd {
															w = mem[q].lit
														} else {
															w = mem[p].lit
														}

//line simplify.w:480
														kv = w >> 1
														mems++
														if w&1 != 0 {
															if vmem[kv].status == varNorm {
																mems++
																vmem[kv].status = forcedFalse
																vmem[kv].link = toDo
																toDo = kv
//line simplify.w:485
															} else if vmem[kv].status == forcedTrue {
																goto unsat
															}
														} else {
															if vmem[kv].status == varNorm {
																mems++
																vmem[kv].status = forcedTrue
																vmem[kv].link = toDo
																toDo = kv
//line simplify.w:491
															} else if vmem[kv].status == forcedFalse {
																goto unsat
															}
														}

//line simplify.w:597
													}

//line simplify.w:603
													bits2 = 0
													for mems, t2 = mems+1, mem[cd].right; t2 >= clsHeadTop; mems, t2 = mems+1, mem[t2].right {
														mems += 2
														bits2 |= mem[mem[t2].lit].sig
//line simplify.w:606
													}
													mems++
													mem[cd].sig = bits2

//line simplify.w:599

//line simplify.w:610
													mems++
													if cmem[cd-litHeadTop].link == 0 {
														mems++
														cmem[cd-litHeadTop].link = strengthened
														strengthened = cd
//line simplify.w:613
													}

//line simplify.w:600
												}

//line simplify.w:553
											}
											varsGone++
										}

//line simplify.w:562
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

//line simplify.w:880
										mems++
										mem[c].lit = round
//line simplify.w:881
										mems++
										cmem[c-litHeadTop].size = 0
//line simplify.w:882
									}

//line simplify.w:870
								}
							}
							c = csave

//line simplify.w:1395
						}

//line simplify.w:1376
					}

//line simplify.w:1349
				}
				mems++
				cmem[c-litHeadTop].size = 0
//line simplify.w:1351
			}
		}

//line simplify.w:1311
	}
	round = min(round, uint32(par.MaxRounds))

//line simplify.w:232
finishUp:

//line simplify.w:1417
	for c = litHeadTop; c < clsHeadTop; c++ {
		mems++
		if mem[c].cls != 0 {
			first := firstLit
			for mems, p = mems+1, mem[c].right; p >= clsHeadTop; mems, p = mems+1, mem[p].right {
				mems++
				pre.cells = append(pre.cells, Lit(mem[p].lit)|first)
//line simplify.w:1423
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

//line simplify.w:234
	goto record
unsat:
	status, pre.unsat = Unsat, true
record:

//line simplify.w:1442
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

//line simplify.w:239
	return status, err
}

//line simplify.w:1459
func (s *Solver) solvePreprocessed(ctx context.Context) (Status, error) {
	pre := s.pre
	s.model, s.truth, s.stats = nil, nil, Stats{}
	if pre.unsat {
		return Unsat, nil
	}
	var sol []Lit
	if len(pre.cells) > 0 {

//line simplify.w:1479
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

//line simplify.w:1494
			if renum[l.Var()] == 0 {
				renum[l.Var()] = red.NewVar().Var()
				old = append(old, l.Var())
			}
			nl := Pos(renum[l.Var()])
			if l.IsNeg() {
				nl = nl.Not()
			}
			clause = append(clause, nl)

//line simplify.w:1490
		}
		red.AddClause(clause...)

//line simplify.w:1468

//line simplify.w:1505
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

//line simplify.w:1469
	}

//line simplify.w:1523
	val := make([]int8, 2*s.NumVars()+2)
	model := make([]Lit, 0, s.NumVars())
	for i := len(sol) - 1; i >= 0; i-- {
		model = append(model, sol[i])
		val[sol[i]], val[sol[i]^1] = 1, -1
	}

//line simplify.w:1543
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

//line simplify.w:1562
			if val[e.lit] == 0 {
				model = append(model, e.lit)
				val[e.lit], val[e.lit^1] = 1, -1
			}
			if val[e.lit] == 1 {
				vv = true
			}

//line simplify.w:1554
			if e.flag == erpFirst {
				break
			}
		}

//line simplify.w:1571
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

//line simplify.w:1559
	}

//line simplify.w:1530
	s.model = model
	s.truth = make([]bool, s.NumVars()+1)
	for _, l := range model {
		s.truth[l.Var()] = !l.IsNeg()
	}

//line simplify.w:1471
	return Sat, nil
}

//line simplify.w:1589
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

//line simplify.w:1611
func (s *Solver) WriteERP(w io.Writer) error {
	if s.pre == nil {
		return errors.New("sat: 전처리한 결과가 없다")
	}
	var b strings.Builder
	erp := s.pre.erp
	for i := 0; i < len(erp); {

//line simplify.w:1625
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

//line simplify.w:1619
	}
	_, err := io.WriteString(w, b.String())
	return err
}
