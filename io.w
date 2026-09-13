\input kotexgweb

\def\title{절 읽기}

@s Lit int
@s Solver int

@* 들어가며.
크누스의 SAT 풀이기들은 모두 같은 ``입출력 껍데기''(I/O wrapper)를 쓴다. 그는
이것을 모든 판에 그대로 옮겨 붙이려고 ``짧고 단순하게'' 짰다고 했다. 이 글은 그
껍데기의 입력 쪽을 \GO/로 옮긴다. 읽는 형식은 둘이다. 하나는 크누스 자신의
형식이고, 다른 하나는 SAT 경진대회가 쓰는 DIMACS 형식이다.
@^Knuth, Donald Ervin@>

읽은 리터럴은 옆집 \.{sat.w}의 세 걸음, 곧 |beginClause|, |addLit|, |endClause|로
풀이기에 쌓는다. 늘 참인 절과 겹친 리터럴은 그 셋이 크누스와 똑같이 다루므로,
여기서는 글자를 리터럴로 바꾸기만 하면 된다. 뼈대는 다음과 같다.

@c
package sat

import (
	"bufio"
	"fmt"
	"io"
	"strconv"
)

@<자료 구조@>

@<함수들@>

@ 읽다가 잘못을 만나면 몇째 줄에서 무엇이 잘못되었는지 알려 준다. 원본은 이럴 때
사연을 찍고 곧바로 |exit|하는데, 꾸러미가 남의 프로그램을 끝내 버릴 수는 없으니
잘못을 값으로 돌려준다. 잘못을 돌려준 풀이기에는 절이 반쯤 쌓여 있을 수 있으므로
더 쓰지 말고 버려야 한다.

@<자료 구조@>=
type ParseError struct {
	Line int    // 잘못이 난 줄, 1부터 센다
	Msg  string // 무엇이 잘못인가
}

@ @<함수들@>=
func (e *ParseError) Error() string {
	return fmt.Sprintf("sat: %d번째 줄: %s", e.Line, e.Msg)
}

@* 크누스의 형식.
크누스의 입력은 한 줄에 절이 하나다. 절은 빈칸으로 가른 리터럴들이고, 리터럴은
변수의 이름이거나 이름 앞에 \.{\~}를 붙인 것(부정)이다. 이름은 \.{!}에서 \.{\}}까지의
ASCII 글자로 짓는다. 가령 Rivest의 유명한 네 변수 절들({\sl TAOCP\/} 6.5--(13),
7.1.1--(32))은 다음 여덟 줄이 된다.
@^Rivest, Ronald Linn@>
$$\chardef~=`\~
\vcenter{\halign{\tt#\cr
x2 x3 ~x4\cr
x1 x3 x4\cr
~x1 x2 x4\cr
~x1 ~x2 x3\cr
~x2 ~x3 x4\cr
~x1 ~x3 ~x4\cr
x1 ~x2 ~x4\cr
x1 x2 ~x3\cr}}$$
원본은 이 입력에 변수를 \.{x2}, \.{x3}, \.{x4}, \.{x1}의 차례로 번호 매긴다.
이름이 처음 나온 차례다.

@ 주석은 따로 없다. 크누스는 \.{\~\ }로 시작하는 줄을 주석으로 치는데, 들여다보면
이것은 규칙이 아니라 결과다. 원본은 뒤에 이름이 붙지 않은 \.{\~}를 ``거짓의
부정''으로, 곧 참으로 읽는다. 참이 든 절은 늘 참이니 버려지고, 그 자리에서
읽기를 멈추니 줄의 나머지는 무엇이 적혀 있든 상관없다. 그래서 \.{\~\ }로
시작하는 줄은 조용히 사라진다. 원본은 늘 참인 절을 버릴 때마다 사연을 한 줄씩
찍되 주석 줄에는 찍지 않는다. 꾸러미는 어느 쪽이든 조용히 버린다.

원본과 다르게 한 곳이 세 군데 있다. 첫째로 줄의 길이와 이름의 길이를 따지지
않는다. 원본은 1024바이트짜리 버퍼(명령 줄 \.b로 바꾼다)와 여덟 글자짜리 이름
칸을 쓴다. 둘째로 줄 끝의 \.{\\r}을 너그럽게 봐준다. 윈도에서 만든 파일도 읽을
수 있게 하려는 것이다. 셋째로 \.{\~\~x}처럼 부정 뒤의 이름이 다시 \.{\~}로
시작하면 잘못으로 친다. 원본은 이 경우 해시용 난수 표의 끝을 넘어 읽는다.

@ 크누스의 형식으로 적힌 절들을 |r|에서 읽어 쌓는 문. 한 줄을 읽을 때마다 절을
하나 시작하고, 리터럴을 하나 만들 때마다 곧바로 보탠다. 절이 늘 참이 되면 줄의
나머지를 건너뛴다. 리터럴이 하나도 없는 줄은 원본처럼 건너뛴다.

@<함수들@>=
func (s *Solver) ReadKnuth(r io.Reader) error {
	sc := bufio.NewScanner(r)
	sc.Buffer(nil, 1<<30)
	line := 0
lines:
	for sc.Scan() {
		line++
		buf := sc.Bytes()
		s.beginClause()
		for j := 0; ; {
			for j < len(buf) && buf[j] == ' ' {
				j++
			}
			if j == len(buf) {
				break
			}
			@<|buf[j]|에서 시작하는 리터럴 |l|을 읽는다@>
			if !s.addLit(l) {
				continue lines
			}
		}
		if len(s.cells) > s.start {
			s.endClause()
		}
	}
	return sc.Err()
}

@ 원본은 빈칸이 아닌 글자가 나올 때마다 먼저 그 글자가 인쇄 가능한 ASCII인지
따진다. 탭도 여기서 걸린다. 홀로 선 \.{\~}는 앞에서 말한 대로 참이다.

@<|buf[j]|에서 시작하는 리터럴 |l|을 읽는다@>=
if buf[j] < ' ' || buf[j] > '~' {
	return &ParseError{line, fmt.Sprintf("쓸 수 없는 글자 %#02x", buf[j])}
}
neg := buf[j] == '~'
if neg {
	j++
}
i := j
for j < len(buf) && buf[j] > ' ' && buf[j] <= '~' {
	j++
}
if i == j {
	s.cells = s.cells[:s.start]
	continue lines
}
@<이름 |buf[i:j]|의 변수로 리터럴 |l|을 만든다@>

@ 사전을 찾을 때 |string(buf[i:j])|는 컴파일러가 새 문자열을 만들지 않고 처리한다.
처음 보는 이름일 때만 |Lookup|을 불러 문자열을 만든다. 벤치마크 가운데 큰 것은
리터럴이 수백만 개이니 아낄 만하다.

@<이름 |buf[i:j]|의 변수로...@>=
if buf[i] == '~' {
	return &ParseError{line, fmt.Sprintf("이름 %q가 ~로 시작한다", buf[i:j])}
}
v, ok := s.index[string(buf[i:j])]
if !ok {
	v = s.Lookup(string(buf[i:j])).Var()
}
l := Pos(v)
if neg {
	l = l.Not()
}

@* DIMACS 형식.
DIMACS 형식은 \.c로 시작하는 주석 줄들로 열 수 있고, 그다음에 머리줄
`\.{p cnf} $n$ $m$'이 온다. 여기서 $n$은 변수의 수, $m$은 절의 수다. 그 뒤로
0이 아닌 정수들이 이어지며, 0 하나가 절 하나를 끝낸다. 정수 $k$는 변수~$k$를,
$-k$는 그 부정을 뜻한다. 줄바꿈은 빈칸과 다를 바 없어서 절 하나가 여러 줄에 걸칠
수도 있다.

크누스는 이 형식을 직접 읽지 않는다. 걸러 내는 프로그램 \.{DIMACS-TO-SAT}이
$k$를 이름 \.{k}로, $-k$를 \.{\~k}로 바꿔 적으면 풀이기가 그것을 읽는다. 나도
DIMACS 변수~$k$에 이름 \.{k}를 붙인다. 그러면 \.{.cnf} 파일을 곧바로 읽든
\.{DIMACS-TO-SAT}을 거쳐 읽든 변수 번호가 같아지고, 따라서 mem 수도 같아진다.
DIMACS 번호와 풀이기의 변수 번호는 일반적으로 다르다. 번호는 이름이 처음 나온
차례로 매겨지기 때문이다. DIMACS 변수~$k$의 리터럴이 필요하면 |Lookup| 문에
|strconv.Itoa(k)|를 주면 된다.
@^DIMACS-TO-SAT@>

@ 이번에도 원본과 다르게 한 곳이 두 군데 있다. 첫째로 빈 절(0 하나)을 빈 절로 받는다.
\.{DIMACS-TO-SAT}은 빈 절을 빈 줄로 옮기고 풀이기는 빈 줄을 건너뛰니, 원본을 거치면
빈 절이 소리 없이 사라진다. 경고를 한 줄 찍기는 하지만 풀이의 답이 틀려진다. 둘째로
SATLIB의 오래된 파일들처럼 \.{\%}로 시작하는 줄이 나오면 거기서 입력을 끝낸다.
절의 수 $m$은 원본처럼 확인하지 않는다(원본은 어긋나면 경고만 한다).

@ DIMACS 형식으로 적힌 절들을 |r|에서 읽어 쌓는 문. 절이 줄을 넘나들 수 있으므로
``절을 쌓는 중인가''(|open|)와 ``그 절이 늘 참이라 이미 버려졌는가''(|dead|)를 줄
밖에서 기억한다. DIMACS 번호에서 변수 번호로 가는 표 |dimacs|는 머리줄을 읽을 때
만든다. 이 표가 아직 없으면 머리줄을 못 본 것이다. 마지막 절이 0으로 끝나지 않았으면
원본처럼 그 절을 마쳐 준다.

@<함수들@>=
func (s *Solver) ReadDIMACS(r io.Reader) error {
	sc := bufio.NewScanner(r)
	sc.Buffer(nil, 1<<30)
	var dimacs []int
	open, dead := false, false
	line := 0
lines:
	for sc.Scan() {
		line++
		buf := sc.Bytes()
		@<DIMACS의 한 줄 |buf|를 처리한다@>
	}
	if err := sc.Err(); err != nil {
		return err
	}
	if open && !dead {
		s.endClause()
	}
	return nil
}

@ 줄의 첫 글자를 보고 갈래를 탄다. 경진대회 파일에는 탭이 흔하므로 여기서는 탭도
빈칸으로 친다.

@<DIMACS의 한 줄 |buf|를 처리한다@>=
j := 0
for j < len(buf) && (buf[j] == ' ' || buf[j] == '\t') {
	j++
}
switch {
case j == len(buf) || buf[j] == 'c':
	continue
case buf[j] == '%':
	break lines
case buf[j] == 'p':
	@<머리줄에서 변수의 수를 읽고 표 |dimacs|를 만든다@>
	continue
case dimacs == nil:
	return &ParseError{line, "p cnf 머리줄보다 절이 먼저 나왔다"}
}
for {
	for j < len(buf) && (buf[j] == ' ' || buf[j] == '\t') {
		j++
	}
	if j == len(buf) {
		break
	}
	@<|buf[j]|에서 정수 |x|와 부호 |neg|를 읽는다@>
	@<정수 |x|를 절에 보태거나 절을 마친다@>
}

@ @<머리줄에서 변수의 수를 읽고...@>=
if dimacs != nil {
	return &ParseError{line, "머리줄이 두 번 나왔다"}
}
var n, m int
_, err := fmt.Sscanf(string(buf[j:]), "p cnf %d %d", &n, &m)
if err != nil || n < 0 || n > maxVar || m < 0 {
	return &ParseError{line, "머리줄은 `p cnf 변수의수 절의수' 꼴이어야 한다"}
}
dimacs = make([]int, n+1)

@ 정수는 손수 읽는다. |strconv.Atoi|에 넘기려면 문자열을 새로 만들어야 하기
때문이다. 자릿수가 터무니없이 많아도 넘치지 않도록, 값이 |maxVar|를 넘으면 더
읽지 않는다. 그러면 남은 숫자가 ``정수 뒤에 빈칸이 아닌 글자''로 걸린다.

@<|buf[j]|에서 정수 |x|와 부호 |neg|를...@>=
neg := buf[j] == '-'
if neg {
	j++
}
i, x := j, 0
for j < len(buf) && '0' <= buf[j] && buf[j] <= '9' && x <= maxVar {
	x = x*10 + int(buf[j]-'0')
	j++
}
if i == j || (j < len(buf) && buf[j] != ' ' && buf[j] != '\t') {
	return &ParseError{line, "정수가 아닌 것이 있다"}
}
if x >= len(dimacs) {
	return &ParseError{line, fmt.Sprintf("변수 %d가 머리줄의 %d보다 크다", x, len(dimacs)-1)}
}

@ 0은 절을 마친다. 버려진 절이면 마칠 것도 없다. 버려진 절의 나머지 정수는 읽기만
하고 변수로 만들지 않는다. 원본이 줄의 나머지를 읽지 않는 것과 같은 결과다.

@<정수 |x|를 절에 보태거나...@>=
if !open {
	s.beginClause()
	open, dead = true, false
}
if x == 0 {
	if !dead {
		s.endClause()
	}
	open = false
	continue
}
if dead {
	continue
}
if dimacs[x] == 0 {
	dimacs[x] = s.Lookup(strconv.Itoa(x)).Var()
}
l := Pos(dimacs[x])
if neg {
	l = l.Not()
}
dead = !s.addLit(l)

@* 시험.
시험은 \.{io\_test.go}로 따로 짜낸다.

@(io_test.go@>=
package sat

import (
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"
)

@<시험들@>

@<시험에 쓰는 함수들@>

@ 첫째 시험은 Rivest의 여덟 절이다. 변수 번호가 이름이 처음 나온 차례로 매겨지는지
본다.

@<시험들@>=
func TestReadKnuthRivest(t *testing.T) {
	const rivest = "x2 x3 ~x4\nx1 x3 x4\n~x1 x2 x4\n~x1 ~x2 x3\n" +
		"~x2 ~x3 x4\n~x1 ~x3 ~x4\nx1 ~x2 ~x4\nx1 x2 ~x3\n"
	s := New()
	if err := s.ReadKnuth(strings.NewReader(rivest)); err != nil {
		t.Fatal(err)
	}
	if s.NumVars() != 4 || s.NumClauses() != 8 || s.NumLiterals() != 24 {
		t.Errorf("변수 %d, 절 %d, 리터럴 %d", s.NumVars(), s.NumClauses(), s.NumLiterals())
	}
	for v, want := range []string{"", "x2", "x3", "x4", "x1"} {
		if v > 0 && s.Name(v) != want {
			t.Errorf("변수 %d의 이름이 %s인데 %s여야 한다", v, s.Name(v), want)
		}
	}
}

@ 둘째 시험은 원본의 버릇들이다. 주석 줄은 사라지고, 늘 참인 절의 뒤쪽 이름은
변수가 되지 않으며, 빈 줄은 건너뛰고, 겹친 리터럴은 하나만 남는다. 주석에 한글이
섞여도 괜찮아야 한다. 원본도 주석의 나머지는 읽지 않는다.

@<시험들@>=
func TestReadKnuthQuirks(t *testing.T) {
	const input = "~ 주석 x9\nx1 ~x1 x5\nx2 ~ x6\n\nx3 x3 ~x2\n"
	s := New()
	if err := s.ReadKnuth(strings.NewReader(input)); err != nil {
		t.Fatal(err)
	}
	if s.NumVars() != 3 || s.Name(3) != "x3" {
		t.Errorf("변수가 %d개, 셋째 이름이 %s", s.NumVars(), s.Name(3))
	}
	got := slices.Collect(s.Clauses())
	if len(got) != 1 || !slices.Equal(got[0], []Lit{Pos(3), Neg(2)}) {
		t.Errorf("절이 %v로 나왔다", got)
	}
	for _, bad := range []string{"x1\tx2\n", "~~x\n"} {
		if err := New().ReadKnuth(strings.NewReader(bad)); err == nil {
			t.Errorf("%q를 잘못으로 보지 않았다", bad)
		}
	}
}

@ 셋째 시험은 DIMACS다. 절이 두 줄에 걸치고, 늘 참인 절 뒤의 변수 4는 만들어지지
않으며, 빈 절이 적히고, \.{\%} 뒤는 읽지 않는다.

@<시험들@>=
func TestReadDIMACS(t *testing.T) {
	const input = "c 주석\np cnf 5 4\n1 -2 0\n3 -3 4 0 2\n\t5 0\n0\n%\n0\n"
	s := New()
	if err := s.ReadDIMACS(strings.NewReader(input)); err != nil {
		t.Fatal(err)
	}
	want := [][]Lit{{Pos(1), Neg(2)}, {Pos(2), Pos(4)}}
	if got := slices.Collect(s.Clauses()); !slices.EqualFunc(got, want, slices.Equal[[]Lit]) {
		t.Errorf("절이 %v인데 %v여야 한다", got, want)
	}
	if s.NumVars() != 4 || s.Name(4) != "5" || !s.empty {
		t.Errorf("변수 %d개, 넷째 이름 %s, 빈 절 %v", s.NumVars(), s.Name(4), s.empty)
	}
	for _, bad := range []string{"1 2 0\n", "p cnf 3 1\n4 0\n", "p cnf 3 1\n1x 0\n"} {
		if err := New().ReadDIMACS(strings.NewReader(bad)); err == nil {
			t.Errorf("%q를 잘못으로 보지 않았다", bad)
		}
	}
}

@ 넷째 시험은 크누스의 벤치마크에서 고른 작은 문제 여섯이다. 수는 \CEE/로 짜낸
원본 \.{SAT13}이 찍은 ``(\dots\ successfully read)'' 줄에서 옮겨 적었다.

\.{testdata}에는 같은 문제가 두 형식으로 들어 있다. 크누스는 \.{.cnf} 파일을
\.{SAT-TO-DIMACS}로 만들었는데, 이 프로그램은 변수에 원본과 같은 차례로 번호를
매기지만 절은 임시 표를 되감으며 적는다. 그래서 \.{.cnf}에는 절이 거꾸로, 절 안의
리터럴도 거꾸로 적혀 있다. 두 파일을 읽어 이 관계가 리터럴 하나까지 맞는지 본다.
@^SAT-TO-DIMACS@>

@<시험들@>=
func TestBenchmarks(t *testing.T) {
	golden := map[string][3]int{
		"poset-nomax-b-12-minus-one": {144, 529, 1671},
		"queen-5x5-5":                {125, 825, 1725},
		"rand-3-1061-250-314159":     {250, 1061, 3183},
		"langfordprime-10":           {273, 1020, 2370},
		"mutex-fourbits-lemmas-1":    {129, 354, 926},
		"mutilated-10-10":            {176, 572, 1300},
	}
	for name, want := range golden {
		ks := readFile(t, filepath.Join("testdata", name+".sat"))
		ds := readFile(t, filepath.Join("testdata", name+".cnf"))
		for _, s := range []*Solver{ks, ds} {
			if got := [3]int{s.NumVars(), s.NumClauses(), s.NumLiterals()}; got != want {
				t.Errorf("%s: %v인데 %v여야 한다", name, got, want)
			}
		}
		samePair(t, name, ks, ds)
	}
}

@ 크누스의 벤치마크 전부(\.{SATexamples.tgz})를 풀어 둔 곳을 환경 변수
\.{SATEXAMPLES}에 적어 주면 백여 쌍 모두를 같은 방법으로 견준다. 150MB쯤 되므로
저장소에는 넣지 않았다.

@<시험들@>=
func TestSATexamples(t *testing.T) {
	dir := os.Getenv("SATEXAMPLES")
	if dir == "" {
		t.Skip("SATEXAMPLES가 비어 있다")
	}
	for _, kind := range []string{"SAT", "UNSAT"} {
		files, _ := filepath.Glob(filepath.Join(dir, "benchmarks-"+kind, "*.sat"))
		for _, f := range files {
			base := strings.TrimSuffix(filepath.Base(f), ".sat")
			cnf := filepath.Join(dir, "benchmarks-"+kind+"-cnf", base+".cnf")
			samePair(t, base, readFile(t, f), readFile(t, cnf))
		}
	}
}

@ 파일 이름의 확장자를 보고 알맞은 읽개로 읽는 문.

@<시험에 쓰는 함수들@>=
func readFile(t *testing.T, path string) *Solver {
	f, err := os.Open(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	s := New()
	if strings.HasSuffix(path, ".cnf") {
		err = s.ReadDIMACS(f)
	} else {
		err = s.ReadKnuth(f)
	}
	if err != nil {
		t.Fatalf("%s: %v", path, err)
	}
	return s
}

@ 크누스 형식으로 읽은 |ks|와 그 짝을 DIMACS로 읽은 |ds|를 견주는 문. |ks|의
$i$번째 절은 |ds|의 뒤에서 $i$번째 절을 뒤집은 것이어야 한다. 리터럴끼리는 부호가
같고, |ds| 쪽 변수의 이름이 |ks| 쪽 변수의 번호여야 한다.

@<시험에 쓰는 함수들@>=
func samePair(t *testing.T, name string, ks, ds *Solver) {
	kc := slices.Collect(ks.Clauses())
	dc := slices.Collect(ds.Clauses())
	if len(kc) != len(dc) {
		t.Errorf("%s: 절이 %d개와 %d개", name, len(kc), len(dc))
		return
	}
	for i, c := range kc {
		d := dc[len(dc)-1-i]
		@<절 |c|와 거꾸로 적힌 절 |d|가 같은지 본다@>
	}
}

@ @<절 |c|와 거꾸로 적힌 절 |d|가...@>=
if len(c) != len(d) {
	t.Errorf("%s: %d번째 절의 길이가 다르다", name, i)
	return
}
for k, l := range c {
	m := d[len(d)-1-k]
	if m.IsNeg() != l.IsNeg() || ds.Name(m.Var()) != strconv.Itoa(l.Var()) {
		t.Errorf("%s: %d번째 절의 %s와 %s가 다르다", name, i, ks.LitName(l), ds.LitName(m))
		return
	}
}

@* 색인.
