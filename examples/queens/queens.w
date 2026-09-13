\input kotexgweb

\def\title{N-퀸}

@s sat.Lit int
@s sat.Solver int

@* 들어가며.
서로 잡아먹지 못하게 퀸 $n$개를 $n\times n$ 판에 놓는 문제다. 1848년에 Max Bezzel이
여덟 개짜리를 내놓았고, 이태 뒤 Franz Nauck이 92가지 답을 찾아냈다.
@^Bezzel, Max@>
@^Nauck, Franz@>

옆집 BDD 꾸러미의 예제에도 같은 이름의 프로그램이 있다. 거기서는 조건을 모두 BDD로
엮은 다음 답을 하나도 늘어놓지 않고 개수를 센다. 대신 판이 조금만 커져도 BDD가
감당하지 못한다. SAT 풀이기는 정반대다. 답 하나를 찾는 일은 판이 수백 칸이어도
눈 깜짝할 새에 끝나지만, 답을 세려면 하나씩 찾을 수밖에 없다. 이 프로그램은 두
얼굴을 모두 보여 준다. 그냥 부르면 해 하나를 찾아 그리고, \.{-count}를 주면 해를
모두 센다.

@c
package main

import (
	"context"
	"flag"
	"fmt"
	"os"
	"strings"

	"github.com/sjnam/sat"
)

func main() {
	@<명령줄을 읽는다@>
	@<조건을 절로 적는다@>
	if *count {
		@<해를 모두 센다@>
	} else {
		@<해를 하나 찾아 그린다@>
	}
}

@<함수들@>

@ @<명령줄을 읽는다@>=
n := flag.Int("n", 8, "판의 크기")
count := flag.Bool("count", false, "해를 모두 센다")
flag.Parse()

@* 조건 적기.
칸 $(i,j)$마다 변수를 하나 둔다. 참이면 그 칸에 퀸이 있다. 조건은 BDD 판과 똑같이
둘이다. 행마다 퀸이 적어도 하나 있어야 하고, 서로 잡는 두 칸에 함께 놓일 수 없다.
앞의 것은 길이 $n$인 절 $n$개가 되고, 뒤의 것은 이진 절 $\bar a\lor\bar b$가 된다.
$n=100$이면 이진 절이 백만 개를 조금 넘는다. 풀이기는 이진 절을 따로 빠르게
다루므로 걱정할 것 없다. 행을 채우고 나면 열마다 하나씩이라는 것은 저절로 따라온다.

@<조건을 절로 적는다@>=
s := sat.New()
x := make([]sat.Lit, *n**n)
for i := range x {
	x[i] = s.NewVar()
}
for i := 0; i < *n; i++ {
	s.AddClause(x[i**n : (i+1)**n]...)
}
@<서로 잡는 두 칸은 함께 놓일 수 없다@>

@ 같은 짝을 두 번 적지 않도록 첨자가 작은 칸을 앞에 둔다.

@<서로 잡는 두 칸은...@>=
for p := range x {
	for q := p + 1; q < len(x); q++ {
		i, j, k, l := p / *n, p % *n, q / *n, q % *n
		if i == k || j == l || i-j == k-l || i+j == k+l {
			s.AddClause(x[p].Not(), x[q].Not())
		}
	}
}

@* 찾기와 세기.
해를 하나 찾으면 그림과 함께 풀이에 든 mem을 찍는다.

@<해를 하나 찾아 그린다@>=
st, err := s.Solve(context.Background())
check(err)
fmt.Printf("%d-퀸: %v, 절 %d개, %v\n", *n, st, s.NumClauses(), s.Stats())
if st == sat.Sat {
	fmt.Print(board(s, x, *n))
}

@ 해를 세는 방법은 곧다. 해를 하나 찾을 때마다 ``바로 이 해는 안 된다''는 절을 더하고
다시 푼다. 해마다 퀸이 정확히 $n$개이므로, 퀸이 놓인 칸들의 부정을 모은 절
하나면 그 해만 막힌다. 더는 풀리지 않으면 다 센 것이다.

이 길은 금방 비싸진다. 이 꾸러미의 |Solve|는 부를 때마다 절 전체로 자료 구조를
새로 짓고 배운 것을 모두 잊는다. 게다가 막는 절이 쌓일수록 남은 해를 찾기가
어려워진다. 내 컴퓨터에서 8-퀸의 92개는 0.1초에 세지만, 10-퀸의 724개는 mem
200억 개, 23초가 걸렸다. 한 번에 해 하나를 찾는 100-퀸이 0.2초인 것과 견주어 보라.
배운 절을 이어 쓰는 점진적 풀이는 꾸러미의 다음 단계에서 다룰 일이다.

@<해를 모두 센다@>=
var total uint64
solutions := 0
for {
	st, err := s.Solve(context.Background())
	check(err)
	total += s.Stats().IMems + s.Stats().Mems
	if st == sat.Unsat {
		break
	}
	if solutions++; solutions == 1 {
		fmt.Print(board(s, x, *n))
	}
	@<찾은 해를 막는 절을 더한다@>
}
fmt.Printf("%d-퀸의 해: %d개 (mem %d)\n", *n, solutions, total)

@ @<찾은 해를 막는 절을...@>=
var block []sat.Lit
for _, l := range x {
	if s.Value(l) {
		block = append(block, l.Not())
	}
}
s.AddClause(block...)

@ 판을 그리는 문. 두 곳에서 부른다.

@<함수들@>=
func board(s *sat.Solver, x []sat.Lit, n int) string {
	var b strings.Builder
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			if s.Value(x[i*n+j]) {
				b.WriteString(" Q")
			} else {
				b.WriteString(" .")
			}
		}
		b.WriteByte('\n')
	}
	return b.String()
}

@ 풀이기가 잘못을 돌려주면 알리고 끝낸다. 두 곳에서 부른다.

@<함수들@>=
func check(err error) {
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

@* 색인.
