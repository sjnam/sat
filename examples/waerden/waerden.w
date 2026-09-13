\input kotexgweb

\def\title{반 데르 바르덴 수}

@s sat.Lit int
@s iter.Seq int

@* 들어가며.
1부터 $n$까지의 정수를 0과 1 두 빛깔로 칠한다. 0으로 칠한 수들 가운데 길이 $j$인
등차수열이 없고, 1로 칠한 수들 가운데 길이 $k$인 등차수열이 없게 할 수 있을까?
1927년에 반 데르 바르덴은 $n$이 충분히 크면 결코 그럴 수 없다는 것을 증명했다.
그렇게 칠할 수 없게 되는 가장 작은 $n$을 반 데르 바르덴 수 $W(j,k)$라 한다.
@^van der Waerden, Bartel Leendert@>

크누스는 {\sl TAOCP\/} 7.2.2.2절을 바로 이 문제로 연다. $j=k=3$이면 절은 이렇다.
$$(x_i\lor x_{i+d}\lor x_{i+2d})\quad\hbox{그리고}\quad
(\bar x_i\lor\bar x_{i+d}\lor\bar x_{i+2d}),\qquad 1\le i,\ i+2d\le n.$$
앞의 절은 세 수가 모두 0이 되는 것을, 뒤의 절은 모두 1이 되는 것을 막는다. 그는
이 절들을 $\hbox{waerden}(3,3;n)$이라 부르고, $n=8$에서는 $x_1\ldots x_8=01100110$
같은 해가 있지만 $n=9$에서는 없다는 데서 이야기를 시작한다. 곧 $W(3,3)=9$다.
@^Knuth, Donald Ervin@>

이 프로그램은 $n$을 1부터 하나씩 늘리며 절을 풀어, 처음으로 만족할 수 없게 되는
곳을 찾는다. SAT 풀이기로 수학의 상수 하나를 재는 셈이다. 해가 있다는 것은 해를
보여 주면 끝나지만, 해가 {\it 없다\/}는 것은 풀이기가 모든 가능성을 지워 없애야
알 수 있다. 크누스의 표에 따르면 $W(3,4)=18$, $W(3,5)=22$, $W(3,6)=32$,
$W(4,4)=35$이다. 이 프로그램으로 모두 금방 확인할 수 있다.

@c
package main

import (
	"context"
	"flag"
	"fmt"
	"iter"
	"os"
	"strings"

	"github.com/sjnam/sat"
)

func main() {
	@<명령줄을 읽는다@>
	@<|n|을 하나씩 늘리며 풀어 본다@>
}

@<함수들@>

@ 두 수열의 길이를 받는다.

@<명령줄을 읽는다@>=
j := flag.Int("j", 3, "0으로 칠한 수들에서 피할 등차수열의 길이")
k := flag.Int("k", 3, "1로 칠한 수들에서 피할 등차수열의 길이")
flag.Parse()

@ $n$마다 풀이기를 새로 만든다. 만족할 수 있으면 칠한 것을 적어 두고 $n$을 늘리고,
만족할 수 없으면 바로 앞의 칠하기를 보여 주고 끝낸다. 수마다 준비와 풀이에 든 mem을
함께 찍으면 $W$ 가까이에서 문제가 갑자기 어려워지는 것이 보인다.

@<|n|을 하나씩 늘리며...@>=
last := ""
for n := 1; ; n++ {
	s := sat.New()
	x := make([]sat.Lit, n+1)
	for i := 1; i <= n; i++ {
		x[i] = s.NewVar()
	}
	@<등차수열을 막는 절들을 넣는다@>
	st, err := s.Solve(context.Background())
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	stats := s.Stats()
	fmt.Printf("waerden(%d,%d;%d): %-5v 절 %4d개, %9d mems\n",
		*j, *k, n, st, s.NumClauses(), stats.IMems+stats.Mems)
	if st == sat.Unsat {
		@<답을 알린다@>
		return
	}
	@<칠한 것을 적어 둔다@>
}

@ 0으로 칠한 수열을 막는 절에는 양의 리터럴을, 1로 칠한 수열을 막는 절에는 음의
리터럴을 쓴다.

@<등차수열을 막는 절들을...@>=
for ap := range progressions(n, *j) {
	c := make([]sat.Lit, len(ap))
	for t, i := range ap {
		c[t] = x[i]
	}
	s.AddClause(c...)
}
for ap := range progressions(n, *k) {
	c := make([]sat.Lit, len(ap))
	for t, i := range ap {
		c[t] = x[i].Not()
	}
	s.AddClause(c...)
}

@ 1부터 $n$ 사이에서 길이 |length|인 등차수열을 모두 내놓는 문. 공차 $d$는 1 이상이다.
앞의 두 곳에서 부른다.

@<함수들@>=
func progressions(n, length int) iter.Seq[[]int] {
	return func(yield func([]int) bool) {
		for d := 1; 1+(length-1)*d <= n; d++ {
			for a := 1; a+(length-1)*d <= n; a++ {
				ap := make([]int, length)
				for t := range ap {
					ap[t] = a + t*d
				}
				if !yield(ap) {
					return
				}
			}
		}
	}
}

@ 참인 변수를 1로 적는다.

@<칠한 것을 적어 둔다@>=
var b strings.Builder
for i := 1; i <= n; i++ {
	if s.Value(x[i]) {
		b.WriteByte('1')
	} else {
		b.WriteByte('0')
	}
}
last = b.String()

@ @<답을 알린다@>=
fmt.Printf("\nW(%d,%d) = %d\n", *j, *k, n)
if n > 1 {
	fmt.Printf("n = %d에서 찾은 칠하기: %s\n", n-1, last)
}

@* 색인.
