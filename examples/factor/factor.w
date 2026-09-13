\input kotexgweb

\def\title{곱셈기를 거꾸로}

@s sat.Lit int
@s sat.Solver int

@* 들어가며.
1640년에 페르마는 $F_n=2^{2^n}+1$ 꼴의 수가 모두 소수라고 믿었다. $F_0$부터 $F_4$까지,
곧 3, 5, 17, 257, 65537은 정말 소수다. 1732년에 오일러가 그 믿음을 깼다.
$F_5=4294967297=641\times6700417$이다. 오일러는 $F_5$의 약수가 $64k+1$ 꼴이어야
한다는 것을 먼저 보이고 후보를 차례로 나눠 보았다.
@^Fermat, Pierre de@>
@^Euler, Leonhard@>

이 프로그램은 약수에 대해 아무것도 모르는 채로 같은 일을 한다. 곱셈기 회로를 절로
적고, 출력 비트를 $N$으로 못 박은 다음, 입력 비트를 찾으라고 풀이기에게 맡긴다.
회로를 앞으로 돌리면 곱셈이지만 거꾸로 돌리면 인수분해가 된다. 만족할 수 없다고
나오면 $N$이 소수라는 증명이다.

이렇게 풀면 빠르냐고? 전혀 그렇지 않다. 인수분해에는 수체 체(number field sieve)
같은 훨씬 좋은 방법이 있고, SAT로는 수십 비트만 넘어도 금방 힘들어진다. 크누스는
{\sl TAOCP\/} 7.2.2.2절에서 곱셈기 회로로 만든 절들을 어려운 벤치마크로 쓴다. 우리
\.{testdata}의 \.{dadda}로 시작하는 문제들이 그것이다. 이 프로그램의 재미는 빠르기가
아니라, 회로 하나를 앞뒤 어느 쪽으로든 돌릴 수 있다는 데 있다.
@^Knuth, Donald Ervin@>

@c
package main

import (
	"context"
	"flag"
	"fmt"
	"math/bits"
	"os"

	"github.com/sjnam/sat"
)

func main() {
	@<명령줄을 읽는다@>
	@<두 인수의 비트를 변수로 만든다@>
	@<곱셈기 회로를 절로 적는다@>
	@<곱을 $N$으로 못 박는다@>
	@<풀어서 알린다@>
}

@<함수들@>

@ @<명령줄을 읽는다@>=
n := flag.Uint64("n", 4294967297, "인수분해할 수")
flag.Parse()
if *n < 4 {
	fmt.Fprintln(os.Stderr, "4 이상의 수를 주어야 한다")
	os.Exit(1)
}
L := bits.Len64(*n)

@* 회로.
$N$이 $L$비트이고 $N=xy$이며 $2\le x\le y$라면, $x\le\sqrt N<2^{\lceil L/2\rceil}$이고
$y\le N/2<2^{L-1}$이다. 그러니 $x$에는 $\lceil L/2\rceil$비트, $y$에는 $L-1$비트면
넉넉하다. 둘 다 1이 아니어야 하므로 맨 아래 비트를 뺀 나머지 비트 가운데 하나는
참이어야 한다. $x\le y$는 굳이 적지 않는다. 뒤바뀐 답도 답이다.

@<두 인수의 비트를...@>=
s := sat.New()
x, y := newBits(s, (L+1)/2), newBits(s, L-1)
s.AddClause(x[1:]...)
s.AddClause(y[1:]...)

@ 비트 |k|개를 새 변수로 만드는 문. 맨 아래 비트가 첨자 0이다. 두 곳에서 부른다.

@<함수들@>=
func newBits(s *sat.Solver, k int) []sat.Lit {
	b := make([]sat.Lit, k)
	for i := range b {
		b[i] = s.NewVar()
	}
	return b
}

@ 곱셈기는 초등학교에서 배운 그대로다. 부분곱 $x_iy_j$를 모두 만들고, $x$의 비트마다
한 줄씩 자리를 옮겨 차례로 더한다. 덧셈은 전가산기를 늘어놓은 물결 자리올림
가산기다. 크누스가 쓰는 Dadda 곱셈기는 부분곱을 더 영리하게 모아 깊이를 줄이지만,
절의 개수는 크게 다르지 않다.

회로의 선마다 변수를 하나씩 두고 게이트마다 그 입출력 관계를 절로 적는다. 이것을
Tseitin 변환이라 한다. 식을 곧이곧대로 곱의 합으로 펼치면 절이 지수적으로 불어나지만,
선마다 이름을 붙이면 게이트 수에 정비례한다.
@^Tseitin, Grigori Samuilovich@>

@<곱셈기 회로를 절로...@>=
zero := s.NewVar()
s.AddClause(zero.Not())
acc := make([]sat.Lit, len(y))
for j := range y {
	acc[j] = and(s, x[0], y[j])
}
for i := 1; i < len(x); i++ {
	row := make([]sat.Lit, len(y))
	for j := range y {
		row[j] = and(s, x[i], y[j])
	}
	acc = append(acc[:i:i], add(s, zero, acc[i:], row)...)
}

@ 여기서 |acc|는 지금까지 더한 값이다. 줄 |i|를 더할 때 아래 |i|비트는 더는 바뀌지
않으므로 그대로 두고, 나머지만 새 줄과 더한다. |acc[:i:i]|로 용량을 잘라 두어야
|append|가 뒤쪽의 옛 비트를 덮어쓰지 않는다.

$c=a\land b$의 절은 셋이다. $(\bar c\lor a)$, $(\bar c\lor b)$, $(c\lor\bar a\lor\bar b)$.

@<함수들@>=
func and(s *sat.Solver, a, b sat.Lit) sat.Lit {
	c := s.NewVar()
	s.AddClause(c.Not(), a)
	s.AddClause(c.Not(), b)
	s.AddClause(c, a.Not(), b.Not())
	return c
}

@ 같은 길이가 아닐 수도 있는 두 비트열 |u|, |v|를 더해 한 비트 긴 합을 주는 문.
모자란 자리는 늘 거짓인 |zero|로 채운다. 맨 아래 자리올림도 |zero|다.

@<함수들@>=
func add(s *sat.Solver, zero sat.Lit, u, v []sat.Lit) []sat.Lit {
	k := max(len(u), len(v))
	sum := make([]sat.Lit, k+1)
	carry := zero
	for i := 0; i < k; i++ {
		a, b := zero, zero
		if i < len(u) {
			a = u[i]
		}
		if i < len(v) {
			b = v[i]
		}
		sum[i], carry = fullAdder(s, a, b, carry)
	}
	sum[k] = carry
	return sum
}

@ 전가산기. 합 $a\oplus b\oplus c$는 입력 여덟 배정마다 절이 하나씩이다. 자리올림
$\langle abc\rangle$는 ``둘이 참이면 참''과 ``둘이 거짓이면 거짓''으로 절 여섯이다.

@<함수들@>=
func fullAdder(s *sat.Solver, a, b, c sat.Lit) (sum, carry sat.Lit) {
	sum, carry = s.NewVar(), s.NewVar()
	in := [3]sat.Lit{a, b, c}
	for m := 0; m < 8; m++ {
		cl := make([]sat.Lit, 0, 4)
		for t, l := range in {
			if m>>t&1 == 1 {
				l = l.Not()
			}
			cl = append(cl, l)
		}
		if bits.OnesCount(uint(m))%2 == 1 {
			s.AddClause(append(cl, sum)...)
		} else {
			s.AddClause(append(cl, sum.Not())...)
		}
	}
	@<자리올림의 절 여섯을 넣는다@>
	return
}

@ 앞의 합 절들에서는 배정 |m|의 비트 |t|가 1이면 |in[t]|가 참인 배정이고, 그 배정을
막는 부분에는 |in[t]|의 부정이 들어갔다. 참인 입력이 홀수 개인 배정이면 |sum|이
참이어야 한다. 자리올림은 세 입력의 짝 $(p,q)$마다 ``둘 다 참이면 참''과 ``둘 다
거짓이면 거짓''을 적으면 된다.

@<자리올림의 절 여섯...@>=
for t := 0; t < 3; t++ {
	p, q := in[(t+1)%3], in[(t+2)%3]
	s.AddClause(p.Not(), q.Not(), carry)
	s.AddClause(p, q, carry.Not())
}

@* 곱을 못 박고 풀기.
곱의 비트 가운데 $N$의 비트는 단위 절로, 그보다 높은 비트는 0으로 못 박는다.

@<곱을 $N$으로...@>=
for t, l := range acc {
	if *n>>t&1 == 1 && t < 64 {
		s.AddClause(l)
	} else {
		s.AddClause(l.Not())
	}
}

@ 풀리면 두 인수를 비트에서 읽어 정말 곱이 $N$인지 확인한다.

@<풀어서 알린다@>=
st, err := s.Solve(context.Background())
if err != nil {
	fmt.Fprintln(os.Stderr, err)
	os.Exit(1)
}
fmt.Printf("%v: 변수 %d개, 절 %d개, %v\n", st, s.NumVars(), s.NumClauses(), s.Stats())
switch st {
case sat.Unsat:
	fmt.Printf("%d은 소수다\n", *n)
case sat.Sat:
	a, b := value(s, x), value(s, y)
	hi, lo := bits.Mul64(a, b)
	fmt.Printf("%d = %d × %d (확인: %v)\n", *n, a, b, hi == 0 && lo == *n)
}

@ 비트열의 값을 읽는 문. 두 곳에서 부른다.

@<함수들@>=
func value(s *sat.Solver, b []sat.Lit) uint64 {
	var v uint64
	for i, l := range b {
		if s.Value(l) {
			v |= 1 << i
		}
	}
	return v
}

@* 색인.
