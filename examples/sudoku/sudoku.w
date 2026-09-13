\input kotexgweb

\def\title{스도쿠}

@s sat.Lit int
@s sat.Solver int

@* 들어가며.
$9\times9$ 판에 1부터 9까지를 채우되, 행마다, 열마다, $3\times3$ 상자마다 같은 숫자가
두 번 나오지 않게 하는 퍼즐이다. 1979년에 미국의 Howard Garns가 ``Number Place''라는
이름으로 퍼즐 잡지에 냈고, 일본의 니코리 사가 1984년에 ``스도쿠''라는 이름을 붙여
널리 퍼뜨렸다. 2012년에는 핀란드의 수학자 Arto Inkala가 ``세상에서 가장 어려운
스도쿠''를 내놓아 신문에 실렸다. 이 프로그램이 기본으로 푸는 것이 그 퍼즐이다.
@^Garns, Howard@>
@^Inkala, Arto@>

사람에게 어려운 퍼즐이 SAT 풀이기에게는 어떨까? 변수 729개, 절 만 개 남짓이면
규칙이 모두 적히고, 풀이기는 몇 밀리초 만에 답을 낸다. 더 흥미로운 것은 답이
{\it 하나뿐\/}임을 보이는 일이다. 찾은 해를 막는 절을 더하고 다시 풀어서 만족할 수
없다고 나오면, 다른 해가 없다는 증명이 끝난다. 좋은 퍼즐이라면 반드시 그래야 한다.

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
	@<명령줄에서 퍼즐을 읽는다@>
	@<변수를 만든다@>
	@<규칙을 절로 적는다@>
	@<주어진 숫자를 단위 절로 적는다@>
	@<풀어서 그린다@>
	@<해가 하나뿐인지 본다@>
}

@<함수들@>

@ 퍼즐은 칸 81개를 행 우선으로 늘어놓은 글자열로 받는다. 1부터 9까지는 주어진 숫자이고,
\.{.}이나 \.0은 빈칸이다. 빈칸 글자와 줄바꿈은 무시하므로 판 모양으로 적어도 된다.

@<명령줄에서 퍼즐을 읽는다@>=
p := flag.String("p", "8..........36......7..9.2...5...7.......457.....1...3...1....68..85...1..9....4..",
	"퍼즐 (칸 81개, 빈칸은 . 또는 0)")
flag.Parse()
var grid []int
for _, ch := range *p {
	switch {
	case ch >= '1' && ch <= '9':
		grid = append(grid, int(ch-'0'))
	case ch == '.' || ch == '0':
		grid = append(grid, 0)
	}
}
if len(grid) != 81 {
	fmt.Fprintf(os.Stderr, "칸이 %d개다. 81개여야 한다.\n", len(grid))
	os.Exit(1)
}

@* 규칙.
행 $r$, 열 $c$의 칸에 숫자 $d+1$이 들어간다는 뜻의 변수 $x_{rcd}$를 둔다. 첨자는 모두
0부터 8까지다.

@<변수를 만든다@>=
s := sat.New()
x := make([]sat.Lit, 729)
for i := range x {
	x[i] = s.NewVar()
}
v := func(r, c, d int) sat.Lit { return x[(r*9+c)*9+d] }

@ 규칙은 네 가지인데 모양이 모두 같다. ``이 아홉 변수 가운데 정확히 하나가 참이다.''
칸마다 숫자가 하나이고, 행마다 숫자 $d$가 한 번, 열마다 한 번, 상자마다 한 번이다.
네 무리가 81개씩이니 ``정확히 하나''가 324번 나온다.

@<규칙을 절로 적는다@>=
for a := 0; a < 9; a++ {
	for b := 0; b < 9; b++ {
		var cell, row, col, box [9]sat.Lit
		for t := 0; t < 9; t++ {
			cell[t] = v(a, b, t)
			row[t] = v(a, t, b)
			col[t] = v(t, a, b)
			box[t] = v(a/3*3+t/3, a%3*3+t%3, b)
		}
		exactlyOne(s, cell[:])
		exactlyOne(s, row[:])
		exactlyOne(s, col[:])
		exactlyOne(s, box[:])
	}
}

@ 상자의 첨자를 풀어 보자. |a|가 0부터 8까지 돌면 행 $\lfloor a/3\rfloor\cdot3$부터
세 행, 열 $(a\bmod3)\cdot3$부터 세 열이 상자 |a|가 된다. |t|가 상자 안에서 행 우선으로
돈다.

``정확히 하나''는 ``적어도 하나''인 긴 절 하나와 ``둘이 함께는 안 된다''인 이진 절
36개로 적는다. 네 곳에서 부른다.

@<함수들@>=
func exactlyOne(s *sat.Solver, lits []sat.Lit) {
	s.AddClause(lits...)
	for i := range lits {
		for j := i + 1; j < len(lits); j++ {
			s.AddClause(lits[i].Not(), lits[j].Not())
		}
	}
}

@ 주어진 숫자는 단위 절이다. 풀이기는 이것들을 수준 0의 트레일에 곧바로 올린다.

@<주어진 숫자를 단위 절로...@>=
for i, d := range grid {
	if d != 0 {
		s.AddClause(v(i/9, i%9, d-1))
	}
}

@* 풀기.
@<풀어서 그린다@>=
st, err := s.Solve(context.Background())
if err != nil {
	fmt.Fprintln(os.Stderr, err)
	os.Exit(1)
}
fmt.Printf("%v: 변수 %d개, 절 %d개, mem %d\n", st, s.NumVars(), s.NumClauses(),
	s.Stats().IMems+s.Stats().Mems)
if st != sat.Sat {
	return
}
fmt.Print(picture(s, v))

@ 찾은 해에서 참인 변수 81개의 부정을 모아 절 하나로 더하고 다시 푼다. 풀리지 않으면
해는 하나뿐이다. 풀리면 두 번째 해를 보여 준다. 그런 퍼즐은 퍼즐 잡지에 실릴 수 없다.

@<해가 하나뿐인지 본다@>=
var block []sat.Lit
for _, l := range x {
	if s.Value(l) {
		block = append(block, l.Not())
	}
}
s.AddClause(block...)
st, err = s.Solve(context.Background())
switch {
case err != nil:
	fmt.Fprintln(os.Stderr, err)
case st == sat.Unsat:
	fmt.Printf("해는 하나뿐이다 (증명에 mem %d)\n", s.Stats().IMems+s.Stats().Mems)
default:
	fmt.Println("해가 또 있다:")
	fmt.Print(picture(s, v))
}

@ 판을 그리는 문. 상자 경계에 줄을 긋는다. 두 곳에서 부른다.

@<함수들@>=
func picture(s *sat.Solver, v func(r, c, d int) sat.Lit) string {
	var b strings.Builder
	for r := 0; r < 9; r++ {
		if r%3 == 0 {
			b.WriteString("+-------+-------+-------+\n")
		}
		for c := 0; c < 9; c++ {
			if c%3 == 0 {
				b.WriteString("| ")
			}
			for d := 0; d < 9; d++ {
				if s.Value(v(r, c, d)) {
					fmt.Fprintf(&b, "%d ", d+1)
				}
			}
		}
		b.WriteString("|\n")
	}
	b.WriteString("+-------+-------+-------+\n")
	return b.String()
}

@* 색인.
