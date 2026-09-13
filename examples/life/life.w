\input kotexgweb

\def\title{거꾸로 도는 생명 게임}

@s sat.Lit int

@* 들어가며.
John Conway의 생명 게임은 칸마다 살았거나 죽은 세포가 있는 무한한 판에서 벌어진다.
한 세대가 지나면 세포는 이웃 여덟 칸을 보고 다음 상태를 정한다. 산 이웃이 정확히
셋이면 태어나고, 산 세포는 산 이웃이 둘이나 셋이면 살아남으며, 나머지는 모두 죽는다.
1970년에 Martin Gardner가 {\sl Scientific American\/}에 소개한 뒤로 이 단순한
규칙에서 끝없이 이상한 것들이 쏟아져 나왔다.
@^Conway, John Horton@>
@^Gardner, Martin@>

앞으로 돌리기는 쉽다. 규칙대로 세면 된다. 거꾸로 돌리기, 곧 주어진 무늬가 {\it 어떤
판에서 나왔는지\/} 찾는 일은 전혀 다르다. 조상이 여럿일 수도 있고 하나도 없을 수도
있다. 조상이 없는 무늬를 ``에덴의 동산''이라 한다. 크누스는 {\sl TAOCP\/} 7.2.2.2절에서
이 거꾸로 돌리기를 SAT의 멋진 쓰임새로 든다. 이 프로그램은 무늬 하나를 받아 $k$세대
전의 조상을 찾는다. 기본 무늬는 \.{SAT}라는 글자다.
@^Knuth, Donald Ervin@>

@c
package main

import (
	"context"
	"flag"
	"fmt"
	"math/bits"
	"os"
	"strings"

	"github.com/sjnam/sat"
)

func main() {
	@<명령줄을 읽는다@>
	@<판과 변수를 마련한다@>
	@<세대마다 생명의 규칙을 절로 적는다@>
	@<풀어서 조상을 그린다@>
}

@ 무늬는 행을 \.{/}로 이어 붙인 글자열로 받는다. \.{\#}은 산 세포, 다른 글자는 죽은
세포다. 조상은 무늬를 둘러싼 폭 |m|의 여백까지 차지할 수 있고, 그 바깥은 영원히
죽어 있다고 친다. 여백이 좁으면 조상이 있어도 못 찾을 수 있다.

@<명령줄을 읽는다@>=
p := flag.String("p", ".###..##..###/#....#..#..#./.##..####..#./...#.#..#..#./###..#..#..#.",
	"무늬 (행을 /로 가른다, #이 산 세포)")
k := flag.Int("k", 1, "거슬러 올라갈 세대 수")
m := flag.Int("m", 1, "무늬 둘레의 여백")
flag.Parse()
rows := strings.Split(*p, "/")

@* 판과 변수.
판의 크기는 $H\times W$이고 무늬는 가운데 놓인다. 시각 $t$는 0부터 $k$까지이고,
시각 $k$가 주어진 무늬다. 시각 $t<k$의 판에서는 모든 칸이 변수다. 칸 하나의 상태를
묻는 문 |cellAt|은 변수이면 그 리터럴과 $-1$을, 정해져 있으면 0이나 1을 준다.

@<판과 변수를 마련한다@>=
h, w := len(rows), len(rows[0])
H, W := h+2**m, w+2**m
s := sat.New()
vars := make([]sat.Lit, *k*H*W)
for i := range vars {
	vars[i] = s.NewVar()
}
cellAt := func(t, i, j int) (sat.Lit, int) {
	if i < 0 || i >= H || j < 0 || j >= W {
		return 0, 0
	}
	if t < *k {
		return vars[(t*H+i)*W+j], -1
	}
	@<무늬에서 칸 $(i,j)$의 상태를 읽는다@>
}

@ @<무늬에서 칸...@>=
if r, c := i-*m, j-*m; r >= 0 && r < h && c >= 0 && c < len(rows[r]) && rows[r][c] == '#' {
	return 0, 1
}
return 0, 0

@* 규칙을 절로.
시각 $t$의 이웃 아홉 칸이 시각 $t+1$의 가운데 칸을 정한다. 가장 곧은 적기는 아홉 칸의
배정 $2^9=512$가지를 모두 늘어놓는 것이다. 배정마다 다음 상태가 정해지므로, ``이웃이
이 배정이면 다음 칸은 이 값이다''를 절 하나로 적는다. 곧 배정의 부정과 다음 칸의
리터럴을 모은 절이다. 다음 칸이 이미 정해져 있으면 규칙과 어긋나는 배정만 막는다.
크누스는 세포 수를 세는 회로로 절을 훨씬 적게 쓰지만, 여기서는 알아보기 쉬운 쪽을
택했다. 판 바깥 칸은 죽어 있으므로 배정에서 빠진다.

판 바로 바깥 한 줄도 살펴야 한다. 판 가장자리의 세포들이 그 바깥에 새 세포를 낳으면
안 되기 때문이다.

@<세대마다 생명의 규칙을...@>=
for t := 0; t < *k; t++ {
	for i := -1; i <= H; i++ {
		for j := -1; j <= W; j++ {
			@<칸 $(i,j)$의 다음 세대를 이웃 아홉 칸으로 묶는다@>
		}
	}
}

@ 이웃 가운데 변수인 것만 |nb|에 모은다. |center|는 그 가운데 칸의 자리다.

@<칸 $(i,j)$의 다음 세대를...@>=
var nb []sat.Lit
center := -1
for di := -1; di <= 1; di++ {
	for dj := -1; dj <= 1; dj++ {
		if l, st := cellAt(t, i+di, j+dj); st < 0 {
			if di == 0 && dj == 0 {
				center = len(nb)
			}
			nb = append(nb, l)
		}
	}
}
y, yst := cellAt(t+1, i, j)
for a := 0; a < 1<<len(nb); a++ {
	@<배정 |a|에서 다음 상태를 셈하고 절을 넣는다@>
}

@ 배정 |a|의 $b$번 비트가 |nb[b]|의 값이다.

@<배정 |a|에서...@>=
live := bits.OnesCount(uint(a))
alive := center >= 0 && a>>center&1 == 1
if alive {
	live--
}
next := live == 3 || alive && live == 2
if yst >= 0 && next == (yst == 1) {
	continue
}
c := make([]sat.Lit, 0, len(nb)+1)
for b, l := range nb {
	if a>>b&1 == 1 {
		l = l.Not()
	}
	c = append(c, l)
}
if yst < 0 {
	if !next {
		y = y.Not()
	}
	c = append(c, y)
	y, _ = cellAt(t+1, i, j)
}
s.AddClause(c...)

@* 풀기.
해가 나오면 세대마다 판을 그리고, 앞으로 한 세대씩 돌려서 정말로 다음 판이 나오는지
확인한다. 만족할 수 없으면 이 여백 안에서는 조상이 없다.

@<풀어서 조상을 그린다@>=
st, err := s.Solve(context.Background())
if err != nil {
	fmt.Fprintln(os.Stderr, err)
	os.Exit(1)
}
fmt.Printf("%v: 변수 %d개, 절 %d개, mem %d\n", st, s.NumVars(), s.NumClauses(),
	s.Stats().IMems+s.Stats().Mems)
if st != sat.Sat {
	fmt.Printf("여백 %d 안에는 %d세대 전의 조상이 없다\n", *m, *k)
	return
}
@<세대마다 판을 읽어 그린다@>
@<앞으로 돌려서 확인한다@>

@ 판 |board[t][i][j]|는 칸의 삶과 죽음이다.

@<세대마다 판을 읽어...@>=
board := make([][][]bool, *k+1)
for t := range board {
	board[t] = make([][]bool, H)
	fmt.Printf("\n세대 %d:\n", t)
	for i := range board[t] {
		board[t][i] = make([]bool, W)
		for j := range board[t][i] {
			l, st := cellAt(t, i, j)
			board[t][i][j] = st == 1 || st < 0 && s.Value(l)
			fmt.Print(map[bool]string{true: " #", false: " ."}[board[t][i][j]])
		}
		fmt.Println()
	}
}

@ 판 바깥 한 줄까지 규칙대로 셈해서 다음 판과 견준다.

@<앞으로 돌려서...@>=
alive := func(t, i, j int) bool { return i >= 0 && i < H && j >= 0 && j < W && board[t][i][j] }
for t := 0; t < *k; t++ {
	for i := -1; i <= H; i++ {
		for j := -1; j <= W; j++ {
			live := 0
			for di := -1; di <= 1; di++ {
				for dj := -1; dj <= 1; dj++ {
					if (di != 0 || dj != 0) && alive(t, i+di, j+dj) {
						live++
					}
				}
			}
			if (live == 3 || alive(t, i, j) && live == 2) != alive(t+1, i, j) {
				fmt.Printf("세대 %d의 칸 (%d,%d)이 틀렸다!\n", t+1, i, j)
				os.Exit(1)
			}
		}
	}
}
fmt.Println("\n앞으로 돌려 확인했다.")

@* 색인.
