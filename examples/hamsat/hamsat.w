\input kotexgweb

\def\title{HAMSAT}

@s sat.Lit int
@s sat.Solver int
@s gbgraph.Graph int

@* 들어가며.
그래프 $G$의 꼭짓점을 모두 한 번씩 지나 제자리로 돌아오는 순환을 해밀턴 순환이라
한다. 그런 순환이 있는지 묻는 문제는 NP-완전이다. 크누스는 2026년 4월에 이 물음을
SAT로 푸는 \.{HAMSAT}을 썼다. {\sl TAOCP\/} 7.2.2.4절의 알고리즘~C가 될 프로그램으로,
\.{SAT13}을 거의 그대로 품고 앞과 뒤만 바꾸었다.
@^Knuth, Donald Ervin@>

착상은 이렇다. 해밀턴 순환의 조건 가운데 일부만 절로 적는다. 꼭짓점마다 나가는 호와
들어오는 호가 정확히 하나씩이라는 조건이다. 이 절들을 만족하는 해는 {\it 순환 덮개},
곧 꼭짓점을 겹치지 않게 모두 덮는 순환 여럿이다. 순환이 하나뿐이면 끝이다. 여럿이면
``이 꼭짓점들끼리만 도는 순환은 안 된다''는 절을 보태고 다시 푼다. 만족할 수 없게 되면
해밀턴 순환이 없다. 이런 방법을 CEGAR(counterexample-guided abstraction refinement),
또는 게으른 절 생성이라 부른다. 보태는 절은 컷셋에서 나오는데, 크누스는 이것을
SAT~2025에 실린 Ohashi, Soh, Le~Berre, Nabeshima, Banbara, Inoue, Tamura의 논문에서
가져왔다.
@^Ohashi, Ryoga@>

크누스는 \.{SAT13}의 |mem| 위쪽에 새 절을 쌓고 수준 0으로 돌아가 풀이를 이어 간다.
우리 꾸러미에서는 그 일이 |AddClause|와 |Solve|면 된다. 옆집 \.{cdcl.w}의 점진적 풀이가
배운 절과 활동도를 간직한 채 이어 풀기 때문이다. 그러니 이 글은 \.{HAMSAT}의 앞과
뒤, 곧 절을 적는 부분과 순환을 분석하는 부분만 옮긴다. 풀이기의 속이 조금 다르므로
mem 수는 원본과 같지 않지만, 해밀턴 그래프인지 아닌지의 답은 같아야 한다.

@c
package main

import (
	"context"
	"flag"
	"fmt"
	"os"
	"strings"

	"github.com/sjnam/go-sgb/gbbasic"
	"github.com/sjnam/go-sgb/gbgraph"
	"github.com/sjnam/go-sgb/gbsave"
	"github.com/sjnam/sat"
)

@<함수들@>

func main() {
	@<명령줄을 읽고 그래프 |g|를 마련한다@>
	@<그래프를 확인하고 호마다 변수를 둔다@>
	@<순환 덮개의 절을 적는다@>
	@<풀고, 순환이 여럿이면 컷셋 절을 보태며 되풀이한다@>
}

@ 그래프는 셋 가운데 하나로 준다. 선택 \.{-gb}에 Stanford GraphBase 형식의 파일을
주면 그것을 읽는다. 크누스의 원본이 받는 것과 같은 파일이다. 선택 \.{-petersen}을
주면 Petersen 그래프를 쓴다. 아무것도 주지 않으면 $m\times n$ 판의 나이트 그래프를
쓰는데, 그 해밀턴 순환이 곧 닫힌 나이트 여행이다. 선택 \.{-opts}에는 크누스식 풀이기
선택을 준다.

@<명령줄을 읽고...@>=
gb := flag.String("gb", "", "Stanford GraphBase 형식의 그래프 파일")
petersen := flag.Bool("petersen", false, "Petersen 그래프를 쓴다")
rows := flag.Int64("m", 8, "나이트 판의 행 수")
cols := flag.Int64("n", 8, "나이트 판의 열 수")
opts := flag.String("opts", "", "풀이기 선택들")
flag.Parse()
var g *gbgraph.Graph
var err error
switch {
case *gb != "":
	g, err = gbsave.RestoreGraph(*gb)
case *petersen:
	g, err = gbbasic.Petersen()
default:
	g, err = gbbasic.Board(*rows, *cols, 0, 0, 5, 0, false)
}
check(err)
knight := *gb == "" && !*petersen

@ 오류가 나면 알리고 끝내는 문. 여러 곳에서 부른다.

@<함수들@>=
func check(err error) {
	if err != nil {
		fail("%v", err)
	}
}

func fail(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "hamsat: "+format+"\n", args...)
	os.Exit(1)
}

@* 호마다 변수 하나.
원본처럼 $G$는 고리가 없는 무향 그래프여야 한다. Stanford GraphBase에서 무향 그래프의
간선은 서로 반대 방향인 호 둘로 적힌다. 호 $v\to u$마다 불 변수를 하나 두고, 참이면
순환이 $v$에서 $u$로 간다고 읽는다. 인접 행렬 |adj[v][u]|에 그 변수의 양의 리터럴을
두고, 호가 없으면 0을 둔다. 크누스는 호 $v\to u$의 변수가 $x$이면 $u\to v$의 변수가
$x\oplus1$이 되게 번호를 매긴다. 우리에게는 그럴 필요가 없다. 반대 방향 호는
|adj[u][v]|로 찾으면 된다.

꼭짓점의 차수가 2보다 작으면 해밀턴 순환이 있을 수 없으니 풀지 않고 답한다.

@<그래프를 확인하고...@>=
n := int(g.N)
adj := make([][]sat.Lit, n)
for v := range adj {
	adj[v] = make([]sat.Lit, n)
}
s := sat.New()
for _, o := range strings.Fields(*opts) {
	check(s.Params.Set(o))
}
for v := 0; v < n; v++ {
	d := 0
	for a := g.Vertices[v].Arcs; a != nil; a, d = a.Next, d+1 {
		u := int(g.Index(a.Tip))
		@<호 $v\to u$가 올바른지 보고, 처음 보는 간선이면 변수 둘을 만든다@>
	}
	if d < 2 {
		fmt.Printf("해밀턴 순환이 없다 (꼭짓점 %s의 차수가 %d)\n", g.Vertices[v].Name, d)
		return
	}
}
@<호가 모두 짝을 이루는지 본다@>

@ 꼭짓점을 차례로 보므로, $u<v$인 호 $v\to u$를 만났다면 간선 $\{u,v\}$의 변수들은
$u$를 볼 때 이미 만들어졌어야 한다.

@<호 $v\to u$가 올바른지...@>=
switch {
case u == v:
	fail("고리 %s->%s가 있다", g.Vertices[v].Name, g.Vertices[v].Name)
case u < v:
	if adj[v][u] == 0 {
		fail("무향 그래프가 아니다: %s->%s는 있는데 %s->%s가 없다",
			g.Vertices[v].Name, g.Vertices[u].Name, g.Vertices[u].Name, g.Vertices[v].Name)
	}
case adj[v][u] != 0:
	fail("겹친 호 %s->%s가 있다", g.Vertices[v].Name, g.Vertices[u].Name)
default:
	adj[v][u], adj[u][v] = s.NewVar(), s.NewVar()
}

@ 앞의 검사로는 $v<u$ 쪽의 호가 빠진 경우와 $u<v$ 쪽에서 호가 겹친 경우를 놓친다.
그러면 호의 수가 만든 변수의 수와 어긋나므로 원본처럼 그것으로 잡는다.

@<호가 모두 짝을...@>=
if g.M != int64(s.NumVars()) {
	fail("무향 그래프가 아니다: 호 %d개 가운데 짝을 이룬 것은 %d개다", g.M, s.NumVars())
}

@* 순환 덮개.
처음 절들은 원본의 두 규칙이다. (0)~서로 반대인 호 $v\to u$와 $u\to v$는 함께 참일
수 없다. 둘 다 참이면 길이 2인 순환이 되기 때문이다. (1)~꼭짓점마다 나가는 호가
정확히 하나, 들어오는 호가 정확히 하나 참이다.

@<순환 덮개의 절을 적는다@>=
for v := 0; v < n; v++ {
	for a := g.Vertices[v].Arcs; a != nil; a = a.Next {
		if u := int(g.Index(a.Tip)); v < u {
			s.AddClause(adj[v][u].Not(), adj[u][v].Not())
		}
	}
}
for v := 0; v < n; v++ {
	var out, in []sat.Lit
	for a := g.Vertices[v].Arcs; a != nil; a = a.Next {
		u := int(g.Index(a.Tip))
		out, in = append(out, adj[v][u]), append(in, adj[u][v])
	}
	exactlyOne(s, out)
	exactlyOne(s, in)
}

@ ``정확히 하나''는 ``적어도 하나''인 절 하나와 ``많아야 하나''인 이진 절
$d\choose2$개로 적는다. 보조 변수를 두어 이진 절의 수를 $d$에 선형으로 줄이는 방법이
여럿 알려져 있는데도 크누스가 이렇게 한 까닭은 셋이다. 관심 있는 그래프에서는 $d$가
대개 작고, 랭퍼드 쌍으로 실험해 보니 \.{SAT13}은 보조 변수가 없을 때 더 빨랐고,
프로그램을 간단히 두고 싶었다고 한다.

@<함수들@>=
func exactlyOne(s *sat.Solver, lits []sat.Lit) {
	s.AddClause(lits...)
	for i := range lits {
		for j := i + 1; j < len(lits); j++ {
			s.AddClause(lits[i].Not(), lits[j].Not())
		}
	}
}

@ 두 규칙을 만족하는 해에서 참인 호들을 따라가 보자. 나가는 호가 하나뿐이니 다음
꼭짓점이 하나로 정해지고, 들어오는 호가 하나뿐이니 두 꼭짓점에서 한 꼭짓점으로
모이는 일도 없다. 그러니 참인 호들은 모든 꼭짓점을 한 번씩 덮는 순환들을 이루고,
규칙 (0) 덕에 순환의 길이는 모두 3 이상이다.

@* 풀고 되풀이하기.
이제 되풀이한다. 풀어서 만족할 수 없으면 해밀턴 순환이 없다. 만족하면 해에서
순환들을 찾고, 할 수 있는 만큼 합친다. 하나로 합쳐지면 해밀턴 순환을 찾은 것이다.
아니면 남은 순환마다 컷셋 절을 보태고 다시 푼다. 한 번 푸는 것을 한 라운드라 하자.
mem은 라운드마다 준비와 풀이에 든 것을 더해 간다.

@<풀고, 순환이...@>=
sol, rsol, cid := make([]int, n), make([]int, n), make([]int, n)
leader, cycs, cloc := make([]int, n/3+2), make([]int, n/3+2), make([]int, n/3+2)
var cycptr, cyctested, c int
var mems uint64
rounds, cutclauses := 0, 0
for {
	rounds++
	st, err := s.Solve(context.Background())
	check(err)
	mems += s.Stats().IMems + s.Stats().Mems
	if st == sat.Unsat {
		@<해밀턴 순환이 없다고 알린다@>
	}
	@<해의 순환들을 찾는다@>
	if cycptr > 1 {
		@<순환들을 합쳐 본다@>
	}
	if cycptr == 1 {
		@<찾은 해밀턴 순환을 확인하고 찍는다@>
		return
	}
	@<남은 순환마다 컷셋 절을 보탠다@>
}

@ @<해밀턴 순환이 없다고...@>=
fmt.Printf("해밀턴 순환이 없다 (%d 라운드, 컷셋 절 %d개, mem %d)\n", rounds, cutclauses, mems)
return

@* 순환 찾기와 합치기.
참인 호 $v\to u$마다 |sol[v]=u|, |rsol[u]=v|로 둔다. 순환에는 1부터 번호를 매기고,
꼭짓점 |v|가 든 순환의 번호를 |cid[v]|에 둔다. 순환 |c|에서 아무렇게나 고른 첫
꼭짓점이 |leader[c]|다. 아직 다른 순환에 흡수되지 않은 순환들의 번호는
|cycs[0..cycptr-1]|에 있고, |cycs[k]=c|이면 |cloc[c]=k|다. 순환의 길이가 3 이상이니
순환은 많아야 $n/3$개다.

@<해의 순환들을 찾는다@>=
for v := 0; v < n; v++ {
	for a := g.Vertices[v].Arcs; a != nil; a = a.Next {
		if u := int(g.Index(a.Tip)); s.Value(adj[v][u]) {
			sol[v], rsol[u] = u, v
		}
	}
	cid[v] = 0
}
cycptr = 0
for v := 0; v < n; v++ {
	if cid[v] == 0 {
		cycptr++
		leader[cycptr], cycs[cycptr-1], cloc[cycptr], cid[v] = v, cycptr, cycptr-1, cycptr
		for u := sol[v]; u != v; u = sol[u] {
			cid[u] = cycptr
		}
	}
}

@ 순환 여럿을 곧바로 컷셋으로 넘기기 전에, 원본은 호 두 개를 맞바꾸어 순환들을
합쳐 본다. 순환 $c$의 호 $v\to w$가 있고, 다른 순환 $c'$에 꼭짓점 $v'$과 $w'$이 있어
$v\to v'$과 $w'\to w$가 $G$의 호이며, $v'$이 $c'$에서 $w'$의 바로 뒤나 바로 앞이라고
하자. 그러면 $v\to w$를 끊고 $v\to v'\to\cdots\to w'\to w$로 돌아가게 하여 $c'$ 전체를
$c$에 끼워 넣을 수 있다. $v'$이 $w'$의 바로 앞이면 $c'$을 거꾸로 돌아야 한다.

합친 결과는 풀이기의 해가 아니다. 그래도 순환 덮개이기는 하니, 하나로 합쳐지면
해밀턴 순환이고, 여럿이 남으면 그 꼭짓점 집합들로 컷셋 절을 만들 수 있다.

원본은 순환 하나씩 맡아 첫 꼭짓점부터 한 바퀴 돌며 다른 순환을 흡수한다. 흡수를
모두 시도한 순환은 |cycs|의 앞쪽 |cyctested|칸에 모인다.

@<순환들을 합쳐 본다@>=
merging:
for j := 0; j < cycptr; j = cloc[c] + 1 {
	cyctested, c = j, cycs[j]
	@<순환 |c|에 다른 순환들을 흡수해 본다; 하나만 남으면 |break merging|@>
}

@ 원본은 두 번째 경우에 길을 뒤집은 뒤 첫 번째 경우의 레이블 |merge|로 뛰어든다.
\GO/는 블록 안으로 뛰어들 수 없으므로, 첫 번째 경우가 아니면 두 번째를 보고, 둘 다
아니면 |continue|로 넘어가게 풀어 적었다. 흡수한 뒤에는 |w|가 끼워 넣은 길의 첫
꼭짓점 |vv|가 되고, |v|의 나머지 이웃들로 계속 시도한다.

@<순환 |c|에 다른...@>=
for v, w := leader[c], sol[leader[c]]; ; v, w = w, sol[w] {
	for a := g.Vertices[v].Arcs; a != nil; a = a.Next {
		vv := int(g.Index(a.Tip))
		cc := cid[vv]
		if cc == c {
			continue
		}
		ww := rsol[vv]
		if adj[ww][w] == 0 {
			if ww = sol[vv]; adj[ww][w] == 0 {
				continue
			}
			@<|ww|에서 |vv|까지의 길을 뒤집는다@>
		}
		@<|vv|에서 |ww|까지의 길을 |c|에 끼우고 순환 |cc|를 지운다@>
	}
	if w == leader[c] {
		break
	}
}

@ 여기 올 때 $|ww|=|sol[vv]|$이다. 그러니 |ww|부터 순환을 따라가며 호의 방향을 뒤집으면
|vv|에서 |ww|로 가는 길이 된다.

@<|ww|에서 |vv|까지의 길을...@>=
for u, uu := ww, sol[ww]; u != vv; {
	uuu := sol[uu]
	sol[uu], rsol[u] = u, uu
	u, uu = uu, uuu
}

@ 순환 |cc|를 지울 때는 조심해야 한다. 지울 순환이 이미 흡수를 모두 시도한 순환
(|cloc[cc]<cyctested|)일 수도 있기 때문이다. 원본은 ``드물지만 불가능하지는 않다!
생각해 보라''라고 적었다. 그럴 때는 |cycs|의 뒤쪽을 한 칸씩 당기고, 아니면 맨 끝의
순환을 |cc|의 자리로 옮긴다.

@<|vv|에서 |ww|까지의 길을 |c|에...@>=
sol[v], sol[ww], rsol[vv], rsol[w] = vv, w, v, ww
w = vv
for u := vv; ; u = sol[u] {
	cid[u] = c
	if u == ww {
		break
	}
}
if cycptr--; cycptr == 1 {
	break merging
}
if k := cloc[cc]; k < cyctested {
	for ; k < cycptr; k++ {
		cycs[k] = cycs[k+1]
		cloc[cycs[k]] = k
	}
	cyctested--
} else {
	cycs[k] = cycs[cycptr]
	cloc[cycs[k]] = k
}

@* 컷셋.
합치고도 순환 $t$개가 남아 꼭짓점들을 $V_1$, \dots, $V_t$로 나누었다고 하자. 해밀턴
순환이라면 어느 $V_j$에서든 적어도 한 번 나가고 한 번 들어와야 한다. 그러니 $V_j$에서
나가는 호들의 절 하나와 $V_j$로 들어오는 호들의 절 하나를 보탠다. 방금 찾은 순환
덮개는 $V_j$ 밖으로 나가는 호가 없으므로 이 절을 어기고, 다시는 나오지 않는다.
순환이 둘이면 $V_1$에서 나가는 호는 곧 $V_2$로 들어오는 호이므로 절 한 쌍이면 된다.

컷의 크기가 0이면 $G$가 이어져 있지 않다. 1이면 그 간선 하나로 나갔다 들어와야
하는데 한 간선을 두 번 지날 수는 없다. 어느 쪽이든 해밀턴 순환이 없다.

@<남은 순환마다 컷셋 절을 보탠다@>=
for j := 0; j < cycptr; j++ {
	c = cycs[j]
	var out, in []sat.Lit
	for v := leader[c]; ; v = sol[v] {
		for a := g.Vertices[v].Arcs; a != nil; a = a.Next {
			if u := int(g.Index(a.Tip)); cid[u] != c {
				out, in = append(out, adj[v][u]), append(in, adj[u][v])
			}
		}
		if sol[v] == leader[c] {
			break
		}
	}
	if len(out) < 2 {
		@<해밀턴 순환이 없다고...@>
	}
	s.AddClause(out...)
	s.AddClause(in...)
	if cutclauses += 2; cycptr == 2 {
		break
	}
}

@* 답 찍기.
합친 순환은 풀이기가 준 해가 아니므로 한 번 더 확인한다. 꼭짓점 0에서 |sol|을
따라가며 모든 꼭짓점을 한 번씩 지나 제자리로 오는지, 지나는 호가 모두 $G$의
호인지 본다. 원본처럼 꼭짓점 0에서 시작해 이름을 늘어놓고, 나이트 그래프이면 판에
걸음 번호를 적은 그림도 그린다.

@<찾은 해밀턴 순환을...@>=
step := make([]int, n)
u := 0
fmt.Print(g.Vertices[0].Name)
for k := 1; k <= n; k++ {
	if step[u] != 0 || adj[u][sol[u]] == 0 {
		panic("hamsat: 찾은 순환이 틀렸다")
	}
	step[u], u = k, sol[u]
	fmt.Print(" ", g.Vertices[u].Name)
}
fmt.Println()
if u != 0 {
	panic("hamsat: 찾은 순환이 틀렸다")
}
if knight {
	@<나이트 판에 걸음 번호를 그린다@>
}
fmt.Printf("해밀턴 순환을 찾았다 (%d 라운드, 컷셋 절 %d개, mem %d)\n", rounds, cutclauses, mems)

@ 생성기 |Board|는 꼭짓점을 행 우선으로 늘어놓으므로 칸 $(i,j)$가 꼭짓점 $i\cdot n+j$다.

@<나이트 판에 걸음...@>=
for i := 0; i < int(*rows); i++ {
	for j := 0; j < int(*cols); j++ {
		fmt.Printf("%4d", step[i*int(*cols)+j])
	}
	fmt.Println()
}

@* 해 보기.
원본과 답을 견주어 보았다. Stanford GraphBase의 생성기로 그래프 스물넷을 만들어 파일로
적고, 크누스의 \.{HAMSAT}과 이 프로그램에 같은 파일을 주었다. 해밀턴 순환이 있는지
없는지는 스물넷 모두 같았다. 라운드 수는 가끔 다른데, 풀이기가 찾아 주는 순환 덮개가
원본과 다르기 때문이다.

몇 가지를 들면 이렇다. 기본값인 $8\times8$ 판에서는 첫 라운드의 순환 덮개가 합치기만으로
해밀턴 순환이 되어 컷셋 절이 하나도 필요 없다. 꼭짓점 열 개의 Petersen 그래프는 두
프로그램 모두 일곱 라운드 만에 해밀턴 순환이 없음을 보인다. 일반화 Petersen 그래프
$GP(n,2)$는 $n\bmod6=5$이면 해밀턴 순환이 없다고 알려져 있는데, 그 가운데 $GP(23,2)$에서
원본은 262라운드, 이 프로그램은 258라운드가 걸렸다.

가장 비싼 것은 뜻밖에 $7\times7$ 판이었다. 나이트는 한 번 뛸 때마다 칸의 색을 바꾸니
칸이 홀수 개인 판에는 닫힌 여행이 있을 수 없다. 풀이기는 이 한 줄짜리 논증을 모르므로,
첫 라운드에서 원본은 mem 7억 3천만 개, 이 프로그램은 5억 5천만 개를 들여 만족할 수
없음을 증명한다. 둘 다 1초 안팎이다.

@* 색인.
