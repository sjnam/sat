\datethis
\def\title{A certificate for the flower snark}

@s sat.Lit int
@s sat.Status int
@s clause int
@s checker int

@* Introduction.
The flower snark clauses are one of Knuth's favorite benchmarks. Exercise~176
of this same section defines the cubic graph $J_q$ on $4q$ vertices and its line graph
$L(J_q)$, which needs four colors when $q$ is odd; the clauses
$fsnark(q)$ that ask for a 3-coloring of $L(J_q)$ are therefore unsatisfiable,
and they are hard. Section 7.2.2.2 uses them again and again.

Exercise 282 asks for a proof that a \.{SAT} solver can check:

\medskip{\narrower\noindent\bf 282.~[M33]\enspace\rm Construct a certificate
of unsatisfiability for the clauses $fsnark(q)$ of exercise 176 when $q\ge3$
is odd, using $O(q)$ clauses, all having length $\le4$.\par}\medskip

\noindent A {\it certificate of unsatisfiability\/} is a sequence of clauses
$(C_1,\ldots,C_t)$ with $C_t=\epsilon$ such that
$$F\land C_1\land\cdots\land C_{i-1}\land\overline C_i\vdash_1\epsilon,
  \qquad 1\le i\le t,\eqno(119)$$
where $\vdash_1$ means ``unit propagation reaches a contradiction'' and
$\overline C_i$ is the conjunction of the complements of $C_i$'s literals.
Checking one is cheap and needs no trust in the solver that produced it, which
is the whole point.

The answer builds such a certificate by hand, in five stages. This program
builds the clauses exactly as the answer prescribes, and checks every one of
them with a unit-propagation checker of its own---no solver anywhere in that
loop. Then it turns the tables: it asks the {\tt sat} package of the directory
above, a Go rendering of Knuth's {\tt SAT13}, to refute $fsnark(q)$ itself, and
checks the certificate that Algorithm~C produces as a byproduct (Theorem~G).
The \.l option of {\tt SAT13}, which writes the learned clauses to a file, was
ported to the package while this reading was being written; it is |SetProof|
there.

I wrote this on 16 September 2026.

@ Every claim is a mode.
@c
package main

import (
	"context"
	"flag"
	"fmt"
	"math/rand/v2"
	"os"
	"strconv"
	"strings"
	"time"

	"github.com/sjnam/sat"
)

@<Types@>
@<Global variables@>
@<Functions@>

func main() {
	@<Read the command line@>
	if on("graph") {
		@<Check the graph against exercise 176@>
	}
	if on("fsnark") {
		@<Generate the clauses and solve them@>
	}
	if on("cert") {
		@<Build the answer's certificate and check it@>
	}
	if on("remarks") {
		@<Check what the answer says in passing@>
	}
	if on("algc") {
		@<Check the certificate that Algorithm C produces@>
	}
	if on("waerden") {
		@<Refute waerden(3,10;97) and check its certificate@>
	}
	if on("selftest") {
		@<Test the checker itself@>
	}
	if mode == "dump" {
		fmt.Print(knuthFile())
	}
}

@ The default $q$ is 9, which makes every mode instant. The interesting
value is 99, the size Knuth uses in the text; \.{-mode algc -q 99} takes a few
seconds.
@<Read the command line@>=
flag.StringVar(&mode, "mode", "all",
	"graph, fsnark, cert, remarks, algc, waerden, selftest, all, or dump")
flag.IntVar(&q, "q", 9, "the order of the flower snark")
flag.Parse()
if q < 3 {
	fmt.Println("q must be at least 3")
	os.Exit(1)
}

@ @<Global variables@>=
var (
	mode string
	q    int
)

@ @<Functions@>=
func on(m string) bool { return mode == m || mode == "all" }

@* The flower snark and its line graph.
The vertices of $J_q$ are $t_j$, $u_j$, $v_j$, $w_j$ and its edges are
$t_j\mathrel-t_{j+1}$, $t_j\mathrel-u_j$, $u_j\mathrel-v_j$,
$u_j\mathrel-w_j$, $v_j\mathrel-w_{j+1}$, $w_j\mathrel-v_{j+1}$, subscripts
modulo~$q$. Answer 176(a) names the corresponding vertices of the line graph
$a_j$, $b_j$, $c_j$, $d_j$, $e_j$, $f_j$ and lists its edges; those twelve per
index are what this program uses, and the graph mode checks them against $J_q$
itself.
@<Global variables@>=
const (
	aVert = iota
	bVert
	cVert
	dVert
	eVert
	fVert
)

@ Vertex $x_j$ of the line graph is number $6(j-1)+x$, with $j$ reduced modulo
$q$ first, exactly as in Knuth's generator.
@<Functions@>=
func vert(x, j int) int {
	j = (j-1)%q + 1
	if j < 1 {
		j += q
	}
	return 6*(j-1) + x
}

func vertName(v int) string {
	return fmt.Sprintf("%c%d", 'a'+v%6, v/6+1)
}

@ Here are the twelve edges of answer 176(a) that belong to index~$j$, in the
order Knuth's program creates them.
@<Functions@>=
func edgesAt(j int) [][2]int {
	k := j + 1
	return [][2]int{
		{vert(aVert, j), vert(aVert, k)}, {vert(aVert, j), vert(bVert, j)},
		{vert(aVert, j), vert(bVert, k)}, {vert(bVert, j), vert(cVert, j)},
		{vert(bVert, j), vert(dVert, j)}, {vert(cVert, j), vert(dVert, j)},
		{vert(cVert, j), vert(eVert, j)}, {vert(dVert, j), vert(fVert, j)},
		{vert(eVert, j), vert(dVert, k)}, {vert(eVert, j), vert(fVert, k)},
		{vert(fVert, j), vert(cVert, k)}, {vert(fVert, j), vert(eVert, k)},
	}
}

func edges() [][2]int {
	var es [][2]int
	for j := 1; j <= q; j++ {
		es = append(es, edgesAt(j)...)
	}
	return es
}

@ The line graph of a cubic graph is 4-regular, and its $12q$ edges fall into
$4q$ triangles---the two at each vertex of $J_q$ and the ones coming from the
edges. The answer names them $\{b_j,c_j,d_j\}$, $\{a_j,a_{j'},b_{j'}\}$,
$\{f_j,e_{j'},c_{j'}\}$, $\{e_j,f_{j'},d_{j'}\}$, where $j'=j+1$; the program
checks that these really are triangles and that they cover every edge exactly
once.
@<Functions@>=
func triangles() [][3]int {
	var ts [][3]int
	for j := 1; j <= q; j++ {
		k := j + 1
		ts = append(ts,
			[3]int{vert(bVert, j), vert(cVert, j), vert(dVert, j)},
			[3]int{vert(aVert, j), vert(aVert, k), vert(bVert, k)},
			[3]int{vert(fVert, j), vert(eVert, k), vert(cVert, k)},
			[3]int{vert(eVert, j), vert(fVert, k), vert(dVert, k)})
	}
	return ts
}

@ The line graph is built here from $J_q$'s own edges, independently of the
list above, and the two are compared. Two edges of $J_q$ are adjacent in
$L(J_q)$ when they share an endpoint.
@<Check the graph against exercise 176@>=
@<Build $L(J_q)$ from $J_q$@>
mine := map[[2]int]bool{}
for _, e := range edges() {
	mine[normalize(e)] = true
}
fmt.Printf("L(J_%d): %d edges from J_%d, %d from answer 176(a), same: %v\n",
	q, len(theirs), q, len(mine), sameEdges(theirs, mine))
@<Check the degrees and the triangles@>

@ @<Build $L(J_q)$ from $J_q$@>=
label := map[[2]int]int{} // an edge of $J_q$ and the vertex of $L(J_q)$ it becomes
for j := 1; j <= q; j++ {
	k := j%q + 1
	@<Name the six edges of $J_q$ that belong to index |j|@>
}
theirs := map[[2]int]bool{}
for e1, v1 := range label {
	for e2, v2 := range label {
		if v1 < v2 && (e1[0] == e2[0] || e1[0] == e2[1] ||
			e1[1] == e2[0] || e1[1] == e2[1]) {
			theirs[[2]int{v1, v2}] = true
		}
	}
}

@ The four vertices of $J_q$ at index $j$ are numbered $4(j-1)+0,\ldots,3$ for
$t_j$, $u_j$, $v_j$, $w_j$.
@<Name the six edges of $J_q$ that belong to index |j|@>=
t, u, v, w := 4*(j-1), 4*(j-1)+1, 4*(j-1)+2, 4*(j-1)+3
tk, vk, wk := 4*(k-1), 4*(k-1)+2, 4*(k-1)+3
label[normalize([2]int{t, tk})] = vert(aVert, j)
label[normalize([2]int{t, u})] = vert(bVert, j)
label[normalize([2]int{u, v})] = vert(cVert, j)
label[normalize([2]int{u, w})] = vert(dVert, j)
label[normalize([2]int{v, wk})] = vert(eVert, j)
label[normalize([2]int{w, vk})] = vert(fVert, j)

@ @<Functions@>=
func normalize(e [2]int) [2]int {
	if e[0] > e[1] {
		return [2]int{e[1], e[0]}
	}
	return e
}

func sameEdges(a, b map[[2]int]bool) bool {
	if len(a) != len(b) {
		return false
	}
	for e := range a {
		if !b[e] {
			return false
		}
	}
	return true
}

@ Every vertex should have degree four, and the $4q$ triangles should cover
each of the $12q$ edges exactly once.
@<Check the degrees and the triangles@>=
deg := make([]int, 6*q)
for _, e := range edges() {
	deg[e[0]]++
	deg[e[1]]++
}
four := true
for _, d := range deg {
	four = four && d == 4
}
cover := map[[2]int]int{}
for _, t := range triangles() {
	for _, e := range [][2]int{{t[0], t[1]}, {t[0], t[2]}, {t[1], t[2]}} {
		cover[normalize(e)]++
	}
}
once := len(cover) == 12*q
for _, n := range cover {
	once = once && n == 1
}
fmt.Printf("  every vertex has degree 4: %v; the %d triangles cover "+
	"every edge exactly once: %v\n", four, len(triangles()), once)

@* The clauses.
A clause is a list of literals, and a literal is $2v+1$ for $\bar v$ and $2v$
for~$v$, where the variable $v.p$ (``vertex $v$ has color $p$'') is numbered
$3v+p-1$.
@<Types@>=
type clause []int

@ @<Functions@>=
func lit(v, p int, neg bool) int {
	l := 2 * (3*v + p - 1)
	if neg {
		l++
	}
	return l
}

func litName(l int) string {
	v, p := l>>1/3, l>>1%3+1
	s := fmt.Sprintf("%s.%d", vertName(v), p)
	if l&1 == 1 {
		return "~" + s
	}
	return s
}

@ Knuth's {\mc SAT-COLOR} writes $n$ clauses (15) saying that every vertex has
a color, then $mc$ clauses (16) saying that adjacent vertices differ, with the
color as the outer loop; his change file prepends the three unit clauses
$b_{1,1}$, $c_{1,2}$, $d_{1,3}$ that break the symmetry. The clauses come out
in exactly that order here, because the order decides the variable numbering
and hence every mem the solver spends.
@<Functions@>=
func fsnarkClauses() []clause {
	cls := []clause{{lit(vert(bVert, 1), 1, false)},
		{lit(vert(cVert, 1), 2, false)}, {lit(vert(dVert, 1), 3, false)}}
	for v := 0; v < 6*q; v++ {
		cls = append(cls, clause{lit(v, 1, false), lit(v, 2, false),
			lit(v, 3, false)})
	}
	@<Append the clauses that keep neighbors apart@>
	return cls
}

@ The neighbors of a vertex are visited in the order of the {\mc SGB} arc
list, which is the reverse of the order in which the edges were created, and
only the neighbor with the larger number is used. This is what makes the file
identical to Knuth's, byte for byte.
@<Append the clauses that keep neighbors apart@>=
arcs := make([][]int, 6*q)
for _, e := range edges() {
	arcs[e[0]] = append([]int{e[1]}, arcs[e[0]]...)
	arcs[e[1]] = append([]int{e[0]}, arcs[e[1]]...)
}
for p := 1; p <= 3; p++ {
	for v := 0; v < 6*q; v++ {
		for _, u := range arcs[v] {
			if u > v {
				cls = append(cls, clause{lit(v, p, true), lit(u, p, true)})
			}
		}
	}
}

@ Knuth's file writes a unit clause with no leading blank, a clause of (15)
with one blank before each literal, and a clause of (16) with none. The first
line is a comment naming the generator. The \.{dump} mode prints it, so that
it can be compared with \.{fsnark-99.sat} of Knuth's {\tt SATexamples}; it
agrees.
@<Functions@>=
func knuthFile() string {
	var b strings.Builder
	fmt.Fprintf(&b, "~ sat-color-snark1 %d\n", q)
	for _, c := range fsnarkClauses() {
		var names []string
		for _, l := range c {
			names = append(names, litName(l))
		}
		if len(c) == 3 { // a clause of (15): a blank before each literal
			b.WriteByte(' ')
			b.WriteString(strings.Join(names, " "))
		} else { // a unit clause, or a clause of (16)
			b.WriteString(strings.Join(names, " "))
		}
		b.WriteByte('\n')
	}
	return b.String()
}

@ Now the clauses can be solved. For odd $q$ they are unsatisfiable; for even
$q$ they are not, which is exercise 176(b) and~(c).
@<Generate the clauses and solve them@>=
cls := fsnarkClauses()
fmt.Printf("fsnark(%d): %d variables, %d clauses\n", q, 18*q, len(cls))
st, stats, _ := solve(cls, false)
fmt.Printf("  %v, %d+%d mems, %d clauses learned\n", st, stats.IMems,
	stats.Mems, stats.Learned)
@<Solve a few small cases of both parities@>

@ @<Solve a few small cases of both parities@>=
save := q
for q = 3; q <= 8; q++ {
	st, _, _ := solve(fsnarkClauses(), false)
	want := sat.Unsat
	if q%2 == 0 {
		want = sat.Sat
	}
	fmt.Printf("  q=%d: %v (expected %v)\n", q, st, want)
}
q = save

@ The package numbers its variables in the order their names first appear, so
adding the clauses in Knuth's order reproduces his numbering. With
|withProof| the learned clauses are collected as they are produced.
@<Functions@>=
func solve(cls []clause, withProof bool) (sat.Status, sat.Stats, []clause) {
	s := sat.New()
	for _, c := range cls {
		var ls []sat.Lit
		for _, l := range c {
			x := s.Lookup(litName(l &^ 1))
			if l&1 == 1 {
				x = x.Not()
			}
			ls = append(ls, x)
		}
		s.AddClause(ls...)
	}
	var proof strings.Builder
	if withProof {
		s.SetProof(&proof)
	}
	st, err := s.Solve(context.Background())
	if err != nil {
		panic(err)
	}
	return st, s.Stats(), parseProof(proof.String(), litFromName)
}

@ The proof comes back as text in Knuth's format, so it has to be read back.
A line that begins with two blanks is a clause that was shortened in place by
on-the-fly subsumption; for our purposes it is just another learned clause.
The names are turned back into the numbering used here, not into the solver's
own, which follows the order in which names first appear.
@<Functions@>=
func parseProof(text string, litOf func(string) int) []clause {
	var out []clause
	for _, line := range strings.Split(text, "\n") {
		names := strings.Fields(line)
		if len(names) == 0 {
			continue
		}
		var c clause
		for _, name := range names {
			c = append(c, litOf(name))
		}
		out = append(out, c)
	}
	return out
}

@ @<Functions@>=
func litFromName(name string) int {
	neg := false
	if name[0] == '~' {
		neg, name = true, name[1:]
	}
	dot := strings.IndexByte(name, '.')
	j, _ := strconv.Atoi(name[1:dot])
	p, _ := strconv.Atoi(name[dot+1:])
	return lit(vert(int(name[0]-'a'), j), p, neg)
}

@* The answer's certificate.
The answer writes $a_j$ for $a_{j,p}$, leaving the color $p$ to be understood,
and uses $j'=j+1$ (modulo $q$) and $p'=p+1$ (modulo 3). Its five stages are
below, each in its own section, and |certificate| strings them together.
@<Functions@>=
func certificate(withBCD bool) []clause {
	var cert []clause
	add := func(ls ...int) { cert = append(cert, clause(ls)) }
	@<Learn the exclusion clauses (17)@>
	@<Learn two clauses for every triangle@>
	@<Learn six clauses, and eighteen more, for every index@>
	@<Learn the clauses of the hint, working down from |q|@>
	@<The endgame@>
	return cert
}

@ ``First learn the exclusion clauses (17).'' They say that a vertex has at
most one color; $fsnark(q)$ leaves them out, because a vertex with two colors
is harmless. They are nevertheless implied, and unit propagation sees it: if
$v$ had two colors, the other two vertices of a triangle through~$v$ would
both be forced into the third color. The answer remarks that the ones for
$b$, $c$ and $d$ are never used, and |withBCD| omits them.
@<Learn the exclusion clauses (17)@>=
for v := 0; v < 6*q; v++ {
	if !withBCD {
		switch v % 6 {
		case bVert, cVert, dVert:
			continue
		}
	}
	for p := 1; p <= 3; p++ {
		for r := p + 1; r <= 3; r++ {
			add(lit(v, p, true), lit(v, r, true))
		}
	}
}

@ ``For every such triangle $\{u,v,w\}$, learn $(\bar u_{p'}\lor v_p\lor w_p)$
and then $(u_p\lor v_p\lor w_p)$.'' The second clause says that every color
appears in every triangle---true because the three vertices of a triangle have
three distinct colors. The first is a stepping stone toward it.
@<Learn two clauses for every triangle@>=
for _, t := range triangles() {
	for p := 1; p <= 3; p++ {
		pp := p%3 + 1
		add(lit(t[0], pp, true), lit(t[1], p, false), lit(t[2], p, false))
		add(lit(t[0], p, false), lit(t[1], p, false), lit(t[2], p, false))
	}
}

@ Now the certificate starts to look ahead along the ring. For each index it
learns six clauses about $a$, $e$, $f$ at $j$ and $j'$, and for $j\ge3$
eighteen more that tie the pattern at indices 1 and~2 to the pattern at $j$
and~$j'$. In the eighteen, $u,v$ and $u',v'$ each run through the three pairs
$(a,e)$, $(e,f)$, $(f,a)$.
@<Learn six clauses, and eighteen more, for every index@>=
pairs := [][2]int{{aVert, eVert}, {eVert, fVert}, {fVert, aVert}}
for j := 1; j <= q; j++ {
	k := j + 1
	for p := 1; p <= 3; p++ {
		@<Learn the six clauses for index |j| and color |p|@>
	}
	if j >= 3 {
		for p := 1; p <= 3; p++ {
			@<Learn the eighteen clauses for index |j| and color |p|@>
		}
	}
}

@ @<Learn the six clauses for index |j| and color |p|@>=
aj, ej, fj := vert(aVert, j), vert(eVert, j), vert(fVert, j)
ak, ek, fk := vert(aVert, k), vert(eVert, k), vert(fVert, k)
add(lit(aj, p, false), lit(fj, p, false), lit(ak, p, false), lit(ek, p, false))
add(lit(aj, p, false), lit(ej, p, false), lit(ak, p, false), lit(fk, p, false))
add(lit(ej, p, false), lit(fj, p, false), lit(ek, p, false), lit(fk, p, false))
add(lit(aj, p, true), lit(ej, p, true), lit(ek, p, true))
add(lit(aj, p, true), lit(fj, p, true), lit(fk, p, true))
add(lit(ej, p, true), lit(fj, p, true), lit(ak, p, true))

@ The odd case keeps two literals from the far index, the even case only one.
@<Learn the eighteen clauses for index |j| and color |p|@>=
for _, uv := range pairs {
	for _, xy := range pairs {
		u1, v1 := vert(uv[0], 1), vert(uv[1], 1)
		u2, v2 := vert(uv[0], 2), vert(uv[1], 2)
		if j%2 == 1 {
			add(lit(u1, p, true), lit(v1, p, true),
				lit(vert(xy[0], j), p, false), lit(vert(xy[1], j), p, false))
			add(lit(u2, p, true), lit(v2, p, true),
				lit(vert(xy[0], k), p, false), lit(vert(xy[1], k), p, false))
		} else {
			add(lit(u1, p, true), lit(v1, p, true), lit(vert(xy[0], j), p, true))
			add(lit(u2, p, true), lit(v2, p, true), lit(vert(xy[0], k), p, true))
		}
	}
}

@ ``Then we're ready to learn $(\bar a_j\lor\bar e_j)$, $(\bar a_j\lor\bar
f_j)$, $(\bar e_j\lor\bar f_j)$ for $j\in\{1,2\}$ and $(a_j\lor e_j\lor
f_j\lor a_{j'})$, $(a_j\lor e_j\lor f_j)$ for $j\in\{1,q\}$.'' The clauses of
the hint say that $a_j$, $e_j$, $f_j$ have three distinct colors and that all
three colors occur among them. After the two starting indices, the same pair
of clauses is learned for $j=q,q-1,\ldots,2$, which walks the conclusion all
the way around the ring.
@<Learn the clauses of the hint, working down from |q|@>=
for p := 1; p <= 3; p++ {
	for _, j := range []int{1, 2} {
		@<Learn that $a_j$, $e_j$, $f_j$ differ@>
	}
	for _, j := range []int{1, q} {
		add(lit(vert(aVert, j), p, false), lit(vert(eVert, j), p, false),
			lit(vert(fVert, j), p, false), lit(vert(aVert, j+1), p, false))
		add(lit(vert(aVert, j), p, false), lit(vert(eVert, j), p, false),
			lit(vert(fVert, j), p, false))
	}
}
for j := q; j >= 2; j-- {
	for p := 1; p <= 3; p++ {
		@<Learn that $a_j$, $e_j$, $f_j$ differ@>
	}
	for p := 1; p <= 3; p++ {
		add(lit(vert(aVert, j-1), p, false), lit(vert(eVert, j-1), p, false),
			lit(vert(fVert, j-1), p, false), lit(vert(aVert, j), p, false))
		add(lit(vert(aVert, j-1), p, false), lit(vert(eVert, j-1), p, false),
			lit(vert(fVert, j-1), p, false))
	}
}

@ @<Learn that $a_j$, $e_j$, $f_j$ differ@>=
add(lit(vert(aVert, j), p, true), lit(vert(eVert, j), p, true))
add(lit(vert(aVert, j), p, true), lit(vert(fVert, j), p, true))
add(lit(vert(eVert, j), p, true), lit(vert(fVert, j), p, true))

@ The endgame is where the parity of $q$ finally bites. Answer 176(c) shows
that the colors of $a_je_jf_j$ are permuted by an odd permutation whenever $j$
is even, so going once around a ring of odd length is impossible. The
certificate says this by fixing the colors of $a_1$ and $e_1$ and walking
around; the three clauses learned at index~$j$ depend on the parity of~$j$,
and the walk closes up on a contradiction.
@<The endgame@>=
for p := 1; p <= 3; p++ {
	for _, pr := range [][2]int{{p%3 + 1, (p+1)%3 + 1}, {(p+1)%3 + 1, p%3 + 1}} {
		p1, p2 := pr[0], pr[1]
		base := []int{lit(vert(aVert, 1), p, true), lit(vert(eVert, 1), p1, true)}
		for j := 2; j <= q; j++ {
			@<Learn three clauses for index |j| of the walk@>
		}
		add(base...)
	}
	add(lit(vert(aVert, 1), p, true))
}

@ @<Learn three clauses for index |j| of the walk@>=
aj, ej := vert(aVert, j), vert(eVert, j)
trio := [][2]int{{p, p2}, {p1, p}, {p2, p1}}
if j%2 == 1 {
	trio = [][2]int{{p, p1}, {p1, p2}, {p2, p}}
}
for _, pq := range trio {
	add(append(append(clause{}, base...), lit(aj, pq[0], true),
		lit(ej, pq[1], false))...)
}

@* Checking a certificate.
The checker is a miniature solver that knows only unit propagation: clauses
watch two literals each, and a clause whose watched literal becomes false
either finds a new watch, forces its other watch, or reports a conflict. This
is the whole of condition (119), and none of the package's machinery is
involved.
@<Types@>=
type checker struct {
	nv     int
	cls    []clause
	watch  [][]int // clauses watching a literal
	val    []int8  // 1 if the literal is true
	reason []int   // the clause that forced a literal, $-1$ if none
	trail  []int
	dead   bool // the clauses at hand are already contradictory
}

@ @<Functions@>=
func newChecker(nv int, cls []clause) *checker {
	c := &checker{nv: nv, watch: make([][]int, 2*nv), val: make([]int8, 2*nv),
		reason: make([]int, 2*nv)}
	for i := range c.reason {
		c.reason[i] = -1
	}
	for _, cl := range cls {
		c.add(cl)
	}
	if c.propagate() >= 0 {
		c.dead = true
	}
	return c
}

@ A unit clause is asserted at once; longer clauses watch their first two
literals.
@<Functions@>=
func (c *checker) add(cl clause) int {
	k := len(c.cls)
	c.cls = append(c.cls, cl)
	switch len(cl) {
	case 0:
		c.dead = true
	case 1:
		if c.assign(cl[0], k) {
			c.dead = true
		}
	default:
		c.watch[cl[0]] = append(c.watch[cl[0]], k)
		c.watch[cl[1]] = append(c.watch[cl[1]], k)
	}
	return k
}

func (c *checker) assign(l, why int) bool {
	if c.val[l] == 1 {
		return false
	}
	if c.val[l^1] == 1 {
		return true // the clauses at hand contradict each other
	}
	c.val[l], c.reason[l] = 1, why
	c.trail = append(c.trail, l)
	return false
}

@ Propagation returns the number of a falsified clause, or $-1$.
@<Functions@>=
func (c *checker) propagate() int {
	for i := 0; i < len(c.trail); i++ {
		l := c.trail[i]
		ws := c.watch[l^1]
		for j := 0; j < len(ws); j++ {
			@<Look at clause |ws[j]|, whose watched literal just went false@>
		}
	}
	return -1
}

@ @<Look at clause |ws[j]|, whose watched literal just went false@>=
k := ws[j]
cl := c.cls[k]
if cl[0] == l^1 {
	cl[0], cl[1] = cl[1], cl[0]
}
if c.val[cl[0]] == 1 {
	continue
}
moved := false
for m := 2; m < len(cl); m++ {
	if c.val[cl[m]^1] != 1 {
		cl[1], cl[m] = cl[m], cl[1]
		c.watch[cl[1]] = append(c.watch[cl[1]], k)
		ws[j] = ws[len(ws)-1]
		ws = ws[:len(ws)-1]
		c.watch[l^1] = ws
		j--
		moved = true
		break
	}
}
if moved {
	continue
}
if c.val[cl[0]^1] == 1 || c.assign(cl[0], k) {
	return k
}

@ @<Functions@>=
func (c *checker) undo(to int) {
	for i := len(c.trail) - 1; i >= to; i-- {
		c.val[c.trail[i]] = 0
		c.reason[c.trail[i]] = -1
	}
	c.trail = c.trail[:to]
}

@ Here is the test of (119) for one clause. Its literals are negated, the
consequences are drawn, and a conflict must appear. What is left behind is the
list of clauses that took part, which exercise 284 uses to tell which clauses
of a certificate are really needed.
@<Functions@>=
func (c *checker) rup(cl clause) (bool, []int) {
	if c.dead {
		return true, nil
	}
	base := len(c.trail)
	conflict, forced := -1, -1
	for _, l := range cl {
		if c.val[l] == 1 { // its negation contradicts what we know
			forced = c.reason[l]
			break
		}
		if c.val[l^1] != 1 {
			c.assign(l^1, -1)
		}
	}
	var used []int
	if forced == -1 {
		conflict = c.propagate()
		if conflict >= 0 {
			used = c.participants(conflict)
		}
	} else if forced >= 0 {
		used = []int{forced}
	}
	c.undo(base)
	return forced != -1 || conflict >= 0, used
}

@ To see which clauses really mattered, start from the falsified clause and
walk back down the trail, taking the reason of every literal that the walk has
touched. This is the marking of exercise 284, done with reasons so that
clauses which propagated something irrelevant are not marked.
@<Functions@>=
func (c *checker) participants(conflict int) []int {
	seen := map[int]bool{}
	used := []int{conflict}
	for _, m := range c.cls[conflict] {
		seen[m^1] = true
	}
	for i := len(c.trail) - 1; i >= 0; i-- {
		l := c.trail[i]
		if !seen[l] || c.reason[l] < 0 {
			continue
		}
		used = append(used, c.reason[l])
		for _, m := range c.cls[c.reason[l]] {
			if m != l {
				seen[m^1] = true
			}
		}
	}
	return used
}

@ A whole certificate is checked in one forward pass. Afterwards the clauses
that the final contradiction really depends on are collected backwards, which
is how exercise 284 saves work; here it only reports how much of the
certificate was redundant.
@<Functions@>=
func check(nv int, cls, cert []clause) (bad, used int, need []bool,
	dur time.Duration) {
	start := time.Now()
	c := newChecker(nv, cls)
	base := len(c.cls)
	deps := make([][]int, len(cert))
	for i, cl := range cert {
		ok, d := c.rup(cl)
		if !ok {
			bad++
		}
		deps[i] = d
		c.add(cl)
	}
	@<Make sure the empty clause follows, and count what was needed@>
	return bad, used, need[base:], time.Since(start)
}

@ @<Make sure the empty clause follows, and count what was needed@>=
ok, last := c.rup(nil)
if !ok {
	bad++
}
need = make([]bool, len(c.cls))
for _, k := range last {
	need[k] = true
}
for i := len(cert) - 1; i >= 0; i-- {
	if !need[base+i] {
		continue
	}
	used++
	for _, k := range deps[i] {
		need[k] = true
	}
}

@* What the answer claims.
The certificate mode builds the clauses and checks them. The exercise asks for
$O(q)$ clauses of length at most four, so both are reported; the count comes
to $147q-102$.
@<Build the answer's certificate and check it@>=
cls := fsnarkClauses()
cert := certificate(true)
long := 0
for _, c := range cert {
	if len(c) > long {
		long = len(c)
	}
}
bad, used, _, dur := check(18*q, cls, cert)
fmt.Printf("certificate for q=%d: %d clauses, longest %d, failures %d, "+
	"needed %d, checked in %v\n", q, len(cert), long, bad, used,
	dur.Round(time.Millisecond))
@<Report how the count grows with $q$@>

@ @<Report how the count grows with $q$@>=
save := q
fmt.Printf("  clauses for q = 3, 5, ..., 15:")
for q = 3; q <= 15; q += 2 {
	fmt.Printf(" %d", len(certificate(true)))
}
fmt.Printf("; that is 147q-102\n")
q = save

@ The answer adds three remarks, and each one is a claim to check: that the
exclusion clauses for $b$, $c$ and $d$ are never used; that the certificate
does not lean on the three symmetry-breaking unit clauses of $fsnark(q)$; and,
implicitly, that $q$ must be odd.
@<Check what the answer says in passing@>=
cls := fsnarkClauses()
bad, used, _, _ := check(18*q, cls, certificate(false))
fmt.Printf("without the exclusion clauses for b, c, d: %d clauses, "+
	"failures %d, needed %d\n", len(certificate(false)), bad, used)
bad, _, _, _ = check(18*q, cls[3:], certificate(true))
fmt.Printf("against fsnark(%d) without its three unit clauses: failures %d\n",
	q, bad)
@<Try an even order@>

@ @<Try an even order@>=
save := q
q++
bad, _, _, _ = check(18*q, fsnarkClauses(), certificate(true))
st, _, _ := solve(fsnarkClauses(), false)
fmt.Printf("at q=%d, which is even: %v, and the certificate has %d failures\n",
	q, st, bad)
q = save

@* Algorithm C's own certificate.
Theorem G says that the clauses Algorithm C learns are themselves a
certificate of unsatisfiability. The package now hands them over through
|SetProof|, so the claim can be tested rather than believed; and once they are
in hand, the two certificates can be compared.
@<Check the certificate that Algorithm C produces@>=
cls := fsnarkClauses()
st, stats, cert := solve(cls, true)
if st != sat.Unsat {
	fmt.Println("expected UNSAT, got", st)
} else {
	@<Report and check what Algorithm C learned@>
}

@ @<Report and check what Algorithm C learned@>=
sum, long := 0, 0
for _, c := range cert {
	sum += len(c)
	if len(c) > long {
		long = len(c)
	}
}
bad, used, _, dur := check(18*q, cls, cert)
fmt.Printf("Algorithm C on fsnark(%d): %d+%d mems, %d clauses learned\n",
	q, stats.IMems, stats.Mems, stats.Learned)
fmt.Printf("  certificate: %d clauses, average length %.1f, longest %d\n",
	len(cert), float64(sum)/float64(len(cert)), long)
fmt.Printf("  failures %d, needed %d (%.1f%%), checked in %v\n", bad, used,
	100*float64(used)/float64(len(cert)), dur.Round(time.Millisecond))
fmt.Printf("  the answer's certificate has %d clauses, none longer than 4\n",
	len(certificate(true)))

@* The other example in the text.
Page 255, where certificates are introduced, gives numbers for two runs:
Algorithm C learns ``about 53,000'' clauses when it refutes
$waerden(3,10;97)$ and ``about 135,000'' when it refutes $fsnark(99)$, of
which ``fewer than 50,000'' and ``fewer than 47,000'' are used again later;
and the waerden certificate ``was found in 272 megamems,'' while checking it
by straightforward unit propagation cost 2.2 gigamems. The flower snark half
is measured by the \.{algc} mode above. The other half needs the van der
Waerden clauses, which are two lines to generate: no $j$ equally spaced
positions may all be 0, and no $k$ equally spaced positions may all be~1.
@<Functions@>=
func waerdenClauses(j, k, n int) []clause {
	var cls []clause
	runs := func(length int, neg bool) {
		for d := 1; (length-1)*d < n; d++ {
			for i := 1; i+(length-1)*d <= n; i++ {
				var c clause
				for t := 0; t < length; t++ {
					l := 2 * (i + t*d - 1)
					if neg {
						l++
					}
					c = append(c, l)
				}
				cls = append(cls, c)
			}
		}
	}
	runs(j, false)
	runs(k, true)
	return cls
}

@ These clauses come out in the same order as Knuth's own
\.{waerden-3-10-97.sat}, so the solver spends the same mems on them and learns
the same clauses.
@<Refute waerden(3,10;97) and check its certificate@>=
cls := waerdenClauses(3, 10, 97)
s, st, cert := solveRaw(97, cls, true)
if st != sat.Unsat {
	fmt.Println("expected UNSAT, got", st)
} else {
	@<Report and check the waerden certificate@>
}

@ @<Report and check the waerden certificate@>=
bad, used, _, dur := check(97, cls, cert)
stats := s.Stats()
fmt.Printf("waerden(3,10;97): %d clauses, %d+%d mems, %d clauses learned\n",
	len(cls), stats.IMems, stats.Mems, stats.Learned)
fmt.Printf("  certificate of %d clauses\n", len(cert))
fmt.Printf("  failures %d, needed %d (%.1f%%), checked in %v\n", bad, used,
	100*float64(used)/float64(len(cert)), dur.Round(time.Millisecond))

@* Testing the checker.
A checker that never says no is worth nothing. The decisive test is this: if a
formula has a satisfying assignment, then no clause that the assignment
falsifies can be implied by it, so unit propagation must fail to derive a
contradiction from it. Random satisfiable problems therefore give a supply of
clauses that the checker has to reject, and it must reject every one.

A second test is the other way round: genuine certificates of the
unsatisfiable problems must pass. Spoiling one is not a test, because a
certificate carries slack---dropping a clause, or changing a literal, often
leaves a sequence that is still valid, since the same conclusions can be
reached along another path. What can be measured is how often the damage
shows, and that is reported rather than insisted upon.
@<Test the checker itself@>=
rng := rand.New(rand.NewPCG(282, 2026))
@<Reject clauses that a satisfying assignment falsifies@>
@<Accept genuine certificates, and see how easily they break@>

@ Ten variables and thirty random clauses of three literals are usually
satisfiable; forty-five are usually not.
@<Functions@>=
func randomProblem(rng *rand.Rand, nv, m int) []clause {
	var cls []clause
	for i := 0; i < m; i++ {
		var c clause
		for len(c) < 3 {
			if l := rng.IntN(2 * nv); !hasVar(c, l) {
				c = append(c, l)
			}
		}
		cls = append(cls, c)
	}
	return cls
}

func hasVar(c clause, l int) bool {
	for _, m := range c {
		if m>>1 == l>>1 {
			return true
		}
	}
	return false
}

@ @<Reject clauses that a satisfying assignment falsifies@>=
const nv = 10
rejected, offered := 0, 0
for trial := 0; trial < 200; trial++ {
	cls := randomProblem(rng, nv, 30)
	s, st, _ := solveRaw(nv, cls, false)
	if st != sat.Sat {
		continue
	}
	c := newChecker(nv, cls)
	for k := 0; k < 5; k++ {
		@<Fabricate a clause the solution falsifies, and offer it@>
	}
}
fmt.Printf("clauses refuted by a known solution: %d of %d rejected\n",
	rejected, offered)

@ Every literal of the fabricated clause is false in the solution, so the
clause cannot follow from the formula by any means, let alone by propagation.
@<Fabricate a clause the solution falsifies, and offer it@>=
var bogus clause
for len(bogus) < 1+rng.IntN(3) {
	v := rng.IntN(nv)
	l := 2 * v
	if s.Value(sat.Pos(v + 1)) {
		l++ // the solution makes $x_{v+1}$ true, so $\bar x_{v+1}$ is false
	}
	if !hasVar(bogus, l) {
		bogus = append(bogus, l)
	}
}
offered++
if ok, _ := c.rup(bogus); !ok {
	rejected++
}

@ @<Accept genuine certificates, and see how easily they break@>=
good, wrong, spoiled, noticed := 0, 0, 0, 0
for trial := 0; trial < 200; trial++ {
	cls := randomProblem(rng, nv, 45)
	_, st, cert := solveRaw(nv, cls, true)
	if st != sat.Unsat || len(cert) < 3 {
		continue
	}
	good++
	bad, _, need, _ := check(nv, cls, cert)
	if bad != 0 {
		wrong++
	}
	@<Spoil this certificate and see whether it is noticed@>
}
fmt.Printf("genuine certificates: %d checked, %d rejected\n", good, wrong)
fmt.Printf("spoiled certificates: %d of %d were noticed\n", noticed, spoiled)

@ The three kinds of damage are: dropping a clause that the backward pass
found necessary, changing one of its literals, and reversing the order.
@<Spoil this certificate and see whether it is noticed@>=
victim := -1
for i, ok := range need {
	if ok {
		victim = i
		break
	}
}
if victim < 0 {
	continue
}
dropped := append(append([]clause{}, cert[:victim]...), cert[victim+1:]...)
changed := append([]clause{}, cert...)
changed[victim] = alter(rng, changed[victim], nv)
reversed := make([]clause, len(cert))
for i, cl := range cert {
	reversed[len(cert)-1-i] = cl
}
for _, mess := range [][]clause{dropped, changed, reversed} {
	spoiled++
	if bad, _, _, _ := check(nv, cls, mess); bad != 0 {
		noticed++
	}
}

@ @<Functions@>=
func alter(rng *rand.Rand, c clause, nv int) clause {
	out := append(clause{}, c...)
	for {
		if l := rng.IntN(2 * nv); !hasVar(out, l) {
			out[rng.IntN(len(out))] = l
			return out
		}
	}
}

@ The random problems have nothing to do with flower snarks, so they get
their own solver call, with plain variable names; the solver itself comes back
too, so that a solution can be read off it.
@<Functions@>=
func solveRaw(nv int, cls []clause, withProof bool) (*sat.Solver, sat.Status,
	[]clause) { // the solver carries the statistics
	s := sat.New()
	for i := 0; i < nv; i++ {
		s.Lookup(fmt.Sprintf("x%d", i+1))
	}
	for _, c := range cls {
		var ls []sat.Lit
		for _, l := range c {
			ls = append(ls, sat.Pos(l>>1+1)+sat.Lit(l&1))
		}
		s.AddClause(ls...)
	}
	var proof strings.Builder
	if withProof {
		s.SetProof(&proof)
	}
	st, err := s.Solve(context.Background())
	if err != nil {
		panic(err)
	}
	return s, st, parseProof(proof.String(), func(name string) int {
		neg := 0
		if name[0] == '~' {
			neg, name = 1, name[1:]
		}
		v, _ := strconv.Atoi(name[1:])
		return 2*(v-1) + neg
	})
}

@* Index.
