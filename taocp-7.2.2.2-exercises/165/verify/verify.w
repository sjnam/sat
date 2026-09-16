\datethis
\def\title{The largest positive autarky}

@s sat.Lit int
@s sat.Status int
@s sat.Solver int

@* Introduction.
An {\it autarky\/} for a family of clauses $F$ is a set $A$ of strictly
distinct literals such that every clause of $F$ either contains a literal of
$A$ or contains no literal of $\bar A$; in the words of page 228, ``$A$
satisfies every clause that $A$ or $\bar A$ touches.'' Whenever $A$ is an
autarky we may set its literals true without losing satisfiability, which is
why Algorithm~X looks for autarkies while it looks ahead. Exercise
7.2.2.2--165 asks for the positive ones:

\medskip{\narrower\noindent\bf165.~[26]\enspace\rm Design an algorithm to find
the largest positive autarky $A$ for a given $F$, namely an autarky that
contains only positive literals. {\it Hint:} Warm up by finding the largest
positive autarky for the clauses $\{12\bar3, 12\bar5, \bar1\bar3\bar4,
13\bar6, 1\bar45, 156, \bar235, 2\bar46, 345, \bar356\}$.\par}\medskip

@ The answer is a small gem, and every sentence of it makes a claim.
\smallskip
\item{1.} In the warm-up, $\bar1\bar3\bar4$ excludes 1, 3, 4; then $13\bar6$
excludes 6; and $A=\{2,5\}$ works, so it is the maximum.
\item{2.} A maximum (not just maximal) positive autarky always exists,
because the union of positive autarkies is a positive autarky.
\item{3.} A clause $(v_1\lor\cdots\lor v_s\lor\bar v_{s+1}\lor\cdots\lor\bar
v_{s+t})$ of $F$ says that $v_1\notin A$ and $\cdots$ and $v_s\notin A$ imply
$v_{s+j}\notin A$, so it generates $t$ Horn clauses; their core is the set of
positive literals that lie in no positive autarky.
\item{4.} A variant of Algorithm 7.1.1C, with steps C1 and C5 modified so that
one clause of $F$ yields $t$ Horn clauses, finds that core in linear time.
\item{5.} By complementing some variables and prohibiting others, the same
method finds the largest autarky contained in any given set of strictly
distinct literals.
\smallskip
\noindent This program checks all five. The first four are statements about
clauses and sets of variables, so they are checked against the definition by
brute force wherever the number of variables allows it. For larger problems
the {\tt sat} package of the directory above supplies an independent route:
a positive autarky containing $v$ exists exactly when a certain set of clauses
is satisfiable under the assumption $a_v$, and the package is asked that
question once per variable. It is also asked, twice per problem, whether the
autarky principle of page 228 really holds.

I wrote this on 16 September 2026.

@ Every claim is a mode.
@c
package main

import (
	"context"
	"flag"
	"fmt"
	"math/bits"
	"math/rand/v2"
	"os"
	"strconv"
	"strings"

	"github.com/sjnam/sat"
)

@<Types@>
@<Global variables@>
@<Functions@>

func main() {
	@<Read the command line@>
	if on("warmup") {
		@<Check the warm-up example@>
	}
	if on("union") {
		@<Check that positive autarkies are closed under union@>
	}
	if on("core") {
		@<Check the core algorithm against brute force@>
	}
	if on("linear") {
		@<Measure the running time of the core algorithm@>
	}
	if on("within") {
		@<Check the bracketed remark@>
	}
	if on("solver") {
		@<Check large problems with the {\tt sat} package@>
	}
	@<Say how it went@>
}

@ @<Read the command line@>=
flag.StringVar(&mode, "mode", "all",
	"warmup, union, core, linear, within, solver, or all")
flag.IntVar(&reps, "reps", 2000, "how many random cases per size")
flag.Uint64Var(&seed, "seed", 20260916, "seed for the random cases")
flag.Parse()

@ @<Global variables@>=
var (
	mode     string
	reps     int
	seed     uint64
	failures int
)

@ Each claim is announced, checked, and marked; one \.{FAIL} anywhere makes the
program exit with a nonzero status.
@<Functions@>=
func on(m string) bool { return mode == m || mode == "all" }

func claim(ok bool, format string, args ...any) {
	mark := "ok  "
	if !ok {
		mark = "FAIL"
		failures++
	}
	fmt.Printf("  %s  %s\n", mark, fmt.Sprintf(format, args...))
}

@ @<Say how it went@>=
if failures > 0 {
	fmt.Printf("\n%d claims failed.\n", failures)
	os.Exit(1)
}
fmt.Println("\nEvery claim checked out.")

@* Clauses and autarkies.
Literals are numbered as Knuth numbers them, $2v$ for $v$ and $2v+1$ for
$\bar v$. The clauses in this program can be long and the problems can have a
few hundred variables, so a clause is simply a list of literals.
@<Types@>=
type fam struct {
	n  int
	cl [][]int
}

@ Knuth's shorthand `$12\bar3$' is read as \.{123'}, one digit per variable.
@<Functions@>=
func parseFam(n int, s string) fam {
	f := fam{n: n}
	for _, w := range strings.Fields(s) {
		var c []int
		for i := 0; i < len(w); i++ {
			l := 2 * int(w[i]-'0')
			if i+1 < len(w) && w[i+1] == '\'' {
				l, i = l+1, i+1
			}
			c = append(c, l)
		}
		f.cl = append(f.cl, c)
	}
	return f
}

func clauseName(c []int) string {
	var b strings.Builder
	for _, l := range c {
		b.WriteString(strconv.Itoa(l >> 1))
		if l&1 == 1 {
			b.WriteByte('\'')
		}
	}
	return b.String()
}

@ The definition, word for word. |in[l]| says whether literal $l$ belongs to
$A$; a clause touched by $A$ or $\bar A$ must contain a literal of $A$.
@<Functions@>=
func isAutarky(f fam, in []bool) bool {
	for _, c := range f.cl {
		touched, satisfied := false, false
		for _, l := range c {
			satisfied = satisfied || in[l]
			touched = touched || in[l] || in[l^1]
		}
		if touched && !satisfied {
			return false
		}
	}
	return true
}

@ A positive autarky is a set of variables; for brute force it is a bitmask.
@<Functions@>=
func positive(n int, set uint64) []bool {
	in := make([]bool, 2*n+2)
	for v := 1; v <= n; v++ {
		if set&(1<<v) != 0 {
			in[2*v] = true
		}
	}
	return in
}

@ Brute force runs through all $2^n$ sets of variables. It reports a largest
positive autarky, the union of all of them, and whether that union is itself
an autarky.
@<Functions@>=
func bruteMax(f fam) (best, union uint64, count int, unionOK bool) {
	for set := uint64(0); set < 1<<uint(f.n); set++ {
		s := set << 1
		if !isAutarky(f, positive(f.n, s)) {
			continue
		}
		count++
		union |= s
		if bits.OnesCount64(s) > bits.OnesCount64(best) {
			best = s
		}
	}
	return best, union, count, isAutarky(f, positive(f.n, union))
}

@* The core algorithm.
Let the proposition $P_v$ mean ``$v\notin A$.'' A clause of $F$ with positive
variables $v_1$, \dots, $v_s$ and negative variables $v_{s+1}$, \dots,
$v_{s+t}$ is satisfied by every positive autarky that touches it, so
$P_{v_1}\land\cdots\land P_{v_s}\Rightarrow P_{v_{s+j}}$ for $1\le j\le t$.
These are definite Horn clauses, and Algorithm 7.1.1C finds their core.

Here is that algorithm with Knuth's own data structures. |conclusion[c]|,
which in the original is a single proposition, becomes a list---that is the
change to step C1---and step C5 then deduces every proposition on the list.
Variables that are |prohibited| enter the core at the start; the answer's
last remark needs that. |reason[v]| records the clause that put $v$ into the
core, or $-1$ for a prohibited variable. |steps| counts one for each literal
looked at in C1, each hypothesis in C4, and each conclusion in C5.
@<Functions@>=
func core(f fam, prohibited []bool) (truth []bool, reason []int, steps int) {
	@<Set up the data structures of Algorithm C@>
	@<Do step C1, with several conclusions per clause@>
	for len(stack) > 0 {
		@<Do steps C2 through C6 for the proposition on top of the stack@>
	}
	return truth, reason, steps
}

@ @<Set up the data structures...@>=
truth, reason = make([]bool, f.n+1), make([]int, f.n+1)
last := make([]int, f.n+1)
for v := range last {
	last[v], reason[v] = -1, -2
}
conclusion, count := make([][]int, len(f.cl)), make([]int, len(f.cl))
var hclause, hprev, stack []int
for v := 1; v <= f.n; v++ {
	if prohibited != nil && prohibited[v] {
		truth[v], reason[v], stack = true, -1, append(stack, v)
	}
}

@ @<Do step C1...@>=
for c, cl := range f.cl {
	for _, l := range cl {
		steps++
		if l&1 == 1 {
			conclusion[c] = append(conclusion[c], l>>1)
		} else {
			count[c]++
		}
	}
	if count[c] == 0 {
		for _, v := range conclusion[c] {
			if !truth[v] {
				truth[v], reason[v], stack = true, c, append(stack, v)
			}
		}
		continue
	}
	for _, l := range cl {
		if l&1 == 0 {
			hclause, hprev = append(hclause, c), append(hprev, last[l>>1])
			last[l>>1] = len(hclause) - 1
		}
	}
}

@ @<Do steps C2 through C6...@>=
p := stack[len(stack)-1]
stack = stack[:len(stack)-1]
for h := last[p]; h >= 0; h = hprev[h] {
	steps++
	c := hclause[h]
	if count[c]--; count[c] != 0 {
		continue
	}
	for _, v := range conclusion[c] {
		steps++
		if !truth[v] {
			truth[v], reason[v], stack = true, c, append(stack, v)
		}
	}
}

@ The largest positive autarky is what the core leaves out.
@<Functions@>=
func largest(f fam) uint64 {
	truth, _, _ := core(f, nil)
	var a uint64
	for v := 1; v <= f.n && v < 64; v++ {
		if !truth[v] {
			a |= 1 << v
		}
	}
	return a
}

@* The warm-up.
@<Check the warm-up example@>=
fmt.Println("165. the warm-up")
w := parseFam(6, "123' 125' 1'3'4' 136' 14'5 156 2'35 24'6 345 3'56")
best, union, count, unionOK := bruteMax(w)
claim(best == 1<<2|1<<5 && union == best && unionOK,
	"by brute force: %d positive autarkies, and the largest is {2,5}", count)
truth, reason, _ := core(w, nil)
@<Replay the answer's deductions@>
claim(largest(w) == best, "the core algorithm finds {2,5} too")
@<Check the example in answer 157@>

@ The answer's reasons are specific: 1, 3, and 4 because of $\bar1\bar3\bar4$,
and 6 because of $13\bar6$. The core algorithm records a reason for every
variable it excludes, so the program asks whether they are those.
@<Replay the answer's deductions@>=
var why []string
for v := 1; v <= 6; v++ {
	if truth[v] {
		why = append(why, fmt.Sprintf("%d by %s", v, clauseName(w.cl[reason[v]])))
	}
}
claim(strings.Join(why, ", ") == "1 by 1'3'4', 3 by 1'3'4', 4 by 1'3'4', 6 by 136'",
	"excluded: %s", strings.Join(why, ", "))

@ Answer 157 gives $\{1,2\}$ as an autarky of $\{1\bar23,\bar124,\bar3\bar4\}$
that is not a pure literal. It is positive, and it is the largest: $\bar3\bar4$
has no positive literal, so 3 and 4 are out.
@<Check the example in answer 157@>=
e157 := parseFam(4, "12'3 1'24 3'4'")
b157, _, _, _ := bruteMax(e157)
claim(b157 == 1<<1|1<<2 && largest(e157) == b157,
	"answer 157's autarky {1,2} is the largest positive one of its clauses")

@* Unions.
The answer's argument for a maximum is that the union of positive autarkies is
a positive autarky. Checked on every family of at most five clauses on three
variables, and on random families of up to ten variables.

The word {\it positive\/} matters. For general autarkies the union may not
even be a set of strictly distinct literals: $F=\{12,\bar1\bar2\}$ has the two
autarkies $\{1,\bar2\}$ and $\{\bar1,2\}$, each of them maximal, and no
maximum.
@<Check that positive autarkies are closed under union@>=
fmt.Println("165. unions of positive autarkies")
var nu, badU int
test := func(f fam) {
	nu++
	if best, union, _, ok := bruteMax(f); !ok || best != union {
		badU++
	}
}
everyFamily(3, 5, test)
sweep(10, reps/10, test)
claim(badU == 0, "%d families, %d where the union fails", nu, badU)
@<Show that general autarkies have no maximum@>

@ Brute force over all $3^n$ sets of strictly distinct literals.
@<Show that general autarkies have no maximum@>=
g := parseFam(2, "12 1'2'")
var maximal []string
for a := 0; a < 9; a++ {
	in := make([]bool, 6)
	for v := 1; v <= 2; v++ {
		if d := a / []int{1, 3}[v-1] % 3; d > 0 {
			in[2*v+d-1] = true
		}
	}
	if isAutarky(g, in) && (in[2] || in[3]) && (in[4] || in[5]) {
		maximal = append(maximal, fmt.Sprint(in[2:]))
	}
}
claim(len(maximal) == 2, "{12, 1'2'} has two maximal autarkies and no maximum")

@* The core against brute force.
@<Check the core algorithm against brute force@>=
fmt.Println("165. the core algorithm")
var nc, badC, badSteps int
cmp := func(f fam) {
	nc++
	best, _, _, _ := bruteMax(f)
	if largest(f) != best {
		badC++
	}
	@<Check that the work is at most twice the total length@>
}
everyFamily(3, 5, cmp)
sweep(12, reps/10, cmp)
claim(badC == 0, "%d families: the core misses the largest positive autarky "+
	"%d times", nc, badC)
claim(badSteps == 0, "steps never exceed twice the number of literals: "+
	"%d exceptions", badSteps)

@ Every literal is looked at once in C1. A proposition is pushed at most once,
so each hypothesis is looked at most once in C4, and a clause's count reaches
zero at most once, so each conclusion is looked at most once in C5. Hence the
steps are at most $2N$, where $N$ is the total length of the clauses.
@<Check that the work is at most twice the total length@>=
_, _, steps := core(f, nil)
total := 0
for _, c := range f.cl {
	total += len(c)
}
if steps > 2*total {
	badSteps++
}

@* Linear time.
The point of changing steps C1 and C5, rather than simply writing out the $t$
Horn clauses, shows up on long clauses. Take $2k$ variables, the one clause
$(k+1\lor\cdots\lor2k\lor\bar1\lor\cdots\lor\bar k)$, and the $k$ unit clauses
$\overline{k+1}$, \dots, $\overline{2k}$. The clause of length $2k$ becomes $k$
Horn clauses with $k$ hypotheses each, so writing them out costs $k^2$; the
modified algorithm touches each literal a bounded number of times.
@<Measure the running time of the core algorithm@>=
fmt.Println("165. linear time")
var lastVariant, lastExpanded, lastN int
for k := 10; k <= 160; k *= 2 {
	f := wide(k)
	_, _, s1 := core(f, nil)
	_, _, s2 := core(expand(f), nil)
	lastVariant, lastExpanded, lastN = s1, s2, 3*k
	fmt.Printf("        k=%3d: N=%4d, %5d steps modified, %6d written out\n",
		k, 3*k, s1, s2)
}
claim(lastVariant <= 2*lastN && lastExpanded > 50*lastN,
	"the modified algorithm stays within 2N; writing the clauses out does not")

@ @<Functions@>=
func wide(k int) fam {
	f := fam{n: 2 * k}
	var big []int
	for v := k + 1; v <= 2*k; v++ {
		big = append(big, 2*v)
		f.cl = append(f.cl, []int{2*v + 1})
	}
	for v := 1; v <= k; v++ {
		big = append(big, 2*v+1)
	}
	f.cl = append(f.cl, big)
	return f
}

@ Writing out the Horn clauses: one clause per negative literal, keeping all
the positive ones. Each has a single conclusion, so on these the modified
algorithm is Algorithm 7.1.1C itself.
@<Functions@>=
func expand(f fam) fam {
	g := fam{n: f.n}
	for _, c := range f.cl {
		var pos []int
		for _, l := range c {
			if l&1 == 0 {
				pos = append(pos, l)
			}
		}
		for _, l := range c {
			if l&1 == 1 {
				g.cl = append(g.cl, append(append([]int{}, pos...), l))
			}
		}
		if len(pos) == len(c) {
			g.cl = append(g.cl, pos)
		}
	}
	return g
}

@* Autarkies inside a given set.
The answer's last remark: complement the variables that appear negatively in
a given set $S$ of strictly distinct literals, prohibit the variables that do
not appear in $S$ at all, and the core algorithm finds the largest autarky
contained in $S$.
@<Functions@>=
func within(f fam, S []int) []int {
	flip, prohibited := make([]bool, f.n+1), make([]bool, f.n+1)
	for v := range prohibited {
		prohibited[v] = true
	}
	for _, l := range S {
		prohibited[l>>1], flip[l>>1] = false, l&1 == 1
	}
	g := fam{n: f.n}
	for _, c := range f.cl {
		d := make([]int, len(c))
		for i, l := range c {
			if d[i] = l; flip[l>>1] {
				d[i] = l ^ 1
			}
		}
		g.cl = append(g.cl, d)
	}
	truth, _, _ := core(g, prohibited)
	var a []int
	for _, l := range S {
		if !truth[l>>1] {
			a = append(a, l)
		}
	}
	return a
}

@ Brute force tries every subset of $S$.
@<Check the bracketed remark@>=
fmt.Println("165. the largest autarky inside a given set of literals")
var nw, badW int
rw := rand.New(rand.NewPCG(seed, 165))
sweep(9, reps/5, func(f fam) {
	var S []int
	for v := 1; v <= f.n; v++ {
		if r := rw.IntN(3); r > 0 {
			S = append(S, 2*v+r-1)
		}
	}
	nw++
	@<Compare |within| with the best subset of |S|@>
})
claim(badW == 0, "%d families with random sets S, %d disagreements", nw, badW)

@ @<Compare |within| with the best subset of |S|@>=
bestSize, unionIn := -1, make([]bool, 2*f.n+2)
for sub := 0; sub < 1<<len(S); sub++ {
	in := make([]bool, 2*f.n+2)
	for i, l := range S {
		in[l] = sub&(1<<i) != 0
	}
	if isAutarky(f, in) {
		bestSize = max(bestSize, bits.OnesCount(uint(sub)))
		for l := range in {
			unionIn[l] = unionIn[l] || in[l]
		}
	}
}
got := within(f, S)
gotIn := make([]bool, 2*f.n+2)
for _, l := range got {
	gotIn[l] = true
}
if len(got) != bestSize || !isAutarky(f, gotIn) || fmt.Sprint(gotIn) != fmt.Sprint(unionIn) {
	badW++
}

@* The {\tt sat} package.
Brute force stops at a dozen variables. For larger problems the program plants
a positive autarky $H$ in a random 3SAT problem---it draws clauses at random
and throws away those that $H$ touches without satisfying---and then asks two
questions of the solver.

First, is the result of the core algorithm really the largest? Introduce a
variable $a_v$ for each $v$, meaning $v\in A$, and for each clause of $F$ and
each negative literal $\bar w$ in it, the clause
$(\bar a_w\lor a_{v_1}\lor\cdots\lor a_{v_s})$. The satisfying assignments of
these clauses are exactly the positive autarkies, so a positive autarky
containing $v$ exists if and only if they are satisfiable under the assumption
$a_v$. That is a different computation from the core---a search rather than a
propagation---though the clauses are dual Horn and the solver never has to
work hard. Each model it returns is checked against the definition as well.

Second, the autarky principle. If $A$ is an autarky, $F$ is satisfiable if
and only if the clauses that $A$ does not touch are satisfiable; and a model
of those, with the literals of $A$ made true, satisfies $F$. The solver is
asked both questions and the model is checked.
@<Check large problems with the {\tt sat} package@>=
fmt.Println("165. larger problems, with the sat package")
var np, calls, badMax, badModel, badPlant, badPrinciple, badExtend, sats, unsats int
var badDef, sizeH, sizeA int
rp := rand.New(rand.NewPCG(seed, 228))
for i := 0; i < reps/40; i++ {
	n := 60 + rp.IntN(80)
	f, H := planted(rp, n)
	np++
	truth, _, _ := core(f, nil)
	@<Check the answer against the definition, and measure it@>
	@<Check that |H| lies inside the largest positive autarky@>
	@<Ask the solver whether each variable can be in a positive autarky@>
	@<Test the autarky principle with the solver@>
}
claim(badDef == 0, "%d problems with 60 to 139 variables: every result is "+
	"a positive autarky by the definition", np)
claim(badPlant == 0, "the planted autarkies (%d variables in all) always lie "+
	"inside the ones found (%d)", sizeH, sizeA)
claim(badMax == 0 && badModel == 0, "%d calls with assumptions agree with the "+
	"core, and every model is a positive autarky", calls)
claim(badPrinciple == 0 && badExtend == 0 && sats > 0 && unsats > 0,
	"the autarky principle holds: %d satisfiable, %d unsatisfiable, "+
		"every extended model satisfies F", sats, unsats)

@ @<Functions@>=
func planted(rng *rand.Rand, n int) (fam, []bool) {
	H := make([]bool, n+1)
	for v := 1; v <= n; v++ {
		H[v] = rng.IntN(10) < 3
	}
	f := fam{n: n}
	for len(f.cl) < 6*n {
		c := randClause(rng, n, 3)
		touched, satisfied := false, false
		for _, l := range c {
			touched = touched || H[l>>1]
			satisfied = satisfied || (H[l>>1] && l&1 == 0)
		}
		if !touched || satisfied {
			f.cl = append(f.cl, c)
		}
	}
	return f, H
}

@ @<Check the answer against the definition, and measure it@>=
inA := make([]bool, 2*n+2)
for v := 1; v <= n; v++ {
	if inA[2*v] = !truth[v]; !truth[v] {
		sizeA++
	}
	if H[v] {
		sizeH++
	}
}
if !isAutarky(f, inA) {
	badDef++
}

@ @<Check that |H| lies inside...@>=
for v := 1; v <= n; v++ {
	if H[v] && truth[v] {
		badPlant++
		break
	}
}

@ @<Ask the solver whether each variable...@>=
s := sat.New()
for v := 1; v <= n; v++ {
	s.Lookup(strconv.Itoa(v))
}
for _, c := range f.cl {
	var pos []sat.Lit
	for _, l := range c {
		if l&1 == 0 {
			pos = append(pos, sat.Lit(l))
		}
	}
	for _, l := range c {
		if l&1 == 1 {
			s.AddClause(append([]sat.Lit{sat.Lit(l)}, pos...)...)
		}
	}
}
for v := 1; v <= n; v++ {
	st, _ := s.Solve(context.Background(), sat.Lit(2*v))
	calls++
	if (st == sat.Sat) == truth[v] {
		badMax++
	}
	if st == sat.Sat {
		@<Check that the model is a positive autarky@>
	}
}

@ In this solver the literal $2v$ stands for $a_v$, so $\bar w\lor\cdots$ is
written with the literal $2w+1$.
@<Check that the model is a positive autarky@>=
in := make([]bool, 2*n+2)
for u := 1; u <= n; u++ {
	in[2*u] = s.Value(sat.Lit(2 * u))
}
if !isAutarky(f, in) {
	badModel++
}

@ @<Test the autarky principle...@>=
whole, rest := sat.New(), sat.New()
for v := 1; v <= n; v++ {
	whole.Lookup(strconv.Itoa(v))
	rest.Lookup(strconv.Itoa(v))
}
for _, c := range f.cl {
	ls, touched := make([]sat.Lit, len(c)), false
	for i, l := range c {
		ls[i], touched = sat.Lit(l), touched || !truth[l>>1]
	}
	whole.AddClause(ls...)
	if !touched {
		rest.AddClause(ls...)
	}
}
st1, _ := whole.Solve(context.Background())
st2, _ := rest.Solve(context.Background())
if st1 != st2 {
	badPrinciple++
}
if st2 == sat.Sat {
	sats++
	@<Extend the model of the untouched clauses and check it@>
} else {
	unsats++
}

@ @<Extend the model...@>=
for _, c := range f.cl {
	ok := false
	for _, l := range c {
		v := l >> 1
		val := !truth[v] || rest.Value(sat.Lit(2*v))
		ok = ok || (val == (l&1 == 0))
	}
	if !ok {
		badExtend++
		break
	}
}

@* Random families.
|sweep| draws random families on $1,\ldots,$|maxN| variables; |everyFamily|
produces every family of at most |max| clauses on $n$ variables, from the $3^n$
possible clauses, the empty one included.
@<Functions@>=
func randClause(rng *rand.Rand, n, k int) []int {
	var c []int
	used := map[int]bool{}
	for len(c) < k && len(c) < n {
		if v := 1 + rng.IntN(n); !used[v] {
			used[v], c = true, append(c, 2*v+rng.IntN(2))
		}
	}
	return c
}

func sweep(maxN, count int, do func(fam)) {
	for n := 1; n <= maxN; n++ {
		rng := rand.New(rand.NewPCG(seed, uint64(n)))
		for i := 0; i < count; i++ {
			f := fam{n: n}
			for j, m := 0, 1+rng.IntN(3*n); j < m; j++ {
				f.cl = append(f.cl, randClause(rng, n, 1+rng.IntN(4)))
			}
			do(f)
		}
	}
}

func everyFamily(n, max int, do func(fam)) {
	cands := [][]int{nil}
	for v := 1; v <= n; v++ {
		var next [][]int
		for _, c := range cands {
			next = append(next, c, append(append([]int{}, c...), 2*v),
				append(append([]int{}, c...), 2*v+1))
		}
		cands = next
	}
	var rec func(start int, cl [][]int)
	rec = func(start int, cl [][]int) {
		if len(cl) > 0 {
			do(fam{n: n, cl: cl})
		}
		if len(cl) == max {
			return
		}
		for i := start; i < len(cands); i++ {
			rec(i+1, append(append([][]int{}, cl...), cands[i]))
		}
	}
	rec(0, nil)
}

@* Index.
