\datethis
\def\title{Stable partial assignments}

@s sat.Lit int
@s sat.Status int
@s sat.Solver int
@s fam int
@s ctx int
@s term int

@* Introduction.
A partial assignment is {\it stable\/} (or ``valid'') if it is consistent and
unit propagation cannot extend it. Exercise 7.2.2.2--363 gives the stable
partial assignments of a problem a weight, shows that they form a lattice, and
asks ten questions about them. Its neighbor, exercise 364, sits on top of the
same notion: a {\it covering\/} assignment is a stable one in which every
assigned variable is constrained.

Two definitions do all the work, and both are quoted here as the exercise
states them. A partial assignment is stable ``if and only if no clause is
entirely false, or entirely false except for at most one unassigned literal.''
And ``variable $x_k$ of a partial assignment is called {\it constrained\/} if it
appears in a clause where $\pm x_k$ is true but all the other literals are
false (thus its value has a `reason').''

@ Writing $x\prec x'$ when $x'$ agrees with $x$ except that $x_k=*$ and
$x'_k\in\{0,1\}$, the exercise defines
$$x\sqsubseteq x'\quad\hbox{if}\quad x=x^{(0)}\prec x^{(1)}\prec\cdots\prec
  x^{(t)}=x'\ \hbox{for some $t\ge0$},$$
where every $x^{(j)}$ is stable. Then, given probabilities $p_k+q_k=1$, the
weight of an unstable assignment is 0 and otherwise
$$W(x)=\prod\{p_k\mid x_k=*\}\cdot
       \prod\{q_k\mid x_k\ne*\ \hbox{and $x_k$ is unconstrained}\}.$$

Everything here is finite and small: a problem on $n$ variables has $3^n$
partial assignments, and the parts of the exercise ask about problems with
three, four, or five of them. So this program tabulates all $3^n$ assignments,
decides stability and constrainedness from the definitions, and answers each
part by looking.

@ Part~(a) is the exception. It asks whether the literals on Algorithm C's
trail, at the moment step C5 chooses a new decision, always form a stable
partial assignment---a question about a real solver, not about a table. The
{\tt sat} package of the directory above is a Go rendering of Knuth's
{\tt SAT13}, and it had no way to show its trail: the port deliberately leaves
out the diagnostics that {\tt SAT13} turns on with its \.v option, and
{\tt SAT13}'s own |sanity| routine, thorough as it is about |tloc| and
|reason| and |value|, never looks at this. So the package grew a |SetTrace|
hook while this reading was being written. It hands over the trail just before
each decision and costs nothing when it isn't used, exactly as |SetProof| does.

Weights are kept as products of symbols rather than as numbers, so that the
program's answer to part~(e) can be compared with the book's table entry by
entry. Only part~(j), which is an identity about sums, needs arithmetic.

I wrote this on 16 September 2026.

@ Every part is a mode.
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
	if on("trail") {
		@<Check part (a) against Algorithm C@>
	}
	if on("weights") {
		@<Check parts (b) and (e)@>
	}
	if on("stable") {
		@<Check part (c)@>
	}
	if on("climb") {
		@<Check parts (d) and (f)@>
	}
	if on("lattice") {
		@<Check parts (h) and (i), and the lattice of part (d)@>
	}
	if on("sum") {
		@<Check the identity of part (j)@>
	}
	if on("horn") {
		@<Check the construction of part (g)@>
	}
	@<Say how it went@>
}

@ @<Read the command line@>=
flag.StringVar(&mode, "mode", "all",
	"trail, weights, stable, climb, lattice, sum, horn, or all")
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

@ Each claim is announced, checked, and marked, and one \.{FAIL} anywhere makes
the program exit with a nonzero status.
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

@* Clauses and partial assignments.
The literal for variable $v$ is $2v$ when positive and $2v+1$ when negative, as
Knuth numbers them; a clause is a bitmask over literals and a family is a list
of clauses. The notation is his too: `$12\bar3$' is the clause
$(x_1\lor x_2\lor\bar x_3)$, which |parseFam| reads as \.{123'}.

@<Types@>=
type fam struct {
	n  int
	cl []uint32
}

@ @<Functions@>=
func lit(v int, positive bool) int {
	if positive {
		return 2 * v
	}
	return 2*v + 1
}

func parseFam(n int, s string) fam {
	f := fam{n: n}
	for _, w := range strings.Fields(s) {
		var c uint32
		for i := 0; i < len(w); i++ {
			v := int(w[i] - '0')
			positive := true
			if i+1 < len(w) && w[i+1] == '\'' {
				positive, i = false, i+1
			}
			c |= 1 << lit(v, positive)
		}
		f.cl = append(f.cl, c)
	}
	return f
}

@ A partial assignment is written in base three, digit $v-1$ saying whether
variable $v$ is unassigned, true, or false. The program tabulates, for every
one of the $3^n$ of them, which literals it makes true, which false, which are
still free, whether it is stable, and which variables it constrains.

@<Types@>=
type ctx struct {
	f     fam
	n, nA int
	pow3  []int

	tmask []uint32 // the literals made true
	fmask []uint32 // the literals made false
	free  []uint32 // the literals on unassigned variables

	isStable []bool
	cons     []uint32 // bit $v$: the assignment constrains variable $v$
}

@ @<Functions@>=
func newCtx(f fam) *ctx {
	c := &ctx{f: f, n: f.n}
	@<Set up the powers of three@>
	@<Tabulate the masks@>
	@<Decide stability and constrainedness@>
	return c
}

func (c *ctx) digit(a, v int) int { return (a / c.pow3[v-1]) % 3 }

@ @<Set up the powers of three@>=
c.pow3 = make([]int, c.n+1)
c.pow3[0] = 1
for i := 1; i <= c.n; i++ {
	c.pow3[i] = 3 * c.pow3[i-1]
}
c.nA = c.pow3[c.n]

@ @<Tabulate the masks@>=
c.tmask = make([]uint32, c.nA)
c.fmask = make([]uint32, c.nA)
c.free = make([]uint32, c.nA)
c.isStable = make([]bool, c.nA)
c.cons = make([]uint32, c.nA)
for a := 0; a < c.nA; a++ {
	for v := 1; v <= c.n; v++ {
		switch c.digit(a, v) {
		case 0:
			c.free[a] |= 1<<lit(v, true) | 1<<lit(v, false)
		case 1:
			c.tmask[a] |= 1 << lit(v, true)
			c.fmask[a] |= 1 << lit(v, false)
		case 2:
			c.tmask[a] |= 1 << lit(v, false)
			c.fmask[a] |= 1 << lit(v, true)
		}
	}
}

@ Straight from the two definitions. A clause that is still unsatisfied leaves
the assignment stable only if two or more of its literals are unassigned; a
clause that is satisfied by exactly one of its literals, all the others being
false, constrains that literal's variable.
@<Decide stability and constrainedness@>=
for a := 0; a < c.nA; a++ {
	c.isStable[a] = true
	for _, cl := range c.f.cl {
		if t := cl & c.tmask[a]; t != 0 {
			if bits.OnesCount32(t) == 1 && cl&^(c.fmask[a]|t) == 0 {
				c.cons[a] |= 1 << uint(bits.TrailingZeros32(t)>>1)
			}
		} else if bits.OnesCount32(cl&^c.fmask[a]) <= 1 {
			c.isStable[a] = false
		}
	}
}

@ Two conveniences: |assign| sets the variable of a literal so that the literal
becomes true, and |code| reads an assignment written as a string like \.{10*}.
@<Functions@>=
func (c *ctx) assign(a, l int) int {
	v := l >> 1
	if c.digit(a, v) != 0 {
		return -1
	}
	if l&1 == 0 {
		return a + c.pow3[v-1]
	}
	return a + 2*c.pow3[v-1]
}

func (c *ctx) code(s string) int {
	a := 0
	for i := 0; i < len(s) && i < c.n; i++ {
		switch s[i] {
		case '1':
			a += c.pow3[i]
		case '0':
			a += 2 * c.pow3[i]
		}
	}
	return a
}

@* Weights.
A weight is a product of $p$'s and $q$'s, so the program keeps it as two
bitmasks and prints it the way the book does: |p| for the unassigned variables,
|q| for the assigned ones that are unconstrained, in order of the variables,
with the empty product printed as~1.

@<Types@>=
type term struct {
	p, q uint32
	zero bool
}

@ @<Functions@>=
func (c *ctx) weight(a int) term {
	if !c.isStable[a] {
		return term{zero: true}
	}
	var t term
	for v := 1; v <= c.n; v++ {
		switch {
		case c.digit(a, v) == 0:
			t.p |= 1 << v
		case c.cons[a]&(1<<v) == 0:
			t.q |= 1 << v
		}
	}
	return t
}

func (t term) String() string {
	if t.zero {
		return "0"
	}
	var b strings.Builder
	for v := 1; v < 32; v++ {
		if t.p&(1<<v) != 0 {
			b.WriteString("p" + strconv.Itoa(v))
		}
		if t.q&(1<<v) != 0 {
			b.WriteString("q" + strconv.Itoa(v))
		}
	}
	if b.Len() == 0 {
		return "1"
	}
	return b.String()
}

@ Part~(b) asks for the weights of the clauses $F$ of 7.2.2.2--(1), which are
$\{1\bar2,23,\bar1\bar3,\bar1\bar23\}$. The answer says $W(001)=1$,
$W(***)=p_1p_2p_3$, and $W(x)=0$ otherwise---so all three variables are
constrained in the one solution, and the empty assignment is the only other
stable one.
@<Check parts (b) and (e)@>=
fmt.Println("363(b). the weights of the clauses F of (1)")
b := newCtx(parseFam(3, "12' 23 1'3' 1'2'3"))
ok := b.weight(b.code("001")).String() == "1" &&
	b.weight(b.code("***")).String() == "p1p2p3"
for a := 0; a < b.nA; a++ {
	if a != b.code("001") && a != b.code("***") && !b.weight(a).zero {
		ok = false
	}
}
claim(ok, "W(001) = 1, W(***) = p1p2p3, and every other weight is 0")
@<Check the table of part (e)@>

@ Part~(e) asks for the weights when the only clause is $123$. The answer gives
them as a table with a row for each value of $x_1$ and a column for each value
of $x_2x_3$, and here it is, copied from page 619.
@<Global variables@>=
var (
	cols = [9]string{"00", "01", "0*", "10", "11", "1*", "*0", "*1", "**"}
	rows = [3]string{"0", "1", "*"}
	book = [3][9]string{
		{"0", "q1q2", "0", "q1q3", "q1q2q3", "q1q2p3", "0", "q1p2q3", "q1p2p3"},
		{"q2q3", "q1q2q3", "q1q2p3", "q1q2q3", "q1q2q3", "q1q2p3",
			"q1p2q3", "q1p2q3", "q1p2p3"},
		{"0", "p1q2q3", "p1q2p3", "p1q2q3", "p1q2q3", "p1q2p3",
			"p1p2q3", "p1p2q3", "p1p2p3"},
	}
)

@ @<Check the table of part (e)@>=
fmt.Println("363(e). the weights when the only clause is 123")
e := newCtx(parseFam(3, "123"))
bad := 0
for i, r := range rows {
	line := "        x1 = " + r + ":"
	for j, col := range cols {
		got := e.weight(e.code(r + col)).String()
		if got != book[i][j] {
			bad++
			got += "(book " + book[i][j] + ")"
		}
		line += fmt.Sprintf(" %8s", got)
	}
	fmt.Println(line)
}
claim(bad == 0, "all 27 weights agree with the table on page 619")

@* Stability, one variable at a time.
Part~(c) takes a stable $x$ with $x_k=1$ and forms $x'$ by setting
$x_k\gets0$ and $x''$ by setting $x_k\gets*$. It then asks whether ``$x_k$ is
unconstrained in $x$'' is the same as (i) $x'$ is consistent; (ii) $x'$ is
stable; (iii) $x''$ is stable. The answer: (i) and (iii) yes, (ii) no, and the
counterexample offered is $x=10*$ with $x'=00*$, against the clause 123.

Consistency is the first half of stability---no clause entirely false---so the
program needs it separately.
@<Functions@>=
func (c *ctx) consistent(a int) bool {
	for _, cl := range c.f.cl {
		if cl&c.tmask[a] == 0 && cl&^c.fmask[a] == 0 {
			return false
		}
	}
	return true
}

@ @<Check part (c)@>=
fmt.Println("363(c). complementing or erasing one value")
var n3, bad1, bad2, bad3 int
sweep(4, reps, func(c *ctx) {
	for a := 0; a < c.nA; a++ {
		for v := 1; v <= c.n; v++ {
			if !c.isStable[a] || c.digit(a, v) != 1 {
				continue
			}
			n3++
			@<Compare the three statements with unconstrainedness@>
		}
	}
})
claim(bad1 == 0, "(i) x' is consistent: %d cases, %d exceptions", n3, bad1)
claim(bad3 == 0, "(iii) x'' is stable: %d exceptions", bad3)
claim(bad2 > 0, "(ii) x' is stable: false, %d exceptions", bad2)
@<Check the counterexample the answer gives@>

@ @<Compare the three statements with unconstrainedness@>=
free := c.cons[a]&(1<<v) == 0
xp := a - c.pow3[v-1] + 2*c.pow3[v-1]
xpp := a - c.pow3[v-1]
if free != c.consistent(xp) {
	bad1++
}
if free != c.isStable[xp] {
	bad2++
}
if free != c.isStable[xpp] {
	bad3++
}

@ @<Check the counterexample the answer gives@>=
one := newCtx(parseFam(3, "123"))
x, xp := one.code("10*"), one.code("00*")
claim(one.isStable[x] && one.cons[x]&(1<<1) == 0 && one.consistent(xp) &&
	!one.isStable[xp], "     and x = 10*, x' = 00* with the clause 123 is one")

@* Climbing.
The relation $x\sqsubseteq x'$ asks for a chain of stable assignments from $x$
up to $x'$, one literal at a time. Since every step adds a literal, the
assignments $x$ with $x\sqsubseteq x'$ are found by walking down from $x'$,
removing one literal at a time and never leaving stability.
@<Functions@>=
func (c *ctx) below(a int) []bool {
	seen := make([]bool, c.nA)
	if !c.isStable[a] {
		return seen
	}
	seen[a] = true
	for queue := []int{a}; len(queue) > 0; {
		b := queue[len(queue)-1]
		queue = queue[:len(queue)-1]
		for v := 1; v <= c.n; v++ {
			if d := c.digit(b, v); d != 0 {
				e := b - d*c.pow3[v-1]
				if c.isStable[e] && !seen[e] {
					seen[e], queue = true, append(queue, e)
				}
			}
		}
	}
	return seen
}

@ It is convenient to name an assignment by the set of literals it holds, the
way the exercise does.
@<Functions@>=
func (c *ctx) name(a int) string {
	var b strings.Builder
	for v := 1; v <= c.n; v++ {
		if d := c.digit(a, v); d != 0 {
			if b.Len() > 0 {
				b.WriteByte(',')
			}
			b.WriteString(strconv.Itoa(v))
			if d == 2 {
				b.WriteByte('\'')
			}
		}
	}
	return "{" + b.String() + "}"
}

@ Part~(d) asks for all $L$ with $L\sqsubseteq\{1,\bar2,\bar3\}$ when the only
clause is 123. The answer: all eight subsets of $\{1,\bar2,\bar3\}$ are stable
except $\{\bar2,\bar3\}$, where $x_1$ is constrained, so seven remain.
@<Check parts (d) and (f)@>=
fmt.Println("363(d). climbing to {1,2',3'} with the single clause 123")
d := newCtx(parseFam(3, "123"))
target := d.code("100")
seen, got := d.below(target), 0
for a := 0; a < d.nA; a++ {
	if seen[a] {
		got++
	}
}
claim(got == 7 && !d.isStable[d.code("*00")],
	"seven of the eight subsets, all but {2',3'}, which is not stable")
@<Check the twelve sets of part (f)@>

@ Part~(f) wants clauses whose $L\sqsubseteq\{1,2,3,4,5\}$ are twelve given
sets. The answer offers $\{\bar1\bar23\bar4\bar5,\bar14,\bar25,\bar34\bar5,
\bar3\bar45\}$, and adds that $\{3\}$ is stable but unreachable below
$\{1,2,3,4,5\}$.
@<Global variables@>=
var twelve = []string{"", "4", "5", "14", "25", "45", "145", "245", "345",
	"1345", "2345", "12345"}

@ @<Check the twelve sets of part (f)@>=
fmt.Println("363(f). twelve sets below {1,2,3,4,5}")
f := newCtx(parseFam(5, "1'2'34'5' 1'4 2'5 3'45' 3'4'5"))
want := make([]bool, f.nA)
for _, s := range twelve {
	want[setCode(f, s)] = true
}
below := f.below(setCode(f, "12345"))
diff := 0
for a := 0; a < f.nA; a++ {
	if below[a] != want[a] {
		diff++
	}
}
claim(diff == 0, "the answer's clauses give exactly the twelve sets asked for")
claim(f.isStable[setCode(f, "3")] && !below[setCode(f, "3")],
	"     and {3} is stable but unreachable, as the answer remarks")

@ @<Functions@>=
func setCode(c *ctx, s string) int {
	a := 0
	for i := 0; i < len(s); i++ {
		a = c.assign(a, lit(int(s[i]-'0'), true))
	}
	return a
}

@* The lattice.
Part~(h) says that if $L$, $L'$, $L''$ are stable with $L'\prec L$ and
$L''\prec L$, then $L'\cap L''$ is stable; part~(i) says that
$L'\sqsubseteq L$ and $L''\sqsubseteq L$ imply
$L'\cap L''\sqsubseteq L$. Intersecting two assignments means keeping the
values they agree on, which in base three is done digit by digit.
@<Functions@>=
func (c *ctx) meet(a, b int) int {
	m := 0
	for v := 1; v <= c.n; v++ {
		if d := c.digit(a, v); d == c.digit(b, v) {
			m += d * c.pow3[v-1]
		}
	}
	return m
}

@ @<Check parts (h) and (i), and the lattice of part (d)@>=
fmt.Println("363(h,i). intersections of stable assignments")
var nh, badH, badI int
sweep(4, reps, func(c *ctx) {
	for a := 0; a < c.nA; a++ {
		if !c.isStable[a] {
			continue
		}
		@<Check part (h) at |a|@>
	}
})
sweep(4, reps/50, func(c *ctx) {
	@<Check part (i) at every target@>
})
claim(badH == 0, "(h) holds: %d pairs one step below a stable L, %d exceptions",
	nh, badH)
claim(badI == 0, "(i) holds: %d exceptions", badI)
@<Look at the lattice that part (d) mentions@>

@ @<Check part (h) at |a|@>=
for v := 1; v <= c.n; v++ {
	for w := v + 1; w <= c.n; w++ {
		dv, dw := c.digit(a, v), c.digit(a, w)
		if dv == 0 || dw == 0 {
			continue
		}
		lp, lpp := a-dv*c.pow3[v-1], a-dw*c.pow3[w-1]
		if !c.isStable[lp] || !c.isStable[lpp] {
			continue
		}
		nh++
		if !c.isStable[c.meet(lp, lpp)] {
			badH++
		}
	}
}

@ @<Check part (i) at every target@>=
for a := 0; a < c.nA; a++ {
	if !c.isStable[a] {
		continue
	}
	seen := c.below(a)
	for x := 0; x < c.nA; x++ {
		if !seen[x] {
			continue
		}
		for y := x + 1; y < c.nA; y++ {
			if seen[y] && !seen[c.meet(x, y)] {
				badI++
			}
		}
	}
}

@ The seven sets of part~(d), ordered by inclusion, are said to illustrate
$L_7$, ``the smallest lattice that is lower semimodular but not modular.'' The
program collects them and checks all three words.
@<Look at the lattice that part (d) mentions@>=
fmt.Println("363(d). the shape of those seven sets")
l7 := newCtx(parseFam(3, "123"))
var elems []int
for a, in := range l7.below(l7.code("100")) {
	if in {
		elems = append(elems, a)
	}
}
@<Decide whether the elements form a lattice@>
claim(len(elems) == 7 && isLattice, "the seven sets form a lattice")
claim(lowerSemi && !modular, "it is lower semimodular but not modular")

@ Within this family the meet is the intersection and the join is the smallest
member containing both, when there is one. The order is inclusion of the
literal sets, which for these all-assigned-or-unassigned members is just
|meet(a,b)==a|.
@<Decide whether the elements form a lattice@>=
isLattice, lowerSemi, modular := true, true, true
join := map[[2]int]int{}
for _, a := range elems {
	for _, b := range elems {
		@<Find the join of |a| and |b|@>
	}
}
if isLattice {
	@<Test lower semimodularity and modularity@>
}

@ @<Find the join of |a| and |b|@>=
best := -1
for _, u := range elems {
	if l7.meet(u, a) == a && l7.meet(u, b) == b {
		if best < 0 || l7.meet(best, u) == u {
			best = u
		}
	}
}
if best < 0 {
	isLattice = false
} else {
	for _, u := range elems {
		if l7.meet(u, a) == a && l7.meet(u, b) == b && l7.meet(best, u) != best {
			isLattice = false
		}
	}
	join[[2]int{a, b}] = best
}

@ A lattice is lower semimodular when $a\lor b$ covering both $a$ and $b$
forces $a$ and $b$ to cover $a\land b$; it is modular when
$a\le c$ implies $a\lor(b\land c)=(a\lor b)\land c$.
@<Test lower semimodularity and modularity@>=
covers := func(u, v int) bool {
	if u == v || l7.meet(u, v) != v {
		return false
	}
	for _, w := range elems {
		if w != u && w != v && l7.meet(u, w) == w && l7.meet(w, v) == v {
			return false
		}
	}
	return true
}
for _, a := range elems {
	for _, b := range elems {
		j, m := join[[2]int{a, b}], l7.meet(a, b)
		if covers(j, a) && covers(j, b) && !(covers(a, m) && covers(b, m)) {
			lowerSemi = false
		}
		for _, cc := range elems {
			if l7.meet(a, cc) != a {
				continue
			}
			lhs := join[[2]int{a, l7.meet(b, cc)}]
			if lhs != l7.meet(join[[2]int{a, b}], cc) {
				modular = false
			}
		}
	}
}

@* The identity of part (j).
Part~(j) claims that $\sum_{x'\sqsubseteq x}W(x')=\prod\{p_k\mid x_k=*\}$
whenever $x$ is stable---the sum running over the assignments {\it below\/}
$x$. With the single clause 123 and $x=001$ the sum has seven terms and comes
to 1; the program checks the identity for every stable assignment of random
problems, with random probabilities.
@<Functions@>=
func (t term) value(p []float64) float64 {
	if t.zero {
		return 0
	}
	x := 1.0
	for v := 1; v < len(p); v++ {
		if t.p&(1<<v) != 0 {
			x *= p[v]
		}
		if t.q&(1<<v) != 0 {
			x *= 1 - p[v]
		}
	}
	return x
}

@ @<Check the identity of part (j)@>=
fmt.Println("363(j). the sum of the weights below a stable assignment")
var nj, badJ int
rng := rand.New(rand.NewPCG(seed, 363))
sweep(4, reps/4, func(c *ctx) {
	p := make([]float64, c.n+1)
	for v := 1; v <= c.n; v++ {
		p[v] = rng.Float64()
	}
	for a := 0; a < c.nA; a++ {
		if !c.isStable[a] {
			continue
		}
		nj++
		@<Compare the sum below |a| with the product of its $p$'s@>
	}
})
claim(badJ == 0, "%d stable assignments, %d where the identity fails", nj, badJ)

@ @<Compare the sum below |a| with the product of its $p$'s@>=
sum := 0.0
for x, in := range c.below(a) {
	if in {
		sum += c.weight(x).value(p)
	}
}
want := 1.0
for v := 1; v <= c.n; v++ {
	if c.digit(a, v) == 0 {
		want *= p[v]
	}
}
if diff := sum - want; diff > 1e-9 || diff < -1e-9 {
	badJ++
}

@* Definite Horn clauses for a given family.
Part~(g) starts from a family $\cal L$ of subsets of $\{1,\ldots,n\}$, closed
under intersection, in which every member can climb to $\{1,\ldots,n\}$ inside
$\cal L$. It asks for definite Horn clauses---exactly one positive literal
each---with $L\in{\cal L}$ if and only if $L\sqsubseteq\{1,\ldots,n\}$.

The answer's recipe is to look at the places where the family stops: if
$L=L'\setminus l$ with $L'\in{\cal L}$ but $L\notin\cal L$, introduce a clause
that makes $L$ unstable by forcing $l$. Such a clause is
$(x_l\lor\bigvee\bar x_k)$, and everything turns on the range of that
disjunction.
@<Functions@>=
func horn(n int, ell map[uint32]bool, printed bool) fam {
	f := fam{n: n}
	for lp := range ell {
		for v := 1; v <= n; v++ {
			if lp&(1<<v) == 0 || ell[lp&^(1<<v)] {
				continue
			}
			src := lp &^ (1 << v)
			if printed {
				src = lp
			}
			@<Add the clause that forces |v|@>
		}
	}
	return f
}

@ @<Add the clause that forces |v|@>=
cl := uint32(1) << lit(v, true)
for k := 1; k <= n; k++ {
	if src&(1<<k) != 0 {
		cl |= 1 << lit(k, false)
	}
}
f.cl = append(f.cl, cl)

@ The book's disjunction runs over $k\in L'$. But $l$ belongs to $L'$, so the
clause then contains $x_l$ and $\bar x_l$ both: it is a tautology, which is no
clause at all in Knuth's convention and can never force anything. Ranging over
$k\in L$ instead gives the implication
$\bigwedge_{k\in L}x_k\Rightarrow x_l$, which makes $L$ unstable exactly as
wanted. The program builds both and compares.
@<Check the construction of part (g)@>=
fmt.Println("363(g). definite Horn clauses for a family of sets")
@<Try both readings on the family of part (f)@>
@<Try both readings on random families@>

@ @<Try both readings on the family of part (f)@>=
ell := map[uint32]bool{}
for _, s := range twelve {
	var m uint32
	for i := 0; i < len(s); i++ {
		m |= 1 << uint(s[i]-'0')
	}
	ell[m] = true
}
claim(closedUnderMeet(ell) && climbs(5, ell),
	"the twelve sets of part (f) are closed under intersection and climb")
claim(rebuilds(5, ell, false), "over k in L, the %d clauses rebuild the family",
	len(horn(5, ell, false).cl))
claim(!rebuilds(5, ell, true), "over k in L', as printed, they do not")

@ |rebuilds| runs the construction and asks whether the sets below
$\{1,\ldots,n\}$ are the family we started from.
@<Functions@>=
func rebuilds(n int, ell map[uint32]bool, printed bool) bool {
	c := newCtx(horn(n, ell, printed))
	all := 0
	for v := 1; v <= n; v++ {
		all = c.assign(all, lit(v, true))
	}
	below := c.below(all)
	for a := 0; a < c.nA; a++ {
		var m uint32
		positive := true
		for v := 1; v <= n; v++ {
			switch c.digit(a, v) {
			case 1:
				m |= 1 << v
			case 2:
				positive = false
			}
		}
		if positive && below[a] != ell[m] {
			return false
		}
		if !positive && below[a] {
			return false
		}
	}
	return true
}

@ @<Functions@>=
func closedUnderMeet(ell map[uint32]bool) bool {
	for a := range ell {
		for b := range ell {
			if !ell[a&b] {
				return false
			}
		}
	}
	return true
}

func climbs(n int, ell map[uint32]bool) bool {
	up := map[uint32]bool{(1 << uint(n+1)) - 2: true}
	for again := true; again; {
		again = false
		for a := range ell {
			if up[a] {
				continue
			}
			for v := 1; v <= n; v++ {
				if a&(1<<v) == 0 && up[a|1<<v] {
					up[a], again = true, true
				}
			}
		}
	}
	for a := range ell {
		if !up[a] {
			return false
		}
	}
	return true
}

@ Random families are made by taking a random collection of subsets, throwing
in $\{1,\ldots,n\}$, closing it under intersection, and then dropping whatever
cannot climb---repeating until nothing changes, which leaves a family that
meets the hypotheses of part~(g).
@<Try both readings on random families@>=
var nfam, badNarrow, badPrinted int
rg := rand.New(rand.NewPCG(seed, 364))
for i := 0; i < reps/4; i++ {
	n := 3 + rg.IntN(2)
	@<Build a random family that satisfies the hypotheses@>
	if len(horn(n, ell, false).cl) == 0 {
		continue // the whole power set; the construction has nothing to do
	}
	nfam++
	if !rebuilds(n, ell, false) {
		badNarrow++
	}
	if !rebuilds(n, ell, true) {
		badPrinted++
	}
}
claim(badNarrow == 0, "over k in L: %d random families that need clauses, "+
	"%d failures", nfam, badNarrow)
claim(badPrinted == nfam, "over k in L', as printed: all %d of them fail",
	nfam)

@ @<Build a random family that satisfies the hypotheses@>=
ell := map[uint32]bool{(1 << uint(n+1)) - 2: true}
for j, k := 0, 2+rg.IntN(2); j < k; j++ {
	var m uint32
	for v := 1; v <= n; v++ {
		if rg.IntN(2) == 1 {
			m |= 1 << v
		}
	}
	ell[m] = true
}
for again := true; again; {
	again = false
	for a := range ell {
		for b := range ell {
			if !ell[a&b] {
				ell[a&b], again = true, true
			}
		}
	}
	if !climbs(n, ell) {
		@<Drop the members that cannot climb@>
		again = true
	}
}

@ @<Drop the members that cannot climb@>=
up := map[uint32]bool{(1 << uint(n+1)) - 2: true}
for more := true; more; {
	more = false
	for a := range ell {
		if up[a] {
			continue
		}
		for v := 1; v <= n; v++ {
			if a&(1<<v) == 0 && up[a|1<<v] {
				up[a], more = true, true
			}
		}
	}
}
for a := range ell {
	if !up[a] {
		delete(ell, a)
	}
}

@* Algorithm C's trail.
Part~(a) is about the solver itself: is the partial assignment on the trail, at
the moment step C5 picks a new decision literal, always stable? The answer says
yes, and calls it an important invariant of Algorithm C.

The package hands the trail over through |SetTrace|. The program gives the
solver clauses it has built itself, so it can check each trail against those
same clauses, from the definition, with no help from the solver.
@<Functions@>=
func trailStable(f fam, trail []sat.Lit) bool {
	var tm, fm uint32
	for _, l := range trail {
		tm |= 1 << uint(l)
		fm |= 1 << uint(l^1)
	}
	for _, cl := range f.cl {
		if cl&tm == 0 && bits.OnesCount32(cl&^fm) <= 1 {
			return false
		}
	}
	return true
}

@ Two kinds of problem are tried: random 3SAT at a ratio that makes both
answers common, and the van der Waerden clauses that open the section, which
are unsatisfiable for $n\ge9$ and make Algorithm C work.
@<Check part (a) against Algorithm C@>=
fmt.Println("363(a). the trail whenever Algorithm C decides")
var runs, decisions, unstable int
rt := rand.New(rand.NewPCG(seed, 5))
for i := 0; i < reps/20; i++ {
	@<Make a random 3SAT problem@>
	@<Solve it, watching every decision@>
}
for n := 9; n <= 20; n++ {
	f := waerden(n)
	@<Solve it, watching every decision@>
}
claim(unstable == 0, "%d runs, %d decisions, %d unstable trails",
	runs, decisions, unstable)

@ @<Make a random 3SAT problem@>=
n := 12 + rt.IntN(12)
f := fam{n: n}
for j := 0; j < 4*n; j++ {
	var cl uint32
	for bits.OnesCount32(cl) < 3 {
		v := 1 + rt.IntN(n)
		if cl&(3<<lit(v, true)) == 0 {
			cl |= 1 << lit(v, rt.IntN(2) == 1)
		}
	}
	f.cl = append(f.cl, cl)
}

@ The variables are created in order, so the solver numbers them the way this
program does, and a literal of the solver is a literal here.
@<Solve it, watching every decision@>=
s := sat.New()
for v := 1; v <= f.n; v++ {
	s.Lookup(strconv.Itoa(v))
}
for _, cl := range f.cl {
	var ls []sat.Lit
	for l := 2; l < 2*f.n+2; l++ {
		if cl&(1<<l) != 0 {
			ls = append(ls, sat.Lit(l))
		}
	}
	s.AddClause(ls...)
}
s.SetTrace(func(level int, trail []sat.Lit) {
	decisions++
	if !trailStable(f, trail) {
		unstable++
	}
})
if _, err := s.Solve(context.Background()); err != nil {
	claim(false, "the solver failed: %v", err)
}
runs++

@ The clauses $waerden(3,3;n)$ ask for a binary string of length $n$ with no
three equally spaced 0s and no three equally spaced 1s.
@<Functions@>=
func waerden(n int) fam {
	f := fam{n: n}
	for d := 1; d <= (n-1)/2; d++ {
		for i := 1; i+2*d <= n; i++ {
			var pos, neg uint32
			for j := 0; j < 3; j++ {
				pos |= 1 << lit(i+j*d, true)
				neg |= 1 << lit(i+j*d, false)
			}
			f.cl = append(f.cl, pos, neg)
		}
	}
	return f
}

@* Random problems.
The parts that speak of all families are checked on random ones, a few thousand
per number of variables. A family is a handful of clauses drawn from the $3^n$
clauses on $n$ variables, the empty clause included, since nothing in the
exercise rules it out.
@<Functions@>=
func sweep(maxN, count int, do func(*ctx)) {
	for n := 1; n <= maxN; n++ {
		cands := allClauses(n)
		rng := rand.New(rand.NewPCG(seed, uint64(n)))
		for i := 0; i < count; i++ {
			f, seen := fam{n: n}, map[uint32]bool{}
			for j, m := 0, 1+rng.IntN(8); j < m; j++ {
				if cl := cands[rng.IntN(len(cands))]; !seen[cl] {
					seen[cl] = true
					f.cl = append(f.cl, cl)
				}
			}
			do(newCtx(f))
		}
	}
}

func allClauses(n int) []uint32 {
	out := []uint32{0}
	for v := 1; v <= n; v++ {
		next := make([]uint32, 0, 3*len(out))
		for _, c := range out {
			next = append(next, c, c|1<<lit(v, true), c|1<<lit(v, false))
		}
		out = next
	}
	return out
}

@* Index.
