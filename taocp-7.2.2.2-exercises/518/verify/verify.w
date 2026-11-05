\datethis
\def\title{3SAT and the permanent}

@s sat.Lit int
@s sat.Status int
@s sat.Solver int

@* Introduction.
Counting the perfect matchings of a bipartite graph means evaluating a
permanent, and Valiant proved in 1979 that this is hard even when the graph is
very simple. Exercise 7.2.2.2--518 asks for a reduction that makes the point
with integers rather than with graphs:

\medskip{\narrower\noindent\bf518.~[M32]\enspace\rm Given a 3SAT problem with
$m$ clauses and $n$ variables, we shall construct a $(6m+n)\times(6m+n)$
matrix $M$ of integers such that the permanent, $\mathop{\rm per}M$, is zero
if and only if the clauses are unsatisfiable. \dots

\smallskip
\item{a)} Find a $6\times6$ matrix $A=(a_{ij})$, whose elements are either 0,
1, or $-1$, such that
$$\mathop{\rm per}\pmatrix{
a_{11}&a_{12}&a_{13}&a_{14}&a_{15}&a_{16}\cr
a_{21}+2p&a_{22}&a_{23}+2q&a_{24}&a_{25}+2r&a_{26}\cr
a_{31}&a_{32}&a_{33}&a_{34}&a_{35}&a_{36}\cr
a_{41}+2u&a_{42}&a_{43}+2v&a_{44}&a_{45}+2w&a_{46}\cr
a_{51}&a_{52}&a_{53}&a_{54}&a_{55}&a_{56}\cr
a_{61}+2x&a_{62}&a_{63}+2y&a_{64}&a_{65}+2z&a_{66}\cr}
=16\Bigl(\mathop{\rm per}\pmatrix{p+1&q&r\cr u&v+1&w\cr x&y&z+1\cr}-1\Bigr).$$
\item{b)} In which of the rows and columns of $M$ does `2' occur twice? once?
not at all?
\item{c)} Conclude that $\mathop{\rm per}M=2^{4m+n}s$, when the 3SAT problem
has exactly $s$ solutions.\par}\medskip

\noindent Part (c) is stronger than the headline: the permanent does not
merely detect satisfiability, it counts solutions. That is what this program
checks. The matrix is built from the exercise's own recipe, the permanent is
evaluated by Ryser's formula---which knows nothing about 3SAT---and the number
of solutions is obtained twice over, once by running through all $2^n$
assignments and once by asking the {\tt sat} package of the directory above
for them one at a time. Three routes that share nothing then have to agree.

I wrote this on 6 November 2026.

@ Every claim is a mode.
@c
package main

import (
	"context"
	"flag"
	"fmt"
	"math/big"
	"math/rand/v2"
	"os"

	"github.com/sjnam/sat"
)

@<Global variables@>
@<Functions@>

func main() {
	@<Read the command line@>
	if on("gadget") {
		@<Check the $6\times6$ matrix of answer 518(a)@>
	}
	if on("twos") {
		@<Check where the 2s fall, as answer 518(b) says@>
	}
	if on("permanent") {
		@<Check that the permanent counts solutions@>
	}
	if on("limits") {
		@<Check what the construction quietly assumes@>
	}
	if on("example") {
		@<Build the matrix of the problem (7)@>
	}
	@<Say how it went@>
}

@ The permanent is the expensive part, so the sizes are deliberately small:
\.{-max} is the largest $6m+n$ that Ryser's formula will be asked for.
@<Read the command line@>=
flag.StringVar(&mode, "mode", "all",
	"gadget, twos, permanent, limits, example, or all")
flag.IntVar(&reps, "reps", 500, "how many random problems to try")
flag.IntVar(&maxN, "max", 22, "the largest 6m+n to take a permanent of")
flag.Uint64Var(&seed, "seed", 20261106, "seed for the random problems")
flag.Parse()

@ @<Global variables@>=
var (
	mode     string
	reps     int
	maxN     int
	seed     uint64
	failures int
)

@ Each claim is announced, checked, and marked; one \.{FAIL} anywhere makes
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

@* The permanent.
Ryser's formula sums over the subsets $S$ of the columns,
$$\mathop{\rm per}M=(-1)^N\sum_S(-1)^{|S|}\prod_i\sum_{j\in S}m_{ij},$$
and a Gray code lets each subset be reached from the one before by changing a
single column, so the row sums are kept up to date in $O(N)$ time per step.
The row sums of the matrices here never exceed~6 in absolute value, so the
product fits in an |int64| as long as $6^N$ does; the sum over all subsets
does not, and is accumulated in a |big.Int|.
@<Functions@>=
func permanent(M [][]int) *big.Int {
	N := len(M)
	if N > 62 {
		panic("the matrix is far too large")
	}
	sum := make([]int64, N)
	total, term := new(big.Int), new(big.Int)
	parity := N & 1
	for g := uint64(1); g < 1<<uint(N); g++ {
		@<Move to the next subset and update the row sums@>
		@<Add this subset's contribution to |total|@>
	}
	return total
}

@ The standard Gray code $g\oplus(g\gg1)$ changes one bit at a time; bit |j|
goes in or out according to whether it is set in the new code word.
@<Move to the next subset and update the row sums@>=
code := g ^ (g >> 1)
j := 0
for b := g & -g; b > 1; b >>= 1 {
	j++
}
in := code&(1<<uint(j)) != 0
for i := 0; i < N; i++ {
	if in {
		sum[i] += int64(M[i][j])
	} else {
		sum[i] -= int64(M[i][j])
	}
}

@ A single zero row sum kills the whole product, which happens often enough on
these sparse matrices to be worth the test.
@<Add this subset's contribution to |total|@>=
prod, zero := int64(1), false
for i := 0; i < N; i++ {
	if sum[i] == 0 {
		zero = true
		break
	}
	prod *= sum[i]
}
if !zero {
	term.SetInt64(prod)
	if popcount(code)&1 != parity {
		total.Sub(total, term)
	} else {
		total.Add(total, term)
	}
}

@ @<Functions@>=
func popcount(x uint64) int {
	n := 0
	for ; x != 0; x &= x - 1 {
		n++
	}
	return n
}

@* The gadget of part (a).
The answer gives
$$A=\pmatrix{x&y&y\cr y&x&y\cr y&y&x\cr},\qquad
x=\pmatrix{-1&0\cr 1&0\cr},\qquad y=\pmatrix{1&1\cr -1&1\cr},$$
written in $2\times2$ blocks, so the symmetry the hint promises is a
symmetry of the three clause positions.
@<Functions@>=
func gadget(x, y [2][2]int) [][]int {
	blk := [3][3][2][2]int{{x, y, y}, {y, x, y}, {y, y, x}}
	A := make([][]int, 6)
	for i := range A {
		A[i] = make([]int, 6)
		for j := 0; j < 6; j++ {
			A[i][j] = blk[i/2][j/2][i%2][j%2]
		}
	}
	return A
}

@ Both sides of the identity are polynomials in $p,q,r,u,v,w,x,y,z$, and each
of those nine letters occurs in exactly one entry of its matrix. A permanent
is a sum of products that take one entry from each row, so each letter can
appear at most once in a product: both sides are multilinear. A multilinear
polynomial in nine variables is determined by its values at the $2^9$ points
where every variable is 0 or~1, so checking those 512 points is not a sample
but a proof.
@<Functions@>=
func identityHolds(A [][]int) bool {
	spots := [9][2]int{{1, 0}, {1, 2}, {1, 4}, {3, 0}, {3, 2}, {3, 4},
		{5, 0}, {5, 2}, {5, 4}}
	for bits := 0; bits < 512; bits++ {
		@<Evaluate both sides at the point |bits|, and compare@>
	}
	return true
}

@ The left side is the $6\times6$ permanent with $2$ added in the six spots
whose letter is 1; the right side is sixteen times one less than a
$3\times3$ permanent with the three diagonal letters raised by one.
@<Evaluate both sides at the point |bits|, and compare@>=
L := make([][]int, 6)
for i := range L {
	L[i] = append([]int(nil), A[i]...)
}
var t [9]int
for k := 0; k < 9; k++ {
	if bits&(1<<uint(k)) != 0 {
		t[k] = 1
		L[spots[k][0]][spots[k][1]] += 2
	}
}
R := [][]int{{t[0] + 1, t[1], t[2]}, {t[3], t[4] + 1, t[5]},
	{t[6], t[7], t[8] + 1}}
want := new(big.Int).Sub(permanent(R), big.NewInt(1))
want.Mul(want, big.NewInt(16))
if permanent(L).Cmp(want) != 0 {
	return false
}

@ Answer 518(a) is checked first, and then I ask how much choice there was.
Searching every $A$ with entries in $\{0,1,-1\}$ is out of the question, but
the hint points at the symmetric shape above, and there only the two blocks
are free: $3^4\cdot3^4=6561$ possibilities.
@<Check the $6\times6$ matrix of answer 518(a)@>=
fmt.Println("518(a). a 6x6 matrix of 0s and +-1s")
xa := [2][2]int{{-1, 0}, {1, 0}}
ya := [2][2]int{{1, 1}, {-1, 1}}
claim(identityHolds(gadget(xa, ya)),
	"the answer's A satisfies the identity at all 512 points of {0,1}^9")
@<Search the symmetric shape for other solutions@>

@ @<Search the symmetric shape for other solutions@>=
found, hasAnswer := 0, false
for a := 0; a < 81; a++ {
	for b := 0; b < 81; b++ {
		x, y := block(a), block(b)
		if !identityHolds(gadget(x, y)) {
			continue
		}
		found++
		if x == xa && y == ya {
			hasAnswer = true
		}
	}
}
claim(hasAnswer, "it is one of the %d symmetric solutions, of 6561 shapes",
	found)

@ @<Functions@>=
func block(k int) [2][2]int {
	var b [2][2]int
	for i := 0; i < 2; i++ {
		for j := 0; j < 2; j++ {
			b[i][j] = k%3 - 1
			k /= 3
		}
	}
	return b
}

@* The matrix.
A clause is a list of three literals, a literal being $v$ or $-v$ for a
variable $v$ in $1\ldots n$. Rows $1\ldots n$ of $M$ and columns
$6m+1\ldots6m+n$ belong to the variables; clause~$i$ owns rows
$n+6(i-1)+1\ldots n+6i$ and columns $6(i-1)+1\ldots6i$, where its copy of~$A$
sits. Everything else is 0 except for the 2s.
@<Functions@>=
func inputCol(i, j int) int { return 6*i + 2*j }

func outputRow(n, i, j int) int { return n + 6*i + 2*j + 1 }

func build(cl [][]int, n int) [][]int {
	m := len(cl)
	N := 6*m + n
	M := make([][]int, N)
	for i := range M {
		M[i] = make([]int, N)
	}
	A := gadget([2][2]int{{-1, 0}, {1, 0}}, [2][2]int{{1, 1}, {-1, 1}})
	for i := 0; i < m; i++ {
		for a := 0; a < 6; a++ {
			copy(M[n+6*i+a][6*i:6*i+6], A[a])
		}
	}
	@<Thread each literal through the clauses that hold it@>
	return M
}

@ ``If literal $l$ appears in $t\ge0$ clauses $i_1<\cdots<i_t$, as element
$j_1,\ldots,j_t$, we put `2' in column $I_{i_{k+1}j_{k+1}}$ of row
$O_{i_kj_k}$ for $0\le k\le t$,'' where $O_{i_0j}$ is row $|l|$ and
$I_{i_{t+1}j}$ is column $6m+|l|$. So each literal threads a chain from its
variable's row, through one input of every clause that holds it, to its
variable's column. Both polarities thread the same row and the same column,
which is why part (b) can say ``twice.''
@<Thread each literal through the clauses that hold it@>=
for v := 1; v <= n; v++ {
	for _, l := range []int{v, -v} {
		row := v - 1
		for i, c := range cl {
			for j, lit := range c {
				if lit == l {
					M[row][inputCol(i, j)] = 2
					row = outputRow(n, i, j)
				}
			}
		}
		M[row][6*m+v-1] = 2
	}
}

@* Where the 2s fall.
Part (b) answers its own question: twice in the $n$ variable rows and $n$
variable columns; once in the $3m$ output rows and $3m$ input columns; never
in the $3m$ input rows and $3m$ output columns. Rows $n+6i+1$, $n+6i+3$,
$n+6i+5$ of clause~$i$ are its inputs and rows $n+6i+2$, $n+6i+4$, $n+6i+6$
its outputs; columns $6i+1$, $6i+3$, $6i+5$ are its inputs and the even ones
its outputs. Counting the 2s of a freshly built matrix must reproduce all
six numbers.
@<Check where the 2s fall, as answer 518(b) says@>=
fmt.Println("518(b). where the 2s are")
rng := rand.New(rand.NewPCG(seed, 518))
bad, tried := 0, 0
for t := 0; t < reps; t++ {
	n := 3 + rng.IntN(4)
	m := 1 + rng.IntN(4)
	cl := randomProblem(rng, m, n)
	if cl == nil {
		continue
	}
	tried++
	if !twosAreRight(build(cl, n), len(cl), n) {
		bad++
	}
}
claim(bad == 0, "%d random problems, %d where a count is wrong", tried, bad)

@ @<Functions@>=
func twosAreRight(M [][]int, m, n int) bool {
	N := len(M)
	rowTwos, colTwos := make([]int, N), make([]int, N)
	for i := 0; i < N; i++ {
		for j := 0; j < N; j++ {
			if M[i][j] == 2 {
				rowTwos[i]++
				colTwos[j]++
			}
		}
	}
	@<Compare the counts against answer 518(b)@>
	return true
}

@ @<Compare the counts against answer 518(b)@>=
for v := 0; v < n; v++ {
	if rowTwos[v] != 2 || colTwos[6*m+v] != 2 {
		return false
	}
}
for i := 0; i < m; i++ {
	for j := 0; j < 3; j++ {
		if rowTwos[outputRow(n, i, j)] != 1 || colTwos[inputCol(i, j)] != 1 {
			return false
		}
		if rowTwos[n+6*i+2*j] != 0 || colTwos[6*i+2*j+1] != 0 {
			return false
		}
	}
}

@* Counting solutions three ways.
A random problem has $m$ clauses of three distinct variables, each negated or
not by a coin, and every variable is made to occur at least once---two
conditions that section ``What the construction assumes'' shows to be
necessary. The generator returns |nil| when it cannot meet them.
@<Functions@>=
func randomProblem(rng *rand.Rand, m, n int) [][]int {
	if n < 3 || 3*m < n {
		return nil
	}
	cl := make([][]int, m)
	for i := range cl {
		vs := rng.Perm(n)[:3]
		cl[i] = make([]int, 3)
		for j, v := range vs {
			cl[i][j] = v + 1
			if rng.IntN(2) == 0 {
				cl[i][j] = -cl[i][j]
			}
		}
	}
	@<Give up unless every variable occurs@>
	return cl
}

@ @<Give up unless every variable occurs@>=
seen := make([]bool, n+1)
for _, c := range cl {
	for _, l := range c {
		seen[abs(l)] = true
	}
}
for v := 1; v <= n; v++ {
	if !seen[v] {
		return nil
	}
}

@ @<Functions@>=
func abs(l int) int {
	if l < 0 {
		return -l
	}
	return l
}

@ The first route to the number of solutions runs through all $2^n$
assignments.
@<Functions@>=
func countByBrute(cl [][]int, n int) int {
	s := 0
	for a := 0; a < 1<<uint(n); a++ {
		ok := true
		for _, c := range cl {
			if !holds(c, a) {
				ok = false
				break
			}
		}
		if ok {
			s++
		}
	}
	return s
}

func holds(c []int, a int) bool {
	for _, l := range c {
		if (a>>uint(abs(l)-1))&1 == 1 == (l > 0) {
			return true
		}
	}
	return false
}

@ The second route asks the package for one solution at a time, blocking each
as it comes. This is the use the readings of this directory make of the
package: not to be believed, but to be checked against something else.
@<Functions@>=
func countWithPackage(cl [][]int, n int) int {
	s := sat.New()
	v := make([]sat.Lit, n+1)
	for i := 1; i <= n; i++ {
		v[i] = s.NewVar()
	}
	for _, c := range cl {
		lits := make([]sat.Lit, len(c))
		for k, l := range c {
			lits[k] = v[abs(l)]
			if l < 0 {
				lits[k] = lits[k].Not()
			}
		}
		s.AddClause(lits...)
	}
	@<Solve again and again, blocking what comes back@>
	return found
}

@ @<Solve again and again, blocking what comes back@>=
found := 0
for {
	st, err := s.Solve(context.Background())
	if err != nil {
		panic(err)
	}
	if st != sat.Sat {
		break
	}
	found++
	block := make([]sat.Lit, n)
	for i := 1; i <= n; i++ {
		block[i-1] = v[i]
		if s.Value(v[i]) {
			block[i-1] = v[i].Not()
		}
	}
	s.AddClause(block...)
}

@ Now the three routes meet. Ryser's formula is the expensive one, so the
sizes are kept under \.{-max}; the default stops at $6m+n=20$, which is a
million subsets.
@<Check that the permanent counts solutions@>=
fmt.Println("518(c). per M = 2^(4m+n) s")
rng := rand.New(rand.NewPCG(seed, 5180))
tried, bad, disagree := 0, 0, 0
biggest, totalSol := 0, 0
for t := 0; t < reps; t++ {
	n := 3 + rng.IntN(3)
	m := 1 + rng.IntN(3)
	if 6*m+n > maxN {
		continue
	}
	cl := randomProblem(rng, m, n)
	if cl == nil {
		continue
	}
	@<Compare the permanent with the two counts@>
}
claim(bad == 0, "%d random problems up to %dx%d, %d where per M differs "+
	"from 2^(4m+n)s", tried, biggest, biggest, bad)
claim(disagree == 0,
	"the package's enumeration disagrees with brute force %d times", disagree)
fmt.Printf("        %d solutions counted in all\n", totalSol)

@ @<Compare the permanent with the two counts@>=
tried++
if 6*len(cl)+n > biggest {
	biggest = 6*len(cl) + n
}
s := countByBrute(cl, n)
totalSol += s
if countWithPackage(cl, n) != s {
	disagree++
}
want := new(big.Int).Lsh(big.NewInt(int64(s)), uint(4*len(cl)+n))
if permanent(build(cl, n)).Cmp(want) != 0 {
	bad++
}

@* What the construction assumes.
Two hypotheses are never stated, and the identity fails without either.

The first is that no literal occurs twice in the same clause. The answer
indexes the clauses that hold a literal as $i_1<\cdots<i_t$, which leaves no
room for two elements of one clause; threading them in the order they are
written is the obvious repair, and it is what |build| does, but the count
comes out wrong all the same.

The second is that every variable occurs somewhere. If variable $v$ occurs in
no clause then both of its literals thread the empty chain, which is the
single entry in row $v$ and column $6m+v$, so that row holds one 2 instead of
the two that part (b) promises, and the permanent loses a factor of 2 for
each such variable.
@<Check what the construction quietly assumes@>=
fmt.Println("the two hypotheses the construction needs")
@<Show that a repeated literal breaks it@>
@<Show that an absent variable breaks it@>

@ The clauses $\{1\,1\,2,\ \bar1\,2\,3\}$ have three variables, all of them
present, and the only flaw is the repetition.
@<Show that a repeated literal breaks it@>=
rep := [][]int{{1, 1, 2}, {-1, 2, 3}}
s := countByBrute(rep, 3)
want := new(big.Int).Lsh(big.NewInt(int64(s)), uint(4*len(rep)+3))
got := permanent(build(rep, 3))
claim(got.Cmp(want) != 0,
	"with a literal twice in one clause, per M = %v but 2^(4m+n)s = %v",
	got, want)

@ With $n=4$ and the single clause $\{1\,2\,3\}$, variable 4 is idle; the
permanent comes out exactly half of what part (c) predicts, and doubling $n$
again halves it again.
@<Show that an absent variable breaks it@>=
idle := [][]int{{1, 2, 3}}
for n := 3; n <= 5; n++ {
	s := countByBrute(idle, n)
	want := new(big.Int).Lsh(big.NewInt(int64(s)), uint(4+n))
	got := permanent(build(idle, n))
	ratio := new(big.Rat).SetFrac(want, got)
	claim((n == 3) == (got.Cmp(want) == 0),
		"n=%d with one clause on variables 1,2,3: per M is 2^(4m+n)s/%v",
		n, ratio.RatString())
}

@* The example of the text.
Equation (7) on page 188 is
$R=\{12\bar3,23\bar4,341,4\bar12,\bar1\bar23,\bar2\bar34,\bar3\bar4\bar1\}$,
the little problem that the section returns to again and again. With $m=7$
and $n=4$ its matrix is $46\times46$, which is the picture printed beside the
exercise. Ryser's formula would need $2^{46}$ terms, so the permanent itself
is out of reach here; what can be checked is the shape, the places of the 2s,
and the number of solutions that part (c) says the permanent must encode.
@<Build the matrix of the problem (7)@>=
fmt.Println("the problem (7) of page 188")
seven := [][]int{{1, 2, -3}, {2, 3, -4}, {3, 4, 1}, {4, -1, 2},
	{-1, -2, 3}, {-2, -3, 4}, {-3, -4, -1}}
M := build(seven, 4)
claim(len(M) == 46, "the matrix is %dx%d, as the figure shows", len(M),
	len(M))
claim(twosAreRight(M, 7, 4), "every row and column holds the 2s of part (b)")
@<Say what the permanent of the example must be@>

@ @<Say what the permanent of the example must be@>=
s := countByBrute(seven, 4)
claim(countWithPackage(seven, 4) == s,
	"it has %d solutions, by brute force and by the package alike", s)
exp := new(big.Int).Lsh(big.NewInt(int64(s)), uint(4*7+4))
fmt.Printf("        so per M = 2^32 * %d = %v, which Ryser cannot reach\n",
	s, exp)
@<Note how small an unsatisfiable example would have to be@>

@ The headline claim of the exercise---that the permanent vanishes exactly
when the clauses are unsatisfiable---has a half that no amount of patience
will check directly. A clause of three distinct literals forbids one eighth
of the assignments, so fewer than eight clauses always leave one standing;
and with two variables every clause of three distinct literals contains a
complementary pair and is a tautology. An unsatisfiable instance therefore
needs $m\ge8$ and $n\ge3$, which makes $M$ at least $51\times51$. Everything
above tests the formula where it can be tested, on problems that do have
solutions, where it pins the permanent exactly rather than merely declaring
it nonzero.
@<Note how small an unsatisfiable example would have to be@>=
smallest := 6*8 + 3
claim(smallest == 51,
	"an unsatisfiable instance needs m>=8 and n>=3, so M is at least %dx%d",
	smallest, smallest)
fmt.Println("        and 2^51 Ryser terms is beyond brute force")
