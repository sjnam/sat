\datethis
\def\title{Six gates}

@s sat.Lit int
@s sat.Status int
@s sat.Stats int
@s point int
@s step int
@s chain int
@s instance int

@* Introduction.
Section 7.2.2.2 has a little parable about learning a Boolean function. Table~2
lists thirty-two points $x=x_1\ldots x_{20}$, sixteen where a hidden function
is~1 and sixteen where it is~0, and a \.{SAT} solver soon finds a four-term DNF,
Eq.~(27), that fits every one of them. Exercise~56 then asks for a fit that
depends on only five of the twenty variables, and exercise~57, the one this
program is about, goes further:

\medskip{\narrower\noindent\bf 57.~[29]\enspace\rm Combining the previous
exercise with the methods of Section 7.1.2, exhibit a function $f$ for Table~2
that can be evaluated with only six Boolean operations(!).\par}\medskip

\noindent The answer recalls from answer~56 that there are twelve sets of five
variables on which Table~2 can be defined consistently, prints the twelve
resulting truth tables with their don't-cares, and says that ``the tenth of
these yields''
$$f(x)=((x_8\oplus(x_9\lor x_{10}))\lor((x_6\lor x_{12})\oplus\bar x_{10}))
  \oplus x_{12}.$$

I wrote this on 16 September 2026, as the first of a series of careful readings
of the \S7.2.2.2 exercises that Knuth's news page asks readers to check. It
checks every statement the answer makes, from the transcription of Table~2 to
the six operations, and then asks the question the exclamation mark invites:
could it be done with five? It cannot, and the program shows that twice, once
by exhaustive search and once with the {\tt sat} package of the directory
above, which is a Go rendering of Knuth's {\tt SAT13}. Along the way it finds
that the tenth table is one of five that allow six operations.

@ The program is a list of modes, one per claim.
@c
package main

import (
	"context"
	"flag"
	"fmt"
	"math/big"
	"math/bits"
	"math/rand/v2"
	"slices"
	"strings"
	"sync"
	"time"

	"github.com/sjnam/sat"
)

@<Types@>
@<Global variables@>
@<Functions@>

func main() {
	@<Read the command line@>
	@<Read Table 2@>
	@<Find the covering sets@>
	if on("table2") {
		@<Check Table 2 against $\pi$ and $e$@>
	}
	if on("covers") {
		@<Report the covering sets@>
	}
	if on("tables") {
		@<Compare the twelve truth tables with the answer@>
	}
	if on("formula") {
		@<Check the formula and count its operations@>
	}
	if on("exhaustive") {
		@<Rule out five steps by exhaustive search@>
	}
	if on("sat") {
		@<Rule out five steps, and find six, with the \.{SAT} solver@>
	}
	if on("selftest") {
		@<Test the two searches against each other@>
	}
	if mode == "direct" {
		@<Try answer 477 on all twenty variables@>
	}
}

@ Every mode but \.{direct} runs under \.{-mode all}, which takes about seven
minutes, most of it spent in the last part of the \.{sat} mode. The mode
\.{direct} is there to show why the argument of (iv) below is needed.
@<Read the command line@>=
flag.StringVar(&mode, "mode", "all", "table2, covers, tables, formula, "+
	"exhaustive, sat, selftest, all, or direct")
trials := flag.Int("trials", 1000, "random instances for selftest")
maxSteps := flag.Int("r", 4, "the most steps to try in direct mode")
flag.Parse()

@ @<Global variables@>=
var mode string

@ @<Functions@>=
func on(m string) bool { return mode == m || mode == "all" }

@* Table 2.
Here is the table, copied from page 199. Each row is $x_1x_2\ldots x_{20}$.
@<Global variables@>=
var leftRows = [16]string{ // the cases where $f(x)=1$
	"11001001000011111101", "10101010001000100001",
	"01101000110000100011", "01001100010011000110",
	"01100010100010111000", "00001101110000011100",
	"11010001001010010000", "00100100111000001000",
	"10001010011001111100", "11000111010000000010",
	"00001011101111101010", "01100011101100010011",
	"10011011001000100101", "00010100101000001000",
	"01111001100011100011", "01000000010011011101",
}

@ @<Global variables@>=
var rightRows = [16]string{ // the cases where $f(x)=0$
	"10101101111110000101", "01000101100010100010",
	"10111011010010101001", "10101010111111011100",
	"01010110001000000010", "01110011110100111100",
	"11110001110110001011", "10011100010110000011",
	"11001110001011010011", "01101001010110101001",
	"11100001001101100100", "00010001010001100100",
	"00110011111110111100", "11001001001110011101",
	"11001110001001001001", "10110011111011111001",
}

@ A point packs $x_j$ into bit $j-1$ of a word.
@<Types@>=
type point struct {
	x   uint32 // bit $j-1$ is $x_j$
	val bool   // the value of $f$ there
}

@ @<Global variables@>=
var points []point // the sixteen ones, then the sixteen zeros

@ @<Read Table 2@>=
for side, rows := range [2][16]string{leftRows, rightRows} {
	for _, s := range rows {
		var x uint32
		for j := 0; j < 20; j++ {
			if s[j] == '1' {
				x |= 1 << j
			}
		}
		points = append(points, point{x, side == 0})
	}
}

@ A transcription slip would spoil everything downstream, so it is worth
having a second source. Answer~53 gives one: the left column is $\pi/4$ in
binary, twenty bits at a time, and the right column is $e/4$. Machin's formula
$\pi/4=4\arctan{1\over5}-\arctan{1\over239}$ and the series for~$e$, carried to
400 bits, are more than enough for 320.
@<Check Table 2 against $\pi$ and $e$@>=
const prec = 400
quarterPi := new(big.Float).SetPrec(prec).Mul(arctanInv(5, prec),
	big.NewFloat(4))
quarterPi.Sub(quarterPi, arctanInv(239, prec))
e := new(big.Float).SetPrec(prec)
term := new(big.Float).SetPrec(prec).SetInt64(1)
for k := int64(1); k <= 120; k++ {
	e.Add(e, term)
	term.Quo(term, new(big.Float).SetPrec(prec).SetInt64(k))
}
e.Quo(e, big.NewFloat(4))
@<Compare the binary expansions with the two columns@>

@ @<Compare the binary expansions with the two columns@>=
for side, v := range []*big.Float{quarterPi, e} {
	scaled := new(big.Float).SetPrec(prec).SetMantExp(v, 320)
	n, _ := scaled.Int(nil)
	s := fmt.Sprintf("%0320b", n)
	rows, agree := [2][16]string{leftRows, rightRows}[side], 0
	for k := range 16 {
		if s[20*k:20*k+20] == rows[k] {
			agree++
		}
	}
	fmt.Printf("Table 2, %s column: %d of 16 rows are %s in binary\n",
		[]string{"left", "right"}[side], agree,
		[]string{"pi/4", "e/4"}[side])
}

@ The series $\arctan(1/x)=\sum_k(-1)^k/((2k+1)x^{2k+1})$ loses about
$2\lg x$ bits a term, so two hundred terms do for $x\ge5$.
@<Functions@>=
func arctanInv(x int64, prec uint) *big.Float {
	sum := new(big.Float).SetPrec(prec)
	xx := new(big.Float).SetPrec(prec).SetInt64(x)
	pow := new(big.Float).SetPrec(prec).Quo(
		new(big.Float).SetPrec(prec).SetInt64(1), xx)
	xx.Mul(xx, xx)
	for k := int64(0); k < 200; k++ {
		t := new(big.Float).SetPrec(prec).Quo(pow,
			new(big.Float).SetPrec(prec).SetInt64(2*k+1))
		if k%2 == 0 {
			sum.Add(sum, t)
		} else {
			sum.Sub(sum, t)
		}
		pow.Quo(pow, xx)
	}
	return sum
}

@* Covering sets.
A set $S$ of variables determines $f$ consistently exactly when no point on
the left agrees with a point on the right in all the positions of~$S$. With
$u_k$ and $v_l$ for the rows, as in answer~56, that says $S$ meets every one of
the 256 differences $u_k\oplus v_l$. There are only $2^{20}$ sets, so I simply
try them all, counting by size and keeping the smallest.
@<Find the covering sets@>=
for _, p := range points[:16] {
	for _, q := range points[16:] {
		diffs = append(diffs, p.x^q.x)
	}
}
for m := uint32(0); m < 1<<20; m++ {
	if covering(m) {
		gen[bits.OnesCount32(m)]++
		if bits.OnesCount32(m) == 5 {
			fives = append(fives, m)
		}
	}
}
slices.SortFunc(fives, func(a, b uint32) int {
	return slices.Compare(members(a), members(b))
})

@ @<Global variables@>=
var (
	diffs []uint32   // the 256 vectors $u_k\oplus v_l$
	gen   [21]int    // how many covering sets there are of each size
	fives []uint32   // the covering sets of size five, in lexicographic order
)

@ @<Functions@>=
func covering(m uint32) bool {
	for _, d := range diffs {
		if d&m == 0 {
			return false
		}
	}
	return true
}

@ A set is a bit mask; |members| lists its variables, numbered from~0.
@<Functions@>=
func members(m uint32) []int {
	var js []int
	for j := 0; j < 20; j++ {
		if m>>j&1 == 1 {
			js = append(js, j)
		}
	}
	return js
}

func setName(m uint32) string {
	var s []string
	for _, j := range members(m) {
		s = append(s, fmt.Sprint(j+1))
	}
	return "{" + strings.Join(s, ",") + "}"
}

@ Answer 56 lists the twelve sets and gives the generating function
$12z^5+994z^6+13503z^7+\cdots+20z^{19}+z^{20}$.
@<Report the covering sets@>=
answer56 := "{1,4,15,17,20} {1,10,15,17,20} {1,15,17,18,20} " +
	"{4,6,7,10,12} {4,6,9,10,12} {4,6,10,12,19} {4,10,12,15,19} " +
	"{5,7,11,12,15} {6,7,8,10,12} {6,8,9,10,12} {7,10,12,15,20} " +
	"{8,15,17,18,20}"
var names []string
for _, m := range fives {
	names = append(names, setName(m))
}
fmt.Println("covering sets by size:", gen)
fmt.Printf("the %d five-sets agree with answer 56: %v\n", len(fives),
	strings.Join(names, " ") == answer56)
fmt.Println("  and so do the coefficients 12, 994, 13503, ..., 20, 1:",
	gen[5] == 12 && gen[6] == 994 && gen[7] == 13503 &&
		gen[19] == 20 && gen[20] == 1)

@* The twelve truth tables.
Section 7.1.2 writes the truth table of $g(y_1,\ldots,y_w)$ as the $2^w$ bits
$g(0,\ldots,0)\ldots g(1,\ldots,1)$, with $y_1$ the most significant. So
restricting a point to a set~$S$ gives a position in the table of~$S$, the
first variable of~$S$ leading, and |ttIndex| computes it.
@<Functions@>=
func ttIndex(x, m uint32) int {
	t := 0
	for _, j := range members(m) {
		t = 2*t + int(x>>j&1)
	}
	return t
}

@ The answer sets the twelve tables in two columns of six, each table being
four groups of eight bits. I read them down the left column first.
@<Global variables@>=
var printedLeft = [6]string{
	"11110110 0*1*010* 10000111 10*0*1*0",
	"011*011* 1*110100 10*001*1 1000**10",
	"011*1*11 010*100* 10*0*000 *101*011",
	"10101110 0*100*1* 1*001*00 1**00***",
	"10101110 0*1*0*10 1*0*1*00 0**01***",
	"1*01110* 00**110* 11**0*00 10*****0",
}
var printedRight = [6]string{
	"00100101 11110*0* 1011**** **0**00*",
	"100*1**0 11*00010 1100**0* *0**0101",
	"**1*1000 1*101100 1*100*10 0*****1*",
	"1*1*1*10 10001100 0*101*1* **1*0*10",
	"1*01*00* 1101*0*0 0011*11* 1*100*0*",
	"001*1001 *1**1*1* 11*0*010 01011001",
}

@ The comparison is done in both reading orders, down the columns and across
the rows, because only one of them can be what was meant.
@<Compare the twelve truth tables with the answer@>=
var down, across []string
for _, col := range [2][6]string{printedLeft, printedRight} {
	for _, s := range col {
		down = append(down, strings.ReplaceAll(s, " ", ""))
	}
}
for r := range 6 {
	across = append(across, down[r], down[6+r])
}
downOK, acrossOK := 0, 0
for i, m := range fives {
	@<Build the table of |m| and compare it with the printed ones@>
}
fmt.Printf("tables that agree, reading down the columns: %d of 12\n", downOK)
fmt.Printf("tables that agree, reading across the rows:  %d of 12\n",
	acrossOK)

@ @<Build the table of |m| and compare it with the printed ones@>=
tt := []byte(strings.Repeat("*", 32))
for _, p := range points {
	tt[ttIndex(p.x, m)] = "01"[b2i(p.val)]
}
if string(tt) == down[i] {
	downOK++
}
if string(tt) == across[i] {
	acrossOK++
}
fmt.Printf("%2d %-16s %s\n", i+1, setName(m), tt)

@ @<Functions@>=
func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

@* Chains.
A Boolean chain has $n$ inputs and $r$ steps $x_i=x_j\circ_i x_k$ with
$j<k<i$; I number the nodes from~0. An operation is a four-bit truth table,
bit $2a+b$ being $a\circ b$, so |0x8| is $\land$, |0x6| is $\oplus$, and |0xe|
is~$\lor$. A chain may end with a complement.
@<Types@>=
type step struct {
	j, k int
	op   uint8
}

type chain struct {
	n     int
	steps []step
	comp  bool // is the output complemented?
}

@ Input $q$ of a chain is bit $q$ of |row|.
@<Functions@>=
func (ch *chain) eval(row uint32) bool {
	v := make([]bool, ch.n, ch.n+len(ch.steps))
	for q := range ch.n {
		v[q] = row>>q&1 == 1
	}
	for _, s := range ch.steps {
		a, b := b2i(v[s.j]), b2i(v[s.k])
		v = append(v, s.op>>(2*a+b)&1 == 1)
	}
	return v[len(v)-1] != ch.comp
}

@ Steps are printed as $g_1$, $g_2$, \dots, and inputs by the names given.
@<Functions@>=
var opForm = [16]string{"0", "~(a|b)", "~a&b", "~a", "a&~b", "~b", "a^b",
	"~(a&b)", "a&b", "~(a^b)", "b", "~a|b", "a", "a|~b", "a|b", "1"}

func (ch *chain) format(names []string) string {
	name := func(i int) string {
		if i < ch.n {
			return names[i]
		}
		return fmt.Sprintf("g%d", i-ch.n+1)
	}
	var s []string
	for i, st := range ch.steps {
		r := strings.NewReplacer("a", name(st.j), "b", name(st.k))
		s = append(s, name(ch.n+i)+" = "+r.Replace(opForm[st.op]))
	}
	return strings.Join(s, "; ")
}

@* The formula.
Written as a chain on all twenty variables, the answer's formula is six steps:
$$\vbox{\halign{$#$\hfil\cr
g_1=x_9\lor x_{10},\quad g_2=x_8\oplus g_1,\quad g_3=x_6\lor x_{12},\cr
g_4=x_{10}\equiv g_3,\quad g_5=g_2\lor g_4,\quad g_6=g_5\oplus x_{12}.\cr}}$$
The fourth, $(x_6\lor x_{12})\oplus\bar x_{10}$, is one operation, since
$\equiv$ is one of the sixteen. Section 7.1.2 prefers {\it normal\/} chains,
whose operations all take $(0,0)$ to~0, and the conversion costs nothing:
$g_4'=x_{10}\oplus g_3$, $g_5'=\bar g_2\land g_4'=\bar g_5$, and
$g_6'=g_5'\oplus x_{12}=\bar g_6$, with the output complemented.
@<Global variables@>=
var bookChain = chain{n: 20, steps: []step{
	{8, 9, 0xe}, {7, 20, 0x6}, {5, 11, 0xe},
	{9, 22, 0x9}, {21, 23, 0xe}, {11, 24, 0x6}}}

var normalChain = chain{n: 20, comp: true, steps: []step{
	{8, 9, 0xe}, {7, 20, 0x6}, {5, 11, 0xe},
	{9, 22, 0x6}, {21, 23, 0x2}, {11, 24, 0x6}}}

@ Three renderings, then: the formula as printed, typed into Go, and the two
chains. All must agree with Table 2 everywhere.
@<Check the formula and count its operations@>=
x := func(x uint32, j int) bool { return x>>(j-1)&1 == 1 }
agree := [3]int{}
for _, p := range points {
	f := ((x(p.x, 8) != (x(p.x, 9) || x(p.x, 10))) ||
		((x(p.x, 6) || x(p.x, 12)) != !x(p.x, 10))) != x(p.x, 12)
	for i, v := range []bool{f, bookChain.eval(p.x), normalChain.eval(p.x)} {
		if v == p.val {
			agree[i]++
		}
	}
}
var xnames []string
for j := 1; j <= 20; j++ {
	xnames = append(xnames, fmt.Sprintf("x%d", j))
}
fmt.Printf("formula, chain, normal chain agree with Table 2 at %v points\n",
	agree)
fmt.Printf("the chain has %d steps: %s\n", len(bookChain.steps),
	bookChain.format(xnames))
fmt.Printf("normal form, output complemented: %s\n",
	normalChain.format(xnames))
@<Show how the formula fills in the tenth table@>

@ The formula's own truth table on $(x_6,x_8,x_9,x_{10},x_{12})$ must agree with
the tenth table wherever that table is not a star.
@<Show how the formula fills in the tenth table@>=
m := fives[9]
var full []byte
for t := 0; t < 32; t++ {
	var row uint32
	for q, j := range members(m) {
		row |= uint32(t>>(4-q)&1) << j
	}
	full = append(full, "01"[b2i(bookChain.eval(row))])
}
tenth, ok := strings.ReplaceAll(printedRight[3], " ", ""), true
for t := range 32 {
	ok = ok && (tenth[t] == '*' || tenth[t] == full[t])
}
fmt.Printf("on %s the formula's table is %s\n", setName(m), full)
fmt.Printf("  the printed tenth table is        %s; consistent: %v\n",
	tenth, ok)

@* Why five steps cannot do: the argument.
Suppose some chain of at most five steps agrees with Table~2, and take a
shortest one, of $r$ steps. By Section 7.1.2 we may take it normal, with a
complement at the end if need be. Then:

\item{(i)} $r>0$, because no covering set has fewer than five elements.

\item{(ii)} Every step but the last is used by a later step, or it could be
deleted; no step uses a trivial operation ($0$, $a$, or~$b$), or it could be
bypassed.

\item{(iii)} The $2r$ operand slots include at least $r-1$ references to
steps, hence at most $r+1$ to inputs. The inputs that occur form a covering
set, since the output depends on nothing else.

\item{(iv)} So either the chain reads at most five variables---and then
exactly five, one of the twelve sets---or $r=5$ and it reads six. In that
second case all ten slots are spoken for: each variable is read once and each
step is used once. The chain is a {\it read-once formula}.

\smallskip\noindent
Both searches below rest on (iv). The exhaustive one looks at every chain of at
most five steps on each of the twelve sets, and at every read-once formula
on each of the 994 covering sets of six; the \.{SAT} one sets up the clauses of
answer~477 for the same two families. They share nothing else.

@* Exhaustive search.
On five variables a function is a 32-bit truth table, on six a 64-bit one;
|varTable| gives the table of variable~$q$ of~$w$, the first leading, which is
the convention of |ttIndex|. A covering set turns Table~2 into a partial
table: |care| marks the positions that are specified and |want| holds their
values.
@<Functions@>=
func varTable(q, w int) uint64 {
	var v uint64
	for t := 0; t < 1<<w; t++ {
		if t>>(w-1-q)&1 == 1 {
			v |= 1 << t
		}
	}
	return v
}

func target(m uint32) (care, want uint64) {
	for _, p := range points {
		t := ttIndex(p.x, m)
		care |= 1 << t
		if p.val {
			want |= 1 << t
		}
	}
	return
}

@ A table |v| fits when it agrees with |want| on all of |care|, or disagrees
on all of it; the second case is the complemented output.
@<Functions@>=
var normalOps = [5]uint8{0x8, 0x4, 0x2, 0x6, 0xe}

func apply(op uint8, a, b uint64) (v uint64) {
	for i, w := range [4]uint64{^a &^ b, ^a & b, a &^ b, a & b} {
		if op>>i&1 == 1 {
			v |= w
		}
	}
	return
}

func fits(v, care, want uint64) bool {
	d := (v ^ want) & care
	return d == 0 || d == care
}

@ Here is the search on five variables. It returns the fewest steps of any
chain of at most |limit| steps that fits, or $-1$. It deepens one step at a
time, so an easy target is found quickly. At each depth the last step is not
built but only tested, all pairs and all five operations; the earlier steps are
built, except that a step whose table is already present is skipped, since it
could be deleted.
@<Functions@>=
func cheapest(care, want uint64, limit int) int {
	nodes := make([]uint64, 0, 5+limit)
	for q := range 5 {
		nodes = append(nodes, varTable(q, 5))
		if fits(nodes[q], care, want) {
			return 0
		}
	}
	for depth := 1; depth <= limit; depth++ {
		if extend(nodes, depth-1, care, want) {
			return depth
		}
	}
	return -1
}

@ @<Functions@>=
func extend(nodes []uint64, more int, care, want uint64) bool {
	L := len(nodes)
	for k := 1; k < L; k++ {
		for j := 0; j < k; j++ {
			for _, op := range normalOps {
				v := apply(op, nodes[j], nodes[k])
				if more == 0 {
					if fits(v, care, want) {
						return true
					}
				} else if !slices.Contains(nodes, v) &&
					extend(append(nodes, v), more-1, care, want) {
					return true
				}
			}
		}
	}
	return false
}

@ The twelve sets are independent, so they run side by side.
@<Rule out five steps by exhaustive search@>=
start := time.Now()
cost := make([]int, len(fives))
var wg sync.WaitGroup
for i, m := range fives {
	wg.Add(1)
	go func() {
		defer wg.Done()
		care, want := target(m)
		cost[i] = cheapest(care, want, 5)
	}()
}
wg.Wait()
fmt.Printf("fewest steps of at most five on the twelve sets (-1 if none): "+
	"%v, %.1fs\n", cost, time.Since(start).Seconds())
@<Rule out read-once formulas on six variables@>

@ A normal read-once function on a set $S$ of variables is a single variable,
or $a\circ b$ with $a$ and $b$ normal read-once functions on the two parts of a
split of~$S$ and $\circ$ one of the five nontrivial normal operations. The
smallest variable of~$S$ goes to the first part; the order of the operands
does not matter, since $a\land\bar b$ and $\bar a\land b$ are both there.
@<Functions@>=
func readOnce(S uint, memo map[uint]map[uint64]bool) map[uint64]bool {
	if r, ok := memo[S]; ok {
		return r
	}
	r := map[uint64]bool{}
	if bits.OnesCount(S) == 1 {
		r[varTable(bits.TrailingZeros(S), 6)] = true
	} else {
		low := S & -S
		rest := S &^ low
		for A := rest; ; A = (A - 1) & rest {
			@<Combine the read-once functions on |low|$\,\cup\,$|A| and on
			  the rest@>
			if A == 0 {
				break
			}
		}
	}
	memo[S] = r
	return r
}

@ @<Combine the read-once functions on |low|...@>=
if B := S &^ (low | A); B != 0 {
	for a := range readOnce(low|A, memo) {
		for b := range readOnce(B, memo) {
			for _, op := range normalOps {
				r[apply(op, a, b)] = true
			}
		}
	}
}

@ @<Rule out read-once formulas on six variables@>=
start = time.Now()
all := readOnce(63, map[uint]map[uint64]bool{})
sixes, matches := 0, 0
for m := uint32(0); m < 1<<20; m++ {
	if bits.OnesCount32(m) == 6 && covering(m) {
		sixes++
		care, want := target(m)
		for v := range all {
			if fits(v, care, want) {
				matches++
			}
		}
	}
}
fmt.Printf("%d read-once functions of six variables, %d covering six-sets, "+
	"%d fits, %.1fs\n", len(all), sixes, matches, time.Since(start).Seconds())

@* The SAT route.
An instance is what a chain has to match: |n| inputs, and a list of rows, input
$q$ being bit $q$ of the row, each with its wanted value.
@<Types@>=
type instance struct {
	n    int
	rows []uint32
	want []bool
}

@ Restricting Table~2 to a covering set gives such an instance, input $q$ being
the $q$th smallest variable of the set. Points that restrict to the same row
are kept once.
@<Functions@>=
func instanceOn(m uint32) instance {
	js := members(m)
	in := instance{n: len(js)}
	seen := map[uint32]bool{}
	for _, p := range points {
		var row uint32
		for q, j := range js {
			row |= (p.x >> j & 1) << q
		}
		if !seen[row] {
			seen[row] = true
			in.rows = append(in.rows, row)
			in.want = append(in.want, p.val)
		}
	}
	return in
}

@ Answer 477 uses a variable $x_{it}$ for the value of step~$i$ at row~$t$, a
variable $s_{ijk}$ saying that step~$i$ has operands $j$ and~$k$, and variables
$f_{ipq}$ for its operation at $(p,q)\ne(0,0)$. I add one more, |comp|, for a
complemented output, because a partial function need not be matched by a normal
function itself. Nodes are numbered from~0 here too.
@<Functions@>=
func solveChain(in instance, r int) (sat.Status, *chain, sat.Stats) {
	s := sat.New()
	n, P, N := in.n, len(in.rows), in.n+r
	@<Create the variables of answer 477@>
	for i := n; i < N; i++ {
		var some []sat.Lit
		for k := 1; k < i; k++ {
			for j := 0; j < k; j++ {
				some = append(some, sel[i][j][k])
				@<Emit the main clauses for $s_{ijk}$@>
			}
		}
		s.AddClause(some...)
	}
	@<Emit the optional clauses of answers 477 and 478@>
	@<Emit the output clauses@>
	st, err := s.Solve(context.Background())
	if err != nil {
		panic(err)
	}
	if st != sat.Sat {
		return st, nil, s.Stats()
	}
	@<Read the chain off the solution@>
	return st, ch, s.Stats()
}

@ @<Create the variables of answer 477@>=
x := make([][]sat.Lit, N)
f := make([][4]sat.Lit, N)
sel := make([][][]sat.Lit, N)
for i := n; i < N; i++ {
	x[i] = make([]sat.Lit, P)
	for t := range P {
		x[i][t] = s.NewVar()
	}
	for pq := 1; pq < 4; pq++ {
		f[i][pq] = s.NewVar()
	}
	sel[i] = make([][]sat.Lit, i)
	for j := range i {
		sel[i][j] = make([]sat.Lit, i)
		for k := j + 1; k < i; k++ {
			sel[i][j][k] = s.NewVar()
		}
	}
}
comp := s.NewVar()

@ The literal $(x\oplus a)$ of answer~477 is true when $x\ne a$.
@<Functions@>=
func differs(l sat.Lit, a int) sat.Lit {
	if a == 1 {
		return l.Not()
	}
	return l
}

@ The main clauses are $(\bar s_{ijk}\lor(x_{it}\oplus a)\lor(x_{jt}\oplus b)
\lor(x_{kt}\oplus c)\lor(f_{ibc}\oplus\bar a))$. When $b=c=0$ the last literal
is false, and when also $a=0$ the clause is dropped. When an operand is an
input its value is known: a true literal drops the clause and a false one is
left out, just as the answer says.
@<Emit the main clauses for $s_{ijk}$@>=
for t := range P {
	for a := range 2 {
		for bc := range 4 {
			if a == 0 && bc == 0 {
				continue
			}
			cl := []sat.Lit{sel[i][j][k].Not(), differs(x[i][t], a)}
			@<Add the operand literals, or skip the clause@>
			if bc != 0 {
				cl = append(cl, differs(f[i][bc], 1-a))
			}
			s.AddClause(cl...)
		}
	}
}

@ @<Add the operand literals, or skip the clause@>=
satisfied := false
for _, o := range [2][2]int{{j, bc >> 1}, {k, bc & 1}} {
	if o[0] >= n {
		cl = append(cl, differs(x[o[0]][t], o[1]))
	} else if int(in.rows[t]>>o[0]&1) != o[1] {
		satisfied = true
	}
}
if satisfied {
	continue
}

@ @<Emit the output clauses@>=
for t := range P {
	if in.want[t] {
		s.AddClause(x[N-1][t], comp)
		s.AddClause(x[N-1][t].Not(), comp.Not())
	} else {
		s.AddClause(x[N-1][t], comp.Not())
		s.AddClause(x[N-1][t].Not(), comp)
	}
}

@ Answers 477 and 478 add clauses that are not needed for correctness but cut
the search down enormously; without them the six-step question on a single
five-set did not finish in a minute. They must not cut off every shortest chain,
and they don't. Take a shortest chain, and among those one whose operand
indices have the smallest sum. By (ii) it uses every step and no trivial
operation. It never has a step $i'$ with operands $j$ and~$i$ where step~$i$
already uses~$j$: that step is a function of $j$ and $i$'s other operand~$k$,
so it can be recomputed from $j$ and~$k$, which lowers the sum. Finally, to put
the operand pairs in colex order whenever step $i+1$ does not use step~$i$,
renumber the steps greedily, always taking next the step with the colex-least
pair among those whose operands are already placed: if step $i+1$ does not use
step~$i$ it was available when step~$i$ was chosen. Renumbering changes none of
the other properties, which do not depend on the numbering.
@<Emit the optional clauses of answers 477 and 478@>=
for i := n; i < N; i++ {
	s.AddClause(f[i][1], f[i][2], f[i][3])
	s.AddClause(f[i][1], f[i][2].Not(), f[i][3].Not())
	s.AddClause(f[i][1].Not(), f[i][2], f[i][3].Not())
	if i < N-1 {
		@<Step |i| is used by a later step@>
	}
	for k := 1; k < i; k++ {
		for j := 0; j < k; j++ {
			@<Forbid reapplied operands and colex inversions after $s_{ijk}$@>
		}
	}
}

@ @<Step |i| is used by a later step@>=
var used []sat.Lit
for ii := i + 1; ii < N; ii++ {
	for j := 0; j < i; j++ {
		used = append(used, sel[ii][j][i])
	}
	for k := i + 1; k < ii; k++ {
		used = append(used, sel[ii][i][k])
	}
}
s.AddClause(used...)

@ @<Forbid reapplied operands...@>=
for ii := i + 1; ii < N; ii++ {
	s.AddClause(sel[i][j][k].Not(), sel[ii][j][i].Not())
	s.AddClause(sel[i][j][k].Not(), sel[ii][k][i].Not())
}
if i+1 < N {
	for kk := 1; kk < i && kk <= k; kk++ {
		for jj := 0; jj < kk && (kk < k || jj < j); jj++ {
			s.AddClause(sel[i][j][k].Not(), sel[i+1][jj][kk].Not())
		}
	}
}

@ Any selected pair will do: every selected pair's clauses hold.
@<Read the chain off the solution@>=
ch := &chain{n: n, comp: s.Value(comp)}
for i := n; i < N; i++ {
	st := step{j: -1}
	for k := 1; k < i && st.j < 0; k++ {
		for j := 0; j < k && st.j < 0; j++ {
			if s.Value(sel[i][j][k]) {
				st.j, st.k = j, k
			}
		}
	}
	for pq := 1; pq < 4; pq++ {
		if s.Value(f[i][pq]) {
			st.op |= 1 << pq
		}
	}
	ch.steps = append(ch.steps, st)
}

@ On each of the twelve sets I ask for chains of $r=1,2,\ldots,6$ steps. By (i)
and (ii) the clauses are exact for $r\ge1$, so five \.{UNSAT}s rule out five
steps; the sixth run says whether six will do, and a chain it finds is checked
against all thirty-two points of Table~2, not only against the clauses.
@<Rule out five steps, and find six, with the \.{SAT} solver@>=
start := time.Now()
var mems uint64
for i, m := range fives {
	in := instanceOn(m)
	var names []string
	for _, j := range members(m) {
		names = append(names, fmt.Sprintf("x%d", j+1))
	}
	var sts []sat.Status
	found := ""
	for r := 1; r <= 6; r++ {
		st, ch, stats := solveChain(in, r)
		mems += stats.Mems
		sts = append(sts, st)
		@<If a chain was found, check it on Table 2 and describe it@>
	}
	fmt.Printf("%2d %-16s r=1..6: %v\n%s", i+1, setName(m), sts, found)
}
fmt.Printf("twelve sets: %d megamems, %.1fs\n", mems/1000000,
	time.Since(start).Seconds())
@<Rule out five steps on the six-sets with the \.{SAT} solver@>

@ @<If a chain was found, check it on Table 2 and describe it@>=
if ch != nil {
	agree := 0
	for _, p := range points {
		var row uint32
		for q, j := range members(m) {
			row |= (p.x >> j & 1) << q
		}
		if ch.eval(row) == p.val {
			agree++
		}
	}
	out := ""
	if ch.comp {
		out = ", output complemented"
	}
	found = fmt.Sprintf("   agrees at %d points: %s%s\n", agree,
		ch.format(names), out)
}

@ By (iv) the six-sets only need $r=5$. This is the slow part: 994 instances,
each an \.{UNSAT} proof, and together almost six minutes.
@<Rule out five steps on the six-sets with the \.{SAT} solver@>=
start, mems = time.Now(), 0
sixes, satisfiable := 0, 0
for m := uint32(0); m < 1<<20; m++ {
	if bits.OnesCount32(m) == 6 && covering(m) {
		sixes++
		st, _, stats := solveChain(instanceOn(m), 5)
		mems += stats.Mems
		if st != sat.Unsat {
			satisfiable++
		}
	}
}
fmt.Printf("%d covering six-sets, %d not UNSAT with five steps: "+
	"%d megamems, %.1fs\n", sixes, satisfiable, mems/1000000,
	time.Since(start).Seconds())

@ Why go through the covering sets at all, when answer 477 could be given all
twenty variables at once? Because it does not finish. With every optional
clause in place, the \.{direct} mode runs $r=1,2,\ldots$ on the whole of
Table~2, and the cost grows more than a hundredfold a step.
@<Try answer 477 on all twenty variables@>=
in := instance{n: 20}
for _, p := range points {
	in.rows = append(in.rows, p.x)
	in.want = append(in.want, p.val)
}
for r := 1; r <= *maxSteps; r++ {
	start := time.Now()
	st, _, stats := solveChain(in, r)
	fmt.Printf("all twenty variables, r=%d: %v, %d megamems, %.1fs\n", r, st,
		stats.Mems/1000000, time.Since(start).Seconds())
}

@* Self-test.
Two searches that report nothing but ``no'' need a check that they can say
``yes.'' So I build random chains of up to five steps on five variables, using
any of the ten nontrivial operations, hide a random third of the truth table,
and ask both searches for the fewest steps. They must agree, and neither may
exceed the chain that was built. A target that one variable already fits is
left to |cheapest| alone: with nontrivial operations forced, the clauses cannot
express a zero-step chain, as answer 477 warns.
@<Test the two searches against each other@>=
rng := rand.New(rand.NewPCG(57, 2026))
nontrivial := []uint8{1, 2, 4, 6, 7, 8, 9, 11, 13, 14}
agreed, trivial := 0, 0
for left := *trials; left > 0; {
	@<Build a random chain and a random partial table@>
	left--
	ex := cheapest(care, want, 5)
	if ex == 0 {
		trivial++
		continue
	}
	@<Find the fewest steps with the \.{SAT} solver and compare@>
}
fmt.Printf("random chains: %d agreed, %d fit by a variable, of %d\n",
	agreed, trivial, *trials)
@<Test the read-once functions against random formulas@>

@ @<Build a random chain and a random partial table@>=
steps := 1 + rng.IntN(5)
nodes := []uint64{}
for q := range 5 {
	nodes = append(nodes, varTable(q, 5))
}
for range steps {
	k := 1 + rng.IntN(len(nodes)-1)
	j := rng.IntN(k)
	op := nontrivial[rng.IntN(len(nontrivial))]
	nodes = append(nodes, apply(op, nodes[j], nodes[k])&0xffffffff)
}
want := nodes[len(nodes)-1]
var care uint64
for t := range 32 {
	if rng.IntN(3) != 0 {
		care |= 1 << t
	}
}
if want&care == 0 || want&care == care {
	continue
}

@ @<Find the fewest steps with the \.{SAT} solver and compare@>=
var in instance
for t := range 32 {
	if care>>t&1 == 1 {
		var row uint32
		for q := range 5 {
			row |= uint32(t>>(4-q)&1) << q
		}
		in.rows = append(in.rows, row)
		in.want = append(in.want, want>>t&1 == 1)
	}
}
in.n = 5
viaSAT := -1
for r := 1; r <= steps && viaSAT < 0; r++ {
	if st, _, _ := solveChain(in, r); st == sat.Sat {
		viaSAT = r
	}
}
if ex == viaSAT && ex <= steps {
	agreed++
} else {
	fmt.Printf("DISAGREE: built with %d steps, exhaustive %d, SAT %d\n",
		steps, ex, viaSAT)
}

@ The read-once functions get a check of their own, built a different way: put
six variables in a pool, and repeatedly replace two of them by a random
nontrivial combination until one is left. Complemented if need be, so that it
takes $(0,\ldots,0)$ to~0, the result must be in the list.
@<Test the read-once functions against random formulas@>=
all := readOnce(63, map[uint]map[uint64]bool{})
found := 0
for range *trials {
	pool := []uint64{}
	for q := range 6 {
		pool = append(pool, varTable(q, 6))
	}
	for len(pool) > 1 {
		a := rng.IntN(len(pool))
		b := (a + 1 + rng.IntN(len(pool)-1)) % len(pool)
		op := nontrivial[rng.IntN(len(nontrivial))]
		v := apply(op, pool[a], pool[b])
		pool[min(a, b)] = v
		pool = slices.Delete(pool, max(a, b), max(a, b)+1)
	}
	if pool[0]&1 == 1 {
		pool[0] = ^pool[0]
	}
	if all[pool[0]] {
		found++
	}
}
fmt.Printf("random read-once formulas found in the list: %d of %d\n",
	found, *trials)

@* Index.
