# TAOCP 7.2.2.2, Exercise 363: A Careful Reading

Written 16 September 2026, against Volume 4B, Addison-Wesley, first printing,
2022, and the errata file as of that date. That file amends one line of this
exercise — part (g)'s "strict Horn clauses" became "definite Horn clauses" on
10 February 2024 — and has nothing on the answer.

This is one reader's response to the request on Knuth's [news
page](https://www-cs-faculty.stanford.edu/~knuth/news.html): read an exercise
and its answer very carefully, then report back.

## What I found

| Item | Finding |
| --- | --- |
| Exercise 363 (statement) | No error. |
| Answer 363(a), the trail of Algorithm C | Confirmed on 112 runs and 1,019 decisions. |
| Answer 363(b), the weights of *F* in (1) | Confirmed. |
| Answer 363(c), which of (i), (ii), (iii) hold | Confirmed, counterexample and all. |
| Answer 363(d), seven of the eight subsets, and *L*₇ | Confirmed, including "lower semimodular but not modular". |
| Answer 363(e), the table of 27 weights | **Every entry confirmed.** |
| Answer 363(f), the five clauses and the twelve sets | Confirmed, including the remark about {3}. |
| Answer 363(g), the clause to introduce | **Wrong as printed:** the disjunction must run over *k* ∈ *L*, not *k* ∈ *L*′. |
| Answer 363(h), (i), (j) | Confirmed. |

Nine parts out of ten are right. The tenth is a slip of one symbol, but it is
the kind that stops the construction from working at all.

## 1. What the exercise asks

A partial assignment is **stable** — Knuth also says "valid" — if it is
consistent and unit propagation cannot extend it; equivalently, if no clause is
entirely false, or entirely false except for at most one unassigned literal.
Variable *x*ₖ is **constrained** if it appears in a clause where ±*x*ₖ is true
but all the other literals are false, so that its value has a reason.

Writing *x* ≺ *x*′ when *x*′ agrees with *x* except that *x*ₖ = ∗ and
*x*′ₖ ∈ {0,1}, the exercise defines *x* ⊑ *x*′ to mean that there is a chain
*x* = *x*⁽⁰⁾ ≺ *x*⁽¹⁾ ≺ ⋯ ≺ *x*⁽ᵗ⁾ = *x*′ of **stable** assignments. Given
probabilities *p*ₖ + *q*ₖ = 1, an unstable assignment has weight 0 and any
other has

*W*(*x*) = ∏{*p*ₖ | *x*ₖ = ∗} · ∏{*q*ₖ | *x*ₖ ≠ ∗ and *x*ₖ is unconstrained}.

Ten questions follow, and this reading answers each one by computation.

## 2. How it is checked

A problem on *n* variables has 3ⁿ partial assignments, and every part of the
exercise lives at *n* ≤ 5. So the program tabulates all of them, decides
stability and constrainedness straight from the two definitions quoted above,
and then reads the answers off the table. Weights are kept as products of
symbols rather than as numbers — `q1q2`, `p1p2p3` — so that part (e) can be
compared with the book entry by entry; only part (j), an identity about sums,
uses arithmetic.

Part (a) is the exception: it is a question about a running solver, and it is
answered in section 3.

## 3. Part (a): the trail whenever Algorithm C decides

> **(a)** True or false: The partial assignment specified by the literals
> currently on the trail in step C5 of Algorithm C is stable.

The answer is "True; indeed, this is an important invariant property of
Algorithm C." It is worth noticing that Knuth's own program does not check it.
`sat13.w` carries a `sanity` routine, switched on by setting
`sanity_checking` to 1, which goes through the clauses, the watch lists, the
heap, the trail and the variables; of the trail it verifies `tloc`, `reason`,
`value` and the binary reasons, but never asks whether the assignment is
stable.

The `sat` package is a Go rendering of `SAT13`, and it had left out both the
`sanity` routine and the diagnostics that `SAT13` turns on with its `v`
option, on the ground that neither costs any mems. To answer part (a) the
package therefore grew one small hook, `SetTrace`, which hands the caller the
trail just before each decision — the moment step C5 describes — and costs
nothing when it is not used. It is the same bargain as `SetProof`, which
exercise 282 needed.

With the hook in place, this reading builds its own clauses, hands them to the
solver, and checks each trail against those same clauses from the definition:

| | |
| --- | --- |
| random 3SAT problems, 12 to 23 variables | 100 |
| *waerden*(3,3;*n*) for 9 ≤ *n* ≤ 20, all unsatisfiable | 12 |
| decisions watched | **1,019** |
| trails that were not stable | **0** |

## 4. Parts (b) and (e): the weights

Part (b) asks for the weights of the four clauses *F* of 7.2.2.2–(1), namely
{12̄, 23, 1̄3̄, 1̄2̄3}. The answer says *W*(001) = 1, *W*(∗∗∗) = *p*₁*p*₂*p*₃,
and *W*(*x*) = 0 otherwise. All 27 assignments were checked: it is so. The
first of those says that all three variables are constrained in the one
solution, which is easy to miss and easy to verify — three of the four clauses
have exactly one true literal there.

Part (e) asks for the weights when the only clause is 123. The answer prints a
table of 27 entries, and the program prints its own:

```text
x1 = 0:        0     q1q2        0     q1q3   q1q2q3   q1q2p3        0   q1p2q3   q1p2p3
x1 = 1:     q2q3   q1q2q3   q1q2p3   q1q2q3   q1q2q3   q1q2p3   q1p2q3   q1p2q3   q1p2p3
x1 = *:        0   p1q2q3   p1q2p3   p1q2q3   p1q2q3   p1q2p3   p1p2q3   p1p2q3   p1p2p3
```

with columns *x*₂*x*₃ = 00, 01, 0∗, 10, 11, 1∗, ∗0, ∗1, ∗∗. Every entry agrees
with page 619, including the three zeros in the first row, which are the
assignments where the single clause has exactly one unassigned literal left.

## 5. Part (c): complementing or erasing one value

Let *x* be stable with *x*ₖ = 1, and let *x*′ and *x*″ come from *x* by setting
*x*ₖ ← 0 and *x*ₖ ← ∗. Is "*x*ₖ is unconstrained in *x*" the same as (i) *x*′
is consistent; (ii) *x*′ is stable; (iii) *x*″ is stable?

| Statement | 87,348 cases | |
| --- | --- | --- |
| (i) *x*′ is consistent | 0 exceptions | true |
| (ii) *x*′ is stable | 14,770 exceptions | **false** |
| (iii) *x*″ is stable | 0 exceptions | true |

which is what the answer says. Its counterexample is confirmed too: with the
clause 123, *x* = 10∗ is stable and leaves *x*₁ unconstrained, and *x*′ = 00∗
is consistent but not stable, since the clause is then down to its last
unassigned literal.

## 6. Parts (d), (h), (i): the lattice

Part (d) asks for all *L* with *L* ⊑ {1, 2̄, 3̄} when the only clause is 123.
The answer: all eight subsets are stable except {2̄, 3̄}, where *x*₁ is
constrained — that is, where unit propagation would force 1 — so seven remain.
Confirmed.

The answer adds that those seven, ordered by inclusion, illustrate *L*₇, "the
smallest lattice that is lower semimodular but not modular." The program
checks all three words: the seven sets do form a lattice, it is lower
semimodular, and it is not modular.

Parts (h) and (i) are the facts that make the lattice work, and both came out
with no exceptions: 92,639 pairs of stable assignments one step below a common
stable *L* all have a stable intersection, and *L*′ ⊑ *L* together with
*L*″ ⊑ *L* always gives *L*′ ∩ *L*″ ⊑ *L*.

## 7. Part (f): twelve sets

Part (f) asks for clauses whose *L* ⊑ {1,2,3,4,5} are exactly

∅, {4}, {5}, {1,4}, {2,5}, {4,5}, {1,4,5}, {2,4,5}, {3,4,5}, {1,3,4,5},
{2,3,4,5}, {1,2,3,4,5}.

The answer offers {1̄2̄34̄5̄, 1̄4, 2̄5, 3̄45̄, 3̄4̄5}, and those five clauses give
exactly those twelve sets, no more and no fewer. The remark that follows is
also right: {3} is stable, yet it is not below {1,2,3,4,5}, because every way
of climbing out of it passes through an unstable assignment. Stability alone
is not enough to be reachable.

## 8. Part (g): one clause too wide

Part (g) starts from a family 𝓛 of subsets of {1,…,*n*}, closed under
intersection, in which every member can climb to {1,…,*n*} inside 𝓛, and asks
for definite Horn clauses with *L* ∈ 𝓛 if and only if *L* ⊑ {1,…,*n*}. The
answer is one sentence:

> **(g)** If *L* = *L*′ \ *l* and *L*′ ∈ 𝓛 but *L* ∉ 𝓛, introduce the clause
> `(x_l ∨ ⋁_{k∈L′} x̄_k)`.

The idea is right and it is the only thing that could work: where the family
stops, a clause has to make *L* unstable by forcing *l*. But the disjunction
is one element too wide. Since *L* = *L*′ \ *l*, the literal *l* belongs to
*L*′, so the clause contains *x̄*ₗ as well as *x*ₗ: it is a tautology. A
tautology is satisfied by everything, so it never makes any assignment
unstable, and in Knuth's own notation (page 187) such clauses are written ℘ and
thrown away.

Running the disjunction over *k* ∈ *L* instead gives

`(x_l ∨ ⋁_{k∈L} x̄_k)`, that is, `⋀_{k∈L} x_k ⇒ x_l`,

which is a definite Horn clause, which makes *L* unstable, and which leaves
every member of 𝓛 alone. The program builds both versions and compares:

| Family | over *k* ∈ *L* | over *k* ∈ *L*′, as printed |
| --- | --- | --- |
| the twelve sets of part (f) | 13 clauses, family rebuilt exactly | fails |
| 499 random families that need clauses | 0 failures | **all 499 fail** |

The failures are not subtle. With tautologies for clauses nothing is ever
forced, so every subset of {1,…,*n*} is stable and every one of them ends up
below {1,…,*n*} — the construction returns the whole power set instead of 𝓛.

The families used for the random test are built to satisfy the hypotheses:
random subsets are closed under intersection, then whatever cannot climb to
{1,…,*n*} is dropped, and the two steps are repeated until nothing changes.
Families for which the construction produces no clauses at all — the whole
power set — are skipped, since they cannot tell the two readings apart.

Line 3 of this part is the line the errata already amends, from "strict Horn
clauses" to "definite Horn clauses". The clause itself is on line 4.

## 9. Part (j): the sum of the weights

Part (j) asks for a proof that ∑ *W*(*x*′) = ∏{*p*ₖ | *x*ₖ = ∗} whenever *x* is
stable, the sum running over the *x*′ with *x*′ ⊑ *x* — the assignments below
*x*, not above it. With the single clause 123 and *x* = 001 the sum has seven
terms, and at *p*ₖ = *q*ₖ = 1/2 they come to 6/8 + 1/4 = 1, which is the empty
product, as it should be.

Checked over 17,635 stable assignments of random problems, with random
probabilities: 0 failures.

## 10. What I checked before reporting this

- **The definitions**, transcribed from the exercise and used directly:
  stability and constrainedness are decided clause by clause, not by running
  any propagation algorithm.
- **The weights**, kept symbolic, so that part (e) is a comparison of 27
  strings with 27 printed products rather than of floating-point numbers.
- **The solver**, for part (a), through a new hook that shows the trail. The
  package's own test suite still reproduces Knuth's mem counts exactly
  afterwards, which is the point of the port: the hook costs nothing when it
  is not used.
- **Both readings of part (g)**, on the answer's own family and on 499 random
  ones.

## 11. Running it

```sh
cd taocp-7.2.2.2-exercises && make
cd 363/verify
./verify                      # every part, in half a second
./verify -mode trail          # part (a), Algorithm C's trail
./verify -mode weights        # parts (b) and (e)
./verify -mode stable         # part (c)
./verify -mode climb          # parts (d) and (f)
./verify -mode lattice        # parts (h), (i), and L_7
./verify -mode sum            # part (j)
./verify -mode horn           # part (g), both readings
./verify -reps 20000          # a larger random sample
```

## References

Donald E. Knuth, *The Art of Computer Programming*, Volume 4B (Addison-Wesley,
2022), §7.2.2.2: exercise 363 on pp. 349–350 and its answer on pp. 619–620;
exercise 364, on covering and core assignments, on p. 350; the clauses *F* of
(1) on pp. 186–187. The weights are from E. Maneva, E. Mossel, and
M. J. Wainwright, *JACM* **54** (2007), 17:1–17:41, who show that survey
propagation is the limit as *p* → 1; the lattice is from F. Ardila and
E. Maneva, *Discrete Mathematics* **309** (2009), 3083–3091; the identity of
part (j) is what let E. Maneva and A. Sinclair, *Theoretical Computer Science*
**407** (2008), 359–369, sharpen the known bounds. Covering assignments are due
to A. Braunstein and R. Zecchina, *Journal of Statistical Mechanics* (June
2004), P06007:1–18.
