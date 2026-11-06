# TAOCP 7.2.2.2, Exercise 518: A Careful Reading

This is one reader's response to the request on Knuth's [news
page](https://www-cs-faculty.stanford.edu/~knuth/news.html): read an exercise
and its answer very carefully, then report back. The news page describes this
one as "reduce 3SAT to testing the permanent of a {−1,0,1,2} matrix for zero".

## What I found

| Item | Finding |
| --- | --- |
| Exercise 518 (statement) | **Two hypotheses are left unsaid.** Every variable must occur in some clause, and no literal may occur twice in one clause. |
| Answer 518(a), the 6 × 6 matrix | Confirmed exactly: both sides are multilinear, so the 512 points of {0,1}⁹ settle it. |
| Answer 518(b), where the 2s fall | Confirmed on 307 random problems, in all six classes of row and column. |
| Answer 518(c), per *M* = 2^(4*m*+*n*)·*s* | Confirmed on 291 random problems, against two independent counts of *s*. |
| The headline, "zero if and only if unsatisfiable" | **Not testable head-on.** The smallest unsatisfiable instance makes *M* 51 × 51, and Ryser's formula needs 2⁵¹ terms. |

The construction works, and part (c) is stronger than the headline: the
permanent gives the number of solutions.

## 1. What the exercise asks

Given a 3SAT problem with *m* clauses and *n* variables, build a
(6*m*+*n*) × (6*m*+*n*) integer matrix *M* whose permanent is zero exactly
when the clauses are unsatisfiable. Each clause gets a copy of a fixed 6 × 6
matrix *A* with entries in {0, 1, −1}, laid along a diagonal; rows 1…*n* and
columns 6*m*+1…6*m*+*n* belong to the variables; everything else is 0 or 2.

Clause *i* has three *inputs*, the odd columns of its block, and three
*outputs*, the even rows. The 2s thread each literal through the clauses that
hold it:

> If literal *l* appears in *t* ≥ 0 clauses *i*₁ < ⋯ < *iₜ*, as element
> *j*₁, …, *jₜ*, we put '2' in column *I*ᵢₖ₊₁ⱼₖ₊₁ of row *O*ᵢₖⱼₖ for
> 0 ≤ *k* ≤ *t* (*O*ᵢ₀ⱼ is row |*l*|, *Iᵢₜ₊₁ⱼ* is column 6*m*+|*l*|).

Part (a) asks for *A*, part (b) for a census of the 2s, part (c) for the
conclusion per *M* = 2^(4*m*+*n*)·*s*, where *s* is the number of solutions.

## 2. How it is checked

Three routes that share nothing have to agree. The matrix is built from the
recipe above and nothing else. Its permanent is evaluated by Ryser's formula,
which knows no 3SAT. The number of solutions is obtained twice: by running
through all 2ⁿ assignments, and by asking the [`sat` package](../..) for one
solution at a time, blocking each as it comes. The permanent is the expensive
route, so sizes stay under `-max`, which defaults to 6*m*+*n* = 22, a few
million subsets.

## 3. Part (a): the gadget

The answer gives *A* in 2 × 2 blocks,

```text
A = | x y y |            | -1  0 |            |  1  1 |
    | y x y |  ,   x  =  |  1  0 |  ,   y  =  | -1  1 |
    | y y x |
```

so the symmetry the hint promises is a symmetry of the three clause
positions. The identity to verify is between two polynomials in
*p*, *q*, *r*, *u*, *v*, *w*, *x*, *y*, *z*. Each letter occurs in exactly one
entry of its matrix, and a permanent is a sum of products that take one entry
per row, so each side is multilinear. **A multilinear polynomial in nine
variables is determined by its values on {0,1}⁹**, so evaluating both sides at
those 512 points proves the identity. The answer's *A* passes.

Within the symmetric shape the two blocks are free, which is 3⁴ · 3⁴ = 6561
possibilities; exactly **four** of them satisfy the identity, and the answer's
is one.

## 4. Part (b): where the 2s fall

| Rows and columns | Answer 518(b) | Here |
| --- | --- | --- |
| the *n* variable rows, the *n* variable columns | twice | twice |
| the 3*m* output rows, the 3*m* input columns | once | once |
| the 3*m* input rows, the 3*m* output columns | never | never |

Checked on 307 random problems, every row and every column.

## 5. Part (c): the permanent counts solutions

| Check | Result |
| --- | --- |
| per *M* = 2^(4*m*+*n*)·*s*, random problems up to 22 × 22 | 291 problems, **0** disagreements |
| the package's enumeration against brute force | 0 disagreements, 2,600 solutions in all |

That the permanent is nonzero when the problem is solvable is the easy half.
The exact value is the stronger check: a slip anywhere in the construction
would change it.

## 6. Two hypotheses the construction needs

Neither is stated, and the identity fails without either.

**No literal twice in one clause.** The answer indexes the clauses holding a
literal as *i*₁ < ⋯ < *iₜ*, which leaves no room for two elements of the same
clause. Threading them in the order written is the obvious repair, but the
count then comes out wrong: for {1 1 2, 1̄ 2 3} the permanent is 13,312 where
2^(4*m*+*n*)·*s* is 10,240.

**Every variable occurs somewhere.** If variable *v* is in no clause, both of
its literals thread the empty chain, which is the single entry in row *v* and
column 6*m*+*v*. That row then holds one 2 instead of the two part (b)
promises, and the permanent loses a factor of 2:

| the single clause {1 2 3} | per *M* against 2^(4*m*+*n*)·*s* |
| --- | --- |
| *n* = 3 | equal |
| *n* = 4 | half |
| *n* = 5 | a quarter |

Both are mild — a repeated literal makes a clause shorter than ternary, and an
idle variable is usually dropped before counting — but part (c) is an exact
identity, and it needs them.

## 7. The example of page 188, and a limit

Equation (7) is *R* = {123̄, 234̄, 341, 41̄2, 1̄2̄3, 2̄3̄4, 3̄4̄1̄}, the little
problem the section returns to again and again. With *m* = 7 and *n* = 4 its
matrix is 46 × 46, which is the picture printed beside the exercise; the
program builds it, confirms the shape and every one of its 2s, and finds the
two solutions by both routes. So per *M* must be 2³² · 2 = 8,589,934,592 —
a number Ryser's formula cannot reach, since 2⁴⁶ terms is too many.

That limit bites harder on the headline claim. A clause of three distinct
literals forbids one eighth of the assignments, so fewer than eight clauses
always leave one standing; and over two variables every clause of three
distinct literals contains a complementary pair, hence is a tautology. An
unsatisfiable instance therefore needs *m* ≥ 8 and *n* ≥ 3, which makes *M*
at least 51 × 51. **The "zero" half of "zero if and only if unsatisfiable"
cannot be exercised by brute force at all.** So this reading tests the exact
formula wherever the permanent is computable, which checks the value itself and
not only whether it is zero.

## 8. Running it

```sh
cd taocp-7.2.2.2-exercises && make
cd 518/verify
./verify                      # every claim, in about nine seconds
./verify -mode gadget         # answer 518(a), and how unique it is
./verify -mode twos           # answer 518(b)
./verify -mode permanent      # answer 518(c), the three routes
./verify -mode limits         # the two unstated hypotheses
./verify -mode example        # the 46x46 matrix of equation (7)
./verify -max 24 -reps 2000   # a longer run
```

The package needed no change for this reading.

## References

Donald E. Knuth, *The Art of Computer Programming*, Volume 4B (Addison-Wesley,
2022), §7.2.2.2: the clauses (7) on p. 188; exercise 518 on p. 367 and its
answer on p. 653. The construction is due to A. Ben-Dor and S. Halevi,
*Israel Symposium on the Theory of Computing Systems* **2** (IEEE, 1993),
108–117. That the permanent is hard to compute even for 0–1 matrices is
L. G. Valiant, *Theoretical Computer Science* **8** (1979), 189–201; Ryser's
formula is in H. J. Ryser, *Combinatorial Mathematics* (MAA, 1963), §4.2.
