# TAOCP 7.2.2.2, Exercise 212: A Careful Reading

Written 16 September 2026, against Volume 4B, Addison-Wesley, first printing,
2022, and the errata file as of that date, which has no entry for exercises
204–212 or their answers.

This is one reader's response to the request on Knuth's [news
page](https://www-cs-faculty.stanford.edu/~knuth/news.html): read an exercise
and its answer very carefully, then report back.

## What I found

| Item | Finding |
| --- | --- |
| Exercise 212(a) (statement) | **Needs one more condition.** As worded, *r* and *c* only allow symbols; the tensor requires them. |
| Exercise 212(b)–(d) (statement) | No error. |
| Answer 212(a) | Right, once *r* and *c* say which symbols must occur. |
| Answer 212(b) | Confirmed. The smallest such examples have *n* = 2. |
| Answer 212(c) | Confirmed. |
| Answer 212(d) | **Wrong as printed:** in the rule for *rᵢₖ* = *cᵢₖ* = 1, "*k* = (*I*, *J*, *K*′)" must be "*k* = *K*′". As printed, no instance has a solution. With that change, solutions correspond one to one with colorings. |
| Answer 211, which 212 continues | Confirmed, with two remarks: the closing example's second "⟺" holds only from left to right, and the names *jk* assume four different clauses, which answer 208 does not promise. |
| Answers 204(a), 207, 208, on which 211 rests | Confirmed. |

The reduction is right in substance, and the composed chain works: a 3SAT
problem becomes a partial latin square of 12,288 rows, the `sat` package solves
it, and the solution decodes back to a solution of the clauses. One symbol in
answer 212(d) keeps it from working as printed.

## 1. What the exercises ask

Exercise 211 (Irving and Jerrum) asks to use exercise 208 to reduce 3SAT to
list coloring of the grid `K_N □ K_3`. Exercise 212 continues:

> Given three *n* × *n* binary matrices (*rᵢₖ*), (*cⱼₖ*), (*pᵢⱼ*), the task is
> to construct an *n* × *n* array (*Xᵢⱼ*) such that *Xᵢⱼ* is blank when
> *pᵢⱼ* = 0, otherwise *Xᵢⱼ* = *k* for some *k* with *rᵢₖ* = *cⱼₖ* = 1;
> furthermore the nonblank entries must be distinct in each row and column.

Part (a) asks to show that this is the binary *n* × *n* × *n* contingency
problem, `x_*jk = c_jk`, `x_i*k = r_ik`, `x_ij* = p_ij`, where ∗ marks the
summed index. Part (b) asks for a small example where `c_*k = r_*k`,
`c_j* = p_*j`, `r_i* = p_i*` is not sufficient. Part (c) reduces `K_M □ K_N`
list coloring to `K_N □ K_N`. Part (d) reduces `K_N □ K_N` list coloring to an
*n* × *n* partial latin square with *n* = *N* + Σ|*L*(*I*, *J*)|.

## 2. How it is checked

Every problem in the chain is an exact cover problem when it is small, so the
program counts solutions by exact cover wherever the sizes allow, and compares
counts, not just yes or no. The exact covers are solved with
[`dancing-cells`](https://github.com/sjnam/dancing-cells), the package behind
the companion readings of §7.2.2.1, so these counts check it as well: its XCC
engine where one cover or every cover is wanted, and its ZDD engine where only
the number is, since a grid for six variables can have close to a million
colorings. Where the sizes do not allow it, the `sat` package decides, and
every solution it returns is decoded back one step, or all the way to the
clauses, and checked against the definitions. Each construction the answers
describe in the forward direction is also carried out by hand, from a solution
to a solution, without a solver.

## 3. The ladder: answers 204(a), 207, 208

Answer 211 starts from answer 208, so the program checks the steps below it
first.

| Check | Result |
| --- | --- |
| 204(a): (*x*₁ ∨ *x*₁ ∨ *x̄*₂) becomes (*X*₁ ∨ *X*₂ ∨ *X*₃), (*X̄*₁ ∨ *X*₂), (*X̄*₂ ∨ *X*₁), (*X*₃ ∨ *X̄*₃) | as printed |
| 207: *C*(*x*, *y*, *z*; *a*, *b*, *c*) is satisfiable exactly when *x* ∨ *y* ∨ *z* | confirmed |
| 207: the twenty clauses use each of 30 literals twice and are unsatisfiable | confirmed |
| 207: the note's sixteen clauses use each of 12 variables four times and are unsatisfiable | confirmed |
| 208: 23*m* clauses before padding, 28*m* after, 21*m* variables, every literal twice | 200 transformations, 0 exceptions |
| 208: satisfiable exactly when the original is (the result decided by the package) | 0 exceptions |
| 208: the padding is satisfied when all *uᵢ* are equal | 0 exceptions |

Answer 208 relies on something it does not say: when one of the twenty clauses
is left out, the other nineteen are satisfiable and every solution falsifies
the missing clause. That holds for each of the twenty choices. When *m* is odd,
"subscripts mod 3*m*" leaves open whether *u*′₃ⱼ₊₁ takes the parity of 3*j* + 1
or of its residue; both readings work, and both are tested. The note's claim
that no twelve clauses do what the sixteen do is not checked here.

## 4. Answer 211: the grid

Colors *jk* and j̅k̅, a permutation *σ* made of 4-cycles, and lists for the
4*n* vertices *jk* and the 3*m* vertices *aₖ*, *bₖ*, *cₖ*. The program names
everything by occurrence rather than by clause, for a reason given below.

**The reduction.** The argument behind the answer does more than decide: in
column 2 the vertices *aₖ*, *bₖ*, *cₖ* use up every barred color, which forces
each variable's four vertices to agree, and column 1 of clause *k* can then be
completed in 2*tₖ* ways, where *tₖ* is the number of true literals. So the
number of colorings should be Σ over solutions of ∏ₖ 2*tₖ*.

| Check | Result |
| --- | --- |
| number of colorings, by exact cover, against Σ ∏ 2*tₖ* | 200 grids, 40 for 6 variables and the rest for 3, 0 exceptions |
| a solution colors the grid by hand, and the coloring gives it back | 0 exceptions |
| answer 207, the note's 16 clauses, and 208 of all eight 3-clauses: grids for *N* = 120, 96, 1,344 | uncolorable, by the package |
| random problems on 30 to 60 variables | 20, colorings found, checked, decoded to solutions |

**The closing example.** "(*jk*, 1) is colored *jk* ⟺ ((*jk*)*σ*, 1) is
colored (*jk*)*σ* ⟺ (*aₖ*, 1) is not colored *jk*." The first equivalence
holds, and so does the implication from the first statement to the last,
since a used color is not free. The converse fails: when *xⱼ* is true the
color *jk* is free in column 1, but a clause with more than one true literal
may give it to *bₖ* or *cₖ*. Over 32,608 colorings of small grids that happens
65,792 times with *xⱼ* positive in clause *k*, so that *jk* is on the list of
*aₖ*. "Cannot be colored *jk*" would make it an equivalence.

**Four clauses.** The names *jk* presuppose that the four occurrences of *xⱼ*
lie in four different clauses. When a variable of the original problem occurs
once, answer 204(a) gives it the clause (*Xᵢ* ∨ *X̄ᵢ*) — the book shows this
degenerate case — and answer 208 puts a cloned literal into it. The resulting
3-clause holds *Xᵢ* twice.

Naming by occurrence fixes the names, but not the choice of *σ*. Take a
clause (*x* ∨ *x̄* ∨ *l*), with *aₖ* belonging to *x*, and let *σ* take the
occurrence of *x* to the *x̄* of the same clause. Then the color *aₖ* has in
column 2 is the one it would need in column 1 when *x* is false, and the
clause behaves like (*x* ∨ *l*). For answer 208's own output this is harmless,
because the harmful order (*X* ∨ *X̄* ∨ *l*) arises only when *X* stands for a
literal that occurs once in the original problem, which can always be made
true. Elsewhere it breaks the reduction:

```text
1 1' 2, 1' 9 5', 8' 10' 7', 6 12 4, 6' 9' 10, 6' 8 12, 12 4' 6, 2' 11 9,
5' 11' 3, 2' 11' 5, 9' 3 11, 4' 7' 10, 5 1' 2, 8 12' 3', 7 8' 3', 4 10 7'
```

These sixteen clauses use each of twelve variables four times, with three
different literals in each clause, and have 90 solutions, all with *x*₁ and
*x*₂ false. With *σ* taking the *x*₁ of the first clause to its *x̄*₁, the grid
cannot be colored. With cycles that never step inside a clause, it can.

| Check | Result |
| --- | --- |
| answer 208 of problems in which a variable occurs once contains (*X* ∨ *X̄* ∨ *l*) | 20 of 20 |
| their grids, with random cycles (68 of 80 stepping inside a clause) | colorable exactly when satisfiable |
| the sixteen clauses above | as described |
| random problems allowing (*x* ∨ *x̄* ∨ *l*), cycles that leave every clause | 200, 0 exceptions |

So the answer is right for inputs whose variables lie in four different
clauses, and it stays right for answer 208's output, but only because of how
that output is built.

## 5. Answer 212(a): the tensor

"Let *xᵢⱼₖ* = 1 if and only if *Xᵢⱼ* = *k*." Then `x_ij* = p_ij` says a cell is
filled exactly when *pᵢⱼ* = 1, and `x_i*k ≤ r_ik`, `x_*jk ≤ c_jk` say the
symbols are allowed and not repeated. The tensor asks for equality, which also
says that row *i* contains every *k* with *rᵢₖ* = 1. The array problem as
worded does not ask for that. With *n* = 1, *r* = *c* = (1), and *p* = (0), the
blank array is a solution, while the tensor has none.

| Check, over all 2^(3*n*²) instances | *n* = 1 | *n* = 2 |
| --- | --- | --- |
| instances where the two readings disagree | 3 of 8 | 909 of 4,096 |
| the tensor keeps its count when *j* and *k* are exchanged | yes | yes |
| every solvable tensor meets the condition of part (b) | yes | yes |

Part (b) needs the tensor reading too: under the array reading, the same
one-cell example is solvable although `r_1* ≠ p_1*`. So the exercise means
that *r* and *c* list the symbols that must occur, as the exact cover in the
answer's note also does, with its items `Rik` and `Cjk` primary. A phrase such
as "row *i* contains *k* if and only if *rᵢₖ* = 1, and column *j* contains *k*
if and only if *cⱼₖ* = 1" would make the statement and part (a) agree.

## 6. Answer 212(b): the small example

The answer's example, *r* = *c* with rows 1100, 0110, 0011, 1001 and *p* with
rows 1010, 1100, 0101, 0011, meets the condition, has
*c*₃₁ = *c*₃₂ = *r*₁₃ = *r*₁₄ = 0 and *p*₁₃ = 1, and has no solution. Every
instance with *n* ≤ 3 was tried:

| *n* | meet the condition | have no solution |
| --- | --- | --- |
| 1 | 2 | 0 |
| 2 | 38 | 4 |
| 3 | 17,984 | 7,272 |

The first at *n* = 2 is *r* = *c* = *p* with rows 01, 10: cell (1, 2) may hold
only symbol 2 by its row and only symbol 1 by its column.

## 7. Answer 212(c): the extension

Rows *M* + 1 to *N* get full lists, and Theorem 7.5.1L extends a latin
rectangle to a latin square. The answer takes the colors to be 1, …, *N*, as
answer 211 provides.

| Check | Result |
| --- | --- |
| random grids up to 5 × 5, colored by exact cover before and after | 2,000, 1,168 colorable, 0 disagreements |
| random latin rectangles up to 29 × 30, extended by bipartite matching | 2,000, 0 failures |

## 8. Answer 212(d): the square

The answer indexes rows, columns, and symbols by
{1, …, *N*} ∪ ⋃{(*I*, *J*, *K*) | *K* ∈ *L*(*I*, *J*)}, calls (*I*, *J*, *K*) a
header when *K* = min *L*(*I*, *J*), and defines *p*, and *r* = *c*, by rules
(i)–(iii) and (i)–(ii).

**As printed it cannot work.** Take a header *h* = (*I*, *J*, *K*). Rule (ii)
for *p* makes `p_hJ = 1`, so the cell (*h*, *J*) must hold a symbol *k*. It
needs `r_hk = 1`, which by rule (ii) for *r* makes *k* an element
(*I*, *J*, *K*′), and `c_Jk = 1`, which by rule (i) makes *k* one of the
integers 1, …, *N*. No symbol is both. The cell (*I*, *h*) fails the same way.

**With *k* = *K*′ it works.** Row *h* then holds the symbols of *L*(*I*, *J*)
in its cells (*h*, *J*) and (*h*, *e*) for the nonheaders *e*; column *h* holds
them in (*I*, *h*) and (*e*, *h*); and each nonheader *e* = (*I*, *J*, *K*) has
two cells in its row and two in its column for its two symbols, *K* and its
predecessor in the list. That forces `X_he = X_eh`, hence `X_hJ = X_Ih`, which
is the color of (*I*, *J*); rows *I* and columns *J*
of the square then carry the list coloring. Conversely a color fills the
gadget in exactly one way.

| Check, on 2,000 random grids up to 3 × 3 | Result |
| --- | --- |
| *n* = *N* + Σ\|*L*(*I*, *J*)\| | every time |
| as printed: squares with a solution | 0; with nonempty lists, some (*h*, *J*) has no symbol |
| with *k* = *K*′: tensor solutions against colorings (967 colorable) | equal in number every time |
| every coloring fills the square by hand; every solution decodes to a coloring | 0 exceptions |
| with *k* = *K*′, under the array reading of section 5 | equal when no list is empty; differ in 437 of 557 grids with an empty list |

The last row repeats the point of section 5 from the other side: under the
array reading the construction fails only when some list is empty, which a
reduction can test for first.

## 9. The whole chain, with the `sat` package

A 3SAT problem on three variables, each occurring four times, becomes the
lists of answer 211 for `K_24 □ K_3`, then the lists of answer 212(c) for
`K_24 □ K_24`, then the square of answer 212(d) read with *k* = *K*′: for the
last of the three problems, *n* = 12,288, with 94,656 possible triples and
801,804 clauses. The package solves each square. Each solution decodes to a
coloring of `K_24 □ K_24`, whose first three rows decode to an assignment that
satisfies the clauses. In the other direction, without the package, a solution
of the clauses colors the grid by hand, bipartite matching extends it to a
latin square, and the gadgets fill the partial latin square, which is checked
against the definition.

An unsatisfiable problem of this kind needs at least sixteen clauses, by the
note in answer 207 (not checked here), and would make *n* about 857,000. So
the chain from grid to square is also run on 50 random lists for `K_4 □ K_3`
to `K_6 □ K_3`, 9 of them colorable; the package's verdict on each square
agrees with exact cover on the grid, and its solutions decode.

The package needed no change for this reading.

## 10. Running it

```sh
cd taocp-7.2.2.2-exercises && make
cd 212/verify
./verify                      # every claim, in about ten seconds
./verify -mode ladder         # answers 204(a), 207, 208
./verify -mode grid           # answer 211
./verify -mode tensor         # answer 212(a), both readings
./verify -mode small          # answer 212(b), and the smallest examples
./verify -mode extend         # answer 212(c)
./verify -mode square         # answer 212(d), as printed and with k = K'
./verify -mode whole          # from 3SAT to a partial latin square
```

## References

Donald E. Knuth, *The Art of Computer Programming*, Volume 4B (Addison-Wesley,
2022), §7.2.2.2: exercises 204–209 on p. 334 and 210–212 on p. 335; answers
204 on p. 587, 207 and 208 on p. 588, 211 and 212 on p. 589. Answer 212 cites
R. W. Irving and M. Jerrum, *SIAM Journal on Computing* **23** (1994),
170–184; answer 207 cites K. Iwama and K. Takaki, *DIMACS Series* **35**
(1997), 315–333.
