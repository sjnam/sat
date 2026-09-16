# TAOCP 7.2.2.2, Exercises 442–444: A Careful Reading

Written 16 September 2026, against Volume 4B, Addison-Wesley, first printing,
2022, and the errata file as of that date, which has no entry for these three
exercises, for their answers, or for the pages they live on.

This is one reader's response to the request on Knuth's [news
page](https://www-cs-faculty.stanford.edu/~knuth/news.html): read an exercise
and its answer very carefully, then report back.

## What I found

| Item | Finding |
| --- | --- |
| Exercise 442 (statement) | No error. |
| Answer 442(a)–(e) | All confirmed. |
| Answer 442(f), the procedure *Pₖ* | Needs one more line: it must begin by applying *Pₖ*₋₁ to *F* itself. |
| Answer 442(f), "in the latter case, every literal is in *Lₖ*" | True for *k* ≥ 2, false for *k* = 1. |
| Exercise 443 (statement) | No error. |
| Answer 443(a)–(f) | All confirmed; the witnesses in (a) go on past *k* = 3. |
| Exercise 444 (statement) | Its "if and only if" holds under one reading of step E2 and fails under the other. |
| Answer 444(a)–(d) | No error. Its proof of (c) speaks of unsatisfiable *F*, and every counterexample found is satisfiable. |
| p. 289, "the examples in exercises 439–444" | Those three exercises contain no representations; 431–441 do. |
| p. 702, "Propagation completeness (UC₁)" | Propagation completeness is PC₁. |

Nothing in the three answers is wrong. Two sentences, though, say a little less
than they need to, and both are about the same thing: what happens at the edge
of a definition, where a quantifier runs out of room.

## 1. What the exercises ask

Exercise 442 generalizes unit propagation. For a family *F* of clauses and a
literal *l*, writing *L*ᵨ⁻ = {*l*₁, …, *l*ᵨ₋₁, *l̄*ᵨ} for a sequence of
literals,

- *F* ⊢₀ *l* ⟺ ε ∈ *F*;
- *F* ⊢ₖ₊₁ *l* ⟺ *F* | *L*₁⁻ ⊢ₖ ε, …, and *F* | *L*ₚ⁻ ⊢ₖ ε, for some strictly
  distinct literals *l*₁, …, *l*ₚ with *l*ₚ = *l*;
- *F* ⊢ₖ ε ⟺ *F* ⊢ₖ *l* and *F* ⊢ₖ *l̄* for some literal *l*.

Exercise 443 sorts all families into classes: *F* ∈ UCₖ when *F* | *L* ⊢ ε
implies *F* | *L* ⊢ₖ ε for every set *L* of strictly distinct literals, and
*F* ∈ PCₖ when *F* | *L* ⊢ *l* implies *F* | *L* ⊢ₖ *l*. Part (a) asks for a
proof that PC₀ ⊂ UC₀ ⊂ PC₁ ⊂ UC₁ ⊂ PC₂ ⊂ ⋯, strictly.

Exercise 444 is about SLUR, which propagates, picks a literal, looks ahead
once, and commits without ever backtracking; it answers `sat`, `unsat`, or
`maybe`. Part (c) claims that it never answers `maybe` exactly when *F* ∈ UC₁.

Two phrases in the definition of ⊢ₖ do the work. **Strictly distinct** means
that no two of *l*₁, …, *l*ₚ share a variable. And the literals **need not
occur in *F***: nothing says they do.

## 2. Computing the relation instead of trusting it

These are small objects — four clauses on three variables is already an
interesting family — so the program computes ⊢ₖ exactly as defined. A set *L*
of strictly distinct literals is the same thing as a partial assignment, and
there are 3ⁿ of those; for each one and each level *k* the program stores
{*l* | *F* | *L* ⊢ₖ *l*} and the truth of *F* | *L* ⊢ₖ ε. A prefix
(*l*₁, …, *l*ᵨ₋₁) is itself a partial assignment, so the sequences the
definition calls for are found by a breadth-first search, and the strictly
distinct rule holds itself: a prefix cannot reuse a variable it has spent.

Nothing in that is a heuristic or a shortcut. The claims are then checked
against the tables, exhaustively where the universe is small enough and on
random samples otherwise.

## 3. Exercise 442

| Part | Check | Result |
| --- | --- | --- |
| (a) ⊢₁ is unit propagation | 12,000 random families, every partial assignment | 0 disagreements |
| (b) ⊢₂ is unit propagation plus failed literals | the same | 0 disagreements |
| (c) two implications, every *k* ≤ 4 | the same | 0 exceptions |
| (d) *F* ⊢ₖ *l* implies *F* ⊢ₖ₊₁ *l* | the same | 0 exceptions |
| (e) clauses longer than *k* leave *Lₖ* empty | the same | 0 exceptions |
| (e) *Lₖ*(*R*′) | computed | ∅, ∅, ∅, {1̄, 2, 4}, {1̄, 2, 4} |
| (f) *Pₖ* finds *Lₖ* whatever the order | 36,000 runs | 0 disagreements |

The clauses *R*′ of 7.2.2.2–(7) behave exactly as answer 442(e) says. The
answer's reason checks out too: *R*′ ⊢₃ 1̄ because *R*′ | 1 ⊢₂ ε, because
*R*′ | 1 ⊢₂ 3 and *R*′ | 1 ⊢₂ 3̄. For the unsatisfiable *R* of (6), *L*₂ is
empty and *L*₃ is everything.

### The parenthesis in answer 442(f)

Answer 442(f) says that when the procedure ends in the empty clause, "every
literal is in *Lₖ*". At *k* ≥ 2 that is what the tables show. At *k* = 1 it is
not, and the reason is worth seeing. Let *F* = {2, 12̄, 1̄2̄}. Unit propagation
forces 2, then 1, then 1̄, so *F* ⊢₁ 1, *F* ⊢₁ 1̄, *F* ⊢₁ 2, and *F* ⊢₁ ε. But
no sequence of strictly distinct literals ends in 2̄: every prefix that gets
anywhere spends the variable 2 at its first step, and it cannot be spent twice.
So *L*₁(*F*) = {1, 1̄, 2}, one literal short of everything. In 36,000 runs this
happened 320 times, always at *k* = 1.

It costs the answer nothing, because part (f) handles *k* = 1 separately, by
unit propagation. It is the sentence, not the procedure, that overreaches.

### The line that answer 442(f) leaves out

The procedure itself does need a repair. As described, *Pₖ*(*F*) calls
*Pₖ*₋₁(*F* | *x*₁), *Pₖ*₋₁(*F* | *x̄*₁), *Pₖ*₋₁(*F* | *x*₂), and so on; it
never looks at *F* by itself. The recursion therefore reaches unit propagation
only if it still has variables to spend. Take *F* = {ε} on one variable and
*k* = 3. Then *P*₃ calls *P*₂(*F* | *x*₁) and *P*₂(*F* | *x̄*₁); neither has a
variable left to try, so each returns its argument rather than {ε}, and *P*₃
reports that all is well — although *F* is the empty clause.

Adding one line repairs it: *Pₖ* begins by applying *Pₖ*₋₁ to *F*. This is the
same corner of the definition as before. *F* ⊢ₖ ε implies *F* ⊢ₖ₊₁ ε precisely
*because* the witnessing literal may be one that does not occur in *F*; the
procedure, which only ever tries literals of *F*, cannot see that by itself.

With the line, 0 disagreements in 36,000 runs. Without it, a refutation is
missed 2,681 times — all of them at *k* = 3, never at *k* = 1 or *k* = 2,
since *P*₂ calls unit propagation directly and so cannot be fooled.

### The running time in part (f)

Part (f) asks for *Lₖ*(*F*) in *O*(*n*^(2*k*−1)*m*) steps. Counting one step
per clause inspected, on random families:

| | *n* = 4 | *n* = 5 | *n* = 6 | *n* = 7 | *n* = 8 |
| --- | --- | --- | --- | --- | --- |
| *k* = 2, steps ÷ *n*³*m* | 0.206 | 0.115 | 0.074 | 0.043 | 0.033 |
| *k* = 3, steps ÷ *n*⁵*m* | 0.084 | 0.041 | 0.024 | 0.012 | 0.008 |

The ratios fall as *n* grows, so the bound holds with room to spare.

## 4. Exercise 443

Every family of at most five clauses on three variables was tried — 101,583 of
them — and random families besides.

| Part | Claim | Result |
| --- | --- | --- |
| (a) | the seven witnesses are strict | confirmed, and the pattern continues to *k* = 4 |
| (b) | PC₀ is the empty family and those containing ε | 0 exceptions |
| (c) | UC₀ is the families containing all their prime clauses | 0 exceptions |
| (d) | *n* variables put *F* in PC*ₙ* | 0 exceptions |
| (e) | *n* variables need not put *F* in UC*ₙ*₋₁ | false as claimed; see below |
| (f) | *R*′ is in UC₂ but not PC₂ | confirmed |

The witnesses of part (a) come in two shapes, and the program builds them for
any *k*: the 2ᵏ clauses running through every sign pattern of the variables
1, …, *k* land in UCₖ ∖ PCₖ once the variable *k*+1 is appended to all of
them, and in PCₖ ∖ UCₖ₋₁ if *k*+1 is appended only to the all-negative one.
The answer lists them up to *k* = 3; they keep working at *k* = 4.

Part (e) is answered "false, by the examples in (c)," and the smallest
witnesses are as small as they could be: {1, 1̄} has one variable and is not in
UC₀, and {12, 12̄, 1̄2, 1̄2̄} has two variables and is not in UC₁. Both are
unsatisfiable without a single unit clause to propagate.

Part (f) places *R*′ exactly. It is in UC₂; it is not in PC₂, because
*R*′ ⊢ 1̄ semantically while *L*₂(*R*′) is empty. The answer's example —
*R*′ | 1 ⊢₂ 2 and *R*′ | 1 ⊢₂ 2̄ — checks out.

## 5. Exercise 444, and what "any literal within *F*" means

Step E2 says: "Otherwise set *l* to any literal within *F*." There are two
ways to read that, and they are not the same algorithm.

- **Narrow.** *l* is a literal that occurs in *F*.
- **Wide.** *l* is either literal of any variable that occurs in *F*.

They differ only when a variable is pure. Since step E3 tries *l* before *l̄*,
the choice decides which branch is looked at first, so under the narrow reading
a pure variable's branch order is fixed by an accident of polarity.

Part (c) claims that SLUR never answers `maybe` if and only if *F* ∈ UC₁. The
program explores every choice step E2 can make, under both readings, over
116,583 families:

| Reading | never `maybe` but not in UC₁ | in UC₁ but `maybe` possible |
| --- | --- | --- |
| Wide | **0** | **0** |
| Narrow | **335**, all satisfiable | 0 |

So the equivalence is exactly true under the wide reading, and the "only if"
direction is false under the narrow one. The smallest counterexample has four
clauses on three variables:

*F* = {23, 23̄, 2̄3, 12̄3̄}.

Here *F* | 1̄ = {23, 23̄, 2̄3, 2̄3̄} is unsatisfiable with nothing to propagate,
so *F* ∉ UC₁. The literal 1̄ does not occur in *F*, so the narrow reading never
lets step E2 commit to it, and every run ends in `sat`. The wide reading offers
1̄, SLUR takes it, and then answers `maybe`.

The answer's own proof is not touched by any of this: it says "every
unsatisfiable *F* recognized by SLUR must be in UC₁," and all 335
counterexamples are satisfiable.

The rest of exercise 444 came out as printed.

| Part | Claim | Result |
| --- | --- | --- |
| (a) | renamable Horn clauses never get a `maybe` | 0 exceptions in 116,583 families, under both readings |
| (b) | {12, 2̄3, 12̄3̄, 1̄23} is always `sat`, and not renamable Horn | confirmed |
| (d) | interleaving the two lookaheads decides the same families | 0 differences in 12,000 families |

Part (d) suggests interleaving the propagation on *F* | *l* with the one on
*F* | *l̄*, stopping as soon as a branch finishes cleanly. That can commit to
the other branch than step E3 would, but under the wide reading both
polarities are on offer anyway, so the outcomes cannot change — and they
don't. On random families the interleaving saves nothing; its point is the
worst case. Let *m* variables *y*₁, …, *yₘ* each imply the head of one
implication chain that ends in a contradiction, so that setting *yⱼ* true
forces the whole chain and setting it false forces nothing:

| | cells | forced, as written | forced, interleaved |
| --- | --- | --- | --- |
| *m* = 1 | 6 | 3 | 2 |
| *m* = 2 | 10 | 9 | 4 |
| *m* = 3 | 14 | 18 | 6 |
| *m* = 4 | 18 | 30 | 8 |

One column is quadratic in *m*, the other is 2*m*, on a family of 4*m* + 2
cells. That is what "linear time with respect to total clause length" needs.

## 6. Page 289, and one line of the index

The paragraph on page 289 that introduces *honest* representations sends the
reader to exercise 444: whenever *L* is a set of *n* literals that fully
characterizes a solution, the clauses *F* | *L* must be easy to satisfy with
SLUR. It adds that "the test is automatically passed whenever every clause of
*F* contains at most one negated auxiliary variable," and that is so: of 3,000
random families over two primary and four auxiliary variables with that
property, not one left SLUR stuck at any solution.

The condition is not vacuous either. Take *H* = {34, 34̄, 3̄4, 23̄4̄}, the
smallest family SLUR can get stuck on, guard it with a primary variable, and
let *F* = {1̄ ∨ *C* | *C* ∈ *H*}. Both values of *x*₁ leave *F* satisfiable, so
*L* = {1} characterizes a solution, and *F* | *L* is *H*, where SLUR commits to
2̄ and is lost. The clause 1̄23̄4̄ has two negated auxiliary variables — just
what the page rules out.

Two smaller things on the same subject, offered as observations rather than
corrections:

- Page 289 says "All of the examples in exercises 439–444 meet this test of
  honesty." Exercises 442, 443, and 444 contain no representations of
  constraints at all; the forcing representations are the ones in exercises
  431–441, which page 288 has just finished pointing at.
- The index entry on page 702 reads "Propagation completeness (UC₁), 360."
  On that page UC₁ is where unit propagation refutes, and PC₁ is where unit
  propagation derives every implied literal; the latter is what the literature
  Knuth cites calls propagation completeness.

## 7. What I checked before reporting this

- **The relation**, computed from its definition by search rather than by any
  propagation algorithm, so that parts (a) and (b) of exercise 442 are
  findings and not assumptions.
- **The classes**, over every partial assignment, exhaustively for every
  family of at most five clauses on three variables.
- **The satisfiability tables**, which everything else rests on, against the
  `sat` package: 363,000 calls to `Solve` with the partial assignment handed
  over as assumption literals, 0 disagreements with the exhaustive loop over
  total assignments. Every model returned was checked against the clauses and
  the assumptions, and every set reported by `Failed` was checked to be
  unsatisfiable by itself. The package needed no change for this reading.
- **The whole program**, which is one literate program, typesets without a
  single warning and runs in six seconds.

## 8. Running it

```sh
cd taocp-7.2.2.2-exercises && make
cd 442-444/verify
./verify                      # every mode, in six seconds
./verify -mode prop           # exercise 442
./verify -mode hier           # exercise 443
./verify -mode slur           # exercise 444
./verify -mode honest         # the honesty test of page 289
./verify -mode oracle         # the tables against the sat package
./verify -reps 20000          # a larger random sample
```

## References

Donald E. Knuth, *The Art of Computer Programming*, Volume 4B (Addison-Wesley,
2022), §7.2.2.2: exercises 442–444 on pp. 359–360 and their answers on
pp. 636–637; honest representations on p. 289; the clauses *R* and *R*′ in
(6) and (7) on pp. 187–188. The hierarchy is due to O. Kullmann, *Annals of
Mathematics and Artificial Intelligence* **40** (2004), 303–352, and
M. Gwynne and O. Kullmann, [arXiv:1406.7398](https://arxiv.org/abs/1406.7398)
(2014), 67 pages; the equivalence of SLUR with UC₁ is in M. Gwynne and
O. Kullmann, *Journal of Automated Reasoning* **52** (2014), 31–65. SLUR
itself is due to J. S. Schlipf, F. S. Annexstein, J. V. Franco, and
R. P. Swaminathan, *Information Processing Letters* **54** (1995), 133–137.
