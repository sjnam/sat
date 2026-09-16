# TAOCP 7.2.2.2, Exercise 165: A Careful Reading

This is one reader's response to the request on Knuth's [news
page](https://www-cs-faculty.stanford.edu/~knuth/news.html): read an exercise
and its answer very carefully, then report back.

## What I found

| Item | Finding |
| --- | --- |
| Exercise 165 (statement) | No error. |
| The warm-up: 1, 3, 4 out by 1̄3̄4̄, then 6 by 136̄, and {2, 5} is the maximum | Confirmed, reason by reason. |
| "The union of positive autarkies is a positive autarky" | Confirmed on 103,583 families. |
| The Horn clauses and their core | Confirmed on 103,983 families against brute force. |
| "A simple variant of Algorithm 7.1.1C … in linear time" | Confirmed: at most 2*N* steps, where writing the clauses out costs quadratic time. |
| The bracketed remark about autarkies inside a given set of literals | Confirmed on 3,600 families. |

The answer is right in every sentence. This reading adds evidence rather than
corrections: brute force for small families, an implementation of the variant
of Algorithm 7.1.1C with Knuth's own data structures, and the `sat` package as
an independent judge for problems of a hundred variables.

## 1. What the exercise asks

An **autarky** for *F* is a set *A* of strictly distinct literals such that
every clause either contains a literal of *A* or contains no literal of *Ā*
(page 228). An autarky can be set true without losing satisfiability.

> **165.** [26] Design an algorithm to find the largest positive autarky *A*
> for a given *F*, namely an autarky that contains only positive literals.
> *Hint:* Warm up by finding the largest positive autarky for the clauses
> {123̄, 125̄, 1̄3̄4̄, 136̄, 14̄5, 156, 2̄35, 24̄6, 345, 3̄56}.

The bars in that list were checked glyph by glyph in the PDF, since everything
in the warm-up depends on them. In Knuth's shorthand 123̄ is the clause
(*x*₁ ∨ *x*₂ ∨ *x̄*₃).

## 2. The warm-up

Brute force over all 64 sets of variables finds exactly two positive
autarkies, ∅ and {2, 5}, so {2, 5} is the largest.

The answer also says *how* one gets there: "Clause 1̄3̄4̄ in the example tells
us that 1, 3, 4 ∉ *A*. Then 136̄ implies 6 ∉ *A*." The core algorithm of
section 4 records the clause that excludes each variable, and it reports

```text
excluded: 1 by 1'3'4', 3 by 1'3'4', 4 by 1'3'4', 6 by 136'
```

which is the answer's argument, word for word. Nothing else is excluded, so 2
and 5 remain.

The example in answer 157 — {1, 2} as an autarky of {12̄3, 1̄24, 3̄4̄} that is not
a pure literal — was checked as well: it is also the largest positive autarky
of its clauses.

## 3. Why there is a maximum

"There always is a maximum (not just maximal) positive autarky, because the
union of positive autarkies is a positive autarky." Brute force confirmed it
on every family of at most five clauses on three variables, and on random
families of up to ten variables: 103,583 families, no exception.

The word *positive* is doing real work there. For general autarkies the union
need not even be a set of strictly distinct literals, and a maximum need not
exist: {12, 1̄2̄} has the two autarkies {1, 2̄} and {1̄, 2}, each maximal.

## 4. The Horn clauses and Algorithm 7.1.1C

Write *P*ᵥ for "*v* ∉ *A*". A clause with positive variables *v*₁, …, *v*ₛ and
negative ones *v*ₛ₊₁, …, *v*ₛ₊ₜ yields the *t* definite Horn clauses
*P*ᵥ₁ ∧ ⋯ ∧ *P*ᵥₛ ⇒ *P*ᵥₛ₊ⱼ, and their core — the propositions true in every
model — is the set of variables in no positive autarky. The largest positive
autarky is everything else.

Algorithm 7.1.1C (Volume 4A, pages 59–60) computes cores with the arrays
`CONCLUSION`, `COUNT`, `TRUTH`, `LAST`, `CLAUSE`, `PREV` and a stack. The
answer's variant changes two steps: in C1, `CONCLUSION(c)` becomes the list of
the *t* negated variables, and in C5 every one of them is deduced. That is
exactly what the program implements, and nothing else is touched. A clause
with *t* = 0 yields no Horn clause but still gets its hypothesis records;
they cost a little and do no harm.

| Check | Result |
| --- | --- |
| largest positive autarky, against brute force | 103,983 families, 0 disagreements |
| steps ≤ 2*N*, *N* the total length of the clauses | 0 exceptions |

The bound 2*N* is the linear-time argument made concrete: every literal is seen
once in C1, every proposition enters the stack at most once so every hypothesis
is seen at most once in C4, and a clause's count reaches zero at most once so
every conclusion is seen at most once in C5.

The change to C1 and C5 is not a nicety. Writing the *t* Horn clauses out
costs *s*·*t* cells for a clause with *s* positive and *t* negative literals.
Take one clause (*x*ₖ₊₁ ∨ ⋯ ∨ *x*₂ₖ ∨ *x̄*₁ ∨ ⋯ ∨ *x̄*ₖ) together with the
*k* unit clauses (*x̄*ₖ₊₁), …, (*x̄*₂ₖ):

| *k* | *N* | steps, modified | steps, written out |
| --- | --- | --- | --- |
| 10 | 30 | 50 | 230 |
| 20 | 60 | 100 | 860 |
| 40 | 120 | 200 | 3,320 |
| 80 | 240 | 400 | 13,040 |
| 160 | 480 | 800 | 51,680 |

## 5. The bracketed remark

"By complementing a subset of variables, and prohibiting another subset, we can
find the largest autarky *A* contained in any given set of strictly distinct
literals." Given *S*, the program complements the variables that occur
negatively in *S*, puts the variables absent from *S* into the core at the
start, and runs the same algorithm. On 3,600 random families with random sets
*S* of up to nine literals, the result agreed with brute force over every
subset of *S* — same size, an autarky by the definition, and equal to the union
of all autarkies inside *S*.

## 6. Larger problems, with the `sat` package

Brute force stops at a dozen variables, so for problems of 60 to 139 variables
the program plants a positive autarky *H* in a random 3SAT problem, runs the
core algorithm, and asks the solver two independent questions.

**Is it the largest?** Introduce a variable *a*ᵥ meaning *v* ∈ *A*. For each
clause of *F* whose positive variables are *u*₁, …, *u*ₛ, and for each
negative literal *v̄* in it, take the clause (*ā*ᵥ ∨ *a*ᵤ₁ ∨ ⋯ ∨ *a*ᵤₛ). These
clauses are satisfied exactly by the positive autarkies. So *v*
belongs to some positive autarky if and only if they are satisfiable under the
assumption *a*ᵥ. This is a search, not a propagation, though the clauses are
dual Horn and the solver never has to work for it.

**Does the autarky principle hold?** *F* should be satisfiable if and only if
the clauses that *A* leaves untouched are, and a model of those, with *A* made
true, should satisfy *F*.

| | |
| --- | --- |
| problems | 50 |
| results that are positive autarkies by the definition | 50 |
| variables planted, and variables in the autarkies found | 1,578 and 1,587, every planted one among them |
| calls to `Solve` with an assumption, agreeing with the core | 5,166 of 5,166 |
| models returned, each a positive autarky | all |
| verdicts on *F* and on the untouched clauses | equal in all 50 (33 satisfiable, 17 not) |
| extended models that satisfy *F* | all 33 |

The package needed no change for this reading.

## 7. Running it

```sh
cd taocp-7.2.2.2-exercises && make
cd 165/verify
./verify                      # every claim, in under a second
./verify -mode warmup         # the warm-up and answer 157's example
./verify -mode union          # unions, and why positive matters
./verify -mode core           # the core algorithm against brute force
./verify -mode linear         # the modified C1 and C5 against writing out
./verify -mode within         # the bracketed remark
./verify -mode solver         # larger problems, with the sat package
```

## References

Donald E. Knuth, *The Art of Computer Programming*, Volume 4B (Addison-Wesley,
2022), §7.2.2.2: autarkies and Algorithm X on pp. 228–229; exercises 156–165
on p. 330; answers 157 and 165 on pp. 578 and 580. Volume 4A (2011), §7.1.1:
Algorithm C, "Core computation for definite Horn clauses," on pp. 59–60. The
answer credits the exercise to unpublished work of O. Kullmann, V. W. Marek,
and M. Truszczyński.
