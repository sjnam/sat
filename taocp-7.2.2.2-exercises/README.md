# Careful Readings of TAOCP §7.2.2.2

Knuth's [news page](https://www-cs-faculty.stanford.edu/~knuth/news.html) asks
readers to take one exercise of *The Art of Computer Programming*, read it and
its answer very carefully, and report back. This directory holds one such
reading per exercise, written against Volume 4B, Addison-Wesley, first printing,
2022, and against the
[errata file](https://www-cs-faculty.stanford.edu/~knuth/err4b.textxt) of the
day. Section 7.2.2.2 is the satisfiability section, and the solver behind these
readings is the [`sat` package](..) in the directory above, a Go rendering of
Knuth's SAT13 whose mem counts agree with the C original.

The readings have a second purpose. Every claim a solver makes here is checked
by a route that does not use it, wherever such a route exists, so each reading
is also a test of the package.

The companion collection for §7.2.2.1 lives in the
[dancing-cells](https://github.com/sjnam/dancing-cells) repository, and these
readings follow its layout.

## The readings

These are the §7.2.2.2 exercises from the news page that have been read so
far.

| Exercise | What the news page asks | What came out |
| --- | --- | --- |
| [6](006) | Verify a certain (previously unpublished) lower bound on van der Waerden numbers W(3,k) | confirmed; the last step needs a lower bound, and holds only once ln k > 4858 |
| [57](057) | Find a 6-gate way to match a certain 20-variable Boolean function at 32 given points | confirmed, and six is the minimum |
| [165](165) | Devise an algorithm to compute the largest positive autarky of given clauses | confirmed in every sentence |
| [212](212) | Prove that partial latin square construction is NP-complete | one symbol wrong in answer 212(d); part (a) needs a stronger statement |
| [282](282) | Find a linear certificate of unsatisfiability for the flower snark clauses | confirmed to the last clause; four numbers in the surrounding text do not reproduce |
| [363](363) | Study the stable partial assignments of a satisfiability problem | confirmed, except for one clause in answer 363(g) |
| [442–444](442-444) | Study the UC and PC hierarchy of progressively harder sets of clauses | confirmed; two places decide what a phrase means |

## What came out

### Beyond the book

- **[6](006).** The Local Lemma argument is sound, and the lopsided graph it
  uses checks out exactly on short strings. Its constants, though, make
  *yd* = 24, so (1 − *y*)ᵈ tends to e⁻²⁴, and the second inequality of
  Theorem L holds only once ln *k* > 4857.97; the answer's "= *O*(1)" is also
  the wrong direction for that step, which needs a lower bound. With
  *p* = (3 ln *k*)/*k* instead of (2 ln *k*)/*k*, the same argument proves
  W(3, *k*) = Ω((*k*/log *k*)²), the bound Li and Shu published in 2010. The
  `sat` package recomputes W(3, *k*) for *k* ≤ 10.
- **[57](057).** Every statement in the answer checks out, including the
  twelve truth tables with their don't-cares. The exercise asks only for six
  operations; no chain of five or fewer matches Table 2 at all, which is shown
  both by exhaustive search and with the solver, and the two agree. Of the
  twelve five-variable tables, exactly five admit six operations; the answer's
  tenth is one of them.
- **[165](165).** The warm-up's deductions, the union argument for a
  maximum, the Horn clauses, the linear-time variant of Algorithm 7.1.1C, and
  the remark about autarkies inside a given set of literals all check out,
  against brute force for small families and, for problems of a hundred
  variables, against the `sat` package: 5,166 calls with assumptions confirm
  that the autarkies found are the largest, and the autarky principle holds on
  every one of 50 planted problems.
- **[212](212).** The chain from 3SAT to a partial latin square works, and
  the `sat` package runs it end to end: a problem on three variables becomes a
  square with 12,288 rows, and the package's solution decodes back to a
  solution of the clauses. Two places needed repair. In answer 212(d) the rule
  for *rᵢₖ* = *cᵢₖ* = 1 must read *k* = *K*′, not *k* = (*I*, *J*, *K*′); as
  printed, the cell (*h*, *J*) of every header has no possible symbol, so no
  instance has a solution. And part (a) holds only if *r* and *c* say which
  symbols must occur, not merely which may. Answer 211 is right, but its names
  *jk* assume that each variable lies in four different clauses, and on inputs
  where it does not, a cycle *σ* that steps inside a clause can break the
  reduction; a sixteen-clause example shows it.
- **[282](282).** The hand-built certificate verifies clause by clause —
  147*q* − 102 of them, none longer than four — and so do the three remarks
  the answer makes in passing. Checking Algorithm C's own certificate (Theorem
  G) needed a new feature in the package, a port of SAT13's `l` option, now
  `SetProof`; the two certificates for *fsnark*(99) are 14,451 clauses against
  126,344.
- **[363](363).** All ten parts check out, computed from the definitions over
  every one of the 3ⁿ partial assignments — including the 27 weights of the
  table on page 619, the seven sets that form *L*₇, and the identity of
  part (j). The clause in answer 363(g) is the exception: as printed its
  disjunction runs over *k* ∈ *L*′, and since *l* ∈ *L*′ that clause contains
  both *x*ₗ and *x̄*ₗ, so it is a tautology and forces nothing. Over *k* ∈ *L*
  the construction works. Part (a), which asks about Algorithm C's trail, is
  the first claim in these readings that needed a new eye inside the solver;
  the package grew `SetTrace` for it.
- **[442–444](442-444).** The relation ⊢ₖ is computed exactly as
  defined, over every partial assignment, and every claim in the three answers
  comes out. Two spots repay a second reading. The procedure of answer 442(f)
  has to begin by applying *P*ₖ₋₁ to *F* itself, or it can miss a
  refutation it already had; and the "if and only if" of exercise 444(c) holds
  when step E2 may pick either literal of a variable of *F*, but fails when the
  choice is confined to literals that occur in *F*.

### Numbers that do not reproduce

| Exercise | Where | Printed | What came out |
| --- | --- | --- | --- |
| [282](282) | p. 255, clauses learned refuting *waerden*(3,10;97) | about 53,000 | **59,629** |
| [282](282) | p. 255, how many of those are used | fewer than 50,000 | **58,546** |
| [282](282) | p. 255, mems to find that certificate | 272 megamems | **573 megamems** |
| [282](282) | p. 255, clauses learned refuting *fsnark*(99) | about 135,000 | **123,407** |

Those four are in the running text, not in an exercise, and they are not a
quirk of this package: Knuth's own `sat13.w`, compiled and run on his own
benchmark files, prints exactly what the package prints.

### Two lines outside the exercises

| Where | Printed | What a reader notices |
| --- | --- | --- |
| p. 289 | "All of the examples in exercises 439–444 meet this test of honesty" | Exercises 442–444 contain no representations to be honest about; the representations are in exercises 431–441. |
| p. 702, the index | "Propagation completeness (UC₁), 360." | Propagation completeness is PC₁; UC₁ is unit-refutation completeness. Both are defined on p. 360. |

## How a reading is put together

Every reading is written the same way. The program is independent of the book:
it builds the objects from the exercise's own definitions, uses the `sat`
package where the question is one of satisfiability, and prints the quantities
the answer prints. Where a number can be reached two ways, it is.

Reports are in English, and so are the literate programs; both are typeset with
`luatex`.

## Building

```sh
make          # tangle every verify.w and build verify/verify
make vet      # go vet
make pdf      # weave and typeset every reading
make check    # typeset, and insist on a clean log
make clean    # remove everything the .w files generate, verify.pdf excepted
```

Adding a reading means putting its directory name in `EXERCISES` in the
[Makefile](Makefile).

Each program also runs on its own:

```sh
cd 057/verify && gtangle verify.w && go run . -mode formula
```

The modes differ from reading to reading; the last section of each `README.md`
lists them.
