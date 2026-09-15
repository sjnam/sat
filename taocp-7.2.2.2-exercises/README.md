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

The news page lists these exercises for §7.2.2.2.

| Exercise | What the news page asks | What came out |
| --- | --- | --- |
| 6 | Verify a certain (previously unpublished) lower bound on van der Waerden numbers W(3,k) | |
| [57](057) | Find a 6-gate way to match a certain 20-variable Boolean function at 32 given points | confirmed, and six is the minimum |
| 165 | Devise an algorithm to compute the largest positive autarky of given clauses | |
| 212 | Prove that partial latin square construction is NP-complete | |
| [282](282) | Find a linear certificate of unsatisfiability for the flower snark clauses | confirmed to the last clause; four numbers in the surrounding text do not reproduce |
| 306–308 | Study the reluctant doubling strategy of Luby, Sinclair, and Zuckerman | |
| 318 | Find the best possible Local Lemma for d-regular dependency graphs with equal weights | |
| 322 | Show that random-walk methods cannot always find solutions of locally feasible problems using independent random variables | |
| 335 | Express the Möbius series of a cocomparability graph as a determinant | |
| 339 | Relate generating functions for traces to generating functions for pyramids | |
| 347 | Find the best possible Local Lemma for a given chordal graph with arbitrary weights | |
| 356 | Prove the Clique Local Lemma | |
| 363 | Study the stable partial assignments of a satisfiability problem | |
| 442–444 | Study the UC and PC hierarchy of progressively harder sets of clauses | |
| 518 | Reduce 3SAT to testing the permanent of a {−1,0,1,2} matrix for zero | |

## What came out

### Beyond the book

- **[57](057).** Every statement in the answer checks out, including the
  twelve truth tables with their don't-cares. The exercise asks only for six
  operations; no chain of five or fewer matches Table 2 at all, which is shown
  both by exhaustive search and with the solver, and the two agree. Of the
  twelve five-variable tables, exactly five admit six operations; the answer's
  tenth is one of them.
- **[282](282).** The hand-built certificate verifies clause by clause —
  147*q* − 102 of them, none longer than four — and so do the three remarks
  the answer makes in passing. Checking Algorithm C's own certificate (Theorem
  G) needed a new feature in the package, a port of SAT13's `l` option, now
  `SetProof`; the two certificates for *fsnark*(99) are 14,451 clauses against
  126,344.

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
