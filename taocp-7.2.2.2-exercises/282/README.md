# TAOCP 7.2.2.2, Exercise 282: A Careful Reading

This is one reader's response to the request on Knuth's [news
page](https://www-cs-faculty.stanford.edu/~knuth/news.html): read an exercise
and its answer very carefully, then report back.

## What I found

| Item | Finding |
| --- | --- |
| Exercise 282 (statement) | No error. |
| The clauses *fsnark*(*q*) of exercise 176 | Reproduced; our generator writes Knuth's own file byte for byte. |
| Answer 282's certificate, every clause | **All verified** by unit propagation, for *q* = 3, 5, …, 15 and *q* = 99. |
| "*O*(*q*) clauses, all of length ≤ 4" | Confirmed: exactly 147*q* − 102 clauses, longest 4. |
| "the exclusion clauses for *b*'s, *c*'s, *d*'s aren't used" | Confirmed; dropping them leaves a valid certificate. |
| "doesn't assume the symmetry-breaking unit clauses" | Confirmed; it verifies against *fsnark*(*q*) without them. |
| "Not all of these clauses are actually necessary" | Confirmed, and quantified: 7,261 of the 14,451 suffice at *q* = 99. |
| Theorem G on our solver (§7.2.2.2, p. 254) | Confirmed: Algorithm C's learned clauses check out as a certificate. |
| p. 255: "about 135,000" learned for *fsnark*(99) | **123,407** with SAT13 as published. |
| p. 255: "fewer than 47,000" of them used | Confirmed: **46,019** by one backward pass, 42,490 at the fixed point. |
| p. 255: "about 53,000" learned for *waerden*(3,10;97) | **59,629**. |
| p. 255: "fewer than 50,000" of them used | **58,546** by one backward pass, **57,484** at the fixed point --- more either way. |
| p. 255: that certificate "found in 272 megamems" | **573 megamems**. |

The exercise and its answer are right, down to the last of the 14,451 clauses
at *q* = 99. The four numbers that do not reproduce are in the running text on
page 255, not in the exercise; they are reported here because this reading had
to measure them anyway, and because two of them can be checked against Knuth's
own program, which agrees with ours exactly.

## 1. What the exercise asks

> **282.** [*M33*] Construct a certificate of unsatisfiability for the clauses
> *fsnark*(*q*) of exercise 176 when *q* ≥ 3 is odd, using *O*(*q*) clauses,
> all having length ≤ 4.

A *certificate of unsatisfiability* for a family *F* is a sequence of clauses
(*C*₁, …, *C*ₜ) ending with the empty clause such that

> *F* ∧ *C*₁ ∧ ⋯ ∧ *C*ᵢ₋₁ ∧ *C̄*ᵢ ⊢₁ ε,  1 ≤ *i* ≤ *t*,  (119)

where ⊢₁ means "unit propagation reaches a contradiction." Checking one is
cheap, and needs no trust in whatever produced it.

## 2. The clauses

Exercise 176 of this same section defines the flower snark `J_q` and names the
vertices of its line graph `a_j`, …, `f_j`; *fsnark*(*q*) asks for a 3-coloring
of `L(J_q)`, with three unit clauses to break the symmetry. The program builds
`L(J_q)` twice — once from `J_q`'s own edges, once from the list in answer
176(a) — and compares:

| | *q* = 9 |
| --- | --- |
| edges of `L(J_q)` from `J_q` | 108 |
| edges from answer 176(a) | 108, the same ones |
| every vertex of degree 4 | yes |
| the 4*q* triangles cover every edge exactly once | yes |

The clauses themselves are generated in the order of Knuth's own
`sat-color` and `flower-snark-line`, down to the placement of blanks, so that

```sh
./verify -q 99 -mode dump | diff - SATexamples/benchmarks-UNSAT/fsnark-99.sat
```

reports no difference. So the solver here sees exactly the instance the book is
talking about, numbers its variables the same way, and spends the same mems.

Solved, they behave as exercise 176(b) and (c) say: unsatisfiable for odd *q*,
satisfiable for even *q* (checked for 3 ≤ *q* ≤ 8, and at *q* = 10).

## 3. The certificate

Answer 282 builds the certificate in five stages: the exclusion clauses (17);
two clauses for each of the 4*q* triangles; six clauses for each index *j*,
plus eighteen more once *j* ≥ 3; the clauses of the hint, walked around the
ring from *q* down to 2; and an endgame that fixes the colors of *a*₁ and
*e*₁ and marches around the odd cycle until it contradicts itself.

The program builds all of it and checks each clause against (119) with a
unit-propagation checker of its own — watched literals, no solver, nothing
from the `sat` package in that loop.

| | *q* = 9 | *q* = 99 |
| --- | --- | --- |
| clauses in the certificate | 1,221 | 14,451 |
| longest clause | 4 | 4 |
| clauses that fail (119) | **0** | **0** |
| the empty clause follows at the end | yes | yes |
| time to check | 2 ms | 27 ms |

The count is exactly 147*q* − 102 — 339, 633, 927, 1221, 1515, 1809, 2103 for
*q* = 3, 5, …, 15 — so it is *O*(*q*), with every clause of length at most 4,
which is what the exercise asks for.

## 4. The three remarks in the answer

The answer closes with a bracketed paragraph, and each sentence in it is a
claim:

| Claim | Check |
| --- | --- |
| "the exclusion clauses for *b*'s, *c*'s, and *d*'s aren't used" | Leaving them out gives 1,140 clauses at *q* = 9 instead of 1,221, and every one still verifies. |
| "This certificate doesn't assume that the symmetry-breaking unit clauses *b*₁,₁ ∧ *c*₁,₂ ∧ *d*₁,₃ … are present" | Checked against *fsnark*(9) with those three clauses removed: no failures. |
| "Not all of these clauses are actually necessary." | True beyond the exclusion clauses: one backward pass from the final contradiction reaches 579 of the 1,221 clauses at *q* = 9 and 8,019 of the 14,451 at *q* = 99; iterating to a fixed point (§6) brings those to 510 and 7,261. |

The restriction to odd *q* cannot be dropped: at *q* = 10 the clauses are
satisfiable, and the certificate breaks in exactly nine places, all of them in
the stage that asserts that `a_j`, `e_j`, `f_j` have three different colors.

## 5. Theorem G on Algorithm C's own clauses

Theorem G (page 254) says that the clauses Algorithm C learns are themselves a
certificate. To test that, the solver has to hand them over, and the `sat`
package had no way to do it — Knuth's SAT13 does, through its `l` option. So
the option was ported while this reading was being written; it is `SetProof`
now, with `Params.LearnSave` for SAT13's `K`. The whole benchmark suite still
reproduces the original's mem counts exactly, since writing a clause costs no
mems.

With the learned clauses in hand, the same checker verifies them:

| | *q* = 9 | *q* = 99 |
| --- | --- | --- |
| mems to refute | 9,563 + 1,635,531 | 104,051 + 764,142,188 |
| clauses learned | 530 | 123,407 |
| clauses in the certificate | 546 | 126,344 |
| average length | 8.3 | 14.6 |
| longest clause | 21 | 57 |
| clauses that fail (119) | **0** | **0** |
| clauses one backward pass reaches | 517 (94.7%) | 46,019 (36.4%) |
| at the fixed point of §6 | 516 | 42,490 |
| time to check | 5 ms | 2.7 s |

(The certificate has a few more clauses than the solver "learned" because
on-the-fly subsumption shortens clauses in place, and each shortened clause is
written out as well; Knuth marks those lines with an extra blank.)

Set that beside §3. Knuth's hand-built certificate for *q* = 99 has 14,451
clauses, none longer than 4, and is checked in 27 milliseconds. Algorithm C's
has 126,344 clauses averaging 14.6 literals, and takes a hundred times longer
to check. The answer's closing words — "the actual clauses learned by
Algorithm C are considerably longer and somewhat chaotic (indeed mysterious);
it's hard to see just where an 'aha' occurs!" — are visible in those two
columns.

## 6. One backward pass is not a fixed point

Exercise 284's marking — walk back from the final contradiction, taking the
reason of every literal the walk touches — says which clauses of a certificate
*that pass* used. It does not say which are necessary. Drop the ones it did
not reach and the propagations change, so another pass reaches fewer still.
Iterating until nothing more drops gives a better measure, and every
intermediate certificate still verifies with no failures; `-passes N` turns it
on.

| certificate | clauses | one pass | fixed point | passes |
| --- | --- | --- | --- | --- |
| answer 282, *q* = 9 | 1,221 | 579 | **510** | 6 |
| answer 282, *q* = 99 | 14,451 | 8,019 | **7,261** | 5 |
| Algorithm C, *q* = 9 | 546 | 517 | **516** | 3 |
| Algorithm C, *q* = 99 | 126,344 | 46,019 | **42,490** | 55 |
| Algorithm C, *waerden*(3,10;97) | 60,047 | 58,546 | **57,484** | 55 |

So a single pass overstates by up to 13%. The fixed point is still only an
upper bound on the smallest certificate — nothing here claims minimality — but
it is a much better one, and the figures quoted elsewhere in this reading say
which of the two they are.

## 7. The numbers on page 255

The text that introduces certificates gives figures for two runs. Since the
`sat` package is a faithful port, each of them can be compared against the
original directly.

| Claim on page 255 | Here |
| --- | --- |
| *fsnark*(99): "about 135,000" clauses learned | 123,407 |
| of those, "fewer than 47,000" used later | 46,019 ✔ |
| *waerden*(3,10;97): "about 53,000" clauses learned | 59,629 |
| of those, "fewer than 50,000" used later | 58,546 ✘ |
| that certificate "was found in 272 megamems" | 33,738 + 572,888,429 mems |

This is **not** a port artifact. Knuth's `sat13.w` was compiled from the copy
in [`knuth/`](../../knuth) with `ctangle` and run on his own
`fsnark-99.sat` and `waerden-3-10-97.sat`; it prints

```text
Altogether 104051+764142188 mems, 1395014 bytes, 202054 nodes, 123407 clauses learned ...
Altogether 33738+572888429 mems, 817609 bytes, 67807 nodes, 59629 clauses learned ...
```

which is what the package reports, mem for mem and clause for clause. So the
figures in the text belong to some earlier run — a different version of the
program, or different parameters — rather than to SAT13 as published. Two of
the five still come out: the flower snark's "fewer than 47,000" is a good
bound on 46,019, and its learned count is within 10%. The other three do not.

### Which "used" is meant

"Were actually used in subsequent steps" can be read two ways, and the two
give very different numbers, so which one the text means has to be settled
before saying a figure does not reproduce.

- **Backward.** Which clauses does the final contradiction rest on? That is
  the marking of exercise 284, which the next sentence on page 255 points to.
- **Forward.** Which clauses does some later step draw on, whether or not
  that step turns out to matter? This is the more literal reading of the
  words. It is counted from the same dependency lists.

| | certificate | backward | forward | page 255 |
| --- | --- | --- | --- | --- |
| *fsnark*(99) | 126,344 | 46,019 (36.4%) | 109,632 (86.8%) | fewer than 47,000 |
| *waerden*(3,10;97) | 60,047 | 58,546 (97.5%) | 58,708 (97.8%) | fewer than 50,000 |

The flower snark settles it. Under the forward reading its count is 109,632,
nearly nine tenths of the certificate and nowhere near 47,000; under the
backward reading it is 46,019, just under. So the text means the backward
count, and the comparisons above are like for like.

Knuth also writes that checking the *waerden*(3,10;97) certificate "with
straightforward unit-propagations was actually 2.2 gigamems," against 272
megamems to find it — the point being that checking can cost more than
solving. The shape of that holds here too: the solver takes 0.9 seconds and
the checker 2.8 seconds on that certificate, of whose 60,047 clauses one
backward pass reaches 58,546 and the fixed point of §6 reaches 57,484.

## 8. What I checked before reporting this

- **The graph**, from two independent constructions (§2).
- **The clause file**, against Knuth's own, byte for byte (§2).
- **The certificate**, clause by clause, with a checker that shares nothing
  with the solver (§3).
- **The checker itself.** If a formula has a satisfying assignment, no clause
  that the assignment falsifies can be implied by it. So the program solves
  random satisfiable problems, fabricates clauses that the solution falsifies,
  and offers them to the checker: 1,000 of 1,000 were rejected. Genuine
  certificates of random unsatisfiable problems all pass (65 of 65). Spoiling
  a certificate — dropping a necessary clause, changing one of its literals,
  reversing the order — is noticed 129 times out of 195; the rest are cases
  where the damage is real but the certificate survives it, since a certificate
  carries slack and the same conclusion can often be reached another way.
  A tautology follows from anything, so the checker must accept one and report
  no dependencies for it: 100 of 100.
- **Every reduced certificate** of §6, which has to keep verifying as clauses
  are dropped; every intermediate certificate in those runs came back with no
  failures.
- **The package's mem counts**, which the full test suite still reproduces
  after the `SetProof` change.

## 9. Running it

```sh
cd taocp-7.2.2.2-exercises && make
cd 282/verify
./verify                      # every mode at q = 9, in a twentieth of a second
./verify -mode graph          # L(J_q) against exercise 176
./verify -mode fsnark         # the clauses, and both parities
./verify -mode cert           # the answer's certificate, checked
./verify -mode remarks        # the three remarks, and an even order
./verify -mode algc -q 99     # Theorem G on fsnark(99); about four seconds
./verify -mode waerden        # the other example on page 255
./verify -mode selftest       # the checker, made to say no
./verify -passes 60           # iterate the marking of §6 to its fixed point
./verify -q 99 -mode dump     # Knuth's fsnark-99.sat, byte for byte
```

## References

Donald E. Knuth, *The Art of Computer Programming*, Volume 4B (Addison-Wesley,
2022), §7.2.2.2: certificates of unsatisfiability, (119), and Theorem G on
pp. 253–255; exercises 277–284 on p. 341 and answer 282 on p. 602.

The same section for the flower snark: exercise 176 on p. 331, with its figure
of *J*₅ and *L*(*J*₅), and answer 176 on p. 582.

E. Goldberg and Y. Novikov, *Proceedings of DATE* **6**,1 (2003), 886–891, who
pointed out that a CDCL solver produces a certificate as a byproduct of its
run — the observation behind Theorem G.

A. Van Gelder, *Proc. Int. Symp. on Artificial Intelligence and Math.* **10**
(2008), 9 pages, from whom the checking procedure of (119) has its name,
reverse unit propagation.

Knuth's benchmark files and generators, `fsnark-99.sat` and
`waerden-3-10-97.sat` among them, are in
[SATexamples.tgz](https://www-cs-faculty.stanford.edu/~knuth/programs/SATexamples.tgz).
