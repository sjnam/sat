# TAOCP 7.2.2.2, Exercise 282: A Careful Reading

Written 16 September 2026, against Volume 4B, Addison-Wesley, first printing,
2022, and the errata file as of that date, which has no entry for this exercise
or its answer.

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
| "Not all of these clauses are actually necessary" | Confirmed, and quantified: 8,019 of the 14,451 suffice at *q* = 99. |
| Theorem G on our solver (§7.2.2.2, p. 254) | Confirmed: Algorithm C's learned clauses check out as a certificate. |
| p. 255: "about 135,000" learned for *fsnark*(99) | **123,407** with SAT13 as published. |
| p. 255: "fewer than 47,000" of them used | Confirmed: **46,019**. |
| p. 255: "about 53,000" learned for *waerden*(3,10;97) | **59,629**. |
| p. 255: "fewer than 50,000" of them used | **58,546**, which is more. |
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

where ⊢₁ means "unit propagation reaches a contradiction." Checking one costs
nothing and requires no trust in whatever produced it, which is the point.

## 2. The clauses

Exercise 176 of this same section defines the flower snark *J*<sub>*q*</sub> and names the
vertices of its line graph *a*<sub>*j*</sub>, …, *f*<sub>*j*</sub>;
*fsnark*(*q*) asks for a 3-coloring of *L*(*J*<sub>*q*</sub>), with three unit
clauses to break the symmetry. The program builds *L*(*J*<sub>*q*</sub>) twice
— once from *J*<sub>*q*</sub>'s own edges, once from the list in answer 176(a)
— and compares:

| | *q* = 9 |
| --- | --- |
| edges of *L*(*J*<sub>*q*</sub>) from *J*<sub>*q*</sub> | 108 |
| edges from answer 176(a) | 108, the same ones |
| every vertex of degree 4 | yes |
| the 4*q* triangles cover every edge exactly once | yes |

The clauses themselves are generated in the order of Knuth's own
`sat-color` and `flower-snark-line`, down to the placement of blanks, so that

```sh
./verify -q 99 -mode dump | diff - SATexamples/benchmarks-UNSAT/fsnark-99.sat
```

reports no difference. That matters: it means the solver here sees exactly the
instance the book is talking about, numbers its variables the same way, and
spends the same mems.

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
| "Not all of these clauses are actually necessary." | True beyond the exclusion clauses: walking backwards from the final contradiction, 579 of the 1,221 clauses at *q* = 9 are reached, and 8,019 of the 14,451 at *q* = 99. |

The restriction to odd *q* is essential rather than decorative: at *q* = 10 the
clauses are satisfiable, and the certificate breaks in exactly nine places, all
of them in the stage that asserts that *a*<sub>*j*</sub>, *e*<sub>*j*</sub>,
*f*<sub>*j*</sub> have three different colors.

## 5. Theorem G, tested rather than believed

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
| mems to refute | 9,563 + 1,635,529 | 104,051 + 764,142,186 |
| clauses learned | 530 | 123,407 |
| clauses in the certificate | 546 | 126,344 |
| average length | 8.3 | 14.6 |
| longest clause | 21 | 57 |
| clauses that fail (119) | **0** | **0** |
| clauses actually needed | 517 (94.7%) | 46,019 (36.4%) |
| time to check | 5 ms | 2.7 s |

(The certificate has a few more clauses than the solver "learned" because
on-the-fly subsumption shortens clauses in place, and each shortened clause is
written out as well; Knuth marks those lines with an extra blank.)

The comparison with §3 is the interesting part. Knuth's hand-built certificate
for *q* = 99 has 14,451 clauses, none longer than 4, and is checked in 27
milliseconds. Algorithm C's has 126,344 clauses averaging 14.6 literals, and
takes a hundred times longer to check. The answer's closing words — "the
actual clauses learned by Algorithm C are considerably longer and somewhat
chaotic (indeed mysterious); it's hard to see just where an 'aha' occurs!" —
are visible in those two columns.

## 6. The numbers on page 255

The text that introduces certificates gives figures for two runs. They are
worth checking because the `sat` package is a faithful port and can be
compared against the original directly.

| Claim on page 255 | Here |
| --- | --- |
| *fsnark*(99): "about 135,000" clauses learned | 123,407 |
| of those, "fewer than 47,000" used later | 46,019 ✔ |
| *waerden*(3,10;97): "about 53,000" clauses learned | 59,629 |
| of those, "fewer than 50,000" used later | 58,546 ✘ |
| that certificate "was found in 272 megamems" | 33,738 + 572,888,427 mems |

This is **not** a port artifact. Knuth's `sat13.w` was compiled from the copy
in [`knuth/`](../../knuth) with `ctangle` and run on his own
`fsnark-99.sat` and `waerden-3-10-97.sat`; it prints

```text
Altogether 104051+764142186 mems, 1395002 bytes, 202054 nodes, 123407 clauses learned ...
Altogether 33738+572888427 mems, 817597 bytes, 67807 nodes, 59629 clauses learned ...
```

which is what the package reports, mem for mem and clause for clause. So the
figures in the text belong to some earlier run — a different version of the
program, or different parameters — rather than to SAT13 as published. Two of
the five still come out: the flower snark's "fewer than 47,000" is a good
bound on 46,019, and its learned count is within 10%. The other three do not.

Knuth also writes that checking the *waerden*(3,10;97) certificate "with
straightforward unit-propagations was actually 2.2 gigamems," against 272
megamems to find it — the point being that checking can cost more than
solving. The shape of that holds here too: the solver takes 0.9 seconds and
the checker 2.8 seconds on that certificate, with 58,546 of its 60,047 clauses
really needed.

## 7. What I checked before reporting this

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
- **The package's mem counts**, which the full test suite still reproduces
  after the `SetProof` change.

## 8. Running it

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
./verify -q 99 -mode dump     # Knuth's fsnark-99.sat, byte for byte
```

## References

Donald E. Knuth, *The Art of Computer Programming*, Volume 4B (Addison-Wesley,
2022), §7.2.2.2: certificates of unsatisfiability and Theorem G on pp. 253–255,
exercises 277–284 on p. 341, exercise 282's answer on p. 602; exercise 176
(p. 331) and its answer (p. 582) for the flower snark. The
certificate format and the reverse-unit-propagation idea are due to E. Goldberg
and Y. Novikov, *Proceedings of DATE* **6**,1 (2003), 886–891, and A. Van
Gelder, *Proc. Int. Symp. on Artificial Intelligence and Math.* **10** (2008).
Knuth's benchmark files and generators are in
[SATexamples.tgz](https://www-cs-faculty.stanford.edu/~knuth/programs/SATexamples.tgz).
