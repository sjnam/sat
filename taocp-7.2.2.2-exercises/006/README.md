# TAOCP 7.2.2.2, Exercise 6: A Careful Reading

Written 16 September 2026, against Volume 4B, Addison-Wesley, first printing,
2022, and the errata file as of that date. That file replaces exercise 5, the
question just before this one, and gives it a new answer about W(3, *k*); it
has nothing on exercise 6 or its answer.

This is one reader's response to the request on Knuth's [news
page](https://www-cs-faculty.stanford.edu/~knuth/news.html): read an exercise
and its answer very carefully, then report back. The news page describes this
one as "verify a certain (previously unpublished) lower bound on van der
Waerden numbers W(3, *k*)".

## What I found

| Item | Finding |
| --- | --- |
| Exercise 6 (statement) | No error. |
| *P* = *p*³ and *P*′ = (1 − *p*)ᵏ ≤ exp(−*kp*) = 1/*k*² | Confirmed. |
| "In the lopsidependency graph, which is bipartite" | Confirmed, both for condition (133) and for the rule of answer 351. |
| *D* and *d* | Confirmed as upper bounds. |
| (1 − *x*)ᴰ = 1/2, *y* = 2*P*, and the orders of *x* and *y* | Confirmed. |
| "(1 − *y*)ᵈ = exp(−*yd* + *O*(*y*²*d*)) = *O*(1)" | **The step needs a lower bound, and the constant is tiny.** Here *yd* = 24 exactly, so (1 − *y*)ᵈ → e⁻²⁴, and "sufficiently large" means ln *k* ≥ 4857.97. |
| W(3, *k*) = Ω(*k*²/(log *k*)³) | Confirmed. The same argument with *p* = (3 ln *k*)/*k* gives Ω((*k*/log *k*)²). |

The bound is right, and the sketch proves it. What the sketch does not show is
how late it starts to work with the constants it chooses: from *k* ≈ 10²¹¹⁰
on.

## 1. What the exercise asks

W(3, *k*) is the smallest *n* such that every string *x*₁ … *xₙ* of 0s and 1s
has three equally spaced 0s or *k* equally spaced 1s. Exercise 6 asks to show,
with the Local Lemma, that W(3, *k*) = Ω(*k*²/(log *k*)³).

The answer sets each *xᵢ* to 0 with probability *p* = (2 ln *k*)/*k* and takes
*n* ≤ *k*²/(ln *k*)³. The bad events are *Aᵢ*, three equally spaced 0s, with
probability *P* = *p*³, and *A*′ⱼ, *k* equally spaced 1s, with probability
*P*′ ≤ 1/*k*². In a bipartite lopsidependency graph each *Aᵢ* has at most
*D* = 3*k*³/((*k* − 1)(ln *k*)³) neighbors and each *A*′ⱼ at most
*d* = (3/2)*k*³/(ln *k*)³. Theorem L (p. 266) then needs *P* ≤ *y*(1 − *x*)ᴰ
and *P*′ ≤ *x*(1 − *y*)ᵈ for some *x* and *y*; the answer chooses
(1 − *x*)ᴰ = 1/2 and *y* = 2*P*, and concludes with
"(1 − *y*)ᵈ = exp(−*yd* + *O*(*y*²*d*)) = *O*(1)".

## 2. The events and the graph

Events of the same kind overlap without being neighbors, which is allowed
only because the graph is *lopsided*: knowing that other triples are not all
0 can only make three 0s less likely. The program checks this exactly.

| Check | Result |
| --- | --- |
| (1 − *p*)ᵏ ≤ exp(−*kp*) = 1/*k*², *p* = (2 ln *k*)/*k*, *k* from 2 to 10⁶ | holds |
| condition (133): Pr(*A* given no non-neighbor happens) ≤ Pr(*A*), by enumerating all strings, *n* ≤ 10, *k* = 3, 4, *p* = 0.2, 0.5, 0.8, all non-neighbors and 30 random subsets | 23,064 cases, none exceeds |
| the rule of answer 351 (Moser and Tardos) for when two events must be joined, applied literally over all settings and changes, *n* ≤ 9 | gives exactly the bipartite graph, on 3,284 ordered pairs |

The second check matters for Algorithm M, whose Theorem M is proved for the
graph of answer 351.

## 3. The degrees

An *Aᵢ* has three positions, and each lies in at most
*k*⌊(*n* − 1)/(*k* − 1)⌋ progressions of length *k*. So *Aᵢ* has at most
3*k*(*n* − 1)/(*k* − 1) neighbors, which is below *D* when
*n* ≤ *k*²/(ln *k*)³. A position lies in at most *n* − 1 progressions of length
3, so *A*′ⱼ has at most *k*(*n* − 1) neighbors, below *d* = 3*kn*/2. Counting
the distinct neighbors exactly for 3 ≤ *k* ≤ 12 and *k* ≤ *n* ≤ 100 (935
pairs) confirms both bounds; the largest ratios to 3*k*(*n* − 1)/(*k* − 1)
and *k*(*n* − 1) are 0.646 and 0.969.

## 4. The last step

Write *L* = ln *k*. The answer's choices give *y* = 2*p*³ = 16*L*³/*k*³ and
*d* = (3/2)*k*³/*L*³, so *yd* = 24 exactly, and (1 − *y*)ᵈ = e⁻²⁴(1 + *o*(1)).
That is a positive constant, which is what the argument needs; but it needs it
as a lower bound, and "= *O*(1)" states an upper bound, which every
probability satisfies. Nor is the constant harmless. With
*x* ≈ ln 2/*D* ≈ (ln 2)*L*³/(3*k*²) and *P*′ ≈ 1/*k*², the second inequality
becomes (ln 2/3) *L*³ e⁻²⁴ ≥ 1 + *o*(1), that is

*L* ≥ exp((24 + ln 3 − ln ln 2)/3) ≈ 4857.97.

The program evaluates both sides exactly, in logarithms, since *k* does not
fit in a floating-point number.

| Check | Result |
| --- | --- |
| *yd* = 24 | exactly, for every *k* |
| threshold for *P*′ ≤ *x*(1 − *y*)ᵈ, found by bisection | ln *k* = 4857.9658, as the closed form predicts; *k* > 10²¹⁰⁹·⁸ |
| sign of the margin on 6,001 values of ln *k* from 1 to 10⁶ | negative below the threshold, positive above |

**A better exponent from the same argument.** Nothing forces
*p* = (2 ln *k*)/*k*. With *p* = (3 ln *k*)/*k* we have *P*′ ≤ 1/*k*³, and with
*n* = *ak*²/*L*³ the product *yd* is 81*a*; the second inequality reads, up to
lower-order terms, 81*a* + ln *a* ≤ *L* + 3 ln *L* + ln(ln 2/3). Taking
*a* = *L*/81, that is *n* = *k*²/(81*L*²), it holds for every *L*. The program
confirms the exact inequalities for all *k* ≥ 8 on the same grid (below 8,
*y* = 2*p*³ is too large). So the argument of the answer, with one constant
changed, proves W(3, *k*) = Ω((*k*/log *k*)²), the bound of Y. Li and J. Shu,
*Advances in Applied Mathematics* **44** (2010), 243–247. For comparison, the
paper the answer cites, Brown, Landman, and Robertson (2008), proves
W(3, *k*) > *k*^(2 − 1/log log *k*) with the symmetric Local Lemma; that is
weaker than the answer's own bound, which fits the news page's "previously
unpublished".

## 5. Concrete bounds

With the constants free, any Local Lemma argument gives a definite bound for
each *k*. The program searches *p* and *x* on logarithmic grids, with *y* as
small as the first inequality allows, so every success is a proof.

With the true degrees, for 3 ≤ *k* ≤ 30, the largest *n* grows only a little
faster than *k*: W(3, 10) > 12, W(3, 20) > 25, W(3, 30) > 38, against 97, and
at least 389 and 903, in the table on page 189. Every such bound is below the
table.

With the answer's *D* and *d*:

| *k* | largest *n* found | ÷ *k*²/(ln *k*)³ | ÷ *k*²/(ln *k*)² |
| --- | --- | --- | --- |
| 10², 10³ | none as large as *k* | | |
| 10⁴ | 4.521 × 10⁴ | 0.35 | 0.038 |
| 10⁵ | 2.697 × 10⁶ | 0.41 | 0.036 |
| 10⁶ | 1.782 × 10⁸ | 0.47 | 0.034 |
| 10⁷ | 1.261 × 10¹⁰ | 0.53 | 0.033 |
| 10⁸ | 9.385 × 10¹¹ | 0.59 | 0.032 |

The ratio to *k*²/(ln *k*)³ grows but has not reached 1 by *k* = 10⁸; every
value is above *k*²/(81(ln *k*)²), which itself passes *k*²/(ln *k*)³ once
ln *k* > 81.

## 6. Algorithm M and the `sat` package

**Resampling.** Algorithm M (p. 266) draws the string, and while some bad
event happens, redraws that event's positions. Theorem M bounds the average
number of redraws of event *j* by *θⱼ*/(1 − *θⱼ*). For *k* = 30 at the
largest *n* above, *n* = 38, with *p* = 0.11 and the corresponding *x* and *y*,
1,000 runs each ended with a string that has no three equally spaced 0s and
no thirty equally spaced 1s, checked by looking at every difference. The
average number of redraws was 0.316 for the 342 events *A* (Theorem M allows
1.013) and 0.112 for the 9 events *A*′ (it allows 0.844).

**The solver.** The clauses *waerden*(3, *k*; *n*) should be satisfiable
exactly when *n* < W(3, *k*). For 3 ≤ *k* ≤ 10 the package finds a string of
length W(3, *k*) − 1, which is checked against the definition, and proves that
none of length W(3, *k*) exists, reproducing 9, 18, 22, 32, 46, 58, 77, 97 from
the table on page 189. For *k* ≤ 6 a plain backtracking search, which extends
strings one bit at a time, finds the same values without the solver. Option
`-wmax 11` adds W(3, 11) = 114, in about ten seconds.

The package needed no change for this reading.

## 7. Running it

```sh
cd taocp-7.2.2.2-exercises && make
cd 006/verify
./verify                      # every claim, in about four seconds
./verify -mode events         # the probabilities and the lopsided graph
./verify -mode degrees        # D and d against exact counts
./verify -mode numbers        # yd = 24, the threshold, the (k/log k)^2 variant
./verify -mode concrete       # definite bounds for k up to 10^8
./verify -mode resample       # Algorithm M and Theorem M
./verify -mode solver         # W(3,k) for k <= 10 with the sat package
```

## References

Donald E. Knuth, *The Art of Computer Programming*, Volume 4B (Addison-Wesley,
2022), §7.2.2.2: the table of W(3, *k*) on p. 189; Lemma L, Theorem L, and
Algorithm M on p. 266, Theorem M on p. 267; exercise 6 on p. 317 and exercise
351 on p. 348; answer 6 on p. 549 and answer 351 on p. 618.

T. Brown, B. M. Landman, and A. Robertson, *Journal of Combinatorial Theory*
**A115** (2008), 1304–1309, as cited by the answer.

Y. Li and J. Shu, "A lower bound for off-diagonal van der Waerden numbers,"
*Advances in Applied Mathematics* **44** (2010), 243–247.

Zach Hunter, "A short proof that w(3, k) ≥ (1 − o(1))k²,"
arXiv:2209.07651 (2022), whose Remark 1.1 summarizes the two bounds above.
