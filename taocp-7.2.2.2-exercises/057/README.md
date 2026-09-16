# TAOCP 7.2.2.2, Exercise 57: A Careful Reading

This is one reader's response to the request on Knuth's [news
page](https://www-cs-faculty.stanford.edu/~knuth/news.html): read an exercise
and its answer very carefully, then report back.

## What I found

| Item | Finding |
| --- | --- |
| Exercise 57 (statement) | No error. |
| Table 2, all 32 rows | Confirmed against π/4 and e/4, as answer 53 says. |
| "in twelve different ways" (from answer 56) | Confirmed; the twelve sets are the ones answer 56 lists. |
| The twelve truth tables, 384 symbols | **All confirmed**, reading down the two columns. |
| The formula for the tenth table | Confirmed at all 32 points; it is consistent with the tenth table. |
| "only six Boolean operations" | Confirmed: six. |
| Could five do? | **No.** Six is the minimum, over all 20 variables. |
| Which tables allow six | Five of the twelve: the 5th, 6th, 9th, 10th, and 11th. |

Everything in the answer is right. The exercise asks for six operations, and
its exclamation mark suggests that this is a surprise; what this reading adds
is that it cannot be beaten. No Boolean chain of five or fewer steps, on any of
the twenty variables, matches Table 2. That is shown twice, by an exhaustive
search and by a SAT solver, and the two share nothing but a short argument
that tells them where to look.

## 1. What the exercise asks

> **57.** [*29*] Combining the previous exercise with the methods of Section
> 7.1.2, exhibit a function *f* for Table 2 that can be evaluated with only six
> Boolean operations(!).

Table 2 (page 199) gives 32 points *x* = *x*₁…*x*₂₀, sixteen where *f*(*x*) = 1
and sixteen where *f*(*x*) = 0. Exercise 56 asks for a function consistent with
the table that depends on only five of the variables. The answer to 57 takes
the twelve five-variable sets of answer 56, prints the truth table each one
gives, with a `*` for every don't-care, and says that the tenth yields

> *f*(*x*) = ((*x*₈ ⊕ (*x*₉ ∨ *x*₁₀)) ∨ ((*x*₆ ∨ *x*₁₂) ⊕ *x̄*₁₀)) ⊕ *x*₁₂.

## 2. Table 2

Everything below starts from the 640 bits of Table 2, so the transcription was
checked first against a second source. Answer 53 reveals that the left column
is the binary expansion of π, and the right column that of e, twenty bits at a
time; more precisely, of π/4 and e/4. Computed to 400 bits,

| | Rows that agree |
| --- | --- |
| left column, π/4 | 16 of 16 |
| right column, e/4 | 16 of 16 |

## 3. The twelve ways

A set of variables determines *f* consistently exactly when it meets every one
of the 256 differences *u*ₖ ⊕ *v*ₗ between a left row and a right row, as answer
56 explains. With only 2²⁰ sets, all of them were simply tried:

| Size | 5 | 6 | 7 | … | 19 | 20 |
| --- | --- | --- | --- | --- | --- | --- |
| covering sets | 12 | 994 | 13503 | … | 20 | 1 |

That is the generating function 12*z*⁵ + 994*z*⁶ + 13503*z*⁷ + ⋯ + 20*z*¹⁹ +
*z*²⁰ of answer 56, and the twelve sets of size five, in lexicographic order,
are exactly the list printed there:

```text
{1,4,15,17,20}  {1,10,15,17,20} {1,15,17,18,20} {4,6,7,10,12}
{4,6,9,10,12}   {4,6,10,12,19}  {4,10,12,15,19} {5,7,11,12,15}
{6,7,8,10,12}   {6,8,9,10,12}   {7,10,12,15,20} {8,15,17,18,20}
```

## 4. The twelve truth tables

Following Section 7.1.2, the truth table of a function of (*y*₁, …, *y*₅) lists
its values from (0, …, 0) to (1, …, 1) with *y*₁ most significant; here the
*y*'s are the variables of the set in increasing order. Each point of Table 2
fills one position, and the other positions are don't-cares.

The answer typesets the twelve tables in two columns of six. Read down the left
column and then down the right, every one of the 384 symbols agrees:

| Reading order | Tables that agree |
| --- | --- |
| down the columns | **12 of 12** |
| across the rows | 2 of 12 (only the first and the last) |

So "the tenth" is the fourth line of the right-hand column, the table of
{6, 8, 9, 10, 12}. That is also the set of variables the formula uses, so the
answer is consistent with itself.

## 5. The formula

The formula agrees with Table 2 at all 32 points. As a chain it is six steps:

```text
g1 = x9 | x10     g2 = x8 ^ g1      g3 = x6 | x12
g4 = ~(x10 ^ g3)  g5 = g2 | g4      g6 = x12 ^ g5
```

The fourth step, (*x*₆ ∨ *x*₁₂) ⊕ *x̄*₁₀, counts as one operation, since ≡ is
one of the sixteen binary operations. Section 7.1.2 prefers *normal* chains,
whose operations all take (0, 0) to 0, and the conversion costs nothing: it is
the same six steps with `g4 = x10 ^ g3`, `g5 = ~g2 & g4`, and the output
complemented. Both chains were evaluated at the 32 points as well, and agree.

The formula's full truth table on (*x*₆, *x*₈, *x*₉, *x*₁₀, *x*₁₂) is

```text
printed:  1*1*1*10 10001100 0*101*1* **1*0*10
formula:  11101010 10001100 01101010 10100110
```

which agrees with the tenth table in every position that is not a star.

## 6. Five operations are not enough

The count of six is what the exercise asks for. It is natural to ask whether it
is the best possible, and it is. Nothing in the answer claims this, so this
section is an addition, not a correction.

The two searches rest on one observation. Take a shortest chain that matches
Table 2, say with *r* ≤ 5 steps, written as a normal chain with the output
complemented if necessary.

1. *r* > 0, because no single variable covers.
2. Every step but the last is used by a later one, or it could be deleted.
3. So the 2*r* operand slots hold at least *r* − 1 references to steps, and at
   most *r* + 1 to variables; and the variables that occur must form a covering
   set.
4. No covering set has fewer than five elements. So either the chain reads
   exactly five variables — one of the twelve sets — or *r* = 5 and it reads six.
   In the second case all ten slots are spoken for: each variable is read once
   and each step used once, so the chain is a *read-once formula*.

**By exhaustive search.** On each of the twelve sets, every chain of at most
five steps was tried against the partial truth table, using the five
nontrivial normal operations and an optional complement of the output. None
fits. Separately, all 967,605 normal read-once functions of six variables were
generated and matched against the partial table of each of the 994 covering
six-sets. None fits.

**With the SAT solver.** Answer 477 constructs clauses that are satisfiable
exactly when an *r*-step normal chain computes given truth tables. Adapted to a
partial table, with one extra variable for a complemented output, they were
given to the [`sat` package](../..) for *r* = 1, …, 5 on each of the twelve
sets, and for *r* = 5 on each of the 994 six-sets. All 12 × 5 + 994 = 1054
instances are unsatisfiable. The optional clauses of answers 477 and 478 were
used, and the program's commentary proves that they keep at least one shortest
chain: in particular, that renumbering the steps greedily puts their operand
pairs in the colex order answer 478 asks for.

| | Instances | Result | Cost |
| --- | --- | --- | --- |
| exhaustive, twelve five-sets | all chains of ≤ 5 steps | no fit | 41 s |
| exhaustive, 994 six-sets | 967,605 read-once functions | no fit | 8 s |
| SAT, twelve five-sets, *r* ≤ 6 | 72 | see §7 | 15,719 megamems |
| SAT, 994 six-sets, *r* = 5 | 994 | all UNSAT | 224,734 megamems |

## 7. Which of the twelve tables allow six

Running the same clauses with *r* = 6 on each of the twelve sets answers a
question the answer leaves open: the tenth table is not the only one.

| | Set | Six operations? |
| --- | --- | --- |
| 1–4 | {1,4,15,17,20} {1,10,15,17,20} {1,15,17,18,20} {4,6,7,10,12} | no |
| **5** | **{4,6,9,10,12}** | **yes** |
| **6** | **{4,6,10,12,19}** | **yes** |
| 7, 8 | {4,10,12,15,19} {5,7,11,12,15} | no |
| **9** | **{6,7,8,10,12}** | **yes** |
| **10** | **{6,8,9,10,12}** | **yes** |
| **11** | **{7,10,12,15,20}** | **yes** |
| 12 | {8,15,17,18,20} | no |

The seven "no"s mean at least seven operations. The solver's chains, each
checked by the program against all 32 points of Table 2 and not merely against
the clauses (every output is complemented):

```text
 5  g1 = x4^x6;   g2 = x4|x12;   g3 = x9&g2;   g4 = g1|g3;   g5 = ~x10&g4; g6 = g2^g5
 6  g1 = x4^x6;   g2 = x4|x12;   g3 = x6^x19;  g4 = g1|g3;   g5 = ~x10&g4; g6 = g2^g5
 9  g1 = x6^x10;  g2 = x7&~x10;  g3 = x8^g2;   g4 = x12&~g2; g5 = g1&g3;   g6 = g4|g5
10  g1 = x9|x10;  g2 = x6|x12;   g3 = x8^g1;   g4 = x10^g2;  g5 = ~g3&g4;  g6 = x12^g5
11  g1 = x7&~x10; g2 = x7^x20;   g3 = ~g1&g2;  g4 = x15&~g3; g5 = x12|g4;  g6 = g1^g5
```

The chain for the tenth table is the answer's formula in normal form, with two
steps swapped. The fifth and sixth share all but one step.

## 8. Why not ask the solver about all twenty variables at once

Answer 477's clauses could take all of Table 2 directly, with twenty inputs,
and no argument about covering sets would be needed. That does not finish.
With every optional clause in place:

| *r* | Result | Cost |
| --- | --- | --- |
| 3 | UNSAT | 499 megamems |
| 4 | UNSAT | 58,535 megamems, 87 s |
| 5 | — | not attempted; the cost grows more than a hundredfold a step |

The observation of §6 turns one hopeless instance into a thousand small ones.

## 9. What I checked before reporting this

- **The transcription.** Table 2 against π and e (§2); the twelve truth tables
  against the program's own tables (§4), in both reading orders.
- **The chains, independently of the clauses.** Every chain the solver
  returns is evaluated at the 32 points of Table 2.
- **That the searches can say yes.** Two searches that report only "no" need
  a check that they can find what exists. The self-test builds 1000 random
  chains of up to five steps on five variables, with any of the ten nontrivial
  operations, hides a random third of each truth table, and asks both searches
  for the fewest steps. They agree every time, and never exceed the chain that
  was built. (Twenty-five of the thousand targets turn out to be fit by a
  single variable, and those are left to the exhaustive search: with trivial
  operations excluded, the clauses cannot express a chain of no steps, as
  answer 477 itself warns.) The read-once list
  is checked the same way, against random formulas built by merging a pool of
  six variables, which is a different construction from the one that made the
  list.
- **The `sat` package.** Every SAT answer in this reading has a SAT-free
  counterpart, and all of them agree: 1054 unsatisfiable instances, five
  satisfiable ones whose chains check out, and the self-test.

## 10. Method

The program is a GWEB literate program. [`verify.w`](verify/verify.w) is the
source and `gtangle` produces the Go from it; the typeset document,
[`verify.pdf`](verify/verify.pdf), is committed beside it so it can be read
without installing GWEB. The SAT solver is the [`sat` package](../..) of this
repository.

To reproduce:

```sh
cd taocp-7.2.2.2-exercises && make
cd 057/verify
./verify -mode table2       # Table 2 against pi/4 and e/4
./verify -mode covers       # the covering sets of answer 56
./verify -mode tables       # the twelve truth tables
./verify -mode formula      # the formula, its chain, and the tenth table
./verify -mode exhaustive   # no chain of five steps, without SAT; under a minute
./verify -mode sat          # the same with SAT, and which tables allow six; about six minutes
./verify -mode selftest     # the two searches against each other
./verify                    # all of the above
./verify -mode direct -r 4  # answer 477 on all twenty variables; a minute and a half
```

## References

Donald E. Knuth, *The Art of Computer Programming*, Volume 4B (Addison-Wesley,
2022), §7.2.2.2: Table 2 and Eq. (27) on pp. 198–199, exercises 53, 56, and 57
on p. 321, their answers on pp. 557–558; exercises 477 and 478 on pp. 362–363,
their answers on p. 642. The construction of clauses for learning a DNF
is due to A. P. Kamath, N. K. Karmarkar, K. G. Ramakrishnan, and M. G. C.
Resende, *Mathematical Programming* **57** (1992), 215–238.
