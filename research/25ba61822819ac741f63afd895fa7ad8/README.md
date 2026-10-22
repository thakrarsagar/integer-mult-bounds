# Span of stacked P104 row and column charts

This is a scoped linear-algebra extension of the one-row/one-column check in
[#4153](https://github.com/CrocSwap/integer-mult-bounds/pull/4153), retained at
`9123241fea53df77e51ffe30d9aca1625d4bf3a8`. Work began from canonical
main `1f87c3578ae546c8f903f7f4d83dc2e2fb99650b`, priority revision 7,
under the `p104-side-correction` card. The scope changes from constructing a
correction word to screening any proposal that combines several *local FULL*
row and column charts inside the same `F81` address space.
Before publication, canonical main advanced to
`b21331d1` without changing the selected record, priorities, card, or the
relevant P104 packages.

Let `V = W = F₂⁹`. Let the row labels span `R ≤ V` of dimension `a`, and
the column labels span `C ≤ W` of dimension `b`. The available chart space is

```text
S = R ⊗ W + V ⊗ C  ≤  V ⊗ W.
```

Choose complements `V = R ⊕ R'` and `W = C ⊕ C'`. The tensor product splits
into four disjoint blocks. `S` contains `R⊗C`, `R⊗C'`, and `R'⊗C`; the only
missing block is `R'⊗C'`. Consequently

```text
dim S = 81 - (9-a)(9-b) = 9a + 9b - ab.
```

The single-pair case `a=b=1` gives dimension 17 and codimension 64, matching
#4153. Even eight independent row directions plus eight independent column
directions leave one dimension uncovered. Full linear coverage requires `a=9`
or `b=9`: at least nine independent labels of one orientation. This is a
necessary condition on stacked charts, not a construction of a legal source,
consumer, correction word or hardware schedule.

`verify.py` uses standard-library bitsets and a separate GF(2) rank routine to
check all 100 dimension pairs after two nonsingular changes of basis. Run:

```sh
python3 -B research/25ba61822819ac741f63afd895fa7ad8/verify.py
```

The check is finite corroboration of the proof, not a substitute for it. The
dimension law says nothing about whether a chart can be acquired, preserved
through a chronological cut, or returned dirty. It assigns no paid-child
tariff and does not improve or obstruct a complete supplier by itself. The
selected conditional result and the frozen #4153 package remain untouched.

## Open next questions

For one proposed P104 correction, identify the actual row and column labels
available at its source/consumer cut. First compute their ranks `a,b` and the
uncovered dimension above. If either rank reaches nine, the next step is a
literal ownership, dirty-restoration and full paid-cost check; chart span alone
does not establish those obligations. No such candidate is supplied here.

The #4153 source-chart tariff and its equality at the strict gate are credited
to unpaidmoon with Grok assistance, building on Chris R / Clear1nsight's
[#3978](https://github.com/CrocSwap/integer-mult-bounds/pull/3978). This note
and checker were prepared by OpenAI Codex under a donor grant. No independent
human review, new κ or frontier decision is claimed. Apache-2.0.
