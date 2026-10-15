# Top-level mixing bound for the P104 X-only `I-G/2` correction

This note proves the lifetime floors reported in `README.md` and records the exact 2×2 mixing test
behind them. The argument uses only the top two frame dimensions (7 and 8): a local invertibility
(determinant) argument for 2×2 mixing at shared 7-frames, plus a counting bound. It is not a
cut-set or crossing-capacity bound.

**Evidence status.** Every finite fact F1–F8 and F7′–F8′ below is recomputed by `verify.py` /
`top_primary.py` (primary implementation) and by `independent.py` (a separately written second
implementation). `verify.py` requires the two to agree on every count and histogram in `SHARED_KEYS`. The
structural parts (nesting, spans, set equalities) are asserted inside each implementation, which fails on its
own if one does not hold. The lemmas and the counting argument are written proofs; they are not machine-checked.
The argument is author-checked only. No human or proof-assistant review is claimed, and AI review passes
in the same loop are not human review.

## 1. Model

**Frozen inputs.** The source/target frame paths come from the pinned `LOWRANK-WITNESS.json`
(`0f541bef…`) and `P104-FIXTURE.json` (`516c06f6…`) of `research/p104-native-channel`, i.e. the frozen
PR #1972 / #1991 chronology.

**Frames.** A frame is a subspace of F₂⁹.
- Source `X_s` (s = 0..103) has a nested frame path `X_s(c)`, where `c` is the cut. It starts at the line `ℓ_s = ⟨q_s⟩`.
- Target `Y_t` has a nested path from ZERO through intermediate frames of dimension ≤ 6 to the hyperplane `H_t`.

**Checker grammar G.** This is the X-only monotone helper model of PR #2353, PR #2393 and PR #2445, exactly
as encoded by Philippe Van Velzen's published relay checker. That checker is vendored unchanged in
`vendor/check_p104_relay_construction.py`, from fork commit `fac9e821`.

A *lifetime* starts at ZERO with an independent dirty value. It moves only to strictly larger frames and ends
at FULL, so its frames form a chain. The operations are:
- *read*: `w += c·x_s`, only while `frame(w) = X_s(cut)`;
- *shear*: `w_i += c·w_j` with **`i ≠ j`**, only when the two frames are equal (the checker enforces both);
- *write*: `Y_t += c·w`, only while `frame(w) = Y_t(cut)`.

Reads and writes occur at nondecreasing cuts. There are **no** in-frame copies, clears, rescalings,
discards or other operations. Each shear is an elementary transvection `I + cE_ij` (`i ≠ j`, determinant
1), so all in-frame mixing in G is invertible. Our proof of the floor 219 uses this. In G′ the same argument
gives only 216; whether 219 holds in G′ is open.

**G is the checker's replay part.** G consists of the part-B replay rules of the checker and its completion
conditions. Part A computes the per-source line count 208 from the geometry alone and reads no word. Part C
prices a word and asserts `lifetimes > idle // 9 = 482` (vendored checker, line 117); it is not part of G. As
published, the checker therefore rejects every word with at most 482 lifetimes, including any word in the
387–482 window (§5). Such a word would have to be checked with the part-B replay alone. Both package replayers
apply only the part-B rules.

**Widened grammar G′.** The same frozen paths, reads and writes, and monotone lifetimes, plus:
- arbitrary rational linear maps among the lifetimes currently in one frame, including singular ones
  (copies `w_i := c·w_j`, clears `w_i := 0`, rescalings `w_i := c·w_i` with any rational `c`, including 0);
- lifetimes born at any frame with source-independent contents, and lifetimes that end at any frame. A lifetime
  born at `V` is treated as entering `V` from ZERO, so its previous frame is ZERO and its entry x-content is 0.

G′ contains the in-frame operations allowed by main's `research/p104-monotone-relay-floor-audit` (#2353), whose
network may make "arbitrary rational linear combinations, copies and clears of helpers within an equal frame".
The proofs below use neither dirty restoration nor the order of cuts. They therefore also hold if those are
relaxed, as in that audit. We have not audited every other difference between that model and G′, and the G′
statements are made for G′ as defined here.

**Completion.** A word is complete when every `Y_t` receives exactly row `t` of `C = I - G/2`, with no dirty
residue. In G every lifetime is also restored; restoration is not used below.

**Notation.**
- `L` is the number of lifetimes.
- `S(V)` is the set of sources whose line lies in `V`.
- `supp(t) = {s : C[t][s] ≠ 0}`.
- `I_t` is the last (largest) intermediate frame of `Y_t`, and `S_I(t) = S(I_t)`.
- `R_t = supp(t) \ S_I(t)`.

Two scopes are used:
- **Full model:** the whole grammar (G or G′).
- **Final-frame delivery class:** words in which every write that carries x-content happens while `Y_t` is at
  `H_t`. Writes at ZERO carry no x-content. Here `R_t = supp(t)`. This class contains:
  - relay-v2 (`WORD_ct12.json`, whose writes occur only at cuts 0 and 4058, checked with `verify.py --extra-word`);
  - relay-construction (its builder writes only at cuts 0 and 4058);
  - per-entry words that arrive into `H_t`, such as PR #2604's, by its stated 0→1→8→9 arrival shape;
  - the demonstration word of this package.

## 2. Finite facts

Each fact below is checked by both implementations. Its counts and histograms are compared by `verify.py`, and
its structural parts are asserted inside each implementation.

Zero counts cannot reveal a check that always returns 0. So each zero count below has a nonzero *companion*,
computed by the same function or expression with the filter removed or shifted:
- F2: the containment counts by dimension;
- F4: the shifted sum count (2,112);
- F5: the histogram of uncovered sources;
- F8 and the broad F8 check: the same searches without the `T` filter (2,112 each);
- F8′ in the final-frame class: the same search in the full model (12).

The diagonal count of F1 has no companion; it follows from the port norms, as stated there.

Credit: the facts that no three target hyperplanes share a 7-frame (F4), that each target's support splits
exactly under 127 hyperplane pairs (F6), that the sources lie in one affine hyperplane (F4), and that 384 of the
5,356 pairwise intersections carry proportional restrictions (F7′) were first reported by **Philippe Van Velzen**
in [#2245](https://github.com/CrocSwap/integer-mult-bounds/discussions/2245#discussioncomment-18951262)
("Geometry for the next attempt", 2026-10-15 14:34Z). This package re-derives them with two implementations and
uses them in the proof.

- **F1.** `supp(t) = S(H_t)`, with `|supp(t)| = 48` for all 104 rows and zero diagonal. All nonzero entries are ±1/2.
  - The diagonal is zero because `C[t][s] = δ_ts − ⟨p_t, p_s⟩/8` and every port has squared norm 8 in the fixture scaling. Combined with `supp(t) = S(H_t)`: for `s ≠ t`, `q_s ∈ H_t` exactly when `⟨p_s, p_t⟩ ≠ 0`, and `q_t ∉ H_t`.
- **F2.** Every `X_s` path is strictly nested and starts at `ℓ_s`. There are 312 X frames of dimension ≥ 7 on the paths, and none lies inside any `H_t`. Hence no read can occur at `H_t` or at a 7-frame inside it.
  - Companion statistic: the number of (X frame, target) pairs with the frame inside `H_t`. By frame dimension it is 4,992 / 144 / 156 / 144 / 92 at dimensions 1 / 3 / 4 / 5 / 6, and 0 at dimensions 7, 8 and 9. No X frame of dimension 2 occurs.
- **F3.** Every `Y_t` path is strictly nested from ZERO, and every intermediate frame has dimension ≤ 6 (the maximum is 6). The sizes `|S_I(t)|` are distributed as `{0:12, 1:24, 2:24, 3:8, 4:24, 12:12}`.
- **F4.** The 104 target normals are distinct and have odd weight (weights 1 / 3 / 5 / 7 / 9 occur 1 / 28 / 54 / 20 / 1 times). Hence no normal is the sum of two others: the sum of two odd-weight vectors has even weight. Both implementations also count such sums directly (0). A 7-frame lies in `H_a`, `H_b`, `H_c` only if its 2-dimensional annihilator contains `n_a, n_b, n_c`, which forces `n_c = n_a + n_b`. Hence a 7-frame lies in at most two target hyperplanes. All sources lie in the affine hyperplane `⟨u*, ·⟩ = 1`, `u* = 13`, and `u*` is not a target normal.
  - Companion statistic: the same pair-sum expression, aimed at the shifted set `{n_t + u*}`, finds 2,112 pairs. These are exactly the 2,112 triples `(t, {a, b})` whose halves `H_t ∩ H_a` and `H_t ∩ H_b` split `supp(t)`. Both implementations count those triples again by their complementarity test (source partitions in the primary, the identity `n_a + n_b = n_t + u*` in the second), and each requires the two counts to agree.
- **F5.** For every `t` and every hyperplane `K` of `H_t`, `R_t ⊄ S(K)`. This holds in both scopes (0 violations). In fact every hyperplane of `H_t` leaves at least 18 sources of `R_t` uncovered in the final-frame class, and at least 12 in the full model; both implementations report the per-target histogram of this minimum.
- **F6.** In the final-frame class, each target's support has exactly 127 two-covers `{K₁, K₂}` by hyperplanes of `H_t`. All of them are *complementary*: `S(K₁) ⊔ S(K₂) = supp(t)`. Each `S(K_i)` spans `K_i`.
- **F6′.** In the full model, 84 targets are *good*, and these are exactly the targets with `|S_I(t)| ∈ {0, 1, 2, 4}`. For a good target, every two-cover of `R_t` is complementary, and each `R_t ∩ S(K_i)` spans `K_i`. The other 20 targets are treated permissively below. The cover counts (all covers / complementary covers / targets) are 127 / 127 / 84, 130 / 127 / 8 and 175 / 127 / 12.
- **F7.** The pair test `T(t, a)` of Lemma 4 holds for:
  - 288 of the 5,356 pairs in the final-frame class (where `R = supp`). Of these, 240 have `|S(K)| = 18` split 9 + 9 and 48 have `|S(K)| = 20` split 10 + 10; in every one, each ratio class spans a 6-dimensional frame.
  - 414 pairs in the full model. 240 of them are good-good; only these have a proven meaning, because Lemma 4 is proved for certified pairs only.
- **F7′.** The singular-mixing test `T′(t, a)` of Lemma 4′ holds for 672 pairs in the final-frame class (the 288 of F7, whose two ratio classes are both nonempty, plus 384 pairs with a single ratio class, i.e. proportional restrictions) and for 1,038 pairs in the full model.
- **F8.** No certified target `t` has two certified partners `a ≠ b` with `T(t, a)`, `T(t, b)` and `S(H_t ∩ H_a) ⊔ S(H_t ∩ H_b) = supp(t)`. Here *certified* means every target in the final-frame class, and every good target in the full model. This holds in both scopes.
  - The primary checker tests complementarity through source partitions. The second implementation uses the equivalent normal identity `n_a + n_b = n_t + u*`, and asserts the equivalence on every cover.
  - A broader finite check also finds 0 triples: any target `t`, any partners `a ≠ b` with `T(t, a)` and `T(t, b)` in the full model, and any two-cover of `R_t` by `H_t ∩ H_a` and `H_t ∩ H_b`, complementary or not. This is a fact about the test, not a theorem about words with permissive targets.
- **F8′.** With `T′` in place of `T`: 0 certified targets in the final-frame class have two such partners, but in the full model 12 good targets do (targets 1, 3, 6, 7, 12, 14, 41, 46, 54, 74, 81 and 83). Both implementations list these IDs and `verify.py` compares the lists.

**Why F8 and F8′ hold (structural reading).** Two further finite facts, reported by both implementations, explain
them without the triple search:
- Every pair intersection has `|S(H_t ∩ H_a)| ∈ {18, 20, 22, 24}` (240 / 1,920 / 1,056 / 2,140 of the 5,356
  pairs). Complementary halves partition the 48 sources of `supp(t)`, so both halves have exactly 24 sources.
  Indeed all 2,112 complementary triples are 24 + 24. In the full model every two-cover of `R_t` by two pair
  halves is complementary (2,112 such triples, for any target), so the same holds there.
- No pair passing `T` has `|S(K)| = 24`. The `T`-pairs have `|S(K)| = 18` or `20` in both scopes: 240 + 48 in the
  final-frame class and 240 + 174 in the full model (168 + 72 good-good).

Hence F8, and the broad F8 check, hold in both scopes. `T′` adds 384 pairs with `|S(K)| = 22` in the final-frame
class. These cannot be complementary halves, so F8′ is 0 there. In the full model `T′` also adds 240 pairs with
`|S(K)| = 24`, 120 of them good-good, and these produce the 12 exempt targets.

## 3. Lemmas

**Lemma 1 (support; G and G′).** At every time, the x-content of a lifetime lies in `S(frame)`.

*Proof.* Reads at `X_s(c)` add `x_s`, and `q_s ∈ X_s(c)` by F2. In-frame operations combine lifetimes in the
same frame. Fresh lifetimes (G′) carry no x-content. Moves only enlarge the frame. ∎

**Lemma 2 (mixing at one frame).** Let `V` be a frame at which no read can occur. Let `w_1..w_n` be all
lifetimes whose chains contain `V`, with x-contents `e_i` on entering `V` and `f_i` on leaving it (a lifetime
born at `V` has `e_i = 0`). Then `f = M e` for a rational matrix `M`, and every value any lifetime holds while at
`V` lies in `span{e_i}`. In G, `M` is a product of elementary transvections and is therefore invertible.

*Proof.* While a lifetime is at `V`, only in-frame operations with other lifetimes at `V` change it, and these
are linear. A lifetime that has not yet entered `V`, or has already left, takes part in none of them. So the
operations act on the tuple of entry values in time order. In G each of them is a shear `I + cE_ij` with
`i ≠ j`. ∎

**Lemma 3 (target entry; G and G′).** Let `B_t` be the set of lifetimes whose chain contains `H_t`, and
`b_t = |B_t|`.
- (a) `b_t ≥ 2`. Summed over the 104 targets, this is the 208 floor. The number 208 comes from Philippe Van
  Velzen's correction screen (#2245). Hiroki Kumazaki's PR #2353 (merged as
  `research/p104-monotone-relay-floor-audit`) proved it for arbitrary monotone relay networks. Part A of the
  vendored relay checker reaches the same total by the dual per-source count: two departures from each source
  line (also ywz65's #2614). That is a different bound, because one lifetime can be both a departure and an
  arrival. The proof of (a) is repeated here because (b) builds on it.
- (b) Suppose `t` is good (or we are in the final-frame class) and `b_t = 2`. Then the two lifetimes pass
  through the two halves `K₁ ≠ K₂` of one complementary two-cover. The one through `K_i` leaves `K_i` with a
  value equal to a nonzero multiple of `C_t` on `R_t ∩ S(K_i)`. The number `n_{K_i}` of lifetimes through `K_i`
  is at least 2.

*Proof of (a).* By F2 no read occurs at `H_t`, so Lemma 2 applies at `H_t`: everything written at `H_t` lies
in `span{u_w : w ∈ B_t}`. Here `u_w` is the value of `w` on entering `H_t`; by Lemma 1 it is supported on
`S(W_w)`, where `W_w ⊊ H_t` is the previous frame. Writes at intermediate frames are supported on `S_I(t)`, and
writes at ZERO carry no x-content. Hence `Σ c_w u_w ≡ C_t` on `R_t`. Since `C_t` is nonzero on the nonempty set
`R_t`, `b_t ≥ 1`. If `b_t = 1`, then `R_t ⊆ S(K)` for any hyperplane `K ⊇ W_w` of `H_t`, contradicting F5.

*Proof of (b).* Let `B_t = {w₁, w₂}`, with previous frames `W₁, W₂ ⊊ H_t`. If `W₁` and `W₂` lay in one
hyperplane `K` of `H_t`, then `R_t ⊆ S(K)`, contradicting F5. So choose any hyperplane `K₂ ⊇ W₂` of `H_t`; then
`W₁ ⊄ K₂`, and any hyperplane `K₁ ⊇ W₁` differs from `K₂`. By the proof of (a), each `s ∈ R_t`
lies in `supp(u₁) ∪ supp(u₂) ⊆ S(K₁) ∪ S(K₂)`, so `{K₁, K₂}` is a two-cover of `R_t`. By F6 or F6′ it is
complementary, so `u₂ = 0` on `S(K₁)`. Then `c₁u₁ = C_t` on `R_t ∩ S(K₁)`. Also `c₁ ≠ 0`: otherwise
`R_t ⊆ supp(u₂) ⊆ S(K₂)`, contradicting F5. By F6/F6′ the set `R_t ∩ S(K₁)` spans `K₁`, and it lies in
`supp(u₁) ⊆ S(W₁)`, so `W₁ ⊇ K₁`; hence `W₁ = K₁`. The same holds for `K₂`.

The lifetime `w₁` enters `K₁` from a proper subframe (possibly ZERO), so its entry value is supported on a
proper subspace of `K₁`. Its exit value `u₁` is not, because its support contains `R_t ∩ S(K₁)`, which spans
`K₁`. No read occurs at `K₁` (F2). If `n_{K₁} = 1`, Lemma 2 gives `M = (1)` in G and a scalar `M` in G′, so the
exit value is a multiple of the entry value: a contradiction. So `n_{K₁} ≥ 2`. ∎

**Lemma 4 (two lifetimes at a shared half; G).** Let `t` and `a` both satisfy Lemma 3(b), and let
`K = H_t ∩ H_a` be a half for both. Suppose `n_K = 2`. Define:
- `B = S(K) ∩ R_t ∩ R_a`, split into `B₊` and `B₋` by the sign of `C[a][s]/C[t][s]` (always ±1);
- `F = S(K) ∩ (R_t Δ R_a)`.

Then there is a partition `F = F₁ ⊔ F₂` and an assignment `{X, Y} = {B₊, B₋}` such that both
`span(X ∪ F₁)` and `span(Y ∪ F₂)` are proper subspaces of `K`. Call this test `T(t, a)`.

*Proof.* Let the two lifetimes enter `K` from `V₁, V₂ ⊊ K` with values `e₁, e₂`. By F2 and Lemma 2,
`(f_t, f_a) = M(e₁, e₂)` with `M = [[α, β], [γ, δ]]` invertible. By Lemma 3(b), `f_t` is a nonzero multiple of
`C_t` on `R_t ∩ S(K)` and `f_a` a nonzero multiple of `C_a` on `R_a ∩ S(K)`. So every `s ∈ B ∪ F` has
`e₁(s) ≠ 0` or `e₂(s) ≠ 0`, and by Lemma 1, `B ∪ F ⊆ S(V₁) ∪ S(V₂)`.

On `B ∩ (S(V₁) \ S(V₂))` we have `e₂ = 0`, so the ratio `f_a/f_t = γ/α` is constant there and the sign class is
constant. Similarly the ratio is `δ/β` on `B ∩ (S(V₂) \ S(V₁))`. If both sets are nonempty with the same class,
then `γ/α = δ/β`, so `αδ = βγ`, contradicting invertibility. Hence there is an assignment such that no
element of `X` lies in `S(V₂) \ S(V₁)` and no element of `Y` lies in `S(V₁) \ S(V₂)`:
- if `B ∩ (S(V₁) \ S(V₂))` is nonempty, let `X` be its class (and `Y` the other);
- otherwise, if `B ∩ (S(V₂) \ S(V₁))` is nonempty, let `Y` be its class;
- otherwise assign arbitrarily.

Since `B ⊆ S(V₁) ∪ S(V₂)`, this gives `X ⊆ S(V₁)` and `Y ⊆ S(V₂)`. Put `F₁ = F ∩ S(V₁)` and
`F₂ = F \ F₁ ⊆ S(V₂)`. The two spans lie in `V₁` and `V₂`, which are proper subspaces of `K`. ∎

In the final-frame class, `F = ∅` and `T(t, a)` reduces to: each ratio class spans a proper subspace of `K`
(an empty class spans `{0}`).

**Lemma 4′ (singular mixing; G′).** Under the hypotheses of Lemma 4 in G′, `T(t, a)` holds or `B` is a single
ratio class (possibly empty). Call this test `T′(t, a)`.

*Proof.* If `M` is invertible, the proof of Lemma 4 applies unchanged. `M ≠ 0` because `f_t ≠ 0`. If `M` has
rank 1, its rows are proportional and `f_t ≠ 0`, so `f_a = λ f_t` with `λ ≠ 0`. Then
`C[a][s]/C[t][s]` is the same constant on all of `B`, so `B` is a single ratio class. ∎

## 4. Theorem

**Theorem.**
- In G, every complete word has `L ≥ 219` (full model) and `L ≥ 234` (final-frame class).
- In G′, every complete word has `L ≥ 216` (full model) and `L ≥ 234` (final-frame class).

*Proof.* Moves strictly enlarge frames, so each lifetime's frames form a chain. Hence each lifetime lies in at
most one `B_t` and passes at most one 7-frame. Let `J` be the number of lifetimes in no `B_t`. Then

    L = Σ_t b_t + J,    E := L − 208 = Σ_t (b_t − 2) + J ≥ 0    (Lemma 3a).

Call `t` *tight* if `b_t = 2`. Call it *certified* if it is good (full model) or if we are in the final-frame
class. Every other target is *permissive*.

For a tight certified `t`, Lemma 3(b) gives two halves. Call the half `(t, K)` *perfect* if:
- `n_K = 2`; and
- the other lifetime at `K` lies in `B_a` for a tight certified `a`.

That lifetime passes `K` and then `H_a`. Its frame just before `H_a` is a proper subspace of `H_a` containing
`K`, hence equal to `K`. So `K` is one of `a`'s halves (Lemma 3(b) for `a`). Lemma 4 then gives `T(t, a)` in G, and
Lemma 4′ gives `T′(t, a)` in G′. Call a certified target *exempt* if it is one of the F8′ targets and we are in
G′ (full model); otherwise no certified target is exempt. By F8 and F8′, no tight certified non-exempt target
has two perfect halves. So the number of *imperfect* halves is at least

    p ≥ (number of tight certified targets) − e,

where `e` is the number of exempt targets: `e = 0` in G and in the G′ final-frame class, and `e = 12` in the G′
full model.

Fix an imperfect half `(t, K)`. By Lemma 3(b), `n_K ≥ 2`. Let `w` be `t`'s lifetime at `K`. No other lifetime at
`K` is in `B_t`: `t`'s other lifetime passes the other half, and a lifetime passes only one 7-frame. A lifetime
at `K` that lies in some `B_a` passes `K ⊂ H_a`, and by F4 there is at most one such `a ≠ t`. A tight `a` has at
most one lifetime through `K`: if both did, both would enter `H_a` from `K`, and then `R_a ⊆ S(K)`, contradicting
F5. Exactly one of the following cases therefore holds:
- **(γ)** some other lifetime at `K` lies in no `B_*`. This covers `n_K ≥ 3` with `a` tight (certified or not),
  since at most one of the other lifetimes can then be in `B_a`.
- **(δ)** no other lifetime at `K` is junk, and they lie in `B_a` for a non-tight `a`.
- **(ε)** `n_K = 2` and the other lifetime lies in `B_a` for a tight permissive `a`.

(If `n_K = 2` and the other lifetime lies in `B_a` for a tight certified `a`, the half is perfect, not imperfect.)

The three cases are charged as follows:
- A junk lifetime passes one 7-frame `K`, which lies in at most two target hyperplanes (F4). So it witnesses at
  most two γ-halves, and `J ≥ ⌈h_γ/2⌉`.
- Each δ-witness is a lifetime of `B_a` with `a` non-tight. It passes one 7-frame, where only one half belongs to
  a target other than `a`, so it witnesses at most one δ-half. Hence `h_δ ≤ Σ_{non-tight} b_a = X + 2m`, where
  `m = m_c + m_p` is the number of non-tight certified and permissive targets and
  `X = Σ_{non-tight} (b_a − 2) ≥ m`.
- In the same way, `h_ε ≤ 2·#{tight permissive} = 2(π − m_p)`, where `π` is the number of permissive targets.

Let `c` be the number of certified targets. Then

    h_γ ≥ p − h_δ − h_ε ≥ (c − m_c − e) − (X + 2m_c + 2m_p) − 2(π − m_p) = A − 3m_c − X,
    where A = c − e − 2π,

and `E = X + J ≥ X + max(0, ⌈h_γ/2⌉)`. Since `X ≥ m_c`:
- `E ≥ X ≥ m_c`;
- `E ≥ X + (A − 3m_c − X)/2 = (A − 3m_c + X)/2 ≥ A/2 − m_c`.

The two lower bounds sum to `A/2`, so their maximum is at least `A/4`, and `E ≥ ⌈A/4⌉` because `E` is an integer.
The four cases are:

| Grammar, scope | `c` | `π` | `e` | `A` | `E ≥` | `L ≥` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| G, final-frame class | 104 | 0 | 0 | 104 | 26 | **234** |
| G, full model | 84 | 20 | 0 | 44 | 11 | **219** |
| G′, final-frame class | 104 | 0 | 0 | 104 | 26 | **234** |
| G′, full model | 84 | 20 | 12 | 32 | 8 | **216** |

∎

The exhaustive integer search in `top_primary.py` and the direct search in `independent.py` confirm that `⌈A/4⌉`
is the exact minimum of these inequalities in all four cases (attained at `m_c = X = ⌈A/4⌉`, `m_p = 0`), and
`independent.py` also evaluates the closed form. The three computations start from the same inequalities: they
check the arithmetic, not the derivation above. The minimum of the inequalities is not a claim that words with
219, 234 or 216 lifetimes exist.

**Strength and limits.**
- All four floors are strictly above the arrival floor 208 (Van Velzen's correction screen; proved for relay
  networks in #2353; Lemma 3a).
- To our knowledge they are the first all-target, all-shape floors above 208 with a written proof in the
  relay-permitting model. Relay-v2's unproved same-model estimate `L ≳ 387` (§5) is stronger.
- They are far below the decision window (§5) and below every fixed-template allowance at the selected saving:
  333 for nine rank-1 steps, 431 for `{1,1,1,1,5}`, 478 for `{1,1,1,6}` and 482 for `{1,1,7}`. They do not reject
  the X-only route.
- The proved top-level excess (26 in the final-frame class, 11 in the full model) is under a tenth of the 274
  lifetimes of slack between 208 and 482. The top-level obstruction alone therefore does not exclude a mixer
  design in the window.
- The argument charges nothing for gathering below the 7-frames, and does not localize relay-v2's measured merge
  loss (823).
- Permissive targets and absorption by non-tight targets are counted as favourably as the argument allows. Both
  floors are therefore safe but loose. For example, if each non-tight target `a` could absorb at most `b_a − 1`
  imperfect halves (an unproved restriction, Open next question 3), the same counting would give `E ≥ 35`, i.e.
  `L ≥ 243`, in the final-frame class; `L ≥ 260` would need absorption excluded entirely. Both conditional values
  are recomputed by both implementations.
- **A sharper count, not adopted here (sketch).** The charging above lets one junk lifetime witness two γ-halves,
  even at a half that lies in no other target hyperplane. Call such a half *private*. By F4 every half of a
  tight certified target `t` is either a pair half `H_t ∩ H_a` or private.
  - At a private half every other lifetime is junk: it cannot lie in `B_a` for `a ≠ t`, and `t`'s other lifetime
    passes the other half. That junk passes only this 7-frame, so it witnesses no other half and is neither
    shared nor absorbed.
  - Pair halves hold at most 24 sources (§2), so a complementary cover by two pair halves is 24 + 24. No
    `T`-pair has `|S(K)| = 24` (nor any `T′`-pair in the final-frame class), so neither half of such a cover
    is perfect. Equivalently, every perfect half has a private complement.
  - So each tight certified target has a private γ-half, which costs one unshared junk lifetime, or two
    imperfect pair halves. Writing `τ_A + τ_B = c − m_c` for the two kinds,
    `E ≥ X + τ_A + max(0, ⌈(2τ_B − (X + 2m) − 2(π − m_p))/2⌉)`. The exact minimum is 42 in the final-frame
    class (G and G′) and 26 in the G full model, which would give `L ≥ 250` and `L ≥ 234`.
  - Status: proposed by an AI review pass in this loop's last review round, and re-checked in a scratch
    computation in this loop (a census of all complementary covers and an exact minimisation). It is not part
    of the Theorem above or of the registered replay, and it has not had the review the stated floors received
    (README Open next question 6). The G′ full-model value was not computed, because there `T′` admits pairs
    with `|S(K)| = 24`. No decision changes: 250 is below 333.

## 5. Window ends and why no construction was attempted

- **387** is the lower end of the window. It comes from Philippe Van Velzen's relay-v2 README (fork
  `fac9e821`), which says in full: "No floor above 255 is proved. A sharing count gives only L ≳ 387." In that
  README 255 is merge loss `L − 208`: its relay cap is "≤ 463 lifetimes (merge-loss ≤ 255)". We read the second
  sentence as an unproved lower estimate of about 387 lifetimes in the same relay-permitting model. No
  derivation or checker for it is published. If established, it would supersede the floors proved here, which are
  weaker but have a written proof. We use 387 only as a window end; nothing here depends on it.
- **482** is the `{1,1,7}` idle-mass allowance of Philippe Van Velzen's window bill (#2245), reproduced here at
  the selected saving with merged `ceiling.py`. Relay-v2's README caps any relay design at ≤ 463 lifetimes,
  arguing that an arrival lifetime "must pass H_t and then FULL" and so cannot have the `{1,1,7}` shape (463 is
  its `{1,1,1,6}` allowance at PR #2559's saving; at the selected saving that allowance is 478).
  Per-entry arrivals ZERO → line → `H_t` → FULL (PR #2604's 0→1→8→9) have the step multiset `{1,1,7}`, which is
  what the fixed-template screen prices, so we quote the larger 482. All floors lie below both caps, so the
  choice does not matter here.
- The mixer design was priced first and failed the pricing gate. A complete design would have to bring the whole
  merge loss into the window, and no lower-level gathering design could be named or priced into it. The
  top-level test of Lemma 4 shows only that lossless 2×2 mixing at shared 7-frames is isolated (F7) and never
  serves both halves of a certified target (F8). As noted above, that obstruction uses only a small part of the
  slack, so it is not by itself a refutation of mixer designs.

**Heuristic, not a theorem.** We expect that arguments using only the 7- and 8-dimensional frames cannot exceed
`4 × 104 = 416`. Locally, each half `K` can be served by two lifetimes entering from the two hyperplanes of `K`
with functionals `v` and `v + u*`. Their union contains every source of `K`, because a source has `⟨u*, q⟩ = 1`.
This satisfies every condition used in this note. We have not defined "top-level argument" formally or
certified a global 416-lifetime configuration. This 416 is unrelated to #2586's 416 endpoint transports.

## 6. Multi-value carriage is realizable, but only locally

`T(0, 1)` holds. For `K = H_0 ∩ H_1`, `|S(K)| = 18`. The nine `+` sources span a 6-frame `W`, and the nine `−`
sources span `W'`.

The demonstration word gathers these classes into one lifetime at `W` and one at `W'`. Both move to `K`, where
two shears are applied: `P += R` and `R += (−1/2)P`. `P` then leaves `K` carrying `C_0|S(K)`, and `R` leaves
carrying `−C_1|S(K)/2`.

Every other entry uses a dedicated lifetime. The unchanged published checker accepts the complete word (4,974
lifetimes), and so do both package replayers.

So one invertible mixer lets two lifetimes deliver two different targets' half rows with no loss at `K`. The 16
non-carrier gathering lifetimes are merge loss at `W` and `W'`. The word is realized and replayed only for the
pair (0, 1); for the other pairs F7 is a necessary test, not a construction. The word is a positive control for
Lemma 4, not a candidate: its mass far exceeds the idle cap.

## 7. Side certificate: geometry lemma (not used by the floors)

For every source-spanned frame `F` of dimension 1–4, `|S(F)|·|T(F)| ≤ 48`, where `T(F)` is the set of targets
whose hyperplane contains `F`. Equality holds in every dimension. The affine bound used by relay-v2 and PR #2675
is 128.

| Dimension | Source-spanned frames | Shape attaining 48 | Frames attaining it |
| ---: | ---: | --- | ---: |
| 1 | 104 | 1 × 48 | 104 |
| 2 | 5,356 | 2 × 24 | 2,140 |
| 3 | 128,230 | 4 × 12 | 168 |
| 4 | 1,264,801 | 6 × 8 | 280 |

How each column is checked:
- The primary implementation enumerates all source-spanned frames breadth-first, as point masks with
  incremental incidence. It produces the frame counts, the maximum, the shapes and the equality counts.
- The second implementation enumerates source subsets with E8 inner-product incidence, without enumerating
  frames. It confirms the maximum and the set of shapes attaining it, but it does not count frames.

A written proof was attempted and **not** obtained. The statement is a finite exhaustive certificate only.
