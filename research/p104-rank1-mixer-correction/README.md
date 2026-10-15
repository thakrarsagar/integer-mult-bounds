# P104 X-only `I-G/2` correction: a top-level mixing bound, lifetime floors 219 / 234 and the 2×2 mixer test

**Research note: scoped proof plus finite certificates.**

This note is not a construction in the decision window. It makes no supplier or κ claim, and the selected frontier is unchanged.

**TL;DR.**
- **Proved:** every complete all-104-target X-only correction word needs at least 219 new helper lifetimes in the published checker's replay grammar, at least 216 if singular in-frame copies and clears are allowed, and at least 234 in the final-frame delivery class that contains relay-v2. To our knowledge these are the first all-target, all-shape floors above 208 with a written proof in the relay-permitting model.
- **No decision changes:** every floor is below each fixed-template allowance (333–482) and below relay-v2's unproved same-model estimate `L ≳ 387`.
- **What lasts:** the 2×2 mixer test with F8 (with invertible mixing, grammar G, no certified target can have both halves served by lossless two-lifetime mixing at its 7-frames; with singular mixing 12 good targets escape, F8′), the dependence of the proof on invertible mixing (219 versus 216), and the heuristic pointer that a decisive floor must charge gathering below the 7-frames.
- **Construction:** multi-value carriage is built, and accepted by the published checker, only for the pair (0, 1).

## Statement

The object is the all-104-target correction `C = I - G/2` on the frozen P104 source and target frame paths of the native channel (PR #1972 / #1991).

**Grammars.**
- **G (checker grammar)** is the X-only monotone helper model of PR #2353, #2393 and #2445, taken exactly as encoded by Philippe Van Velzen's published relay checker. The checker is vendored unchanged in `vendor/` from fork commit `fac9e821`. Its only in-frame operation is the shear `w_i += c·w_j` with `i ≠ j` between lifetimes in one frame, so in-frame mixing is always invertible.
  - G is the checker's part-B replay rules together with its completion conditions. Part A (the per-source line count 208) depends only on the geometry, and part C (pricing) is not part of G.
  - Part C asserts `lifetimes > idle // 9 = 482` (vendored checker, line 117). So, as published, the checker rejects every word with at most 482 lifetimes, including any word in the 387–482 window. Such a word would have to be checked with the part-B replay alone. The package's own replayers apply only the part-B rules, and the demonstration word (4,974 lifetimes) passes all three parts.
- **G′ (widened grammar)** adds singular in-frame operations (copies, clears and rescalings, including by 0) and lifetimes born or ended at any frame. The proof uses neither dirty restoration nor cut order, so relaxing those changes nothing. G′ contains the in-frame copies and clears allowed by main's `research/p104-monotone-relay-floor-audit` (#2353). We have not audited every other difference from that model.

**1. Proved lifetime floors above 208.** Every complete correction word has at least this many new helper lifetimes:

| Scope | G (invertible in-frame mixing) | G′ (singular in-frame mixing allowed) |
| --- | ---: | ---: |
| Full model | **219** | **216** |
| Final-frame delivery class | **234** | **234** |

- In the *final-frame delivery class*, every write that carries x-content happens while `Y_t` is at `H_t`. The class contains:
  - relay-v2 (checked: its writes occur only at cuts 0 and 4058);
  - the relay construction (its builder writes only at cuts 0 and 4058);
  - per-entry words with arrivals into `H_t`, such as PR #2604's;
  - this package's demonstration word.
- The written proof is in [PROOF.md](PROOF.md). It uses only the top two frame dimensions (7 and 8): a 2×2 invertibility argument at shared 7-frames plus a counting bound with closed form `E ≥ ⌈A/4⌉`. It is not a cut-set or crossing-capacity bound.
- Our proof of 219 uses invertible in-frame mixing. If singular mixing is allowed, the 2×2 test weakens (Lemma 4′), 12 good targets escape it, and the same argument gives only 216. Whether 219 holds in G′ is open; no G′ word with fewer than 219 lifetimes is known or claimed. The final-frame floor 234 holds in both grammars.
- **Novelty, and its limits.** To our knowledge, these are the first all-target floors above 208 with a written proof in the relay-permitting X-only monotone helper model (relays and all lifetime shapes allowed). Novelty rests on an overlap search, which is not proof of novelty.
- **A stronger, unproved estimate exists in the same model.** Relay-v2's README (fork `fac9e821`) says: "No floor above 255 is proved. A sharing count gives only L ≳ 387." There, 255 is merge loss `L − 208`: the same README caps relay designs at "≤ 463 lifetimes (merge-loss ≤ 255)". So the first sentence says that no floor that rejects relay designs is proved. We read the second as an unproved lower estimate of about 387 lifetimes in the same relay-permitting model; no derivation or checker for it is published. If it were established, it would supersede the floors here. Ours are weaker, but they have a written proof and a replay.
- **Floors with different scopes:**
  - no-relay access-cover minima are far above 208: 4,480 in Philippe Van Velzen's correction screen and 4,580 in #2392 (commdata2338, merged as `research/p104-no-relay-cover-audit`);
  - #2640 (Nick Petalas) proves at least 4,680 for homogeneous `{1,1,7}` shapes only, and states that it does not improve the unrestricted 208;
  - #2383 (commdata2338, merged as `research/p104-private-code-relay-floor`) and #2467 (ywz65, open) keep the 208 floor when the network may also read the eight-dimensional root code freely, or read every original helper at its actual frame. The floors here are **not** claimed under those extra reads (Open next question 5).

**2. The 2×2 mixer test.** Suppose exactly two lifetimes pass a shared 7-frame `K = H_t ∩ H_a` and leave it carrying the two targets' half rows. This is lossless multi-value carriage. For two certified targets in G it is possible only if the test `T(t, a)` holds (PROOF.md, Lemma 4). Every target is certified in the final-frame class; in the full model the 84 good targets are.
- *Final-frame class:* `T(t, a)` holds for **288 of the 5,356 target pairs**. 240 have `|S(K)| = 18` split 9 + 9 and 48 have `|S(K)| = 20` split 10 + 10; every ratio class spans a 6-frame.
- *Full model:* `T(t, a)` holds for 414 pairs, but Lemma 4 is proved only for pairs of certified ("good") targets. The meaningful count is therefore the **240 pairs between the 84 good targets**. The other 174 pairs involve a permissive target, for which `T` is computed but not proved necessary.
- **No target in the final-frame class, and no good target with two good partners in the full model, can have both of its halves served this way** (finite fact F8). A broader finite check also finds no hit when the target, its partners and the two-cover of `R_t` are unrestricted. That check is a fact about the test, not a theorem about permissive targets.
- *Why F8 holds.* Complementary halves split the 48 sources of `supp(t)`, and a pair intersection holds at most 24 sources, so both halves hold exactly 24 (all 2,112 complementary triples are 24 + 24). No pair passing `T` has `|S(K)| = 24`: every `T`-pair has 18 or 20. Both implementations report these histograms (PROOF.md §2).
- *Singular mixing (G′, Lemma 4′):* the weaker test `T′` holds for 672 final-frame pairs. These are the 288 above plus 384 pairs with proportional restrictions, a count first reported by Philippe Van Velzen. It holds for 1,038 full-model pairs. No final-frame target has two such halves, but 12 good targets do (targets 1, 3, 6, 7, 12, 14, 41, 46, 54, 74, 81 and 83). This is why the G′ full-model floor is 216.

**3. Multi-value carriage is realizable, but we built it for only one pair.**
- *The word.* It uses one invertible 2×2 mixer at `K = H_0 ∩ H_1`. Nine lifetimes gather the `+` ratio class into a 6-frame `W`, and nine gather the `−` class into `W'`. The two carriers meet at `K` and are mixed by two shears; they then leave carrying `C_0|S(K)` and `-C_1|S(K)/2`. Every other entry gets a dedicated lifetime.
- *The replay.* The **unchanged published checker** prints `PASS_P104_RELAY_CONSTRUCTION lifetimes=4974 per_target=47.83 line_floor=208 idle_cap=482`. Both package replayers agree.
- *Scope.* `T(t, a)` is only a necessary test. For the other 287 final-frame pairs that pass it, multi-value carriage is not constructed here.
- *Relation to PR #2445.* The 78 lifetimes serving Y0 and Y1 equal Ross Richardson's proved two-target minimum (PR #2445). His reversible two-total basis in the common frame is the same sharing idea.
- This word is a positive control for Lemma 4, not a candidate.

## Why no construction was attempted

The planned work was to price a complete rank-one-mixer design first. A word would be built only if a named design could reach the window `L ≈ 387–482` with a per-lifetime profile passing the PR #2675 fixed-template ideal-idle screen at the selected complex saving 0.0016754627.

**Window ends.**
- 387 is relay-v2's unproved sharing-count lower estimate, quoted above. It serves only as a window end; nothing here depends on it.
- 482 is the `{1,1,7}` idle-mass allowance of Philippe Van Velzen's window bill (#2245), reproduced here at the selected saving.
- Relay-v2's README also caps any relay design at ≤ 463 lifetimes, arguing that an arrival lifetime "must pass H_t and then FULL" and so cannot have the `{1,1,7}` shape. (463 is its `{1,1,1,6}` allowance at PR #2559's saving; at the selected saving that allowance is 478.) Per-entry arrivals ZERO → line → `H_t` → FULL (PR #2604's 0→1→8→9) have the step multiset `{1,1,7}`, which is what the screen prices, so we quote 482. Every floor here is below both caps.

**Why the design failed the pricing step.**
- The mixer design relies on lossless invertible mixing of block values at shared frames.
- A complete design must also bring the merge loss below the 7-frames into the window. No lower-level gathering design could be named or priced into it. Relay-v2's measured total merge loss is 823, and this note does not localize it.
- The top-level test (F7, F8) shows that lossless 2×2 mixing is isolated and never serves both halves of a certified target. The proved top-level excess, however, is only 26 (final-frame class) or 11 (full model) of the 274 lifetimes of slack between 208 and 482. So the test alone does **not** refute mixer designs. The design failed because no complete design could be priced, not because the test excludes it.

No word in the window was built and no search was run. The bounded alternative was the lower bound above.

## Decision consequence (scoped)

**Scope.** This note concerns the X-only monotone correction route of #2245, as screened by the PR #2675 fixed template and the window bill. It says nothing about:
- #2586's nonmonotone physical inverse-transpose, whose frame-decreasing endpoint conversions lie outside both grammars;
- the PR #2458 + PR #2712 pair consumer. Concurrent PR #2741 (Nick Petalas) rejects it at the selected saving for every pair count, even with the other corrections supplied free. That PR extends Jose Manuel's (jmbarrancoml) four-pair screen in #2619. Concurrent PR #2744 (flyingviper) audits the consumer's cost credits and the PR #2725 stopping decision.

**Within that route, the floors neither reject nor open it.** At the selected saving, the fixed-template allowances are:
- 333 for nine rank-1 steps;
- 431 for `{1,1,1,1,5}`;
- 478 for `{1,1,1,6}`;
- 482 for `{1,1,7}`.

All of them are above every floor. The useful change is where future work should look:
- No construction path into the window is named. Further mixer constructions or searches need a new lower-level idea first.
- *Heuristic, not a theorem:* we expect that arguments using only the 7- and 8-dimensional frames cannot exceed `4 × 104 = 416`. Locally, each half can be served by two lifetimes entering from two complementary hyperplanes of `K`, and that satisfies every condition used here (PROOF.md §5). We have not certified a global 416-lifetime configuration, and this 416 is unrelated to #2586's 416 endpoint transports.
- If that expectation is right, a floor above 482 must charge gathering below the 7-frames (Open next question 1).

**Optimistic complete ledger for the mixer design.**

| Term | Status |
| --- | --- |
| Lifetimes through the 104 target hyperplanes: ≥ 208 | proved (number from Philippe Van Velzen's correction screen; relay-network proof in #2353; restated as Lemma 3a) |
| At least one imperfect half per tight certified target; top-level excess ≥ 26 (final-frame) or ≥ 11 (full, G) | proved here |
| Merge loss below the top two levels | UNKNOWN, not zero (relay-v2's total merge loss is 823) |
| Hosting: ≥ 104 new helpers live over cuts 1104–2525 on top of 72 channel roles | author-checked claim in the #2245 window bill (Philippe Van Velzen), not re-proved here |
| Owner windows, native recipes for new transports, dual orientation, precision, all-size admission | UNKNOWN |
| Value ceiling | the bit cap 0.0017334270 |

## Side certificates (not used by the floors)

4. **Geometry lemma (finite certificate).** For every source-spanned frame of dimension 1–4, `|S(F)|·|T(F)| ≤ 48`. Here `S(F)` is the set of sources in `F` and `T(F)` the set of targets with `F ⊆ H_t`. The affine bound used by relay-v2 and PR #2675 is 128.
   - Equality holds in every dimension, attained by 104 frames of shape 1×48, 2,140 of 2×24, 168 of 4×12 and 280 of 6×8.
   - The primary enumerates all 104 / 5,356 / 128,230 / 1,264,801 source-spanned frames and produces these counts. The second implementation enumerates source subsets instead; it confirms the maximum 48 and the four shapes but does not count frames.
   - A written proof was attempted and **not** obtained.
5. **Frame-class block inventory.** A block is `S(F) × class`, where a class is a maximal set of targets in `T(F)` whose rows are proportional on `S(F)`. It is maximal within `T(F)` for that frame, not over all frames. Blocks with at least 40 entries:
   - dim 2: 2,112 of 2×23 and 384 of 2×22;
   - dim 3: 768 of 3×15, 7,040 of 3×14 and 168 of 4×10;
   - dim 4: 280 of 6×8, 4,480 of 6×7, 3,360 of 5×8 and 2,880 of 4×10.

   This inventory is produced by the primary implementation only.

## What is new relative to predecessors

- **Philippe Van Velzen** produced the relay construction, relay-v2 at 1,031 lifetimes, the cell-tree and flag designs, the published checker and the window bill. In #2245 he asked to "prove loss > 274". The number 208 is his, and so are several geometric facts used here (credited at F4, F6 and F7′ in PROOF.md): no three targets share a 7-frame, 127 splitting hyperplane pairs per target, the affine hyperplane `u*`, and the 384 proportional pairs. The new step is a top-level mixing bound with a written proof. It is not the cell-tree pool identity, it charges no lower-level loss, and relay-v2's unproved estimate `L ≳ 387` is stronger.
- **Hiroki Kumazaki** (#2353, merged as `research/p104-monotone-relay-floor-audit`) proved the 208 floor for arbitrary monotone relay networks with in-frame copies and clears: two arrivals per target hyperplane. Lemma 3(a) restates that per-target arrival bound.
  - **ywz65** (#2614) proved the dual bound of two departures per source line. That per-source count is the one in part A of the relay checker. It also totals 208 but is a different bound, since one lifetime can be both a departure and an arrival.
- **Ross Richardson** (#2445) proved the exact two-target minimum 78 for Y0/Y1. The 2×2 test here is a necessary condition, evaluated for **all** 5,356 pairs, for two lifetimes to carry such a basis through the shared 7-frame. Finite fact F8 shows that, with invertible mixing, this never closes both halves of one certified target.
- **Nick Petalas** (#2640, rank-`r` crossing capacity `2^(7−r)`) and **Arham Tahir** (#2675, #2682, coupled-history screen) showed that the marginal crossing inequalities admit 208 lifetimes. The argument here is not a crossing capacity: it uses 2×2 invertibility at shared 7-frames together with the cover structure of each target.
- **Different objects, not all-target lifetime floors in this model** (floors in other scopes are listed under Statement 1):
  - per-target minima: #2393 (commdata2338, merged as `research/p104-y0-source-acquisition`; Y0 alone needs exactly 48) and commdata2338's single-target minima 37–48 (#2658, which extends ywz65's #2496);
  - commdata2338's growth and error bounds for the combined relay word (#2654) and endpoint fusion (#2662);
  - the three-target shared collectors of Nick Petalas (#2548) and ywz65 (#2572).
- **On main, none of these bounds new-helper lifetimes in this model:**
  - `p104-minimum-shared-space` (Gareth Davidson): relaxed shared space of dimension 96, no chronology;
  - `p104-side-correction-rank-obstruction` (Gonzalo Mier, #2173): `I-G/2` has full rank, so any rank-one decomposition needs 104 summands;
  - `p104-cut-maxflow-audit` (Michael Yee): frozen original chronology, max-flow 8;
  - `p104-terminal-correction-floor` (Adam Gall): paid ranks after the channel completes (208, or 104 with free clean copies and disposal), a different object and cut;
  - `p104-tail-side-correction-seed749717` (Cinna Davis): promotes `Y_t` to FULL, outside this grammar, with zero new helpers.

## Reproduce

From the repository root (standard library, Python ≥ 3.12; about 2–3.5 minutes on a loaded 4-CPU machine, peak memory about 350 MB):

```sh
python3 -I -B research/p104-rank1-mixer-correction/verify.py
```

Expected final line:

```text
PASS_P104_RANK1_MIXER_TOP floor_full=219 floor_final_frame=234 floor_full_singular_mixing=216 pairs_passing_T_final_frame=288 pairs_passing_T_full=414 both_halves_T=0 demo_lifetimes=4974 controls=7 lemma_max_ST=48
```

The command runs these steps:
- It checks the input pins and the vendored checker's SHA-256.
- It recomputes the finite facts F1–F8 and F7′–F8′ of PROOF.md, the histograms behind the structural reading of F8, and all four floors (exact integer minimisation). It also computes the conditional floors of Open next question 3 and the fixed-template allowances 333 / 431 / 478 / 482 (merged `ceiling.py`).
- It regenerates the demonstration word in a private temporary directory. Its SHA-256 must be `cf8f444b01d839ec627f976f5ff56b345a295fcd3577037b82dde604a4acb40a`.
- It replays that word with the primary replayer, with the unchanged published checker, and with `independent.py`.
- It runs the seven negative controls. Each replayer must reject each control with the reason pinned in `EXPECTED.json`.
- It runs the side certificates, then compares every number with [EXPECTED.json](EXPECTED.json). Any expected key the run does not produce is a failure.

`independent.py` shares no code with `top_primary.py` or `verify.py`. `verify.py` requires the two to agree on every key in `SHARED_KEYS`. These keys cover the counts and histograms of F1–F8 and F7′–F8′ (including the 12 F8′ target IDs), all floors, the conditional floors and the word hash. The structural parts of F1–F6 (nesting, spans, set equalities) are asserted separately by each implementation, and either one fails on its own.

Zero counts get a nonzero companion, so that a check that always returns 0 cannot agree silently. Each implementation computes the companion with the same function or expression as the zero count, with the filter removed or shifted:
- F2: X-frame/target containments by dimension;
- F4: pairs of normals summing to a *shifted* normal `n_t + u*` (2,112);
- F5: the per-target histogram of uncovered sources;
- F8 and the broad F8 check: the same searches with the `T` filter removed (2,112 each);
- F8′ (final-frame class, 0): the same search in the full model (12).

The one zero count without a companion is the diagonal of `I − G/2`. It follows from every port having squared norm 8 in the fixture scaling (F1). `independent.py` uses:
- point-mask frames;
- annihilator (functional) descriptions of hyperplanes;
- a pivot-dictionary elimination;
- E8 inner products recomputed from root vectors;
- the normal identity `n_a + n_b = n_t + u*` instead of source partitions;
- a direct search and the closed form `⌈A/4⌉` for the floor minimum. Like the primary's search, these start from the inequalities of PROOF.md §4, so they recompute the minimum but do not check the derivation of the inequalities;
- subset enumeration for the geometry lemma.

Options:
- `--skip-lemma` omits the side-certificate enumerations.
- `--json NEW_FILE` writes the full receipt to a file that must not already exist.
- `--extra-word WORD.json` is optional and local, not registered. It replays a third-party word with the primary replayer and the published checker, then reports its class and the applicable floor (234 for the final-frame class, otherwise 219). For relay-v2 `WORD_ct12.json` (sha256 `10d47696ed9b42992f8518512c7007ce39774c66d95bfe6de3d964d419058a73`) it reports:
  - 1,031 lifetimes;
  - profile `{1:2427, 2:1094, 3:998, 4:96, 5:66, 6:157, 7:2}`;
  - rank mass 9,279;
  - final-frame class, applicable floor 234.

## Negative controls

Each mutation of the demonstration word must be rejected by all three replayers (primary, unchanged published checker, independent), each for the reason pinned in `EXPECTED.json`.

| Control | Mutation | Pinned rejection reason |
| --- | --- | --- |
| `perturbed_mixer_coefficient` | mixer shear coefficient `-1/2 → -1/3` | Y1 keeps a dirty residue (its compensation writes no longer match) |
| `dirty_residue` | one compensation write dropped | Y0 keeps a dirty residue |
| `illegal_frame_move` | carrier `P` moved `W → W'` instead of `W → K` | the move does not strictly enlarge the frame |
| `non_monotone_lifetime` | a `K → W'` move inserted after mixing | the move does not strictly enlarge the frame |
| `read_of_Y` | an operation outside the X-only grammar | unknown operation |
| `unequal_frame_shear` | `P` moved legally to a different 7-frame `K' ⊃ W`, then mixed with `R` at `K` | the shear joins unequal frames |
| `write_before_target_frame` | `P`'s write to Y0 moved to the cut just before Y0 reaches `H_0` | the write is outside Y0's frame at that cut |

All seven are rejected by all three replayers for the pinned reasons. `verify.py` also fails if a pin, the vendored checker, an input or any expected value drifts.

## Pins and sources

- Base commit: `d9b24831174325cad2e04e34da2068d7acb02938` (origin/main at about 23:00Z on 2026-10-15; all times are UTC). The package was first prepared on `bcdf338bf` and rebased cleanly onto `936fac15b` (about 21:35Z), then onto `d9b248311` after #2383, #2392 and #2393 were merged, so that these cited packages exist at the base.
  - Across the three commits, the only guidance change is six lines added to the bottleneck brief before `936fac15b` (the QQ16 observation-contract map and the bootstrap obligation map). The selected record, the task catalogue and every input below are byte-identical.
  - The other changes (PR ledger, review records, contributor credits, the package runner's process-group cleanup) do not affect this package. [SOURCES.json](SOURCES.json) records the details.
- Inputs:
  - `research/p104-native-channel/inputs/LOWRANK-WITNESS.json` (`0f541bef7f19fdeffd67157684e9f03d785f42c89973632f508fc1a0452b580e`);
  - `research/p104-native-channel/inputs/P104-FIXTURE.json` (`516c06f6ec3cb84be588c546108de897650288576dd5fbf5fe44b9c5546ad8a4`);
  - `research/complex-local-word-ceiling/ceiling.py` (`86a1432870b3b21d8454106ec9162fddc0471472d9214c590a1420f2426cedfc`).
- Vendored, unchanged: `vendor/check_p104_relay_construction.py`, sha256 `b808e70129fc2c01fbead974c770e0a39245f3a3968c53bcd1f49fb1972e865d`, git blob `d8a249db16ead8bfb8b47336ab5ce3a8133e1783`. Origin: `philippeVV/integer-mult-bounds@fac9e821d31bc199b49e8ed463074a50d1264311`, `research/p104-correction-screen/relay-construction/`, Apache-2.0. See [vendor/NOTICE.md](vendor/NOTICE.md).
- Predecessor heads and the cited main packages are pinned in [SOURCES.json](SOURCES.json).
- Overlap:
  - `scripts/find_overlap.py` for `p104-side-correction`, `complex-new-helper-inventory` and `complex-rank-shape-decoder`, at 18:20–18:44Z on 2026-10-15, with complete pagination: 770 / 758 open PRs and 1,337 / 1,349 discussion records;
  - targeted term searches and a P104 open-PR refresh at 19:50Z;
  - refreshes at about 21:30Z, 22:20Z and 23:00Z on 2026-10-15 of #2245 (no comment after 17:07Z), the #1163 claims, and PRs created since 19:00Z mentioning P104, lifetimes, relays, `I-G/2` or mixers. The newest P104 PRs (#2772, a physical-dual precision grid; #2784, decoder floors; #2813, exact precision for the ADD-retimed P104 dual) concern different objects, and #2720 (Nick Petalas) is a T74 correction floor, a different family.
  - No match is not proof of novelty.

## Scope, inherited assumptions and unresolved obligations

- **Model.** The floors are stated for G and G′ on the frozen PR #1972 / #1991 paths. Any change to the frozen chronology or the channel paths needs a new census. So does any operation outside G′, such as descents, cross-frame additions, or reads of `Y`, of the root code or of original helpers. The 208 floor is known to survive the last two kinds of read (#2383, #2467); whether 219 / 234 survive them is open (Open next question 5).
- **What the floors count.** They count new helper lifetimes only. They are lower bounds; no word with 216, 219 or 234 lifetimes is constructed or claimed to exist.
- **Permissive targets and loose charging.** The 20 targets whose last intermediate frame holds 3 or 12 sources are treated permissively in the full model, and so is absorption by non-tight targets. The counting also lets one junk lifetime witness two halves even at a half that lies in no other target hyperplane. The floors are therefore safe but loose; Open next question 6 records a sharper count that is not adopted here.
- **Side certificates.** The geometry lemma is a finite exhaustive certificate, not a written proof. The floors use neither it nor the inventory.
- **Inherited and unverified here:** the window-bill hosting facts (author-checked by Philippe Van Velzen in #2245), relay-v2's unproved estimate 387 and its 463 cap.
- **Not addressed.** This note does not address a construction in the window, hosting or owners, native recipes, dual orientation, precision, all-size admission, κ, or an exact optimum.
- **Unrun here.** The registered CPython 3.12 replay (only CPython 3.14.4 is installed locally; hosted CI runs 3.12). There is no human or proof-assistant review.
- **Local check, not registered.** A linear scan of `k = 0..600` for each of the four step shapes finds a single pass-to-fail transition at 333 / 482 / 478 / 431. This supports the bisection used for the allowances.

## Open next questions

1. **Can lower-level gathering be charged, giving a floor above 482 or locating a lossless lower structure?**
   - *Why it matters:* this is the only remaining way to reject the X-only correction route, or to find a design in the window. We expect (heuristically, PROOF.md §5) that top-level reasoning alone cannot exceed 416.
   - *First step:* extend Lemma 4 to 6-frames `M ⊂ K`. The `+` and `−` gathering frames of a perfect half must be formed from lifetimes whose other outputs serve other halves. Then pose the resulting per-level excess counting as an exact integer program over the 7- and 6-levels.
   - *Blocked by:* the case explosion at 6-frames, which lie in up to 7 seven-frames and up to 4 target hyperplanes. A written proof will need a structured relaxation, not an enumeration.
2. **Do the 20 permissive targets really escape?**
   - *Why it matters:* treating them exactly could lift the full-model floor from 219 toward 234.
   - *First step:* run Lemmas 3–4 with the actual non-complementary covers of the 12 targets with `|S_I| = 12` and the 8 with `|S_I| = 3`. The broader F8 check already finds no target, permissive or not, with two `T`-partners whose halves cover `R_t`; what is missing is a proof that `T` is necessary for them.
   - *Blocked by:* their covers have exclusive parts spanning only 5–6 dimensions, so entry frames can lie below dimension 7.
3. **Can a non-tight target `a` absorb `b_a` imperfect halves, one per lifetime?**
   - *Why it matters:* all four floor minimisers use non-tight targets with `b_a = 3` that each absorb three halves. If each non-tight target could absorb at most `b_a − 1` halves, the same counting would give `L ≥ 243` in the final-frame class. `L ≥ 260` would need absorption excluded entirely. Both conditional values are recomputed by both implementations.
   - *First step:* enumerate the three-covers of `R_t` by hyperplanes of `H_t` and apply the Lemma 4 test with the induced partial constraints.
   - *Blocked by:* `C(255,3)` triples per target, which needs bitset pruning.
4. **Does the geometry lemma have a written proof?**
   - *Why it matters:* it would explain the 48 = 1×48 = 2×24 = 4×12 = 6×8 ceiling structurally, and might extend to higher dimensions.
   - *First step:* use E8 non-orthogonality of the ports (for `s ≠ t`, `q_s ∈ H_t ⟺ ⟨p_s, p_t⟩ ≠ 0`, finite fact F1; `q_t ∉ H_t`).
   - *Blocked by:* the 104 ports are not a full E8 orbit.
5. **Do the floors survive root-code and original-helper reads?**
   - *Why it matters:* #2383 (commdata2338) and #2467 (ywz65) show that the 208 floor survives free reads of the eight-dimensional root code and read-only reads of every original helper at its actual frame. If 219 / 234 also survive, they apply to those wider models.
   - *First step:* Lemmas 1–2 need no read at `H_t` or at a 7-frame inside it, and exact entry supports. Check whether any of the 72 original helper paths visits a 7-frame inside a target hyperplane (#2467 shows that none visits a target hyperplane itself). Then restate Lemmas 3(b) and 4 modulo the root code, using #2383's invariant that the source part at frame `V` lies in the root code plus `U(V)`.
   - *Blocked by:* Lemma 4's determinant argument uses exact entry supports. With free root-code reads, entry values are known only modulo the root code.
6. **Should the sharper private-half count be adopted?**
   - *Why it matters:* it would raise the proved floors to 250 (final-frame class, G and G′) and 234 (full model, G), using only finite facts already certified here. No decision would change (250 < 333).
   - *Status:* the argument is sketched in PROOF.md §4 ("Strength and limits"): a half that lies in no other target hyperplane can be served only by junk that serves no other half, and every perfect half has such a complement. It was proposed by an AI review pass in this loop's last review round and re-checked only in a scratch computation in this loop (a census of all complementary covers and an exact minimisation). It is not in the registered replay or in `independent.py`. The G′ full-model value was not computed, because there `T′` admits pairs with `|S(K)| = 24`.
   - *First step:* write the count as a lemma in PROOF.md §4 and add the refined minimisation to both implementations.
   - *Blocked by:* nothing known; it arrived after the last full verification round.

## Credit

- Philippe Van Velzen: the 208 number (correction screen), relay construction and relay-v2, the cell-tree and flag designs, the published checker, the window bill, the #2245 handoff, and the first report of the geometric facts credited in PROOF.md §2.
- Hiroki Kumazaki: #2353 (`p104-monotone-relay-floor-audit`).
- commdata2338: #2383, #2392, #2393, #2654, #2658, #2662 and #2633.
- Ross Richardson: #2445 and #2458.
- Nick Petalas: #2594, #2604, #2640, #2548 and #2741.
- ywz65: #2614, #2467, #2572, #2586 and #2496.
- Arham Tahir: #2675 and #2682.
- Jose Manuel (jmbarrancoml): the #2619 four-pair consumer screen that #2741 extends.
- Gareth Davidson: `p104-minimum-shared-space`. Michael Yee: `p104-cut-maxflow-audit`. Gonzalo Mier: #2173 (`p104-side-correction-rank-obstruction`). Adam Gall: `p104-terminal-correction-floor` and #1940. Cinna Davis: `p104-tail-side-correction-seed749717`.
- Rohan Arun: #1972. Chafik Boukhalfa: #1991. Josie Elliston: #1071. Ali Romman: #1125.
- Douglas Colkitt: `ceiling.py`.
- flyingviper: #2744 (concurrent context).

Author-checked only. The primary and second implementations were written separately in the same AI-assisted session. They were reviewed by AI review passes in the same loop, which are not human review. No proof assistant was used.

Prepared by thakrarsagar with substantial AI assistance from Claude (Anthropic, Claude Opus 5.5). Apache-2.0.
