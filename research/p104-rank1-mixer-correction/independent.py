#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Second, separately written checker for the P104 top-level mixing bound.

Shares no code with top_primary.py / verify.py.  Representation: frames are 512-bit point masks,
hyperplanes of H_t are functionals w modulo the target normal (annihilator / dual description),
source sets are Python sets, ranks use a pivot-dictionary elimination, the E8 Gram entries are
recomputed from the root vectors, complementary halves are detected through the normal identity
n_a + n_b = n_t + u* (the primary uses source-set partitions), the floor minimum is recomputed by a
direct search AND by the closed form ceil((n_cert - n_exempt - 2 n_perm) / 4) of PROOF.md section 4
(both from the same counting inequalities, so this checks the arithmetic, not the derivation), the
geometry lemma is checked by subset enumeration with incidence intersections (no frame enumeration),
and the demonstration word is replayed with point-mask frames.

Checks F1-F8 and F7'-F8' of PROOF.md section 2 (including the nonzero companion statistics and the |S(K)|
histograms behind the structural reading of F8), the floors, the conditional floors of Open next question 3,
and the lemma maxima and equality shapes.

Usage: python3 -I -B independent.py REPO_ROOT WORD.json [--skip-lemma] [--replay-only]"""
import hashlib
import json
import os
import sys
from fractions import Fraction
from itertools import combinations, product

root, word_path = sys.argv[1], sys.argv[2]
SKIP_LEMMA = '--skip-lemma' in sys.argv
REPLAY_ONLY = '--replay-only' in sys.argv          # replay WORD only (used for the negative controls)


def die(msg):
    raise SystemExit('FAIL(independent): ' + msg)


inp = os.path.join(root, 'research', 'p104-native-channel', 'inputs')
for name, digest in (('LOWRANK-WITNESS.json', '0f541bef7f19fdeffd67157684e9f03d785f42c89973632f508fc1a0452b580e'),
                     ('P104-FIXTURE.json', '516c06f6ec3cb84be588c546108de897650288576dd5fbf5fe44b9c5546ad8a4')):
    if hashlib.sha256(open(os.path.join(inp, name), 'rb').read()).hexdigest() != digest:
        die('input pin mismatch: ' + name)
wit = json.load(open(os.path.join(inp, 'LOWRANK-WITNESS.json')))
fix = json.load(open(os.path.join(inp, 'P104-FIXTURE.json')))['section4_explicit_P104']

# ---- E8 ports and the correction I - G/2, G = <p,p'>/4
cands = []
for i in range(8):
    for j in range(i + 1, 8):
        for sj in (2, -2):
            v = [0] * 8
            v[i], v[j] = 2, sj
            cands.append(tuple(v))
for signs in product((1, -1), repeat=7):
    if sum(1 for x in signs if x < 0) % 2 == 0:
        cands.append((1,) + signs)
gone = set(map(tuple, fix['F0'])) | set(map(tuple, fix['C']))
ports = sorted(set(cands) - gone)
N = len(ports)
if N != 104:
    die('the fixture does not leave 104 ports')


def corr(t, s):
    ip = sum(a * b for a, b in zip(ports[t], ports[s]))
    return (1 if t == s else 0) - Fraction(ip, 8)


CORR = [[corr(t, s) for s in range(N)] for t in range(N)]


# ---- frames as 512-bit point masks
def close(gens):
    pts = {0}
    for v in gens:
        if v not in pts:
            pts |= {p ^ v for p in pts}
    m = 0
    for p in pts:
        m |= 1 << p
    return m


def dimension(mask):
    return bin(mask).count('1').bit_length() - 1


live = {k: close(v) for k, v in wit['initial_frames'].items()}
hist = {k: [(0, live[k])] for k in live}
for idx, ev in enumerate(wit['program']):
    if ev[0] == 'transport':
        if live[ev[1]] != close(ev[2]):
            die('a transport does not start at the current frame')
        live[ev[1]] = close(ev[3])
        hist[ev[1]].append((idx + 1, live[ev[1]]))
    elif ev[0] == 'zero':                      # the channel's private register is created mid-program
        live['C'] = close(ev[2])
        hist['C'] = [(idx + 1, live['C'])]
NE = len(wit['program'])
qv = [wit['initial_frames']['X%d' % s][0] for s in range(N)]
Hm = [hist['Y%d' % t][-1][1] for t in range(N)]


def dot(a, b):
    return bin(a & b).count('1') % 2


def inside(small, big):
    return small & ~big == 0


res = {}
if not REPLAY_ONLY:
    # F1: row supports, diagonal, entry values
    sizes = {}
    for t in range(N):
        k = sum(1 for s in range(N) if CORR[t][s] != 0)
        sizes[str(k)] = sizes.get(str(k), 0) + 1
    res['row_support_size_hist'] = sizes
    res['diagonal_nonzero'] = sum(1 for t in range(N) if CORR[t][t] != 0)
    res['offdiag_values'] = sorted({str(CORR[t][s]) for t in range(N) for s in range(N) if CORR[t][s] != 0},
                                   key=Fraction)
    if sizes != {'48': N} or res['diagonal_nonzero'] or res['offdiag_values'] != ['-1/2', '1/2']:
        die('F1: rows of I-G/2 are not 48-sparse with zero diagonal and entries +-1/2')

normal = []
for t in range(N):
    ns = [v for v in range(1, 512) if all(not dot(v, p) for p in range(512) if Hm[t] >> p & 1)]
    if len(ns) != 1 or dimension(Hm[t]) != 8:
        die('H_%d is not a hyperplane with a unique normal' % t)
    normal.append(ns[0])
ustar = [u for u in range(1, 512) if all(dot(u, x) for x in qv)]
if len(ustar) != 1:
    die('the sources do not lie in exactly one affine hyperplane')
US = ustar[0]
SUPP = [{s for s in range(N) if CORR[t][s] != 0} for t in range(N)]
for t in range(N):
    if SUPP[t] != {s for s in range(N) if not dot(normal[t], qv[s])}:
        die('F1: supp C_%d differs from the sources whose line lies in H_%d' % (t, t))


def rank(vecs):
    piv = {}
    for v in vecs:
        while v:
            hb = v.bit_length() - 1
            if hb in piv:
                v ^= piv[hb]
            else:
                piv[hb] = v
                break
    return len(piv)


def strict_chain(masks):
    return all(inside(a, b) and a != b for a, b in zip(masks, masks[1:]))


# ---- F2: X paths; F3: Y paths and the last intermediate frame I_t
x_big = x_big_in = 0
contain = {}
for s in range(N):
    masks = [m for _, m in hist['X%d' % s]]
    if masks[0] != close([qv[s]]) or not strict_chain(masks):
        die('F2: the X%d path does not start at its line or is not strictly nested' % s)
    for m in masks:
        k = sum(1 for t in range(N) if inside(m, Hm[t]))
        contain[dimension(m)] = contain.get(dimension(m), 0) + k
        if dimension(m) >= 7:
            x_big += 1
            x_big_in += k
if x_big_in:
    die('F2: an X frame of dimension >= 7 lies inside a target hyperplane')
SI, y_inter_max = [], 0
for t in range(N):
    masks = [m for _, m in hist['Y%d' % t]]
    if masks[0] != 1 or not strict_chain(masks):
        die('F3: the Y%d path is not strictly nested from ZERO' % t)
    y_inter_max = max([y_inter_max] + [dimension(m) for m in masks[:-1]])
    SI.append({s for s in SUPP[t] if masks[-2] >> qv[s] & 1})
if y_inter_max > 6:
    die('F3: an intermediate target frame has dimension > 6')

# ---- F4: distinct odd normals, no normal is the sum of two others
nset = set(normal)
if US in nset:
    die('F4: u* is a target normal')


def pairs_summing_into(values):
    return sum(1 for a, b in combinations(normal, 2) if a ^ b in values)


triples = pairs_summing_into(nset)
shifted = pairs_summing_into({v ^ US for v in normal})        # same-path nonzero companion (complementary triples)
if len(nset) != N or any(bin(v).count('1') % 2 == 0 for v in normal) or triples:
    die('F4: target normals are not distinct, odd and sum-free')
if not REPLAY_ONLY:
    sih = {}
    for t in range(N):
        sih[str(len(SI[t]))] = sih.get(str(len(SI[t])), 0) + 1
    wts = {}
    for v in normal:
        wts[bin(v).count('1')] = wts.get(bin(v).count('1'), 0) + 1
    res.update(x_frames_dim_ge7=x_big, x_frames_dim_ge7_inside_target_hyperplane=x_big_in,
               x_frame_target_containments_by_dim={str(d): contain[d] for d in sorted(contain)},
               y_intermediate_max_dim=y_inter_max, distinct_odd_normals=len(nset),
               normal_weight_hist={str(k): wts[k] for k in sorted(wts)}, normal_sum_triples=triples,
               normal_shifted_sum_triples=shifted, ustar=US, SI_sizes_histogram={k: sih[k] for k in sorted(sih, key=int)})


def hyper_functionals(t):
    """hyperplanes of H_t as canonical functionals w (w ~ w ^ normal[t]), excluding the normal itself"""
    seen = set()
    for w in range(1, 512):
        if w == normal[t]:
            continue
        seen.add(min(w, w ^ normal[t]))
    return sorted(seen)


def analyse(R):
    """F5 and per-target 2-covers of R[t] (dual description) -> (good flags, cover counts, F5 violations,
    histogram of the fewest sources of R[t] left uncovered by one hyperplane)"""
    goodf, counts, f5, low = [], [], 0, {}
    for t in range(N):
        fs = hyper_functionals(t)
        if len(fs) != 255:
            die('H_%d does not have 255 hyperplanes' % t)
        sk = {w: {s for s in SUPP[t] if not dot(w, qv[s])} for w in fs}
        least = min(len(R[t] - sk[w]) for w in fs)
        f5 += least == 0
        low[least] = low.get(least, 0) + 1
        ok, cnt, comp = True, 0, 0
        for w1, w2 in combinations(fs, 2):
            A, B = sk[w1], sk[w2]
            if R[t] <= (A | B):
                cnt += 1
                is_comp = (w1 ^ w2) in (US, US ^ normal[t])
                if is_comp != ((A | B) == SUPP[t] and not (A & B)):
                    die('dual complementarity disagrees with the source partition')
                comp += is_comp
                e1, e2 = R[t] & (A - B), R[t] & (B - A)
                if not (is_comp and rank([qv[s] for s in e1]) == 7 and rank([qv[s] for s in e2]) == 7):
                    ok = False
        goodf.append(ok)
        counts.append((cnt, comp))
    return goodf, counts, f5, {str(k): low[k] for k in sorted(low)}


def cover_hist(counts):
    h = {}
    for c in counts:
        h[c] = h.get(c, 0) + 1
    return sorted([c[0], c[1], k] for c, k in h.items())


def classes(t, a):
    K = SUPP[t] & SUPP[a]
    return K, [s for s in K if CORR[a][s] == CORR[t][s]], [s for s in K if CORR[a][s] == -CORR[t][s]]


def pair_test_T(R, t, a, singular=False):
    """Lemma 4 test T(t, a); with singular=True, Lemma 4' (T, or the doubly constrained set is one ratio class)"""
    K = SUPP[t] & SUPP[a]
    both = sorted(K & R[t] & R[a])
    single = sorted(K & (R[t] ^ R[a]))
    same = [s for s in both if CORR[a][s] == CORR[t][s]]
    flip = [s for s in both if CORR[a][s] == -CORR[t][s]]
    if len(same) + len(flip) != len(both):
        die('a ratio on a shared 7-frame is not +-1')
    if singular and (not same or not flip):
        return True
    for choice in range(2 ** len(single)):
        side1 = [single[i] for i in range(len(single)) if (choice >> i) % 2]
        side2 = [single[i] for i in range(len(single)) if not (choice >> i) % 2]
        for X, Y in ((same, flip), (flip, same)):
            if rank([qv[s] for s in X + side1]) <= 6 and rank([qv[s] for s in Y + side2]) <= 6:
                return True
    return False


def ll(D, t, a):
    return D[(min(t, a), max(t, a))]


def perfect_hits(D, pool):
    """(t, a, b) with a < b both partners of t in pool and complementary halves (normal identity).  Used with the
    T relation (F8), the T' relation (F8') and the unfiltered relation (companion: all complementary triples)."""
    hits = []
    for t in pool:
        partners = [a for a in pool if a != t and ll(D, t, a)]
        for a, b in combinations(partners, 2):
            if normal[a] ^ normal[b] == normal[t] ^ US:
                hits.append((t, a, b))
    return hits


def any_cover(D, R):
    """(t, a, b) over all targets with a < b partners of t under D whose halves cover R[t], complementary or not"""
    hits = 0
    for t in range(N):
        partners = [a for a in range(N) if a != t and ll(D, t, a)]
        for a, b in combinations(partners, 2):
            if R[t] <= ((SUPP[t] & SUPP[a]) | (SUPP[t] & SUPP[b])):
                hits += 1
    return hits


def size_hist(D, pool):
    """histogram of |S(H_t ∩ H_a)| over pairs t < a in pool related by D"""
    h = {}
    for (t, a), v in D.items():
        if v and t in pool and a in pool:
            k = len(SUPP[t] & SUPP[a])
            h[k] = h.get(k, 0) + 1
    return {str(k): h[k] for k in sorted(h)}


def minimise(n_cert, n_perm, n_exempt=0, absorb='X+2m'):
    """direct search: E = X + J with J >= h_gamma/2 and the absorption limits of PROOF.md section 4"""
    best = 10 ** 9
    for nontight_cert in range(n_cert + 1):
        for nontight_perm in range(n_perm + 1):
            m = nontight_cert + nontight_perm
            for X in range(m, m + 400):
                tight_unexempt = max(0, n_cert - nontight_cert - n_exempt)
                absorbable = {'X+2m': X + 2 * m, 'X+m': X + m, 'none': 0}[absorb] + 2 * (n_perm - nontight_perm)
                gamma = max(0, tight_unexempt - absorbable)
                best = min(best, X + (gamma + 1) // 2)
    return best


def closed_form(n_cert, n_perm, n_exempt=0):
    """PROOF.md section 4: min E = ceil(A/4), A = n_cert - n_exempt - 2 n_perm (A >= 0)"""
    A = n_cert - n_exempt - 2 * n_perm
    return max(0, -(-A // 4))


if not REPLAY_ONLY:
    Rres = [set(SUPP[t]) for t in range(N)]
    Rful = [SUPP[t] - SI[t] for t in range(N)]
    good_res, cnt_res, f5_res, low_res = analyse(Rres)
    good_ful, cnt_ful, f5_ful, low_ful = analyse(Rful)
    if not all(good_res) or any(c != (127, 127) for c in cnt_res):
        die('F6: final-frame covers are not 127 complementary spanning two-covers per target')
    GOOD = [t for t in range(N) if good_ful[t]]
    if GOOD != [t for t in range(N) if len(SI[t]) in (0, 1, 2, 4)]:
        die("F6': good targets are not those with |S_I| in {0,1,2,4}")
    res.update(single_cover_violations=f5_res + f5_ful,
               min_uncovered_by_one_hyperplane=dict(final_frame=low_res, full=low_ful),
               final_frame_cover_hist=cover_hist(cnt_res),
               full_cover_hist=cover_hist(cnt_ful), good_targets=len(GOOD))
    pairs = [(t, a) for t in range(N) for a in range(N) if t < a]
    LLr = {p: pair_test_T(Rres, *p) for p in pairs}
    LLf = {p: pair_test_T(Rful, *p) for p in pairs}
    SGr = {p: pair_test_T(Rres, *p, singular=True) for p in pairs}
    SGf = {p: pair_test_T(Rful, *p, singular=True) for p in pairs}
    shp = {}
    for (t, a), v in LLr.items():
        if v:
            K, same, flip = classes(t, a)
            key = (len(K), len(same), len(flip), rank([qv[s] for s in same]), rank([qv[s] for s in flip]))
            shp[key] = shp.get(key, 0) + 1
    ALLD = {p: True for p in pairs}
    comp_all = perfect_hits(ALLD, range(N))
    if len(comp_all) != shifted:
        die('complementary triples differ from the shifted normal-sum count')
    halves = {}
    for t, a, b in comp_all:
        k = (len(SUPP[t] & SUPP[a]), len(SUPP[t] & SUPP[b]))
        halves[k] = halves.get(k, 0) + 1
    sing_r = {h[0] for h in perfect_hits(SGr, range(N))}
    sing_f = {h[0] for h in perfect_hits(SGf, GOOD)}
    everyone, goodset = set(range(N)), set(GOOD)
    res.update(
        pairs_passing_T_final_frame=sum(LLr.values()),
        pairs_passing_T_full=sum(LLf.values()),
        pairs_passing_T_full_good_good=sum(1 for (t, a), v in LLf.items() if v and t in GOOD and a in GOOD),
        pairs_passing_T_shapes_final_frame=sorted(list(k) + [v] for k, v in shp.items()),
        both_halves_T_final_frame=len(perfect_hits(LLr, range(N))),
        both_halves_T_full_good=len(perfect_hits(LLf, GOOD)),
        both_halves_T_any_targets_any_cover_full=any_cover(LLf, Rful),
        any_cover_triples_unfiltered_full=any_cover(ALLD, Rful),
        complementary_target_triples=len(comp_all),
        complementary_halves_SK_sizes=sorted(list(k) + [v] for k, v in halves.items()),
        pairs_passing_Tprime_final_frame=sum(SGr.values()),
        pairs_passing_Tprime_full=sum(SGf.values()),
        both_halves_Tprime_final_frame_targets=len(sing_r),
        both_halves_Tprime_full_good_targets=len(sing_f),
        both_halves_Tprime_full_good_target_ids=sorted(sing_f),
        pair_SK_size_hist=size_hist(ALLD, everyone),
        pairs_passing_T_SK_size_hist=dict(final_frame=size_hist(LLr, everyone), full=size_hist(LLf, everyone),
                                          full_good_good=size_hist(LLf, goodset)),
        pairs_passing_Tprime_SK_size_hist=dict(final_frame=size_hist(SGr, everyone), full=size_hist(SGf, everyone),
                                               full_good_good=size_hist(SGf, goodset)),
    )
    if res['both_halves_T_final_frame'] or res['both_halves_T_full_good']:
        die('F8: some certified target has two complementary halves passing T')
    n_good, n_perm = len(GOOD), N - len(GOOD)
    floors = dict(floor_final_frame=(N, 0, 0), floor_full=(n_good, n_perm, 0),
                  floor_final_frame_singular_mixing=(N, 0, len(sing_r)),
                  floor_full_singular_mixing=(n_good, n_perm, len(sing_f)))
    for key, (nc, npm, ne) in floors.items():
        e = minimise(nc, npm, ne)
        if e != closed_form(nc, npm, ne):
            die('direct search and closed form disagree for ' + key)
        res[key] = 2 * N + e
    res['conditional_floor_final_frame'] = {'absorb_at_most_b_minus_1': 2 * N + minimise(N, 0, absorb='X+m'),
                                            'no_absorption': 2 * N + minimise(N, 0, absorb='none')}

# ---- replay of a word with point-mask frames
raw = open(word_path, 'rb').read()
res['demo_word_sha256'] = hashlib.sha256(raw).hexdigest()
word = json.loads(raw)
ops = word['ops']
if ops[0][0] != 'move_zero_all':
    die('the word does not start with move_zero_all')
L = ops[0][1]
fr = [1] * L
val = [{-1 - k: Fraction(1)} for k in range(L)]      # dirt keys negative, sources non-negative
outY = [dict() for _ in range(N)]
prof = {}
clock = 0


def frame_at(key, cut):
    m = None
    for c, f in hist[key]:
        if c <= cut:
            m = f
    return m


def acc(d, c, src):
    for k, v in src.items():
        d[k] = d.get(k, 0) + c * v
        if d[k] == 0:
            del d[k]


for op in ops[1:]:
    if op[0] == 'move':
        new = close(op[2])
        if fr[op[1]] & ~new or new == fr[op[1]]:
            die('move of lifetime %d does not strictly enlarge its frame' % op[1])
        r = dimension(new) - dimension(fr[op[1]])
        prof[r] = prof.get(r, 0) + 1
        fr[op[1]] = new
    elif op[0] == 'read':
        if op[4] < clock:
            die('read at cut %d precedes cut %d' % (op[4], clock))
        if fr[op[1]] != frame_at('X%d' % op[2], op[4]):
            die('read of X%d outside its retained frame at cut %d' % (op[2], op[4]))
        clock = op[4]
        acc(val[op[1]], Fraction(op[3]), {op[2]: Fraction(1)})
    elif op[0] == 'shear':
        if op[1] == op[2] or fr[op[1]] != fr[op[2]]:
            die('shear of lifetime %d by %d across unequal frames (or onto itself)' % (op[1], op[2]))
        acc(val[op[1]], Fraction(op[3]), dict(val[op[2]]))
    elif op[0] == 'write':
        if op[4] < clock:
            die('write at cut %d precedes cut %d' % (op[4], clock))
        if fr[op[2]] != frame_at('Y%d' % op[1], op[4]):
            die('write to Y%d outside its frame at cut %d' % (op[1], op[4]))
        clock = op[4]
        acc(outY[op[1]], Fraction(op[3]), val[op[2]])
    else:
        die('operation %r is outside the X-only grammar' % (op[0],))
fullmask = (1 << 512) - 1
for t in range(N):
    if any(k < 0 for k in outY[t]):
        die('target %d keeps a dirty residue' % t)
    if outY[t] != {s: CORR[t][s] for s in range(N) if CORR[t][s] != 0}:
        die('target %d is not row %d of I-G/2' % (t, t))
if any(f != fullmask for f in fr):
    die('a lifetime does not end at FULL')
if any(val[k] != {-1 - k: 1} for k in range(L)):
    die('a dirty lifetime is not restored')
res['demo_lifetimes'] = L
res['demo_profile'] = {str(r): prof[r] for r in sorted(prof)}
if REPLAY_ONLY:
    print(json.dumps(res, sort_keys=True))
    print('PASS_P104_INDEPENDENT_REPLAY lifetimes=%d' % L)
    raise SystemExit(0)

# ---- geometry lemma by subset enumeration (no frame enumeration): maxima and the (|S|,|T|) shapes attaining them
if not SKIP_LEMMA:
    Tset = [0] * N
    for s in range(N):
        for t in range(N):
            if CORR[t][s] != 0:
                Tset[s] |= 1 << t
    srcpos = {qv[s]: s for s in range(N)}
    best = {1: 0, 2: 0, 3: 0, 4: 0}
    eq = {1: set(), 2: set(), 3: set(), 4: set()}

    def note(d, ns, nt):
        if ns * nt > best[d]:
            best[d] = ns * nt
            eq[d] = set()
        if ns * nt == best[d]:
            eq[d].add((ns, nt))
    for s in range(N):
        note(1, 1, bin(Tset[s]).count('1'))
    for a, b in combinations(range(N), 2):
        pts = [0, qv[a], qv[b], qv[a] ^ qv[b]]
        note(2, sum(1 for p in pts if p in srcpos), bin(Tset[a] & Tset[b]).count('1'))
    for a, b, c in combinations(range(N), 3):
        base = [0, qv[a], qv[b], qv[a] ^ qv[b]]
        if qv[c] in base:
            continue
        span3 = base + [p ^ qv[c] for p in base]
        T3 = Tset[a] & Tset[b] & Tset[c]
        n3 = sum(1 for p in span3 if p in srcpos)
        note(3, n3, bin(T3).count('1'))
        if T3 == 0:
            continue
        for d in range(c + 1, N):
            if qv[d] in span3:
                continue
            T4 = T3 & Tset[d]
            if not T4:
                continue
            note(4, n3 + sum(1 for p in span3 if p ^ qv[d] in srcpos), bin(T4).count('1'))
    res['lemma'] = {str(k): v for k, v in best.items()}
    res['lemma_equality_shapes'] = {str(k): sorted(list(x) for x in v) for k, v in eq.items()}
    if any(v != 48 for v in best.values()):
        die('geometry lemma maximum is not 48 in every dimension')
print(json.dumps(res, sort_keys=True))
print('PASS_P104_RANK1_MIXER_INDEPENDENT floor_full=%d floor_final_frame=%d floor_full_singular_mixing=%d '
      'pairs_passing_T_final_frame=%d pairs_passing_T_full=%d good=%d demo_lifetimes=%d%s' % (
          res['floor_full'], res['floor_final_frame'], res['floor_full_singular_mixing'],
          res['pairs_passing_T_final_frame'], res['pairs_passing_T_full'], res['good_targets'], L,
          '' if SKIP_LEMMA else ' lemma_max=%d' % max(res['lemma'].values())))
