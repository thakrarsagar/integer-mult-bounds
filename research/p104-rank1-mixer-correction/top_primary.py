# SPDX-License-Identifier: Apache-2.0
"""Primary implementation: P104 geometry, the top-level (7/8-dimension) 2x2 mixing test and the
lifetime floors of PROOF.md.  Standard library only, exact arithmetic.

Representation: a subspace of F2^9 is a canonical reduced-echelon basis (tuple of ints); sets of
sources are 104-bit integers.  The second implementation (independent.py) uses annihilators and
incidence bitsets instead and shares no code with this module.
"""
import hashlib
import json
import os
from fractions import Fraction as Q
from itertools import combinations, product

PINS = {
    'research/p104-native-channel/inputs/LOWRANK-WITNESS.json':
        '0f541bef7f19fdeffd67157684e9f03d785f42c89973632f508fc1a0452b580e',
    'research/p104-native-channel/inputs/P104-FIXTURE.json':
        '516c06f6ec3cb84be588c546108de897650288576dd5fbf5fe44b9c5546ad8a4',
    'research/complex-local-word-ceiling/ceiling.py':
        '86a1432870b3b21d8454106ec9162fddc0471472d9214c590a1420f2426cedfc',
}
FULL_BASIS = tuple(1 << i for i in range(8, -1, -1))


def need(ok, why):
    if not ok:
        raise SystemExit('FAIL: ' + why)


# ----------------------------------------------------------------- F2 linear algebra (echelon form)
def rref(vectors):
    """Canonical reduced echelon basis of span(vectors), pivots = leading bits, sorted descending."""
    rows = []
    for v in vectors:
        for r in rows:
            if v >> (r.bit_length() - 1) & 1:
                v ^= r
        if v:
            lead = v.bit_length() - 1
            rows = [r ^ v if r >> lead & 1 else r for r in rows]
            rows.append(v)
    return tuple(sorted(rows, reverse=True))


def member(basis, v):
    for r in basis:
        if v >> (r.bit_length() - 1) & 1:
            v ^= r
    return v == 0


def contained(a, b):
    return all(member(b, v) for v in a)


def parity(a, b):
    return bin(a & b).count('1') & 1


def rank_of(vectors):
    return len(rref(vectors))


# ----------------------------------------------------------------- pinned inputs
def load(root):
    for rel, digest in PINS.items():
        with open(os.path.join(root, rel), 'rb') as fh:
            need(hashlib.sha256(fh.read()).hexdigest() == digest, 'input pin mismatch: ' + rel)
    pkg = os.path.join(root, 'research', 'p104-native-channel', 'inputs')
    with open(os.path.join(pkg, 'LOWRANK-WITNESS.json')) as fh:
        wit = json.load(fh)
    with open(os.path.join(pkg, 'P104-FIXTURE.json')) as fh:
        fx = json.load(fh)['section4_explicit_P104']
    roots = set()
    for i, j in combinations(range(8), 2):
        for sg in (-1, 1):
            v = [0] * 8
            v[i] = 2
            v[j] = 2 * sg
            roots.add(tuple(v))
    for sg in product((-1, 1), repeat=7):
        if sg.count(-1) % 2 == 0:
            roots.add((1, *sg))
    removed = {tuple(r) for r in fx['F0'] + fx['C']}
    ports = [r for r in sorted(roots) if r not in removed]
    n = len(ports)
    need(n == 104, 'the fixture does not leave exactly 104 ports')
    gram = [[sum(x * y for x, y in zip(a, b)) // 4 for b in ports] for a in ports]
    corr = [[(Q(1) if t == s else Q(0)) - Q(gram[t][s], 2) for s in range(n)] for t in range(n)]
    cur = {r: rref(f) for r, f in wit['initial_frames'].items()}
    path = {r: [(0, cur[r])] for r in cur}
    for i, e in enumerate(wit['program']):
        if e[0] == 'transport':
            need(cur[e[1]] == rref(e[2]), 'a transport does not start at the current frame')
            cur[e[1]] = rref(e[3])
            path[e[1]].append((i + 1, cur[e[1]]))
        elif e[0] == 'zero':
            cur['C'] = rref(e[2])
            path['C'] = [(i + 1, cur['C'])]
    q = [wit['initial_frames']['X%d' % s][0] for s in range(n)]
    return dict(n=n, C=corr, q=q, NE=len(wit['program']),
                X=[path['X%d' % s] for s in range(n)], Y=[path['Y%d' % t] for t in range(n)])


def bits(it):
    m = 0
    for i in it:
        m |= 1 << i
    return m


def members(mask):
    out = []
    while mask:
        low = mask & -mask
        out.append(low.bit_length() - 1)
        mask ^= low
    return out


# ----------------------------------------------------------------- finite facts (PROOF.md section 2)
def facts(g):
    """Check F1-F4 and return the frames plus a report of every counted fact (compared with independent.py)."""
    n, q, C = g['n'], g['q'], g['C']
    H = [g['Y'][t][-1][1] for t in range(n)]
    need(all(len(h) == 8 for h in H), 'a final target frame is not a hyperplane')
    # F1: support, diagonal and entries of I - G/2
    supp = [bits(s for s in range(n) if C[t][s]) for t in range(n)]
    diag_nonzero = sum(1 for t in range(n) if C[t][t] != 0)
    need(diag_nonzero == 0, 'I-G/2 has a nonzero diagonal entry')
    sizes = [bin(m).count('1') for m in supp]
    need(all(z == 48 for z in sizes), 'a row of I-G/2 does not have exactly 48 nonzeros')
    offdiag = sorted({str(C[t][s]) for t in range(n) for s in range(n) if C[t][s]}, key=Q)
    need(offdiag == ['-1/2', '1/2'], 'a nonzero entry of I-G/2 is not +-1/2')
    need(all(supp[t] == bits(s for s in range(n) if member(H[t], q[s])) for t in range(n)),
         'supp C_t differs from the set of sources whose line lies in H_t')
    # F2: X paths start at the source line, are strictly nested, and no X frame of dim >= 7 lies in a target hyperplane
    x_big = x_big_inside = 0
    contain = {}
    for s in range(n):
        p = g['X'][s]
        need(p[0][1] == rref([q[s]]), 'the X%d path does not start at its source line' % s)
        need(all(contained(a[1], b[1]) and len(a[1]) < len(b[1]) for a, b in zip(p, p[1:])),
             'the X%d path is not strictly nested' % s)
        for _, f in p:
            k = sum(1 for t in range(n) if contained(f, H[t]))
            contain[len(f)] = contain.get(len(f), 0) + k
            if len(f) >= 7:
                x_big += 1
                x_big_inside += k
    need(x_big_inside == 0, 'an X frame of dimension >= 7 lies inside a target hyperplane')
    # F3: Y paths strictly nested from ZERO, intermediate frames of dim <= 6, then H_t
    SI, y_inter_max = [], 0
    for t in range(n):
        p = g['Y'][t]
        need(p[0][1] == () and all(contained(a[1], b[1]) and len(a[1]) < len(b[1]) for a, b in zip(p, p[1:])),
             'the Y%d path is not strictly nested from ZERO' % t)
        y_inter_max = max([y_inter_max] + [len(f) for _, f in p[:-1]])
        top = p[-2][1]
        SI.append(bits(s for s in range(n) if member(top, q[s])))
    need(y_inter_max <= 6, 'an intermediate target frame has dimension > 6')
    # F4: distinct odd normals, sum-free (a 7-frame lies in at most two target hyperplanes), affine sources
    normals = []
    for t in range(n):
        cand = [v for v in range(1, 512) if all(not parity(v, h) for h in H[t])]
        need(len(cand) == 1, 'H_%d has no unique normal' % t)
        normals.append(cand[0])
    need(len(set(normals)) == n, 'two target hyperplanes coincide')
    need(all(bin(v).count('1') % 2 == 1 for v in normals), 'a target normal has even weight')
    ustar = [u for u in range(1, 512) if all(parity(u, x) for x in q)]
    need(len(ustar) == 1, 'the sources do not lie in exactly one affine hyperplane')
    nset = set(normals)
    need(ustar[0] not in nset, 'u* is a target normal')

    def pair_sums_in(values):
        return sum(1 for a, b in combinations(normals, 2) if a ^ b in values)
    sum_triples = pair_sums_in(nset)
    # same-path nonzero companion: pairs {a, b} with n_a + n_b = n_t + u* for some t (u* is not a normal, so t is
    # neither a nor b); these are the complementary target triples, counted again by source partitions in verify.py
    shifted_triples = pair_sums_in({v ^ ustar[0] for v in normals})
    need(sum_triples == 0, 'a target normal is the sum of two others (a 7-frame lies in three target hyperplanes)')
    weights = [bin(v).count('1') for v in normals]
    report = dict(row_support_size_hist={str(z): sizes.count(z) for z in sorted(set(sizes))},
                  diagonal_nonzero=diag_nonzero, offdiag_values=offdiag,
                  x_frames_dim_ge7=x_big, x_frames_dim_ge7_inside_target_hyperplane=x_big_inside,
                  x_frame_target_containments_by_dim={str(d): contain[d] for d in sorted(contain)},
                  y_intermediate_max_dim=y_inter_max, distinct_odd_normals=len(nset),
                  normal_weight_hist={str(w): weights.count(w) for w in sorted(set(weights))},
                  normal_sum_triples=sum_triples, normal_shifted_sum_triples=shifted_triples, ustar=ustar[0])
    return dict(H=H, supp=supp, SI=SI, normals=normals, ustar=ustar[0], report=report)


def hyperplanes_of(Ht):
    """All 255 hyperplanes of the 8-dim subspace Ht, as canonical bases."""
    out = set()
    for w in range(1, 512):
        elems = [x for x in span_elems(Ht) if not parity(w, x)]
        if len(elems) == 128:
            out.add(rref(elems))
    return sorted(out)


def span_elems(basis):
    s = [0]
    for b in basis:
        s += [x ^ b for x in s]
    return s


def covers(g, F, R):
    """For each target t, all 2-covers {K1,K2} of the source set R[t] by hyperplanes of H_t.
    Returns per target: list of (K1, K2, S1, S2, complementary, exclusive-span dims)."""
    n, q = g['n'], g['q']
    out = []
    for t in range(n):
        hs = hyperplanes_of(F['H'][t])
        need(len(hs) == 255, 'H_%d does not have exactly 255 hyperplanes' % t)
        sk = [bits(s for s in members(F['supp'][t]) if member(K, q[s])) for K in hs]
        rows = []
        for i in range(255):
            for j in range(i + 1, 255):
                if (sk[i] | sk[j]) & R[t] == R[t]:
                    e1 = R[t] & sk[i] & ~sk[j]
                    e2 = R[t] & sk[j] & ~sk[i]
                    comp = (sk[i] | sk[j]) == F['supp'][t] and not (sk[i] & sk[j])
                    d1 = rank_of([q[s] for s in members(e1)])
                    d2 = rank_of([q[s] for s in members(e2)])
                    rows.append((hs[i], hs[j], sk[i], sk[j], comp, d1, d2))
        out.append(rows)
    return out


def single_cover_stats(g, F, R):
    """F5: number of targets t for which some hyperplane K of H_t has R[t] ⊆ S(K) (must be 0), and the histogram
    of min over K of |R[t] minus S(K)| (a nonzero companion statistic)."""
    n, q = g['n'], g['q']
    bad, hist = 0, {}
    for t in range(n):
        low = None
        for K in hyperplanes_of(F['H'][t]):
            sk = bits(s for s in members(F['supp'][t]) if member(K, q[s]))
            u = bin(R[t] & ~sk).count('1')
            low = u if low is None else min(low, u)
        bad += low == 0
        hist[str(low)] = hist.get(str(low), 0) + 1
    return bad, {k: hist[k] for k in sorted(hist, key=int)}


def pair_test(g, R, t, a, supp, singular=False):
    """The pair test T(t, a): a necessary condition (PROOF.md Lemma 4), not a construction, for two lifetimes at
    K = H_t ∩ H_a to leave K carrying t's and a's half values: a partition F1 ⊔ F2 of the singly-constrained sources such that
    span(B_x ∪ F1) and span(B_y ∪ F2) are proper subspaces of K for the two ratio classes B_x, B_y.
    With singular=True this is Lemma 4' (in-frame mixing may be singular): the test above, or B is a
    single ratio class (possibly empty)."""
    C, q = g['C'], g['q']
    SK = supp[t] & supp[a]
    B = members(SK & R[t] & R[a])
    Fr = members(SK & (R[t] ^ R[a]))
    Bp = [s for s in B if C[a][s] == C[t][s]]
    Bm = [s for s in B if C[a][s] == -C[t][s]]
    need(len(Bp) + len(Bm) == len(B), 'a ratio C[a][s]/C[t][s] on K is not +-1')
    if singular and (not Bp or not Bm):
        return True
    for mask in range(1 << len(Fr)):
        F1 = [Fr[i] for i in range(len(Fr)) if mask >> i & 1]
        F2 = [Fr[i] for i in range(len(Fr)) if not mask >> i & 1]
        for X, Y in ((Bp, Bm), (Bm, Bp)):
            if rank_of([q[s] for s in X + F1]) < 7 and rank_of([q[s] for s in Y + F2]) < 7:
                return True
    return False


def complementary_perfect(g, F, good, LL):
    """Triples (t, a, b): t in `good` with two partners a < b in `good`, LL[t][a] and LL[t][b], whose 7-frames
    H_t ∩ H_a and H_t ∩ H_b are complementary halves (disjoint source sets with union supp(t)).  Called with the
    T relation (F8, must give none), the T' relation (F8') and the unfiltered relation a != t (the nonzero
    companion: all complementary target triples)."""
    supp = F['supp']
    hits = []
    for t in good:
        part = [a for a in good if a != t and LL[t][a]]
        for a, b in combinations(part, 2):
            ha, hb = supp[t] & supp[a], supp[t] & supp[b]
            if ha | hb == supp[t] and not ha & hb:
                hits.append((t, a, b))
    return hits


def any_cover_hits(g, F, R, LL):
    """Broader finite check: triples (t, a, b) over ALL targets with LL[t][a], LL[t][b] (a < b) whose halves
    H_t ∩ H_a and H_t ∩ H_b cover R[t] (complementary or not).  Lemma 4 is proved only for certified pairs, so
    this is a fact about the test, not a theorem about words with permissive targets.  Called with the
    unfiltered relation a != t it gives the nonzero companion (all pair-half two-covers of R[t])."""
    n, supp = g['n'], F['supp']
    hits = 0
    for t in range(n):
        part = [a for a in range(n) if a != t and LL[t][a]]
        for a, b in combinations(part, 2):
            if R[t] & ~((supp[t] & supp[a]) | (supp[t] & supp[b])) == 0:
                hits += 1
    return hits


def floor_excess(n_good, n_free, n_exempt=0, absorb='X+2m'):
    """Exact integer minimum of E = X + J over the counting constraints of PROOF.md section 4.
    n_good: certified targets; n_free: targets treated permissively; n_exempt: certified targets allowed two
    perfect halves (Lemma 4' hits), assumed tight.  Variables: m_g (non-tight certified), m_f (non-tight
    permissive), X >= m_g + m_f (total excess of non-tight targets) and J >= ceil(h_gamma / 2) with
    h_gamma >= max(0, n_good - m_g - n_exempt) - h_delta - 2 (n_free - m_f).  The bound on h_delta is the proved
    X + 2 (m_g + m_f) (absorb='X+2m') or, for the conditional variants of Open next question 3, X + m_g + m_f
    (absorb='X+m') or 0 (absorb='none')."""
    best = None
    for m_g in range(n_good + 1):
        for m_f in range(n_free + 1):
            m = m_g + m_f
            for X in range(m, m + 3 * n_good + 3):
                h_delta = {'X+2m': X + 2 * m, 'X+m': X + m, 'none': 0}[absorb]
                h_gamma = max(0, n_good - m_g - n_exempt) - h_delta - 2 * (n_free - m_f)
                E = X + max(0, -(-h_gamma // 2))
                if best is None or E < best[0]:
                    best = (E, m_g, m_f, X)
    return best


# ----------------------------------------------------------------- geometry lemma and rank-one inventory
def lemma(g, F, maxd=4):
    """Breadth-first enumeration of every source-spanned frame of dimension <= maxd (frames as 512-bit
    point masks; T(F) carried incrementally as the intersection of the source incidence sets T_s).
    Returns per dimension: frame count, max |S(F)||T(F)|, (|S|,|T|) histogram, the shapes attaining the
    maximum, and the histogram of
    frame-class blocks (|S(F)|, class size), where a class is a maximal set of targets in T(F) whose rows
    restricted to S(F) are proportional (maximal within T(F) for this frame, not over all frames)."""
    n, q, C = g['n'], g['q'], g['C']
    Ts = [bits(t for t in range(n) if C[t][s]) for s in range(n)]
    srcpt = {q[s]: s for s in range(n)}

    def pts(mask):
        out = []
        while mask:
            low = mask & -mask
            out.append(low.bit_length() - 1)
            mask ^= low
        return out

    level = {(1 | 1 << q[s]): Ts[s] for s in range(n)}
    res = {}
    for d in range(1, maxd + 1):
        best, shapes, rect = 0, {}, {}
        nxt = {}
        for mask, T in level.items():
            P = pts(mask)
            S = [srcpt[p] for p in P if p in srcpt]
            ns, nt_ = len(S), bin(T).count('1')
            shapes[(ns, nt_)] = shapes.get((ns, nt_), 0) + 1
            best = max(best, ns * nt_)
            if nt_:
                s0 = S[0]
                cls = {}
                for t in members(T):
                    key = tuple((C[t][s] > 0) == (C[t][s0] > 0) for s in S)
                    cls[key] = cls.get(key, 0) + 1
                for size in cls.values():
                    rect[(ns, size)] = rect.get((ns, size), 0) + 1
            if d < maxd:
                for s in range(n):
                    if not mask >> q[s] & 1:
                        m2 = mask
                        for p in P:
                            m2 |= 1 << (p ^ q[s])
                        if m2 not in nxt:
                            nxt[m2] = T & Ts[s]
        res[d] = dict(frames=len(level), max_ST=best,
                      shapes=sorted([list(k) + [v] for k, v in shapes.items()]),
                      equality_shapes=sorted([list(k) + [v] for k, v in shapes.items() if k[0] * k[1] == best]),
                      rank_one_rectangles=sorted([list(k) + [v] for k, v in rect.items()]))
        level = nxt
    return res
