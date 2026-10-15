# SPDX-License-Identifier: Apache-2.0
"""Deterministic builder of the multi-value carriage demonstration word.

One invertible 2x2 mixer sits at the shared 7-frame K = H_t ∩ H_a of a pair (t, a) passing the 2x2 test T:
nine lifetimes gather the '+' ratio class into a 6-dim frame W, nine gather the '-' class into W',
the two carriers meet at K, are mixed by two shears, and then leave K for H_t and H_a carrying
C_t|S(K) and -(C_a|S(K))/2.  Every other demanded entry uses its own lifetime
ZERO -> line -> H_t -> FULL.  Dirty values are compensated at cut 0 and restored at FULL.
Word format: the unchanged published relay checker's format (Discussion #2245, relay-construction)."""
import json
from fractions import Fraction as Q

from top_primary import FULL_BASIS, contained, need, rref


def build(g, t0, a0):
    n, q, C, NE = g['n'], g['q'], g['C'], g['NE']
    H = [list(g['Y'][t][-1][1]) for t in range(n)]
    supp = [frozenset(s for s in range(n) if C[t][s]) for t in range(n)]
    SK = sorted(supp[t0] & supp[a0])
    plus = [s for s in SK if C[a0][s] == C[t0][s]]
    minus = [s for s in SK if C[a0][s] == -C[t0][s]]
    W, Wp, K = rref([q[s] for s in plus]), rref([q[s] for s in minus]), rref([q[s] for s in SK])
    need(plus and minus and len(W) < 7 and len(Wp) < 7 and len(K) == 7,
         'pair (%d, %d) has an empty ratio class, a ratio class spanning K, or S(K) not spanning a 7-frame' % (t0, a0))
    need(contained(W, K) and contained(Wp, K) and contained(K, H[t0]) and contained(K, H[a0]),
         'the gathering frames are not nested inside K = H_%d ∩ H_%d' % (t0, a0))
    val, shears, reads, writes = {}, [], [], []
    low, mid, top, full = [], [], [], []
    count = [0]

    def new():
        L = count[0]
        count[0] += 1
        val[L] = {('d', L): Q(1)}
        return L

    def add(L, c, src):
        for k, v in src.items():
            z = val[L].get(k, 0) + c * v
            if z:
                val[L][k] = z
            else:
                val[L].pop(k, None)

    def read0(L, s, c):
        low.append(['move', L, [q[s]]])
        low.append(['read', L, s, str(c), 0])
        add(L, c, {('x', s): Q(1)})
        reads.append((L, s, c))

    def gather(cls, frame):
        lives = []
        for s in cls:
            L = new()
            read0(L, s, C[t0][s])
            lives.append(L)
        for L in lives:
            mid.append(['move', L, list(frame)])
        head = lives[0]
        for L in lives[1:]:
            mid.append(['shear', head, L, '1'])
            add(head, Q(1), dict(val[L]))
            shears.append((head, L, Q(1)))
        for L in lives[1:]:
            full.append(['move', L, list(FULL_BASIS)])
        return head

    P = gather(plus, W)
    R = gather(minus, Wp)
    mid += [['move', P, list(K)], ['move', R, list(K)]]
    mid.append(['shear', P, R, '1'])
    add(P, Q(1), dict(val[R]))
    shears.append((P, R, Q(1)))
    mid.append(['shear', R, P, '-1/2'])
    add(R, Q(-1, 2), dict(val[P]))
    shears.append((R, P, Q(-1, 2)))
    top += [['move', P, H[t0]], ['move', R, H[a0]]]
    writes += [(t0, P, Q(1)), (a0, R, Q(-2))]
    full += [['move', P, list(FULL_BASIS)], ['move', R, list(FULL_BASIS)]]
    for t in range(n):
        for s in sorted(supp[t]):
            if t in (t0, a0) and s in SK:
                continue
            L = new()
            c = C[t][s]
            low.append(['move', L, [q[s]]])
            low.append(['read', L, s, str(c), 0])
            add(L, c, {('x', s): Q(1)})
            reads.append((L, s, c))
            top.append(['move', L, H[t]])
            writes.append((t, L, Q(1)))
            full.append(['move', L, list(FULL_BASIS)])
    comp = []
    for t, L, c in writes:
        for k, v in sorted(val[L].items()):
            if k[0] == 'd':
                comp.append(['write', t, k[1], str(-c * v), 0])
    ops = [['move_zero_all', count[0]]] + comp + low + mid + top
    ops += [['write', t, L, str(c), NE] for t, L, c in writes] + full
    ops += [['shear', i, j, str(-c)] for i, j, c in reversed(shears)]
    ops += [['read', L, s, str(-c), NE] for L, s, c in reads]
    meta = dict(pair=[t0, a0], shared_sources=len(SK), plus=len(plus), minus=len(minus),
                W_dim=len(W), Wp_dim=len(Wp), mixer_lifetimes=[P, R], gather_lifetimes=len(SK),
                per_entry_lifetimes=count[0] - len(SK))
    return dict(lifetimes=count[0], design='one 2x2 mixer at K=H_%d cap H_%d plus per-entry lifetimes' % (t0, a0),
                meta=meta, ops=ops)


def dump(word, path):
    with open(path, 'w') as fh:
        json.dump(word, fh, separators=(',', ':'), sort_keys=True)
