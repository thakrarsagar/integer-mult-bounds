#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Replay the P104 top-level mixing bound: finite facts F1-F8, the 2x2 mixing test (Lemma 4) and its
singular-mixing variant (Lemma 4'), the lifetime floors of PROOF.md, the multi-value carriage demonstration
word (replayed by this primary replayer, by the UNCHANGED published relay checker and by independent.py),
seven negative controls with pinned rejection reasons, the side certificates (geometry lemma
|S(F)||T(F)| <= 48 for dims <= 4 and the frame-class block inventory) and the fixed-template allowances.

Usage (from the repository root):
    python3 -I -B research/p104-rank1-mixer-correction/verify.py [--skip-lemma] [--json NEW_FILE]
    python3 -I -B research/p104-rank1-mixer-correction/verify.py --extra-word WORD.json   (local, optional)
Prints PASS_P104_RANK1_MIXER_TOP ... on success; any failure raises SystemExit('FAIL: ...') naming the
violated condition.  Standard library only; exact Fractions; read-only except a private temporary directory."""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)
import build_demo as BD  # noqa: E402
import top_primary as P  # noqa: E402
from top_primary import need  # noqa: E402

VENDOR = os.path.join(HERE, 'vendor', 'check_p104_relay_construction.py')
VENDOR_SHA = 'b808e70129fc2c01fbead974c770e0a39245f3a3968c53bcd1f49fb1972e865d'
SELECTED_SAVING = Q(67018507072324140917, 40000000000000000000000)   # selected complex saving (PR2675)
CHANNEL = {1: 1074, 2: 58, 3: 86, 4: 104, 5: 48, 6: 24, 7: 8, 8: 8}
TEMPLATE = (73, 832, 9, 56)


def sha(path):
    with open(path, 'rb') as fh:
        return hashlib.sha256(fh.read()).hexdigest()


# ----------------------------------------------------------------- primary replayer (echelon frames)
def replay(g, word):
    """Replay a word in the published relay format with separate bookkeeping.  Rejects unknown ops,
    non-nested or non-increasing moves, reads/writes outside the retained frames, cut regressions,
    dirty or inexact target rows and unrestored lifetimes."""
    n, C = g['n'], g['C']
    ops = word['ops']
    need(ops and ops[0][0] == 'move_zero_all', 'the word does not start with move_zero_all')
    NL = ops[0][1]
    frame = [()] * NL
    steps = [[] for _ in range(NL)]
    val = [{('d', L): Q(1)} for L in range(NL)]
    Y = [{} for _ in range(n)]
    now = 0

    def at(path, c):
        cur = None
        for start, f in path:
            if start <= c:
                cur = f
        return cur

    def add(dst, c, src):
        for k, v in src.items():
            z = dst.get(k, 0) + c * v
            if z:
                dst[k] = z
            else:
                dst.pop(k, None)

    for o in ops[1:]:
        kind = o[0]
        if kind == 'move':
            L, new = o[1], P.rref(o[2])
            need(len(new) > len(frame[L]) and P.contained(frame[L], new),
                 'move does not strictly enlarge the frame of lifetime %d' % L)
            steps[L].append(len(new) - len(frame[L]))
            frame[L] = new
        elif kind == 'read':
            L, s, c, cut = o[1], o[2], Q(o[3]), o[4]
            need(cut >= now, 'read at cut %d precedes the previous cut %d' % (cut, now))
            now = cut
            need(frame[L] == at(g['X'][s], cut), 'read of X%d outside its retained frame at cut %d' % (s, cut))
            add(val[L], c, {('x', s): Q(1)})
        elif kind == 'shear':
            i, j, c = o[1], o[2], Q(o[3])
            need(i != j and frame[i] == frame[j], 'shear %d += c*%d does not join two distinct lifetimes in one frame' % (i, j))
            add(val[i], c, dict(val[j]))
        elif kind == 'write':
            t, L, c, cut = o[1], o[2], Q(o[3]), o[4]
            need(cut >= now, 'write at cut %d precedes the previous cut %d' % (cut, now))
            now = cut
            need(frame[L] == at(g['Y'][t], cut), 'write to Y%d outside its frame at cut %d' % (t, cut))
            add(Y[t], c, val[L])
        else:
            raise SystemExit('FAIL: operation %r is outside the X-only grammar' % (kind,))
    for t in range(n):
        need(all(k[0] == 'x' for k in Y[t]), 'Y%d keeps a dirty residue' % t)
        need({k[1]: v for k, v in Y[t].items()} == {s: C[t][s] for s in range(n) if C[t][s]},
             'Y%d is not row %d of I-G/2' % (t, t))
    need(all(f == P.FULL_BASIS for f in frame), 'a lifetime does not end at FULL')
    need(all(val[L] == {('d', L): Q(1)} for L in range(NL)), 'a dirty lifetime is not restored')
    need(all(sum(s) == 9 for s in steps), 'a lifetime does not climb exactly 9 rank units')
    prof = {}
    for s in steps:
        for r in s:
            prof[r] = prof.get(r, 0) + 1
    return dict(lifetimes=NL, profile={str(r): prof[r] for r in sorted(prof)},
                rank_mass=sum(r * c for r, c in prof.items()))


def controls(g, word):
    """Seven rejecting mutations of the demonstration word; each must FAIL in every replayer for the pinned
    reason (EXPECTED.json control_reasons)."""
    P_, R_ = word['meta']['mixer_lifetimes']
    t0 = word['meta']['pair'][0]
    ops = word['ops']
    k_mix = next(i for i, o in enumerate(ops) if o[0] == 'shear' and o[1] == R_ and o[3] == '-1/2')
    k_comp = next(i for i, o in enumerate(ops) if o[0] == 'write' and o[4] == 0 and o[2] == P_)
    k_toK = next(i for i, o in enumerate(ops) if o[0] == 'move' and o[1] == P_ and len(o[2]) == 7)
    W = next(o[2] for o in ops if o[0] == 'move' and o[1] == P_ and len(o[2]) == 6)
    wprime = next(o[2] for o in ops if o[0] == 'move' and o[1] == R_ and len(o[2]) == 6)
    K = P.rref(ops[k_toK][2])
    v = next(x for x in range(1, 512) if not P.member(K, x))
    K_other = P.rref(list(W) + [v])             # a different 7-frame containing W: a legal move for P
    need(len(K_other) == 7 and K_other != K and P.contained(P.rref(W), K_other),
         'control setup: no second 7-frame containing W was found')
    k_read = next(i for i, o in enumerate(ops) if o[0] == 'read' and o[4] == 0)
    k_final = next(i for i, o in enumerate(ops) if o[0] == 'write' and o[4] != 0 and o[1] == t0)
    cut_H = g['Y'][t0][-1][0]                    # first cut at which Y_t0 is at H_t0
    need(cut_H >= 1, 'control setup: Y_%d is at H_%d from cut 0' % (t0, t0))
    out = {}

    def mutate(name, fn):
        w = json.loads(json.dumps(word))
        fn(w['ops'])
        out[name] = w
    mutate('perturbed_mixer_coefficient', lambda o: o[k_mix].__setitem__(3, '-1/3'))
    mutate('dirty_residue', lambda o: o.pop(k_comp))
    mutate('illegal_frame_move', lambda o: o.__setitem__(k_toK, ['move', P_, list(wprime)]))
    mutate('non_monotone_lifetime', lambda o: o.insert(k_mix + 1, ['move', R_, list(wprime)]))
    mutate('read_of_Y', lambda o: o.insert(k_read + 1, ['read_Y', o[k_read][1], 0, '1', 0]))
    mutate('unequal_frame_shear', lambda o: o.__setitem__(k_toK, ['move', P_, list(K_other)]))
    mutate('write_before_target_frame', lambda o: o[k_final].__setitem__(4, cut_H - 1))
    return out


def published(word_path):
    proc = subprocess.run([sys.executable, '-I', '-B', VENDOR, ROOT, word_path], capture_output=True, text=True,
                          timeout=600)
    return proc.returncode, (proc.stdout + proc.stderr).strip().splitlines()


def independent_replay(word_path):
    proc = subprocess.run([sys.executable, '-I', '-B', os.path.join(HERE, 'independent.py'), ROOT, word_path,
                           '--replay-only'], capture_output=True, text=True, timeout=600)
    lines = (proc.stdout + proc.stderr).strip().splitlines()
    return proc.returncode, (lines[-1] if lines else '')


def extra_word(g, path):
    """Optional local check (not registered): replay a third-party word with the primary replayer and the
    vendored published checker, report whether it lies in the final-frame delivery class, and compare with
    the floors."""
    with open(path) as fh:
        word = json.load(fh)
    rep = replay(g, word)
    code, lines = published(path)
    need(code == 0, 'the published checker rejects the extra word: %r' % lines[-1:])
    def target_frame(t, c):
        cur = None
        for start, f in g['Y'][t]:
            if start <= c:
                cur = f
        return cur
    # final-frame class: every write happens while Y_t is at ZERO (no x-content possible) or at H_t
    final_frame = all(target_frame(o[1], o[4]) in ((), g['Y'][o[1]][-1][1]) for o in word['ops'] if o[0] == 'write')
    floor = 234 if final_frame else 219
    need(rep['lifetimes'] >= floor, 'the extra word has fewer lifetimes than the proved floor')
    return dict(extra_word=os.path.basename(path), replay=rep, published=lines[-1], final_frame_class=final_frame,
                applicable_floor=floor)


def allowance(per):
    """Largest k such that the channel profile plus k lifetimes of step multiset `per` passes the merged
    ceiling.py relaxation (PR2675 fixed template, ideal idle) at the selected complex saving."""
    sys.path.insert(0, os.path.join(ROOT, 'research', 'complex-local-word-ceiling'))
    import ceiling as CE

    def passes(k):
        prof = dict(CHANNEL)
        for r, c in per.items():
            prof[r] = prof.get(r, 0) + c * k
        try:
            return CE.relax(prof, *TEMPLATE, SELECTED_SAVING)[1] < 1
        except ValueError:
            return False
    lo, hi = 0, 2000
    need(passes(lo) and not passes(hi), 'the allowance bisection bracket [0, 2000] does not straddle the transition')
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (mid, hi) if passes(mid) else (lo, mid)
    return lo


SHARED_KEYS = (
    # F1-F4
    'row_support_size_hist', 'diagonal_nonzero', 'offdiag_values', 'x_frames_dim_ge7',
    'x_frames_dim_ge7_inside_target_hyperplane', 'x_frame_target_containments_by_dim', 'y_intermediate_max_dim',
    'distinct_odd_normals', 'normal_weight_hist', 'normal_sum_triples', 'normal_shifted_sum_triples',
    'complementary_target_triples', 'ustar', 'SI_sizes_histogram',
    # F5-F6'
    'single_cover_violations', 'min_uncovered_by_one_hyperplane', 'final_frame_cover_hist', 'full_cover_hist', 'good_targets',
    # F7-F8, Lemma 4' and the structural reading of F8
    'pairs_passing_T_final_frame', 'pairs_passing_T_full', 'pairs_passing_T_full_good_good',
    'pairs_passing_T_shapes_final_frame', 'both_halves_T_final_frame', 'both_halves_T_full_good',
    'both_halves_T_any_targets_any_cover_full', 'any_cover_triples_unfiltered_full',
    'pairs_passing_Tprime_final_frame', 'pairs_passing_Tprime_full',
    'both_halves_Tprime_final_frame_targets', 'both_halves_Tprime_full_good_targets',
    'both_halves_Tprime_full_good_target_ids',
    'pair_SK_size_hist', 'pairs_passing_T_SK_size_hist', 'pairs_passing_Tprime_SK_size_hist',
    'complementary_halves_SK_sizes',
    # floors
    'floor_final_frame', 'floor_full', 'floor_final_frame_singular_mixing', 'floor_full_singular_mixing',
    'conditional_floor_final_frame',
    'demo_word_sha256')
LEMMA_KEYS = ('lemma', 'lemma_equality_shapes', 'rank_one_inventory_top')


def main():
    argv = sys.argv[1:]
    skip_lemma = '--skip-lemma' in argv
    if '--extra-word' in argv:
        g = P.load(ROOT)
        print(json.dumps(extra_word(g, argv[argv.index('--extra-word') + 1]), indent=1, sort_keys=True))
        print('PASS_P104_RANK1_MIXER_EXTRA_WORD')
        return
    with open(os.path.join(HERE, 'EXPECTED.json')) as fh:
        EXP = json.load(fh)
    need(sha(VENDOR) == VENDOR_SHA, 'the vendored published checker differs from fac9e821 (sha256 mismatch)')
    g = P.load(ROOT)
    F = P.facts(g)
    n = g['n']
    out = dict(F['report'])
    sizes = [bin(m).count('1') for m in F['SI']]
    out['SI_sizes_histogram'] = {str(k): sizes.count(k) for k in sorted(set(sizes))}
    R_full = [F['supp'][t] & ~F['SI'][t] for t in range(n)]
    R_res = list(F['supp'])
    f5_res, f5_res_hist = P.single_cover_stats(g, F, R_res)
    f5_full, f5_full_hist = P.single_cover_stats(g, F, R_full)
    out['single_cover_violations'] = f5_res + f5_full
    out['min_uncovered_by_one_hyperplane'] = dict(final_frame=f5_res_hist, full=f5_full_hist)
    need(out['single_cover_violations'] == 0, 'F5 fails: a hyperplane of some H_t covers R_t')
    cov_full = P.covers(g, F, R_full)
    cov_res = P.covers(g, F, R_res)
    need(all(len(c) == 127 and all(r[4] and r[5] == 7 and r[6] == 7 for r in c) for c in cov_res),
         'F6 fails: some target lacks exactly 127 complementary spanning two-covers in the final-frame class')

    def cover_hist(cov):
        h = {}
        for c in cov:
            key = (len(c), sum(1 for r in c if r[4]))
            h[key] = h.get(key, 0) + 1
        return sorted(list(k) + [v] for k, v in h.items())
    out['final_frame_cover_hist'] = cover_hist(cov_res)
    out['full_cover_hist'] = cover_hist(cov_full)
    good = [t for t in range(n) if all(r[4] and r[5] == 7 and r[6] == 7 for r in cov_full[t])]
    out['good_targets'] = len(good)
    need(good == [t for t in range(n) if sizes[t] in (0, 1, 2, 4)], "F6' fails: good targets are not |S_I| in {0,1,2,4}")
    LLr = [[False] * n for _ in range(n)]       # T(t, a), final-frame class
    LLf = [[False] * n for _ in range(n)]       # T(t, a), full model
    SGr = [[False] * n for _ in range(n)]       # T'(t, a), final-frame class
    SGf = [[False] * n for _ in range(n)]       # T'(t, a), full model
    ALL = [[a != t for a in range(n)] for t in range(n)]    # unfiltered relation, for the companion statistics
    for t in range(n):
        for a in range(t + 1, n):
            LLr[t][a] = LLr[a][t] = P.pair_test(g, R_res, t, a, F['supp'])
            LLf[t][a] = LLf[a][t] = P.pair_test(g, R_full, t, a, F['supp'])
            SGr[t][a] = SGr[a][t] = P.pair_test(g, R_res, t, a, F['supp'], singular=True)
            SGf[t][a] = SGf[a][t] = P.pair_test(g, R_full, t, a, F['supp'], singular=True)

    def npairs(M, pool=None):
        pool = range(n) if pool is None else pool
        return sum(M[t][a] for t in pool for a in pool if t < a)

    def sk_hist(M, pool=None):
        """histogram of |S(H_t ∩ H_a)| over the pairs t < a in pool related by M"""
        pool = range(n) if pool is None else pool
        h = {}
        for t in pool:
            for a in pool:
                if t < a and M[t][a]:
                    k = bin(F['supp'][t] & F['supp'][a]).count('1')
                    h[k] = h.get(k, 0) + 1
        return {str(k): h[k] for k in sorted(h)}
    out['pairs_passing_T_final_frame'] = npairs(LLr)
    out['pairs_passing_T_full'] = npairs(LLf)
    out['pairs_passing_T_full_good_good'] = npairs(LLf, good)
    out['pairs_passing_Tprime_final_frame'] = npairs(SGr)
    out['pairs_passing_Tprime_full'] = npairs(SGf)
    # structural reading of F8 / F8' (PROOF.md section 2): |S(K)| of all pairs, of T- and T'-pairs, of complementary halves
    out['pair_SK_size_hist'] = sk_hist(ALL)
    out['pairs_passing_T_SK_size_hist'] = dict(final_frame=sk_hist(LLr), full=sk_hist(LLf),
                                               full_good_good=sk_hist(LLf, good))
    out['pairs_passing_Tprime_SK_size_hist'] = dict(final_frame=sk_hist(SGr), full=sk_hist(SGf),
                                                    full_good_good=sk_hist(SGf, good))
    comp_all = P.complementary_perfect(g, F, list(range(n)), ALL)
    out['complementary_target_triples'] = len(comp_all)
    need(len(comp_all) == out['normal_shifted_sum_triples'],
         'complementary triples by source partitions differ from the shifted normal-sum count')
    halves = {}
    for t, a, b in comp_all:
        k = (bin(F['supp'][t] & F['supp'][a]).count('1'), bin(F['supp'][t] & F['supp'][b]).count('1'))
        halves[k] = halves.get(k, 0) + 1
    out['complementary_halves_SK_sizes'] = sorted(list(k) + [v] for k, v in halves.items())
    shapes = {}
    for t in range(n):
        for a in range(t + 1, n):
            if LLr[t][a]:
                SK = P.members(F['supp'][t] & F['supp'][a])
                pl = [s for s in SK if g['C'][a][s] == g['C'][t][s]]
                mi = [s for s in SK if g['C'][a][s] == -g['C'][t][s]]
                key = (len(SK), len(pl), len(mi), P.rank_of([g['q'][s] for s in pl]), P.rank_of([g['q'][s] for s in mi]))
                shapes[key] = shapes.get(key, 0) + 1
    out['pairs_passing_T_shapes_final_frame'] = sorted(list(k) + [v] for k, v in shapes.items())
    out['both_halves_T_final_frame'] = len(P.complementary_perfect(g, F, list(range(n)), LLr))
    out['both_halves_T_full_good'] = len(P.complementary_perfect(g, F, good, LLf))
    need(out['both_halves_T_final_frame'] == 0 and out['both_halves_T_full_good'] == 0,
         'F8 fails: some certified target has two complementary halves passing T')
    out['both_halves_T_any_targets_any_cover_full'] = P.any_cover_hits(g, F, R_full, LLf)
    out['any_cover_triples_unfiltered_full'] = P.any_cover_hits(g, F, R_full, ALL)
    # structural reading of F8 (PROOF.md section 2): complementary halves are always (24, 24), every pair-half
    # two-cover of R_t (full model, any target) is complementary, and no pair passing T has |S(K)| = 24
    need(max(int(k) for k in out['pair_SK_size_hist']) == 24
         and out['complementary_halves_SK_sizes'] == [[24, 24, len(comp_all)]],
         'structural F8: complementary halves are not all (24, 24)')
    need(out['any_cover_triples_unfiltered_full'] == len(comp_all),
         'structural F8: some pair-half two-cover of R_t in the full model is not complementary')
    need(all('24' not in h for h in out['pairs_passing_T_SK_size_hist'].values()),
         'structural F8: a pair passing T has |S(K)| = 24')
    sing_r = sorted({h[0] for h in P.complementary_perfect(g, F, list(range(n)), SGr)})
    sing_f = sorted({h[0] for h in P.complementary_perfect(g, F, good, SGf)})
    out['both_halves_Tprime_final_frame_targets'] = len(sing_r)
    out['both_halves_Tprime_full_good_targets'] = len(sing_f)
    out['both_halves_Tprime_full_good_target_ids'] = sing_f
    e_res = P.floor_excess(n, 0)
    e_full = P.floor_excess(len(good), n - len(good))
    e_res_s = P.floor_excess(n, 0, n_exempt=len(sing_r))
    e_full_s = P.floor_excess(len(good), n - len(good), n_exempt=len(sing_f))
    out['floor_final_frame'] = 2 * n + e_res[0]
    out['floor_full'] = 2 * n + e_full[0]
    out['floor_final_frame_singular_mixing'] = 2 * n + e_res_s[0]
    out['floor_full_singular_mixing'] = 2 * n + e_full_s[0]
    out['floor_minimizers'] = dict(final_frame=list(e_res), full=list(e_full), final_frame_singular_mixing=list(e_res_s),
                                   full_singular_mixing=list(e_full_s))
    out['conditional_floor_final_frame'] = {'absorb_at_most_b_minus_1': 2 * n + P.floor_excess(n, 0, absorb='X+m')[0],
                                            'no_absorption': 2 * n + P.floor_excess(n, 0, absorb='none')[0]}
    pair = EXP['demo_pair']
    need(LLr[pair[0]][pair[1]], 'the demonstration pair fails the 2x2 test')
    word = BD.build(g, *pair)
    reasons = EXP['control_reasons']
    tmp = tempfile.mkdtemp(prefix='p104mix-')
    try:
        wpath = os.path.join(tmp, 'DEMO-WORD.json')
        BD.dump(word, wpath)
        out['demo_word_sha256'] = sha(wpath)
        out['demo_meta'] = word['meta']
        out['demo_replay'] = replay(g, word)
        code, lines = published(wpath)
        need(code == 0 and lines and lines[-1].startswith('PASS_P104_RELAY_CONSTRUCTION lifetimes=%d ' % word['lifetimes']),
             'the published checker rejects the demonstration word: %r' % lines[-1:])
        out['demo_published_checker'] = lines[-1]
        code, last = independent_replay(wpath)
        need(code == 0 and last.startswith('PASS_P104_INDEPENDENT_REPLAY lifetimes=%d' % word['lifetimes']),
             'independent replay-only mode rejects the demonstration word: %r' % last)
        ctl = {}
        mutants = controls(g, word)
        need(sorted(mutants) == sorted(reasons), 'the control set differs from EXPECTED.json control_reasons')
        for name, w in mutants.items():
            got = {}
            try:
                replay(g, w)
                got['primary'] = 'ACCEPTED'
            except SystemExit as e:
                got['primary'] = str(e)
            cp = os.path.join(tmp, name + '.json')
            BD.dump(w, cp)
            c2, l2 = published(cp)
            got['published'] = l2[-1] if c2 != 0 and l2 else 'ACCEPTED'
            c3, l3 = independent_replay(cp)
            got['independent'] = l3 if c3 != 0 else 'ACCEPTED'
            for who, prefix in (('primary', 'FAIL: '), ('published', 'FAIL: '), ('independent', 'FAIL(independent): ')):
                need(got[who].startswith(prefix) and reasons[name][who] in got[who],
                     'control %s: %s replayer did not reject for the pinned reason %r (got %r)'
                     % (name, who, reasons[name][who], got[who]))
            ctl[name] = got
        out['controls'] = ctl
        ind = subprocess.run([sys.executable, '-I', '-B', os.path.join(HERE, 'independent.py'), ROOT, wpath]
                             + (['--skip-lemma'] if skip_lemma else []), capture_output=True, text=True, timeout=1800)
        need(ind.returncode == 0, 'the independent checker failed: ' + (ind.stdout + ind.stderr)[-600:])
        ind_lines = ind.stdout.strip().splitlines()
        out['independent'] = ind_lines[-1]
        ind_json = json.loads(ind_lines[-2])
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    for key in SHARED_KEYS:
        need(key in ind_json, 'independent.py does not report %s' % key)
        need(json.loads(json.dumps(ind_json[key])) == json.loads(json.dumps(out[key])),
             'independent disagrees on %s: %r vs %r' % (key, ind_json[key], out[key]))
    need(ind_json['demo_lifetimes'] == word['lifetimes'] and ind_json['demo_profile'] == out['demo_replay']['profile'],
         'independent replay disagrees on the demonstration word')
    out['allowances_selected_saving'] = {'1x9': allowance({1: 9}), '1,1,7': allowance({1: 2, 7: 1}),
                                         '1,1,1,6': allowance({1: 3, 6: 1}), '1,1,1,1,5': allowance({1: 4, 5: 1})}
    if not skip_lemma:
        lem = P.lemma(g, F, 4)
        out['lemma'] = {str(d): dict(frames=v['frames'], max_ST=v['max_ST']) for d, v in lem.items()}
        out['lemma_equality_shapes'] = {str(d): v['equality_shapes'] for d, v in lem.items()}
        out['rank_one_inventory'] = {str(d): v['rank_one_rectangles'] for d, v in lem.items()}
        out['rank_one_inventory_top'] = {str(d): [r for r in v['rank_one_rectangles'] if r[0] * r[1] >= 40]
                                         for d, v in lem.items()}
        need(all(v['max_ST'] == 48 for v in lem.values()), 'geometry lemma fails: max |S(F)||T(F)| != 48 in some dimension')
        for d, v in lem.items():
            need(ind_json['lemma'][str(d)] == v['max_ST'], 'independent lemma maximum disagrees at dim %d' % d)
            need(ind_json['lemma_equality_shapes'][str(d)] == sorted([r[0], r[1]] for r in v['equality_shapes']),
                 'independent lemma equality shapes disagree at dim %d' % d)
    for key, want in EXP['expected'].items():
        if skip_lemma and key in LEMMA_KEYS:
            continue
        need(key in out, 'EXPECTED.json key %s is not produced by this run' % key)
        got = json.loads(json.dumps(out[key]))
        need(got == want, 'expected %s=%r, got %r' % (key, want, got))
    if '--json' in argv:
        with open(argv[argv.index('--json') + 1], 'x') as fh:
            json.dump(out, fh, indent=1, sort_keys=True)
    show = {k: out[k] for k in sorted(out) if k not in ('rank_one_inventory',)}
    print(json.dumps(show, indent=1, sort_keys=True))
    print('PASS_P104_RANK1_MIXER_TOP floor_full=%d floor_final_frame=%d floor_full_singular_mixing=%d '
          'pairs_passing_T_final_frame=%d pairs_passing_T_full=%d both_halves_T=%d demo_lifetimes=%d controls=%d%s' % (
              out['floor_full'], out['floor_final_frame'], out['floor_full_singular_mixing'],
              out['pairs_passing_T_final_frame'], out['pairs_passing_T_full'],
              out['both_halves_T_final_frame'] + out['both_halves_T_full_good'], word['lifetimes'], len(out['controls']),
              '' if skip_lemma else ' lemma_max_ST=%d' % max(v['max_ST'] for v in lem.values())))


if __name__ == '__main__':
    main()
