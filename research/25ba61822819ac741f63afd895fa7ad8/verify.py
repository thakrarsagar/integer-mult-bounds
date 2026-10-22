"""Exact span check for stacked row and column charts over F_2^9 tensor F_2^9."""

DIM = 9


def tensor(left, right):
    return sum(right << (DIM * i) for i in range(DIM) if left >> i & 1)


def rank(vectors):
    pivots = {}
    for vector in vectors:
        while vector:
            bit = vector.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = vector
                break
            vector ^= pivots[bit]
    return len(pivots)


def check():
    # Two different invertible triangular changes of basis avoid only
    # checking coordinate subspaces.
    rows = [(1 << i) | (1 << (i + 1)) if i < DIM - 1 else 1 << i
            for i in range(DIM)]
    cols = [1 << 0 if i == 0 else (1 << i) | (1 << (i - 1))
            for i in range(DIM)]
    assert rank(rows) == rank(cols) == DIM
    for a in range(DIM + 1):
        for b in range(DIM + 1):
            vectors = [tensor(r, v) for r in rows[:a] for v in rows]
            vectors += [tensor(v, c) for v in rows for c in cols[:b]]
            actual = rank(vectors)
            expected = DIM * DIM - (DIM - a) * (DIM - b)
            assert actual == expected, (a, b, actual, expected)
    assert 81 - (9 - 1) * (9 - 1) == 17
    assert 81 - (9 - 8) * (9 - 8) == 80
    print("PASS_P104_STACKED_CHART_SPAN 100 dimension pairs; codim=(9-a)(9-b)")


if __name__ == "__main__":
    check()
