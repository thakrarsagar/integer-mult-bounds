"""Count the two residual Schur guards by complementary planes over F2.

Independent finite check of the seven representatives in PR #4689.  No GL4
matrices or predecessor executable are enumerated or imported.
"""

from itertools import product

S = (0, 0, 4, 8)
STATES = (
    ((0, 0, 4, 8), 1, 36, (280, 180, 100)),
    ((0, 0, 4, 9), 3, 4, (3192, 1380, 468)),
    ((0, 2, 0, 8), 126, 1, (15120, 4674, 366)),
    ((0, 2, 2, 8), 18, 1, (14448, 4896, 816)),
    ((0, 4, 4, 8), 3, 4, (3192, 1380, 468)),
    ((0, 4, 4, 9), 3, 4, (3528, 1242, 270)),
    ((0, 6, 0, 8), 18, 1, (14448, 4896, 816)),
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def apply(matrix, vector):
    return sum(((row & vector).bit_count() % 2) << i
               for i, row in enumerate(matrix))


def multiply(a, b):
    out = []
    for row in a:
        value = 0
        for j in range(4):
            if row & (1 << j):
                value ^= b[j]
        out.append(value)
    return tuple(out)


def columns(vectors):
    return tuple(sum(((v >> i) & 1) << j for j, v in enumerate(vectors))
                 for i in range(4))


def planes():
    return sorted({tuple(sorted((0, x, y, x ^ y)))
                   for x in range(1, 16) for y in range(x + 1, 16)})


def stabilizer(t):
    # Every matrix commuting with S preserves ker S and im S.  Each block is GL2.
    gl2 = [(x, y) for x in range(1, 4) for y in range(1, 4) if x != y]
    return sum(multiply(columns((a, b, c << 2, d << 2)), t)
               == multiply(t, columns((a, b, c << 2, d << 2)))
               for (a, b), (c, d) in product(gl2, repeat=2))


def transitions(t, subspaces):
    first = full = decompositions = 0
    for u, w in product(subspaces, repeat=2):
        projection = {x ^ y: x for x in u for y in w}
        if len(projection) != 16:
            continue
        decompositions += 1
        # The order-two principal minor is invertible precisely when the
        # projected restrictions S|U and T|U are both invertible.
        x, y = u[1:3]
        su = [projection[apply(S, v)] for v in (x, y)]
        tu = [projection[apply(t, v)] for v in (x, y)]
        second_good = (su[0] and su[1] and su[0] != su[1]
                       and tu[0] and tu[1] and tu[0] != tu[1])
        for x in u[1:]:
            sx, tx = projection[apply(S, x)], projection[apply(t, x)]
            for y in u[1:]:
                if x == y:
                    continue
                # In basis (x,y), the first pivot is 1 iff the projected
                # image of x is x or x+y.  Six bases of W share this result.
                if sx in (x, x ^ y) and tx in (x, x ^ y):
                    first += 6
                    full += 6 * second_good
    need(decompositions == 560, "complementary plane count")
    return first, full


def main():
    subspaces = planes()
    need(len(subspaces) == 35, "two-plane count")
    total = 0
    for index, (t, split_count, expected_stabilizer, expected_depths) in enumerate(STATES, 1):
        z = stabilizer(t)
        first, full = transitions(t, subspaces)
        need(z == expected_stabilizer, f"state {index} stabilizer")
        need(first % z == full % z == 0, f"state {index} orbit divisibility")
        depths = ((20160 - first) // z, (first - full) // z, full // z)
        need(depths == expected_depths, f"state {index} depths {depths}")
        total += split_count * full
        print(f"state {index}: stabilizer={z} orbit={20160 // z} "
              f"depths={depths} full_headers={split_count * full}")
    need(total == 93564, "aggregate full-guard count")
    print(f"PASS_PLANE_TRANSITIONS full_guard_headers={total} "
          "decompositions_per_state=560 no_GL4_enumeration")


if __name__ == "__main__":
    main()
