"""Reviewer's independent check of the power-contamination claims. Shares no code with the
package under review. Rule, from Mehiri-Nadji section 2.1: an empty cell becomes contaminated
when two of its four orthogonal neighbours are contaminated, or when two diagonally opposite
neighbours (NW+SE or NE+SW) are contaminated."""
import itertools, sys
from fractions import Fraction
from math import comb


def make(h, w):
    idx = lambda r, c: r * w + c
    rules = []                       # per cell: list of (bit_a, bit_b) pairs that infect it
    for r in range(h):
        for c in range(w):
            orth = [idx(rr, cc) for rr, cc in ((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1)) if 0 <= rr < h and 0 <= cc < w]
            pairs = [(1 << a, 1 << b) for a, b in itertools.combinations(orth, 2)]
            for (r1, c1), (r2, c2) in (((r - 1, c - 1), (r + 1, c + 1)), ((r - 1, c + 1), (r + 1, c - 1))):
                if 0 <= r1 < h and 0 <= c1 < w and 0 <= r2 < h and 0 <= c2 < w:
                    pairs.append((1 << idx(r1, c1), 1 << idx(r2, c2)))
            rules.append(pairs)
    full = (1 << (h * w)) - 1

    def closure(s):
        changed = True
        while changed:
            changed = False
            for cell in range(h * w):
                if not (s >> cell) & 1:
                    for a, b in rules[cell]:
                        if s & a and s & b:
                            s |= 1 << cell; changed = True; break
        return s
    return closure, full, idx


def count_min(h, w, size):
    closure, full, _ = make(h, w)
    n = 0
    for combo in itertools.combinations(range(h * w), size):
        s = 0
        for x in combo: s |= 1 << x
        if closure(s) == full: n += 1
    return n


ok = True
def check(name, cond, extra=""):
    global ok; ok &= bool(cond); print(("ok   " if cond else "FAIL ") + name, extra)

# ---- Conjecture 2: alpha_{2,2k+1} = (k+1)(3k+2)2^(k-1), minimum size k+2
for k in range(1, 6):
    below = count_min(2, 2 * k + 1, k + 1)
    got = count_min(2, 2 * k + 1, k + 2)
    want = (k + 1) * (3 * k + 2) * 2 ** (k - 1)
    check(f"2 x {2*k+1}: no percolating set of size {k+1}; {got} of size {k+2}", below == 0 and got == want, f"(formula {want})")

# ---- two-row characterisation and generating function, every subset, widths 1..9
def word_ok(cols):
    if cols[0] == 0 or cols[-1] == 0: return False
    if any(cols[i] == 0 and cols[i + 1] == 0 for i in range(len(cols) - 1)): return False
    if 3 in cols: return True
    return any({cols[i], cols[i + 1]} == {1, 2} for i in range(len(cols) - 1))
P = {}
char_ok = True; tested = 0
for w in range(1, 10):
    closure, full, idx = make(2, w)
    coeff = [0] * (2 * w + 1)
    for cols in itertools.product(range(4), repeat=w):     # 0 empty, 1 upper, 2 lower, 3 both
        s = 0
        for c, v in enumerate(cols):
            if v & 1: s |= 1 << idx(0, c)
            if v & 2: s |= 1 << idx(1, c)
        perc = closure(s) == full
        tested += 1
        if perc != word_ok(cols): char_ok = False
        if perc: coeff[bin(s).count("1")] += 1
    P[w] = coeff
check(f"two-row characterisation, all {tested} subsets for widths 1..9", char_ok)

# series of q x/(1 - q x(1+x)) - 2 y x/(1 - y x(1+2x)), q = 2y + y^2, as polynomials in y per power of x
def padd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): out[i + j] += x * y
    return out
def series(num, d1, d2, W):       # coefficients c_w with c_w = num*[w==1] + d1*c_{w-1} + d2*c_{w-2}
    c = {0: [0]}
    for w in range(1, W + 1):
        t = pmul(d1, c[w - 1]) if w >= 1 else [0]
        if w >= 2: t = padd(t, pmul(d2, c[w - 2]))
        if w == 1: t = padd(t, num)
        c[w] = t
    return c
q = [0, 2, 1]; y = [0, 1]
A = series(q, q, q, 9)                         # q x / (1 - q x - q x^2)
B = series([0, 2], y, [0, 2], 9)               # 2 y x / (1 - y x - 2 y x^2)
gf_ok = True
for w in range(1, 10):
    f = padd(A[w], [-v for v in B[w]]); f = f + [0] * (2 * w + 1 - len(f))
    if [int(v) for v in f[:2 * w + 1]] != P[w] or any(f[2 * w + 1:]): gf_ok = False
check("generating function matches the brute-force count by size, widths 1..9", gf_ok, f"e.g. width 4: {P[4]}")

# ---- Conjecture 3: odd squares
schroeder = [1, 2, 6, 22, 90, 394, 1806, 8558]
for k in range(1, 4):                          # full brute force, 3x3, 5x5, 7x7
    n = 2 * k + 1
    below = count_min(n, n, k) if k >= 1 else 0
    closure, full, idx = make(n, n)
    good = []; 
    for combo in itertools.combinations(range(n * n), k + 1):
        s = 0
        for x in combo: s |= 1 << x
        if closure(s) == full: good.append(combo)
    odd = all(sorted(x // n for x in c) == list(range(0, n, 2)) and sorted(x % n for x in c) == list(range(0, n, 2)) for c in good)
    check(f"{n} x {n}: none of size {k}; {len(good)} of size {k+1}; all have one seed per odd row and odd column", below == 0 and len(good) == schroeder[k] and odd, f"(Schroeder {schroeder[k]})")

def avoids(p, pat):
    m = len(pat)
    for sub in itertools.combinations(range(len(p)), m):
        vals = [p[i] for i in sub]; order = sorted(range(m), key=lambda i: vals[i])
        rank = [0] * m
        for r_, i in enumerate(order): rank[i] = r_ + 1
        if tuple(rank) == pat: return False
    return True
tested = 0; sep_ok = True; counts = []
for n in range(1, 9):
    N = 2 * n - 1
    closure, full, idx = make(N, N)
    cnt = 0
    for p in itertools.permutations(range(1, n + 1)):
        s = 0
        for j in range(n): s |= 1 << idx(2 * (p[j] - 1), 2 * j)
        perc = closure(s) == full
        tested += 1; cnt += perc
        if n <= 7 and perc != (avoids(p, (2, 4, 1, 3)) and avoids(p, (3, 1, 4, 2))): sep_ok = False
    counts.append(cnt)
check(f"permutation seeds on (2n-1)^2, n = 1..8 ({tested} configurations): counts {counts}", counts == schroeder)
check("percolates exactly when the permutation avoids 2413 and 3142 (n = 1..7)", sep_ok)
print("\nALL CHECKS PASSED" if ok else "\nSOME CHECKS FAILED")
