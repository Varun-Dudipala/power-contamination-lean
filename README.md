# Power contamination on grids: two conjectures, proved in Lean 4

Formal proofs of Conjectures 2 and 3 of E.-M. Mehiri and M. L. Nadji,
*The Power Contamination Problem on Grids Revisited: Optimality, Combinatorics,
and Links to Integer Sequences*, arXiv:2509.12756v3 (9 April 2026).

```lean
theorem alpha_two_odd (k : ℕ) (hk : 1 ≤ k) :
    alpha 2 (2 * k + 1) = (k + 1) * (3 * k + 2) * 2 ^ (k - 1)

theorem alpha_odd_square (k : ℕ) (hk : 1 ≤ k) :
    alpha (2 * k + 1) (2 * k + 1) = Nat.largeSchroder k
```

`alpha h w` is the number of percolating sets of minimum size on the `h × w` grid.
`Nat.largeSchroder` is Mathlib's definition of the large Schröder numbers (OEIS A006318).

## What has to be trusted

Only the definitions at the top of `PowerContamination/Defs.lean` (about 35 lines):

| Name | Meaning |
|---|---|
| `Cell` | a pair (row, column) of integers |
| `grid h w` | rows `0..h-1`, columns `0..w-1` |
| `rules` | the eight infecting pairs of offsets: the six pairs of orthogonal neighbours and the two opposite diagonal pairs |
| `Infected h w S c` | `c` is a seed, or `c` is in the grid and both cells of some rule pair are infected |
| `Percolates h w S` | every cell of the grid is infected |
| `IsMinPercolating h w S` | `S` is a set of grid cells, percolates, and no percolating set of grid cells is smaller |
| `alpha h w` | the number of such `S` |

Everything else is checked by Lean.

## How to check

Lean 4.33.1 and Mathlib at commit `0df444a360eaa60ab8c11dca51a86af692955474`, both pinned
in this repository. The same two commands run on every push (see the Build workflow).

```bash
lake exe cache get
```

```bash
lake build PowerContamination
```

```bash
lake env lean check/Axioms.lean
```

The second command prints the axioms behind each theorem. The expected output is
`[propext, Classical.choice, Quot.sound]` three times and no errors. It also re-states both
conjectures directly against the definitions and checks the small values
`alpha 2 3 = 10`, `alpha 2 5 = 48`, `alpha 2 7 = 176`, `alpha 3 3 = 2`, `alpha 5 5 = 6`,
`alpha 7 7 = 22`, which agree with exhaustive search.

No file uses `sorry`, `native_decide`, an added axiom, or `set_option`.

## Outline of the proofs

### Two rows (`alpha_two_odd`)

| File | Content |
|---|---|
| `Obstructions.lean` | A sealed set of seed-free columns (or rows) is never entered. On two rows a set percolates iff the first and last columns are occupied, no two consecutive columns are empty, and some column is full or two adjacent columns carry seeds in different rows. |
| `Words.lean` | A two-row set is a word over `O, A, B, D` (empty, top, bottom, both). Percolation is acceptance by a small automaton (`percolates_two_iff_good`). |
| `Encode.lean` | Sets on `2 × w` are in bijection with words of length `w`; seeds correspond to weight. |
| `TwoRowCount.lean` | The number of accepted words by length and weight satisfies a recurrence over four automaton states. Its values near the diagonal are computed in closed form. |
| `TwoRow.lean` | The minimum is `k + 2` seeds and the count is `(k+1)(3k+2)2^(k-1)`. |

### Odd squares (`alpha_odd_square`)

| File | Content |
|---|---|
| `SepList.lean` | `SepL l a`: the list `l` is a separable arrangement of the values `a, …, a+|l|-1` (built by direct and skew sums of blocks with adjacent value ranges). |
| `SquareFill.lean` | Two full rectangles touching diagonally across a one-cell gap fill their bounding rectangle. Hence separable seeds percolate. |
| `SquareClosed.lean` | Conversely, cut the positions into as few separable blocks as possible. With more than one block the union of the block rectangles is closed and misses a column. Hence percolating permutation seeds are separable. |
| `SquareMin.lean` | On `(2n-1) × (2n-1)` every percolating set has at least `n` cells, and one with exactly `n` cells has one seed in each even row and each even column. |
| `SchroderCount.lean` | Separable arrangements of `k+1` values are counted by `Nat.largeSchroder k`: each of length at least two is a direct sum or a skew sum but not both, complement exchanges the two kinds, and a direct sum splits uniquely at its first summand. |
| `Square.lean` | Minimum sets are exactly the seed sets of separable arrangements, so their number is `R_k`. |

The seed of value `v` at position `t` is the cell `(2v, 2t)` (rows and columns are
numbered from 0, so "odd" rows and columns of the paper are the even indices here).

## Scope

- The second theorem is also proved for `k = 0` (`alpha_odd_square'`).
- The bivariate generating function for all percolating two-row sets, stated in the
  prose draft, is not formalised. Only what the two conjectures need is.
- These are formal proofs of the two statements as defined above. Whether the
  definitions match the paper's model is a matter of reading `Defs.lean` against
  Section 2.1 of the paper; the small values above agree with an exhaustive search
  written separately in Python (`check/brute_force.py`).
- Priority has not been established: a web search on 19 November 2026 found no other
  proof of either conjecture, but MathSciNet and zbMATH were not searched. The enumeration
  of separable permutations by Schröder numbers is classical (Shapiro and Stephens, 1991),
  and it is re-proved here from scratch.

## Credits

The mathematical argument formalised here follows a research draft prepared with OpenAI
Codex. The Lean formalisation was written by Claude (Anthropic).
