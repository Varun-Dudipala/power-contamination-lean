import Mathlib

/-!
# Power contamination on grids: definitions

The model of E.-M. Mehiri and M. L. Nadji, *The Power Contamination Problem on Grids
Revisited* (arXiv:2509.12756v3), rules (a)-(h): a cell of the `h × w` grid becomes
infected when two of its four orthogonal neighbours are infected, or when both members
of one of its two opposite diagonal pairs are infected.

Everything a reader has to trust is in the first part of this file: `Cell`, `grid`,
`rules`, `Infected`, `Percolates`, `IsMinPercolating` and `alpha`.
-/

namespace PowerContamination

/-- A cell is a pair (row, column) of integers. -/
abbrev Cell := ℤ × ℤ

/-- The `h × w` grid: rows `0, …, h-1` and columns `0, …, w-1`. -/
def grid (h w : ℕ) : Set Cell := {c | 0 ≤ c.1 ∧ c.1 < h ∧ 0 ≤ c.2 ∧ c.2 < w}

/-- The eight infecting pairs of relative offsets: the six pairs of orthogonal
neighbours and the two pairs of opposite diagonal neighbours. -/
def rules : List (Cell × Cell) :=
  [((-1, 0), (1, 0)), ((0, -1), (0, 1)),
   ((-1, 0), (0, -1)), ((-1, 0), (0, 1)), ((1, 0), (0, -1)), ((1, 0), (0, 1)),
   ((-1, -1), (1, 1)), ((-1, 1), (1, -1))]

/-- The cells that are eventually infected when the process starts from `S`. -/
inductive Infected (h w : ℕ) (S : Set Cell) : Cell → Prop
  | seed {c : Cell} : c ∈ S → Infected h w S c
  | step {c : Cell} (r : Cell × Cell) : c ∈ grid h w → r ∈ rules →
      Infected h w S (c + r.1) → Infected h w S (c + r.2) → Infected h w S c

/-- `S` percolates if every cell of the grid is eventually infected. -/
def Percolates (h w : ℕ) (S : Set Cell) : Prop := ∀ c ∈ grid h w, Infected h w S c

/-- A percolating set of cells of the grid with the least possible number of cells. -/
def IsMinPercolating (h w : ℕ) (S : Finset Cell) : Prop :=
  (↑S : Set Cell) ⊆ grid h w ∧ Percolates h w ↑S ∧
    ∀ S' : Finset Cell, (↑S' : Set Cell) ⊆ grid h w → Percolates h w ↑S' → S.card ≤ S'.card

/-- `alpha h w`: the number of percolating sets of minimum size on the `h × w` grid. -/
noncomputable def alpha (h w : ℕ) : ℕ := Nat.card {S : Finset Cell // IsMinPercolating h w S}

/-! ### Working form: closed sets -/

/-- A set that no rule can enlarge. -/
def Closed (h w : ℕ) (T : Set Cell) : Prop :=
  ∀ c ∈ grid h w, ∀ r ∈ rules, c + r.1 ∈ T → c + r.2 ∈ T → c ∈ T

theorem mem_grid {h w : ℕ} {i j : ℤ} :
    (i, j) ∈ grid h w ↔ 0 ≤ i ∧ i < h ∧ 0 ≤ j ∧ j < w := Iff.rfl

theorem Infected.mem_of_closed {h w : ℕ} {S T : Set Cell} (hST : S ⊆ T) (hT : Closed h w T)
    {c : Cell} (hc : Infected h w S c) : c ∈ T := by
  induction hc with
  | seed hc => exact hST hc
  | step r hg hr _ _ ih1 ih2 => exact hT _ hg r hr ih1 ih2

theorem percolates_iff {h w : ℕ} {S : Set Cell} :
    Percolates h w S ↔ ∀ T : Set Cell, S ⊆ T → Closed h w T → grid h w ⊆ T := by
  constructor
  · intro hP T hST hT c hc
    exact (hP c hc).mem_of_closed hST hT
  · intro H c hc
    exact H {c | Infected h w S c} (fun c hc => Infected.seed hc)
      (fun c hg r hr h1 h2 => Infected.step r hg hr h1 h2) hc

theorem closed_iff {h w : ℕ} {T : Set Cell} : Closed h w T ↔
    ∀ i j : ℤ, (0 ≤ i ∧ i < h ∧ 0 ≤ j ∧ j < w) →
      (((i - 1, j) ∈ T → (i + 1, j) ∈ T → (i, j) ∈ T) ∧
       ((i, j - 1) ∈ T → (i, j + 1) ∈ T → (i, j) ∈ T) ∧
       ((i - 1, j) ∈ T → (i, j - 1) ∈ T → (i, j) ∈ T) ∧
       ((i - 1, j) ∈ T → (i, j + 1) ∈ T → (i, j) ∈ T) ∧
       ((i + 1, j) ∈ T → (i, j - 1) ∈ T → (i, j) ∈ T) ∧
       ((i + 1, j) ∈ T → (i, j + 1) ∈ T → (i, j) ∈ T) ∧
       ((i - 1, j - 1) ∈ T → (i + 1, j + 1) ∈ T → (i, j) ∈ T) ∧
       ((i - 1, j + 1) ∈ T → (i + 1, j - 1) ∈ T → (i, j) ∈ T)) := by
  constructor
  · intro hT i j hg
    have H := hT (i, j) hg
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [← sub_eq_add_neg] using H ((-1, 0), (1, 0)) (by simp [rules])
    · simpa [← sub_eq_add_neg] using H ((0, -1), (0, 1)) (by simp [rules])
    · simpa [← sub_eq_add_neg] using H ((-1, 0), (0, -1)) (by simp [rules])
    · simpa [← sub_eq_add_neg] using H ((-1, 0), (0, 1)) (by simp [rules])
    · simpa [← sub_eq_add_neg] using H ((1, 0), (0, -1)) (by simp [rules])
    · simpa [← sub_eq_add_neg] using H ((1, 0), (0, 1)) (by simp [rules])
    · simpa [← sub_eq_add_neg] using H ((-1, -1), (1, 1)) (by simp [rules])
    · simpa [← sub_eq_add_neg] using H ((-1, 1), (1, -1)) (by simp [rules])
  · rintro H ⟨i, j⟩ hg r hr
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := H i j hg
    simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Prod.mk_add_mk, add_zero, ← sub_eq_add_neg]
    exacts [a1, a2, a3, a4, a5, a6, a7, a8]

/-- Orthogonal rule in a form whose side conditions are linear arithmetic. -/
theorem Closed.orth {h w : ℕ} {T : Set Cell} (hT : Closed h w T) {i j i1 j1 i2 j2 : ℤ}
    (hg : 0 ≤ i ∧ i < h ∧ 0 ≤ j ∧ j < w) (h1 : (i1, j1) ∈ T) (h2 : (i2, j2) ∈ T)
    (hn1 : (i1 = i - 1 ∧ j1 = j) ∨ (i1 = i + 1 ∧ j1 = j) ∨ (i1 = i ∧ j1 = j - 1) ∨
      (i1 = i ∧ j1 = j + 1))
    (hn2 : (i2 = i - 1 ∧ j2 = j) ∨ (i2 = i + 1 ∧ j2 = j) ∨ (i2 = i ∧ j2 = j - 1) ∨
      (i2 = i ∧ j2 = j + 1))
    (hne : i1 ≠ i2 ∨ j1 ≠ j2) : (i, j) ∈ T := by
  obtain ⟨a1, a2, a3, a4, a5, a6, -, -⟩ := closed_iff.1 hT i j hg
  rcases hn1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hn2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first
      | omega
      | exact a1 h1 h2 | exact a1 h2 h1 | exact a2 h1 h2 | exact a2 h2 h1
      | exact a3 h1 h2 | exact a3 h2 h1 | exact a4 h1 h2 | exact a4 h2 h1
      | exact a5 h1 h2 | exact a5 h2 h1 | exact a6 h1 h2 | exact a6 h2 h1

/-- Diagonal rule in a form whose side conditions are linear arithmetic. -/
theorem Closed.diag {h w : ℕ} {T : Set Cell} (hT : Closed h w T) {i j i1 j1 i2 j2 : ℤ}
    (hg : 0 ≤ i ∧ i < h ∧ 0 ≤ j ∧ j < w) (h1 : (i1, j1) ∈ T) (h2 : (i2, j2) ∈ T)
    (hd : i1 = i - 1 ∧ i2 = i + 1 ∧ ((j1 = j - 1 ∧ j2 = j + 1) ∨ (j1 = j + 1 ∧ j2 = j - 1))) :
    (i, j) ∈ T := by
  obtain ⟨-, -, -, -, -, -, a7, a8⟩ := closed_iff.1 hT i j hg
  obtain ⟨rfl, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hd
  · exact a7 h1 h2
  · exact a8 h1 h2

end PowerContamination
