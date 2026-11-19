import PowerContamination.Defs

/-!
# Obstructions and the two-row grid

* A sealed set of seed-free columns (or rows) can never be entered.
* On two rows, a set percolates exactly when its first and last columns are occupied,
  no two consecutive columns are empty, and some column is full or two adjacent
  columns carry seeds in different rows.
-/

namespace PowerContamination

/-- A set `J` of seed-free columns, each of which has a neighbouring column that is in `J`
or outside the grid, is never entered. -/
theorem not_percolates_of_blocked_cols {h w : ℕ} {S : Set Cell} (hS : S ⊆ grid h w)
    (J : Set ℤ)
    (hJ : ∀ j ∈ J, (j - 1 ∈ J ∨ j - 1 < 0) ∨ (j + 1 ∈ J ∨ (w : ℤ) ≤ j + 1))
    (hSJ : ∀ c ∈ S, c.2 ∉ J) {c0 : Cell} (hc0 : c0 ∈ grid h w) (hc0J : c0.2 ∈ J) :
    ¬ Percolates h w S := by
  intro hP
  rw [percolates_iff] at hP
  have hT : Closed h w {c | c ∈ grid h w ∧ c.2 ∉ J} := by
    rw [closed_iff]
    intro i j hg
    have hJj := hJ j
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h1 h2 <;>
      refine ⟨hg, fun hj => ?_⟩ <;>
      rcases hJj hj with (h3 | h3) | (h3 | h3) <;>
      first
        | exact h1.2 hj | exact h2.2 hj | exact h1.2 h3 | exact h2.2 h3
        | (have g1 := h1.1; have g2 := h2.1; simp only [mem_grid] at g1 g2; omega)
  exact (hP {c | c ∈ grid h w ∧ c.2 ∉ J} (fun c hc => ⟨hS hc, hSJ c hc⟩) hT hc0).2 hc0J

/-- The same statement for rows. -/
theorem not_percolates_of_blocked_rows {h w : ℕ} {S : Set Cell} (hS : S ⊆ grid h w)
    (J : Set ℤ)
    (hJ : ∀ i ∈ J, (i - 1 ∈ J ∨ i - 1 < 0) ∨ (i + 1 ∈ J ∨ (h : ℤ) ≤ i + 1))
    (hSJ : ∀ c ∈ S, c.1 ∉ J) {c0 : Cell} (hc0 : c0 ∈ grid h w) (hc0J : c0.1 ∈ J) :
    ¬ Percolates h w S := by
  intro hP
  rw [percolates_iff] at hP
  have hT : Closed h w {c | c ∈ grid h w ∧ c.1 ∉ J} := by
    rw [closed_iff]
    intro i j hg
    have hJi := hJ i
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h1 h2 <;>
      refine ⟨hg, fun hi => ?_⟩ <;>
      rcases hJi hi with (h3 | h3) | (h3 | h3) <;>
      first
        | exact h1.2 hi | exact h2.2 hi | exact h1.2 h3 | exact h2.2 h3
        | (have g1 := h1.1; have g2 := h2.1; simp only [mem_grid] at g1 g2; omega)
  exact (hP {c | c ∈ grid h w ∧ c.1 ∉ J} (fun c hc => ⟨hS hc, hSJ c hc⟩) hT hc0).2 hc0J

/-! ### Two rows -/

/-- Two rows, necessity of a witness: without a full column and without two adjacent
columns seeded in different rows, the closure has at most one cell per column. -/
theorem not_percolates_two_of_no_witness {w : ℕ} {S : Set Cell} (hS : S ⊆ grid 2 w) (hw : 0 < w)
    (hD : ∀ j : ℤ, ¬((0, j) ∈ S ∧ (1, j) ∈ S))
    (hAB : ∀ j j' : ℤ, j' = j + 1 → ¬((0, j) ∈ S ∧ (1, j') ∈ S))
    (hBA : ∀ j j' : ℤ, j' = j + 1 → ¬((1, j) ∈ S ∧ (0, j') ∈ S)) :
    ¬ Percolates 2 w S := by
  intro hP
  rw [percolates_iff] at hP
  let T : Set Cell := {c | c ∈ grid 2 w ∧
    (c ∈ S ∨ ∃ jl jr : ℤ, jl = c.2 - 1 ∧ jr = c.2 + 1 ∧ (c.1, jl) ∈ S ∧ (c.1, jr) ∈ S)}
  have mem_T : ∀ i j : ℤ, (i, j) ∈ T ↔ ((0 ≤ i ∧ i < (2 : ℕ) ∧ 0 ≤ j ∧ j < w) ∧
      ((i, j) ∈ S ∨ ∃ jl jr : ℤ, jl = j - 1 ∧ jr = j + 1 ∧ (i, jl) ∈ S ∧ (i, jr) ∈ S)) :=
    fun i j => Iff.rfl
  have F1 : ∀ j : ℤ, ¬((0, j) ∈ T ∧ (1, j) ∈ T) := by
    intro j hh
    rw [mem_T, mem_T] at hh
    obtain ⟨⟨-, a | ⟨al, ar, e1, e2, a, a'⟩⟩, ⟨-, b | ⟨bl, br, e3, e4, b, b'⟩⟩⟩ := hh
    · exact hD j ⟨a, b⟩
    · exact hBA bl j (by omega) ⟨b, a⟩
    · exact hAB al j (by omega) ⟨a, b⟩
    · obtain rfl : al = bl := by omega
      exact hD al ⟨a, b⟩
  have F2 : ∀ j j' : ℤ, j' = j + 1 → ¬((0, j) ∈ T ∧ (1, j') ∈ T) := by
    intro j j' hj hh
    rw [mem_T, mem_T] at hh
    obtain ⟨⟨-, a | ⟨al, ar, e1, e2, a, a'⟩⟩, ⟨-, b | ⟨bl, br, e3, e4, b, b'⟩⟩⟩ := hh
    · exact hAB j j' hj ⟨a, b⟩
    · obtain rfl : bl = j := by omega
      exact hD bl ⟨a, b⟩
    · obtain rfl : ar = j' := by omega
      exact hD ar ⟨a', b⟩
    · exact hBA bl ar (by omega) ⟨b, a'⟩
  have F2' : ∀ j j' : ℤ, j' = j + 1 → ¬((1, j) ∈ T ∧ (0, j') ∈ T) := by
    intro j j' hj hh
    rw [mem_T, mem_T] at hh
    obtain ⟨⟨-, a | ⟨al, ar, e1, e2, a, a'⟩⟩, ⟨-, b | ⟨bl, br, e3, e4, b, b'⟩⟩⟩ := hh
    · exact hBA j j' hj ⟨a, b⟩
    · obtain rfl : bl = j := by omega
      exact hD bl ⟨b, a⟩
    · obtain rfl : ar = j' := by omega
      exact hD ar ⟨b, a'⟩
    · exact hAB bl ar (by omega) ⟨b, a'⟩
  have F3 : ∀ i j : ℤ, (0 ≤ i ∧ i < (2 : ℕ) ∧ 0 ≤ j ∧ j < w) →
      (i, j - 1) ∈ T → (i, j + 1) ∈ T → (i, j) ∈ T := by
    intro i j hg h1 h2
    rw [mem_T] at h1 h2 ⊢
    refine ⟨hg, ?_⟩
    obtain ⟨-, a | ⟨al, ar, e1, e2, a, a'⟩⟩ := h1
    · obtain ⟨-, b | ⟨bl, br, e3, e4, b, b'⟩⟩ := h2
      · exact Or.inr ⟨j - 1, j + 1, rfl, rfl, a, b⟩
      · obtain rfl : bl = j := by omega
        exact Or.inl b
    · obtain rfl : ar = j := by omega
      exact Or.inl a'
  have notT : ∀ i j : ℤ, (i < 0 ∨ 2 ≤ i) → (i, j) ∉ T := by
    intro i j hi hh
    rw [mem_T] at hh
    omega
  have hT : Closed 2 w T := by
    rw [closed_iff]
    intro i j hg
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h1 h2
      · exact absurd h1 (notT _ _ (by omega))
      · exact F3 0 j hg h1 h2
      · exact absurd h1 (notT _ _ (by omega))
      · exact absurd h1 (notT _ _ (by omega))
      · exact absurd ⟨h2, h1⟩ (F2 (j - 1) j (by omega))
      · exact absurd ⟨h1, h2⟩ (F2' j (j + 1) rfl)
      · exact absurd h1 (notT _ _ (by omega))
      · exact absurd h1 (notT _ _ (by omega))
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h1 h2
      · exact absurd h2 (notT _ _ (by omega))
      · exact F3 1 j hg h1 h2
      · exact absurd ⟨h2, h1⟩ (F2' (j - 1) j (by omega))
      · exact absurd ⟨h1, h2⟩ (F2 j (j + 1) rfl)
      · exact absurd h1 (notT _ _ (by omega))
      · exact absurd h1 (notT _ _ (by omega))
      · exact absurd h2 (notT _ _ (by omega))
      · exact absurd h2 (notT _ _ (by omega))
  have hST : S ⊆ T := fun c hc => ⟨hS hc, Or.inl hc⟩
  exact F1 0 ⟨hP T hST hT (by rw [mem_grid]; omega), hP T hST hT (by rw [mem_grid]; omega)⟩

/-- Two rows, sufficiency. -/
theorem percolates_two_of_witness {w : ℕ} {S : Set Cell} (hS : S ⊆ grid 2 w)
    (hfirst : (0, 0) ∈ S ∨ (1, 0) ∈ S)
    (hlast : (0, (w : ℤ) - 1) ∈ S ∨ (1, (w : ℤ) - 1) ∈ S)
    (hgap : ∀ j j' : ℤ, 0 ≤ j → j' = j + 1 → j' < w →
      ((0, j) ∈ S ∨ (1, j) ∈ S) ∨ ((0, j') ∈ S ∨ (1, j') ∈ S))
    (hwit : ∃ j j' : ℤ, j' = j + 1 ∧ (((0, j') ∈ S ∧ (1, j') ∈ S) ∨
      ((0, j) ∈ S ∧ (1, j') ∈ S) ∨ ((1, j) ∈ S ∧ (0, j') ∈ S))) :
    Percolates 2 w S := by
  rw [percolates_iff]
  intro T hST hT
  have stepR : ∀ j : ℤ, 0 ≤ j → j + 1 < w → (0, j) ∈ T → (1, j) ∈ T →
      ((0, j + 1) ∈ T ∨ (1, j + 1) ∈ T) → (0, j + 1) ∈ T ∧ (1, j + 1) ∈ T := by
    rintro j hj hj' a b (c | c)
    · exact ⟨c, hT.orth (by omega) c b (by omega) (by omega) (by omega)⟩
    · exact ⟨hT.orth (by omega) c a (by omega) (by omega) (by omega), c⟩
  have stepL : ∀ j : ℤ, 0 ≤ j - 1 → j < w → (0, j) ∈ T → (1, j) ∈ T →
      ((0, j - 1) ∈ T ∨ (1, j - 1) ∈ T) → (0, j - 1) ∈ T ∧ (1, j - 1) ∈ T := by
    rintro j hj hj' a b (c | c)
    · exact ⟨c, hT.orth (by omega) c b (by omega) (by omega) (by omega)⟩
    · exact ⟨hT.orth (by omega) c a (by omega) (by omega) (by omega), c⟩
  have fullR : ∀ (m : ℕ) (j : ℤ), 0 ≤ j → j + m < w → (0, j) ∈ T → (1, j) ∈ T →
      (0, j + m) ∈ T ∧ (1, j + m) ∈ T := by
    intro m
    induction m with
    | zero => intro j _ _ a b; simpa using ⟨a, b⟩
    | succ m ih =>
      intro j hj hjm a b
      push_cast at hjm
      obtain ⟨a', b'⟩ := ih j hj (by omega) a b
      have key : (0, j + m + 1) ∈ T ∧ (1, j + m + 1) ∈ T := by
        by_cases hocc : (0, j + m + 1) ∈ S ∨ (1, j + m + 1) ∈ S
        · exact stepR (j + m) (by omega) (by omega) a' b' (hocc.imp (fun x => hST x) (fun x => hST x))
        · have hnl : j + m + 1 ≠ w - 1 := by
            intro e
            rw [e] at hocc
            exact hocc hlast
          rcases hgap (j + m + 1) (j + m + 2) (by omega) (by ring) (by omega) with h2 | h2
          · exact absurd h2 hocc
          · apply stepR (j + m) (by omega) (by omega) a' b'
            rcases h2 with h2 | h2
            · exact Or.inl (hT.orth (by omega) a' (hST h2) (by omega) (by omega) (by omega))
            · exact Or.inr (hT.orth (by omega) b' (hST h2) (by omega) (by omega) (by omega))
      have e : j + ((m + 1 : ℕ) : ℤ) = j + m + 1 := by push_cast; ring
      rw [e]
      exact key
  have fullL : ∀ (m : ℕ) (j : ℤ), j < w → 0 ≤ j - m → (0, j) ∈ T → (1, j) ∈ T →
      (0, j - m) ∈ T ∧ (1, j - m) ∈ T := by
    intro m
    induction m with
    | zero => intro j _ _ a b; simpa using ⟨a, b⟩
    | succ m ih =>
      intro j hj hjm a b
      push_cast at hjm
      obtain ⟨a', b'⟩ := ih j hj (by omega) a b
      have key : (0, j - m - 1) ∈ T ∧ (1, j - m - 1) ∈ T := by
        by_cases hocc : (0, j - m - 1) ∈ S ∨ (1, j - m - 1) ∈ S
        · exact stepL (j - m) (by omega) (by omega) a' b' (hocc.imp (fun x => hST x) (fun x => hST x))
        · have hnl : j - m - 1 ≠ 0 := by
            intro e
            rw [e] at hocc
            exact hocc hfirst
          rcases hgap (j - m - 2) (j - m - 1) (by omega) (by ring) (by omega) with h2 | h2
          · apply stepL (j - m) (by omega) (by omega) a' b'
            rcases h2 with h2 | h2
            · exact Or.inl (hT.orth (by omega) a' (hST h2) (by omega) (by omega) (by omega))
            · exact Or.inr (hT.orth (by omega) b' (hST h2) (by omega) (by omega) (by omega))
          · exact absurd h2 hocc
      have e : j - ((m + 1 : ℕ) : ℤ) = j - m - 1 := by push_cast; ring
      rw [e]
      exact key
  obtain ⟨j0, j1, hj1, hwit⟩ := hwit
  have hfull : (0 ≤ j1 ∧ j1 < w) ∧ (0, j1) ∈ T ∧ (1, j1) ∈ T := by
    rcases hwit with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · have g := hS a
      rw [mem_grid] at g
      exact ⟨by omega, hST a, hST b⟩
    · have g := hS b
      rw [mem_grid] at g
      exact ⟨by omega, hT.orth (by omega) (hST a) (hST b) (by omega) (by omega) (by omega), hST b⟩
    · have g := hS b
      rw [mem_grid] at g
      exact ⟨by omega, hST b, hT.orth (by omega) (hST a) (hST b) (by omega) (by omega) (by omega)⟩
  obtain ⟨hb, f0, f1⟩ := hfull
  rintro ⟨i, j⟩ hg
  rw [mem_grid] at hg
  rcases le_total j1 j with hle | hle
  · have e := Int.toNat_of_nonneg (show 0 ≤ j - j1 by omega)
    have := fullR (j - j1).toNat j1 hb.1 (by omega) f0 f1
    have e' : j1 + ((j - j1).toNat : ℤ) = j := by omega
    rw [e'] at this
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    exacts [this.1, this.2]
  · have e := Int.toNat_of_nonneg (show 0 ≤ j1 - j by omega)
    have := fullL (j1 - j).toNat j1 hb.2 (by omega) f0 f1
    have e' : j1 - ((j1 - j).toNat : ℤ) = j := by omega
    rw [e'] at this
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    exacts [this.1, this.2]

end PowerContamination
