import PowerContamination.TwoRowCount

/-!
# Conjecture 2 of Mehiri and Nadji: `α(2, 2k+1) = (k+1)(3k+2)2^(k-1)`
-/

namespace PowerContamination

open Finset

/-- **Conjecture 2** of arXiv:2509.12756v3. For every `k ≥ 1`, the number of percolating sets
of minimum size on the `2 × (2k+1)` grid is `(k+1)(3k+2)2^(k-1)`. -/
theorem alpha_two_odd (k : ℕ) (hk : 1 ≤ k) :
    alpha 2 (2 * k + 1) = (k + 1) * (3 * k + 2) * 2 ^ (k - 1) := by
  have hw : 0 < 2 * k + 1 := by omega
  have hperc : ∀ S : Finset Cell, (↑S : Set Cell) ⊆ grid 2 (2 * k + 1) →
      (Percolates 2 (2 * k + 1) (↑S : Set Cell) ↔ good (enc S (2 * k + 1)) = true) :=
    fun S hS => percolates_two_iff_good hw S hS
  have hF : ∀ (S : Finset Cell) (m : ℕ), (↑S : Set Cell) ⊆ grid 2 (2 * k + 1) →
      (F Sym.O false m (enc S (2 * k + 1)) = true ↔
        S.card = m ∧ Percolates 2 (2 * k + 1) (↑S : Set Cell)) := by
    intro S m hS
    rw [hperc S hS, card_eq_weight hS]
    show (decide (weight (enc S (2 * k + 1)) = m) && acc Sym.O false (enc S (2 * k + 1))) = true ↔ _
    rw [Bool.and_eq_true, decide_eq_true_eq]
    rfl
  -- every percolating set has at least `k + 2` seeds
  have hlow : ∀ S : Finset Cell, (↑S : Set Cell) ⊆ grid 2 (2 * k + 1) →
      Percolates 2 (2 * k + 1) (↑S : Set Cell) → k + 2 ≤ S.card := by
    intro S hS hP
    by_contra hlt
    have hpos := cnt_pos (p := F Sym.O false S.card) (l := enc S (2 * k + 1))
      ((hF S S.card hS).2 ⟨rfl, hP⟩)
    rw [enc_length] at hpos
    have hz : cnt (F Sym.O false S.card) (2 * k + 1) = 0 := U0_low k S.card (by omega)
    omega
  have hval : cnt (F Sym.O false (k + 2)) (2 * k + 1) = (k + 1) * (3 * k + 2) * 2 ^ (k - 1) :=
    U0_main k hk
  -- a percolating set with exactly `k + 2` seeds exists
  have hex : ∃ S0 : Finset Cell, (↑S0 : Set Cell) ⊆ grid 2 (2 * k + 1) ∧
      Percolates 2 (2 * k + 1) (↑S0 : Set Cell) ∧ S0.card = k + 2 := by
    have hpos : 0 < cnt (F Sym.O false (k + 2)) (2 * k + 1) := by
      rw [hval]
      positivity
    obtain ⟨l, hlen, hl⟩ := exists_of_cnt_pos hpos
    have hsub : (↑(decSet l) : Set Cell) ⊆ grid 2 (2 * k + 1) := by
      have := decSet_subset l
      rwa [hlen] at this
    have henc : enc (decSet l) (2 * k + 1) = l := by
      have := enc_decSet l
      rwa [hlen] at this
    have := (hF (decSet l) (k + 2) hsub).1 (by rw [henc]; exact hl)
    exact ⟨decSet l, hsub, this.2, this.1⟩
  have hmin : ∀ S : Finset Cell,
      S ∈ ((box (2 * k + 1)).powerset.filter
        (fun S => F Sym.O false (k + 2) (enc S (2 * k + 1)) = true)) ↔
      IsMinPercolating 2 (2 * k + 1) S := by
    intro S
    rw [mem_filter, ← subset_grid_iff]
    constructor
    · rintro ⟨hS, hFS⟩
      obtain ⟨hc, hP⟩ := (hF S (k + 2) hS).1 hFS
      exact ⟨hS, hP, fun S' hS' hP' => hc ▸ hlow S' hS' hP'⟩
    · rintro ⟨hS, hP, hm⟩
      obtain ⟨S0, h0, hP0, hc0⟩ := hex
      have hc : S.card = k + 2 := le_antisymm (hc0 ▸ hm S0 h0 hP0) (hlow S hS hP)
      exact ⟨hS, (hF S (k + 2) hS).2 ⟨hc, hP⟩⟩
  unfold alpha
  rw [Nat.subtype_card _ hmin, card_sets_eq_cnt]
  exact hval

end PowerContamination
