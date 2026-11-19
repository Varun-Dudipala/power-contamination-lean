import PowerContamination.SquareMin
import PowerContamination.SchroderCount

/-!
# Conjecture 3 of Mehiri and Nadji: `α(2k+1, 2k+1)` is the large Schröder number `R_k`
-/

namespace PowerContamination

open Finset

theorem seeds_subset_grid {l : List ℕ} {n : ℕ} (hs : SepL l 0) (hlen : l.length = n) :
    (↑(seeds l) : Set Cell) ⊆ grid (2 * n - 1) (2 * n - 1) := by
  intro c hc
  rw [mem_coe, mem_seeds] at hc
  obtain ⟨t, ht, rfl⟩ := hc
  have hx : l.getD t 0 ∈ l := by
    rw [List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  have := (hs.mem_iff _).1 hx
  rw [mem_grid]
  omega

/-- The minimum percolating sets of the `(2k+1) × (2k+1)` grid are exactly the seed sets of
the separable arrangements of `k+1` values. -/
theorem isMinPercolating_square_iff (k : ℕ) (S : Finset Cell) :
    S ∈ (sepSet (k + 1) 0).image seeds ↔
      IsMinPercolating (2 * (k + 1) - 1) (2 * (k + 1) - 1) S := by
  have hnpos : 0 < k + 1 := by omega
  rw [mem_image]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [mem_sepSet] at hl
    obtain ⟨hlen, hs⟩ := hl
    refine ⟨seeds_subset_grid hs hlen, percolates_seeds_of_sepL hs hlen, ?_⟩
    intro S' hS' hP'
    rw [card_seeds, hlen]
    exact (min_structure hnpos hS' hP').1
  · rintro ⟨hS, hP, hmin⟩
    obtain ⟨hlow, hstruct⟩ := min_structure hnpos hS hP
    have hid : SepL (List.range' 0 (k + 1)) 0 := SepL.range' (k + 1) 0 hnpos
    have hidlen : (List.range' 0 (k + 1)).length = k + 1 := by simp
    have hle := hmin _ (seeds_subset_grid hid hidlen) (percolates_seeds_of_sepL hid hidlen)
    rw [card_seeds, hidlen] at hle
    obtain ⟨l, hlen, hnd, rfl⟩ := hstruct (by omega)
    have hP' : Percolates (2 * l.length - 1) (2 * l.length - 1) (↑(seeds l) : Set Cell) := by
      rw [hlen]
      exact hP
    obtain ⟨a, hs⟩ := sepL_of_percolates (by omega) hnd hP'
    have ha : a = 0 := by
      have hmem : a + l.length - 1 ∈ l := (hs.mem_iff _).2 (by omega)
      obtain ⟨t, ht, hte⟩ := List.mem_iff_getElem.1 hmem
      have hc : (2 * ((l.getD t 0 : ℕ) : ℤ), 2 * (t : ℤ)) ∈ (↑(seeds l) : Set Cell) := by
        rw [mem_coe, mem_seeds]
        exact ⟨t, ht, rfl⟩
      have := hS hc
      rw [mem_grid, List.getD_eq_getElem _ _ ht, hte] at this
      omega
    subst ha
    exact ⟨l, mem_sepSet.2 ⟨hlen, hs⟩, rfl⟩

/-- For every `k`, the number of percolating sets of minimum size on the `(2k+1) × (2k+1)`
grid is the large Schröder number `R_k`. -/
theorem alpha_odd_square' (k : ℕ) : alpha (2 * k + 1) (2 * k + 1) = Nat.largeSchroder k := by
  have e : 2 * k + 1 = 2 * (k + 1) - 1 := by omega
  rw [e]
  unfold alpha
  rw [Nat.subtype_card _ (isMinPercolating_square_iff k), card_image_of_injOn, card_sepSet]
  intro l hl l' hl' he
  rw [mem_coe, mem_sepSet] at hl hl'
  exact seeds_inj (by rw [hl.1, hl'.1]) he

/-- **Conjecture 3** of arXiv:2509.12756v3, as stated there (for `k ≥ 1`). -/
theorem alpha_odd_square (k : ℕ) (_hk : 1 ≤ k) :
    alpha (2 * k + 1) (2 * k + 1) = Nat.largeSchroder k :=
  alpha_odd_square' k

end PowerContamination
