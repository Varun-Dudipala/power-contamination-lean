import PowerContamination

open PowerContamination

#check alpha_two_odd
#check alpha_odd_square

#print axioms alpha_two_odd
#print axioms alpha_odd_square
#print axioms alpha_odd_square'

-- the statements exactly as conjectured, restated from scratch against the definitions
example : ∀ k : ℕ, 1 ≤ k →
    Nat.card {S : Finset (ℤ × ℤ) // IsMinPercolating 2 (2 * k + 1) S} =
      (k + 1) * (3 * k + 2) * 2 ^ (k - 1) := alpha_two_odd

example : ∀ k : ℕ, 1 ≤ k →
    Nat.card {S : Finset (ℤ × ℤ) // IsMinPercolating (2 * k + 1) (2 * k + 1) S} =
      Nat.largeSchroder k := alpha_odd_square

-- small instances, to compare with brute force (10, 48, 176; 2, 6, 22, 90)
example : alpha 2 3 = 10 := by have := alpha_two_odd 1 (by norm_num); simpa using this
example : alpha 2 5 = 48 := by have := alpha_two_odd 2 (by norm_num); simpa using this
example : alpha 2 7 = 176 := by have := alpha_two_odd 3 (by norm_num); simpa using this
example : alpha 1 1 = 1 := by have := alpha_odd_square' 0; simpa using this
example : alpha 3 3 = 2 := by have := alpha_odd_square' 1; simpa using this
example : alpha 5 5 = 6 := by have := alpha_odd_square' 2; simpa using this
example : alpha 7 7 = 22 := by
  have := alpha_odd_square' 3
  simpa [Nat.largeSchroder_succ, Finset.sum_range_succ, ← Finset.range_eq_Ico, Finset.Iic_eq_Icc,
    Finset.sum_Icc_succ_top] using this
