import PowerContamination.SepList

/-!
# Separable seeds fill the square

Two fully infected rectangles that touch diagonally across a one-cell gap infect their
bounding rectangle. By induction a separable arrangement infects its whole rectangle.
-/

namespace PowerContamination

theorem int_ind_up (P : ℤ → Prop) (m : ℤ) (h0 : P m) (hs : ∀ n, m ≤ n → P n → P (n + 1)) :
    ∀ n, m ≤ n → P n := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = m + k :=
    ⟨(n - m).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  clear hn
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have := hs (m + k) (by omega) ih
    rwa [show m + (k : ℤ) + 1 = m + ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this

theorem int_ind_down (P : ℤ → Prop) (m : ℤ) (h0 : P m) (hs : ∀ n, n ≤ m → P n → P (n - 1)) :
    ∀ n, n ≤ m → P n := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = m - k :=
    ⟨(m - n).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  clear hn
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have := hs (m - k) (by omega) ih
    rwa [show m - (k : ℤ) - 1 = m - ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this

/-- Rectangle `A` above-left of rectangle `B`, touching diagonally across a gap of one. -/
theorem merge_plus {h w : ℕ} {T : Set Cell} (hT : Closed h w T) (a b c d e f : ℤ)
    (h0 : 0 ≤ a) (hab : a ≤ b) (hbe : b + 2 ≤ e) (he : e < h)
    (hc0 : 0 ≤ c) (hcd : c ≤ d) (hdf : d + 2 ≤ f) (hf : f < w)
    (hA : ∀ i j : ℤ, a ≤ i → i ≤ b → c ≤ j → j ≤ d → (i, j) ∈ T)
    (hB : ∀ i j : ℤ, b + 2 ≤ i → i ≤ e → d + 2 ≤ j → j ≤ f → (i, j) ∈ T) :
    ∀ i j : ℤ, a ≤ i → i ≤ e → c ≤ j → j ≤ f → (i, j) ∈ T := by
  have x : (b + 1, d + 1) ∈ T :=
    hT.diag (by omega) (hA b d hab le_rfl hcd le_rfl)
      (hB (b + 2) (d + 2) le_rfl hbe le_rfl hdf) (by omega)
  have rowL : ∀ j, j ≤ d + 1 → c ≤ j → (b + 1, j) ∈ T := by
    refine int_ind_down (fun j => c ≤ j → (b + 1, j) ∈ T) (d + 1) (fun _ => x) ?_
    intro n hn ih hc
    exact hT.orth (by omega) (hA b (n - 1) hab le_rfl hc (by omega)) (ih (by omega))
      (by omega) (by omega) (by omega)
  have rowR : ∀ j, d + 1 ≤ j → j ≤ f → (b + 1, j) ∈ T := by
    refine int_ind_up (fun j => j ≤ f → (b + 1, j) ∈ T) (d + 1) (fun _ => x) ?_
    intro n hn ih hf'
    exact hT.orth (by omega) (hB (b + 2) (n + 1) le_rfl hbe (by omega) hf') (ih (by omega))
      (by omega) (by omega) (by omega)
  have colU : ∀ i, i ≤ b + 1 → a ≤ i → (i, d + 1) ∈ T := by
    refine int_ind_down (fun i => a ≤ i → (i, d + 1) ∈ T) (b + 1) (fun _ => x) ?_
    intro n hn ih ha
    exact hT.orth (by omega) (hA (n - 1) d ha (by omega) hcd le_rfl) (ih (by omega))
      (by omega) (by omega) (by omega)
  have colD : ∀ i, b + 1 ≤ i → i ≤ e → (i, d + 1) ∈ T := by
    refine int_ind_up (fun i => i ≤ e → (i, d + 1) ∈ T) (b + 1) (fun _ => x) ?_
    intro n hn ih he'
    exact hT.orth (by omega) (hB (n + 1) (d + 2) (by omega) he' le_rfl hdf) (ih (by omega))
      (by omega) (by omega) (by omega)
  have UR : ∀ i, i ≤ b + 1 → a ≤ i → ∀ j, d + 1 ≤ j → j ≤ f → (i, j) ∈ T := by
    refine int_ind_down (fun i => a ≤ i → ∀ j, d + 1 ≤ j → j ≤ f → (i, j) ∈ T) (b + 1)
      (fun _ j h1 h2 => rowR j h1 h2) ?_
    intro n hn ih ha
    refine int_ind_up (fun j => j ≤ f → (n - 1, j) ∈ T) (d + 1)
      (fun _ => colU (n - 1) (by omega) ha) ?_
    intro j hj ihj hjf
    exact hT.orth (by omega) (ih (by omega) (j + 1) (by omega) hjf) (ihj (by omega))
      (by omega) (by omega) (by omega)
  have LL : ∀ i, b + 1 ≤ i → i ≤ e → ∀ j, j ≤ d + 1 → c ≤ j → (i, j) ∈ T := by
    refine int_ind_up (fun i => i ≤ e → ∀ j, j ≤ d + 1 → c ≤ j → (i, j) ∈ T) (b + 1)
      (fun _ j h1 h2 => rowL j h1 h2) ?_
    intro n hn ih hne
    refine int_ind_down (fun j => c ≤ j → (n + 1, j) ∈ T) (d + 1)
      (fun _ => colD (n + 1) (by omega) hne) ?_
    intro j hj ihj hcj
    exact hT.orth (by omega) (ih (by omega) (j - 1) (by omega) hcj) (ihj (by omega))
      (by omega) (by omega) (by omega)
  intro i j hai hie hcj hjf
  by_cases hi : i ≤ b + 1
  · by_cases hj : d + 1 ≤ j
    · exact UR i hi hai j hj hjf
    · by_cases hi' : i ≤ b
      · exact hA i j hai hi' hcj (by omega)
      · exact LL i (by omega) hie j (by omega) hcj
  · by_cases hj : j ≤ d + 1
    · exact LL i (by omega) hie j hj hcj
    · exact hB i j (by omega) hie (by omega) hjf

/-- Reflecting the rows preserves closedness. -/
theorem Closed.reflect {h w : ℕ} {T : Set Cell} (hT : Closed h w T) :
    Closed h w {c | ((h : ℤ) - 1 - c.1, c.2) ∈ T} := by
  rw [closed_iff]
  intro i j hg
  simp only [Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h1 h2 <;>
    first
      | exact hT.orth (by omega) h1 h2 (by omega) (by omega) (by omega)
      | exact hT.diag (by omega) h2 h1 (by omega)

/-- Rectangle `A` below-left of rectangle `B`. -/
theorem merge_minus {h w : ℕ} {T : Set Cell} (hT : Closed h w T) (a b c d e f : ℤ)
    (h0 : 0 ≤ a) (hab : a ≤ b) (hbe : b + 2 ≤ e) (he : e < h)
    (hc0 : 0 ≤ c) (hcd : c ≤ d) (hdf : d + 2 ≤ f) (hf : f < w)
    (hA : ∀ i j : ℤ, b + 2 ≤ i → i ≤ e → c ≤ j → j ≤ d → (i, j) ∈ T)
    (hB : ∀ i j : ℤ, a ≤ i → i ≤ b → d + 2 ≤ j → j ≤ f → (i, j) ∈ T) :
    ∀ i j : ℤ, a ≤ i → i ≤ e → c ≤ j → j ≤ f → (i, j) ∈ T := by
  intro i j hai hie hcj hjf
  have key := merge_plus hT.reflect ((h : ℤ) - 1 - e) ((h : ℤ) - 1 - (b + 2)) c d
    ((h : ℤ) - 1 - a) f (by omega) (by omega) (by omega) (by omega) hc0 hcd hdf hf
    (fun i' j' h1 h2 h3 h4 => hA ((h : ℤ) - 1 - i') j' (by omega) (by omega) h3 h4)
    (fun i' j' h1 h2 h3 h4 => hB ((h : ℤ) - 1 - i') j' (by omega) (by omega) h3 h4)
    ((h : ℤ) - 1 - i) j (by omega) (by omega) hcj hjf
  simp only [Set.mem_ofPred_eq] at key
  rwa [show (h : ℤ) - 1 - ((h : ℤ) - 1 - i) = i by ring] at key

theorem getD_append_left' (l1 l2 : List ℕ) {t : ℕ} (ht : t < l1.length) :
    (l1 ++ l2).getD t 0 = l1.getD t 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left ht]

theorem getD_append_right' (l1 l2 : List ℕ) (t : ℕ) :
    (l1 ++ l2).getD (l1.length + t) 0 = l2.getD t 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- A separable arrangement placed at positions `p, p+1, …` infects its whole rectangle. -/
theorem rect_of_sepL {h w : ℕ} {T : Set Cell} (hT : Closed h w T) {l : List ℕ} {a : ℕ}
    (hl : SepL l a) :
    ∀ p : ℕ, 2 * (a + l.length) ≤ h + 1 → 2 * (p + l.length) ≤ w + 1 →
      (∀ t : ℕ, t < l.length → (2 * ((l.getD t 0 : ℕ) : ℤ), 2 * ((p : ℤ) + (t : ℤ))) ∈ T) →
      ∀ i j : ℤ, 2 * (a : ℤ) ≤ i → i ≤ 2 * ((a : ℤ) + (l.length : ℤ)) - 2 →
        2 * (p : ℤ) ≤ j → j ≤ 2 * ((p : ℤ) + (l.length : ℤ)) - 2 → (i, j) ∈ T := by
  induction hl with
  | single a =>
    intro p hh hw hseed i j h1 h2 h3 h4
    have := hseed 0 (by simp)
    simp only [List.length_singleton, Nat.cast_one] at h2 h4
    obtain rfl : i = 2 * (a : ℤ) := by omega
    obtain rfl : j = 2 * (p : ℤ) := by omega
    simpa using this
  | @plus l1 l2 a h1 h2 ih1 ih2 =>
    intro p hh hw hseed
    rw [List.length_append] at hh hw
    have hp1 := h1.length_pos
    have hp2 := h2.length_pos
    have R1 := ih1 p (by omega) (by omega) (fun t ht => by
      have := hseed t (by rw [List.length_append]; omega)
      rwa [getD_append_left' l1 l2 ht] at this)
    have R2 := ih2 (p + l1.length) (by omega) (by omega) (fun t ht => by
      have := hseed (l1.length + t) (by rw [List.length_append]; omega)
      rw [getD_append_right'] at this
      have e : ((p + l1.length : ℕ) : ℤ) + (t : ℤ) = (p : ℤ) + ((l1.length + t : ℕ) : ℤ) := by
        push_cast; ring
      rw [e]
      exact this)
    intro i j hi1 hi2 hj1 hj2
    rw [List.length_append] at hi2 hj2
    push_cast at hi2 hj2 R1 R2
    exact merge_plus hT (2 * (a : ℤ)) (2 * ((a : ℤ) + l1.length) - 2) (2 * (p : ℤ))
      (2 * ((p : ℤ) + l1.length) - 2) (2 * ((a : ℤ) + l1.length + l2.length) - 2)
      (2 * ((p : ℤ) + l1.length + l2.length) - 2)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun i j a1 a2 a3 a4 => R1 i j a1 a2 a3 a4)
      (fun i j a1 a2 a3 a4 => R2 i j (by omega) (by omega) (by omega) (by omega))
      i j hi1 (by omega) hj1 (by omega)
  | @minus l1 l2 a h1 h2 ih1 ih2 =>
    intro p hh hw hseed
    rw [List.length_append] at hh hw
    have hp1 := h1.length_pos
    have hp2 := h2.length_pos
    have R1 := ih1 p (by omega) (by omega) (fun t ht => by
      have := hseed t (by rw [List.length_append]; omega)
      rwa [getD_append_left' l1 l2 ht] at this)
    have R2 := ih2 (p + l1.length) (by omega) (by omega) (fun t ht => by
      have := hseed (l1.length + t) (by rw [List.length_append]; omega)
      rw [getD_append_right'] at this
      have e : ((p + l1.length : ℕ) : ℤ) + (t : ℤ) = (p : ℤ) + ((l1.length + t : ℕ) : ℤ) := by
        push_cast; ring
      rw [e]
      exact this)
    intro i j hi1 hi2 hj1 hj2
    rw [List.length_append] at hi2 hj2
    push_cast at hi2 hj2 R1 R2
    exact merge_minus hT (2 * (a : ℤ)) (2 * ((a : ℤ) + l2.length) - 2) (2 * (p : ℤ))
      (2 * ((p : ℤ) + l1.length) - 2) (2 * ((a : ℤ) + l2.length + l1.length) - 2)
      (2 * ((p : ℤ) + l1.length + l2.length) - 2)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun i j a1 a2 a3 a4 => R1 i j (by omega) (by omega) a3 a4)
      (fun i j a1 a2 a3 a4 => R2 i j a1 a2 (by omega) (by omega))
      i j hi1 (by omega) hj1 (by omega)

/-- The seed set of an arrangement: value `l[t]` at position `t` gives the cell
`(2 l[t], 2 t)`. -/
def seeds (l : List ℕ) : Finset Cell :=
  (Finset.range l.length).image (fun t : ℕ => (2 * ((l.getD t 0 : ℕ) : ℤ), 2 * (t : ℤ)))

theorem mem_seeds {l : List ℕ} {c : Cell} :
    c ∈ seeds l ↔ ∃ t : ℕ, t < l.length ∧ c = (2 * ((l.getD t 0 : ℕ) : ℤ), 2 * (t : ℤ)) := by
  simp only [seeds, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

/-- Separable seeds percolate on the odd square. -/
theorem percolates_seeds_of_sepL {n : ℕ} {l : List ℕ} (hl : SepL l 0) (hn : l.length = n) :
    Percolates (2 * n - 1) (2 * n - 1) (↑(seeds l) : Set Cell) := by
  rw [percolates_iff]
  intro T hST hT
  rintro ⟨i, j⟩ hg
  rw [mem_grid] at hg
  have npos := hl.length_pos
  refine rect_of_sepL hT hl 0 (by omega) (by omega) (fun t ht => hST ?_) i j
    (by omega) (by omega) (by omega) (by omega)
  rw [Finset.mem_coe, mem_seeds]
  exact ⟨t, ht, by simp⟩

end PowerContamination
