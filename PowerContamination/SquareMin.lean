import PowerContamination.SquareClosed
import PowerContamination.Obstructions

/-!
# Minimum percolating sets on the odd square

On the `(2n-1) × (2n-1)` grid every percolating set has at least `n` cells, and one with
exactly `n` cells is the seed set of an arrangement of `n` distinct values.
-/

namespace PowerContamination

open Finset

/-- Occupied lines: the first and last are occupied and no two consecutive ones are empty. -/
theorem line_lemma (n : ℕ) (X : Finset ℤ) (h0 : (0 : ℤ) ∈ X)
    (hlast : (2 * (n : ℤ) - 2) ∈ X)
    (hgap : ∀ j : ℤ, 0 ≤ j → j + 1 ≤ 2 * (n : ℤ) - 2 → j ∈ X ∨ j + 1 ∈ X)
    (hbd : ∀ x ∈ X, 0 ≤ x ∧ x ≤ 2 * (n : ℤ) - 2) :
    n ≤ X.card ∧ (X.card = n → (∀ x ∈ X, ∃ t : ℕ, t < n ∧ x = 2 * (t : ℤ)) ∧
      ∀ t : ℕ, t < n → 2 * (t : ℤ) ∈ X) := by
  have himg : Finset.Ico (0 : ℤ) n ⊆ X.image (· / 2) := by
    intro i hi
    rw [mem_Ico] at hi
    rw [mem_image]
    by_cases hl : i = n - 1
    · exact ⟨2 * (n : ℤ) - 2, hlast, by omega⟩
    · rcases hgap (2 * i) (by omega) (by omega) with h | h
      · exact ⟨2 * i, h, by omega⟩
      · exact ⟨2 * i + 1, h, by omega⟩
  have hc1 : n ≤ (X.image (· / 2)).card := by
    have := card_le_card himg
    simpa using this
  have hc2 : (X.image (· / 2)).card ≤ X.card := card_image_le
  refine ⟨by omega, fun hcard => ?_⟩
  have hinj : Set.InjOn (fun x : ℤ => x / 2) ↑X := card_image_iff.1 (by omega)
  have hev : ∀ t : ℕ, t < n → 2 * (t : ℤ) ∈ X := by
    intro t
    induction t with
    | zero => intro _; simpa using h0
    | succ t ih =>
      intro ht
      have h2t := ih (by omega)
      have hodd : 2 * (t : ℤ) + 1 ∉ X := by
        intro hmem
        have := hinj (mem_coe.2 h2t) (mem_coe.2 hmem) (by simp only; omega)
        omega
      rcases hgap (2 * (t : ℤ) + 1) (by omega) (by omega) with h | h
      · exact absurd h hodd
      · rw [show 2 * (((t + 1 : ℕ)) : ℤ) = 2 * (t : ℤ) + 1 + 1 by push_cast; ring]
        exact h
  refine ⟨fun x hx => ?_, hev⟩
  obtain ⟨hx0, hx1⟩ := hbd x hx
  have ht : (x / 2).toNat < n := by omega
  have hmem := hev _ ht
  have := hinj (mem_coe.2 hx) (mem_coe.2 hmem) (by simp only; omega)
  exact ⟨(x / 2).toNat, ht, this⟩

theorem card_seeds (l : List ℕ) : (seeds l).card = l.length := by
  unfold seeds
  rw [card_image_of_injective, card_range]
  intro t t' h
  simp only [Prod.mk.injEq] at h
  omega

theorem seeds_inj {l l' : List ℕ} (hlen : l.length = l'.length) (h : seeds l = seeds l') :
    l = l' := by
  apply List.ext_getElem hlen
  intro t ht ht'
  have hm : (2 * ((l.getD t 0 : ℕ) : ℤ), 2 * (t : ℤ)) ∈ seeds l' := by
    rw [← h, mem_seeds]
    exact ⟨t, ht, rfl⟩
  rw [mem_seeds] at hm
  obtain ⟨t', -, he⟩ := hm
  simp only [Prod.mk.injEq] at he
  obtain rfl : t = t' := by omega
  have := he.1
  rw [List.getD_eq_getElem _ _ ht, List.getD_eq_getElem _ _ ht'] at this
  omega

/-- Lower bound and structure of minimum sets on the odd square. -/
theorem min_structure {n : ℕ} (hn : 0 < n) {S : Finset Cell}
    (hS : (↑S : Set Cell) ⊆ grid (2 * n - 1) (2 * n - 1))
    (hP : Percolates (2 * n - 1) (2 * n - 1) (↑S : Set Cell)) :
    n ≤ S.card ∧ (S.card = n → ∃ l : List ℕ, l.length = n ∧ l.Nodup ∧ S = seeds l) := by
  classical
  have hgrid : ∀ c ∈ S, 0 ≤ c.1 ∧ c.1 ≤ 2 * (n : ℤ) - 2 ∧ 0 ≤ c.2 ∧ c.2 ≤ 2 * (n : ℤ) - 2 := by
    rintro ⟨i, j⟩ hc
    have := hS hc
    rw [mem_grid] at this
    simp only
    omega
  -- columns
  have colL := line_lemma n (S.image Prod.snd)
    (by
      by_contra hcon
      exact not_percolates_of_blocked_cols hS {0}
        (fun x hx => by simp only [Set.mem_singleton_iff] at hx ⊢; omega)
        (fun c hc hcJ => by
          simp only [Set.mem_singleton_iff] at hcJ
          exact hcon (hcJ ▸ mem_image_of_mem Prod.snd hc))
        (c0 := (0, 0)) (by rw [mem_grid]; omega) rfl hP)
    (by
      by_contra hcon
      exact not_percolates_of_blocked_cols hS {2 * (n : ℤ) - 2}
        (fun x hx => by simp only [Set.mem_singleton_iff] at hx ⊢; omega)
        (fun c hc hcJ => by
          simp only [Set.mem_singleton_iff] at hcJ
          exact hcon (hcJ ▸ mem_image_of_mem Prod.snd hc))
        (c0 := (0, 2 * (n : ℤ) - 2)) (by rw [mem_grid]; omega) rfl hP)
    (by
      intro j hj0 hj1
      by_contra hcon
      push Not at hcon
      exact not_percolates_of_blocked_cols hS {j, j + 1}
        (fun x hx => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
          omega)
        (fun c hc hcJ => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcJ
          rcases hcJ with e | e
          · exact hcon.1 (e ▸ mem_image_of_mem Prod.snd hc)
          · exact hcon.2 (e ▸ mem_image_of_mem Prod.snd hc))
        (c0 := (0, j)) (by rw [mem_grid]; omega) (by simp) hP)
    (by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
      have := hgrid c hc
      omega)
  -- rows
  have rowL := line_lemma n (S.image Prod.fst)
    (by
      by_contra hcon
      exact not_percolates_of_blocked_rows hS {0}
        (fun x hx => by simp only [Set.mem_singleton_iff] at hx ⊢; omega)
        (fun c hc hcJ => by
          simp only [Set.mem_singleton_iff] at hcJ
          exact hcon (hcJ ▸ mem_image_of_mem Prod.fst hc))
        (c0 := (0, 0)) (by rw [mem_grid]; omega) rfl hP)
    (by
      by_contra hcon
      exact not_percolates_of_blocked_rows hS {2 * (n : ℤ) - 2}
        (fun x hx => by simp only [Set.mem_singleton_iff] at hx ⊢; omega)
        (fun c hc hcJ => by
          simp only [Set.mem_singleton_iff] at hcJ
          exact hcon (hcJ ▸ mem_image_of_mem Prod.fst hc))
        (c0 := (2 * (n : ℤ) - 2, 0)) (by rw [mem_grid]; omega) rfl hP)
    (by
      intro j hj0 hj1
      by_contra hcon
      push Not at hcon
      exact not_percolates_of_blocked_rows hS {j, j + 1}
        (fun x hx => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
          omega)
        (fun c hc hcJ => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcJ
          rcases hcJ with e | e
          · exact hcon.1 (e ▸ mem_image_of_mem Prod.fst hc)
          · exact hcon.2 (e ▸ mem_image_of_mem Prod.fst hc))
        (c0 := (j, 0)) (by rw [mem_grid]; omega) (by simp) hP)
    (by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
      have := hgrid c hc
      omega)
  have hcs : (S.image Prod.snd).card ≤ S.card := card_image_le
  have hrs : (S.image Prod.fst).card ≤ S.card := card_image_le
  refine ⟨by omega, fun hcard => ?_⟩
  obtain ⟨-, hcolEven⟩ := colL.2 (by omega)
  obtain ⟨hrowAll, -⟩ := rowL.2 (by omega)
  have hfst : Set.InjOn Prod.fst (↑S : Set Cell) := card_image_iff.1 (by omega)
  have key : ∀ t : ℕ, t < n → ∃ r : ℕ, r < n ∧ (2 * (r : ℤ), 2 * (t : ℤ)) ∈ S := by
    intro t ht
    obtain ⟨⟨i, j⟩, hc, hj⟩ := mem_image.1 (hcolEven t ht)
    obtain ⟨r, hr, hi⟩ := hrowAll i (mem_image.2 ⟨(i, j), hc, rfl⟩)
    simp only at hj hi
    subst hj hi
    exact ⟨r, hr, hc⟩
  choose! r hr hrS using key
  have hlen : ((List.range n).map r).length = n := by simp
  have hget : ∀ t, t < n → ((List.range n).map r).getD t 0 = r t := by
    intro t ht
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact ht)]
    simp
  have hsub : seeds ((List.range n).map r) ⊆ S := by
    intro c hc
    rw [mem_seeds] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    rw [hlen] at ht
    rw [hget t ht]
    exact hrS t ht
  refine ⟨(List.range n).map r, hlen, ?_, ?_⟩
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro x hx y hy hxy
    rw [List.mem_range] at hx hy
    have := hfst (mem_coe.2 (hrS x hx)) (mem_coe.2 (hrS y hy)) (by simp only; rw [hxy])
    simp only [Prod.mk.injEq] at this
    omega
  · exact (eq_of_subset_of_card_le hsub (by rw [card_seeds, hlen]; omega)).symm

end PowerContamination
