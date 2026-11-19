import PowerContamination.Words

/-!
# Seed sets on two rows are in bijection with words

`enc` is a bijection from the subsets of the `2 × w` grid onto the words of length `w`,
and it sends the number of seeds to the weight of the word.
-/

namespace PowerContamination

open Finset

/-- All words of length `n`. -/
def words : ℕ → Finset (List Sym)
  | 0 => {[]}
  | n + 1 => (words n).image (List.cons Sym.O) ∪ (words n).image (List.cons Sym.A) ∪
      (words n).image (List.cons Sym.B) ∪ (words n).image (List.cons Sym.D)

theorem mem_words : ∀ (n : ℕ) (l : List Sym), l ∈ words n ↔ l.length = n := by
  intro n
  induction n with
  | zero => intro l; simp [words]
  | succ n ih =>
    intro l
    cases l with
    | nil => simp [words]
    | cons x l => cases x <;> simp [words, ih]

/-- Number of words of length `n` satisfying `p`. -/
def cnt (p : List Sym → Bool) (n : ℕ) : ℕ := ((words n).filter (fun l => p l = true)).card

theorem cnt_zero (p : List Sym → Bool) : cnt p 0 = if p [] = true then 1 else 0 := by
  unfold cnt
  simp only [words, filter_singleton]
  split_ifs <;> simp

theorem cnt_succ (p : List Sym → Bool) (n : ℕ) :
    cnt p (n + 1) = cnt (fun l => p (Sym.O :: l)) n + cnt (fun l => p (Sym.A :: l)) n +
      cnt (fun l => p (Sym.B :: l)) n + cnt (fun l => p (Sym.D :: l)) n := by
  have himg : ∀ x : Sym, (((words n).image (List.cons x)).filter (fun l => p l = true)).card =
      cnt (fun l => p (x :: l)) n := by
    intro x
    rw [filter_image, card_image_of_injective _ List.cons_injective]
    rfl
  have hdisj : ∀ x y : Sym, x ≠ y →
      Disjoint ((words n).image (List.cons x)) ((words n).image (List.cons y)) := by
    intro x y hxy
    rw [disjoint_left]
    intro l h1 h2
    simp only [mem_image] at h1 h2
    obtain ⟨a, -, rfl⟩ := h1
    obtain ⟨b, -, hb⟩ := h2
    exact hxy (List.cons.inj hb).1.symm
  have hU : ∀ s t : Finset (List Sym), Disjoint s t →
      ((s ∪ t).filter (fun l => p l = true)).card =
        (s.filter (fun l => p l = true)).card + (t.filter (fun l => p l = true)).card := by
    intro s t h
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]
  have e : cnt p (n + 1) = (((words n).image (List.cons Sym.O) ∪
      (words n).image (List.cons Sym.A) ∪ (words n).image (List.cons Sym.B) ∪
      (words n).image (List.cons Sym.D)).filter (fun l => p l = true)).card := rfl
  rw [e, hU _ _ (disjoint_union_left.2 ⟨disjoint_union_left.2
      ⟨hdisj _ _ (by decide), hdisj _ _ (by decide)⟩, hdisj _ _ (by decide)⟩),
    hU _ _ (disjoint_union_left.2 ⟨hdisj _ _ (by decide), hdisj _ _ (by decide)⟩),
    hU _ _ (hdisj _ _ (by decide)), himg, himg, himg, himg]

theorem cnt_congr {p q : List Sym → Bool} (h : ∀ l, p l = q l) (n : ℕ) : cnt p n = cnt q n := by
  rw [show p = q from funext h]

theorem cnt_false (n : ℕ) : cnt (fun _ => false) n = 0 := by
  simp [cnt]

theorem cnt_pos {p : List Sym → Bool} {l : List Sym} (hp : p l = true) :
    0 < cnt p l.length :=
  card_pos.2 ⟨l, mem_filter.2 ⟨(mem_words _ _).2 rfl, hp⟩⟩

theorem exists_of_cnt_pos {p : List Sym → Bool} {n : ℕ} (h : 0 < cnt p n) :
    ∃ l : List Sym, l.length = n ∧ p l = true := by
  obtain ⟨l, hl⟩ := card_pos.1 h
  rw [mem_filter, mem_words] at hl
  exact ⟨l, hl⟩

/-! ### The bijection -/

theorem wordFrom_inj {c c' : ℤ → Sym} : ∀ (n : ℕ) (j : ℤ),
    wordFrom c j n = wordFrom c' j n → ∀ t : ℕ, t < n → c (j + t) = c' (j + t)
  | 0, _, _, t, ht => by omega
  | n + 1, j, h, t, ht => by
    simp only [wordFrom, List.cons.injEq] at h
    cases t with
    | zero => simpa using h.1
    | succ t =>
      have := wordFrom_inj n (j + 1) h.2 t (by omega)
      rwa [show j + 1 + (t : ℤ) = j + ((t + 1 : ℕ) : ℤ) by push_cast; ring] at this

theorem wordFrom_eq_of_getD (c : ℤ → Sym) : ∀ (l : List Sym) (j : ℤ),
    (∀ t : ℕ, t < l.length → c (j + t) = l.getD t Sym.O) → wordFrom c j l.length = l
  | [], _, _ => rfl
  | x :: l, j, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.cast_zero, add_zero, List.getD_cons_zero] at h0
    have ih := wordFrom_eq_of_getD c l (j + 1) (fun t ht => by
      have := h (t + 1) (by simpa using ht)
      rw [List.getD_cons_succ] at this
      rw [← this]
      congr 1
      push_cast
      ring)
    simp [wordFrom, h0, ih]

theorem enc_length (S : Finset Cell) (w : ℕ) : (enc S w).length = w := wordFrom_length _ _ _

/-- The seed set of a word. -/
def decSet (l : List Sym) : Finset Cell :=
  ((range l.length).filter (fun t => (l.getD t Sym.O).top = true)).image
      (fun t : ℕ => ((0 : ℤ), (t : ℤ))) ∪
    ((range l.length).filter (fun t => (l.getD t Sym.O).bot = true)).image
      (fun t : ℕ => ((1 : ℤ), (t : ℤ)))

theorem mem_decSet_zero (l : List Sym) (t : ℕ) :
    ((0 : ℤ), (t : ℤ)) ∈ decSet l ↔ t < l.length ∧ (l.getD t Sym.O).top = true := by
  simp [decSet]

theorem mem_decSet_one (l : List Sym) (t : ℕ) :
    ((1 : ℤ), (t : ℤ)) ∈ decSet l ↔ t < l.length ∧ (l.getD t Sym.O).bot = true := by
  simp [decSet]

theorem decSet_subset (l : List Sym) : (↑(decSet l) : Set Cell) ⊆ grid 2 l.length := by
  intro c hc
  rw [mem_coe, decSet, mem_union, mem_image, mem_image] at hc
  rcases hc with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
  · rw [mem_filter, mem_range] at ht
    rw [mem_grid]
    omega

theorem colType_decSet (l : List Sym) (t : ℕ) (ht : t < l.length) :
    colType (decSet l) (t : ℤ) = l.getD t Sym.O := by
  apply Sym.ext'
  · rw [Bool.eq_iff_iff, colType_top, mem_decSet_zero]
    simp [ht]
  · rw [Bool.eq_iff_iff, colType_bot, mem_decSet_one]
    simp [ht]

theorem enc_decSet (l : List Sym) : enc (decSet l) l.length = l :=
  wordFrom_eq_of_getD _ l 0 (fun t ht => by simpa using colType_decSet l t ht)

theorem enc_inj {w : ℕ} {S S' : Finset Cell} (hS : (↑S : Set Cell) ⊆ grid 2 w)
    (hS' : (↑S' : Set Cell) ⊆ grid 2 w) (h : enc S w = enc S' w) : S = S' := by
  have hc : ∀ t : ℕ, t < w → colType S t = colType S' t := fun t ht => by
    simpa using wordFrom_inj w 0 h t ht
  ext ⟨i, j⟩
  by_cases hg : (i, j) ∈ grid 2 w
  · rw [mem_grid] at hg
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = t := ⟨j.toNat, (Int.toNat_of_nonneg hg.2.2.1).symm⟩
    have := hc t (by omega)
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rw [← colType_top, ← colType_top, this]
    · rw [← colType_bot, ← colType_bot, this]
  · exact ⟨fun h => absurd (hS h) hg, fun h => absurd (hS' h) hg⟩

private theorem card_aux : ∀ l : List Sym,
    ((range l.length).filter (fun t => (l.getD t Sym.O).top = true)).card +
      ((range l.length).filter (fun t => (l.getD t Sym.O).bot = true)).card = weight l
  | [] => by simp
  | x :: l => by
    have ih := card_aux l
    rw [card_filter, card_filter] at ih ⊢
    rw [List.length_cons, sum_range_succ', sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, weight_cons, Sym.wt_eq]
    omega

theorem card_decSet (l : List Sym) : (decSet l).card = weight l := by
  unfold decSet
  rw [card_union_of_disjoint, card_image_of_injective, card_image_of_injective, card_aux]
  · intro a b h
    simpa using h
  · intro a b h
    simpa using h
  · rw [disjoint_left]
    intro c h1 h2
    simp only [mem_image] at h1 h2
    obtain ⟨a, -, rfl⟩ := h1
    obtain ⟨b, -, hb⟩ := h2
    simp at hb

theorem card_eq_weight {w : ℕ} {S : Finset Cell} (hS : (↑S : Set Cell) ⊆ grid 2 w) :
    S.card = weight (enc S w) := by
  have hsub : (↑(decSet (enc S w)) : Set Cell) ⊆ grid 2 w := by
    have := decSet_subset (enc S w)
    rwa [enc_length] at this
  have hdec : decSet (enc S w) = S := by
    refine enc_inj hsub hS ?_
    have := enc_decSet (enc S w)
    rwa [enc_length] at this
  calc S.card = (decSet (enc S w)).card := by rw [hdec]
    _ = weight (enc S w) := card_decSet _

/-- The cells of the `2 × w` grid. -/
noncomputable def box (w : ℕ) : Finset Cell := Finset.Ico (0 : ℤ) 2 ×ˢ Finset.Ico (0 : ℤ) w

theorem subset_grid_iff {w : ℕ} (S : Finset Cell) :
    (↑S : Set Cell) ⊆ grid 2 w ↔ S ∈ (box w).powerset := by
  rw [mem_powerset]
  constructor
  · rintro h ⟨i, j⟩ hc
    have := h hc
    rw [mem_grid] at this
    simp only [box, mem_product, mem_Ico]
    omega
  · rintro h ⟨i, j⟩ hc
    have := h hc
    simp only [box, mem_product, mem_Ico] at this
    rw [mem_grid]
    omega

/-- Counting two-row seed sets is counting words. -/
theorem card_sets_eq_cnt (w : ℕ) (p : List Sym → Bool) :
    (((box w).powerset).filter (fun S => p (enc S w) = true)).card = cnt p w := by
  unfold cnt
  refine Finset.card_bij (fun S _ => enc S w) ?_ ?_ ?_
  · intro S hS
    rw [mem_filter] at hS ⊢
    exact ⟨(mem_words _ _).2 (enc_length S w), hS.2⟩
  · intro S hS S' hS' h
    rw [mem_filter, ← subset_grid_iff] at hS hS'
    exact enc_inj hS.1 hS'.1 h
  · intro l hl
    rw [mem_filter, mem_words] at hl
    obtain ⟨hlen, hp⟩ := hl
    subst hlen
    refine ⟨decSet l, ?_, enc_decSet l⟩
    rw [mem_filter, ← subset_grid_iff]
    exact ⟨decSet_subset l, by rw [enc_decSet]; exact hp⟩

end PowerContamination
