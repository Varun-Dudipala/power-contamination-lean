import PowerContamination.SepList

/-!
# Separable arrangements are counted by the large Schröder numbers

`sepSet n a` is the finite set of separable arrangements of `a, …, a+n-1`. Every such
arrangement of length at least two is a direct sum or a skew sum, never both; complementing
the values exchanges the two kinds; and a direct sum splits uniquely into a first
summand that is not a direct sum and a separable remainder. This gives the recurrence of
`Nat.largeSchroder`.
-/

noncomputable section

namespace PowerContamination

open Finset Classical

/-- Separable arrangements of the values `a, …, a+n-1`. -/
def sepSet (n a : ℕ) : Finset (List ℕ) :=
  (List.range' a n).permutations.toFinset.filter (fun l => SepL l a)

theorem mem_sepSet {n a : ℕ} {l : List ℕ} : l ∈ sepSet n a ↔ l.length = n ∧ SepL l a := by
  simp only [sepSet, mem_filter, List.mem_toFinset, List.mem_permutations]
  constructor
  · rintro ⟨hp, hs⟩
    exact ⟨by simpa using hp.length_eq, hs⟩
  · rintro ⟨hlen, hs⟩
    exact ⟨hlen ▸ hs.perm, hs⟩

/-- A direct sum of two separable blocks. -/
def PlusDec (l : List ℕ) (a : ℕ) : Prop :=
  ∃ l1 l2, l = l1 ++ l2 ∧ SepL l1 a ∧ SepL l2 (a + l1.length)

/-- A skew sum of two separable blocks. -/
def MinusDec (l : List ℕ) (a : ℕ) : Prop :=
  ∃ l1 l2, l = l1 ++ l2 ∧ SepL l1 (a + l2.length) ∧ SepL l2 a

theorem PlusDec.sepL {l : List ℕ} {a : ℕ} : PlusDec l a → SepL l a := by
  rintro ⟨l1, l2, rfl, h1, h2⟩
  exact SepL.plus h1 h2

theorem MinusDec.sepL {l : List ℕ} {a : ℕ} : MinusDec l a → SepL l a := by
  rintro ⟨l1, l2, rfl, h1, h2⟩
  exact SepL.minus h1 h2

theorem PlusDec.two_le {l : List ℕ} {a : ℕ} : PlusDec l a → 2 ≤ l.length := by
  rintro ⟨l1, l2, rfl, h1, h2⟩
  have := h1.length_pos
  have := h2.length_pos
  rw [List.length_append]
  omega

theorem plus_or_minus {l : List ℕ} {a : ℕ} (h : SepL l a) (h2 : 2 ≤ l.length) :
    PlusDec l a ∨ MinusDec l a := by
  cases h with
  | single a => simp at h2
  | plus h1 h2' => exact Or.inl ⟨_, _, rfl, h1, h2'⟩
  | minus h1 h2' => exact Or.inr ⟨_, _, rfl, h1, h2'⟩

theorem not_plus_and_minus {l : List ℕ} {a : ℕ} : ¬(PlusDec l a ∧ MinusDec l a) := by
  rintro ⟨⟨l1, l2, rfl, h1, h2⟩, ⟨m1, m2, he, g1, g2⟩⟩
  have p1 := h1.length_pos
  have p2 := h2.length_pos
  have q1 := g1.length_pos
  have q2 := g2.length_pos
  have hlen : l1.length + l2.length = m1.length + m2.length := by
    have := congrArg List.length he
    simpa using this
  have pl1 : l1 <+: l1 ++ l2 := List.prefix_append l1 l2
  have pm1 : m1 <+: l1 ++ l2 := by
    rw [he]
    exact List.prefix_append m1 m2
  rcases le_or_gt l1.length m1.length with hle | hgt
  · have hsub := (List.prefix_of_prefix_length_le pl1 pm1 hle).subset
    have ha : a ∈ l1 := (h1.mem_iff a).2 ⟨le_rfl, by omega⟩
    have := (g1.mem_iff a).1 (hsub ha)
    omega
  · have hsub := (List.prefix_of_prefix_length_le pm1 pl1 hgt.le).subset
    have hmax : a + m2.length + m1.length - 1 ∈ m1 := (g1.mem_iff _).2 ⟨by omega, by omega⟩
    have := (h1.mem_iff _).1 (hsub hmax)
    omega

/-! ### Complement -/

/-- Complement of the values in `0, …, N`. -/
def kap (N : ℕ) (l : List ℕ) : List ℕ := l.map (fun x => N - x)

theorem kap_length (N : ℕ) (l : List ℕ) : (kap N l).length = l.length := by
  simp [kap]

theorem kap_kap {N : ℕ} {l : List ℕ} (h : ∀ x ∈ l, x ≤ N) : kap N (kap N l) = l := by
  unfold kap
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  have := h x hx
  simp only [Function.comp_apply, id_eq]
  omega

theorem plus_kap {l : List ℕ} {n : ℕ} (h : PlusDec l 0) (hlen : l.length = n) :
    MinusDec (kap (n - 1) l) 0 := by
  obtain ⟨l1, l2, rfl, h1, h2⟩ := h
  rw [List.length_append] at hlen
  have p1 := h1.length_pos
  have p2 := h2.length_pos
  have c1 := h1.compl (n - 1) (by omega)
  have c2 := h2.compl (n - 1) (by omega)
  refine ⟨kap (n - 1) l1, kap (n - 1) l2, by simp [kap], c1.cast ?_, c2.cast ?_⟩
  · rw [kap_length]; omega
  · omega

theorem minus_kap {l : List ℕ} {n : ℕ} (h : MinusDec l 0) (hlen : l.length = n) :
    PlusDec (kap (n - 1) l) 0 := by
  obtain ⟨l1, l2, rfl, h1, h2⟩ := h
  rw [List.length_append] at hlen
  have p1 := h1.length_pos
  have p2 := h2.length_pos
  have c1 := h1.compl (n - 1) (by omega)
  have c2 := h2.compl (n - 1) (by omega)
  refine ⟨kap (n - 1) l1, kap (n - 1) l2, by simp [kap], c1.cast ?_, c2.cast ?_⟩
  · omega
  · rw [kap_length]; omega

theorem card_minus_eq_plus (n : ℕ) :
    ((sepSet n 0).filter (fun l => MinusDec l 0)).card =
      ((sepSet n 0).filter (fun l => PlusDec l 0)).card := by
  have hbd : ∀ l ∈ sepSet n 0, ∀ x ∈ l, x ≤ n - 1 := by
    intro l hl x hx
    rw [mem_sepSet] at hl
    have := (hl.2.mem_iff x).1 hx
    omega
  refine Finset.card_bij (fun l _ => kap (n - 1) l) ?_ ?_ ?_
  · intro l hl
    rw [mem_filter, mem_sepSet] at hl ⊢
    have := minus_kap hl.2 hl.1.1
    exact ⟨⟨by rw [kap_length]; exact hl.1.1, this.sepL⟩, this⟩
  · intro l hl l' hl' he
    rw [mem_filter] at hl hl'
    rw [← kap_kap (hbd l hl.1), ← kap_kap (hbd l' hl'.1), he]
  · intro b hb
    rw [mem_filter] at hb
    have hb' := hb
    rw [mem_sepSet] at hb'
    have := plus_kap hb'.2 hb'.1.1
    refine ⟨kap (n - 1) b, ?_, kap_kap (hbd b hb.1)⟩
    rw [mem_filter, mem_sepSet]
    exact ⟨⟨by rw [kap_length]; exact hb'.1.1, this.sepL⟩, this⟩

/-! ### Translation -/

theorem card_sepSet_shift (m a : ℕ) : (sepSet m a).card = (sepSet m 0).card := by
  symm
  refine Finset.card_bij (fun l _ => l.map (· + a)) ?_ ?_ ?_
  · intro l hl
    rw [mem_sepSet] at hl ⊢
    exact ⟨by rw [List.length_map]; exact hl.1, (hl.2.shift a).cast (zero_add a)⟩
  · intro l _ l' _ he
    exact List.map_injective_iff.2 (add_left_injective a) he
  · intro b hb
    rw [mem_sepSet] at hb
    refine ⟨b.map (· - a), ?_, ?_⟩
    · rw [mem_sepSet]
      exact ⟨by rw [List.length_map]; exact hb.1, hb.2.unshift 0 a (zero_add a)⟩
    · rw [List.map_map]
      conv_rhs => rw [← List.map_id b]
      apply List.map_congr_left
      intro x hx
      have := (hb.2.mem_iff x).1 hx
      simp only [Function.comp_apply, id_eq]
      omega

/-! ### First summand -/

theorem card_plus (n : ℕ) :
    ((sepSet n 0).filter (fun l => PlusDec l 0)).card =
      ∑ i ∈ Ico 1 n, ((sepSet i 0).filter (fun l => ¬PlusDec l 0)).card *
        (sepSet (n - i) 0).card := by
  have hR : (∑ i ∈ Ico 1 n, ((sepSet i 0).filter (fun l => ¬PlusDec l 0)).card *
      (sepSet (n - i) 0).card) =
      ((Ico 1 n).sigma (fun i => ((sepSet i 0).filter (fun l => ¬PlusDec l 0)) ×ˢ
        (sepSet (n - i) i))).card := by
    rw [card_sigma]
    apply sum_congr rfl
    intro i _
    rw [card_product, card_sepSet_shift (n - i) i]
  rw [hR]
  symm
  have key : ∀ (i : ℕ) (l1 l2 : List ℕ) (i' : ℕ) (l1' l2' : List ℕ),
      l1.length = i → SepL l1 0 → SepL l2 i → l1'.length = i' → SepL l1' 0 →
      ¬PlusDec l1' 0 → l1 ++ l2 = l1' ++ l2' → i < i' → False := by
    intro i l1 l2 i' l1' l2' hl1 s1 s2 hl1' s1' np he hlt
    have pl : l1 <+: l1 ++ l2 := List.prefix_append l1 l2
    have pl' : l1' <+: l1 ++ l2 := by
      rw [he]
      exact List.prefix_append l1' l2'
    obtain ⟨m, rfl⟩ := List.prefix_of_prefix_length_le pl pl' (by omega)
    rw [List.append_assoc] at he
    have hl2 : l2 = m ++ l2' := List.append_cancel_left he
    rw [List.length_append] at hl1'
    have hm : m ≠ [] := by
      intro e
      subst e
      simp at hl1'
      omega
    have sm : SepL m i := s2.of_prefix m (hl2 ▸ List.prefix_append m l2') hm (by
      intro x hx
      have := (s1'.mem_iff x).1 (List.mem_append_right l1 hx)
      rw [List.length_append] at this
      omega)
    exact np ⟨l1, m, rfl, s1, sm.cast (by omega)⟩
  refine Finset.card_bij (fun x _ => x.2.1 ++ x.2.2) ?_ ?_ ?_
  · rintro ⟨i, l1, l2⟩ hx
    simp only [mem_sigma, mem_Ico, mem_product, mem_filter, mem_sepSet] at hx
    obtain ⟨⟨hi1, hi2⟩, ⟨⟨hl1, s1⟩, -⟩, hl2, s2⟩ := hx
    have s2' : SepL l2 (0 + l1.length) := s2.cast (by omega)
    simp only [mem_filter, mem_sepSet]
    exact ⟨⟨by rw [List.length_append]; omega, SepL.plus s1 s2'⟩, l1, l2, rfl, s1, s2'⟩
  · rintro ⟨i, l1, l2⟩ hx ⟨i', l1', l2'⟩ hx' he
    simp only [mem_sigma, mem_Ico, mem_product, mem_filter, mem_sepSet] at hx hx'
    obtain ⟨⟨hi1, hi2⟩, ⟨⟨hl1, s1⟩, np⟩, hl2, s2⟩ := hx
    obtain ⟨⟨hi1', hi2'⟩, ⟨⟨hl1', s1'⟩, np'⟩, hl2', s2'⟩ := hx'
    simp only at he
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · exact (key i l1 l2 i' l1' l2' hl1 s1 s2 hl1' s1' np' he hlt).elim
    · subst heq
      obtain ⟨rfl, rfl⟩ := List.append_inj he (by omega)
      rfl
    · exact (key i' l1' l2' i l1 l2 hl1' s1' s2' hl1 s1 np he.symm hgt).elim
  · intro b hb
    rw [mem_filter, mem_sepSet] at hb
    obtain ⟨⟨hblen, -⟩, hplus⟩ := hb
    have hex : ∃ k, ∃ l1 l2, b = l1 ++ l2 ∧ SepL l1 0 ∧ SepL l2 (0 + l1.length) ∧
        l1.length = k := by
      obtain ⟨l1, l2, h⟩ := hplus
      exact ⟨_, l1, l2, h.1, h.2.1, h.2.2, rfl⟩
    obtain ⟨l1, l2, hb, h1, h2, hk⟩ := Nat.find_spec hex
    have p1 := h1.length_pos
    have p2 := h2.length_pos
    have hlen : l1.length + l2.length = n := by
      rw [← hblen, hb, List.length_append]
    refine ⟨⟨l1.length, (l1, l2)⟩, ?_, hb.symm⟩
    simp only [mem_sigma, mem_Ico, mem_product, mem_filter, mem_sepSet]
    refine ⟨⟨by omega, by omega⟩, ⟨⟨trivial, h1⟩, ?_⟩, by omega, h2.cast (by omega)⟩
    rintro ⟨m1, m2, hm, g1, g2⟩
    have q2 := g2.length_pos
    have hl1len : l1.length = m1.length + m2.length := by
      rw [hm, List.length_append]
    refine Nat.find_min hex (m := m1.length) (by omega)
      ⟨m1, m2 ++ l2, ?_, g1, SepL.plus g2 (h2.cast (by omega)), rfl⟩
    rw [hb, hm, List.append_assoc]

/-! ### The recurrence -/

/-- Number of separable arrangements of `n` values. -/
def sN (n : ℕ) : ℕ := (sepSet n 0).card
/-- Those that are direct sums. -/
def bN (n : ℕ) : ℕ := ((sepSet n 0).filter (fun l => PlusDec l 0)).card
/-- Those that are not direct sums. -/
def uN (n : ℕ) : ℕ := ((sepSet n 0).filter (fun l => ¬PlusDec l 0)).card

theorem sN_eq (n : ℕ) : sN n = bN n + uN n :=
  (card_filter_add_card_filter_not _).symm

theorem uN_eq_bN (n : ℕ) (hn : 2 ≤ n) : uN n = bN n := by
  unfold uN bN
  rw [← card_minus_eq_plus]
  congr 1
  apply filter_congr
  intro l hl
  rw [mem_sepSet] at hl
  constructor
  · intro np
    rcases plus_or_minus hl.2 (by omega) with h | h
    · exact absurd h np
    · exact h
  · intro hm hp
    exact not_plus_and_minus ⟨hp, hm⟩

theorem uN_one : uN 1 = 1 := by
  unfold uN
  have : (sepSet 1 0).filter (fun l => ¬PlusDec l 0) = {[0]} := by
    ext l
    rw [mem_filter, mem_sepSet, mem_singleton]
    constructor
    · rintro ⟨⟨hlen, hs⟩, -⟩
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hlen
      have := (hs.mem_iff x).1 (by simp)
      simp only [List.length_singleton] at this
      obtain rfl : x = 0 := by omega
      rfl
    · rintro rfl
      refine ⟨⟨rfl, SepL.single 0⟩, fun hp => ?_⟩
      have := hp.two_le
      simp at this
  rw [this, card_singleton]

theorem bN_one : bN 1 = 0 := by
  unfold bN
  rw [card_eq_zero, filter_eq_empty_iff]
  intro l hl hp
  rw [mem_sepSet] at hl
  have := hp.two_le
  omega

theorem bN_eq (n : ℕ) : bN n = ∑ i ∈ Ico 1 n, uN i * sN (n - i) := card_plus n

private theorem largeSchroder_succ' (k : ℕ) : Nat.largeSchroder (k + 1) =
    Nat.largeSchroder k + ∑ i ∈ range (k + 1), Nat.largeSchroder i * Nat.largeSchroder (k - i) := by
  rw [Nat.largeSchroder_succ]
  congr 1
  apply sum_congr _ (fun _ _ => rfl)
  ext i
  simp

/-- Separable arrangements of `k + 1` values are counted by the large Schröder number. -/
theorem card_sepSet (k : ℕ) : (sepSet (k + 1) 0).card = Nat.largeSchroder k := by
  show sN (k + 1) = Nat.largeSchroder k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [sN_eq, bN_one, uN_one, Nat.largeSchroder_zero]
    | succ m =>
      have ih' : ∀ j, j ≤ m → sN (j + 1) = Nat.largeSchroder j := fun j hj => ih j (by omega)
      have e1 : sN (m + 1 + 1) = 2 * bN (m + 1 + 1) := by
        rw [sN_eq, uN_eq_bN _ (by omega)]
        ring
      have e2 : bN (m + 1 + 1) = ∑ j ∈ range (m + 1), uN (j + 1) * Nat.largeSchroder (m - j) := by
        rw [bN_eq, sum_Ico_eq_sum_range]
        apply sum_congr (by simp)
        intro j hj
        rw [mem_range] at hj
        rw [show 1 + j = j + 1 by ring, show m + 1 + 1 - (j + 1) = (m - j) + 1 by omega,
          ih' (m - j) (by omega)]
      have e3 : ∀ j, j < m → 2 * uN (j + 1 + 1) = Nat.largeSchroder (j + 1) := by
        intro j hj
        have := ih' (j + 1) (by omega)
        rw [sN_eq, uN_eq_bN _ (by omega)] at this
        rw [uN_eq_bN _ (by omega)]
        omega
      have e4 : ∑ j ∈ range m, 2 * (uN (j + 1 + 1) * Nat.largeSchroder (m - (j + 1))) =
          ∑ j ∈ range m, Nat.largeSchroder (j + 1) * Nat.largeSchroder (m - (j + 1)) := by
        apply sum_congr rfl
        intro j hj
        rw [mem_range] at hj
        rw [← mul_assoc, e3 j hj]
      rw [e1, e2, largeSchroder_succ' m, mul_sum, sum_range_succ', sum_range_succ', e4,
        show uN (0 + 1) = 1 from uN_one, Nat.largeSchroder_zero, Nat.sub_zero]
      ring

end PowerContamination
