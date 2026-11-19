import PowerContamination.Encode

/-!
# Counting accepted words by length and weight

`W p s n m` is the number of words of length `n` and weight `m` accepted by the automaton
from the state (previous symbol `p`, witness flag `s`). The four functions `Tt, T0, U, U0`
are the states that matter; their values near the diagonal `2m = n` are computed.
-/

namespace PowerContamination

open Finset

@[simp] theorem Sym.O_beq_O : (Sym.O == Sym.O) = true := by decide
@[simp] theorem Sym.A_beq_O : (Sym.A == Sym.O) = false := by decide
@[simp] theorem Sym.B_beq_O : (Sym.B == Sym.O) = false := by decide
@[simp] theorem Sym.D_beq_O : (Sym.D == Sym.O) = false := by decide

/-- Words of weight `m` accepted from the state `(p, s)`. -/
def F (p : Sym) (s : Bool) (m : ℕ) (l : List Sym) : Bool := decide (weight l = m) && acc p s l

/-- Their number among the words of length `n`. -/
def W (p : Sym) (s : Bool) (n m : ℕ) : ℕ := cnt (F p s m) n

theorem W_zero (p : Sym) (s : Bool) (m : ℕ) :
    W p s 0 m = if m = 0 ∧ s = true ∧ p ≠ Sym.O then 1 else 0 := by
  unfold W
  rw [cnt_zero]
  have : (F p s m [] = true) ↔ (m = 0 ∧ s = true ∧ p ≠ Sym.O) := by
    simp only [F, acc, weight_nil, Bool.and_eq_true, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(of_decide_eq_true h1).symm, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨decide_eq_true h1.symm, h2, h3⟩
  simp only [this]

theorem W_succ (p : Sym) (s : Bool) (n m : ℕ) :
    W p s (n + 1) m =
      (if p = Sym.O then 0 else W Sym.O s n m) +
      (if 1 ≤ m then W Sym.A (s || p.bot) n (m - 1) + W Sym.B (s || p.top) n (m - 1) else 0) +
      (if 2 ≤ m then W Sym.D true n (m - 2) else 0) := by
  unfold W
  rw [cnt_succ]
  have hO : cnt (fun l => F p s m (Sym.O :: l)) n =
      if p = Sym.O then 0 else cnt (F Sym.O s m) n := by
    split_ifs with hp
    · rw [← cnt_false n]
      apply cnt_congr
      intro l
      subst hp
      simp [F, acc]
    · apply cnt_congr
      intro l
      cases p <;> simp_all [F, acc, Sym.top, Sym.bot, Sym.wt]
  have hA : cnt (fun l => F p s m (Sym.A :: l)) n =
      if 1 ≤ m then cnt (F Sym.A (s || p.bot) (m - 1)) n else 0 := by
    split_ifs with hm
    · apply cnt_congr
      intro l
      have : (1 + weight l = m) ↔ (weight l = m - 1) := by omega
      simp [F, acc, Sym.top, Sym.bot, Sym.wt, this]
    · rw [← cnt_false n]
      apply cnt_congr
      intro l
      have : ¬(1 + weight l = m) := by omega
      simp [F, acc, Sym.wt, this]
  have hB : cnt (fun l => F p s m (Sym.B :: l)) n =
      if 1 ≤ m then cnt (F Sym.B (s || p.top) (m - 1)) n else 0 := by
    split_ifs with hm
    · apply cnt_congr
      intro l
      have : (1 + weight l = m) ↔ (weight l = m - 1) := by omega
      simp [F, acc, Sym.top, Sym.bot, Sym.wt, this]
    · rw [← cnt_false n]
      apply cnt_congr
      intro l
      have : ¬(1 + weight l = m) := by omega
      simp [F, acc, Sym.wt, this]
  have hD : cnt (fun l => F p s m (Sym.D :: l)) n =
      if 2 ≤ m then cnt (F Sym.D true (m - 2)) n else 0 := by
    split_ifs with hm
    · apply cnt_congr
      intro l
      have : (2 + weight l = m) ↔ (weight l = m - 2) := by omega
      simp [F, acc, Sym.top, Sym.bot, Sym.wt, this]
    · rw [← cnt_false n]
      apply cnt_congr
      intro l
      have : ¬(2 + weight l = m) := by omega
      simp [F, acc, Sym.wt, this]
  rw [hO, hA, hB, hD]
  split_ifs <;> ring

/-! ### The four relevant states -/

theorem W_true_eq (p : Sym) (hp : p ≠ Sym.O) (n m : ℕ) : W p true n m = W Sym.A true n m := by
  cases n with
  | zero => simp [W_zero, hp]
  | succ n => simp [W_succ, hp]

theorem W_B_false : ∀ n m : ℕ, W Sym.B false n m = W Sym.A false n m := by
  intro n
  induction n with
  | zero => intro m; simp [W_zero]
  | succ n ih =>
    intro m
    rw [W_succ, W_succ]
    by_cases h1 : 1 ≤ m <;> by_cases h2 : 2 ≤ m <;>
      simp [Sym.top, Sym.bot, ih, W_true_eq Sym.B (by decide), h1, h2, add_comm]

/-- Witness seen, previous column occupied. -/
def Tt (n m : ℕ) : ℕ := W Sym.A true n m
/-- Witness seen, previous column empty. -/
def T0 (n m : ℕ) : ℕ := W Sym.O true n m
/-- No witness yet, previous column a single seed. -/
def U (n m : ℕ) : ℕ := W Sym.A false n m
/-- No witness yet, previous column empty (also the start state). -/
def U0 (n m : ℕ) : ℕ := W Sym.O false n m

theorem Tt_zero (m : ℕ) : Tt 0 m = if m = 0 then 1 else 0 := by simp [Tt, W_zero]
theorem T0_zero (m : ℕ) : T0 0 m = 0 := by simp [T0, W_zero]
theorem U_zero (m : ℕ) : U 0 m = 0 := by simp [U, W_zero]
theorem U0_zero (m : ℕ) : U0 0 m = 0 := by simp [U0, W_zero]

theorem Tt_succ (n m : ℕ) : Tt (n + 1) m =
    T0 n m + (if 1 ≤ m then 2 * Tt n (m - 1) else 0) + (if 2 ≤ m then Tt n (m - 2) else 0) := by
  unfold Tt T0
  rw [W_succ]
  by_cases h1 : 1 ≤ m <;> by_cases h2 : 2 ≤ m <;>
    simp [Sym.top, Sym.bot, W_true_eq Sym.B (by decide), W_true_eq Sym.D (by decide), h1, h2,
      two_mul]

theorem T0_succ (n m : ℕ) : T0 (n + 1) m =
    (if 1 ≤ m then 2 * Tt n (m - 1) else 0) + (if 2 ≤ m then Tt n (m - 2) else 0) := by
  unfold Tt T0
  rw [W_succ]
  by_cases h1 : 1 ≤ m <;> by_cases h2 : 2 ≤ m <;>
    simp [Sym.top, Sym.bot, W_true_eq Sym.B (by decide), W_true_eq Sym.D (by decide), h1, h2,
      two_mul]

theorem U_succ (n m : ℕ) : U (n + 1) m =
    U0 n m + (if 1 ≤ m then U n (m - 1) + Tt n (m - 1) else 0) +
      (if 2 ≤ m then Tt n (m - 2) else 0) := by
  unfold Tt U U0
  rw [W_succ]
  by_cases h1 : 1 ≤ m <;> by_cases h2 : 2 ≤ m <;>
    simp [Sym.top, Sym.bot, W_true_eq Sym.B (by decide), W_true_eq Sym.D (by decide), h1, h2]

theorem U0_succ (n m : ℕ) : U0 (n + 1) m =
    (if 1 ≤ m then 2 * U n (m - 1) else 0) + (if 2 ≤ m then Tt n (m - 2) else 0) := by
  unfold Tt U U0
  rw [W_succ]
  by_cases h1 : 1 ≤ m <;> by_cases h2 : 2 ≤ m <;>
    simp [Sym.top, Sym.bot, W_true_eq Sym.D (by decide), W_B_false, h1, h2, two_mul]

/-- Too few seeds: nothing is accepted. -/
theorem zero_region : ∀ n m : ℕ, (2 * m < n → Tt n m = 0) ∧ (2 * m ≤ n → T0 n m = 0) ∧
    (2 * m ≤ n → U n m = 0) ∧ (2 * m ≤ n + 1 → U0 n m = 0) := by
  intro n
  induction n with
  | zero =>
    intro m
    exact ⟨fun h => by omega, fun _ => T0_zero m, fun _ => U_zero m, fun _ => U0_zero m⟩
  | succ n ih =>
    intro m
    have a1 : ∀ m', 2 * m' < n → Tt n m' = 0 := fun m' => (ih m').1
    have a2 : ∀ m', 2 * m' ≤ n → T0 n m' = 0 := fun m' => (ih m').2.1
    have a3 : ∀ m', 2 * m' ≤ n → U n m' = 0 := fun m' => (ih m').2.2.1
    have a4 : ∀ m', 2 * m' ≤ n + 1 → U0 n m' = 0 := fun m' => (ih m').2.2.2
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have e1 : (if 1 ≤ m then 2 * Tt n (m - 1) else 0) = 0 := by
        split_ifs with h1
        · rw [a1 (m - 1) (by omega)]
        · rfl
      have e2 : (if 2 ≤ m then Tt n (m - 2) else 0) = 0 := by
        split_ifs with h2
        · exact a1 (m - 2) (by omega)
        · rfl
      rw [Tt_succ, a2 m (by omega), e1, e2]
    · have e1 : (if 1 ≤ m then 2 * Tt n (m - 1) else 0) = 0 := by
        split_ifs with h1
        · rw [a1 (m - 1) (by omega)]
        · rfl
      have e2 : (if 2 ≤ m then Tt n (m - 2) else 0) = 0 := by
        split_ifs with h2
        · exact a1 (m - 2) (by omega)
        · rfl
      rw [T0_succ, e1, e2]
    · have e1 : (if 1 ≤ m then U n (m - 1) + Tt n (m - 1) else 0) = 0 := by
        split_ifs with h1
        · rw [a3 (m - 1) (by omega), a1 (m - 1) (by omega)]
        · rfl
      have e2 : (if 2 ≤ m then Tt n (m - 2) else 0) = 0 := by
        split_ifs with h2
        · exact a1 (m - 2) (by omega)
        · rfl
      rw [U_succ, a4 m (by omega), e1, e2]
    · have e1 : (if 1 ≤ m then 2 * U n (m - 1) else 0) = 0 := by
        split_ifs with h1
        · rw [a3 (m - 1) (by omega)]
        · rfl
      have e2 : (if 2 ≤ m then Tt n (m - 2) else 0) = 0 := by
        split_ifs with h2
        · exact a1 (m - 2) (by omega)
        · rfl
      rw [U0_succ, e1, e2]

private theorem tail_zero (n m : ℕ) (hz : 2 * m < n + 2) :
    (if 2 ≤ m + 1 then Tt n (m + 1 - 2) else 0) = 0 := by
  split_ifs with h2
  · exact (zero_region n (m + 1 - 2)).1 (by omega)
  · rfl

theorem Tt_step (N M n m : ℕ) (hN : N = n + 1) (hM : M = m + 1) (hz : 2 * m < n + 2) :
    Tt N M = T0 n M + 2 * Tt n m := by
  subst hN hM
  rw [Tt_succ, tail_zero n m hz, if_pos (by omega), Nat.add_sub_cancel, add_zero]

theorem T0_step (N M n m : ℕ) (hN : N = n + 1) (hM : M = m + 1) (hz : 2 * m < n + 2) :
    T0 N M = 2 * Tt n m := by
  subst hN hM
  rw [T0_succ, tail_zero n m hz, if_pos (by omega), Nat.add_sub_cancel, add_zero]

theorem U_step (N M n m : ℕ) (hN : N = n + 1) (hM : M = m + 1) (hz : 2 * m < n + 2) :
    U N M = U0 n M + U n m + Tt n m := by
  subst hN hM
  rw [U_succ, tail_zero n m hz, if_pos (by omega), Nat.add_sub_cancel, add_zero, add_assoc]

theorem U0_step (N M n m : ℕ) (hN : N = n + 1) (hM : M = m + 1) (hz : 2 * m < n + 2) :
    U0 N M = 2 * U n m := by
  subst hN hM
  rw [U0_succ, tail_zero n m hz, if_pos (by omega), Nat.add_sub_cancel, add_zero]

theorem U0_step2 (N M n m m' : ℕ) (hN : N = n + 1) (hM : M = m + 2) (hm' : m' = m + 1) :
    U0 N M = 2 * U n m' + Tt n m := by
  subst hN hM hm'
  rw [U0_succ, if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel,
    show m + 2 - 1 = m + 1 by omega]

/-! ### Values near the diagonal -/

theorem Tt_diag : ∀ a : ℕ, Tt (2 * a) a = 2 ^ a
  | 0 => by
    show Tt 0 0 = 2 ^ 0
    rw [Tt_zero]
    rfl
  | a + 1 => by
    have h1 := Tt_step (2 * (a + 1)) (a + 1) (2 * a + 1) a (by ring) rfl (by omega)
    have h2 := T0_step (2 * a + 1) (a + 1) (2 * a) a rfl rfl (by omega)
    have h3 := (zero_region (2 * a + 1) a).1 (by omega)
    rw [h1, h2, h3, Tt_diag a]
    ring

theorem Tt_odd : ∀ a : ℕ, Tt (2 * a + 1) (a + 1) = (a + 1) * 2 ^ (a + 1)
  | 0 => by
    have h1 := Tt_step (2 * 0 + 1) (0 + 1) (2 * 0) 0 rfl rfl (by omega)
    have h2 : T0 (2 * 0) (0 + 1) = 0 := T0_zero _
    have h3 : Tt (2 * 0) 0 = 1 := Tt_diag 0
    rw [h1, h2, h3]
    norm_num
  | a + 1 => by
    have h1 := Tt_step (2 * (a + 1) + 1) (a + 1 + 1) (2 * (a + 1)) (a + 1) rfl rfl (by omega)
    have h2 := T0_step (2 * (a + 1)) (a + 1 + 1) (2 * a + 1) (a + 1) (by ring) rfl (by omega)
    rw [h1, h2, Tt_odd a, Tt_diag (a + 1)]
    ring

theorem U_odd : ∀ a : ℕ, U (2 * a + 1) (a + 1) = (a + 1) * 2 ^ a
  | 0 => by
    have h1 := U_step (2 * 0 + 1) (0 + 1) (2 * 0) 0 rfl rfl (by omega)
    have h2 : U0 (2 * 0) (0 + 1) = 0 := U0_zero _
    have h3 : U (2 * 0) 0 = 0 := U_zero _
    have h4 : Tt (2 * 0) 0 = 1 := Tt_diag 0
    rw [h1, h2, h3, h4]
    norm_num
  | a + 1 => by
    have h1 := U_step (2 * (a + 1) + 1) (a + 1 + 1) (2 * (a + 1)) (a + 1) rfl rfl (by omega)
    have h2 := U0_step (2 * (a + 1)) (a + 1 + 1) (2 * a + 1) (a + 1) (by ring) rfl (by omega)
    have h3 := (zero_region (2 * (a + 1)) (a + 1)).2.2.1 (by omega)
    rw [h1, h2, h3, U_odd a, Tt_diag (a + 1)]
    ring

theorem U_even : ∀ a : ℕ, 4 * U (2 * a) (a + 1) = a * (3 * a + 5) * 2 ^ a
  | 0 => by
    have h : U (2 * 0) (0 + 1) = 0 := U_zero _
    rw [h]
    norm_num
  | a + 1 => by
    have h1 := U_step (2 * (a + 1)) (a + 1 + 1) (2 * a + 1) (a + 1) (by ring) rfl (by omega)
    have h2 := U0_step2 (2 * a + 1) (a + 1 + 1) (2 * a) a (a + 1) rfl (by ring) rfl
    have ih := U_even a
    rw [h1, h2, U_odd a, Tt_odd a, Tt_diag a]
    calc 4 * (2 * U (2 * a) (a + 1) + 2 ^ a + (a + 1) * 2 ^ a + (a + 1) * 2 ^ (a + 1))
        = 2 * (4 * U (2 * a) (a + 1)) +
            4 * (2 ^ a + (a + 1) * 2 ^ a + (a + 1) * 2 ^ (a + 1)) := by ring
      _ = (a + 1) * (3 * (a + 1) + 5) * 2 ^ (a + 1) := by rw [ih]; ring

/-- The number of percolating words of length `2k+1` with `k+2` seeds. -/
theorem U0_main (k : ℕ) (hk : 1 ≤ k) :
    U0 (2 * k + 1) (k + 2) = (k + 1) * (3 * k + 2) * 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := U0_step2 (2 * (j + 1) + 1) (j + 1 + 2) (2 * (j + 1)) (j + 1) (j + 1 + 1) rfl rfl rfl
  have hU := U_even (j + 1)
  have hT := Tt_diag (j + 1)
  have e : 2 * U0 (2 * (j + 1) + 1) (j + 1 + 2) =
      2 * ((j + 1 + 1) * (3 * (j + 1) + 2) * 2 ^ j) := by
    rw [h, hT]
    calc 2 * (2 * U (2 * (j + 1)) (j + 1 + 1) + 2 ^ (j + 1))
        = 4 * U (2 * (j + 1)) (j + 1 + 1) + 2 * 2 ^ (j + 1) := by ring
      _ = 2 * ((j + 1 + 1) * (3 * (j + 1) + 2) * 2 ^ j) := by rw [hU]; ring
  rw [Nat.add_sub_cancel]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) e

/-- With at most `k+1` seeds no word of length `2k+1` percolates. -/
theorem U0_low (k m : ℕ) (hm : m ≤ k + 1) : U0 (2 * k + 1) m = 0 :=
  (zero_region (2 * k + 1) m).2.2.2 (by omega)

end PowerContamination
