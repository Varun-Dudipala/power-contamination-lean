import PowerContamination.Obstructions

/-!
# Two-row seed sets as words

A seed set on the `2 × w` grid is encoded by a word of length `w` over the alphabet
`O` (empty column), `A` (top cell only), `B` (bottom cell only), `D` (both cells).
Percolation becomes acceptance by a small automaton (`good`).
-/

namespace PowerContamination

/-- Column symbols. -/
inductive Sym
  | O | A | B | D
  deriving DecidableEq, Repr

namespace Sym

def top : Sym → Bool
  | A => true | D => true | _ => false

def bot : Sym → Bool
  | B => true | D => true | _ => false

def mk : Bool → Bool → Sym
  | false, false => O | true, false => A | false, true => B | true, true => D

def wt : Sym → ℕ
  | O => 0 | A => 1 | B => 1 | D => 2

@[simp] theorem top_mk (a b : Bool) : (mk a b).top = a := by cases a <;> cases b <;> rfl
@[simp] theorem bot_mk (a b : Bool) : (mk a b).bot = b := by cases a <;> cases b <;> rfl

theorem ext' {x y : Sym} (h1 : x.top = y.top) (h2 : x.bot = y.bot) : x = y := by
  cases x <;> cases y <;> simp_all [top, bot]

theorem eq_O_iff (x : Sym) : x = O ↔ x.top = false ∧ x.bot = false := by
  cases x <;> simp [top, bot]

theorem wt_eq (x : Sym) : x.wt = (if x.top then 1 else 0) + (if x.bot then 1 else 0) := by
  cases x <;> rfl

end Sym

/-- The automaton: `p` is the previous symbol, `s` records whether a full column or an
adjacent `AB`/`BA` pair has been seen. -/
def acc : Sym → Bool → List Sym → Bool
  | p, s, [] => s && (p != Sym.O)
  | p, s, x :: l => !(p == Sym.O && x == Sym.O) &&
      acc x (s || (x.top && x.bot) || (p.top && x.bot) || (p.bot && x.top)) l

/-- The words of percolating two-row sets. -/
def good (l : List Sym) : Bool := acc Sym.O false l

/-- Number of seeds of a word. -/
def weight (l : List Sym) : ℕ := (l.map Sym.wt).sum

@[simp] theorem weight_nil : weight [] = 0 := rfl
@[simp] theorem weight_cons (x : Sym) (l : List Sym) : weight (x :: l) = x.wt + weight l := by
  simp [weight]

/-- The word read off a column function, starting at column `j`. -/
def wordFrom (c : ℤ → Sym) : ℤ → ℕ → List Sym
  | _, 0 => []
  | j, n + 1 => c j :: wordFrom c (j + 1) n

@[simp] theorem wordFrom_length (c : ℤ → Sym) (n : ℕ) : ∀ j : ℤ, (wordFrom c j n).length = n := by
  induction n with
  | zero => intro j; rfl
  | succ n ih => intro j; simp [wordFrom, ih]

/-- A witness at column `i`: a full column, or seeds in different rows of columns `i-1, i`. -/
def Wit (c : ℤ → Sym) (i : ℤ) : Prop :=
  ((c i).top = true ∧ (c i).bot = true) ∨ ((c (i - 1)).top = true ∧ (c i).bot = true) ∨
    ((c (i - 1)).bot = true ∧ (c i).top = true)

private theorem notboth (a b : Sym) :
    (!(a == Sym.O && b == Sym.O)) = true ↔ ¬(a = Sym.O ∧ b = Sym.O) := by
  cases a <;> cases b <;> decide

theorem acc_iff (c : ℤ → Sym) (n : ℕ) : ∀ (j : ℤ) (s : Bool) (e : ℤ), e = j + n →
    (acc (c (j - 1)) s (wordFrom c j n) = true ↔
      (∀ i : ℤ, j - 1 ≤ i → i + 1 < e → ¬(c i = Sym.O ∧ c (i + 1) = Sym.O)) ∧
      c (e - 1) ≠ Sym.O ∧ (s = true ∨ ∃ i : ℤ, j ≤ i ∧ i < e ∧ Wit c i)) := by
  induction n with
  | zero =>
    intro j s e he
    obtain rfl : e = j := by simpa using he
    simp only [wordFrom, acc, Bool.and_eq_true, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨hs, hp⟩
      exact ⟨fun i h1 h2 => by omega, hp, Or.inl hs⟩
    · rintro ⟨-, hp, hs | ⟨i, h1, h2, -⟩⟩
      · exact ⟨hs, hp⟩
      · omega
  | succ n ih =>
    intro j s e he
    have he' : e = j + 1 + n := by push_cast at he; omega
    have IH := ih (j + 1) (s || ((c j).top && (c j).bot) || ((c (j - 1)).top && (c j).bot) ||
      ((c (j - 1)).bot && (c j).top)) e he'
    rw [show j + 1 - 1 = j by ring] at IH
    have hs' : (s || ((c j).top && (c j).bot) || ((c (j - 1)).top && (c j).bot) ||
        ((c (j - 1)).bot && (c j).top)) = true ↔ s = true ∨ Wit c j := by
      simp [Wit, or_assoc]
    have hstep : acc (c (j - 1)) s (wordFrom c j (n + 1)) =
        (!(c (j - 1) == Sym.O && c j == Sym.O) &&
          acc (c j) (s || ((c j).top && (c j).bot) || ((c (j - 1)).top && (c j).bot) ||
            ((c (j - 1)).bot && (c j).top)) (wordFrom c (j + 1) n)) := rfl
    rw [hstep, Bool.and_eq_true, notboth, IH, hs']
    constructor
    · rintro ⟨h0, h1, h2, h3⟩
      refine ⟨?_, h2, ?_⟩
      · intro i hi1 hi2
        rcases eq_or_lt_of_le hi1 with hi | hi
        · subst hi
          rw [show j - 1 + 1 = j by ring]
          exact h0
        · exact h1 i (by omega) hi2
      · rcases h3 with (h3 | h3) | ⟨i, a, b, cw⟩
        · exact Or.inl h3
        · exact Or.inr ⟨j, le_rfl, by omega, h3⟩
        · exact Or.inr ⟨i, by omega, b, cw⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, h2, ?_⟩
      · have := h1 (j - 1) le_rfl (by omega)
        rwa [show j - 1 + 1 = j by ring] at this
      · intro i a b
        exact h1 i (by omega) b
      · rcases h3 with h | ⟨i, a, b, cw⟩
        · exact Or.inl (Or.inl h)
        · rcases eq_or_lt_of_le a with rfl | a'
          · exact Or.inl (Or.inr cw)
          · exact Or.inr ⟨i, by omega, b, cw⟩

/-! ### Encoding seed sets -/

/-- The symbol of column `j` of a seed set. -/
def colType (S : Finset Cell) (j : ℤ) : Sym :=
  Sym.mk (decide (((0 : ℤ), j) ∈ S)) (decide (((1 : ℤ), j) ∈ S))

theorem colType_top (S : Finset Cell) (j : ℤ) : (colType S j).top = true ↔ ((0 : ℤ), j) ∈ S := by
  simp [colType]

theorem colType_bot (S : Finset Cell) (j : ℤ) : (colType S j).bot = true ↔ ((1 : ℤ), j) ∈ S := by
  simp [colType]

theorem colType_eq_O (S : Finset Cell) (j : ℤ) :
    colType S j = Sym.O ↔ ((0 : ℤ), j) ∉ S ∧ ((1 : ℤ), j) ∉ S := by
  rw [Sym.eq_O_iff]
  simp [colType]

theorem colType_ne_O (S : Finset Cell) (j : ℤ) :
    colType S j ≠ Sym.O ↔ ((0 : ℤ), j) ∈ S ∨ ((1 : ℤ), j) ∈ S := by
  rw [Ne, colType_eq_O]
  tauto

/-- The word of a seed set on the `2 × w` grid. -/
def enc (S : Finset Cell) (w : ℕ) : List Sym := wordFrom (colType S) 0 w

theorem wit_colType (S : Finset Cell) (i : ℤ) : Wit (colType S) i ↔
    ((((0 : ℤ), i) ∈ S ∧ ((1 : ℤ), i) ∈ S) ∨ (((0 : ℤ), i - 1) ∈ S ∧ ((1 : ℤ), i) ∈ S) ∨
      (((1 : ℤ), i - 1) ∈ S ∧ ((0 : ℤ), i) ∈ S)) := by
  simp only [Wit, colType_top, colType_bot]

theorem percolates_two_iff_good {w : ℕ} (hw : 0 < w) (S : Finset Cell)
    (hS : (↑S : Set Cell) ⊆ grid 2 w) :
    Percolates 2 w (↑S : Set Cell) ↔ good (enc S w) = true := by
  have hm1 : colType S (-1) = Sym.O := by
    rw [colType_eq_O]
    constructor <;> intro hmem <;>
    · have g := hS hmem
      rw [mem_grid] at g
      omega
  have hseed : ∀ c ∈ S, colType S c.2 ≠ Sym.O := by
    rintro ⟨c1, c2⟩ hc
    have g := hS hc
    rw [mem_grid] at g
    rw [colType_ne_O]
    obtain rfl | rfl : c1 = 0 ∨ c1 = 1 := by omega
    · exact Or.inl hc
    · exact Or.inr hc
  have key := acc_iff (colType S) w 0 false (w : ℤ) (by ring)
  rw [show (0 : ℤ) - 1 = -1 by norm_num, hm1] at key
  unfold good enc
  rw [key]
  constructor
  · intro hP
    refine ⟨?_, ?_, ?_⟩
    · rintro i hi1 hi2 ⟨hO1, hO2⟩
      rcases eq_or_lt_of_le hi1 with hi | hi
      · have hi' : i + 1 = 0 := by omega
        rw [hi'] at hO2
        refine not_percolates_of_blocked_cols hS {0} ?_ ?_ (c0 := (0, 0))
          (by rw [mem_grid]; omega) rfl hP
        · intro j hj
          simp only [Set.mem_singleton_iff] at hj ⊢
          omega
        · intro c hc hc0
          simp only [Set.mem_singleton_iff] at hc0
          exact hseed c hc (hc0 ▸ hO2)
      · refine not_percolates_of_blocked_cols hS {i, i + 1} ?_ ?_ (c0 := (0, i))
          (by rw [mem_grid]; omega) (by simp) hP
        · intro j hj
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj ⊢
          omega
        · intro c hc hc0
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc0
          rcases hc0 with hc0 | hc0
          · exact hseed c hc (hc0 ▸ hO1)
          · exact hseed c hc (hc0 ▸ hO2)
    · intro hO
      refine not_percolates_of_blocked_cols hS {(w : ℤ) - 1} ?_ ?_ (c0 := (0, (w : ℤ) - 1))
        (by rw [mem_grid]; omega) rfl hP
      · intro j hj
        simp only [Set.mem_singleton_iff] at hj ⊢
        omega
      · intro c hc hc0
        simp only [Set.mem_singleton_iff] at hc0
        exact hseed c hc (hc0 ▸ hO)
    · refine Or.inr ?_
      by_contra hno
      push Not at hno
      have hcol : ∀ {i j : ℤ}, (i, j) ∈ S → 0 ≤ j ∧ j < w := by
        intro i j hc
        have g := hS hc
        rw [mem_grid] at g
        omega
      refine not_percolates_two_of_no_witness hS hw ?_ ?_ ?_ hP
      · rintro j ⟨a, b⟩
        exact hno j (hcol a).1 (hcol a).2 ((wit_colType S j).2 (Or.inl ⟨a, b⟩))
      · rintro j j' hj ⟨a, b⟩
        refine hno j' (hcol b).1 (hcol b).2 ((wit_colType S j').2 (Or.inr (Or.inl ⟨?_, b⟩)))
        rwa [show j' - 1 = j by omega]
      · rintro j j' hj ⟨a, b⟩
        refine hno j' (hcol b).1 (hcol b).2 ((wit_colType S j').2 (Or.inr (Or.inr ⟨?_, b⟩)))
        rwa [show j' - 1 = j by omega]
  · rintro ⟨h1, h2, h3⟩
    refine percolates_two_of_witness hS ?_ ?_ ?_ ?_
    · have := h1 (-1) le_rfl (by omega)
      rw [hm1, show (-1 : ℤ) + 1 = 0 by norm_num] at this
      exact (colType_ne_O S 0).1 (fun h => this ⟨rfl, h⟩)
    · exact (colType_ne_O S _).1 h2
    · intro j j' hj hj' hlt
      subst hj'
      have := h1 j (by omega) hlt
      by_contra hcon
      push Not at hcon
      exact this ⟨(colType_eq_O S j).2 hcon.1, (colType_eq_O S (j + 1)).2 hcon.2⟩
    · rcases h3 with h3 | ⟨i, -, -, hw'⟩
      · exact absurd h3 (by decide)
      · exact ⟨i - 1, i, by ring, (wit_colType S i).1 hw'⟩

end PowerContamination
