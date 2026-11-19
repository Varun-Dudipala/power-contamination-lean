import PowerContamination.Defs

/-!
# Separable arrangements

`SepL l a` says that the list `l` is a separable arrangement of the consecutive values
`a, a+1, …, a + |l| - 1`: it is built from single values by direct sums (`plus`) and skew
sums (`minus`) of blocks whose value ranges are adjacent.
-/

namespace PowerContamination

inductive SepL : List ℕ → ℕ → Prop
  | single (a : ℕ) : SepL [a] a
  | plus {l1 l2 : List ℕ} {a : ℕ} : SepL l1 a → SepL l2 (a + l1.length) → SepL (l1 ++ l2) a
  | minus {l1 l2 : List ℕ} {a : ℕ} : SepL l1 (a + l2.length) → SepL l2 a → SepL (l1 ++ l2) a

namespace SepL

theorem cast {l : List ℕ} {a b : ℕ} (h : SepL l a) (e : a = b) : SepL l b := e ▸ h

theorem length_pos {l : List ℕ} {a : ℕ} (h : SepL l a) : 0 < l.length := by
  induction h with
  | single a => simp
  | plus _ _ ih1 _ => rw [List.length_append]; omega
  | minus _ _ ih1 _ => rw [List.length_append]; omega

theorem ne_nil {l : List ℕ} {a : ℕ} (h : SepL l a) : l ≠ [] :=
  List.ne_nil_of_length_pos h.length_pos

theorem perm {l : List ℕ} {a : ℕ} (h : SepL l a) : l.Perm (List.range' a l.length) := by
  induction h with
  | single a => simp
  | @plus l1 l2 a _ _ ih1 ih2 =>
    rw [List.length_append, ← List.range'_append_1]
    exact ih1.append ih2
  | @minus l1 l2 a _ _ ih1 ih2 =>
    rw [List.length_append, add_comm, ← List.range'_append_1]
    exact List.perm_append_comm.trans (ih2.append ih1)

theorem mem_iff {l : List ℕ} {a : ℕ} (h : SepL l a) (x : ℕ) :
    x ∈ l ↔ a ≤ x ∧ x < a + l.length := by
  rw [h.perm.mem_iff, List.mem_range'_1]

theorem nodup {l : List ℕ} {a : ℕ} (h : SepL l a) : l.Nodup :=
  h.perm.nodup_iff.2 List.nodup_range'

theorem shift {l : List ℕ} {a : ℕ} (h : SepL l a) (d : ℕ) :
    SepL (l.map (· + d)) (a + d) := by
  induction h with
  | single a => exact SepL.single (a + d)
  | @plus l1 l2 a _ _ ih1 ih2 =>
    rw [List.map_append]
    exact SepL.plus ih1 (ih2.cast (by rw [List.length_map]; omega))
  | @minus l1 l2 a _ _ ih1 ih2 =>
    rw [List.map_append]
    exact SepL.minus (ih1.cast (by rw [List.length_map]; omega)) ih2

theorem unshift {l : List ℕ} {b : ℕ} (h : SepL l b) :
    ∀ a d : ℕ, a + d = b → SepL (l.map (· - d)) a := by
  induction h with
  | single b =>
    intro a d hb
    have : b - d = a := by omega
    simpa [this] using SepL.single a
  | @plus l1 l2 b _ _ ih1 ih2 =>
    intro a d hb
    rw [List.map_append]
    exact SepL.plus (ih1 a d hb) (ih2 (a + (l1.map (· - d)).length) d
      (by rw [List.length_map]; omega))
  | @minus l1 l2 b _ _ ih1 ih2 =>
    intro a d hb
    rw [List.map_append]
    exact SepL.minus (ih1 (a + (l2.map (· - d)).length) d
      (by rw [List.length_map]; omega)) (ih2 a d hb)

/-- Complementing the values exchanges direct and skew sums. -/
theorem compl {l : List ℕ} {a : ℕ} (h : SepL l a) :
    ∀ N : ℕ, a + l.length ≤ N + 1 → SepL (l.map (fun x => N - x)) (N + 1 - (a + l.length)) := by
  induction h with
  | single a =>
    intro N hN
    simp only [List.length_singleton] at hN
    have : N + 1 - (a + 1) = N - a := by omega
    simpa [this] using SepL.single (N - a)
  | @plus l1 l2 a _ _ ih1 ih2 =>
    intro N hN
    rw [List.length_append] at hN
    rw [List.map_append]
    refine SepL.minus ((ih1 N (by omega)).cast ?_) ((ih2 N (by omega)).cast ?_)
    · rw [List.length_append, List.length_map]; omega
    · rw [List.length_append]; omega
  | @minus l1 l2 a _ _ ih1 ih2 =>
    intro N hN
    rw [List.length_append] at hN
    rw [List.map_append]
    refine SepL.plus ((ih1 N (by omega)).cast ?_) ((ih2 N (by omega)).cast ?_)
    · rw [List.length_append]; omega
    · rw [List.length_append, List.length_map]; omega

/-- A nonempty prefix whose values stay below `a + (its length)` is itself separable. -/
theorem of_prefix {l : List ℕ} {a : ℕ} (h : SepL l a) :
    ∀ m : List ℕ, m <+: l → m ≠ [] → (∀ x ∈ m, x < a + m.length) → SepL m a := by
  induction h with
  | single a =>
    intro m hm hne _
    have h1 : m.length ≤ 1 := by simpa using hm.length_le
    have h2 : 0 < m.length := List.length_pos_of_ne_nil hne
    have : m = [a] := hm.eq_of_length (by simp; omega)
    rw [this]
    exact SepL.single a
  | @plus l1 l2 a h1 h2 ih1 ih2 =>
    intro m hm hne hb
    rcases le_or_gt m.length l1.length with hle | hgt
    · exact ih1 m (List.prefix_of_prefix_length_le hm (List.prefix_append l1 l2) hle) hne hb
    · obtain ⟨r, rfl⟩ := List.prefix_of_prefix_length_le (List.prefix_append l1 l2) hm hgt.le
      rw [List.length_append] at hgt
      have hr : r ≠ [] := by
        intro e
        subst e
        simp at hgt
      have hr2 : r <+: l2 := (List.prefix_append_right_inj l1).1 hm
      refine SepL.plus h1 (ih2 r hr2 hr ?_)
      intro x hx
      have := hb x (List.mem_append_right l1 hx)
      rw [List.length_append] at this
      omega
  | @minus l1 l2 a h1 h2 ih1 ih2 =>
    intro m hm hne hb
    have hl2 := h2.length_pos
    rcases le_or_gt m.length l1.length with hle | hgt
    · exfalso
      have hm1 := ih1 m (List.prefix_of_prefix_length_le hm (List.prefix_append l1 l2) hle) hne
        (fun x hx => by have := hb x hx; omega)
      have hmpos := hm1.length_pos
      have hmem : a + l2.length + m.length - 1 ∈ m := (hm1.mem_iff _).2 (by omega)
      have := hb _ hmem
      omega
    · obtain ⟨r, rfl⟩ := List.prefix_of_prefix_length_le (List.prefix_append l1 l2) hm hgt.le
      have hr2 : r <+: l2 := (List.prefix_append_right_inj l1).1 hm
      have hl1 := h1.length_pos
      have hmem : a + l2.length + l1.length - 1 ∈ l1 := (h1.mem_iff _).2 (by omega)
      have := hb _ (List.mem_append_left r hmem)
      rw [List.length_append] at this
      have hlen : r.length = l2.length := le_antisymm hr2.length_le (by omega)
      rw [hr2.eq_of_length hlen]
      exact SepL.minus h1 h2

/-- The increasing arrangement is separable. -/
theorem range' : ∀ (n a : ℕ), 0 < n → SepL (List.range' a n) a
  | 0, _, h => by omega
  | 1, a, _ => by simpa using SepL.single a
  | n + 2, a, _ => by
    have h1 : SepL [a] a := SepL.single a
    have h2 := SepL.range' (n + 1) (a + 1) (by omega)
    have : List.range' a (n + 2) = [a] ++ List.range' (a + 1) (n + 1) := by
      simp [List.range'_succ]
    rw [this]
    exact SepL.plus h1 (by simpa using h2)

end SepL

end PowerContamination
