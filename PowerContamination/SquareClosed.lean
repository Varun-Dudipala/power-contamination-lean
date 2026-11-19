import PowerContamination.SquareFill

/-!
# Percolating permutation seeds are separable

Cut the positions into consecutive blocks, each a separable arrangement of consecutive
values, using as few blocks as possible. If there is more than one block, the union of
the block rectangles is closed and misses a column, so the seeds do not percolate.
-/

namespace PowerContamination

open Finset

/-- The entries of `l` at positions `p, …, q-1`. -/
def slice (l : List ℕ) (p q : ℕ) : List ℕ := (l.drop p).take (q - p)

theorem slice_length {l : List ℕ} {p q : ℕ} (hq : q ≤ l.length) :
    (slice l p q).length = q - p := by
  simp only [slice, List.length_take, List.length_drop]
  omega

theorem slice_append {l : List ℕ} {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) :
    slice l p q ++ slice l q r = slice l p r := by
  unfold slice
  have e1 : r - p = (q - p) + (r - q) := by omega
  have e2 : l.drop q = (l.drop p).drop (q - p) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [e1, List.take_add, e2]

theorem slice_getD {l : List ℕ} {p q s : ℕ} (hs : s < q - p) :
    (slice l p q).getD s 0 = l.getD (p + s) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  unfold slice
  rw [List.getElem?_take_of_lt hs, List.getElem?_drop]

theorem mem_slice {l : List ℕ} {p q t : ℕ} (hp : p ≤ t) (ht : t < q) (hq : q ≤ l.length) :
    l.getD t 0 ∈ slice l p q := by
  have h1 : t - p < (slice l p q).length := by rw [slice_length hq]; omega
  have h2 := slice_getD (l := l) (p := p) (q := q) (s := t - p) (by omega)
  rw [show p + (t - p) = t by omega] at h2
  rw [← h2, List.getD_eq_getElem _ _ h1]
  exact List.getElem_mem h1

theorem exists_of_mem_slice {l : List ℕ} {p q x : ℕ} (hq : q ≤ l.length)
    (hx : x ∈ slice l p q) : ∃ t, p ≤ t ∧ t < q ∧ x = l.getD t 0 := by
  obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.1 hx
  have hs' := hs
  rw [slice_length hq] at hs'
  refine ⟨p + s, by omega, by omega, ?_⟩
  rw [← slice_getD hs', List.getD_eq_getElem _ _ hs]

theorem getD_inj {l : List ℕ} (hnd : l.Nodup) {t t' : ℕ} (ht : t < l.length)
    (ht' : t' < l.length) (h : l.getD t 0 = l.getD t' 0) : t = t' := by
  rw [List.getD_eq_getElem _ _ ht, List.getD_eq_getElem _ _ ht'] at h
  exact (List.Nodup.getElem_inj_iff hnd).1 h

/-- `p < q` are neighbouring cuts. -/
def Consec (C : Finset ℕ) (p q : ℕ) : Prop :=
  p ∈ C ∧ q ∈ C ∧ p < q ∧ ∀ x ∈ C, ¬(p < x ∧ x < q)

/-- A set of cuts all of whose blocks are separable arrangements of consecutive values. -/
def Valid (l : List ℕ) (C : Finset ℕ) : Prop :=
  0 ∈ C ∧ l.length ∈ C ∧ (∀ x ∈ C, x ≤ l.length) ∧
    ∀ p q, Consec C p q → ∃ a, SepL (slice l p q) a

theorem valid_range (l : List ℕ) : Valid l (range (l.length + 1)) := by
  refine ⟨by simp, by simp, fun x hx => by rw [mem_range] at hx; omega, ?_⟩
  rintro p q ⟨hp, hq, hpq, hbetween⟩
  rw [mem_range] at hp hq
  have hq' : q = p + 1 := by
    by_contra hne
    exact hbetween (p + 1) (by rw [mem_range]; omega) ⟨by omega, by omega⟩
  subst hq'
  have hlen : (slice l p (p + 1)).length = 1 := by rw [slice_length (by omega)]; omega
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hlen
  exact ⟨x, hx ▸ SepL.single x⟩

theorem consec_cover {C : Finset ℕ} {n : ℕ} (h0 : 0 ∈ C) (hn : n ∈ C) {t : ℕ} (ht : t < n) :
    ∃ p q, Consec C p q ∧ p ≤ t ∧ t < q := by
  have hA : (C.filter (· ≤ t)).Nonempty := ⟨0, by simp [h0]⟩
  have hB : (C.filter (t < ·)).Nonempty := ⟨n, by simp [hn, ht]⟩
  have hp := (C.filter (· ≤ t)).max'_mem hA
  have hq := (C.filter (t < ·)).min'_mem hB
  rw [mem_filter] at hp hq
  refine ⟨_, _, ⟨hp.1, hq.1, by omega, ?_⟩, hp.2, hq.2⟩
  rintro x hx ⟨h1, h2⟩
  by_cases hxt : x ≤ t
  · have := Finset.le_max' (C.filter (· ≤ t)) x (by rw [mem_filter]; exact ⟨hx, hxt⟩)
    omega
  · have := Finset.min'_le (C.filter (t < ·)) x (by rw [mem_filter]; exact ⟨hx, by omega⟩)
    omega

theorem valid_erase {l : List ℕ} {C : Finset ℕ} {p q r : ℕ} (hC : Valid l C)
    (h1 : Consec C p q) (h2 : Consec C q r) (hm : ∃ a, SepL (slice l p r) a) :
    Valid l (C.erase q) := by
  obtain ⟨c0, cn, cb, cs⟩ := hC
  obtain ⟨hp, hq, hpq, hpq'⟩ := h1
  obtain ⟨-, hr, hqr, hqr'⟩ := h2
  have hrn := cb r hr
  refine ⟨mem_erase.2 ⟨by omega, c0⟩, mem_erase.2 ⟨by omega, cn⟩,
    fun x hx => cb x (mem_of_mem_erase hx), ?_⟩
  rintro x y ⟨hx, hy, hxy, hbet⟩
  rw [mem_erase] at hx hy
  by_cases hmid : x < q ∧ q < y
  · have hxp : x = p := by
      have h1 : x ≤ p := by
        by_contra h
        exact hpq' x hx.2 ⟨by omega, hmid.1⟩
      have h2 : ¬(x < p ∧ p < y) := hbet p (mem_erase.2 ⟨by omega, hp⟩)
      omega
    have hyr : y = r := by
      have h1 : r ≤ y := by
        by_contra h
        exact hqr' y hy.2 ⟨hmid.2, by omega⟩
      have h2 : ¬(x < r ∧ r < y) := hbet r (mem_erase.2 ⟨by omega, hr⟩)
      omega
    subst hxp hyr
    exact hm
  · refine cs x y ⟨hx.2, hy.2, hxy, ?_⟩
    intro z hz hz'
    by_cases hzq : z = q
    · subst hzq
      exact hmid hz'
    · exact hbet z (mem_erase.2 ⟨hzq, hz⟩) hz'

/-- The cell `(i, j)` lies in the rectangle of the block with positions `p, …, q-1` and
values `a, …, a + (q - p) - 1`. -/
abbrev InRect (p q a : ℕ) (i j : ℤ) : Prop :=
  2 * (a : ℤ) ≤ i ∧ i ≤ 2 * ((a : ℤ) + ((q - p : ℕ) : ℤ)) - 2 ∧ 2 * (p : ℤ) ≤ j ∧
    j ≤ 2 * (q : ℤ) - 2

theorem sepL_of_percolates {l : List ℕ} (hpos : 0 < l.length) (hnd : l.Nodup)
    (hP : Percolates (2 * l.length - 1) (2 * l.length - 1) (↑(seeds l) : Set Cell)) :
    ∃ a, SepL l a := by
  classical
  have hex : ∃ m, ∃ C, Valid l C ∧ C.card = m := ⟨_, _, valid_range l, rfl⟩
  obtain ⟨C, hC, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ C', Valid l C' → C.card ≤ C'.card := fun C' hC' =>
    hcard ▸ Nat.find_min' hex ⟨C', hC', rfl⟩
  obtain ⟨c0, cn, cb, cs⟩ := id hC
  by_cases hint : ∃ q ∈ C, 0 < q ∧ q < l.length
  · exfalso
    obtain ⟨q0, hq0, hq0pos, hq0n⟩ := hint
    have nomerge : ∀ x y z a1 a2, Consec C x y → Consec C y z → SepL (slice l x y) a1 →
        SepL (slice l y z) a2 → a2 ≠ a1 + (y - x) ∧ a1 ≠ a2 + (z - y) := by
      intro x y z a1 a2 hxy hyz s1 s2
      have hzn := cb z hyz.2.1
      have hyz' := hyz.2.2.1
      have hlen1 : (slice l x y).length = y - x := slice_length (by omega)
      have hlen2 : (slice l y z).length = z - y := slice_length hzn
      have happ := slice_append (l := l) hxy.2.2.1.le hyz.2.2.1.le
      have hbad : (∃ a, SepL (slice l x z) a) → False := by
        intro hm
        have hv := valid_erase hC hxy hyz hm
        have h1 := hmin _ hv
        rw [card_erase_of_mem hxy.2.1] at h1
        have h2 : 0 < C.card := card_pos.2 ⟨_, c0⟩
        omega
      constructor
      · intro e
        refine hbad ⟨a1, ?_⟩
        rw [← happ]
        exact SepL.plus s1 (s2.cast (by rw [hlen1]; exact e))
      · intro e
        refine hbad ⟨a2, ?_⟩
        rw [← happ]
        exact SepL.minus (s1.cast (by rw [hlen2]; exact e)) s2
    let U : Set Cell :=
      {c | ∃ p q a, Consec C p q ∧ SepL (slice l p q) a ∧ InRect p q a c.1 c.2}
    have memU : ∀ i j : ℤ, (i, j) ∈ U ↔
        ∃ p q a, Consec C p q ∧ SepL (slice l p q) a ∧ InRect p q a i j := fun i j => Iff.rfl
    have far : ∀ p q a p' q' a' (i j i' j' : ℤ), Consec C p q → Consec C p' q' →
        SepL (slice l p q) a → SepL (slice l p' q') a' → q ≤ p' → InRect p q a i j →
        InRect p' q' a' i' j' →
        j + 2 ≤ j' ∧ (i + 2 ≤ i' ∨ i' + 2 ≤ i) ∧ ¬(j + 2 = j' ∧ (i + 2 = i' ∨ i' + 2 = i)) := by
      intro p q a p' q' a' i j i' j' hc hc' s s' hqp ⟨r1, r2, r3, r4⟩ ⟨r1', r2', r3', r4'⟩
      have hqn := cb q hc.2.1
      have hqn' := cb q' hc'.2.1
      have hlen : (slice l p q).length = q - p := slice_length hqn
      have hlen' : (slice l p' q').length = q' - p' := slice_length hqn'
      have hpq := hc.2.2.1
      have hpq' := hc'.2.2.1
      have hdisj : a + (q - p) ≤ a' ∨ a' + (q' - p') ≤ a := by
        by_contra hcon
        push Not at hcon
        have m1 : max a a' ∈ slice l p q := (s.mem_iff _).2 (by rw [hlen]; omega)
        have m2 : max a a' ∈ slice l p' q' := (s'.mem_iff _).2 (by rw [hlen']; omega)
        obtain ⟨t, ht1, ht2, ht3⟩ := exists_of_mem_slice hqn m1
        obtain ⟨t', ht1', ht2', ht3'⟩ := exists_of_mem_slice hqn' m2
        have := getD_inj hnd (by omega) (by omega) (ht3.symm.trans ht3')
        omega
      refine ⟨by omega, by omega, ?_⟩
      rintro ⟨e1, e2⟩
      have hq_eq : p' = q := by omega
      subst hq_eq
      have nm := nomerge p p' q' a a' hc hc' s s'
      rcases hdisj with hd | hd
      · exact nm.1 (by omega)
      · exact nm.2 (by omega)
    have pairU : ∀ i j i' j' : ℤ, (i, j) ∈ U → (i', j') ∈ U →
        (∃ p q a, Consec C p q ∧ SepL (slice l p q) a ∧ InRect p q a i j ∧
          InRect p q a i' j') ∨
        ((j + 2 ≤ j' ∨ j' + 2 ≤ j) ∧ (i + 2 ≤ i' ∨ i' + 2 ≤ i) ∧
          ¬((j + 2 = j' ∨ j' + 2 = j) ∧ (i + 2 = i' ∨ i' + 2 = i))) := by
      intro i j i' j' hu hv
      rw [memU] at hu hv
      obtain ⟨p, q, a, hc, s, hr⟩ := hu
      obtain ⟨p', q', a', hc', s', hr'⟩ := hv
      have tri : (p = p' ∧ q = q') ∨ q ≤ p' ∨ q' ≤ p := by
        obtain ⟨hp, hq, hpq, hb⟩ := hc
        obtain ⟨hp', hq', hpq', hb'⟩ := hc'
        have h1 := hb p' hp'
        have h2 := hb' p hp
        have h3 := hb q' hq'
        have h4 := hb' q hq
        omega
      rcases tri with ⟨rfl, rfl⟩ | h | h
      · left
        have hsp := s.length_pos
        have hsp' := s'.length_pos
        have h1 := (s.mem_iff a').1 ((s'.mem_iff a').2 ⟨le_rfl, by omega⟩)
        have h2 := (s'.mem_iff a).1 ((s.mem_iff a).2 ⟨le_rfl, by omega⟩)
        obtain rfl : a = a' := by omega
        exact ⟨p, q, a, hc, s, hr, hr'⟩
      · right
        have := far p q a p' q' a' i j i' j' hc hc' s s' h hr hr'
        omega
      · right
        have := far p' q' a' p q a i' j' i j hc' hc s' s h hr' hr
        omega
    have hUclosed : Closed (2 * l.length - 1) (2 * l.length - 1) U := by
      rw [closed_iff]
      intro i j hg
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h1 h2 <;>
        rcases pairU _ _ _ _ h1 h2 with
          ⟨p, q, a, hc, s, ⟨r1, r2, r3, r4⟩, ⟨r1', r2', r3', r4'⟩⟩ | hfar
      all_goals first
        | exact (memU i j).2 ⟨p, q, a, hc, s, by omega, by omega, by omega, by omega⟩
        | (exfalso; omega)
    have hsub : (↑(seeds l) : Set Cell) ⊆ U := by
      intro c hc
      rw [mem_coe, mem_seeds] at hc
      obtain ⟨t, ht, rfl⟩ := hc
      obtain ⟨p, q, hc', hpt, htq⟩ := consec_cover c0 cn ht
      obtain ⟨a, s⟩ := cs p q hc'
      have hqn := cb q hc'.2.1
      have hm := (s.mem_iff _).1 (mem_slice hpt htq hqn)
      rw [slice_length hqn] at hm
      exact (memU _ _).2 ⟨p, q, a, hc', s, by omega, by omega, by omega, by omega⟩
    have hgrid := (percolates_iff.1 hP) U hsub hUclosed
    have hcell : ((0 : ℤ), 2 * (q0 : ℤ) - 1) ∈ U := hgrid (by rw [mem_grid]; omega)
    rw [memU] at hcell
    obtain ⟨p, q, a, hc, s, r1, r2, r3, r4⟩ := hcell
    exact hc.2.2.2 q0 hq0 ⟨by omega, by omega⟩
  · have hcon : Consec C 0 l.length :=
      ⟨c0, cn, hpos, fun x hx hx' => hint ⟨x, hx, hx'.1, hx'.2⟩⟩
    obtain ⟨a, s⟩ := cs 0 l.length hcon
    have e : slice l 0 l.length = l := by simp [slice]
    rw [e] at s
    exact ⟨a, s⟩

end PowerContamination
