import GurvichNaumova.Basic

open Finset

namespace GN

/-- The reflection `T - D` of a set `D ⊆ [1, T - 1]`. -/
def refl (T : ℤ) (D : Finset ℤ) : Finset ℤ := (Icc 1 (T - 1)).filter (fun x => T - x ∈ D)

/-- Assembly: `[1, T + j] \ Tri` splits as the pairs `{x, T - x}` avoiding `D ∪ (T - D)`,
the part `F` of `D` not hit by the reflection, and the rest `R` around `T`. -/
theorem assembly (T : ℤ) (t : ℕ) (hT : T = 3 ^ t) (j : ℤ) (hj : 0 ≤ j) (D Tri : Finset ℤ)
    (hD : ∀ x ∈ D, 1 ≤ x ∧ x ≤ T - 1)
    (hTri : ∀ x ∈ Tri, (T + 1 ≤ x ∧ x ≤ T + j) ∨ (1 ≤ x ∧ x ≤ T - 1 ∧ T - x ∈ D))
    (hR : Good ((insert T (Icc (T + 1) (T + j) ∪ refl T D)) \ Tri))
    (hF : Good (D.filter (fun x => T - x ∉ D))) :
    Good (Icc 1 (T + j) \ Tri) := by
  have hT1 : 1 ≤ T := by rw [hT]; exact one_le_pow₀ (by norm_num)
  set E := (Icc 1 (T - 1)).filter (fun x => x ∉ D ∧ T - x ∉ D) with hE
  have hEg : Good E := by
    refine good_of_symm T t hT E.card E rfl ?_
    intro x hx
    simp only [hE, mem_filter, mem_Icc] at hx ⊢
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, ?_, ?_⟩
    · exact hx.2.2
    · rw [sub_sub_cancel]; exact hx.2.1
  have heq : Icc 1 (T + j) \ Tri = E ∪ (D.filter (fun x => T - x ∉ D) ∪
      ((insert T (Icc (T + 1) (T + j) ∪ refl T D)) \ Tri)) := by
    ext x
    have a1 := hD x
    have a2 := hD (T - x)
    have a3 := hTri x
    simp only [mem_sdiff, mem_Icc, mem_union, mem_filter, mem_insert, refl, hE]
    by_cases p1 : x ∈ D <;> by_cases p2 : T - x ∈ D <;> by_cases p3 : x ∈ Tri <;>
      simp only [p1, p2, p3, true_implies, false_implies, not_true_eq_false,
        not_false_eq_true, and_true, and_false, or_false, false_or, or_true, true_or,
        iff_true, false_iff] at a1 a2 a3 ⊢ <;> omega
  rw [heq]
  refine Good.union hEg (Good.union hF hR ?_) ?_
  · rw [disjoint_left]
    intro x hx hx'
    simp only [mem_filter] at hx
    simp only [mem_sdiff, mem_insert, mem_union, mem_Icc, refl, mem_filter] at hx'
    have := hD x hx.1
    rcases hx'.1 with h | h | h
    · omega
    · omega
    · exact hx.2 h.2
  · rw [disjoint_left]
    intro x hx hx'
    simp only [hE, mem_filter, mem_Icc] at hx
    simp only [mem_union, mem_filter, mem_sdiff, mem_insert, mem_Icc, refl] at hx'
    rcases hx' with h | ⟨h | h | h, _⟩
    · exact hx.2.1 h.1
    · omega
    · omega
    · exact hx.2.2 h.2

/-- The case `j = 2`. -/
theorem case_two (T : ℤ) (t : ℕ) (hT : T = 3 ^ t) (h9 : 9 ≤ T) :
    Good (Icc 1 (T + 2) \ {T + 2 - 1, T + 2, T - 2 * 2 + 1}) := by
  refine assembly T t hT 2 (by norm_num) {3} _ ?_ ?_ ?_ ?_
  · intro x hx; simp only [mem_singleton] at hx; omega
  · intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; omega
  · have : (insert T (Icc (T + 1) (T + 2) ∪ refl T {3})) \ {T + 2 - 1, T + 2, T - 2 * 2 + 1} =
        {T} := by
      ext x; simp only [mem_sdiff, mem_insert, mem_union, mem_Icc, refl, mem_filter,
        mem_singleton]; omega
    rw [this]; exact Good.single T t hT
  · have : ({3} : Finset ℤ).filter (fun x => T - x ∉ ({3} : Finset ℤ)) = {3} := by
      ext x; simp only [mem_filter, mem_singleton]; omega
    rw [this]; exact Good.single 3 1 (by norm_num)

/-- The cases B and A1: offsets `(j - 1, j, -(2j - 1))` and Lemma 1 on `[-(j - 2), j - 2]`. -/
theorem case_BA1 (T : ℤ) (t : ℕ) (hT : T = 3 ^ t) (j : ℤ) (hj : 5 ≤ j) (hj3 : j % 3 = 2)
    (hjT : 2 * j + 1 ≤ T)
    (hF : Good ((insert (2 * j - 1) (Icc 1 (j - 2))).filter
      (fun x => T - x ∉ insert (2 * j - 1) (Icc 1 (j - 2))))) :
    Good (Icc 1 (T + j) \ {T + j - 1, T + j, T - 2 * j + 1}) := by
  refine assembly T t hT j (by omega) _ _ ?_ ?_ ?_ hF
  · intro x hx; simp only [mem_insert, mem_Icc] at hx; omega
  · intro x hx; simp only [mem_insert, mem_singleton, mem_Icc] at hx ⊢; omega
  · have : (insert T (Icc (T + 1) (T + j) ∪ refl T (insert (2 * j - 1) (Icc 1 (j - 2))))) \
        {T + j - 1, T + j, T - 2 * j + 1} = (Icc (-(j - 2)) (j - 2)).image (fun x => T + 1 * x) := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_union, mem_Icc, refl, mem_filter, mem_singleton,
        mem_image]
      constructor
      · intro h; exact ⟨x - T, by omega, by omega⟩
      · rintro ⟨y, hy, rfl⟩; omega
    rw [this]
    exact (zs_Icc (j - 2) (by omega) (by omega)).good T 1 t hT one_ne_zero

end GN
