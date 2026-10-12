import GurvichNaumova.Basic

open Finset

namespace GN

theorem ZS.scale {S : Finset ℤ} (hS : ZS S) (s : ℤ) (hs : s ≠ 0) :
    ZS (S.image (fun x => s * x)) := by
  have hinj : Function.Injective (fun x : ℤ => s * x) := fun x y h => mul_left_cancel₀ hs h
  induction hS with
  | empty => simpa using ZS.empty
  | zero => simpa using ZS.zero
  | triple hab hac hbc h =>
    rename_i a b c
    simp only [image_insert, image_singleton]
    refine ZS.triple (fun e => hab (hinj e)) (fun e => hac (hinj e)) (fun e => hbc (hinj e)) ?_
    have : s * a + s * b + s * c = s * (a + b + c) := by ring
    rw [this, h, mul_zero]
  | union _ _ hd ihA ihB =>
    rw [image_union]
    exact ZS.union ihA ihB ((disjoint_image hinj).2 hd)

/-- The even integers in `[-2L, 2L]`. -/
theorem zs_even (L : ℤ) (hL : 0 ≤ L) (h3 : L % 3 ≠ 2) :
    ZS ((Icc (-(2 * L)) (2 * L)).filter (fun d => d % 2 = 0)) := by
  have heq : (Icc (-(2 * L)) (2 * L)).filter (fun d => d % 2 = 0) =
      (Icc (-L) L).image (fun x => 2 * x) := by
    ext d
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨d / 2, by omega, by omega⟩
    · rintro ⟨x, hx, rfl⟩
      omega
  rw [heq]
  exact (zs_Icc L hL h3).scale 2 (by norm_num)

/-! ## Perfect matchings of `[1, K]` given by involutions -/

/-- The smaller element of each pair of the matching `σ` of `[1, K]`. -/
def Sig0 (σ : ℤ → ℤ) (K : ℤ) : Finset ℤ := (Icc 1 K).filter (fun z => z < σ z)

/-- The data required of the pairing of `[1, 2N - 2]` used in the main construction. -/
def Gadget (N : ℤ) (σ : ℤ → ℤ) : Prop :=
  (∀ x ∈ Icc 1 (2 * N - 2), σ x ∈ Icc 1 (2 * N - 2)) ∧
  (∀ x ∈ Icc 1 (2 * N - 2), σ (σ x) = x) ∧
  (∀ x ∈ Icc 1 (2 * N - 2), σ x ≠ x) ∧
  (∀ x ∈ Icc 1 (2 * N - 2), ∀ y ∈ Icc 1 (2 * N - 2), x < σ x → y < σ y →
      x + σ x = y + σ y → x = y) ∧
  ZS (insert (2 * N - 2) ((Sig0 σ (2 * N - 2)).image (fun z => z + σ z - (2 * N + 1)))) ∧
  (∀ z ∈ Sig0 σ (2 * N - 2), 0 < z + σ z - (2 * N + 1) → (z + σ z - (2 * N + 1)) % 2 = 0)

/-- The pairing for even `N`. -/
def sigE (N x : ℤ) : ℤ :=
  if x = 1 then N else if x = N then 1 else if x = 2 then N + 1 else if x = N + 1 then 2
  else if x ≤ N - 1 then x + N - 1 else x - (N - 1)

/-- The pairing for odd `N ≥ 7`. -/
def sigO (N x : ℤ) : ℤ :=
  if x = 1 then N else if x = N then 1 else if x = 2 then N + 1 else if x = N + 1 then 2
  else if x = 2 * N - 3 then 2 * N - 2 else if x = 2 * N - 2 then 2 * N - 3
  else if x = 3 then N - 1 else if x = N - 1 then 3 else if x = 4 then N + 2
  else if x = N + 2 then 4 else if x ≤ N - 2 then x + N - 2 else x - (N - 2)

theorem gadget_one : Gadget 1 id := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; exfalso; simp only [mem_Icc] at hx; omega
  · intro x hx; exfalso; simp only [mem_Icc] at hx; omega
  · intro x hx; exfalso; simp only [mem_Icc] at hx; omega
  · intro x hx; exfalso; simp only [mem_Icc] at hx; omega
  · have : Sig0 id (2 * 1 - 2) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro x hx
      simp only [Sig0, mem_filter, mem_Icc] at hx; omega
    rw [this]; simpa using ZS.zero
  · intro z hz; exfalso; simp only [Sig0, mem_filter, mem_Icc] at hz; omega

theorem sigE_spec (N x : ℤ) (hN : 4 ≤ N) (hx1 : 1 ≤ x) (hx2 : x ≤ 2 * N - 2) :
    (x = 1 ∧ sigE N x = N) ∨ (x = N ∧ sigE N x = 1) ∨ (x = 2 ∧ sigE N x = N + 1) ∨
    (x = N + 1 ∧ sigE N x = 2) ∨ (3 ≤ x ∧ x ≤ N - 1 ∧ sigE N x = x + N - 1) ∨
    (N + 2 ≤ x ∧ x ≤ 2 * N - 2 ∧ sigE N x = x - (N - 1)) := by
  unfold sigE; split_ifs <;> omega

theorem gadget_even (M : ℤ) (hM : 2 ≤ M) (h3 : M % 3 = 2) : Gadget (2 * M) (sigE (2 * M)) := by
  have sp := fun x (h1 : 1 ≤ x) (h2 : x ≤ 2 * (2 * M) - 2) => sigE_spec (2 * M) x (by omega) h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp only [mem_Icc] at hx ⊢; have := sp x hx.1 hx.2; omega
  · intro x hx; simp only [mem_Icc] at hx
    have h1 := sp x hx.1 hx.2
    have h2 := sp (sigE (2 * M) x) (by omega) (by omega)
    omega
  · intro x hx; simp only [mem_Icc] at hx; have := sp x hx.1 hx.2; omega
  · intro x hx y hy; simp only [mem_Icc] at hx hy
    have h1 := sp x hx.1 hx.2
    have h2 := sp y hy.1 hy.2
    omega
  · have heq : insert (2 * (2 * M) - 2) ((Sig0 (sigE (2 * M)) (2 * (2 * M) - 2)).image
        (fun z => z + sigE (2 * M) z - (2 * (2 * M) + 1))) =
        {4 * M - 2, -(2 * M), -(2 * M - 2)} ∪
          (Icc (-(2 * (M - 2))) (2 * (M - 2))).filter (fun d => d % 2 = 0) := by
      ext d
      simp only [mem_insert, mem_image, Sig0, mem_filter, mem_Icc, mem_union, mem_singleton]
      constructor
      · rintro (h | ⟨z, ⟨⟨hz1, hz2⟩, hz3⟩, rfl⟩)
        · omega
        · have := sp z hz1 hz2; omega
      · rintro ((h | h | h) | ⟨⟨h1, h2⟩, h4⟩)
        · omega
        · have := sp 1 (by omega) (by omega); exact Or.inr ⟨1, by omega, by omega⟩
        · have := sp 2 (by omega) (by omega); exact Or.inr ⟨2, by omega, by omega⟩
        · have := sp ((d + 2 * M + 2) / 2) (by omega) (by omega)
          exact Or.inr ⟨(d + 2 * M + 2) / 2, by omega, by omega⟩
    rw [heq]
    refine ZS.union (ZS.triple (by omega) (by omega) (by omega) (by ring))
      (zs_even (M - 2) (by omega) (by omega)) ?_
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_insert, mem_singleton, mem_filter, mem_Icc] at hx hx'
    omega
  · intro z hz; simp only [Sig0, mem_filter, mem_Icc] at hz
    have := sp z hz.1.1 hz.1.2; omega

set_option maxHeartbeats 2000000 in
theorem sigO_spec (N x : ℤ) (hN : 7 ≤ N) (hx1 : 1 ≤ x) (hx2 : x ≤ 2 * N - 2) :
    (x = 1 ∧ sigO N x = N) ∨ (x = N ∧ sigO N x = 1) ∨ (x = 2 ∧ sigO N x = N + 1) ∨
    (x = N + 1 ∧ sigO N x = 2) ∨ (x = 2 * N - 3 ∧ sigO N x = 2 * N - 2) ∨
    (x = 2 * N - 2 ∧ sigO N x = 2 * N - 3) ∨ (x = 3 ∧ sigO N x = N - 1) ∨
    (x = N - 1 ∧ sigO N x = 3) ∨ (x = 4 ∧ sigO N x = N + 2) ∨ (x = N + 2 ∧ sigO N x = 4) ∨
    (5 ≤ x ∧ x ≤ N - 2 ∧ sigO N x = x + N - 2) ∨
    (N + 3 ≤ x ∧ x ≤ 2 * N - 4 ∧ sigO N x = x - (N - 2)) := by
  unfold sigO; split_ifs <;> omega

theorem gadget_odd (M : ℤ) (hM : 3 ≤ M) (h3 : M % 3 = 0) :
    Gadget (2 * M + 1) (sigO (2 * M + 1)) := by
  have sp := fun x (h1 : 1 ≤ x) (h2 : x ≤ 2 * (2 * M + 1) - 2) =>
    sigO_spec (2 * M + 1) x (by omega) h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp only [mem_Icc] at hx ⊢; have := sp x hx.1 hx.2; omega
  · intro x hx; simp only [mem_Icc] at hx
    have h1 := sp x hx.1 hx.2
    have h2 := sp (sigO (2 * M + 1) x) (by omega) (by omega)
    omega
  · intro x hx; simp only [mem_Icc] at hx; have := sp x hx.1 hx.2; omega
  · intro x hx y hy; simp only [mem_Icc] at hx hy
    have h1 := sp x hx.1 hx.2
    have h2 := sp y hy.1 hy.2
    omega
  · have heq : insert (2 * (2 * M + 1) - 2) ((Sig0 (sigO (2 * M + 1)) (2 * (2 * M + 1) - 2)).image
        (fun z => z + sigO (2 * M + 1) z - (2 * (2 * M + 1) + 1))) =
        {4 * M, -(2 * M + 1), -(2 * M - 1)} ∪ ({4 * M - 4, -(2 * M), -(2 * M - 4)} ∪
          (Icc (-(2 * (M - 3))) (2 * (M - 3))).filter (fun d => d % 2 = 0)) := by
      ext d
      simp only [mem_insert, mem_image, Sig0, mem_filter, mem_Icc, mem_union, mem_singleton]
      constructor
      · rintro (h | ⟨z, ⟨⟨hz1, hz2⟩, hz3⟩, rfl⟩)
        · omega
        · have := sp z hz1 hz2; omega
      · rintro ((h | h | h) | ((h | h | h) | ⟨⟨h1, h2⟩, h4⟩))
        · omega
        · have := sp 1 (by omega) (by omega); exact Or.inr ⟨1, by omega, by omega⟩
        · have := sp 2 (by omega) (by omega); exact Or.inr ⟨2, by omega, by omega⟩
        · have := sp (4 * M - 1) (by omega) (by omega)
          exact Or.inr ⟨4 * M - 1, by omega, by omega⟩
        · have := sp 3 (by omega) (by omega); exact Or.inr ⟨3, by omega, by omega⟩
        · have := sp 4 (by omega) (by omega); exact Or.inr ⟨4, by omega, by omega⟩
        · have := sp ((d + 2 * M + 4) / 2) (by omega) (by omega)
          exact Or.inr ⟨(d + 2 * M + 4) / 2, by omega, by omega⟩
    rw [heq]
    refine ZS.union (ZS.triple (by omega) (by omega) (by omega) (by ring))
      (ZS.union (ZS.triple (by omega) (by omega) (by omega) (by ring))
        (zs_even (M - 3) (by omega) (by omega)) ?_) ?_
    · rw [disjoint_left]
      intro x hx hx'
      simp only [mem_insert, mem_singleton, mem_filter, mem_Icc] at hx hx'
      omega
    · rw [disjoint_left]
      intro x hx hx'
      simp only [mem_insert, mem_singleton, mem_filter, mem_Icc, mem_union] at hx hx'
      omega
  · intro z hz; simp only [Sig0, mem_filter, mem_Icc] at hz
    have := sp z hz.1.1 hz.1.2; omega

theorem gadget_exists (N : ℤ) (h1 : 1 ≤ N) (h3 : N % 3 = 1) : ∃ σ, Gadget N σ := by
  by_cases hN : N = 1
  · subst hN; exact ⟨id, gadget_one⟩
  by_cases h2 : N % 2 = 0
  · obtain ⟨M, rfl⟩ : ∃ M, N = 2 * M := ⟨N / 2, by omega⟩
    exact ⟨_, gadget_even M (by omega) (by omega)⟩
  · obtain ⟨M, rfl⟩ : ∃ M, N = 2 * M + 1 := ⟨N / 2, by omega⟩
    exact ⟨_, gadget_odd M (by omega) (by omega)⟩

end GN
