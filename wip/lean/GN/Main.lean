import LeanLab.GN.CaseA2

open Finset

namespace GN

theorem exists_level (n : ℤ) (h : 1 ≤ n) : ∃ t : ℕ, (3 : ℤ) ^ t ≤ n ∧ n < 3 ^ (t + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  have hm : m ≠ 0 := by omega
  refine ⟨Nat.log 3 m, ?_, ?_⟩
  · have := Nat.pow_log_le_self 3 hm
    exact_mod_cast this
  · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) m
    exact_mod_cast this

theorem pow3_mono {a b : ℕ} (h : a ≤ b) : (3 : ℤ) ^ a ≤ 3 ^ b :=
  pow_le_pow_right₀ (by norm_num) h

theorem pow3_lt {a b : ℕ} (h : (3 : ℤ) ^ a < 3 ^ b) : a < b :=
  (pow_lt_pow_iff_right₀ (by norm_num)).1 h

theorem level_unique (n : ℤ) (a b : ℕ) (ha1 : (3 : ℤ) ^ a ≤ n) (ha2 : n < 3 ^ (a + 1))
    (hb1 : (3 : ℤ) ^ b ≤ n) (hb2 : n < 3 ^ (b + 1)) : a = b := by
  have h1 : a < b + 1 := pow3_lt (lt_of_le_of_lt ha1 hb2)
  have h2 : b < a + 1 := pow3_lt (lt_of_le_of_lt hb1 ha2)
  omega

/-- The invariant: for `n = 3^t + j` with `j ≡ 2 (mod 3)` and `2 ≤ j ≤ (3^t - 1)/2`,
the set `[1, n]` minus the triple `{n - 1, n, 3^(t+1) - 2n + 1}` is good. -/
def Hyp (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → (3 : ℤ) ^ t + 2 ≤ n → 2 * n + 1 ≤ 3 ^ (t + 1) → n % 3 = 2 →
    Good (Icc 1 n \ {n - 1, n, 3 ^ (t + 1) - 2 * n + 1})

theorem main_aux (m : ℕ) : Good (Icc 1 (m : ℤ)) ∧ Hyp m := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  have IH' : ∀ k : ℤ, 0 ≤ k → k < m → Good (Icc 1 k) ∧ Hyp k := by
    intro k h0 h1
    have := IH k.toNat (by omega)
    rwa [Int.toNat_of_nonneg h0] at this
  set n : ℤ := m with hn
  have hn0 : 0 ≤ n := by omega
  -- small cases
  by_cases hsmall : n ≤ 2
  · have hH : Hyp n := by
      intro t ht h1
      have : (1 : ℤ) ≤ 3 ^ t := one_le_pow₀ (by norm_num)
      omega
    refine ⟨?_, hH⟩
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with h | h | h
    · rw [h]; simpa using Good.empty
    · rw [h]; simpa using Good.single 1 0 (by norm_num)
    · rw [h]
      have : Icc (1 : ℤ) 2 = {1, 2} := by ext x; simp only [mem_Icc, mem_insert, mem_singleton]; omega
      rw [this]; exact Good.pair 1 2 1 (by norm_num) (by norm_num)
  push_neg at hsmall
  obtain ⟨t, ht1, ht2⟩ := exists_level n (by omega)
  set T : ℤ := 3 ^ t with hT
  have hT3 : (3 : ℤ) ^ (t + 1) = 3 * T := by rw [hT]; ring
  have htpos : 1 ≤ t := by
    by_contra h
    have : t = 0 := by omega
    rw [this] at ht2; norm_num at ht2; omega
  have hTodd : T % 2 = 1 := three_pow_odd t
  have hTm3 : T % 3 = 0 := three_pow_mod3 t htpos
  have hT3le : 3 ≤ T := by rw [hT]; exact le_self_pow₀ (by norm_num) (by omega)
  -- `Hyp n` holds vacuously outside the lower-half class `2 (mod 3)`
  have hvac : ¬ (T + 2 ≤ n ∧ 2 * n + 1 ≤ 3 * T ∧ n % 3 = 2) → Hyp n := by
    intro hnot t' ht' h1 h2 h3
    have : t' = t := by
      have hle : (3 : ℤ) ^ t' ≤ n := by omega
      have hlt : n < 3 ^ (t' + 1) := by omega
      exact level_unique n t' t hle hlt ht1 ht2
    subst this
    exact absurd ⟨h1, by omega, h3⟩ hnot
  by_cases hnT : n = T
  · -- `n = 3^t`
    refine ⟨?_, hvac (by omega)⟩
    have hset : Icc 1 n = Icc 1 (T - 1) ∪ {T} := by
      ext x; simp only [mem_Icc, mem_union, mem_singleton]; omega
    rw [hset]
    refine Good.union (IH' (T - 1) (by omega) (by omega)).1 (Good.single T t hT) ?_
    simp
  by_cases hup : 3 * T + 1 ≤ 2 * n
  · -- upper half: pairs `{x, 3^(t+1) - x}`
    refine ⟨?_, hvac (by omega)⟩
    have hset : Icc 1 n = Icc 1 (3 * T - 1 - n) ∪ Icc (3 * T - 1 - n + 1) (3 * T - 1 - (3 * T - 1 - n)) := by
      ext x; simp only [mem_Icc, mem_union]; omega
    rw [hset]
    refine Good.union (IH' (3 * T - 1 - n) (by omega) (by omega)).1 ?_ ?_
    · refine good_Icc_symm (3 * T) (t + 1) hT3.symm ((2 * n - 3 * T + 1) / 2).toNat _ ?_
      omega
    · rw [disjoint_left]; intro x hx hx'; simp only [mem_Icc] at hx hx'; omega
  -- lower half
  set j := n - T with hj
  have hj1 : 1 ≤ j := by omega
  have hj2 : 2 * j + 1 ≤ T := by omega
  by_cases hj3 : j % 3 ≠ 2
  · refine ⟨?_, hvac (by omega)⟩
    have hset : Icc 1 n = Icc 1 (T - j - 1) ∪ (Icc (-j) j).image (fun x => T + 1 * x) := by
      ext x
      simp only [mem_Icc, mem_union, mem_image]
      constructor
      · intro h
        by_cases hx : x ≤ T - j - 1
        · left; omega
        · right; exact ⟨x - T, by omega, by ring⟩
      · rintro (h | ⟨y, hy, rfl⟩) <;> omega
    rw [hset]
    refine Good.union (IH' (T - j - 1) (by omega) (by omega)).1
      ((zs_Icc j (by omega) hj3).good T 1 t hT one_ne_zero) ?_
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_Icc, mem_image] at hx hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    omega
  push_neg at hj3
  -- the class `j ≡ 2 (mod 3)`: first the invariant
  have hTri : Good (Icc 1 (T + j) \ {T + j - 1, T + j, T - 2 * j + 1}) := by
    by_cases hj2' : j = 2
    · have h9 : 9 ≤ T := by
        have : 2 ≤ t := by
          by_contra h
          have : t = 1 := by omega
          rw [hT, this] at hj2; omega
        have := pow3_mono this
        rw [hT]; norm_num at this ⊢; linarith
      rw [hj2']
      exact case_two T t hT h9
    have hj5 : 5 ≤ j := by omega
    rcases lt_trichotomy (3 * j) T with hA | hE | hB
    · -- case A: `3j < 3^t`
      obtain ⟨u, hu1, hu2⟩ := exists_level j (by omega)
      have hu : 1 ≤ u := by
        by_contra h
        have : u = 0 := by omega
        rw [this] at hu2; norm_num at hu2; omega
      have hU3 : (3 : ℤ) ^ (u + 1) = 3 * 3 ^ u := by ring
      have hUm3 : (3 : ℤ) ^ u % 3 = 0 := three_pow_mod3 u hu
      have hUodd : (3 : ℤ) ^ (u + 1) % 2 = 1 := three_pow_odd (u + 1)
      by_cases hA1 : 2 * j + 1 ≤ 3 ^ (u + 1)
      · -- case A1: `j` in the lower half of its level
        refine case_BA1 T t hT j hj5 hj3 hj2 ?_
        have hHj := (IH' j (by omega) (by omega)).2 u hu (by omega) hA1 hj3
        have hfilt : (insert (2 * j - 1) (Icc 1 (j - 2))).filter
            (fun x => T - x ∉ insert (2 * j - 1) (Icc 1 (j - 2))) =
            (Icc 1 j \ {j - 1, j, 3 ^ (u + 1) - 2 * j + 1}) ∪
              {3 ^ (u + 1) - 2 * j + 1, 2 * j - 1} := by
          ext x
          simp only [mem_filter, mem_insert, mem_Icc, mem_union, mem_sdiff, mem_singleton]
          omega
        rw [hfilt]
        refine Good.union hHj (Good.pair _ _ (u + 1) (by omega) (by ring)) ?_
        rw [disjoint_left]
        intro x hx hx'
        simp only [mem_sdiff, mem_Icc, mem_insert, mem_singleton] at hx hx'
        omega
      · -- case A2: `j` in the upper half of its level
        have hut : u + 1 < t := by
          apply pow3_lt
          rw [← hT]; omega
        have hTP : T = 3 * 3 ^ (u + 1) ∨ 9 * 3 ^ (u + 1) ≤ T := by
          rcases (by omega : t = u + 2 ∨ u + 3 ≤ t) with h | h
          · left; rw [hT, h]; ring
          · right
            have := pow3_mono h
            have e : (3 : ℤ) ^ (u + 3) = 9 * 3 ^ (u + 1) := by ring
            rw [hT]; linarith
        exact case_A2 T t hT (3 ^ (u + 1)) (u + 1) rfl (by omega) hTP j hj3 (by omega) (by omega)
          (IH' (3 ^ (u + 1) - 1 - j) (by omega) (by omega)).1
    · -- `3j = 3^t` is impossible
      exfalso
      obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have h' : T = 3 * 3 ^ s := by rw [hT, hs]; ring
      by_cases hs0 : s = 0
      · rw [hs0] at h'; omega
      · have := three_pow_mod3 s (by omega)
        omega
    · -- case B: `3j > 3^t`
      refine case_BA1 T t hT j hj5 hj3 hj2 ?_
      obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have h' : T = 3 * 3 ^ s := by rw [hT, hs]; ring
      have hs1 : 1 ≤ s := by
        by_contra h
        have : s = 0 := by omega
        rw [this] at h'; omega
      have hsm3 := three_pow_mod3 s hs1
      have hs' : (3 : ℤ) ^ (s + 1) = 3 * 3 ^ s := by ring
      have hHj := (IH' j (by omega) (by omega)).2 s hs1 (by omega) (by omega) hj3
      have hfilt : (insert (2 * j - 1) (Icc 1 (j - 2))).filter
          (fun x => T - x ∉ insert (2 * j - 1) (Icc 1 (j - 2))) =
          Icc 1 j \ {j - 1, j, 3 ^ (s + 1) - 2 * j + 1} := by
        ext x
        simp only [mem_filter, mem_insert, mem_Icc, mem_sdiff, mem_singleton]
        omega
      rw [hfilt]
      exact hHj
  -- conclusion for `n = 3^t + j`, `j ≡ 2 (mod 3)`
  have hTn : Icc 1 (T + j) = Icc 1 n := by rw [hj]; ring_nf
  rw [hTn] at hTri
  have hsub : ({T + j - 1, T + j, T - 2 * j + 1} : Finset ℤ) ⊆ Icc 1 n := by
    intro x hx; simp only [mem_insert, mem_singleton, mem_Icc] at hx ⊢; omega
  refine ⟨?_, ?_⟩
  · rw [← sdiff_union_of_subset hsub]
    refine Good.union hTri (Good.triple _ _ _ (t + 1) (by omega) (by omega) (by omega)
      (by rw [hT3]; ring)) sdiff_disjoint
  · intro t' ht' h1 h2 h3
    have : t' = t := by
      have hle : (3 : ℤ) ^ t' ≤ n := by omega
      have hlt : n < 3 ^ (t' + 1) := by omega
      exact level_unique n t' t hle hlt ht1 ht2
    subst this
    have e : ({n - 1, n, 3 ^ (t' + 1) - 2 * n + 1} : Finset ℤ) =
        {T + j - 1, T + j, T - 2 * j + 1} := by
      ext x; simp only [mem_insert, mem_singleton]; omega
    rw [e]; exact hTri

/-- **Gurvich–Naumova Conjecture 1.** For every `n`, the set `{1, …, n}` has a partition into
parts of at most three elements, each with sum a power of three. -/
theorem good_Icc (n : ℕ) : Good (Icc 1 (n : ℤ)) := (main_aux n).1

end GN
