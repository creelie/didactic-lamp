import GurvichNaumova.Gadget
import GurvichNaumova.Assembly

open Finset

namespace GN

section Pairing

variable {σ : ℤ → ℤ} {K : ℤ}

theorem pair_disj (hinv : ∀ x ∈ Icc 1 K, σ (σ x) = x)
    {z w : ℤ} (hz : z ∈ Sig0 σ K) (hw : w ∈ Sig0 σ K) (hzw : z ≠ w) :
    z ≠ σ w ∧ σ z ≠ w ∧ σ z ≠ σ w := by
  simp only [Sig0, mem_filter] at hz hw
  have iz := hinv z hz.1
  have iw := hinv w hw.1
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : σ z = w := by rw [h, iw]
    omega
  · intro h
    have : σ w = z := by rw [← h, iz]
    omega
  · intro h
    have : σ (σ z) = σ (σ w) := by rw [h]
    rw [iz, iw] at this
    exact hzw this

/-- The zero-sum triples `(e + z, e + σ z, -(2e + z + σ z))` attached to the pairs. -/
def top (σ : ℤ → ℤ) (K e : ℤ) : Finset ℤ :=
  (Sig0 σ K).biUnion (fun z => {e + z, e + σ z, -(2 * e + z + σ z)})

theorem top_zs (hmem : ∀ x ∈ Icc 1 K, σ x ∈ Icc 1 K) (hinv : ∀ x ∈ Icc 1 K, σ (σ x) = x)
    (hinj : ∀ x ∈ Icc 1 K, ∀ y ∈ Icc 1 K, x < σ x → y < σ y → x + σ x = y + σ y → x = y)
    (e : ℤ) (he : 0 ≤ e) : ZS (top σ K e) := by
  refine ZS.biUnion _ _ ?_ ?_
  · intro z hz
    simp only [Sig0, mem_filter] at hz
    have m := hmem z hz.1
    simp only [mem_Icc] at hz m
    exact ZS.triple (by omega) (by omega) (by omega) (by ring)
  · intro z hz w hw hzw
    have hz' : z ∈ Sig0 σ K := hz
    have hw' : w ∈ Sig0 σ K := hw
    obtain ⟨d1, d2, d3⟩ := pair_disj hinv hz' hw' hzw
    simp only [Sig0, mem_filter] at hz' hw'
    have hs : z + σ z ≠ w + σ w := fun h => hzw (hinj z hz'.1 w hw'.1 hz'.2 hw'.2 h)
    have m1 := hmem z hz'.1
    have m2 := hmem w hw'.1
    simp only [mem_Icc] at hz' hw' m1 m2
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_insert, mem_singleton] at hx hx'
    omega

theorem top_eq (hmem : ∀ x ∈ Icc 1 K, σ x ∈ Icc 1 K) (hinv : ∀ x ∈ Icc 1 K, σ (σ x) = x)
    (hne : ∀ x ∈ Icc 1 K, σ x ≠ x) (e : ℤ) :
    top σ K e = Icc (e + 1) (e + K) ∪ (Sig0 σ K).image (fun z => -(2 * e + z + σ z)) := by
  ext y
  simp only [top, mem_biUnion, mem_union, mem_Icc, mem_image, mem_insert, mem_singleton]
  constructor
  · rintro ⟨z, hz, h⟩
    have hz' := hz
    simp only [Sig0, mem_filter] at hz'
    have m := hmem z hz'.1
    simp only [mem_Icc] at hz' m
    rcases h with h | h | h
    · left; omega
    · left; omega
    · right; exact ⟨z, hz, h.symm⟩
  · rintro (⟨h1, h2⟩ | ⟨z, hz, rfl⟩)
    · have hw : y - e ∈ Icc 1 K := by simp only [mem_Icc]; omega
      have m := hmem _ hw
      have iv := hinv _ hw
      have nv := hne _ hw
      by_cases hlt : y - e < σ (y - e)
      · exact ⟨y - e, by simp only [Sig0, mem_filter]; exact ⟨hw, hlt⟩, Or.inl (by ring)⟩
      · refine ⟨σ (y - e), ?_, Or.inr (Or.inl (by rw [iv]; ring))⟩
        simp only [Sig0, mem_filter]
        refine ⟨m, ?_⟩
        rw [iv]; omega
    · exact ⟨z, hz, Or.inr (Or.inr rfl)⟩

end Pairing

/-- The case A2: `j` in the upper half of its level `p - 1`, `P = 3^p`, `3P ≤ T`. -/
theorem case_A2 (T : ℤ) (t : ℕ) (hT : T = 3 ^ t) (P : ℤ) (p : ℕ) (hP : P = 3 ^ p) (hp : 1 ≤ p)
    (hTP : T = 3 * P ∨ 9 * P ≤ T) (j : ℤ) (hj3 : j % 3 = 2) (hjlo : P + 1 ≤ 2 * j)
    (hjhi : j ≤ P - 1) (hlow : Good (Icc 1 (P - 1 - j))) :
    Good (Icc 1 (T + j) \ {T + j - 1, T + j, T - 2 * j + 1}) := by
  have hP2 : P % 2 = 1 := hP ▸ three_pow_odd p
  have hP3 : P % 3 = 0 := hP ▸ three_pow_mod3 p hp
  obtain ⟨c, hc⟩ : ∃ c, P = 2 * c + 1 := ⟨P / 2, by omega⟩
  set N := j - c with hN
  set K := 2 * N - 2 with hK
  set e := P - 1 - j with he
  obtain ⟨σ, hmem, hinv, hne, hinj, hZS, hev⟩ := gadget_exists N (by omega) (by omega)
  rw [← hK] at hmem hinv hne hinj hZS hev
  set Δ := insert (2 * N - 2) ((Sig0 σ K).image (fun z => z + σ z - (2 * N + 1))) with hΔ
  set S := Δ.image (fun x => P + 1 * x) with hS
  set D := Icc 1 e ∪ S with hD
  -- bounds on the elements of Δ
  have hΔb : ∀ δ ∈ Δ, 2 - 2 * N ≤ δ ∧ δ ≤ 2 * N - 2 ∧ (0 < δ → δ % 2 = 0) := by
    intro δ hδ
    rw [hΔ, mem_insert] at hδ
    rcases hδ with rfl | hδ
    · omega
    · obtain ⟨z, hz, rfl⟩ := mem_image.1 hδ
      have h1 := hev z hz
      simp only [Sig0, mem_filter] at hz
      have m := hmem z hz.1
      simp only [mem_Icc] at hz m
      omega
  have hSmem : ∀ y, y ∈ S → ∃ δ ∈ Δ, y = P + δ := by
    intro y hy
    obtain ⟨δ, hδ, rfl⟩ := mem_image.1 hy
    exact ⟨δ, hδ, by ring⟩
  have hTP' : 3 * P ≤ T := by omega
  have hP3' : 3 ≤ P := by rw [hP]; exact le_self_pow₀ (by norm_num) (by omega)
  refine assembly T t hT j (by omega) D _ ?_ ?_ ?_ ?_
  · -- D ⊆ [1, T - 1]
    intro x hx
    rw [hD, mem_union] at hx
    rcases hx with hx | hx
    · simp only [mem_Icc] at hx; omega
    · obtain ⟨δ, hδ, rfl⟩ := hSmem x hx
      have := hΔb δ hδ
      omega
  · -- the special triple
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · left; omega
    · left; omega
    · right
      refine ⟨by omega, by omega, ?_⟩
      rw [hD, mem_union]
      right
      rw [hS, mem_image]
      exact ⟨2 * N - 2, by rw [hΔ]; exact mem_insert_self _ _, by omega⟩
  · -- the rest around `T`
    have hR : (insert T (Icc (T + 1) (T + j) ∪ refl T D)) \ {T + j - 1, T + j, T - 2 * j + 1} =
        (Icc (-e) e ∪ top σ K e).image (fun x => T + 1 * x) := by
      rw [top_eq hmem hinv hne]
      ext x
      simp only [mem_sdiff, mem_insert, mem_union, mem_Icc, refl, mem_filter, mem_singleton,
        mem_image]
      constructor
      · rintro ⟨h1, h2⟩
        rcases h1 with rfl | ⟨a1, a2⟩ | ⟨⟨c1, c2⟩, hx⟩
        · exact ⟨0, Or.inl ⟨by omega, by omega⟩, by ring⟩
        · exact ⟨x - T, by omega, by ring⟩
        · rw [hD, mem_union, mem_Icc] at hx
          rcases hx with hx | hx
          · exact ⟨x - T, Or.inl ⟨by omega, by omega⟩, by ring⟩
          · obtain ⟨δ, hδ, hδe⟩ := hSmem _ hx
            rw [hΔ, mem_insert] at hδ
            rcases hδ with rfl | hδ
            · exfalso; omega
            · obtain ⟨z, hz, rfl⟩ := mem_image.1 hδ
              exact ⟨x - T, Or.inr (Or.inr ⟨z, hz, by omega⟩), by ring⟩
      · rintro ⟨a, ha, rfl⟩
        rcases ha with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨z, hz, rfl⟩
        · refine ⟨?_, by omega⟩
          rcases (by omega : a = 0 ∨ 0 < a ∨ a < 0) with h | h | h
          · left; omega
          · right; left; omega
          · right; right
            refine ⟨⟨by omega, by omega⟩, ?_⟩
            rw [hD, mem_union, mem_Icc]
            left; omega
        · exact ⟨Or.inr (Or.inl ⟨by omega, by omega⟩), by omega⟩
        · have hz' := hz
          simp only [Sig0, mem_filter] at hz'
          have m := hmem z hz'.1
          simp only [mem_Icc] at hz' m
          refine ⟨Or.inr (Or.inr ⟨⟨by omega, by omega⟩, ?_⟩), by omega⟩
          rw [hD, mem_union]
          right
          rw [hS, mem_image]
          refine ⟨z + σ z - (2 * N + 1), ?_, by omega⟩
          rw [hΔ]
          exact mem_insert_of_mem (mem_image_of_mem _ hz)
    rw [hR]
    refine ZS.good ?_ T 1 t hT one_ne_zero
    refine ZS.union (zs_Icc e (by omega) (by omega)) (top_zs hmem hinv hinj e (by omega)) ?_
    rw [top_eq hmem hinv hne, disjoint_left]
    intro x hx hx'
    simp only [mem_Icc, mem_union, mem_image] at hx hx'
    rcases hx' with h | ⟨z, hz, rfl⟩
    · omega
    · simp only [Sig0, mem_filter] at hz
      have m := hmem z hz.1
      simp only [mem_Icc] at hz m
      omega
  · -- `D` meets its reflection nowhere, and is good
    have hfilt : D.filter (fun x => T - x ∉ D) = D := by
      refine filter_true_of_mem ?_
      intro x hx hx'
      rw [hD, mem_union] at hx hx'
      rcases hx with hx | hx <;> rcases hx' with hx' | hx'
      · simp only [mem_Icc] at hx hx'; omega
      · simp only [mem_Icc] at hx
        obtain ⟨δ, hδ, hδe⟩ := hSmem _ hx'
        have := hΔb δ hδ
        omega
      · simp only [mem_Icc] at hx'
        obtain ⟨δ, hδ, hδe⟩ := hSmem _ hx
        have := hΔb δ hδ
        omega
      · obtain ⟨δ, hδ, hδe⟩ := hSmem _ hx
        obtain ⟨δ', hδ', hδe'⟩ := hSmem _ hx'
        have h1 := hΔb δ hδ
        have h2 := hΔb δ' hδ'
        omega
    rw [hfilt, hD]
    refine Good.union hlow (hZS.good P 1 p hP one_ne_zero) ?_
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨δ, hδ, rfl⟩ := hSmem _ hx'
    have := hΔb δ hδ
    simp only [mem_Icc] at hx
    omega

end GN
