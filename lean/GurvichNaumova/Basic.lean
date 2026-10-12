import Mathlib

open Finset

namespace GN

/-- A finite set of integers is admissible if it has at most three elements
and its sum is a power of three. -/
def Adm (s : Finset ℤ) : Prop := s.card ≤ 3 ∧ ∃ k : ℕ, ∑ x ∈ s, x = 3 ^ k

/-- `Good S`: the set `S` is a disjoint union of admissible sets. -/
inductive Good : Finset ℤ → Prop
  | empty : Good ∅
  | part {s : Finset ℤ} : Adm s → Good s
  | union {A B : Finset ℤ} : Good A → Good B → Disjoint A B → Good (A ∪ B)

/-- `ZS S`: the set `S` is a disjoint union of `{0}` and of zero-sum triples. -/
inductive ZS : Finset ℤ → Prop
  | empty : ZS ∅
  | zero : ZS {0}
  | triple {a b c : ℤ} : a ≠ b → a ≠ c → b ≠ c → a + b + c = 0 → ZS {a, b, c}
  | union {A B : Finset ℤ} : ZS A → ZS B → Disjoint A B → ZS (A ∪ B)

theorem Good.single (a : ℤ) (k : ℕ) (h : a = 3 ^ k) : Good {a} :=
  Good.part ⟨by simp, k, by simp [h]⟩

theorem Good.pair (a b : ℤ) (k : ℕ) (hab : a ≠ b) (h : a + b = 3 ^ k) : Good {a, b} :=
  Good.part ⟨card_le_two.trans (by norm_num), k, by rw [sum_pair hab, h]⟩

theorem Good.triple (a b c : ℤ) (k : ℕ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : a + b + c = 3 ^ k) : Good {a, b, c} := by
  refine Good.part ⟨card_le_three, k, ?_⟩
  rw [sum_insert (by simp [hab, hac]), sum_pair hbc, ← h]; ring

theorem Good.union' {A B : Finset ℤ} (hA : Good A) (hB : Good B) (h : Disjoint A B) :
    Good (A ∪ B) := Good.union hA hB h

theorem Good.congr {A B : Finset ℤ} (h : A = B) (hA : Good A) : Good B := h ▸ hA

theorem Good.biUnion {ι : Type*} [DecidableEq ι] (I : Finset ι) (f : ι → Finset ℤ)
    (hf : ∀ i ∈ I, Good (f i)) (hd : (I : Set ι).PairwiseDisjoint f) :
    Good (I.biUnion f) := by
  induction I using Finset.induction_on with
  | empty => simpa using Good.empty
  | insert i I hi ih =>
    rw [biUnion_insert]
    refine Good.union (hf i (mem_insert_self _ _)) (ih (fun j hj => hf j (mem_insert_of_mem hj))
      (hd.subset (by simp))) ?_
    rw [disjoint_biUnion_right]
    intro j hj
    exact hd (by simp) (by simp [hj]) (by rintro rfl; exact hi hj)

theorem ZS.congr {A B : Finset ℤ} (h : A = B) (hA : ZS A) : ZS B := h ▸ hA

theorem ZS.biUnion {ι : Type*} [DecidableEq ι] (I : Finset ι) (f : ι → Finset ℤ)
    (hf : ∀ i ∈ I, ZS (f i)) (hd : (I : Set ι).PairwiseDisjoint f) :
    ZS (I.biUnion f) := by
  induction I using Finset.induction_on with
  | empty => simpa using ZS.empty
  | insert i I hi ih =>
    rw [biUnion_insert]
    refine ZS.union (hf i (mem_insert_self _ _)) (ih (fun j hj => hf j (mem_insert_of_mem hj))
      (hd.subset (by simp))) ?_
    rw [disjoint_biUnion_right]
    intro j hj
    exact hd (by simp) (by simp [hj]) (by rintro rfl; exact hi hj)

/-- An affine image `x ↦ c + s x` of a zero-sum decomposition, with `c = 3^k`, is good. -/
theorem ZS.good {S : Finset ℤ} (hS : ZS S) (c s : ℤ) (k : ℕ) (hc : c = 3 ^ k) (hs : s ≠ 0) :
    Good (S.image (fun x => c + s * x)) := by
  have hinj : Function.Injective (fun x : ℤ => c + s * x) := by
    intro x y hxy
    have : s * x = s * y := by simpa using hxy
    exact mul_left_cancel₀ hs this
  induction hS with
  | empty => simpa using Good.empty
  | zero => simpa using Good.single c k hc
  | triple hab hac hbc h =>
    rename_i a b d
    simp only [image_insert, image_singleton]
    refine Good.triple _ _ _ (k + 1) (fun e => hab (hinj e)) (fun e => hac (hinj e))
      (fun e => hbc (hinj e)) ?_
    have : c + s * a + (c + s * b) + (c + s * d) = 3 * c + s * (a + b + d) := by ring
    rw [this, h, hc]; ring
  | union _ _ hd ihA ihB =>
    rw [image_union]
    exact Good.union ihA ihB ((disjoint_image hinj).2 hd)

/-! ## Pairs `{x, Q - x}` -/

/-- A symmetric interval around `Q / 2` is good when `Q = 3^k`. -/
theorem good_Icc_symm (Q : ℤ) (k : ℕ) (hQ : Q = 3 ^ k) :
    ∀ (m : ℕ) (a : ℤ), Q - 1 - 2 * a = 2 * m → Good (Icc (a + 1) (Q - 1 - a)) := by
  intro m
  induction m with
  | zero =>
    intro a h
    have : Icc (a + 1) (Q - 1 - a) = ∅ := by
      ext x; simp; omega
    rw [this]; exact Good.empty
  | succ m ih =>
    intro a h
    have hset : Icc (a + 1) (Q - 1 - a) = {a + 1, Q - 1 - a} ∪ Icc (a + 1 + 1) (Q - 1 - (a + 1)) := by
      ext x; simp only [mem_Icc, mem_union, mem_insert, mem_singleton]; omega
    rw [hset]
    refine Good.union (Good.pair _ _ k (by omega) (by rw [← hQ]; ring)) (ih (a + 1) (by omega)) ?_
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_Icc, mem_insert, mem_singleton] at hx hx'
    omega

theorem three_pow_odd (k : ℕ) : (3 : ℤ) ^ k % 2 = 1 := by
  have : Odd ((3 : ℤ) ^ k) := Odd.pow (by decide)
  rcases this with ⟨m, hm⟩
  omega

theorem three_pow_mod3 (k : ℕ) (hk : 1 ≤ k) : (3 : ℤ) ^ k % 3 = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]; simp

/-- A subset of `[1, Q - 1]` closed under `x ↦ Q - x` is good when `Q = 3^k`. -/
theorem good_of_symm (Q : ℤ) (k : ℕ) (hQ : Q = 3 ^ k) :
    ∀ (n : ℕ) (X : Finset ℤ), X.card = n → (∀ x ∈ X, 1 ≤ x ∧ x ≤ Q - 1 ∧ Q - x ∈ X) →
      Good X := by
  have hodd : Q % 2 = 1 := hQ ▸ three_pow_odd k
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hX hsym
    rcases X.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact Good.empty
    · obtain ⟨h1, h2, h3⟩ := hsym x hx
      have hne : x ≠ Q - x := by omega
      set Y := X \ {x, Q - x} with hY
      have hsub : ({x, Q - x} : Finset ℤ) ⊆ X := by
        intro y hy; simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hx
        · exact h3
      have hXY : X = {x, Q - x} ∪ Y := by
        rw [hY, union_sdiff_of_subset hsub]
      have hcard : Y.card < n := by
        rw [← hX, hY, card_sdiff_of_subset hsub, card_pair hne]
        have : 2 ≤ X.card := by
          rw [← card_pair hne]; exact card_le_card hsub
        omega
      have hYsym : ∀ y ∈ Y, 1 ≤ y ∧ y ≤ Q - 1 ∧ Q - y ∈ Y := by
        intro y hy
        rw [hY, mem_sdiff] at hy
        obtain ⟨hyX, hy'⟩ := hy
        obtain ⟨g1, g2, g3⟩ := hsym y hyX
        refine ⟨g1, g2, ?_⟩
        rw [hY, mem_sdiff]
        refine ⟨g3, ?_⟩
        simp only [mem_insert, mem_singleton] at hy' ⊢
        omega
      rw [hXY]
      refine Good.union (Good.pair _ _ k hne (by rw [← hQ]; ring)) (ih _ hcard Y rfl hYsym) ?_
      rw [hY]; exact disjoint_sdiff

/-! ## Lemma 1: zero-sum triples on `[-ℓ, ℓ]` -/

def tri1 (k i : ℤ) : Finset ℤ := {-(3 * k - i), 1 + i, 3 * k - 1 - 2 * i}
def tri2 (k i : ℤ) : Finset ℤ := {-(2 * k - i), -(k - i), 3 * k - 2 * i}

theorem zs_core (k : ℤ) (hk : 0 ≤ k) :
    ZS ((Icc (-(3 * k)) (3 * k)).erase 0) := by
  have heq : (Icc (-(3 * k)) (3 * k)).erase 0 = (Ico 0 k).biUnion (fun i => tri1 k i ∪ tri2 k i) := by
    ext x
    simp only [mem_erase, mem_Icc, mem_biUnion, mem_Ico, mem_union, tri1, tri2, mem_insert,
      mem_singleton]
    constructor
    · rintro ⟨hx0, hx1, hx2⟩
      rcases (by omega : (1 ≤ x ∧ x ≤ k) ∨ (k + 1 ≤ x ∧ (3 * k - 1 - x) % 2 = 0) ∨
          (k + 1 ≤ x ∧ (3 * k - x) % 2 = 0) ∨ (x ≤ -(2 * k + 1)) ∨
          (-(2 * k) ≤ x ∧ x ≤ -(k + 1)) ∨ (-k ≤ x ∧ x ≤ -1)) with h | h | h | h | h | h
      · exact ⟨x - 1, by omega, by omega⟩
      · exact ⟨(3 * k - 1 - x) / 2, by omega, by omega⟩
      · exact ⟨(3 * k - x) / 2, by omega, by omega⟩
      · exact ⟨3 * k + x, by omega, by omega⟩
      · exact ⟨2 * k + x, by omega, by omega⟩
      · exact ⟨k + x, by omega, by omega⟩
    · rintro ⟨i, hi, h⟩
      omega
  rw [heq]
  refine ZS.biUnion _ _ ?_ ?_
  · intro i hi
    simp only [mem_Ico] at hi
    refine ZS.union (ZS.triple (by omega) (by omega) (by omega) (by ring))
      (ZS.triple (by omega) (by omega) (by omega) (by ring)) ?_
    rw [disjoint_left]
    intro x hx hx'
    simp only [tri1, tri2, mem_insert, mem_singleton] at hx hx'
    omega
  · intro i hi j hj hij
    simp only [coe_Ico, Set.mem_Ico] at hi hj
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx hx'
    simp only [tri1, tri2, mem_union, mem_insert, mem_singleton] at hx hx'
    omega

/-- Lemma 1: `[-ℓ, ℓ]` is a disjoint union of `{0}` and zero-sum triples when `ℓ ≢ 2 (mod 3)`. -/
theorem zs_Icc (l : ℤ) (hl : 0 ≤ l) (h3 : l % 3 ≠ 2) : ZS (Icc (-l) l) := by
  obtain ⟨k, hk, rfl | rfl⟩ : ∃ k, 0 ≤ k ∧ (l = 3 * k ∨ l = 3 * k + 1) :=
    ⟨l / 3, by omega, by omega⟩
  · have : Icc (-(3 * k)) (3 * k) = {0} ∪ (Icc (-(3 * k)) (3 * k)).erase 0 := by
      ext x; simp only [mem_union, mem_singleton, mem_erase, mem_Icc]; omega
    rw [this]
    refine ZS.union ZS.zero (zs_core k hk) ?_
    simp
  · have : Icc (-(3 * k + 1)) (3 * k + 1) =
        {-(3 * k + 1), 0, 3 * k + 1} ∪ (Icc (-(3 * k)) (3 * k)).erase 0 := by
      ext x; simp only [mem_union, mem_insert, mem_singleton, mem_erase, mem_Icc]; omega
    rw [this]
    refine ZS.union (ZS.triple (by omega) (by omega) (by omega) (by ring)) (zs_core k hk) ?_
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_insert, mem_singleton, mem_erase, mem_Icc] at hx hx'
    omega

end GN
