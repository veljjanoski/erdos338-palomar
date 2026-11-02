module

public import Erdos338.Structure

/-!
# Sums of two distinct elements

`rep A m` indexes the ways to write `m = a + (m - a)` with `a, m - a ∈ A` and `a ≠ m - a`. If `A`
has lower density at least `δ`, then for every `R` the set of `m` with at least `R` such
representations has lower density at least `δ ^ 2 / 8` (`pairs_dense`). A sum of numbers with many
representations is a sum of distinct elements of `A` that avoid a given finite set (`greedy`).
-/

@[expose] public section

open Finset

namespace Erdos338Proof

open Classical in
/-- The `a ≤ m` with `a ∈ A`, `m - a ∈ A` and `2 a ≠ m`: the ordered representations of `m` as a
sum of two distinct elements of `A`. -/
noncomputable def rep (A : Set ℕ) (m : ℕ) : Finset ℕ :=
  (range (m + 1)).filter fun a ↦ a ∈ A ∧ m - a ∈ A ∧ 2 * a ≠ m

lemma mem_rep {A : Set ℕ} {m a : ℕ} :
    a ∈ rep A m ↔ a ≤ m ∧ a ∈ A ∧ m - a ∈ A ∧ 2 * a ≠ m := by
  simp [rep]

lemma card_rep_le (A : Set ℕ) (m : ℕ) : #(rep A m) ≤ m + 1 := by
  classical
  unfold rep
  exact (card_filter_le _ _).trans (card_range _).le

/-- Counting pairs: the `k ^ 2 - k` ordered pairs of distinct elements of `A ∩ [0, L)`, where
`k = |A ∩ [0, L)|`, have sums below `b ≥ 2 L`. A sum below `b` has at most `b` representations,
and fewer than `R` unless it lies in the set counted on the right. -/
lemma pair_count (A : Set ℕ) (R : ℕ) {b L : ℕ} (hL : 2 * L ≤ b) :
    cnt A L * cnt A L ≤ b * cnt {m | R ≤ #(rep A m)} b + b * R + cnt A L := by
  classical
  set M : Set ℕ := {m | R ≤ #(rep A m)} with hM
  set S := (range L).filter (· ∈ A) with hS
  have hk : cnt A L = #S := rfl
  have h1 : #S.offDiag ≤ ∑ m ∈ range b, #(rep A m) := by
    rw [card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ ↦ p.1 + p.2) (t := range b)]
    · apply sum_le_sum
      intro m _
      apply card_le_card_of_injOn Prod.fst
      · intro p hp
        rw [Finset.mem_coe, mem_filter, mem_offDiag] at hp
        obtain ⟨⟨hp1, hp2, hne⟩, hsum⟩ := hp
        rw [hS, mem_filter] at hp1 hp2
        rw [Finset.mem_coe, mem_rep]
        have e : m - p.1 = p.2 := by omega
        rw [e]
        exact ⟨by omega, hp1.2, hp2.2, by omega⟩
      · intro p hp q hq hpq
        simp only [Finset.mem_coe, mem_filter] at hp hq
        exact Prod.ext hpq (by omega)
    · intro p hp
      rw [Finset.mem_coe, mem_offDiag, hS, mem_filter, mem_filter, mem_range, mem_range] at hp
      rw [Finset.mem_coe, mem_range]
      show p.1 + p.2 < b
      omega
  have h2 : ∑ m ∈ range b, #(rep A m) ≤ ∑ m ∈ range b, ((if m ∈ M then b else 0) + R) := by
    apply sum_le_sum
    intro m hm
    rw [mem_range] at hm
    split_ifs with h
    · have := card_rep_le A m
      omega
    · have h' : ¬ R ≤ #(rep A m) := h
      omega
  have h3 : ∑ m ∈ range b, ((if m ∈ M then b else 0) + R) = b * cnt M b + b * R := by
    rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, card_range, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    unfold cnt
    convert rfl
  have h4 := h1.trans (h2.trans h3.le)
  rw [offDiag_card] at h4
  rw [hk]
  omega

/-- If `A` has lower density at least `δ`, then for every `R` the set of numbers with at least `R`
representations as a sum of two distinct elements of `A` has lower density at least `δ ^ 2 / 8`. -/
lemma pairs_dense {δ : ℝ} (hδ : 0 < δ) {A : Set ℕ} {N₀ : ℕ}
    (hN₀ : ∀ b ≥ N₀, δ * b ≤ cnt A b) (R : ℕ) :
    ∃ N, ∀ b ≥ N, δ ^ 2 / 8 * b ≤ cnt {m | R ≤ #(rep A m)} b := by
  set q := ⌈(4 + 8 * (R : ℝ)) / δ ^ 2⌉₊ with hq
  refine ⟨2 * N₀ + q + 5, fun b hb ↦ ?_⟩
  set L := b / 2 with hLdef
  have hL1 : 2 * L ≤ b := by omega
  have hL2 : b ≤ 2 * L + 1 := by omega
  have hmain := pair_count A R hL1
  set k := cnt A L
  set c := cnt {m | R ≤ #(rep A m)} b
  have hk : δ * L ≤ k := hN₀ L (by omega)
  have hkL : k ≤ L := cnt_le_of_subset fun _ _ hx ↦ hx
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hceil : (4 + 8 * (R : ℝ)) / δ ^ 2 ≤ (b : ℝ) - 4 := by
    have h1 := Nat.le_ceil ((4 + 8 * (R : ℝ)) / δ ^ 2)
    have h2 : (q : ℝ) + 4 ≤ b := by exact_mod_cast (by omega : q + 4 ≤ b)
    linarith
  have hR : 4 + 8 * (R : ℝ) ≤ δ ^ 2 * ((b : ℝ) - 4) := by
    have := mul_le_mul_of_nonneg_left hceil hδ2.le
    rwa [mul_div_cancel₀ _ hδ2.ne'] at this
  have hb4 : (4 : ℝ) ≤ b := by
    have : (0 : ℝ) ≤ (4 + 8 * (R : ℝ)) / δ ^ 2 := by positivity
    linarith
  have hmainR : (k : ℝ) * k ≤ b * c + b * R + k := by exact_mod_cast hmain
  have hLr1 : (2 * L : ℝ) ≤ b := by exact_mod_cast hL1
  have hLr2 : (b : ℝ) ≤ 2 * L + 1 := by exact_mod_cast hL2
  have hkL' : (k : ℝ) ≤ L := by exact_mod_cast hkL
  have hk2 : δ ^ 2 * (L : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hk 2
  have hL3 : ((b : ℝ) - 1) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ b - 1 := by linarith
    have : ((b : ℝ) - 1) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
    linarith
  have hL4 : δ ^ 2 * ((b : ℝ) - 1) ^ 2 ≤ δ ^ 2 * (4 * (L : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hL3 hδ2.le
  have hprod : (b : ℝ) * (4 + 8 * R) ≤ b * (δ ^ 2 * (b - 4)) :=
    mul_le_mul_of_nonneg_left hR (by positivity)
  have key : (b : ℝ) * (δ ^ 2 / 8 * b) ≤ b * c := by
    nlinarith
  have hbpos : (0 : ℝ) < b := by linarith
  exact le_of_mul_le_mul_left key hbpos

/-- If `m` has more than `2 |V|` representations, one of them avoids `V`. -/
lemma exists_rep_avoid {A : Set ℕ} {m : ℕ} (V : Finset ℕ) (h : 2 * #V < #(rep A m)) :
    ∃ a ∈ rep A m, a ∉ V ∧ m - a ∉ V := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : rep A m ⊆ V ∪ V.image (m - ·) := by
    intro a ha
    rw [mem_union, mem_image]
    by_cases haV : a ∈ V
    · exact Or.inl haV
    · refine Or.inr ⟨m - a, hcon a ha haV, ?_⟩
      have := (mem_rep.1 ha).1
      omega
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  have h2 : #(V.image (m - ·)) ≤ #V := card_image_le
  omega

/-- **Greedy step**: if every element of `Ms` has more than `2 (|U| + 2 |Ms|)` representations,
then the sum of `Ms` is a sum of `2 |Ms|` distinct elements of `A`, none of them in `U`. -/
lemma greedy (A : Set ℕ) (U : Finset ℕ) (Ms : Multiset ℕ)
    (hMs : ∀ m ∈ Ms, 2 * (#U + 2 * Multiset.card Ms) < #(rep A m)) :
    ∃ S : Finset ℕ, Disjoint U S ∧ (∀ x ∈ S, x ∈ A) ∧ #S = 2 * Multiset.card Ms ∧
      ∑ x ∈ S, x = Ms.sum := by
  classical
  induction Ms using Multiset.induction_on with
  | empty => exact ⟨∅, disjoint_empty_right _, by simp, by simp, by simp⟩
  | cons m Ms ih =>
    rw [Multiset.card_cons] at hMs
    obtain ⟨S, hUS, hSA, hScard, hSsum⟩ := ih fun x hx ↦ by
      have := hMs x (Multiset.mem_cons_of_mem hx)
      omega
    have hV : 2 * #(U ∪ S) < #(rep A m) := by
      have h1 := card_union_le U S
      have h2 := hMs m (Multiset.mem_cons_self m Ms)
      omega
    obtain ⟨a, ha, haV, hbV⟩ := exists_rep_avoid (U ∪ S) hV
    obtain ⟨ham, haA, hbA, hne⟩ := mem_rep.1 ha
    rw [mem_union, not_or] at haV hbV
    have hab : a ≠ m - a := by omega
    have haS : a ∉ insert (m - a) S := by
      rw [mem_insert, not_or]
      exact ⟨hab, haV.2⟩
    refine ⟨insert a (insert (m - a) S), ?_, ?_, ?_, ?_⟩
    · rw [disjoint_insert_right, disjoint_insert_right]
      exact ⟨haV.1, hbV.1, hUS⟩
    · intro x hx
      rw [mem_insert, mem_insert] at hx
      rcases hx with rfl | rfl | hx
      exacts [haA, hbA, hSA x hx]
    · rw [card_insert_of_notMem haS, card_insert_of_notMem hbV.2, hScard, Multiset.card_cons]
      ring
    · rw [sum_insert haS, sum_insert hbV.2, hSsum, Multiset.sum_cons]
      omega

end Erdos338Proof
