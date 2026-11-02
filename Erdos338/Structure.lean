module

public import Erdos338.Covering

/-!
# Sums of a bounded number of elements of a set of positive density

If `E ⊆ ℕ` contains `0`, its elements generate `ℤ`, and `E` has lower density at least `γ > 0`
(in the form `γ b ≤ |E ∩ [0, b)|` for all large `b`), then every large integer is a sum of exactly
`K` elements of `E`, where `K` depends only on `γ` (`cover`). The proof applies
`Erdos338Proof.nsmul_eq_univ` to `E ∩ [0, ℓ]` in `ZMod ℓ` for suitable `ℓ ∈ E`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace Erdos338Proof

open Classical in
/-- `cnt S b` is the number of elements of `S` below `b`. -/
noncomputable def cnt (S : Set ℕ) (b : ℕ) : ℕ := #((range b).filter (· ∈ S))

lemma cnt_le_of_subset {S : Set ℕ} {b c : ℕ} (h : ∀ x ∈ S, x < b → x < c) : cnt S b ≤ c := by
  classical
  unfold cnt
  calc #((range b).filter (· ∈ S)) ≤ #(range c) := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_range] at hx
        exact mem_range.2 (h x hx.2 hx.1)
    _ = c := card_range c

/-- One dense step: for a large `ℓ ∈ E`, every `x` with `h ℓ ≤ x` and `x + h ℓ ≤ m ℓ` is a sum
of `m` elements of `E`. -/
lemma dense_step {γ : ℝ} (hγ : 0 < γ) {h : ℕ} (hh : (4 / γ : ℝ) < h) {E : Set ℕ}
    {F : Finset ℕ} (hFE : (F : Set ℕ) ⊆ E)
    (h1 : (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) {N : ℕ}
    (hN : ∀ b ≥ N, γ * b ≤ cnt E b) (hE0 : 0 ∈ E) {ℓ : ℕ} (hℓE : ℓ ∈ E)
    (hℓN : N ≤ ℓ) (hℓF : F.sup id ≤ ℓ) (hℓγ : (2 / γ : ℝ) ≤ ℓ) {m x : ℕ}
    (hx1 : h * ℓ ≤ x) (hx2 : x + h * ℓ ≤ m * ℓ) :
    ∃ M : Multiset ℕ, M.card = m ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by
  classical
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < 2 / γ := by positivity
    exact_mod_cast this.trans_le hℓγ
  have : NeZero ℓ := ⟨hℓpos.ne'⟩
  set A := (range (ℓ + 1)).filter (· ∈ E) with hA
  have hA0 : 0 ∈ A := by simp [hA, hE0]
  have hAℓ : ℓ ∈ A := by simp [hA, hℓE]
  have hle : ∀ a ∈ A, a ≤ ℓ := by
    intro a ha
    simp only [hA, mem_filter, mem_range] at ha
    omega
  set f := Nat.castAddMonoidHom (ZMod ℓ)
  set S := A.image f with hS
  -- `S` is large
  have hAcnt : γ * ℓ ≤ #A := by
    have h1 := hN ℓ hℓN
    have h2 : cnt E ℓ ≤ #A := by
      unfold cnt
      apply card_le_card
      intro a ha
      simp only [mem_filter, mem_range] at ha
      rw [hA]
      exact mem_filter.2 ⟨mem_range.2 (by omega), ha.2⟩
    exact h1.trans (by exact_mod_cast h2)
  have hScard : #A ≤ #S + 1 := by
    have hinj : Set.InjOn f (A.erase ℓ : Set ℕ) := by
      intro a ha b hb hab
      simp only [coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at ha hb
      have ha' : a < ℓ := lt_of_le_of_ne (hle a ha.1) ha.2
      have hb' : b < ℓ := lt_of_le_of_ne (hle b hb.1) hb.2
      have := congrArg ZMod.val hab
      simp only [f, Nat.coe_castAddMonoidHom, ZMod.val_natCast] at this
      rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
    have h1 : #(A.erase ℓ) ≤ #S := by
      rw [← card_image_of_injOn hinj]
      exact card_le_card (image_subset_image (erase_subset ℓ A))
    have h2 := card_erase_add_one hAℓ
    omega
  have hcard : 2 * Fintype.card (ZMod ℓ) ≤ h * #S := by
    rw [ZMod.card]
    have hS' : (γ * ℓ - 1 : ℝ) ≤ #S := by
      have : (#A : ℝ) ≤ #S + 1 := by exact_mod_cast hScard
      linarith
    have hpos : (0 : ℝ) ≤ γ * ℓ - 1 := by
      have : γ * (2 / γ) ≤ γ * ℓ := mul_le_mul_of_nonneg_left hℓγ hγ.le
      rw [mul_div_cancel₀ _ hγ.ne'] at this
      linarith
    have key : (4 / γ) * (γ * ℓ - 1) ≤ (h : ℝ) * #S :=
      mul_le_mul hh.le hS' hpos (by positivity)
    have e : (4 / γ) * (γ * ℓ - 1) = 4 * ℓ - 4 / γ := by field_simp
    have h4 : (4 / γ : ℝ) ≤ 2 * ℓ := by
      have : (4 / γ : ℝ) = 2 * (2 / γ) := by ring
      linarith
    have : (2 * ℓ : ℝ) ≤ h * #S := by linarith
    exact_mod_cast this
  -- `S` generates `ZMod ℓ`
  have hgen : AddSubgroup.closure (S : Set (ZMod ℓ)) = ⊤ := by
    set φ : ℤ →ₗ[ℤ] ZMod ℓ := (Int.castAddHom (ZMod ℓ)).toIntLinearMap
    have hmap : (1 : ZMod ℓ) ∈ Submodule.span ℤ (S : Set (ZMod ℓ)) := by
      have h2 : φ 1 ∈ Submodule.span ℤ (φ '' ((Nat.cast : ℕ → ℤ) '' F)) := by
        rw [← Submodule.map_span]
        exact Submodule.mem_map_of_mem h1
      have e1 : φ 1 = 1 := by simp [φ]
      rw [e1] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, ?_, by simp [φ, f]⟩)
      simp only [hA, mem_filter, mem_range]
      refine ⟨?_, hFE hn⟩
      have : n ≤ F.sup id := Finset.le_sup (f := id) hn
      omega
    replace hmap : (1 : ZMod ℓ) ∈ (Submodule.span ℤ (S : Set (ZMod ℓ))).toAddSubgroup := hmap
    rw [Submodule.span_int_eq_addSubgroupClosure] at hmap
    rw [eq_top_iff]
    intro z _
    have : (z.val : ℕ) • (1 : ZMod ℓ) ∈ AddSubgroup.closure (S : Set (ZMod ℓ)) :=
      AddSubgroup.nsmul_mem _ hmap _
    simpa using this
  have h0S : (0 : ZMod ℓ) ∈ S := Finset.mem_image.2 ⟨0, hA0, by simp [f]⟩
  have hh1 : 1 ≤ h := by
    have : (0 : ℝ) < h := lt_of_le_of_lt (by positivity) hh
    exact_mod_cast this
  have huniv := nsmul_eq_univ h0S hgen hh1 hcard
  obtain ⟨M, hMc, hMA, hMs⟩ := exists_multiset_of_nsmul_eq_univ hA0 hAℓ hle huniv hx1 hx2
  refine ⟨M, hMc, fun a ha ↦ ?_, hMs⟩
  have := hMA a ha
  simp only [hA, mem_filter] at this
  exact this.2

/-- A set of lower density at least `γ` has an element in `(y, C y]` for all large `y`, once
`2 / γ ≤ C`. -/
lemma exists_mem_Ioc {γ : ℝ} (hγ : 0 < γ) {C : ℕ} (hC : (2 / γ : ℝ) ≤ C) {E : Set ℕ} {N : ℕ}
    (hN : ∀ b ≥ N, γ * b ≤ cnt E b) {y : ℕ} (hyN : N ≤ y) (hy2 : 2 ≤ y) :
    ∃ ℓ ∈ E, y < ℓ ∧ ℓ ≤ C * y := by
  by_contra hcon
  push Not at hcon
  have hC1 : 1 ≤ C := by
    have : (0 : ℝ) < C := lt_of_lt_of_le (by positivity) hC
    exact_mod_cast this
  have hle : cnt E (C * y + 1) ≤ y + 1 := by
    apply cnt_le_of_subset
    intro x hx hxb
    by_contra hxy
    exact absurd (hcon x hx (by omega)) (by omega)
  have hb : N ≤ C * y + 1 := by nlinarith
  have h1 := hN _ hb
  have h2 : (cnt E (C * y + 1) : ℝ) ≤ y + 1 := by exact_mod_cast hle
  have h3 : (2 : ℝ) ≤ γ * C := by
    have := mul_le_mul_of_nonneg_left hC hγ.le
    rwa [mul_div_cancel₀ _ hγ.ne'] at this
  have hy : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  push_cast at h1
  nlinarith

/-- **Covering**: for `γ > 0` there is `K` such that every `E ⊆ ℕ` containing `0`, whose elements
generate `ℤ`, and with `γ b ≤ |E ∩ [0, b)|` for all large `b`, contains every large integer as a
sum of exactly `K` elements. -/
theorem cover {γ : ℝ} (hγ : 0 < γ) : ∃ K : ℕ, (2 / γ : ℝ) < K ∧ ∀ E : Set ℕ, 0 ∈ E →
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ E ∧ (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) →
    (∃ N, ∀ b ≥ N, γ * b ≤ cnt E b) →
    ∃ N', ∀ x ≥ N', ∃ M : Multiset ℕ, M.card = K ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by
  set h : ℕ := ⌈4 / γ⌉₊ + 1 with hhdef
  set C : ℕ := ⌈2 / γ⌉₊ + 1 with hCdef
  have hh : (4 / γ : ℝ) < h := by
    rw [hhdef]; push_cast; linarith [Nat.le_ceil (4 / γ)]
  have hC : (2 / γ : ℝ) ≤ C := by
    rw [hCdef]; push_cast; linarith [Nat.le_ceil (2 / γ)]
  have hh1 : 1 ≤ h := by omega
  have hC1 : 1 ≤ C := by omega
  refine ⟨h * (C + 1), ?_, ?_⟩
  · have : (h : ℝ) ≤ h * (C + 1) := by
      have : (1 : ℝ) ≤ C + 1 := by linarith [(Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
      nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
    have h42 : (2 / γ : ℝ) < 4 / γ := by
      apply div_lt_div_of_pos_right (by norm_num) hγ
    push_cast
    linarith
  rintro E hE0 ⟨F, hFE, h1⟩ ⟨N, hN⟩
  set L : ℕ := N + F.sup id + ⌈2 / γ⌉₊ + 2 with hL
  refine ⟨h * C * (L + 1), fun x hx ↦ ?_⟩
  have hhC : 0 < h * C := Nat.mul_pos (by omega) (by omega)
  set y := x / (h * C) with hy
  have hyL : L + 1 ≤ y := by
    rw [hy]
    exact (Nat.le_div_iff_mul_le hhC).2 (by rw [mul_comm]; exact hx)
  obtain ⟨ℓ, hℓE, hyℓ, hℓy⟩ := exists_mem_Ioc hγ hC hN (y := y) (by omega) (by omega)
  have hℓγ : (2 / γ : ℝ) ≤ ℓ := by
    have : ⌈2 / γ⌉₊ ≤ ℓ := by omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  apply dense_step hγ hh hFE h1 hN hE0 hℓE (by omega) (by omega) hℓγ
  · -- `h ℓ ≤ h C y ≤ x`
    calc h * ℓ ≤ h * (C * y) := Nat.mul_le_mul_left h hℓy
      _ = y * (h * C) := by ring
      _ ≤ x := Nat.div_mul_le_self x (h * C)
  · -- `x < h C (y + 1) ≤ h C ℓ`
    have hx' : x < (y + 1) * (h * C) := by rw [hy, mul_comm]; exact Nat.lt_mul_div_succ x hhC
    have : (y + 1) * (h * C) ≤ ℓ * (h * C) := Nat.mul_le_mul_right _ hyℓ
    nlinarith

end Erdos338Proof
