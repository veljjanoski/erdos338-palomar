module

public import Erdos338.Pairs
public import Erdos338.Residue
public import Erdos338.Shift

/-!
# Assembly

`restricted_of_density`: if every residue class modulo every `Q ≥ 1` contains a sum of distinct
elements of `A`, and `δ b ≤ |A ∩ [0, b)|` for all large `b` with `δ > 0`, then every large `n` is
a sum of a bounded number of distinct elements of `A`.

Let `M_R` be the set of numbers with at least `R` representations as a sum of two distinct elements
of `A`. For every `R`, `γ b ≤ |M_R ∩ [0, b)|` for all large `b`, with `γ = δ ^ 2 / 8`
(`pairs_dense`), so `usl` gives
`K`, independent of `R`, such that all large numbers `≡ K b₀ (mod d)` are sums of `K` elements of
`M_R`, with `d ≤ K`. Fix the residue mod `d` with a set `S₀` of distinct elements, chosen for the
modulus `K!` so that `|S₀| ≤ B` with `B` independent of `R`. With `R > 2 (B + 2 K)`, the `K`
elements of `M_R` can be written as sums of `2 K` distinct elements of `A` outside `S₀`
(`greedy`).
-/

@[expose] public section

open Finset
open scoped Nat

namespace Erdos338Proof

theorem restricted_of_density (A : Set ℕ)
    (hres : ∀ Q, 0 < Q → ∀ c, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ ∑ x ∈ S, x ≡ c [MOD Q])
    {δ : ℝ} (hδ : 0 < δ) {N₀ : ℕ} (hN₀ : ∀ b ≥ N₀, δ * b ≤ cnt A b) :
    ∃ t, ∀ᶠ n in Filter.atTop, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ #S ≤ t ∧ ∑ x ∈ S, x = n := by
  classical
  have hγ : 0 < δ ^ 2 / 8 := by positivity
  obtain ⟨K, hK⟩ := usl hγ
  have hQ : 0 < K ! := Nat.factorial_pos K
  obtain ⟨B, T, hBT⟩ := residue_uniform hQ (hres _ hQ)
  set R := 2 * (B + 2 * K) + 1 with hR
  obtain ⟨d, b₀, N', hd1, hdK, hcov⟩ := hK {m | R ≤ #(rep A m)} (pairs_dense hδ hN₀ R)
  have hdQ : d ∣ K ! := Nat.dvd_factorial hd1 hdK
  refine ⟨B + 2 * K, Filter.eventually_atTop.2 ⟨T + K * b₀ + d * N', fun n hn ↦ ?_⟩⟩
  obtain ⟨S₀, hS₀A, hS₀B, hS₀T, hS₀c⟩ := hBT (n - K * b₀)
  set s₀ := ∑ x ∈ S₀, x with hs₀
  have hmod : s₀ ≡ n - K * b₀ [MOD d] := Nat.ModEq.of_dvd hdQ hS₀c
  obtain ⟨x, hx⟩ := (Nat.modEq_iff_dvd' (by omega)).1 hmod
  have hxN : N' ≤ x := by
    by_contra h
    push Not at h
    have : d * x < d * N' := Nat.mul_lt_mul_of_pos_left h hd1
    omega
  obtain ⟨Ms, hMs1, hMs2, hMs3⟩ := hcov x hxN
  obtain ⟨Sp, hdisj, hSpA, hSpc, hSps⟩ := greedy A S₀ Ms fun m hm ↦ by
    have h : R ≤ #(rep A m) := hMs2 m hm
    rw [hMs1]
    omega
  refine ⟨S₀ ∪ Sp, fun y hy ↦ ?_, ?_, ?_⟩
  · rcases mem_union.1 hy with hy | hy
    exacts [hS₀A y hy, hSpA y hy]
  · rw [card_union_of_disjoint hdisj, hSpc, hMs1]
    omega
  · rw [sum_union hdisj, hSps, hMs3]
    omega

lemma ncard_inter_Iio (S : Set ℕ) (b : ℕ) : (S ∩ Set.Iio b).ncard = cnt S b := by
  classical
  have e : S ∩ Set.Iio b = ↑((range b).filter (· ∈ S)) := by
    ext x
    simp [and_comm]
  rw [e, Set.ncard_coe_finset]
  unfold cnt
  convert rfl

lemma ncard_Iio (b : ℕ) : (Set.Iio b).ncard = b := by
  have e : Set.Iio b = ↑(range b) := by
    ext x
    simp
  rw [e, Set.ncard_coe_finset, card_range]

end Erdos338Proof
