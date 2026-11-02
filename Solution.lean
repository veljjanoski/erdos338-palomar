module

public import Mathlib
public import Erdos338

/-!
# Erdős Problem 338: restricted order of robust sets of positive lower density

Proof of the statement of `Challenge.lean`. The definitions are repeated verbatim.

Let `A` have lower density greater than `δ > 0`, and let `A \ F` be a basis for every finite `F`.

1. For every modulus `Q ≥ 1`, every residue class mod `Q` contains a sum of distinct elements of
   `A` (`Erdos338Proof.residue_of_robust`): remove the elements of `A` in residue classes that
   contain only finitely many of them, write a number of the given class as a sum of elements of
   what is left, and replace the summands one by one by distinct elements of the same classes.
2. For every `R`, the set `M_R` of numbers with at least `R` representations `a + b` with
   `a ≠ b` in `A` has lower density at least `δ ^ 2 / 8` (`Erdos338Proof.pairs_dense`), by
   counting pairs.
3. There is `K`, depending only on `δ`, such that every set of lower density at least `δ ^ 2 / 8`
   contains, as sums of exactly `K` of its elements, all large numbers of one residue class
   mod some `d ≤ K` (`Erdos338Proof.usl`). This uses Kneser's theorem for finite abelian groups
   (`Finset.add_kneser`, from Yaël Dillies and Mantas Bakšys) in `ZMod ℓ`; see
   `Erdos338Proof.nsmul_eq_univ` and `Erdos338Proof.cover`.
4. Fix the residue with a set `S₀` from step 1 for the modulus `K!`, so that `|S₀|` is bounded
   independently of `R`. With `R` large, each of the `K` elements of `M_R` is `a + b` with `a`,
   `b` not used before (`Erdos338Proof.greedy`). So every large number is a sum of at most
   `|S₀| + 2 K` distinct elements of `A` (`Erdos338Proof.restricted_of_density`).
-/

@[expose] public section

open Filter

open scoped Topology

namespace Set

/--
Given a set `S` and an element `b` in an order `β`, where all intervals bounded above are finite,
we define the partial density of `S` (relative to a set `A`) to be the proportion of elements in
`{x ∈ A | x < b}` that lie in `S ∩ A`.

This definition was inspired from https://github.com/b-mehta/unit-fractions
-/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

/--
Given a set `S` in an order `β`, where all intervals bounded above are finite, we define the lower
density of `S` (relative to a set `A`) to be the liminf of the partial densities of `S`
(relative to `A`) for `b → ∞`.
-/
noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

end Set

namespace Erdos338

/-- `HasOrder A h` means that $A$ is a basis of order $h$: every sufficiently large natural number
is a sum of at most $h$ elements of $A$, with repetition allowed.

The summands form a `Multiset`, so repetition is allowed. Allowing at most $h$ summands makes the
notion independent of whether $0 \in A$. With exactly $h$ summands, as in
`Set.IsAsymptoticAddBasisOfOrder`, this notion is `(insert 0 A).IsAsymptoticAddBasisOfOrder h`. -/
def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = m

/-- `HasRestrictedOrder A t` means that every sufficiently large natural number is a sum of at most
$t$ distinct elements of $A$.

The summands form a `Finset`, so they are distinct. A summand $0$ never helps, so the notion does
not depend on whether $0 \in A$. -/
def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ t ∧ ∑ x ∈ S, x = m

/--
If $A \setminus F$ is a basis for every finite set $F$ and $A$ has positive lower density, then $A$
has a restricted order: every sufficiently large integer is a sum of a bounded number of distinct
elements of $A$.
-/
theorem erdos_338.variants.lowerDensity_pos :
    ∀ A : Set ℕ, (∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) → 0 < A.lowerDensity →
      ∃ t, HasRestrictedOrder A t := by
  intro A hrob hpos
  -- `δ = lowerDensity / 2` is eventually a lower bound for `|A ∩ [0, b)| / b`
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ b ≥ N₀, A.lowerDensity / 2 * b ≤ Erdos338Proof.cnt A b := by
    have hlt : A.lowerDensity / 2 < atTop.liminf fun b : ℕ ↦ A.partialDensity Set.univ b :=
      half_lt_self hpos
    have hev := eventually_lt_of_lt_liminf hlt (isBoundedUnder_of_eventually_ge (a := 0)
      (Eventually.of_forall fun b ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N + 1, fun b hb ↦ ?_⟩
    have h := hN b (by omega)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Erdos338Proof.ncard_inter_Iio,
      Erdos338Proof.ncard_Iio] at h
    have hb : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    rw [lt_div_iff₀ hb] at h
    exact h.le
  obtain ⟨t, ht⟩ := Erdos338Proof.restricted_of_density A
    (fun Q hQ c ↦ Erdos338Proof.residue_of_robust A hrob hQ c) (half_pos hpos) hN₀
  exact ⟨t, ht⟩

end Erdos338
