module

public import Mathlib

/-!
# Erdős Problem 338: restricted order of robust sets of positive lower density

A partial result on Erdős Problem 338
([erdosproblems.com/338](https://www.erdosproblems.com/338)). Erdős and Graham asked whether a set
$A$ such that $A \setminus F$ is a basis for every finite set $F$ must have a restricted order.
The statement below answers this positively when $A$ has positive lower density.

The definitions `Set.partialDensity`, `Set.lowerDensity`, `Erdos338.HasOrder` and
`Erdos338.HasRestrictedOrder` are copied verbatim from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (Apache-2.0), files
`FormalConjecturesForMathlib/Data/Set/Density.lean` (Copyright 2025 The Formal Conjectures
Authors) and `FormalConjectures/ErdosProblems/338.lean` (Copyright 2026 The Formal Conjectures
Authors) at commit `d995ef5d306637c0a2e489c7e579647168d7df2f`, with the same names. The first
(robustness) hypothesis on $A$ is the one of
`Erdos338.erdos_338.variants.basis_after_finite_removal` there, and the density hypothesis is
written as in `Erdos338.erdos_338.variants.kelly_lowerDensity`. Here `A.lowerDensity` is the lower
asymptotic density $\liminf_{b \to \infty} |A \cap [0, b)| / b$.

*References:*
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
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
  sorry

end Erdos338
