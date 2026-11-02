module

public import Mathlib

/-!
# Every residue class is a sum of distinct elements

If `A \ F` is a basis for every finite `F`, then for every modulus `Q ≥ 1` every residue class
mod `Q` contains a sum of distinct elements of `A` (`residue_of_robust`). Remove the finitely many
elements of `A` that lie in residue classes containing only finitely many elements of `A`; the
rest is still a basis, and in a sum of its elements each summand can be replaced by a different
element of the same (infinite) class. For a fixed `Q` the number of summands and their sum can be
bounded uniformly over all classes (`residue_uniform`).
-/

@[expose] public section

open Finset

namespace Erdos338Proof

theorem residue_of_robust (A : Set ℕ)
    (hrob : ∀ F : Set ℕ, F.Finite → ∃ h, ∀ᶠ m in Filter.atTop, ∃ S : Multiset ℕ,
      (∀ x ∈ S, x ∈ A \ F) ∧ Multiset.card S ≤ h ∧ S.sum = m)
    {Q : ℕ} (hQ : 0 < Q) (c : ℕ) :
    ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ ∑ x ∈ S, x ≡ c [MOD Q] := by
  classical
  set F : Set ℕ := {a | a ∈ A ∧ {x | x ∈ A ∧ x ≡ a [MOD Q]}.Finite} with hFdef
  have hF : F.Finite := by
    have hsub : F ⊆ ⋃ r ∈ Set.Iio Q,
        {x | x ∈ A ∧ x % Q = r ∧ {y | y ∈ A ∧ y % Q = r}.Finite} := by
      intro a ha
      simp only [Set.mem_iUnion, Set.mem_Iio]
      exact ⟨a % Q, Nat.mod_lt a hQ, ha.1, rfl, ha.2⟩
    refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio Q) fun r _ ↦ ?_) hsub
    by_cases hr : {y | y ∈ A ∧ y % Q = r}.Finite
    · exact hr.subset fun x hx ↦ ⟨hx.1, hx.2.1⟩
    · exact Set.Finite.subset Set.finite_empty fun x hx ↦ (hr hx.2.2).elim
  obtain ⟨h, hh⟩ := hrob F hF
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hh
  obtain ⟨Ms, hMs, -, hsum⟩ := hN (c + Q * N) (by nlinarith)
  -- replace the summands by distinct elements of the same classes
  have key : ∀ Ms : Multiset ℕ, (∀ x ∈ Ms, x ∈ A \ F) →
      ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ ∑ x ∈ S, x ≡ Ms.sum [MOD Q] := by
    intro Ms
    induction Ms using Multiset.induction_on with
    | empty => exact fun _ ↦ ⟨∅, by simp, by simp [Nat.ModEq.refl]⟩
    | cons a Ms ih =>
      intro hMs
      obtain ⟨S, hSA, hSsum⟩ := ih fun x hx ↦ hMs x (Multiset.mem_cons_of_mem hx)
      have ha := hMs a (Multiset.mem_cons_self a Ms)
      have hinf : {x | x ∈ A ∧ x ≡ a [MOD Q]}.Infinite := fun hfin ↦ ha.2 ⟨ha.1, hfin⟩
      obtain ⟨a', ⟨ha'A, ha'a⟩, ha'S⟩ := hinf.exists_notMem_finset S
      refine ⟨insert a' S, fun x hx ↦ ?_, ?_⟩
      · rcases mem_insert.1 hx with rfl | hx
        exacts [ha'A, hSA x hx]
      · rw [sum_insert ha'S, Multiset.sum_cons]
        exact ha'a.add hSsum
  obtain ⟨S, hSA, hS⟩ := key Ms hMs
  refine ⟨S, hSA, hS.trans ?_⟩
  rw [hsum]
  show (c + Q * N) % Q = c % Q
  exact Nat.add_mul_mod_self_left c Q N

/-- For a fixed modulus, the sets of `residue_of_robust` can be chosen with bounded size and sum. -/
lemma residue_uniform {A : Set ℕ} {Q : ℕ} (hQ : 0 < Q)
    (hres : ∀ c, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ ∑ x ∈ S, x ≡ c [MOD Q]) :
    ∃ B T : ℕ, ∀ c, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ #S ≤ B ∧ ∑ x ∈ S, x ≤ T ∧
      ∑ x ∈ S, x ≡ c [MOD Q] := by
  choose f hfA hf using hres
  refine ⟨(range Q).sup fun c ↦ #(f c), (range Q).sup fun c ↦ ∑ x ∈ f c, x,
    fun c ↦ ⟨f (c % Q), hfA _, ?_, ?_, ?_⟩⟩
  · exact le_sup (f := fun c ↦ #(f c)) (mem_range.2 (Nat.mod_lt c hQ))
  · exact le_sup (f := fun c ↦ ∑ x ∈ f c, x) (mem_range.2 (Nat.mod_lt c hQ))
  · exact (hf _).trans (Nat.mod_modEq c Q)

end Erdos338Proof
