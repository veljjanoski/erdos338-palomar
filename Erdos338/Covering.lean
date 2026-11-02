module

public import Mathlib
public import Erdos338.Kneser.Kneser

/-!
# Sums of many copies of a dense finite set

Kneser's theorem for `h` summands, and its consequence for a set `A ⊆ [0, ℓ]` containing `0` and
`ℓ`: if `A` is not too small, every residue mod `ℓ` is a sum of `h` elements of `A`, and so every
integer in `[h ℓ, (m - h) ℓ]` is a sum of exactly `m` elements of `A`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace Erdos338Proof

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- `h • (s + H) = h • s + H` when `H + H = H`. -/
lemma nsmul_add_stab (s H : Finset G) (hH : H + H = H) {h : ℕ} (hh : 1 ≤ h) :
    h • (s + H) = h • s + H := by
  induction h, hh using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [succ_nsmul, ih, succ_nsmul]
    calc n • s + H + (s + H) = n • s + s + (H + H) := by abel
      _ = n • s + s + H := by rw [hH]

/-- **Kneser's theorem for `h` summands**: with `H` the stabilizer of `h • s`,
`h |s + H| ≤ |h • s| + (h - 1) |H|`. -/
lemma kneser_nsmul {h : ℕ} (hh : 1 ≤ h) :
    ∀ s : Finset G, s.Nonempty →
      h * #(s + (h • s).addStab) ≤ #(h • s) + (h - 1) * #(h • s).addStab := by
  induction h, hh using Nat.le_induction with
  | base =>
    intro s _
    simp [add_addStab]
  | succ n hn ih =>
    intro s hs
    set H := ((n + 1) • s).addStab with hHdef
    have hns : (n • s).Nonempty := hs.nsmul
    have hn1 : ((n + 1) • s).Nonempty := hs.nsmul
    have hHH : H + H = H := addStab_add_addStab _
    have hsH : (s + H).Nonempty := hs.add hn1.addStab
    -- the stabilizer of `n • (s + H) = n • s + H` is `H`
    have hnsH : n • (s + H) = n • s + H := nsmul_add_stab s H hHH hn
    have hstab : (n • (s + H)).addStab = H := by
      rw [hnsH]
      apply le_antisymm
      · calc (n • s + H).addStab ⊆ (n • s + H + s).addStab := subset_addStab_add_left hs
          _ = ((n + 1) • s + H).addStab := by rw [succ_nsmul]; congr 1; abel
          _ = H := by rw [add_addStab]
      · calc H = H.addStab := (addStab_idem _).symm
          _ ⊆ (n • s + H).addStab := subset_addStab_add_right hns
    have key := ih (s + H) hsH
    rw [hstab, hnsH, add_assoc, hHH] at key
    -- Kneser for `n • s` and `s`
    have hk := add_kneser (n • s) s
    rw [← succ_nsmul] at hk
    rw [← hHdef] at hk
    -- combine
    have hsub : (n - 1) * #H + #H = n * #H := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
    have hexp : (n + 1) * #(s + H) = n * #(s + H) + #(s + H) := by ring
    simp only [Nat.add_sub_cancel]
    omega

/-- In a finite abelian group `G`, if `s` contains `0`, generates `G` and `2 |G| ≤ h |s|`, then
`h • s = G`. -/
lemma nsmul_eq_univ [Fintype G] {s : Finset G} (h0 : (0 : G) ∈ s)
    (hgen : AddSubgroup.closure (s : Set G) = ⊤) {h : ℕ} (hh : 1 ≤ h)
    (hcard : 2 * Fintype.card G ≤ h * #s) : h • s = univ := by
  by_contra hne
  have hs : s.Nonempty := ⟨0, h0⟩
  set T := h • s with hTdef
  have hT : T.Nonempty := hs.nsmul
  set H := T.addStab with hHdef
  have hH0 : (0 : G) ∈ H := hT.zero_mem_addStab
  have hHstab : (H : Set G) = AddAction.stabilizer G (T : Set G) := coe_addStab hT
  have mem_H : ∀ {k : G}, k ∈ H ↔ k ∈ AddAction.stabilizer G (T : Set G) := by
    intro k; rw [← Finset.mem_coe, hHstab, SetLike.mem_coe]
  -- `T` is a union of `H`-cosets that misses a coset, so `|T| + |H| ≤ |G|`
  obtain ⟨y, hy⟩ : ∃ y, y ∉ T := by
    by_contra hall
    exact hne (eq_univ_of_forall fun x ↦ by by_contra hx; exact hall ⟨x, hx⟩)
  have hdisj : Disjoint T (y +ᵥ H) := by
    rw [Finset.disjoint_left]
    intro z hzT hzH
    obtain ⟨k, hk, rfl⟩ := Finset.mem_vadd_finset.1 hzH
    have hnk : -k ∈ AddAction.stabilizer G (T : Set G) := neg_mem (mem_H.1 hk)
    have : -k +ᵥ (y +ᵥ k) ∈ (T : Set G) := by
      rw [← AddAction.mem_stabilizer_iff.1 hnk]
      exact Set.vadd_mem_vadd_set (Finset.mem_coe.2 hzT)
    apply hy
    have e : -k +ᵥ (y +ᵥ k) = y := by simp [vadd_eq_add]
    rw [e] at this
    exact Finset.mem_coe.1 this
  have hTH : #T + #H ≤ Fintype.card G := by
    rw [← card_vadd_finset y H, ← card_union_of_disjoint hdisj]
    exact card_le_univ _
  -- `s + H` is a union of at least two `H`-cosets
  have hsub : s ⊆ s + H := by
    intro x hx
    exact Finset.mem_add.2 ⟨x, hx, 0, hH0, add_zero x⟩
  have hHsub : H ⊆ s + H := by
    intro x hx
    exact Finset.mem_add.2 ⟨0, h0, x, hx, zero_add x⟩
  have hdvd : #H ∣ #(s + H) := card_addStab_dvd_card_add_addStab s T
  have hHpos : 0 < #H := card_pos.2 ⟨0, hH0⟩
  have hne2 : #(s + H) ≠ #H := by
    intro heq
    have hsH : s + H = H := (eq_of_subset_of_card_le hHsub heq.le).symm
    have hsH' : (s : Set G) ⊆ AddAction.stabilizer G (T : Set G) := by
      intro x hx
      exact mem_H.1 (hsH ▸ hsub (Finset.mem_coe.1 hx))
    have htop : AddAction.stabilizer G (T : Set G) = ⊤ :=
      eq_top_iff.2 (hgen ▸ (AddSubgroup.closure_le _).2 hsH')
    apply hne
    apply eq_univ_of_forall
    intro g
    obtain ⟨t, ht⟩ := hT
    have hg : g - t ∈ AddAction.stabilizer G (T : Set G) := htop ▸ AddSubgroup.mem_top _
    have : (g - t) +ᵥ t ∈ (T : Set G) := by
      rw [← AddAction.mem_stabilizer_iff.1 hg]
      exact Set.vadd_mem_vadd_set (Finset.mem_coe.2 ht)
    simpa [vadd_eq_add] using this
  have h2H : 2 * #H ≤ #(s + H) := by
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : c ≠ 1 := by rintro rfl; exact hne2 (by rw [hc, mul_one])
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hne' : (s + H).Nonempty := hs.add ⟨0, hH0⟩
      rw [mul_zero, card_eq_zero] at hc
      exact hne'.ne_empty hc
    rw [hc]
    have : 2 ≤ c := by omega
    nlinarith
  have hsle : #s ≤ #(s + H) := card_le_card hsub
  have hK := kneser_nsmul hh s hs
  rw [← hTdef, ← hHdef] at hK
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hK
  have h3 : k * (2 * #H) ≤ k * #(s + H) := Nat.mul_le_mul_left k h2H
  have h4 : (k + 1) * #s ≤ (k + 1) * #(s + H) := Nat.mul_le_mul_left _ hsle
  nlinarith

/-- An element of `h • (A.image f)` is the image of a sum of `h` elements of `A`. -/
lemma exists_multiset_of_mem_nsmul_image {f : ℕ →+ G} {A : Finset ℕ} :
    ∀ {h : ℕ} {z : G}, z ∈ h • A.image f →
      ∃ M : Multiset ℕ, M.card = h ∧ (∀ a ∈ M, a ∈ A) ∧ f M.sum = z := by
  intro h
  induction h with
  | zero =>
    intro z hz
    rw [zero_nsmul, Finset.mem_zero] at hz
    exact ⟨0, by simp, by simp, by simp [hz]⟩
  | succ n ih =>
    intro z hz
    rw [succ_nsmul, Finset.mem_add] at hz
    obtain ⟨x, hx, w, hw, rfl⟩ := hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨M, hMc, hMA, hMs⟩ := ih hx
    refine ⟨a ::ₘ M, by simp [hMc], ?_, ?_⟩
    · intro b hb
      rcases Multiset.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact hMA b hb
    · rw [Multiset.sum_cons, map_add, hMs, add_comm]

/-- If every residue mod `ℓ` is a sum of `h` elements of `A ⊆ [0, ℓ]` and `0, ℓ ∈ A`, then every
`x` with `h ℓ ≤ x` and `x + h ℓ ≤ m ℓ` is a sum of exactly `m` elements of `A`. -/
lemma exists_multiset_of_nsmul_eq_univ {A : Finset ℕ} {ℓ h m x : ℕ} [NeZero ℓ]
    (hA0 : 0 ∈ A) (hAℓ : ℓ ∈ A) (hle : ∀ a ∈ A, a ≤ ℓ)
    (huniv : h • A.image (Nat.castAddMonoidHom (ZMod ℓ)) = univ)
    (hx1 : h * ℓ ≤ x) (hx2 : x + h * ℓ ≤ m * ℓ) :
    ∃ M : Multiset ℕ, M.card = m ∧ (∀ a ∈ M, a ∈ A) ∧ M.sum = x := by
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
  obtain ⟨M₀, hc, hA, hs⟩ := exists_multiset_of_mem_nsmul_image
    (huniv ▸ Finset.mem_univ (x : ZMod ℓ))
  simp only [Nat.coe_castAddMonoidHom] at hs
  have hsum : M₀.sum ≤ h * ℓ := by
    rw [← hc]
    exact Multiset.sum_le_card_nsmul _ _ fun a ha ↦ hle a (hA a ha)
  have hmod : M₀.sum ≡ x [MOD ℓ] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hs
  obtain ⟨j, hj⟩ : ℓ ∣ x - M₀.sum := (Nat.modEq_iff_dvd' (by omega)).1 hmod
  have hjm : h + j ≤ m := by
    have : j * ℓ ≤ x := by rw [mul_comm]; omega
    by_contra hcon
    have : m * ℓ < (h + j) * ℓ := Nat.mul_lt_mul_of_pos_right (by omega) hℓ
    nlinarith
  refine ⟨M₀ + Multiset.replicate j ℓ + Multiset.replicate (m - (h + j)) 0, ?_, ?_, ?_⟩
  · simp [hc]; omega
  · intro a ha
    simp only [Multiset.mem_add, Multiset.mem_replicate] at ha
    rcases ha with (ha | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact hA a ha
    · exact hAℓ
    · exact hA0
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_zero, add_zero]
    rw [mul_comm j ℓ, ← hj]
    omega

end Erdos338Proof
