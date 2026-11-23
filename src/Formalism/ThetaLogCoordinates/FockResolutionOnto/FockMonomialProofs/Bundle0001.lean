module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementD

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.EArith
section
namespace Formalism.InvariantFactorPaths.L4

open Finset

theorem eArith_ge : ∀ (s : ℕ) (ka : ℕ → ℤ) (β : ℕ → ℕ) (c : ℤ),
    (∀ i, i + 1 < s → ka (i + 1) + β (i + 1) ≤ ka i) → (0 < s → ka 0 + β 0 ≤ c) →
    (∑ a ∈ range s, (β a : ℤ)) ≤
      (c - (∑ a ∈ range s, (β a : ℤ)) + 1) * (∑ a ∈ range s, (β a : ℤ)) - (∑ a ∈ range s, (β a : ℤ) * ka a) +
        ∑ b ∈ range s, ∑ a ∈ range b, ((β a : ℤ) + 1) * (β b : ℤ) := by
  intro s ka β c h1 h2
  have key : ∀ a, a < s → ka a + ∑ a' ∈ range (a + 1), (β a' : ℤ) ≤ c := by
    intro a
    induction a with
    | zero =>
      intro ha
      simpa using h2 ha
    | succ a ih =>
      intro ha
      have h3 := h1 a ha
      have h4 := ih (by omega)
      rw [Finset.sum_range_succ]
      linarith
  clear h2
  induction s with
  | zero => simp
  | succ s ihs =>
    have IH := ihs (fun i hi => h1 i (by omega)) (fun a ha => key a (by omega))
    have hk := key s (by omega)
    rw [Finset.sum_range_succ] at hk
    have hinner : ∑ a ∈ range s, ((β a : ℤ) + 1) * (β s : ℤ) = (∑ a ∈ range s, (β a : ℤ) + s) * β s := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      simp
    simp only [Finset.sum_range_succ, hinner]
    have hb : (0 : ℤ) ≤ β s := Nat.cast_nonneg _
    have hs : (0 : ℤ) ≤ s := Nat.cast_nonneg _
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hk), mul_nonneg hb hs]

theorem exponent_arithmetic_holds : EArith := by
  intro s ka β c h1 h2 h3
  have h4 := eArith_ge s ka β c h1 h2
  have h5 : (1 : ℤ) ≤ ∑ a ∈ range s, (β a : ℤ) := by exact_mod_cast h3
  linarith

end Formalism.InvariantFactorPaths.L4
end

-- bundled from Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.Sl2RaisePowSuccLowerApplyEq
section
namespace Formalism.InvariantFactorPaths.L4

section
variable {k V : Type} [Field k] [CharZero k] [AddCommGroup V] [Module k V] {e f h : V →ₗ[k] V}

theorem sl2_weight_raise_pow_apply_eq (he : ∀ x, h (e x) - e (h x) = (2 : k) • e x) {u : V} {μ : k} (hu : h u = μ • u) (m : ℕ) :
    h ((e ^ m) u) = (μ + 2 * (m : k)) • (e ^ m) u := by
  induction m with
  | zero => simp [hu]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h1 := he ((e ^ m) u)
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem sl2_raise_pow_succ_lower_apply_eq (he : ∀ x, h (e x) - e (h x) = (2 : k) • e x) (hef : ∀ x, e (f x) - f (e x) = h x)
    {u : V} {μ : k} (hu : h u = μ • u) (m : ℕ) :
    (e ^ (m + 1)) (f u) = f ((e ^ (m + 1)) u) + (((m : k) + 1) * (μ + (m : k))) • (e ^ m) u := by
  induction m with
  | zero =>
    have h1 := hef u
    rw [sub_eq_iff_eq_add] at h1
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero, one_mul]
    rw [h1, hu, add_comm]
  | succ m ih =>
    have hs : e ((e ^ m) u) = (e ^ (m + 1)) u := by rw [pow_succ', Module.End.mul_apply]
    rw [pow_succ' e (m + 1), Module.End.mul_apply, Module.End.mul_apply, ih, map_add (f := _), map_smul]
    have h1 := hef ((e ^ (m + 1)) u)
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, sl2_weight_raise_pow_apply_eq he hu (m + 1), hs, add_comm (_ • _) (f _), add_assoc, ← add_smul]
    congr 1
    congr 1
    push_cast
    ring

theorem sl2_eq_zero_of_lower_zero_of_raise_pow_zero (he : ∀ x, h (e x) - e (h x) = (2 : k) • e x) (hef : ∀ x, e (f x) - f (e x) = h x)
    {u : V} {μ : ℤ} (hu : h u = ((μ : ℤ) : k) • u) (hf : f u = 0) :
    ∀ j : ℕ, μ + j ≤ 0 → (e ^ j) u = 0 → u = 0 := by
  intro j
  induction j with
  | zero =>
    intro _ h0
    simpa using h0
  | succ j ih =>
    intro hj h0
    apply ih (by omega)
    have hc := sl2_raise_pow_succ_lower_apply_eq he hef hu j
    rw [hf, map_zero, h0, map_zero, zero_add] at hc
    have hne : ((j : k) + 1) * (((μ : ℤ) : k) + (j : k)) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Nat.succ_ne_zero j
      · have h5 : (μ + j : ℤ) ≠ 0 := by omega
        exact_mod_cast h5
    exact (smul_eq_zero.mp hc.symm).resolve_left hne

end

theorem sl2_injectivity_holds : Sl2Injective := by
  intro k V _ _ _ _ e f h he hf hef u μ j hu hex hj h0
  obtain ⟨s, hs⟩ := hex
  induction s generalizing u μ j with
  | zero => simpa using hs
  | succ s ih =>
    have hfu : f u = 0 := by
      apply ih (f u) (μ - 2) (j + 1)
      · have h1 := hf u
        rw [hu, map_smul, sub_eq_iff_eq_add] at h1
        rw [h1]
        push_cast
        rw [sub_smul]
        abel
      · omega
      · rw [sl2_raise_pow_succ_lower_apply_eq he hef hu j, pow_succ', Module.End.mul_apply, h0]
        simp
      · rw [pow_succ, Module.End.mul_apply] at hs
        exact hs
    exact sl2_eq_zero_of_lower_zero_of_raise_pow_zero he hef hu hfu j hj h0

end Formalism.InvariantFactorPaths.L4
end

