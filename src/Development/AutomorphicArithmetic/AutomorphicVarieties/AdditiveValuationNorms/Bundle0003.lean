module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsAlt
section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.lift :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (g : Module.End ℤ_[l] X), GenBy l R X →
      ∃ S : Matrix (Fin R) (Fin R) ℤ_[l], ∀ c : ℤ_[l], cokLen (c • g - 1) ≤ vl l (c • S - 1).det := by
  intro l _ X _ _ R g hgen
  obtain ⟨π, hπ⟩ := hgen
  choose s hs using fun j : Fin R => hπ (g (π (Pi.single j 1)))
  refine ⟨Matrix.of fun i j => s j i, fun c => ?_⟩
  have hcomm : ∀ v : Fin R → ℤ_[l], π (Matrix.mulVec (Matrix.of fun i j => s j i) v) = g (π v) := by
    have h : π ∘ₗ (Matrix.of fun i j => s j i).mulVecLin = g ∘ₗ π := by
      ext j
      simp [Matrix.mulVec_single_one]
      rw [← hs j]
    intro v
    simpa using LinearMap.congr_fun h v
  set A : Matrix (Fin R) (Fin R) ℤ_[l] := c • (Matrix.of fun i j => s j i) - 1 with hA
  have hcommA : ∀ v, π (A.mulVecLin v) = (c • g - 1) (π v) := by
    intro v
    simp only [hA, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, map_sub, map_smul, hcomm, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
  let φ : (Fin R → ℤ_[l]) →ₗ[ℤ_[l]] X ⧸ LinearMap.range (c • g - 1) :=
    (LinearMap.range (c • g - 1)).mkQ ∘ₗ π
  have hker : LinearMap.range A.mulVecLin ≤ LinearMap.ker φ := by
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [hcommA]
    exact LinearMap.mem_range_self _ _
  have hsurj : Function.Surjective ((LinearMap.range A.mulVecLin).liftQ φ hker) := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨v, rfl⟩ := hπ y
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  have hlen := Module.length_le_of_surjective _ hsurj
  have hdet := KStar.Selmer.length_cokernel_eq_addVal_det A
  unfold cokLen
  exact hlen.trans_eq hdet
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.PadicUnitsDistanceLeMax
section
open UpperTheory.V UpperTheory.V.PropA

private theorem padic_units_distance_le_max (l : ℕ) [Fact l.Prime] (a b : ℤ_[l]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (z : PadicAlgCl l) :
    ‖a - b‖ ≤ max ‖algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l]) * z - 1‖
      ‖algebraMap ℚ_[l] (PadicAlgCl l) (b : ℚ_[l]) * z - 1‖ := by
  set A := algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])
  set B := algebraMap ℚ_[l] (PadicAlgCl l) (b : ℚ_[l])
  have hA : ‖A‖ = 1 := by
    simp only [A, PadicAlgCl.norm_extends, ← PadicInt.norm_def, ha]
  have hAB : ‖A - B‖ = ‖a - b‖ := by
    simp only [A, B, ← map_sub, PadicAlgCl.norm_extends, ← PadicInt.coe_sub, ← PadicInt.norm_def]
  have hdiff : A * z - 1 - (B * z - 1) = (A - B) * z := by ring
  have hmax : ‖A * z - 1 - (B * z - 1)‖ ≤ max ‖A * z - 1‖ ‖B * z - 1‖ := by
    have := IsUltrametricDist.norm_add_le_max (A * z - 1) (-(B * z - 1))
    rwa [norm_neg, ← sub_eq_add_neg] at this
  rcases le_or_gt 1 ‖z‖ with hz | hz
  · calc ‖a - b‖ ≤ ‖a - b‖ * ‖z‖ := le_mul_of_one_le_right (norm_nonneg _) hz
      _ = ‖A * z - 1 - (B * z - 1)‖ := by rw [hdiff, norm_mul, hAB]
      _ ≤ _ := hmax
  · have hAz : ‖A * z‖ < 1 := by rw [norm_mul, hA, one_mul]; exact hz
    have h1 : (1 : ℝ) ≤ ‖A * z - 1‖ := by
      have := IsUltrametricDist.norm_add_le_max (A * z) (-(A * z - 1))
      rw [norm_neg, show A * z + -(A * z - 1) = 1 by ring, norm_one] at this
      rcases le_max_iff.mp this with h | h
      · exact absurd h (not_le.mpr hAz)
      · exact h
    calc ‖a - b‖ ≤ 1 := PadicInt.norm_le_one _
      _ ≤ ‖A * z - 1‖ := h1
      _ ≤ _ := le_max_left _ _

theorem UpperTheory.V.PropA.ball :
    ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (c : ℕ), IsLevel l u c → ∀ (j : ℕ) (z : PadicAlgCl l), ∃ s : ℤ_[l], ∀ e : ℕ,
      ((l : ℝ) ^ (j + c))⁻¹ * ‖s - e‖ ≤ ‖algebraMap ℚ_[l] (PadicAlgCl l) (((u ^ l ^ j) ^ e : ℤ_[l]) : ℚ_[l]) * z - 1‖ := by
  intro l _ u c hc j z
  obtain ⟨hu, -, hdist⟩ := lteNorm l u c hc
  have hK : (0 : ℝ) < (l : ℝ) ^ (j + c) := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  set r : ℕ → ℝ := fun e =>
    (l : ℝ) ^ (j + c) * ‖algebraMap ℚ_[l] (PadicAlgCl l) (((u ^ l ^ j) ^ e : ℤ_[l]) : ℚ_[l]) * z - 1‖ with hr
  have hunit : ∀ e : ℕ, ‖((u ^ l ^ j) ^ e : ℤ_[l])‖ = 1 := by
    intro e
    rw [← pow_mul, norm_pow, hu, one_pow]
  obtain ⟨s, hs⟩ := helly l (fun e : ℕ => (e : ℤ_[l])) r (by
    intro a b
    have key := padic_units_distance_le_max l _ _ (hunit a) (hunit b) z
    have h := hdist j a b
    have : ‖(a : ℤ_[l]) - b‖ = (l : ℝ) ^ (j + c) * ‖(u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b‖ := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
    simp only [this, hr]
    rw [← mul_max_of_nonneg _ _ hK.le]
    exact mul_le_mul_of_nonneg_left key hK.le)
  refine ⟨s, fun e => ?_⟩
  have := hs e
  simp only [hr] at this
  rw [inv_mul_le_iff₀ hK]
  exact this
end

