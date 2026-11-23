module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0076

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet



section DimZero

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem chart_finite {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : Module.Finite ℚ (chartRingQ y c) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) (by
    rintro _ ⟨p, rfl⟩
    exact (CoordCurveDegree.isAlgebraic_ratio hP c hc p).isIntegral)

theorem chart_eq_top {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (hb : Birational y)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : chartRingQ y c = ⊤ := by
  have hfin := chart_finite hP c hc
  rw [eq_top_iff]
  intro s _
  obtain ⟨d, g, h, hg, hh, hh0, he⟩ := hb s
  obtain ⟨t₁, ht₁, e₁⟩ := SectionsDimZero.valueSpan_le y c hc d (Submodule.subset_span ⟨g, hg, rfl⟩)
  obtain ⟨t₂, ht₂, e₂⟩ := SectionsDimZero.valueSpan_le y c hc d (Submodule.subset_span ⟨h, hh, rfl⟩)
  rw [LinearMap.mulRight_apply] at e₁ e₂
  have hw : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have ht0 : t₂ ≠ 0 := by
    rintro rfl
    exact hh0 (by rw [← e₂, zero_mul])
  have hs : s = t₁ * t₂⁻¹ := by
    rw [← e₁, ← e₂, ← mul_assoc] at he
    have := mul_right_cancel₀ hw he
    rw [this]; field_simp
  rw [hs]
  refine mul_mem ht₁ ?_
  have halg : IsAlgebraic ℚ (⟨t₂, ht₂⟩ : chartRingQ y c) := IsAlgebraic.of_finite ℚ _
  exact Subalgebra.inv_mem_of_algebraic (A := chartRingQ y c) (x := ⟨t₂, ht₂⟩)
    (halg.algHom (chartRingQ y c).val)

theorem span_eq_top {y : (Σ k, ι k) → Ω} [Module.Finite ℚ Ω] (a : K → ℤ) (τ : ℕ) :
    Submodule.span ℚ (chartLatNm y a τ : Set Ω) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro s _
  have halg : ∀ x : Ω, IsAlgebraic ℤ x := fun x =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (IsAlgebraic.of_finite ℚ x)
  have hex : ∀ c : ∀ k, ι k, ∃ n : ℤ, n ≠ 0 ∧
      IsIntegral ℤ (n • (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) := fun c =>
    (halg _).exists_integral_multiple
  choose n hn0 hn using hex
  have hN : (∏ c, n c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hn0 c
  have hmem : (∏ c, n c) • s ∈ chartLatNm y a τ := by
    intro c _
    have e : ((∏ c, n c) • s) * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) =
        (∏ c' ∈ Finset.univ.erase c, n c') • (n c • (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ c), smul_mul_assoc]
    rw [e]
    exact ((hn c).zsmul _).tower_top
  have h1 : (∏ c, n c) • s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := Submodule.subset_span hmem
  have h2 := Submodule.smul_mem _ (((∏ c, n c : ℤ) : ℚ)⁻¹) h1
  rwa [← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN), one_smul] at h2

theorem nefRR_dimZero (y : (Σ k, ι k) → Ω) (a : K → ℤ) (hP : IsArithVar (mCoordIdeal y) (0 + 1))
    (hb : Birational y) :
    (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω))) ∧
      Tendsto (fun τ : ℕ => ((0 : ℕ).factorial : ℝ) *
        (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ) /
        (τ : ℝ) ^ 0) atTop (𝓝 (genDeg (mCoordIdeal y) 0 a : ℝ)) := by
  classical
  choose c hcX using hP.2.1.2.2
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k (CoordCurveDegree.X_mem_of_eq_zero h0)
  have hfin := chart_finite hP c hc
  rw [chart_eq_top hP hb c hc] at hfin
  have hΩ : Module.Finite ℚ Ω := Module.Finite.equiv (Subalgebra.topEquiv (R := ℚ) (A := Ω)).toLinearEquiv
  refine ⟨fun τ => inferInstance, ?_⟩
  have hQ : chartLatQ y a 0 = ⊤ := by
    rw [eq_top_iff]
    intro s _ c' hc'
    rw [chart_eq_top hP hb c' hc']
    trivial
  have hd := SectionsDimZero.proof K ι Ω y a 0 hP
  rw [hQ] at hd
  have hs : ∀ τ : ℕ, Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) =
      Module.finrank ℚ (⊤ : Submodule ℚ Ω) := fun τ => by rw [span_eq_top]
  simp only [hs, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, div_one, ← hd, Int.cast_natCast]
  exact tendsto_const_nhds

end DimZero

end GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel
