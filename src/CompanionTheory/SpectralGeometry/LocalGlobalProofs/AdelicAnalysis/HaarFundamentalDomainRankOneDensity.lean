module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PositiveMajorantGaussian
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalProductGramFiberRankOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGramFiberContinuousDensity
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0027
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaIntegralOverCoordinates
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0051
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0061
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceFormRationalThetaIdentity
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0033

@[expose] public section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem bound_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ β : F, β ≠ 0 → ∃ (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) (C : ℝ), Continuous φ ∧ (∀ X, 0 < φ X) ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β))) < ⊤ ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (φ (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = (I : ℝ≥0∞) ∧ |(I : ℝ) - (∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β)))).toReal * ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf hminf m hm β hβ
  obtain ⟨hF, hEc, hfin, hconj⟩ := id hCM
  have hd : d = 2 := by
    have h := Module.finrank_eq_card_basis b
    simpa [hfin] using h.symm
  obtain ⟨B, hBs, hBd, hBE, hBR⟩ := _root_.GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ d b
  obtain ⟨ρ, e, hρ, he, heρ, hen, hem⟩ := _root_.GlobalTheory.CompanionTheory.SW.real_iso F hF
  have hP : ∀ w, ∃ P : Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ,
      P.PosDef ∧ P * (B.map (ρ w))⁻¹ * P = B.map (ρ w) := by
    intro w
    refine _root_.GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm _ _ ?_ ?_
    · exact hBs.map _
    · have h := RingHom.map_det (ρ w) B
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero _).2 hBd
  choose Pm hPd hPm using hP
  obtain ⟨lf, hlf, hlf1⟩ := _root_.GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI := _root_.GlobalTheory.CompanionTheory.SW.BB.isProbabilityMeasure_prH F E σ hCM M J hJ μ 𝓕 hμ h𝓕
  obtain ⟨hgi, hgf⟩ := _root_.GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable F E σ hCM M J hJ d b e he
  obtain ⟨hii, hif⟩ := GlobalTheory.T.trace_form_invariance_under_unitary F E σ M J d b B ρ e heρ
    (fun h => ((hBR (AF F)).2 h _ (fun p q => rfl)).1)
  have hcard : Fintype.card (Fin M × Fin d) = 2 * M := by simp [hd, mul_comm]
  obtain ⟨C, Df, Dinf, hDf, ⟨hDc, hD0, hDd⟩, hmain⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.Core.core_estimate F hF (Fin M × Fin d) M hcard hM B hBs hBd ρ hρ Pm hPd hPm lf hlf hlf1
      (HA (AF F) σ J) (prH μ 𝓕) (ginf e σ J b) (gfin σ J b) hgi hgf hii hif
      (fun N hN => _root_.GlobalTheory.CompanionTheory.SW.BB.CountHyp.main_bound F E σ hCM M J hJ hM d b ρ e he heρ hen μ 𝓕 hμ h𝓕 N hN)
  obtain ⟨hgc, hgr⟩ := _root_.GlobalTheory.CompanionTheory.SW.BB.gaussQ_continuous_rapidDecay F E σ hCM M d b e he hen Pm
  have h2 : (1 / 2 : F) ≠ 0 := by norm_num
  have hinfint : ∫⁻ X, ENNReal.ofReal (gaussQ e b Pm X)
      ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β))) =
      ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (fun w => ρ w β)) := by
    obtain ⟨i1, i2, i3, i4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    obtain ⟨hK1, hK2, hK3⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b laminf hinf.1
    obtain ⟨t1, t2, t3, t4, t5, t6, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
    have hs := _root_.GlobalTheory.CompanionTheory.SW.BB.ScalTrace.trace_det F E h2 hfin σ (Ainf F) β
    have hDcont : Continuous fun S : HermR (Ainf F) σ 1 =>
        (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) *
          Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))) := by
      refine continuous_const.mul (hDc.comp (he.continuous.comp (continuous_const.mul (t6.comp ?_))))
      exact (continuous_apply_apply 0 0).comp continuous_subtype_val
    have h := _root_.GlobalTheory.CompanionTheory.SW.LocGauss.fibre_rapid_eq_density F E σ hCM M J hJ d b (coordW (Ainf F) b laminf 1 M)
      (coordHerm (Ainf F) σ b laminf 1) minf (hK2 1 M) (hK3 1) hminf (gaussQ e b Pm) hgc
      (fun X => (Real.exp_pos _).le) (hgr hPd) _ hDcont
      (_root_.GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens F E σ hCM M J hJ hM d b B (hBR (Ainf F)).1 ρ e he heρ Pm laminf hinf.1
        (hem laminf hinf) Dinf hDc hD0 hDd) (hermScal (Ainf F) σ (algebraMap F _ β)) (hs.2 hβ)
    rw [h, hs.1]
    have : (e (algebraMap F (Ainf F) β)) = fun w => ρ w β := funext fun w => heρ β w
    rw [this]
  have hκ : 0 ≤ (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (fun w => ρ w β) :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) _) (hD0 _)
  refine ⟨gaussQ e b Pm, C, hgc, fun X => Real.exp_pos _, ?_, ?_⟩
  · rw [hinfint]; exact ENNReal.ofReal_lt_top
  · intro a ha
    obtain ⟨I, hI, hIb⟩ := hmain a ha β hβ
    obtain ⟨c1, c2, c3⟩ := hDf a ha
    have hprod := _root_.GlobalTheory.CompanionTheory.SW.EulerDens.hasProd_fibre_mass F E σ hCM M J hJ d b lam hlam m hm lf hlf hlf1 a ha (Df a) c1 c2
      (fun U hU => by
        rw [_root_.GlobalTheory.CompanionTheory.SW.BB.finDensity_coord F E σ hCM M J hJ d b B (hBR (Af F)).1 lf hlf a U]
        exact c3 U hU) β hβ
    refine ⟨I, ?_, ?_⟩
    · rw [_root_.GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.lintegral_thetaMeas_gauss F E σ hCM M J hJ d b B hBE ρ e he heρ Pm μ 𝓕 hμ h𝓕 a ha β]
      exact hI
    · rw [hinfint, hprod.tprod_eq, ENNReal.toReal_ofReal hκ]
      convert hIb using 3
      ring

end GlobalTheory.CompanionTheory.SW.BB
