module

public import CompanionTheory.AutomorphicTheory.ThetaDilations.Bundle0001
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ReductionToSiegelDomain
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionAutomorphy
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0061
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionGrowthBound
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCount
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0050
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummable
public import CompanionTheory.AutomorphicTheory.ThetaDilations.ThetaLint
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSets
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.ThetaDilations.Bounded
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

set_option maxHeartbeats 400000 in
theorem bounded : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → wt M τ * ‖((∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - eis ψ lf B ρ P φ τ)‖ ≤ C := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM Ω _ Pr gf gi hC φ hφ
  have H := _root_.GlobalTheory.CompanionTheory.SW.Core.SelfDual.naQuad F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1
  have hO := hC.2.2.2.1
  obtain ⟨𝒟, h𝒟⟩ : ∃ 𝒟 : ((ι → A F) → ℂ) → (InfinitePlace F → ℂ) → ℂ, ∀ φ τ,
    𝒟 φ τ = (∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - eis ψ lf B ρ P φ τ := ⟨_, fun _ _ => rfl⟩
  have hUD := fun ω => _root_.GlobalTheory.CompanionTheory.SW.ThetaUD.main F ψ hψ ι M B ρ P hQ _ _ (hO ω)
  have hei := _root_.GlobalTheory.CompanionTheory.SW.Core.EiInv.ei_inv F lf hlf h1 ψ hψ ι M B ρ P hQ hM
  have heb := _root_.GlobalTheory.CompanionTheory.SW.Core.EiBound.ei_bound F lf hlf h1 ψ hψ ι M B ρ P hQ hM
  have hti := _root_.GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral.main F lf hlf h1 ψ hψ ι M B ρ P hQ Ω Pr gf gi hC
  have hsm : ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → ∀ c : ℂ, 𝒟 (c • φ) τ = c * 𝒟 φ τ := fun φ τ hφ hτ c => by
    simp only [h𝒟, fun ω => (hUD ω φ τ).2.2 c, (hei φ hφ τ hτ).2.2.2 c, integral_const_mul, mul_sub]
  have good := good_ex hlf h1 hψ hQ (𝒟 := 𝒟) fun φ τ hφ hτ =>
    ⟨fun b => by simp only [h𝒟, fun ω => (hUD ω φ τ).1 b, (hei φ hφ τ hτ).1 b],
      fun a ha => by simp only [h𝒟, fun ω => (hUD ω φ τ).2.1 a ha, (hei φ hφ τ hτ).2.1 a ha],
      by simp only [h𝒟, mul_sub, ← integral_const_mul, (hei φ hφ τ hτ).2.2.1,
        fun ω => _root_.GlobalTheory.CompanionTheory.SW.ThW.thetaInvariance F lf hlf h1 ψ hψ ι M B ρ P hQ _ _ (hO ω) φ hφ τ hτ], hsm φ τ hφ hτ⟩
  have hadd : ∀ τ, (∀ w, 0 < (τ w).im) → ∀ φ φ', SB φ → SB φ' → 𝒟 (φ + φ') τ = 𝒟 φ τ + 𝒟 φ' τ := by
    intro τ hτ φ φ' hφ hφ'
    obtain ⟨w₀, hw₀⟩ := Finite.exists_min fun w => (τ w).im
    have e1 : ∀ ω, theta B ρ P (gf ω) (gi ω) (φ + φ') τ =
        theta B ρ P (gf ω) (gi ω) φ τ + theta B ρ P (gf ω) (gi ω) φ' τ := fun ω => by
      have hs := (_root_.GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero F ι M B ρ P hQ _ _ (hO ω) τ hτ).1
      rw [theta, theta, theta, ← (hs φ hφ).of_norm.tsum_add (hs φ' hφ').of_norm]
      simp only [thTerm, Pi.add_apply, add_mul]
    have e2 : ∀ b, eiTerm ψ lf B ρ P (φ + φ') τ b = eiTerm ψ lf B ρ P φ τ b + eiTerm ψ lf B ρ P φ' τ b := fun b => by
      rw [eiTerm, eiTerm, eiTerm, ← add_mul, fstar, fstar, fstar,
        ← integral_add (sb_int H.2.2.2.2.2 (sb_opU H _ hφ)) (sb_int H.2.2.2.2.2 (sb_opU H _ hφ'))]
      simp only [opU, Pi.add_apply, mul_add]
    obtain ⟨_, s1⟩ := heb φ hφ _ (hτ w₀)
    obtain ⟨_, s2⟩ := heb φ' hφ' _ (hτ w₀)
    simp only [h𝒟, e1, eis, e2, Pi.add_apply, integral_add (hti φ τ hφ hτ).1 (hti φ' τ hφ' hτ).1,
      (s1 τ hw₀).1.of_norm.tsum_add (s2 τ hw₀).1.of_norm]
    ring
  obtain ⟨S, κ, t, hκ, ht, hred⟩ := _root_.GlobalTheory.CompanionTheory.SW.Red.reduction F hQ.1 ρ hQ.2.2.2.2.1
  have hwt : ∀ τ : InfinitePlace F → ℂ, 0 ≤ wt M τ := fun τ => Finset.prod_nonneg fun _ _ => by positivity
  have hS : ∀ φ, SB φ → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) →
      (∀ v w, κ * (τ w).im ≤ (τ v).im) → wt M τ * ‖𝒟 φ τ‖ ≤ C := fun φ hφ => by
    obtain ⟨C₁, b1⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound F ι M B ρ P hQ Ω Pr gf gi hC φ hφ κ t hκ ht
    obtain ⟨C₂, b2⟩ := heb φ hφ t ht
    refine ⟨|C₁| + |C₂|, by positivity, fun τ h2 h3 => ?_⟩
    have hτ : ∀ w, 0 < (τ w).im := fun w => ht.trans_le (h2 w)
    have h4 := (mul_le_mul_right (hti φ τ hφ hτ).2 _).trans (b1 τ h2 h3).2
    rw [← ENNReal.ofReal_mul (hwt τ)] at h4
    have h5 := (ENNReal.ofReal_le_ofReal_iff (abs_nonneg C₁)).1 (h4.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))
    have h6 : ‖𝒟 φ τ‖ ≤ ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ + ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ := by
      simp only [h𝒟, eis, ← sub_sub]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_tsum_le_tsum_norm (b2 τ h2).1))
    refine (mul_le_mul_of_nonneg_left h6 (hwt τ)).trans ?_
    rw [mul_add]
    exact add_le_add h5 ((b2 τ h2).2.trans (le_abs_self _))
  choose T hT1 hT2 using good
  obtain ⟨L, s, C₀, hL, horb⟩ := orbit_adelic H hφ
  have := H.2.2.2.2.2.1
  have := H.2.2.2.2.2.2.1
  choose C hC0 hCb using fun (r : SL(2, F)) (a : ι → A F) => hS _ ((hT1 r).1 _ (sb_ind a hL))
  refine ⟨∑ r ∈ S, ∑ a ∈ s, |C₀| * C r a, fun τ hτ => ?_⟩
  rw [← h𝒟]
  obtain ⟨r, hr, k, hk, h2, h3⟩ := hred τ hτ
  have hmob := _root_.GlobalTheory.CompanionTheory.SW.Core.Mobius.main F ρ τ hτ
  obtain ⟨-, c, hc, e⟩ := horb (Matrix.SpecialLinearGroup.map (algebraMap F (A F)) k) (fun i j => ((_root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F).2.2.2.2.2.2.1 (k i j)).2 (hk i j)) _ (hT1 k)
  have hτ' : ∀ w, 0 < (mob ρ (r * k) τ w).im := fun w => (hmob.1 _ w).2
  rw [← hT2 k φ τ hφ hτ, ← hT2 r _ _ ((hT1 k).1 φ hφ) fun w => (hmob.1 k w).2, ← hmob.2.1, e,
    map_sum_sb (hT1 r).2.2.1 (hT1 r).2.2.2.1 s c fun a => sb_ind a hL]
  have e2 := congrFun (map_sum_sb (T := fun φ _ => 𝒟 φ (mob ρ (r * k) τ))
    (fun φ φ' h h' => funext fun _ => hadd _ hτ' φ φ' h h') (fun c φ h => funext fun _ => hsm φ _ h hτ' c) s c
    fun a => (hT1 r).1 _ (sb_ind a hL)) 0
  rw [e2, Finset.sum_apply]
  refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ a ∈ s, |C₀| * C r a)
    (fun r _ => Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (hC0 r a)) hr)
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hwt _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Pi.smul_apply, norm_smul, mul_left_comm]
  exact mul_le_mul ((hc a).trans (le_abs_self _)) (hCb r a _ h2 h3) (mul_nonneg (hwt _) (norm_nonneg _)) (abs_nonneg _)

end CompanionTheory.PlacePermOperatorBicommutantSpan
end
end

-- bundled from CompanionTheory.AutomorphicTheory.ThetaDilations.ThetaFin
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

theorem theta_measure_locally_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM μ 𝓕 hμ h𝓕 T hT hd
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 M
  refine ⟨fun X => ?_⟩
  obtain ⟨K, hK, hX⟩ := exists_compact_mem_nhds X
  obtain ⟨N, r, hN, hr, hsub⟩ := (_root_.GlobalTheory.CompanionTheory.SW.Cpt.compact_tuples F E σ hcm _ (Module.finBasis F E) 1 M).2 K hK
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeanCount.mean_count_box F E σ hcm M J hJ hM _ (Module.finBasis F E) μ 𝓕 hμ h𝓕 N hN
  have hsub' : K ⊆ {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV (Module.finBasis F E) v) ∧ sizeTup (Module.finBasis F E) (projInf X) ≤ r} := hsub
  refine ⟨K, hX, lt_of_le_of_lt (le_trans ?_ ((measure_mono hsub').trans (hC r hr))) ENNReal.ofReal_lt_top⟩
  have hm : Measurable (K.indicator (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
  rw [← lintegral_indicator_one hK.measurableSet, ← lintegral_indicator_one hK.measurableSet,
    theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 _ _ _ hm, theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 _ _ _ hm]
  suffices hs : {X : Fin 1 → Fin M → E | gramE σ J X = T} ⊆ {X | X ≠ 0} from
    mul_le_mul_right (lintegral_mono fun h => ENNReal.tsum_mono_subtype (fun X => K.indicator
      (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (actW (AF F) σ J h⁻¹ (ratTup (AF F) X))) hs) _
  refine fun X hX h0 => hd ?_
  rw [← show gramE σ J X = T from hX, h0, Matrix.det_unique]
  simp [gramE, hE, hform]

end CompanionTheory.PlacePermOperatorBicommutantSpan
end
end

