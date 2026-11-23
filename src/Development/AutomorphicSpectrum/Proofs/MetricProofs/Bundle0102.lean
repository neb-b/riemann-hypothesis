module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0095
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0048
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BigLineImpliesHeightPositivity
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem selfIntersection_le_volNm_of_moriwakiBig : MoriwakiBigStatement → BirationalPullbackPushforwardFormula := by
  intro h K _ ι _ Ω _ y D A P0 II hD hII hV hB hP hS hF hC
  have hN : NefOnGeneric (mCoordIdeal y) A :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.proof K ι (mCoordIdeal y) P0 A hP hS
  have hb := h K ι Ω y D A P0 II hII hV hB hP hS hC hF hN
  obtain ⟨hfin, C, hC'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Small.packing K ι Ω y D A (chartLatNm y A.a) hV hB hS.1 (fun _ => le_rfl)
  refine hb.trans ?_
  unfold arVolP
  have h0 : ∀ (La : ℕ → AddSubgroup Ω) (τ : ℕ), 0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) La τ := by
    intro La τ
    unfold smallSectionCount
    exact Real.log_natCast_nonneg _
  have hden : ∀ k : ℕ, (0 : ℝ) ≤ ((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := fun k => by positivity
  refine Filter.limsup_le_limsup ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun k => div_le_div_of_nonneg_right
      (GroundTheory.Heights₂.Heights.HilbertSamuel.smallSectionCount_mono_lattice _ _
        (GroundTheory.Heights₂.Heights.HilbertSamuel.chartLat_le_chartLatNm y A.a _) (hfin _)) (hden k)
  · exact Filter.isCoboundedUnder_le_of_le Filter.atTop (fun k => div_nonneg (h0 _ _) (hden k))
  · refine Filter.isBoundedUnder_of_eventually_le (a := max C 0 * 2 ^ (D + 1) * ((D + 1).factorial : ℝ)) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkpos : (0 : ℝ) < ((1 * k : ℕ) : ℝ) := by
      rw [one_mul]
      exact_mod_cast hk
    have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpos : (0 : ℝ) < ((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    have h1 := hC' (1 * k)
    have h2 : ((1 * k : ℕ) : ℝ) + 1 ≤ 2 * ((1 * k : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((1 * k : ℕ) : ℝ) := by
        rw [one_mul]
        exact_mod_cast hk
      linarith
    have h3 : (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) ≤ (2 * ((1 * k : ℕ) : ℝ)) ^ (D + 1) :=
      pow_le_pow_left₀ (by positivity) h2 _
    have h4 : C * (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) ≤ max C 0 * (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hF' := hF.ne'
    calc _ ≤ max C 0 * (2 * ((1 * k : ℕ) : ℝ)) ^ (D + 1) :=
          h1.trans (h4.trans (mul_le_mul_of_nonneg_left h3 (le_max_right _ _)))
      _ = max C 0 * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) *
          (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
        field_simp
        ring

end GlobalTheory.CompanionTheory.Ar.Small
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundaryOnPrimes
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead

theorem aeval_eq_image {σ E : Type} [CommRing E] [Algebra ℚ E] (π : MvPolynomial σ ℂ →+* E)
    (G : MvPolynomial σ ℚ) :
    aeval (fun q => π (X q)) G = π (map (algebraMap ℚ ℂ) G) := by
  have h : (aeval (fun q => π (X q)) : MvPolynomial σ ℚ →ₐ[ℚ] E).toRingHom =
      π.comp (map (algebraMap ℚ ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact DFunLike.congr_fun (RingHom.ext_rat
        ((aeval (fun q => π (X q)) : MvPolynomial σ ℚ →ₐ[ℚ] E).toRingHom.comp C)
        ((π.comp (map (algebraMap ℚ ℂ))).comp C)) r
    · intro i
      simp
  exact DFunLike.congr_fun h G

theorem aeval_int_eq {σ Ω : Type} [CommRing Ω] [Algebra ℚ Ω] (τ : σ → Ω)
    (g : MvPolynomial σ ℤ) : aeval τ g = aeval τ (map (Int.castRingHom ℚ) g) := by
  have h : (aeval τ : MvPolynomial σ ℤ →ₐ[ℤ] Ω).toRingHom =
      (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom.comp (map (Int.castRingHom ℚ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact DFunLike.congr_fun (RingHom.ext_int
        ((aeval τ : MvPolynomial σ ℤ →ₐ[ℤ] Ω).toRingHom.comp C)
        (((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom.comp
          (map (Int.castRingHom ℚ))).comp C)) r
    · intro i
      simp
  exact DFunLike.congr_fun h g

theorem map_map_int {σ : Type} (g : MvPolynomial σ ℤ) :
    map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) g) = map (Int.castRingHom ℂ) g := by
  rw [MvPolynomial.map_map,
    RingHom.ext_int ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ)]

theorem read_in_field {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (τ : σ → Ω)
    (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (Js : Set (MvPolynomial σ ℤ)) (e n : ℕ)
    (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ)
    (hF : aeval τ F ≠ 0) (hS : S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)))
    (hz : ∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i))
    (hprime : ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q))
    (𝔮 : Ideal (MvPolynomial σ ℂ))
    (hker : ∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ 𝔮)
    (hFq : map (algebraMap ℚ ℂ) F ∉ 𝔮)
    (E : Type) [Field E] [Algebra ℚ E] (π : MvPolynomial σ ℂ →+* E)
    (hπ : ∀ p, π p = 0 ↔ p ∈ 𝔮) :
    (∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮 := by
  have hau : ∀ G : MvPolynomial σ ℚ,
      aeval (fun q => π (X q)) G = π (map (algebraMap ℚ ℂ) G) := aeval_eq_image π
  have hunit : IsUnit (aeval (fun q => π (X q)) F) := by
    rw [hau]
    exact IsUnit.mk0 _ (fun h => hFq ((hπ _).1 h))
  obtain ⟨φ, hφ⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.Kext.exists_algHom_adjoin_inv Ω σ τ F S E (fun q => π (X q)) hF hS
    (fun G hG => by rw [hau]; exact (hπ _).2 (hker G hG)) hunit
  have hτS : ∀ q, τ q ∈ S := fun q => by
    rw [hS]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨q, rfl⟩)
  let τS : σ → S := fun q => ⟨τ q, hτS q⟩
  have hcoe : ∀ G : MvPolynomial σ ℚ, ((aeval τS G : S) : Ω) = aeval τ G := by
    intro G
    have h : S.val.comp (aeval τS) = aeval τ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [τS]
    exact DFunLike.congr_fun h G
  have hq : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmem : ∀ s, s ∈ RingHom.ker φ ↔ φ s = 0 := fun s => RingHom.mem_ker
  have hleft : (∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔
      (∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ RingHom.ker φ) := by
    constructor
    · intro h g hg s hs
      rw [hmem, hφ (map (Int.castRingHom ℚ) g) s (by rw [hs, aeval_int_eq]), hau, map_map_int]
      exact (hπ _).2 (h g hg)
    · intro h g hg
      have hs := hcoe (map (Int.castRingHom ℚ) g)
      have h0 := h g hg (aeval τS (map (Int.castRingHom ℚ) g)) (by rw [hs, aeval_int_eq])
      rw [hmem, hφ _ _ hs, hau, map_map_int] at h0
      exact (hπ _).1 h0
  have hright : ∀ i, z i ∈ RingHom.ker φ ↔ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮 := by
    intro i
    have hzi : φ (z i * (aeval τS F) ^ N i) = aeval (fun q => π (X q)) (Z i) :=
      hφ _ _ (by push_cast; rw [hcoe, hz])
    have hfS : φ (aeval τS F) = aeval (fun q => π (X q)) F := hφ _ _ (hcoe F)
    rw [map_mul, map_pow, hfS] at hzi
    have hf0 : aeval (fun q => π (X q)) F ≠ 0 := hunit.ne_zero
    rw [hmem, ← hπ, ← hau, ← hzi]
    simp [hf0]
  rw [hleft, hprime _ hq]
  exact exists_congr fun i => and_congr_right fun _ => hright i

theorem boundary_on_primes : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (Js : Set (MvPolynomial σ ℤ)) (e n : ℕ) (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ), aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) → (∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i)) → (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) → ∀ 𝔮 : Ideal (MvPolynomial σ ℂ), 𝔮.IsPrime → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ 𝔮) → map (algebraMap ℚ ℂ) F ∉ 𝔮 → ((∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮) := by
  intro Ω _ _ σ τ F S Js e n z Z N hF hS hz hprime 𝔮 h𝔮 hker hFq
  have : IsDomain (MvPolynomial σ ℂ ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let π : MvPolynomial σ ℂ →+* FractionRing (MvPolynomial σ ℂ ⧸ 𝔮) :=
    (algebraMap (MvPolynomial σ ℂ ⧸ 𝔮) (FractionRing (MvPolynomial σ ℂ ⧸ 𝔮))).comp
      (Ideal.Quotient.mk 𝔮)
  have hπ : ∀ p, π p = 0 ↔ p ∈ 𝔮 := by
    intro p
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let _ : Algebra ℚ (FractionRing (MvPolynomial σ ℂ ⧸ 𝔮)) :=
    (π.comp ((C : ℂ →+* MvPolynomial σ ℂ).comp (algebraMap ℚ ℂ))).toAlgebra
  exact read_in_field τ F S Js e n z Z N hF hS hz hprime 𝔮 hker hFq _ π hπ

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsConjInvariantMollifier
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_conj_invariant_mollifier : ∀ n : ℕ, ∃ ρ : ReciprocityTheory.AnForm.A.Mollifier n, ∀ v, ρ.toFun (star v) = ρ.toFun v := by
  intro n
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm n
  have hmp : MeasureTheory.MeasurePreserving (fun v : Fin n → ℂ => star v) :=
    MeasureTheory.volume_preserving_pi (fun _ => Complex.conjLIE.measurePreserving)
  have hme : MeasurableEmbedding (fun v : Fin n → ℂ => star v) :=
    (starLinearEquiv ℝ (A := Fin n → ℂ)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v : Fin n → ℂ => star v) :=
    contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) i)
  have hI : MeasureTheory.Integrable ρ.toFun :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [ρ.integral_eq_one]; norm_num)
  have hcomp : ∫ w : Fin n → ℂ, ρ.toFun (star w) = 1 := by
    rw [hmp.integral_comp hme ρ.toFun, ρ.integral_eq_one]
  have hI2 : MeasureTheory.Integrable (fun w : Fin n → ℂ => ρ.toFun (star w)) :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [hcomp]; norm_num)
  refine ⟨⟨fun v => (ρ.toFun v + ρ.toFun (star v)) / 2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (ρ.contDiff.add (ρ.contDiff.comp hsm)).div_const 2
  · intro w
    exact div_nonneg (add_nonneg (ρ.nonneg _) (ρ.nonneg _)) two_pos.le
  · intro w hw
    by_contra h
    have h1 : ρ.toFun w = 0 := by
      by_contra h'
      exact h (ρ.support_subset h')
    have h2 : ρ.toFun (star w) = 0 := by
      by_contra h'
      have hb := ρ.support_subset h'
      rw [Metric.mem_ball, dist_zero_right, norm_star] at hb
      exact h (by rw [Metric.mem_ball, dist_zero_right]; exact hb)
    exact hw (by simp [h1, h2])
  · show ∫ w : Fin n → ℂ, (ρ.toFun w + ρ.toFun (star w)) / 2 = 1
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hI hI2, ρ.integral_eq_one, hcomp]
    norm_num
  · intro c w hc
    show (ρ.toFun (c • w) + ρ.toFun (star (c • w))) / 2 = (ρ.toFun w + ρ.toFun (star w)) / 2
    rw [star_smul, ρ.circle_inv c w hc, ρ.circle_inv (star c) (star w) (by rw [norm_star]; exact hc)]
  · intro v
    show (ρ.toFun (star v) + ρ.toFun (star (star v))) / 2 = (ρ.toFun v + ρ.toFun (star v)) / 2
    rw [star_star, add_comm]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteFibresOfAnalyticLocalDiffeo
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

open LintegralFibSum

theorem lintegral_absFibre_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite)
    (hsm : ∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x))
    (hGm : ∀ j, AEStronglyMeasurable (fun u => G ((A.chart j).symm u) * locDens A Φ j u)
      (volume.restrict (A.chart j).target))
    (Pt : ChartPartition A) :
    ∫⁻ y, ENNReal.ofReal (∑ᶠ x ∈ q ⁻¹' {y} \ S, |G x * pushDens A Φ q x|) =
      ∑ j, ∫⁻ u in (A.chart j).target, ENNReal.ofReal
        |Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u| := by
  classical
  set Qj : Fin A.n → (Fin e → ℂ) → (Fin e → ℂ) := fun j => q ∘ (A.chart j).symm with hQj
  set h : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    |Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u| with hh
  have hms : ∀ j, MeasurableSet (A.chart j).target := fun j => (A.chart j).open_target.measurableSet
  have hdiff : ∀ j (s : Set (Fin e → ℂ)), s ⊆ goodT A q j → volume s = 0 →
      volume (Qj j '' s) = 0 := by
    intro j s hs h0
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ h0
    intro u hu
    exact ((hs hu).2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  have hN : ∀ j, volume (Qj j '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := fun j =>
    hdiff j _ Set.inter_subset_left
      (measure_mono_null (Set.inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1) (hS j))
  have hTn : ∀ j, volume ((A.chart j).target \ goodT A q j) = 0 := fun j =>
    measure_mono_null (target_diff_goodT_subset A q S hq j) (hS j)
  have hgt : ∀ j, goodT A q j =ᵐ[volume] (A.chart j).target := by
    intro j
    refine ae_eq_set.mpr ⟨?_, hTn j⟩
    have : goodT A q j \ (A.chart j).target = ∅ := Set.diff_eq_empty.mpr fun u hu => hu.1
    rw [this]
    exact measure_empty
  have hAE : ∀ j, AEMeasurable (h j) (volume.restrict (A.chart j).target) := by
    intro j
    have hχ : ContinuousOn (fun u => Pt.χ j ((A.chart j).symm u)) (A.chart j).target := by
      have := (Pt.smooth j j).continuousOn
      rw [Set.preimage_univ, Set.inter_univ] at this
      exact this
    have h1 := hχ.aestronglyMeasurable (μ := volume) (hms j)
    have h2 := (h1.mul (hGm j)).norm
    refine h2.aemeasurable.congr (ae_of_all _ fun u => ?_)
    simp only [hh, Real.norm_eq_abs, Pi.mul_apply, mul_assoc]
  set h' : Fin A.n → (Fin e → ℂ) → ℝ := fun j u => |(hAE j).mk (h j) u| with hh'
  have hm' : ∀ j, Measurable (h' j) := fun j =>
    continuous_abs.measurable.comp (hAE j).measurable_mk
  have heq : ∀ j, ∀ᵐ u, u ∈ (A.chart j).target → h j u = h' j u := by
    intro j
    filter_upwards [(ae_restrict_iff' (hms j)).mp (hAE j).ae_eq_mk] with u hu ht
    have h0 : 0 ≤ h j u := abs_nonneg _
    show h j u = |(hAE j).mk (h j) u|
    rw [← hu ht, abs_of_nonneg h0]
  have hD : ∀ j, volume (Qj j '' (goodT A q j ∩ {u | h j u ≠ h' j u})) = 0 := fun j =>
    hdiff j _ Set.inter_subset_left
      (measure_mono_null (t := {u | ¬ (u ∈ (A.chart j).target → h j u = h' j u)})
        (fun u hu hc => hu.2 (hc hu.1.1)) (ae_iff.mp (heq j)))
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ Qj j ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [show goodT A q j ∩ Qj j ⁻¹' {y} = _ from goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset Set.inter_subset_right).image _
  have hlow : ∀ j, AEMeasurable (fun y => ENNReal.ofReal (fibSum (goodT A q j) (Qj j) (h' j) y)) ∧
      ∫⁻ y, ENNReal.ofReal (fibSum (goodT A q j) (Qj j) (h' j) y) =
        ∫⁻ u in goodT A q j, ENNReal.ofReal (h' j u) := fun j =>
    lintegral_fibSum_open (isOpen_goodT A q j) (fun u hu => hu.2) (fun u => abs_nonneg _)
      ((hm' j).comp measurable_subtype_coe) (hfinj j)
  have hsame : ∀ᵐ y, ∀ j, fibSum (goodT A q j) (Qj j) (h j) y =
      fibSum (goodT A q j) (Qj j) (h' j) y := by
    refine ae_all_iff.mpr fun j => ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hD j)] with y hy
    unfold fibSum
    refine finsum_mem_congr rfl fun u hu => ?_
    have : h j u = h' j u := by
      by_contra hne
      exact hy ⟨u, ⟨hu.1, hne⟩, hu.2⟩
    rw [this]
  have hterm : ∀ j x, x ∈ (A.chart j).source → x ∉ S →
      h j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
        Pt.χ j x * |G x * pushDens A Φ q x| := by
    intro j x hx hxS
    have hJ : 0 ≤ jacN (q ∘ (A.chart j).symm) (A.chart j x) := by unfold jacN; positivity
    have hd := locDens_div_jacN A Φ q S hq hsm j hx hxS
    calc h j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x)
        = |Pt.χ j x * G x * (locDens A Φ j (A.chart j x) /
            jacN (q ∘ (A.chart j).symm) (A.chart j x))| := by
          simp only [hh, (A.chart j).left_inv hx]
          rw [← mul_div_assoc, abs_div, abs_of_nonneg hJ]
      _ = Pt.χ j x * |G x * pushDens A Φ q x| := by
          rw [hd, mul_assoc, abs_mul, abs_of_nonneg (Pt.nonneg j x)]
  have hae := sum_fibSum_ae A q S hN hq hfin Pt h (fun x => |G x * pushDens A Φ q x|) hterm
  calc ∫⁻ y, ENNReal.ofReal (∑ᶠ x ∈ q ⁻¹' {y} \ S, |G x * pushDens A Φ q x|)
      = ∫⁻ y, ∑ j, ENNReal.ofReal (fibSum (goodT A q j) (Qj j) (h' j) y) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae, hsame] with y hy hs
        rw [← hy, ENNReal.ofReal_sum_of_nonneg fun j _ =>
          fibSum_nonneg _ _ (fun u => abs_nonneg _) y]
        exact Finset.sum_congr rfl fun j _ => by rw [hs j]
    _ = ∑ j, ∫⁻ u in goodT A q j, ENNReal.ofReal (h' j u) := by
        rw [lintegral_finsetSum' _ fun j _ => (hlow j).1]
        exact Finset.sum_congr rfl fun j _ => (hlow j).2
    _ = ∑ j, ∫⁻ u in (A.chart j).target, ENNReal.ofReal (h j u) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [setLIntegral_congr (hgt j)]
        refine lintegral_congr_ae ?_
        filter_upwards [(ae_restrict_iff' (hms j)).mpr (heq j)] with u hu
        rw [hu]

end GlobalTheory.CompanionTheory.Ar.Giv.Push
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolution
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isBlockDiag_one_add_single {N j : ℕ} {ca cb : Fin N} (hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s hrs
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
  have h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hrs hs.symm
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem not_sameOrbit_of_ptData : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t → ¬ SameOrbit (fstPt k₀ (RW.lift x x)) (sndPt k₀ (RW.lift x x)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hW x z₀ z₁ F h t hP hOrb
  obtain ⟨hF, hG, h0, h1, hbd, hdet, ht, hE0, hE1⟩ := hP
  obtain ⟨hb0, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase.main K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW x z₀ z₁ h0 h1
  obtain ⟨c, hc, hcz⟩ : SameOrbit z₁ z₀ := orbit_trans (orbit_trans h1 (orbit_symm hOrb)) (orbit_symm h0)
  have hz : ∀ q, z₁ q = c q.1 * z₀ q := fun q => congrFun hcz q

  have hbase : basePart M.blk z₁ = basePart M.blk z₀ := by
    funext q
    have e₀ : z₀ ⟨q.1.1, F.c q.1⟩ = 1 := (hE0 a).1 q.1
    have e₁ : z₁ ⟨q.1.1, F.c q.1⟩ = 1 := (hE1 a).1 q.1
    have hc1 : c q.1.1 = 1 := by
      have := hz ⟨q.1.1, F.c q.1⟩
      rw [e₀, e₁, mul_one] at this
      exact this.symm
    show z₁ ⟨q.1.1, q.2⟩ = z₀ ⟨q.1.1, q.2⟩
    rw [hz, show c (Sigma.fst (⟨q.1.1, q.2⟩ : Σ k, ι k)) = 1 from hc1, one_mul]
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    have hN := M.j_le
    have ha := a.2
    have hb' := b.2
    unfold lastCol at hca
    split_ifs at hca with hl <;> omega
  have hbd₁ : IsBlockDiag j (h * (1 + Matrix.single cb ca t)) := hbd.mul (isBlockDiag_one_add_single hs t)
  have hplk : ∀ m : ι k₀, plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ (h * (1 + Matrix.single cb ca t)) =
      c k₀ * plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ h := fun m => by
    have e₀ := (hE0 a).2 k₀ hk m
    have e₁ := (hE1 a).2 k₀ hk m
    rw [hbase] at e₁
    have e₂ := hz ⟨k₀, m⟩
    rw [e₁, e₀] at e₂
    exact e₂
  have hmin := Ind.minor_eq_of_plk M hb0 hF hG hk hbd₁ hbd hplk
  have hpl := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane.param_relation N j a b ca cb M.j_le hb hab hca hcb h 1 0 t (c k₀) hdet isBlockDiag_one
    Matrix.blockTriangular_one (fun I => by
      have e : (1 + Matrix.single cb ca (0 : ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by simp
      rw [e, Matrix.mul_one]
      exact hmin I)
  have h2 := hpl.2
  simp only [mul_zero, Matrix.one_apply_eq, mul_one, Finset.prod_const_one, one_mul] at h2
  exact ht h2.symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem genDeg_of_system (h : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement) :
    GenDegStatement :=
  _root_.PositivityTheory.HtPt.Aig.genDeg (_root_.PositivityTheory.HtPt.Aig.pfCoord h) fibreDim

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameHeightFormulaStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_height_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ (h : ModelOK (aOf 𝔐 bW bO φ) x₀ m) (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → Submodule.span (GenField Ω (rk (CMType H) D.p D.q)) (Set.range j) = ⊤ → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∃ xdeg : CMType H × Fin (D.p + D.q) → (K₀ ⊕ StepIx (CMType H) D.p D.q) → ℤ, Fl.RootLines xdeg (fun _ => 1) ∧ ∀ τ i, (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i) = -∑ k ∈ Finset.Iic i, xdeg (τ, k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots.rootLines | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots.rootLines | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots.rootLines <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionTransitionPolynomialStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_resolution_transition_polynomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → (∀ p : (k : K) → ι k, SncRes.coord P p '' SncRes.src P p = {t | ∀ h ∈ SncRes.ideal P p, eval t h = 0}) ∧ ∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), eval (SncRes.coord P p x) q ≠ 0 ∧ ∀ y ∈ SncRes.src P p ∩ SncRes.src P p', eval (SncRes.coord P p y) q ≠ 0 → ∀ l, SncRes.coord P p' y l * eval (SncRes.coord P p y) q = eval (SncRes.coord P p y) (F l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans <;> assumption)
end

