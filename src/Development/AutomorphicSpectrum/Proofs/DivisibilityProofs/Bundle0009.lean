module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0004
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.WeilBound.CoreStatements.IdealCycleValues.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AbelianFrobeniusLift
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem exists_frobenius_all_primes : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E], (∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) → ∀ p : ℕ, p.Prime → ∃ φ : E ≃ₐ[ℚ] E, ∀ (O : Type) [CommRing O] (n : Ideal O), n.IsPrime → (p : O) ∈ n → ∀ (τ : 𝓞 E →+* O) (x : 𝓞 E), τ (RingOfIntegers.mapRingEquiv φ.toRingEquiv x) - τ x ^ p ∈ n :=
  _root_.UpperTheory.Reformulated.B.DYda8.main

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AntisymmetricPerturbationBoundStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antisymmetric_perturbation_bound :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (R : RP Ψ N →ₗ[ℝ] ℝ)
      (v ε : ℝ) (Pl l : MvPolynomial (Ψ × Fin N) ℝ),
      0 < v →
      (∀ lam : Wt Ψ N, eval (fun x => lam x.1 x.2) Pl = R (linRoot lam ^ (dimFl Ψ N + 1))) →
      Pl.IsHomogeneous (dimFl Ψ N + 1) →
      l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j →
      (∀ m, |AddMonoidAlgebra.coeff (Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l) m| ≤ ε) →
      ∃ α β : Ψ → ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 →
        |R (monomial m 1) + v * (∑ τ, (α τ - β τ) * Sh j τ (monomial m 1) +
          ∑ τ, β τ * Tot τ (monomial m 1))| ≤ ε :=
  @GlobalTheory.CompanionTheory.Ar.Top.cor_b_poly_functional
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionConstantMetric
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem intersection_snoc_constWeight : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (c : ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → II K ι P (e + 1) (Fin.snoc L (HermLine.ofWeight (fun _ => c) (fun _ _ _ => rfl))) = -c * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) :=
  RootFieldNumerics.intersection_constant_metric_line

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartRingLocalizationMembership
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

theorem GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, ι k), segreVec y c ≠ 0 → ∀ t : Ω, t ∈ chartRing O (segreVec y) c ↔ ∃ s : A, s ∉ m ∧ algebraMap A Ω s * t ∈ chartRing ℤ (segreVec y) c := by
  intro K _ _ ι _ Ω _ y A _ _ hA m _ O _ _ _ _ _ _ _ c hc t
  have hconst : ∀ a : A, algebraMap A Ω a ∈ chartRing ℤ (segreVec y) c := hA c hc
  have hmul : ∀ {a b : A}, a ∉ m → b ∉ m → a * b ∉ m := fun ha hb h =>
    (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha hb
  constructor
  · intro ht
    induction ht using Algebra.adjoin_induction with
    | mem a ha =>
      refine ⟨1, fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one m).2 h), ?_⟩
      rw [map_one, one_mul]
      exact Algebra.subset_adjoin ha
    | algebraMap o =>
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl o
      refine ⟨s, s.2, ?_⟩
      have h' : algebraMap A Ω (s : A) * algebraMap O Ω o = algebraMap A Ω a := by
        rw [IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω a, ← map_mul,
          mul_comm, h]
      rw [h']
      exact hconst a
    | add a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨r, hr, hb⟩ := hb
      refine ⟨s * r, hmul hs hr, ?_⟩
      have : algebraMap A Ω (s * r) * (a + b) =
          algebraMap A Ω r * (algebraMap A Ω s * a) + algebraMap A Ω s * (algebraMap A Ω r * b) := by
        rw [map_mul]; ring
      rw [this]
      exact add_mem (mul_mem (hconst r) ha) (mul_mem (hconst s) hb)
    | mul a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨r, hr, hb⟩ := hb
      refine ⟨s * r, hmul hs hr, ?_⟩
      have : algebraMap A Ω (s * r) * (a * b) = (algebraMap A Ω s * a) * (algebraMap A Ω r * b) := by
        rw [map_mul]; ring
      rw [this]
      exact mul_mem ha hb
  · rintro ⟨s, hs, ht⟩
    have hle : ∀ {a : Ω}, a ∈ chartRing ℤ (segreVec y) c → a ∈ chartRing O (segreVec y) c := by
      intro a ha
      induction ha using Algebra.adjoin_induction with
      | mem a ha => exact Algebra.subset_adjoin ha
      | algebraMap n =>
        have : algebraMap ℤ Ω n = algebraMap O Ω (n : O) := by simp
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      | add a b _ _ ha hb => exact add_mem ha hb
      | mul a b _ _ ha hb => exact mul_mem ha hb
    obtain ⟨u, hu⟩ := IsLocalization.map_units O (⟨s, hs⟩ : m.primeCompl)
    have hu' : (u : O) = algebraMap A O s := hu
    have hinv : algebraMap O Ω ((u⁻¹ : Oˣ) : O) * algebraMap A Ω s = 1 := by
      rw [IsScalarTower.algebraMap_apply A O Ω, ← hu', ← map_mul, Units.inv_mul, map_one]
    have : t = algebraMap O Ω ((u⁻¹ : Oˣ) : O) * (algebraMap A Ω s * t) := by
      rw [← mul_assoc, hinv, one_mul]
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) (hle ht)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoSeriesThreeStep
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem co_series_three_step : (∀ (Sg : Type) [Fintype Sg] [DecidableEq Sg] (φ : Equiv.Perm Sg) (p k : ℕ), 2 ≤ p → 1 ≤ k → ∀ (La : Sg → ℝ) (τ : Sg), ∑ σ, co φ p k τ σ * La σ = (∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * La ((φ ^ (n + 1)) τ)) - La τ / ((p : ℝ) - 1)) ∧ (∀ (Sg : Type) (φ : Equiv.Perm Sg) (p k : ℕ), 2 ≤ p → ∀ (La : Sg → ℝ) (q : ℕ → Sg → ℝ), (∀ r τ, q r τ = ((p : ℝ) ^ ((r + 1) * k))⁻¹ * La ((φ ^ (r + 1)) τ) + q (r + 1) τ) → (∀ r τ, q (r + 1) τ = ((p : ℝ) ^ k)⁻¹ * q r (φ τ)) → ∀ τ, (p : ℝ) ^ k * q 0 τ = q 0 (φ τ) + La (φ τ)) := by
  refine ⟨?_, ?_⟩
  · intro Sg _ _ φ p k hp hk La τ
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hpk1 : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
    have hpk0 : (0 : ℝ) < (p : ℝ) ^ k := by linarith
    set r : ℝ := ((p : ℝ) ^ k)⁻¹ with hr
    have hr0 : 0 ≤ r := (inv_pos.mpr hpk0).le
    have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hpk1
    have hgeo : Summable (fun n : ℕ => r ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
    have hterm : ∀ σ n, returnTerm φ p k τ σ n = if (φ ^ (n + 1)) τ = σ then r ^ (n + 1) else 0 := by
      intro σ n
      simp only [returnTerm, one_div, hr]
    have hsum : ∀ σ, Summable (returnTerm φ p k τ σ) := by
      intro σ
      refine Summable.of_norm_bounded hgeo ?_
      intro n
      rw [hterm]
      split_ifs
      · rw [Real.norm_of_nonneg (pow_nonneg hr0 _)]
      · simpa using pow_nonneg hr0 (n + 1)
    have hsum' : ∀ σ, Summable (fun n => returnTerm φ p k τ σ n * La σ) :=
      fun σ => (hsum σ).mul_right _
    have hinner : ∀ n : ℕ, ∑ σ, returnTerm φ p k τ σ n * La σ = r ^ (n + 1) * La ((φ ^ (n + 1)) τ) := by
      intro n
      rw [Finset.sum_eq_single ((φ ^ (n + 1)) τ)]
      · rw [hterm, if_pos rfl]
      · intro b _ hb
        rw [hterm, if_neg (Ne.symm hb), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hswap : ∑ σ, (∑' n, returnTerm φ p k τ σ n) * La σ =
        ∑' n : ℕ, r ^ (n + 1) * La ((φ ^ (n + 1)) τ) := by
      simp_rw [← tsum_mul_right]
      rw [← Summable.tsum_finsetSum (fun σ _ => hsum' σ)]
      exact tsum_congr hinner
    have hlast : ∑ σ, (if σ = τ then 1 / ((p : ℝ) - 1) else 0) * La σ = La τ / ((p : ℝ) - 1) := by
      rw [Finset.sum_eq_single τ]
      · rw [if_pos rfl]; ring
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    simp only [co, sub_mul]
    rw [Finset.sum_sub_distrib, hswap, hlast]
  · intro Sg φ p k hp La q h1 h2 τ
    have hp0 : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : p ≠ 0))
    have a := h1 0 τ
    have b := h2 0 τ
    simp only [zero_add, one_mul, pow_one] at a b
    rw [a, b]
    field_simp
    ring

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ConstantsMonomialApproximation
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section ChartForms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem isMultiHomog_chartMonomial (d : ∀ k, ι k) :
    IsMultiHomog (∏ k, X ⟨k, d k⟩ : MRing ι ℤ) (fun _ => 1) := by
  have h := IsWeightedHomogeneous.prod (R := ℤ) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, d k⟩ : MRing ι ℤ)) (fun k => blockWeight ι ⟨k, d k⟩)
    (fun k _ => isWeightedHomogeneous_X ℤ _ _)
  have e : (∑ k, blockWeight ι ⟨k, d k⟩) = fun _ : K => 1 := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h

theorem isMultiHomog_mul_const {f g : MRing ι ℤ} {a b : ℕ}
    (hf : IsMultiHomog f (fun _ => a)) (hg : IsMultiHomog g (fun _ => b)) :
    IsMultiHomog (f * g) (fun _ => a + b) :=
  IsWeightedHomogeneous.mul hf hg

theorem isMultiHomog_pow_const {f : MRing ι ℤ} (hf : IsMultiHomog f (fun _ => 1)) (n : ℕ) :
    IsMultiHomog (f ^ n) (fun _ => n) := by
  induction n with
  | zero => rw [pow_zero]; exact isWeightedHomogeneous_one ℤ (blockWeight ι)
  | succ n ih => rw [pow_succ]; exact isMultiHomog_mul_const ih hf

theorem pointConeMap_chartMonomial (y : (Σ k, ι k) → Ω) (d : ∀ k, ι k) :
    pointConeMap ℤ y (∏ k, X ⟨k, d k⟩ : MRing ι ℤ) =
      C (segreVec y d) * ∏ k : K, (X k : MvPolynomial K Ω) := by
  simp [pointConeMap, segreVec, Finset.prod_mul_distrib, map_prod]

theorem exists_form_of_mem_chart (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hs : segreVec y c ≠ 0)
    {r : Ω} (hr : r ∈ chartRing ℤ (segreVec y) c) :
    ∃ (n : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => n) ∧
      pointConeMap ℤ y G = C (r * segreVec y c ^ n) * (∏ k : K, (X k : MvPolynomial K Ω)) ^ n := by
  set T : MvPolynomial K Ω := ∏ k : K, (X k : MvPolynomial K Ω) with hT
  set s : Ω := segreVec y c with hsdef
  set M : MRing ι ℤ := ∏ k, X ⟨k, c k⟩ with hM
  have hMh : IsMultiHomog M (fun _ => 1) := isMultiHomog_chartMonomial c
  have hMc : pointConeMap ℤ y M = C s * T := pointConeMap_chartMonomial y c
  unfold chartRing at hr
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    refine ⟨1, ∏ k, X ⟨k, d k⟩, isMultiHomog_chartMonomial d, ?_⟩
    rw [pointConeMap_chartMonomial, pow_one, pow_one, div_mul_cancel₀ _ hs]
  | algebraMap z =>
    refine ⟨0, C z, ?_, ?_⟩
    · exact isWeightedHomogeneous_C (blockWeight ι) z
    · have h1 : (C z : MRing ι ℤ) = algebraMap ℤ (MRing ι ℤ) z := rfl
      rw [h1, AlgHom.commutes]
      simp [MvPolynomial.algebraMap_eq]
  | add u v _ _ hu hv =>
    obtain ⟨a, F, hF, hFc⟩ := hu
    obtain ⟨b, G, hG, hGc⟩ := hv
    refine ⟨a + b, F * M ^ b + G * M ^ a, ?_, ?_⟩
    · have h1 := isMultiHomog_mul_const hF (isMultiHomog_pow_const hMh b)
      have h2 := isMultiHomog_mul_const hG (isMultiHomog_pow_const hMh a)
      rw [add_comm b a] at h2
      exact IsWeightedHomogeneous.add h1 h2
    · simp only [map_add (f := _), map_mul, map_pow, hFc, hGc, hMc]
      ring
  | mul u v _ _ hu hv =>
    obtain ⟨a, F, hF, hFc⟩ := hu
    obtain ⟨b, G, hG, hGc⟩ := hv
    refine ⟨a + b, F * G, isMultiHomog_mul_const hF hG, ?_⟩
    simp only [map_mul, map_pow, hFc, hGc]
    ring

theorem pointConeMap_map_int (A : Type) [CommRing A] [Algebra A Ω] (y : (Σ k, ι k) → Ω) (G : MRing ι ℤ) :
    pointConeMap A y (MvPolynomial.map (Int.castRingHom A) G) = pointConeMap ℤ y G := by
  induction G using MvPolynomial.induction_on with
  | C z => simp [pointConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.map_X]; simp [pointConeMap]

end ChartForms

theorem const_mul_chartMonomial_pow_form : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (c : ∀ k, ι k) (a : A), ∃ (n : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - (MvPolynomial.map (Int.castRingHom A) G) ∈ pointIdeal A y := by
  intro K _ _ ι _ Ω _ y A _ _ hA c a
  by_cases hs : segreVec y c = 0
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hs
    refine ⟨1, 0, isWeightedHomogeneous_zero ℤ _ _, ?_⟩
    have hX : (X ⟨k, c k⟩ : MRing ι A) ∈ pointIdeal A y := by
      simp [pointIdeal, RingHom.mem_ker, pointConeMap, hk]
    rw [map_zero, sub_zero, pow_one]
    exact Ideal.mul_mem_left _ _
      (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem (fun k => (X ⟨k, c k⟩ : MRing ι A)) (Finset.mem_univ k)) hX)
  · obtain ⟨n, G, hG, hGc⟩ := exists_form_of_mem_chart y c hs (hA c hs a)
    refine ⟨n, G, hG, ?_⟩
    rw [pointIdeal, RingHom.mem_ker, map_sub, pointConeMap_map_int, hGc, map_mul, map_pow]
    have hM : pointConeMap A y (∏ k, X ⟨k, c k⟩ : MRing ι A) =
        C (segreVec y c) * ∏ k : K, (X k : MvPolynomial K Ω) := by
      simp [pointConeMap, segreVec, Finset.prod_mul_distrib, map_prod]
    have hC : pointConeMap A y (C a : MRing ι A) = C (algebraMap A Ω a) := by
      simp [pointConeMap, MvPolynomial.algebraMap_eq]
    rw [hM, hC, mul_pow, ← C_pow, C_mul]
    ring

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ContinuousWallBoundExtend
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem rat_points_suffice_on_walls : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b :=
  @RootFieldNumerics.continuous_bound_wall_extension

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CurveDegreeLinearNefCone
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem curveDeg_linear_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' a : ℝ), (∀ W, M.curveDeg (lam + mu) (s + s') W = M.curveDeg lam s W + M.curveDeg mu s' W) ∧ (∀ W, M.curveDeg (a • lam) (a * s) W = a * M.curveDeg lam s W) ∧ (∀ p, 0 ≤ s → M.NefAt p lam 0 → M.NefAt p 0 1 → M.NefAt p lam s) ∧ (0 ≤ s → M.NefGen lam 0 → M.NefGen 0 1 → M.NefGen lam s) :=
  @RootFieldNumerics.curveDeg_linear_and_nef

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CutoffCoefficientsBoundStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_coefficients_bound : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C rd Lval : ℝ) (B₀ : ℕ) (A₀ b₀ : ℝ), T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C rd Lval → 128 ≤ B₀ → T.bad.card ≤ B₀ → T.IdentAt II hh frob B₀ A₀ b₀ → |T.j * A₀ + N * b₀| ≤ C * N * bigLam B₀ rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flat_85_bound | exact GlobalTheory.CompanionTheory.Ar.Top.flat_85_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flat_85_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberMulExpand
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycNum_mul : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * cycNum Z cls H (classList cls μ ++ Q) := by
  exact @BaseChangeColon.cycNum_mul_expansion

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivCycleMapLocalisation
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxSynthPendingDepth 1


attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem GlobalTheory.CompanionTheory.Ar.Num.divCycle_map_localisation :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (Mo : Submonoid R) [IsLocalization Mo R'] (P : Ideal (MRing ι R)) (f : MRing ι R) (W' : Ideal (MRing ι R')), W'.IsPrime → divCycle (P.map (MvPolynomial.map (algebraMap R R'))) (MvPolynomial.map (algebraMap R R') f) W' = divCycle P f (W'.comap (MvPolynomial.map (algebraMap R R'))) := by
  intro K _ _ ι _ R R' _ _ _ Mo _ P f W' hW'
  classical
  let φ : MRing ι R →+* MRing ι R' := MvPolynomial.map (algebraMap R R')
  let M : Submonoid (MRing ι R) := Mo.map (C (σ := (Σ k, ι k)) (R := R))
  have : IsLocalization M (MRing ι R') := MvPolynomial.isLocalization Mo R'
  have hφ : algebraMap (MRing ι R) (MRing ι R') = φ := rfl
  set J := P ⊔ Ideal.span {f} with hJdef
  have hJ : P.map φ ⊔ Ideal.span {φ f} = J.map (algebraMap (MRing ι R) (MRing ι R')) := by
    rw [hφ, hJdef, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hdisj : Disjoint (M : Set (MRing ι R)) (W'.comap (algebraMap (MRing ι R) (MRing ι R'))) :=
    (IsLocalization.isPrime_iff_isPrime_disjoint M (MRing ι R') W').mp hW' |>.2
  have hWp : (W'.comap (algebraMap (MRing ι R) (MRing ι R'))).IsPrime := Ideal.comap_isPrime _ _
  have hmap : (W'.comap (algebraMap (MRing ι R) (MRing ι R'))).map
      (algebraMap (MRing ι R) (MRing ι R')) = W' := IsLocalization.map_under M _ W'
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = W'.comap (algebraMap (MRing ι R) (MRing ι R')) := ⟨_, rfl⟩
  rw [← hQ] at hdisj hWp hmap
  subst hmap
  have hmin : Q.map (algebraMap (MRing ι R) (MRing ι R')) ∈ (P.map φ ⊔ Ideal.span {φ f}).minimalPrimes ↔
      Q ∈ J.minimalPrimes := by
    rw [hJ, IsLocalization.minimalPrimes_map M]
    show (Q.map (algebraMap (MRing ι R) (MRing ι R'))).comap
      (algebraMap (MRing ι R) (MRing ι R')) ∈ J.minimalPrimes ↔ _
    rw [← hQ]
  have hrel : IsRelevant (Q.map (algebraMap (MRing ι R) (MRing ι R'))) ↔ IsRelevant Q := by
    refine forall_congr' fun k => exists_congr fun i => not_congr ?_
    have hX : (X ⟨k, i⟩ : MRing ι R') =
        algebraMap (MRing ι R) (MRing ι R') (X ⟨k, i⟩) := (MvPolynomial.map_X _ _).symm
    rw [hX, ← Ideal.mem_comap, ← hQ]
  have hl : ∀ (h₁ : Q.IsPrime) (h₂ : (Q.map (algebraMap (MRing ι R) (MRing ι R'))).IsPrime),
      @multAt _ _ _ _ J Q h₁ =
        @multAt _ _ _ _ (P.map φ ⊔ Ideal.span {φ f})
          (Q.map (algebraMap (MRing ι R) (MRing ι R'))) h₂ := by
    intro h₁ h₂
    unfold multAt
    rw [hJ]
    exact GenericCycleCorresp.length_eq M J Q hdisj
  have hQ' : Ideal.comap (MvPolynomial.map (algebraMap R R') : MRing ι R →+* MRing ι R')
      (Q.map (algebraMap (MRing ι R) (MRing ι R'))) = Q := hQ.symm
  rw [hQ']
  change divCycle (P.map φ) (φ f) _ = divCycle P f Q
  unfold divCycle
  by_cases hc : Q ∈ J.minimalPrimes ∧ IsRelevant Q
  · rw [dite_eq_left ⟨hmin.mpr hc.1, hrel.mpr hc.2⟩, dite_eq_left hc, hl]
  · rw [dite_eq_right (fun h => hc ⟨hmin.mp h.1, hrel.mp h.2⟩), dite_eq_right hc]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeLeGap
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flagDeg_le_mul_gap : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Wt Ψ N) (τ₀ : Ψ), ‖lam‖ ≤ 1 → Dominant lam → flagDeg lam ≤ C * gap j lam τ₀ := by
  exact @RootFieldNumerics.flagDeg_le_gap

end GlobalTheory.CompanionTheory.Ar.Top
end

