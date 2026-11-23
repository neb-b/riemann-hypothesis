module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartA
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0046

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChartConeObjects
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*}

def dehomIdeal (i : (k : K) → ι k) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.span (Set.range fun k => (X ⟨k, i k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ))

abbrev DehomRing (i : (k : K) → ι k) := MvPolynomial (Σ k, ι k) ℂ ⧸ dehomIdeal i

def dehom (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] DehomRing i :=
  Ideal.Quotient.mkₐ ℂ (dehomIdeal i)

def coneUnit (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ :=
  ∏ k, X ⟨k, i k⟩

abbrev ConeRing (i : (k : K) → ι k) := Localization.Away (coneUnit i)

theorem isUnit_coneX (i : (k : K) → ι k) (k : K) :
    IsUnit (algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X ⟨k, i k⟩)) :=
  isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))
    (Finset.mem_univ k))) (IsLocalization.Away.algebraMap_isUnit (coneUnit i))

def coneRatio (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ConeRing i :=
  aeval fun p => (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) *
    algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X p)

theorem coneRatio_X_self (i : (k : K) → ι k) (k : K) : coneRatio i (X ⟨k, i k⟩) = 1 := by
  rw [coneRatio, aeval_X]
  exact (isUnit_coneX i k).val_inv_mul

def ratioMap (i : (k : K) → ι k) : DehomRing i →+* ConeRing i :=
  Ideal.Quotient.lift (dehomIdeal i) (coneRatio i : MvPolynomial (Σ k, ι k) ℂ →+* ConeRing i) (by
    have hle : dehomIdeal i ≤ RingHom.ker (coneRatio i : MvPolynomial (Σ k, ι k) ℂ →+* ConeRing i) := by
      rw [dehomIdeal, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      simp [coneRatio_X_self]
    exact fun a ha => hle ha)

theorem ratioMap_dehom (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    ratioMap i (dehom i f) = coneRatio i f :=
  Ideal.Quotient.lift_mk _ _ _

omit [Fintype K] in
theorem dehom_X_self (i : (k : K) → ι k) (k : K) : dehom i (X ⟨k, i k⟩) = 1 := by
  rw [← sub_eq_zero, ← map_one (dehom i), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)

theorem dehom_coneUnit (i : (k : K) → ι k) : dehom i (coneUnit i) = 1 := by
  rw [coneUnit, map_prod]
  exact Finset.prod_eq_one fun k _ => dehom_X_self i k

omit [Fintype K] in
theorem dehom_surjective (i : (k : K) → ι k) : Function.Surjective (dehom i) :=
  Ideal.Quotient.mk_surjective

def evalOne (i : (k : K) → ι k) : ConeRing i →+* DehomRing i :=
  IsLocalization.Away.lift (coneUnit i) (g := (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i))
    (by rw [AlgHom.coe_toRingHom, dehom_coneUnit]; exact isUnit_one)

theorem evalOne_algebraMap (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    evalOne i (algebraMap _ (ConeRing i) f) = dehom i f :=
  IsLocalization.lift_eq _ _

theorem evalOne_comp_algebraMap (i : (k : K) → ι k) :
    (evalOne i).comp (algebraMap _ (ConeRing i)) = (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i) :=
  RingHom.ext (evalOne_algebraMap i)

theorem evalOne_comp_ratioMap (i : (k : K) → ι k) : (evalOne i).comp (ratioMap i) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, RingHom.id_apply]
    have h1 : ratioMap i (Ideal.Quotient.mk (dehomIdeal i) (C c)) =
        algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (C c) := by
      rw [show Ideal.Quotient.mk (dehomIdeal i) (C c) = dehom i (C c) from rfl, ratioMap_dehom, coneRatio,
        aeval_C, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i),
        MvPolynomial.algebraMap_eq]
    rw [h1, evalOne_algebraMap]
    rfl
  · intro p
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (X p) = dehom i (X p) from rfl, ratioMap_dehom, coneRatio, aeval_X,
      map_mul, evalOne_algebraMap]
    have hu : evalOne i (((isUnit_coneX i p.1).unit : (ConeRing i)ˣ) : ConeRing i) = 1 := by
      rw [IsUnit.unit_spec, evalOne_algebraMap, dehom_X_self]
    have hinv : evalOne i (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) = 1 := by
      have := congrArg (evalOne i) ((isUnit_coneX i p.1).unit.inv_mul)
      rwa [map_mul, hu, mul_one, map_one] at this
    rw [hinv, one_mul]

theorem evalOne_ratioMap (i : (k : K) → ι k) (g : DehomRing i) : evalOne i (ratioMap i g) = g :=
  RingHom.congr_fun (evalOne_comp_ratioMap i) g

variable [DecidableEq K]

def segreDehom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    MvPolynomial (Fin m) ℂ →ₐ[ℂ] DehomRing i :=
  aeval fun a => dehom i (∏ k, X ⟨k, σ a k⟩)

theorem segreDehom_chartSubst {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MvPolynomial (Σ k, ι k) ℂ) : segreDehom σ i (chartSubst σ i f) = dehom i f := by
  have h : (segreDehom σ i).comp (chartSubst σ i) = dehom i := by
    apply MvPolynomial.algHom_ext
    intro p
    rw [AlgHom.comp_apply, chartSubst_X, segreDehom, aeval_X, Equiv.apply_symm_apply, map_prod]
    rw [Finset.prod_eq_single p.1]
    · simp only [Function.update_self]
    · intro k _ hk
      rw [Function.update_of_ne hk, dehom_X_self]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact AlgHom.congr_fun h f

theorem segreDehom_surjective {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Function.Surjective (segreDehom σ i) := fun g => by
  obtain ⟨f, rfl⟩ := dehom_surjective i g
  exact ⟨chartSubst σ i f, segreDehom_chartSubst σ i f⟩

end Objects

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def curveChartMono (c : ∀ k, ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

def chartUnit (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * a k)

def chartIndexLog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : ℝ :=
  Real.log (genIndex (chartLat y a τ) (curveMul y (chartUnit y c a τ)))

def chartRadius (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (t : (Σ k, ι k) → ℂ) : ℝ :=
  A.h t / ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k

end Objects

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


open Classical in
theorem sum_single_chart_apply (k' : K) (j : ι k') (b : ℕ) (k : K) :
    ∑ i, (Finsupp.single (⟨k', j⟩ : Σ k, ι k) b) ⟨k, i⟩ = if k' = k then b else 0 := by
  classical
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro he
    exact h (Sigma.mk.inj_iff.mp he).1

theorem isMultiHomog_curveChartMono (c : ∀ k, ι k) (d : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (curveChartMono c d) d := by
  classical
  have h : curveChartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
    rw [curveChartMono, monomial_sum_one]
    exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
  have hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d := by
    funext k
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_chart_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  have hm := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial (ι := ι)
    (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)
  rw [hd] at hm
  exact hm


omit [∀ k, Fintype (ι k)] in
theorem aeval_curveChartMono (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (curveChartMono c d) = chartUnit y c (fun k => (d k : ℤ)) 1 := by
  simp [curveChartMono, chartUnit, map_prod]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ne_zero_of_X_notMem {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply hp
  show X p ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]


omit [∀ k, Fintype (ι k)] in
theorem curveChartMono_notMem {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    curveChartMono c d ∉ mCoordIdeal y := by
  intro h
  have h' : mConeMap y (curveChartMono c d) = 0 := h
  rw [curveChartMono, map_prod] at h'
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h'
  rw [map_pow, mConeMap, aeval_X] at hk
  exact mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _) (pow_eq_zero_iff'.mp hk).1

theorem exists_chart {y : (Σ k, ι k) → Ω} {n : ℕ} (hP : IsArithVar (mCoordIdeal y) n) :
    ∃ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal y) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hP.2.1.2.2
  exact ⟨c, hc, fun k => ne_zero_of_X_notMem (hc k)⟩

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveRatSectionSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveRationalSectionSum

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logNorm_smul {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    logNorm X s (fun p => c p.1 * z p) = logNorm X s z := by
  unfold logNorm
  rw [eval_smul_homog s a hs c z, X.smul c z hc, norm_mul]
  have hprod : (∏ k, ‖c k‖ ^ X.a k) = ‖∏ k, c k ^ a k‖ := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hXa k, zpow_natCast, norm_pow]
  rw [hprod, mul_div_mul_left _ _
    (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)))]

theorem arInt_eq_sum {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    arInt P s X (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
      ∑ᶠ q : projPts P, logNorm X s (Quot.out q : mcPts P) := by
  have : Nonempty K := hP.1
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) =>
      Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).h z)) = Fin.elim0 :=
    funext fun j => j.elim0
  unfold arInt
  rw [hφ]
  exact PtsIntegralPoints.homogProof K ι P _ hP.2.1.2.1 (HilbertSamuel.CurvePointsFinite.proof K ι P hP)
    fun c z hc _ => logNorm_smul hXa hs c z hc


end CurveRationalSectionSum


end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
  GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem FibreMultiHomog.proof : FibreMultiHomog.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G hv hP
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k n f hf => ?_
  rw [show (DirectSum.decompose (weightedHomogeneousSubmodule G.Φ (cycBlockWt k)) f n : MvPolynomial _ G.Φ) =
    weightedHomogeneousComponent (cycBlockWt k) n f from MvPolynomial.decompose'_apply _ _ f n]
  obtain ⟨b, hb, F, e⟩ := exists_clear G f
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker] at hf ⊢
  have hF : liftZ κ v F ∈ P' := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← e, map_mul, aeval_C]
    simp [hf]
  have hc : weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) ∈ P' := by
    have hH := cyc_isHomogeneous_of_isMultiHomogIdeal hP k.1
    have := hH n hF
    rwa [show (DirectSum.decompose (weightedHomogeneousSubmodule ℤ (cycBlockWt k.1)) (liftZ κ v F) n : MRing ι') =
      weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) from
        MvPolynomial.decompose'_apply _ _ (liftZ κ v F) n] at this
  rw [liftZ_component hv, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← component_map, ← e,
    weightedHomogeneousComponent_C_mul, map_mul, aeval_C] at hc
  exact (mul_eq_zero.1 hc).resolve_left ((map_ne_zero _).2 hb)

end GroundTheory.Heights₂.Heights.Targets
end
end

