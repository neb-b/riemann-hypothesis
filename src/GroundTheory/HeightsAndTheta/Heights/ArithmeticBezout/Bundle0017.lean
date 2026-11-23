module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0014

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set MvPolynomial

noncomputable section

namespace LogInt

variable {n k : ℕ}

def ballSet (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j => u (i, j)) < 1}

theorem measurableSet_ballSet (h : HermNorm n) : MeasurableSet (ballSet h k) := by
  have e : ballSet h k = ⋂ i, {u : Fin k × Fin n → ℂ | h.norm (fun j => u (i, j)) < 1} := by
    ext u; simp [ballSet]
  rw [e]
  exact MeasurableSet.iInter fun i => measurableSet_lt (measurable_groupNorm h i) measurable_const

theorem ballSet_subset_polydisc (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballSet h k ⊆ polydisc _ C := by
  intro u hu
  simp only [polydisc, mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

theorem normT_univ (h : HermNorm n) (u : Fin k × Fin n → ℂ) :
    normT h Finset.univ u = fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij := by
  funext ij
  simp [normT]

theorem integrableOn_log_mahler (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ) (hf : f ≠ 0) :
    IntegrableOn (fun u : Fin k × Fin n → ℂ =>
        Real.log ‖eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f‖)
        (ballSet h k) ∧
      ∀ᵐ u ∂(volume.restrict (ballSet h k)),
        eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f ≠ 0 := by
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  obtain ⟨h1, h2⟩ := logNormT h C hC0 hC Finset.univ f hf
  simp only [normT_univ] at h1 h2
  exact ⟨h1.mono_set (ballSet_subset_polydisc h C hC0 hC),
    ae_restrict_of_ae_restrict_of_subset (ballSet_subset_polydisc h C hC0 hC) h2⟩

end LogInt

theorem mahlerMul : MahlerMul.Statement := by
  intro n k h f g hf hg
  obtain ⟨i1, z1⟩ := LogInt.integrableOn_log_mahler h f hf
  obtain ⟨i2, z2⟩ := LogInt.integrableOn_log_mahler h g hg
  unfold mahler sphereMean
  change ⨍ u in LogInt.ballSet h k, _ = (⨍ u in LogInt.ballSet h k, _) + ⨍ u in LogInt.ballSet h k, _
  rw [setAverage_eq, setAverage_eq, setAverage_eq, ← smul_add, ← integral_add i1 i2]
  congr 1
  refine setIntegral_congr_ae (LogInt.measurableSet_ballSet h) ?_
  have := (ae_restrict_iff' (LogInt.measurableSet_ballSet h)).mp (z1.and z2)
  filter_upwards [this] with u hu hB
  obtain ⟨h1, h2⟩ := hu hB
  rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

namespace AdmissibleAE

variable {n : ℕ}

def formsIn (W : Ideal (MvPolynomial (Fin n) ℂ)) : Submodule ℝ (Fin n → ℂ) where
  carrier := {u | linForm u ∈ W}
  zero_mem' := by simp [linForm]
  add_mem' := by
    intro a b ha hb
    have : linForm (a + b) = linForm a + linForm b := by
      simp [linForm, Finset.sum_add_distrib, add_mul]
    simp only [Set.mem_ofPred_eq, this] at ha hb ⊢
    exact W.add_mem ha hb
  smul_mem' := by
    intro c u hu
    have : linForm (c • u) = C (c : ℂ) * linForm u := by
      simp [linForm, Finset.mul_sum, ← mul_assoc, Complex.real_smul]
    simp only [Set.mem_ofPred_eq, this] at hu ⊢
    exact W.mul_mem_left _ hu

theorem linForm_single (j : Fin n) :
    linForm (Pi.single j (1 : ℂ)) = (X j : MvPolynomial (Fin n) ℂ) := by
  simp [linForm, Pi.single_apply]

theorem formsIn_ne_top {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsRelevant W) : formsIn W ≠ ⊤ := by
  obtain ⟨j, hj⟩ := hW
  intro htop
  have hmem : Pi.single j (1 : ℂ) ∈ formsIn W := htop ▸ Submodule.mem_top
  exact hj (linForm_single j ▸ hmem)

end AdmissibleAE


open AdmissibleAE in
theorem AdmissibleAE.proof : AdmissibleAE.Statement := by
  intro n Z hrel
  unfold IsAdmissible
  refine (Filter.eventually_all_finset _).2 fun W hW => ?_
  rw [ae_iff]
  have hnull : volume (formsIn W : Set (Fin n → ℂ)) = 0 :=
    Measure.addHaar_submodule volume _ (formsIn_ne_top (hrel W hW))
  simp only [not_not]
  exact hnull

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAENrm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

theorem linForm_const_mul (c : ℂ) (v : Fin n → ℂ) :
    linForm (fun j => c * v j) = C c * linForm v := by
  simp only [linForm, Finset.mul_sum, map_mul, mul_assoc]

theorem HermNorm.norm_ne_zero (h : HermNorm n) {v : Fin n → ℂ} (hv : v ≠ 0) : h.norm v ≠ 0 := by
  intro h0
  apply hv
  have hs : ∑ i, ‖(h.mat *ᵥ v) i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)).mp h0
  have hm : h.mat *ᵥ v = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖(h.mat *ᵥ v) i‖)).mp hs i
      (Finset.mem_univ i)
    simpa using this
  exact Matrix.eq_zero_of_mulVec_eq_zero h.isUnit_det.ne_zero hm

theorem IsAdmissible.nrmv (h : HermNorm n) {Z : ProjCycle ℂ n} {v : Fin n → ℂ}
    (hv : IsAdmissible Z v) : IsAdmissible Z (nrmv h v) := by
  intro W hW hmem
  apply hv W hW
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hv W hW
    simp [linForm]
  have hc : ((h.norm v : ℝ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (h.norm_ne_zero hv0))
  have hmem' : C ((h.norm v : ℝ) : ℂ)⁻¹ * linForm v ∈ W := by
    rw [← linForm_const_mul]; exact hmem
  have : linForm v = C (((h.norm v : ℝ) : ℂ)⁻¹)⁻¹ * (C ((h.norm v : ℝ) : ℂ)⁻¹ * linForm v) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  rw [this]
  exact W.mul_mem_left _ hmem'

theorem AdmissibleAENrm.proof (h1 : AdmissibleAE.Statement) : AdmissibleAENrm.Statement := by
  intro n h Z hrel
  exact ae_restrict_of_ae ((h1 n Z hrel).mono fun v hv => hv.nrmv h)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

theorem AreaFormulaInj.proof (h : AreaFormulaInjSet.Statement) : AreaFormulaInj.Statement := by
  classical
  intro E F _ _ _ _ _ _ _ _ _ _ k hk U A f g hU hf hAU hA hinj hg
  let f' : E → F := U.piecewise f (fun _ => 0)
  have hf'm : Measurable f' := hf.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hEq : ∀ x ∈ A, f' x = f x := fun x hx => Set.piecewise_eq_of_mem _ _ _ (hAU hx)
  have hJ : Measurable fun x : E => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) :=
    ENNReal.measurable_ofReal.comp (continuous_areaJacobian.measurable.comp (measurable_fderiv ℝ f))
  let ρ : Measure E := ((μH[(k : ℝ)] : Measure E).restrict A).withDensity
    fun x : E => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F))
  have hmap : ρ.map f' = (μH[(k : ℝ)] : Measure F).restrict (f '' A) := by
    ext S hS
    have hpre : MeasurableSet (f' ⁻¹' S) := hf'm hS
    rw [Measure.map_apply hf'm hS, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
      Measure.restrict_apply hS,
      ← h E F k hk U _ f hU hf (by exact fun x hx => hAU hx.2) (hpre.inter hA) (hinj.mono fun x hx => hx.2)]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨hyS, hyA⟩, rfl⟩
      exact ⟨by simpa [Set.mem_preimage, hEq y hyA] using hyS, y, hyA, rfl⟩
    · rintro ⟨hzS, y, hyA, rfl⟩
      exact ⟨y, ⟨by simpa [Set.mem_preimage, hEq y hyA] using hzS, hyA⟩, rfl⟩
  calc ∫⁻ y in f '' A, g y ∂(μH[(k : ℝ)]) = ∫⁻ z, g z ∂(ρ.map f') := by rw [hmap]
    _ = ∫⁻ x, g (f' x) ∂ρ := lintegral_map hg hf'm
    _ = ∫⁻ x in A, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) * g (f' x)
          ∂(μH[(k : ℝ)]) := lintegral_withDensity_eq_lintegral_mul _ hJ (hg.comp hf'm)
    _ = _ := setLIntegral_congr_fun hA fun x hx => by rw [hEq x hx, mul_comm]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallAverageLinear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Matrix

noncomputable section

namespace BallAverageLinear

def matEquiv {n : ℕ} (h : HermNorm n) : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofLinearMap (f := (Matrix.mulVecLin h.mat).restrictScalars ℝ)
      (g := (Matrix.mulVecLin h.mat⁻¹).restrictScalars ℝ)
      (LinearMap.ext fun v => by
        simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h.isUnit_det])
      (LinearMap.ext fun v => by
        simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]))

theorem matEquiv_apply {n : ℕ} (h : HermNorm n) (v : Fin n → ℂ) : matEquiv h v = h.mat *ᵥ v := rfl

theorem ballH_eq_preimage {n : ℕ} (h : HermNorm n) :
    ballH h = matEquiv h ⁻¹' ballH (HermNorm.std n) := by
  ext v
  simp [ballH, HermNorm.norm, HermNorm.std, matEquiv_apply]

end BallAverageLinear

open BallAverageLinear in
theorem BallAverageLinear.proof : BallAverageLinear.Statement := by
  intro n h φ
  set L := matEquiv h
  have hb := ballH_eq_preimage h
  have hpre : ∀ s : Set (Fin n → ℂ), IntegrableOn (fun v => φ (h.mat *ᵥ v)) (L ⁻¹' s) ↔
      IntegrableOn φ s := by
    intro s
    have he : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
    have hmap : (map L volume).IsAddHaarMeasure := L.isAddHaarMeasure_map volume
    have h2 : map L (volume : Measure (Fin n → ℂ)) =
        addHaarScalarFactor (map L volume) volume • volume := isAddLeftInvariant_eq_smul _ _
    have hpos := addHaarScalarFactor_pos_of_isAddHaarMeasure (map L (volume : Measure (Fin n → ℂ))) volume
    rw [show (fun v => φ (h.mat *ᵥ v)) = φ ∘ L from rfl, ← he.integrableOn_map_iff, h2,
      show (addHaarScalarFactor (map L volume) volume • (volume : Measure (Fin n → ℂ))) =
        ((addHaarScalarFactor (map L volume) volume : ENNReal) • volume) from rfl,
      IntegrableOn, IntegrableOn, Measure.restrict_smul,
      integrable_smul_measure (by simpa using hpos.ne') ENNReal.coe_ne_top]
  refine ⟨by rw [hb]; exact hpre _, ?_⟩
  rw [hb]
  exact SphereMean.setAverage_comp_linearEquiv volume volume L _ φ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem BallVolume.proof : BallVolume.Statement := by
  intro n h
  have hcont : Continuous fun v : Fin n → ℂ => h.norm v := by
    simp only [HermNorm.norm, Matrix.mulVec, dotProduct]
    fun_prop
  have hopen : IsOpen (ballH h) := isOpen_lt hcont continuous_const
  have hzero : (0 : Fin n → ℂ) ∈ ballH h := by
    show h.norm 0 < 1
    simp [HermNorm.norm]
  have hR : 0 ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbdd : Bornology.IsBounded (ballH h) := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℂ))
      (r := ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖)).subset fun v hv => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
    intro j
    exact norm_le_of_hermNorm_lt h hv j
  exact ⟨hopen.measure_pos volume ⟨0, hzero⟩, hbdd.measure_lt_top⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCharacterised
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem not_isChowForm_zero (hPt : ProjPrimeHasPoint.Statement) {F : Type} [Field F] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) F)} (hW : IsProjPrime W) (g : MvPolynomial (Fin 0 × Fin n) F) :
    ¬ IsChowForm W 0 g := by
  intro hg
  obtain ⟨x, hx, hxW⟩ := hPt F n W hW
  have hunit : g ∣ 1 := by
    rw [eq_C_of_isEmpty g] at hg ⊢
    have hc : AddMonoidAlgebra.coeff g 0 ≠ 0 := fun h => hg.1 (by rw [h, map_zero])
    exact ⟨C (AddMonoidAlgebra.coeff g 0)⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩
  have hinc : (fun _ => 0 : Fin 0 × Fin n → AlgebraicClosure F) ∈ incidence W 0 :=
    ⟨x, hx, hxW, fun i => i.elim0⟩
  have := (hg.2 1).mpr hunit _ hinc
  simp at this

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartLengthAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ChartLengthAlgClosed.proof (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartFinite.Statement) (h₄ : LengthFiniteAlgebra.Statement) (h₅ : ChartMaxIdeals.Statement)
    (h₆ : ChartLocalOrder.Statement) (h₇ : ChartResidueDegreeAlgClosed.Statement) :
    ChartLengthAlgClosed.Statement := by
  intro F _ _ n e I f t u q p _ hI hf hu hq hp hqt
  classical

  have hpt : specFirst f t ∉ p := by
    rw [hp, Ideal.mem_span_singleton]
    exact hqt
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₃ F n e I f t p hI hf hpt
  rw [h₄ (Localization.AtPrime p) (ChartLoc I t e p)
    (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))]
  refine finsum_maximalSpectrum_ord_eq_sum _ _ (chartIdeal I t e p) ?_ _ ?_
  · have h := h₅ F n e I f t u q p hI hf hu hq hp hqt
    convert h using 1
    ext W
    simp
  · intro W hW _
    obtain ⟨hWs, hWq⟩ := Finset.mem_filter.mp hW
    have hrel : W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
      rw [Finsupp.mem_support_iff] at hWs
      by_contra h
      exact hWs (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
    have hqW : q ∈ incIdeal W e := hWq ▸ Ideal.mem_span_singleton_self q
    have htW : linForm t ∉ W := fun h => by
      have hIW : I ≤ W := le_trans le_sup_left hrel.1.1.2
      have := h₂ F n e I W f t hf hIW h
      rw [← hWq, Ideal.mem_span_singleton] at this
      exact hqt this
    obtain ⟨_, hord⟩ := h₆ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hlen := h₇ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hdiv : divCycle I u W = localMult (I ⊔ Ideal.span {linForm u}) W := by
      simp [divCycle, fundCycle, Finsupp.onFinset_apply, hrel]
    rw [hlen, mul_one, hdiv]
    exact hord

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreePos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowDegreePos.proof : ChowDegreePos.Statement := by
  intro n k δ W g hk hW hg hδ
  by_contra hlt
  have hδ0 : δ = 0 := by omega
  subst hδ0

  have hnt : NonTorsionWeight (groupWeight k n) := by
    intro m ij h
    have := congrFun h ij.1
    simpa [groupWeight] using this

  have hsupp : ∀ m ∈ g.support, m = 0 := by
    intro m hm
    have h1 : Finsupp.weight (groupWeight k n) m = 0 := hδ (mem_support_iff.1 hm)
    ext ij
    exact (weightedDegree_eq_zero_iff hnt).1 h1 ij
  obtain ⟨c, rfl⟩ : ∃ c, g = C c := by
    refine ⟨AddMonoidAlgebra.coeff g 0, ?_⟩
    ext m
    rw [coeff_C]
    split_ifs with hm
    · rw [hm]
    · by_contra hne
      exact hm (hsupp m (mem_support_iff.2 hne)).symm
  have hc : c ≠ 0 := by
    intro h
    apply hg.1
    rw [h, C_0]
  have hdvd : (C c : MvPolynomial (Fin k × Fin n) ℂ) ∣ 1 :=
    ⟨C c⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩
  have hvan := (hg.2 1).2 hdvd

  obtain ⟨x, hx0, hx⟩ : ∃ x : Fin n → AlgebraicClosure ℂ, x ≠ 0 ∧ ∀ p ∈ W, aeval x p = 0 := by
    by_contra hne
    obtain ⟨j, hj⟩ := hW.isRelevant
    apply hj
    have hrad : X j ∈ W.radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure ℂ)]
      rw [mem_vanishingIdeal_iff]
      intro y hy
      by_cases hy0 : y = 0
      · subst hy0
        simp
      · exact absurd ⟨y, hy0, hy⟩ hne
    rwa [hW.isPrime.radical] at hrad
  have hmem : (0 : Fin k × Fin n → AlgebraicClosure ℂ) ∈ incidence W k :=
    ⟨x, hx0, hx, fun i => by simp⟩
  have := hvan 0 hmem
  simp at this

end GroundTheory.Heights₂.Heights
end

