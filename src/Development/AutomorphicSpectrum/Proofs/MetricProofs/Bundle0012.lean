module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MobiusChangeOfVariablesPair
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

def dom : Set ℂ := {a | den g a ≠ 0}

def cod : Set ℂ := {b | g 1 1 - g 0 1 * b ≠ 0}

variable {g}

theorem det_eq : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g

theorem isOpen_dom : IsOpen (dom g) := by
  have hc : Continuous fun a : ℂ => GlobalTheory.CompanionTheory.Ar.PB.FibPt.den g a := by
    show Continuous fun a : ℂ => g 0 0 + g 0 1 * a
    fun_prop
  exact isOpen_ne_fun hc continuous_const

theorem hasDerivAt_mob {a : ℂ} (ha : a ∈ dom g) : HasDerivAt (mob g) (mobD g a) a := by
  have hden : g 0 0 + g 0 1 * a ≠ 0 := ha
  have h1 : HasDerivAt (fun z : ℂ => g 1 0 + g 1 1 * z) (g 1 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 1 1)).const_add (g 1 0)
  have h2 : HasDerivAt (fun z : ℂ => g 0 0 + g 0 1 * z) (g 0 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 0 1)).const_add (g 0 0)
  have h := h1.div h2 hden
  have heq : GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g
      = (fun z : ℂ => g 1 0 + g 1 1 * z) / (fun z : ℂ => g 0 0 + g 0 1 * z) := by
    funext z
    rfl
  have hval : GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a
      = (g 1 1 * (g 0 0 + g 0 1 * a) - (g 1 0 + g 1 1 * a) * g 0 1) / (g 0 0 + g 0 1 * a) ^ 2 := by
    rw [show GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a = g.det / (g 0 0 + g 0 1 * a) ^ 2 from rfl,
      GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    ring
  rw [heq, hval]
  exact h

theorem injOn_mob (hg : IsUnit g.det) : Set.InjOn (mob g) (dom g) := by
  intro a ha b hb hab
  have ha' : g 0 0 + g 0 1 * a ≠ 0 := ha
  have hb' : g 0 0 + g 0 1 * b ≠ 0 := hb
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    rw [← GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    exact hg.ne_zero
  have h : (g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)
      = (g 1 0 + g 1 1 * b) / (g 0 0 + g 0 1 * b) := hab
  rw [div_eq_div_iff ha' hb'] at h
  have h2 : (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (a - b) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hdet
  · exact sub_eq_zero.1 h3

theorem image_mob (hg : IsUnit g.det) : mob g '' dom g = cod g := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    rw [← GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    exact hg.ne_zero
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : g 0 0 + g 0 1 * a ≠ 0 := ha
    show g 1 1 - g 0 1 * ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) ≠ 0
    have hval : g 1 1 - g 0 1 * ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a))
        = (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 0 0 + g 0 1 * a) := by
      field_simp
      ring
    rw [hval]
    exact div_ne_zero hdet ha'
  · intro hb
    have hb' : g 1 1 - g 0 1 * b ≠ 0 := hb
    have hx : (g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b) * (g 1 1 - g 0 1 * b)
        = g 0 0 * b - g 1 0 := div_mul_cancel₀ _ hb'
    have hden : g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))
        = (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 1 - g 0 1 * b) := by
      rw [eq_div_iff hb']
      linear_combination g 0 1 * hx
    have hnum : g 1 0 + g 1 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))
        = b * (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 1 - g 0 1 * b) := by
      rw [eq_div_iff hb']
      linear_combination g 1 1 * hx
    refine ⟨(g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b), ?_, ?_⟩
    · show g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b)) ≠ 0
      rw [hden]
      exact div_ne_zero hdet hb'
    · show (g 1 0 + g 1 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))) /
          (g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))) = b
      rw [hnum, hden, div_div_div_cancel_right₀ hb', mul_div_assoc, div_self hdet, mul_one]

theorem null_affine {c d : ℂ} (h : c ≠ 0 ∨ d ≠ 0) : volume {a : ℂ | c + d * a = 0} = 0 := by
  refine Set.Subsingleton.measure_zero ?_ _
  intro x hx y hy
  have hx' : c + d * x = 0 := hx
  have hy' : c + d * y = 0 := hy
  have hd : d ≠ 0 := by
    rintro rfl
    rcases h with hc | hd
    · exact hc (by simpa using hx')
    · exact hd rfl
  have hxy : d * (x - y) = 0 := by
    linear_combination hx' - hy'
  exact sub_eq_zero.1 ((mul_eq_zero.1 hxy).resolve_left hd)

theorem ae_prod_self {V : Set ℂ} (hV : volume Vᶜ = 0) :
    (V ×ˢ V : Set (ℂ × ℂ)) =ᵐ[(volume : Measure (ℂ × ℂ))] (Set.univ : Set (ℂ × ℂ)) := by
  rw [ae_eq_univ]
  have h1 : (volume : Measure (ℂ × ℂ)) (Prod.fst ⁻¹' Vᶜ) = 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.preimage_null hV
  have h2 : (volume : Measure (ℂ × ℂ)) (Prod.snd ⁻¹' Vᶜ) = 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.preimage_null hV
  refine measure_mono_null (fun p hp => ?_) (measure_union_null h1 h2)
  simp only [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hp
  simpa only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff] using hp

theorem null_dom (hg : IsUnit g.det) : volume (dom g)ᶜ = 0 := by
  have hne : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg.ne_zero
    rw [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq, h.1, h.2]
    ring
  refine measure_mono_null (fun a ha => ?_) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_affine hne)
  have ha' : ¬ (g 0 0 + g 0 1 * a ≠ 0) := ha
  exact not_not.1 ha'

theorem null_cod (hg : IsUnit g.det) : volume (cod g)ᶜ = 0 := by
  have hne : g 1 1 ≠ 0 ∨ -g 0 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have h01 : g 0 1 = 0 := neg_eq_zero.1 h.2
    apply hg.ne_zero
    rw [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq, h.1, h01]
    ring
  refine measure_mono_null (fun b hb => ?_) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_affine hne)
  have hb' : ¬ (g 1 1 - g 0 1 * b ≠ 0) := hb
  show g 1 1 + -g 0 1 * b = 0
  linear_combination not_not.1 hb'

theorem det_smul_one (z : ℂ) :
    LinearMap.det ((z • (1 : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Complex.normSq z := by
  have hmul : ((z • (1 : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ z := by
    refine LinearMap.ext fun w => ?_
    rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    simp
  rw [hmul, ← Algebra.norm_apply, Algebra.norm_complex_apply]

theorem det_prodMap (z w : ℂ) :
    ((z • (1 : ℂ →L[ℝ] ℂ)).prodMap (w • (1 : ℂ →L[ℝ] ℂ))).det
      = Complex.normSq z * Complex.normSq w := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_smul_one, GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_smul_one]

theorem integral_mob_sq (hg : IsUnit g.det) (f : ℂ × ℂ → ℝ) :
    ∫ p : ℂ × ℂ, (Complex.normSq (mobD g p.1) * Complex.normSq (mobD g p.2)) * f (mob g p.1, mob g p.2)
      = ∫ q : ℂ × ℂ, f q := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure (ℂ × ℂ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hUo : IsOpen (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) := GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.isOpen_dom
  have hUm : MeasurableSet (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) :=
    hUo.measurableSet.prod hUo.measurableSet
  have hderiv : ∀ p ∈ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g,
      HasFDerivWithinAt (Prod.map (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g))
        ((GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1 • (1 : ℂ →L[ℝ] ℂ)).prodMap
          (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2 • (1 : ℂ →L[ℝ] ℂ)))
        (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) p := by
    intro p hp
    exact (HasFDerivAt.prodMap p
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.hasDerivAt_mob hp.1).complexToReal_fderiv
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.hasDerivAt_mob hp.2).complexToReal_fderiv).hasFDerivWithinAt
  have hinj : Set.InjOn (Prod.map (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g))
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) := by
    intro p hp q hq hpq
    exact Prod.ext (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.injOn_mob hg hp.1 hq.1 (congrArg Prod.fst hpq))
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.injOn_mob hg hp.2 hq.2 (congrArg Prod.snd hpq))
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hUm hderiv hinj f
  rw [Set.prodMap_image_prod, GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.image_mob hg,
    setIntegral_congr_set (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.ae_prod_self (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_cod hg)),
    setIntegral_congr_set (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.ae_prod_self (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_dom hg)),
    setIntegral_univ, setIntegral_univ] at hcv
  rw [hcv]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_prodMap, Prod.map_apply, smul_eq_mul]
  rw [abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main :
    ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ × ℂ → ℝ, ∫ p : ℂ × ℂ, (Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1) * Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2)) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.1, GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.2) = ∫ q : ℂ × ℂ, f q :=
  fun _ hg f => GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.integral_mob_sq hg f
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace SamePotInt

variable {D : ℕ}

theorem exists_fderiv_fderiv_re {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ} (hH : AnalyticAt ℂ H y) :
    ∃ B : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ, ∀ v w,
      fderiv ℝ (fderiv ℝ fun z => (H z).re) y v w = (B v w).re := by
  let Φ : ((Fin D → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin D → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ)
  have hev : (fderiv ℝ fun z => (H z).re) =ᶠ[𝓝 y] fun z => Φ (fderiv ℂ H z) := by
    filter_upwards [hH.eventually_analyticAt] with z hz
    have h1 : HasFDerivAt H ((fderiv ℂ H z).restrictScalars ℝ) z :=
      hz.differentiableAt.hasFDerivAt.restrictScalars ℝ
    exact (Complex.reCLM.hasFDerivAt.comp z h1).fderiv
  have hd : DifferentiableAt ℂ (fderiv ℂ H) y := hH.fderiv.differentiableAt
  refine ⟨fderiv ℂ (fderiv ℂ H) y, fun v w => ?_⟩
  have h2 : HasFDerivAt (fun z => Φ (fderiv ℂ H z))
      (Φ.comp ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ)) y :=
    Φ.hasFDerivAt.comp y (hd.hasFDerivAt.restrictScalars ℝ)
  rw [hev.fderiv_eq, h2.fderiv]
  rfl

theorem hessC_re_eq_zero {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ} (hH : AnalyticAt ℂ H y) :
    hessC (fun z => (H z).re) y = 0 := by
  obtain ⟨B, hB⟩ := exists_fderiv_fderiv_re hH
  ext i j
  simp only [hessC, Matrix.zero_apply, hB, map_smul, _root_.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  push_cast
  ring

theorem hessC_eq_of_eventuallyEq_add_re {a a' : (Fin D → ℂ) → ℝ} {H : (Fin D → ℂ) → ℂ}
    {y : Fin D → ℂ} (ha : ContDiffAt ℝ 2 a y) (hH : AnalyticAt ℂ H y)
    (hev : a' =ᶠ[𝓝 y] fun z => a z + (H z).re) : hessC a' y = hessC a y := by
  have hb : ContDiffAt ℝ 2 (fun z => (H z).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hH.contDiffAt.restrict_scalars ℝ)
  have h2 : fderiv ℝ (fderiv ℝ a') y =
      fderiv ℝ (fderiv ℝ a) y + fderiv ℝ (fderiv ℝ fun z => (H z).re) y := by
    have hda : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ a z :=
      (ha.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have hdb : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (fun z => (H z).re) z :=
      (hb.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have h1 : fderiv ℝ a' =ᶠ[𝓝 y] fun z => fderiv ℝ a z + fderiv ℝ (fun z => (H z).re) z := by
      filter_upwards [hev.eventuallyEq_nhds, hda, hdb] with z hz hza hzb
      rw [hz.fderiv_eq]
      exact fderiv_add hza hzb
    rw [h1.fderiv_eq]
    exact fderiv_add ((ha.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have h0 := hessC_re_eq_zero hH
  rw [← add_zero (hessC a y), ← h0]
  ext i j
  simp only [hessC, Matrix.add_apply, h2, _root_.add_apply]
  push_cast
  ring

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem locDens_eq_of_samePot (A : FinHolAtlas e X) {U : Set X} {P Q : Fin e → LocPot X}
    (hPQ : ∀ i, SamePot A U (P i) (Q i)) (hC : ∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hU : (A.chart j).symm y ∈ U) :
    locDens A P j y = locDens A Q j y := by
  have key : ∀ i, hessC (fun y' => (P i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      hessC (fun y' => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro i
    obtain ⟨V, hVo, hxV, G, hG, hPQV⟩ := hPQ i _ hU
    have hsrc : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hy
    have ha : ContDiffAt ℝ 2 (fun y' => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
      have h := hC i _ hU j hsrc
      rw [(A.chart j).right_inv hy] at h
      exact h
    have hH : AnalyticAt ℂ (fun y' => G ((A.chart j).symm y')) y := hG j y ⟨hy, hxV⟩
    refine hessC_eq_of_eventuallyEq_add_re ha hH ?_
    have hV : (A.chart j).symm ⁻¹' V ∈ 𝓝 y :=
      ((A.chart j).continuousAt_symm hy).preimage_mem_nhds (hVo.mem_nhds hxV)
    filter_upwards [hV] with z hz
    exact sub_eq_iff_eq_add'.mp (hPQV _ hz)
  simp only [locDens, maDens, key]

end SamePotInt

theorem mInt_congr_samePot : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (U : Set X) (P Q : Fin e → LocPot X) (g g' : X → ℝ), IsNull A Uᶜ →
    (∀ i, SamePot A U (P i) (Q i)) → (∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) → (∀ x ∈ U, g x = g' x) →
    mInt A P g = mInt A Q g' ∧ (MIntegrable A P g ↔ MIntegrable A Q g') := by
  intro e X _ _ _ A U P Q g g' hN hPQ hC hg
  have hpt : ∀ (j : Fin A.n) (y : Fin e → ℂ), y ∈ (A.chart j).target → (A.chart j).symm y ∈ U →
      g ((A.chart j).symm y) = g' ((A.chart j).symm y) ∧ locDens A P j y = locDens A Q j y :=
    fun j y hy hU => ⟨hg _ hU, SamePotInt.locDens_eq_of_samePot A hPQ hC j hy hU⟩
  have hae : ∀ (j : Fin A.n), ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin e → ℂ)),
      y ∈ (A.chart j).target → (A.chart j).symm y ∈ U := by
    intro j
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (hN j)
    intro y hy
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hy
    exact ⟨hy.1, hy.2⟩
  constructor
  · by_cases h : Nonempty (ChartPartition A)
    · simp only [mInt, dif_pos h, integralWith]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine MeasureTheory.setIntegral_congr_ae (A.chart j).open_target.measurableSet ?_
      filter_upwards [hae j] with y hy hyt
      obtain ⟨h1, h2⟩ := hpt j y hyt (hy hyt)
      simp only [h1, h2]
    · simp only [mInt, dif_neg h]
  · unfold MIntegrable
    refine forall_congr' fun j => forall_congr' fun K => forall_congr' fun hK =>
      forall_congr' fun hKc => ?_
    refine MeasureTheory.integrableOn_congr_fun_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hKc.isClosed.measurableSet]
    filter_upwards [hae j] with y hy hyK
    obtain ⟨h1, h2⟩ := hpt j y (hK hyK) (hy (hK hyK))
    simp only [h1, h2]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodense
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Bdry

theorem bdry_isClosed_dense_compl (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X)
    (hs : IsSection A L s) (hn : IsSNC A L s m W) : IsClosed (bdry s) ∧ Dense (bdry s)ᶜ := by
  have key := _root_.GlobalTheory.CompanionTheory.Metric.bdry_snc_chart e X A L s nb m W hs hn
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨ψ, -, hyψ, S, hS⟩ := key y
    have hopen : IsOpen (ψ.source ∩ ψ ⁻¹' {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0}) := by
      apply ψ.continuousOn.isOpen_inter_preimage ψ.open_source
      have : {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0} = ⋂ i ∈ S, {z : Fin e → ℂ | z i ≠ 0} := by
        ext z; simp
      rw [this]
      exact isOpen_biInter_finset fun i _ =>
        isOpen_ne_fun (continuous_apply i) continuous_const
    have hmem : y ∈ ψ.source ∩ ψ ⁻¹' {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0} := by
      refine ⟨hyψ, fun i hi h0 => hy ((hS y hyψ).2 ⟨i, hi, h0⟩)⟩
    refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
    rintro y' ⟨h1, h2⟩ hb
    obtain ⟨i, hi, h0⟩ := (hS y' h1).1 hb
    exact h2 i hi h0
  · rw [dense_iff_inter_open]
    intro V hV ⟨x, hx⟩
    obtain ⟨ψ, -, hxψ, S, hS⟩ := key x
    have hsub : V ∩ ψ.source ⊆ ψ.source := Set.inter_subset_right
    have himg : IsOpen (ψ '' (V ∩ ψ.source)) :=
      ψ.isOpen_image_of_subset_source (hV.inter ψ.open_source) hsub
    have hne : (ψ '' (V ∩ ψ.source)).Nonempty := ⟨ψ x, x, ⟨hx, hxψ⟩, rfl⟩
    obtain ⟨z, hz, hz0⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero e).inter_open_nonempty _ himg hne
    obtain ⟨y, ⟨hyV, hyψ⟩, rfl⟩ := hz
    refine ⟨y, hyV, fun hb => ?_⟩
    obtain ⟨i, -, h0⟩ := (hS y hyψ).1 hb
    exact hz0 i h0

end GlobalTheory.CompanionTheory.Ar.Bdry
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChart
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem contDiffAt_comp_compatChart_symm :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
      (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ),
      IsCompatChart A ψ → IsOpen U → A.SmoothOn U g →
        ∀ z ∈ ψ.target, ψ.symm z ∈ U → ContDiffAt ℝ ∞ (g ∘ ψ.symm) z := by
  intro e X _ A ψ U g hψ hU hg z hz hzU
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hτ : ContDiffAt ℝ ∞ (⇑(A.chart j) ∘ ⇑ψ.symm) z :=
    (((hψ j).2 z ⟨hz, hj⟩).contDiffAt).restrict_scalars ℝ
  have hy : (A.chart j) (ψ.symm z) ∈ (A.chart j).target ∩ ⇑(A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm ((A.chart j) (ψ.symm z)) ∈ U
    rw [(A.chart j).left_inv hj]
    exact hzU
  have hgc : ContDiffAt ℝ ∞ (g ∘ ⇑(A.chart j).symm) ((A.chart j) (ψ.symm z)) :=
    (hg j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hy)
  have hcomp := hgc.comp z hτ
  apply hcomp.congr_of_eventuallyEq
  have hev : ∀ᶠ w in 𝓝 z, ψ.symm w ∈ (A.chart j).source :=
    (ψ.continuousAt_symm hz).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply, (A.chart j).left_inv hw]

end GlobalTheory.CompanionTheory.Metric
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartCompositionStatement
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOn_of_chart_composition : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | exact GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | (intros; apply GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' <;> assumption)
end

