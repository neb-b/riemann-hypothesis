module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudyIntegral
public import GroundTheory.HeightsAndTheta.Heights.Bundle0002

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ContDiff
open MeasureTheory Topology Set MvPolynomial

noncomputable section

variable {N : ℕ}

namespace CP

instance instMeasurableSpace : MeasurableSpace (CP N) := borel (CP N)

instance instBorelSpace : BorelSpace (CP N) := ⟨rfl⟩

def fsChartMeasure (i : Fin (N + 1)) : Measure (Fin N → ℂ) :=
  volume.withDensity fun z => ENNReal.ofReal (fsVolumeDensity i z)

def fsMeasure (N : ℕ) : Measure (CP N) := (fsChartMeasure (N := N) 0).map (chartInv 0)

lemma measurable_chartInv (i : Fin (N + 1)) : Measurable (chartInv (N := N) i) :=
  (continuous_chartInv i).measurable

lemma measurable_fsVolumeDensity (i : Fin (N + 1)) :
    Measurable (fsVolumeDensity (N := N) i) := by
  have : fsVolumeDensity (N := N) i = fun z =>
      N.factorial / (Real.pi ^ N * (1 + normSqSum z) ^ (N + 1)) := by
    funext z; exact fsVolumeDensity_eq i z
  rw [this]
  unfold normSqSum
  fun_prop

theorem lintegral_fsVolumeDensity (i : Fin (N + 1)) :
    ∫⁻ z, ENNReal.ofReal (fsVolumeDensity i z) = 1 := by
  have h := lintegral_pi_complex_monomial 0 N (fun _ => 0) 1 one_pos
  simp only [mul_zero, pow_zero, Finset.prod_const_one, Finset.sum_const_zero, zero_add,
    add_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_pow, div_one] at h
  have hpt : ∀ z : Fin N → ℂ, ENNReal.ofReal (fsVolumeDensity i z) =
      ENNReal.ofReal (N.factorial / Real.pi ^ N) *
        ENNReal.ofReal (1 / (1 + ∑ j, ‖z j‖ ^ 2) ^ (N + 1)) := by
    intro z
    rw [← ENNReal.ofReal_mul (by positivity), fsVolumeDensity_eq]
    congr 1
    rw [normSqSum]
    field_simp
  rw [lintegral_congr hpt, lintegral_const_mul _ (by fun_prop), h, ← ENNReal.ofReal_mul (by positivity)]
  have hpi := Real.pi_pos
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  rw [show (N.factorial : ℝ) / Real.pi ^ N * (Real.pi ^ N / N.factorial) = 1 by field_simp]
  simp

theorem fsMeasure_univ : fsMeasure N univ = 1 := by
  rw [fsMeasure, Measure.map_apply (measurable_chartInv 0) MeasurableSet.univ, preimage_univ,
    fsChartMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_fsVolumeDensity]

instance (N : ℕ) : IsProbabilityMeasure (fsMeasure N) := ⟨fsMeasure_univ⟩

def fsNormPoly (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (x : CP N) : ℝ :=
  ‖eval x.rep P‖ / norm2 x.rep ^ n

theorem fsNormPoly_mk {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n)
    (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    fsNormPoly n P (Projectivization.mk ℂ v hv) = ‖eval v P‖ / norm2 v ^ n := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [fsNormPoly, ← ha, Units.smul_def]
  have he : eval ((a : ℂ) • v) P = (a : ℂ) ^ n * eval v P :=
    evalAt_smul (RingHom.id ℂ) hP (a : ℂ) v
  have hn : 0 < norm2 v := euclideanNorm_pos hv
  have ha0 : 0 < ‖(a : ℂ)‖ := norm_pos_iff.mpr a.ne_zero
  rw [he, norm_mul, norm_pow, euclideanNorm_smul, mul_pow]
  field_simp

theorem continuous_fsNormPoly {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n) :
    Continuous (fsNormPoly (N := N) n P) := by
  rw [ProjTopology.continuous_iff]
  have : fsNormPoly (N := N) n P ∘ Projectivization.mk' ℂ =
      fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => ‖eval v.1 P‖ / norm2 v.1 ^ n := by
    funext ⟨v, hv⟩; exact fsNormPoly_mk hP v hv
  rw [this]
  have hc : Continuous fun v : Fin (N + 1) → ℂ => norm2 v :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
      (continuous_norm.comp (continuous_apply j)).pow 2)
  refine Continuous.div ?_ ((hc.comp continuous_subtype_val).pow n)
    fun v => (pow_pos (euclideanNorm_pos v.2) n).ne'
  exact continuous_norm.comp ((MvPolynomial.continuous_eval P).comp continuous_subtype_val)

def sectionL2NormSq (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : ℝ :=
  ∫ x, fsNormPoly n P x ^ 2 ∂fsMeasure N

def l2Norm (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : ℝ := √(sectionL2NormSq (N := N) n P)

lemma sectionL2NormSq_nonneg (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : 0 ≤ sectionL2NormSq (N := N) n P :=
  integral_nonneg fun _ => sq_nonneg _

lemma fubiniStudy_l2Norm_sq_eq (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) :
    l2Norm (N := N) n P ^ 2 = sectionL2NormSq n P := Real.sq_sqrt (sectionL2NormSq_nonneg n P)

lemma chartVec_zero_succ (z : Fin N → ℂ) (j : Fin N) : chartVec 0 z j.succ = z j := by
  rw [← Fin.succAbove_zero, chartVec_succAbove]

lemma fsNormPoly_monomial_sq_chartInv (a : Fin (N + 1) →₀ ℕ) (z : Fin N → ℂ) :
    fsNormPoly a.degree (monomial a (1 : ℂ)) (chartInv 0 z) ^ 2 =
      (∏ j, ‖z j‖ ^ (2 * a j.succ)) / (1 + ∑ j, ‖z j‖ ^ 2) ^ a.degree := by
  rw [chartInv, fsNormPoly_mk (isHomogeneous_monomial 1 rfl), eval_monomial, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), div_pow,
    show (norm2 (chartVec 0 z) ^ a.degree) ^ 2 = (norm2 (chartVec 0 z) ^ 2) ^ a.degree by ring,
    euclideanNorm_sq, normSq2_chartVec, norm_prod, Fin.prod_univ_succ, chartVec_self]
  simp only [one_pow, norm_one, one_mul, norm_pow, chartVec_zero_succ]
  congr 1
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm]

theorem fubiniStudy_l2Norm_monomial_sq (a : Fin (N + 1) →₀ ℕ) :
    l2Norm (N := N) a.degree (monomial a (1 : ℂ)) ^ 2 =
      (∏ i, ((a i).factorial : ℝ)) * N.factorial / (a.degree + N).factorial := by
  have hdeg : a.degree = a 0 + ∑ j : Fin N, a j.succ := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  have hfm : AEStronglyMeasurable (fun x : CP N => fsNormPoly a.degree (monomial a (1 : ℂ)) x ^ 2)
      (Measure.map (chartInv 0) (fsChartMeasure (N := N) 0)) :=
    ((continuous_fsNormPoly (isHomogeneous_monomial (1 : ℂ) rfl)).pow 2).aestronglyMeasurable
  rw [fubiniStudy_l2Norm_sq_eq, sectionL2NormSq, fsMeasure, integral_map (measurable_chartInv 0).aemeasurable hfm,
    fsChartMeasure]
  have hd : (fun z => ENNReal.ofReal (fsVolumeDensity (N := N) 0 z)) =
      fun z => (((fsVolumeDensity (N := N) 0 z).toNNReal : NNReal) : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul (measurable_fsVolumeDensity 0).real_toNNReal]
  have hpt : ∀ z : Fin N → ℂ, (fsVolumeDensity (N := N) 0 z).toNNReal •
      fsNormPoly a.degree (monomial a (1 : ℂ)) (chartInv 0 z) ^ 2 =
      (N.factorial / Real.pi ^ N) * ((∏ j, ‖z j‖ ^ (2 * a j.succ)) /
        (1 + ∑ j, ‖z j‖ ^ 2) ^ (∑ j : Fin N, a j.succ + N + 1 + a 0)) := by
    intro z
    rw [NNReal.smul_def, Real.coe_toNNReal _ (fsVolumeDensity_pos 0 z).le, smul_eq_mul,
      fsNormPoly_monomial_sq_chartInv, fsVolumeDensity_eq, normSqSum,
      show ∑ j : Fin N, a j.succ + N + 1 + a 0 = a.degree + (N + 1) by rw [hdeg]; ring, pow_add]
    have hS : 0 < 1 + ∑ j, ‖z j‖ ^ 2 := by positivity
    have hpi := Real.pi_pos
    field_simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    (integral_pi_complex_monomial (a 0) N (fun j => a j.succ) 1 one_pos).2,
    Fin.prod_univ_succ, show ∑ j : Fin N, a j.succ + N + a 0 = a.degree + N by rw [hdeg]; ring]
  have hpi := Real.pi_pos
  have hf : ((a.degree + N).factorial : ℝ) ≠ 0 := by positivity
  simp only [one_pow, div_one]
  field_simp

end CP

end

end GroundTheory.Heights₂.Heights
