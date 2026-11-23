module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
public import GroundTheory.HeightsAndTheta.Heights.ComplexPoints
public import GroundTheory.HeightsAndTheta.Heights.FinrankFibreAtOfIsInvertibleSheaf
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.PSpaceFinite
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudyMetric
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafAlt

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace NumberField GroundTheory.Arith.SchemeCoh
  MeasureTheory MvPolynomial TensorProduct
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

namespace L2MonomialOrthogonality

variable {N : ℕ}

def monoInner (n : ℕ) (a b : Fin (N + 1) →₀ ℕ) (v : Fin (N + 1) → ℂ) : ℂ :=
  starRingEnd ℂ (eval v (monomial a (1 : ℂ))) * eval v (monomial b (1 : ℂ)) /
    ((norm2 v ^ (2 * n) : ℝ) : ℂ)

lemma monoInner_smul {n : ℕ} {a b : Fin (N + 1) →₀ ℕ} (ha : a.degree = n) (hb : b.degree = n)
    (t : ℂ) (ht : t ≠ 0) (v : Fin (N + 1) → ℂ) :
    monoInner n a b (t • v) = monoInner n a b v := by
  have hea : eval (t • v) (monomial a (1 : ℂ)) = t ^ n * eval v (monomial a 1) :=
    evalAt_smul (RingHom.id ℂ) (isHomogeneous_monomial 1 ha) t v
  have heb : eval (t • v) (monomial b (1 : ℂ)) = t ^ n * eval v (monomial b 1) :=
    evalAt_smul (RingHom.id ℂ) (isHomogeneous_monomial 1 hb) t v
  have htn : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr ht).ne'
  have e : starRingEnd ℂ t ^ n * t ^ n = ((‖t‖ : ℂ) ^ 2) ^ n := by
    rw [← mul_pow, Complex.conj_mul']
  unfold monoInner
  rw [hea, heb, euclideanNorm_smul, map_mul, map_pow]
  push_cast
  calc _ = (starRingEnd ℂ t ^ n * t ^ n) * (starRingEnd ℂ (eval v (monomial a (1 : ℂ))) *
        eval v (monomial b (1 : ℂ))) / (((‖t‖ : ℂ) ^ 2) ^ n * (norm2 v : ℂ) ^ (2 * n)) := by ring
    _ = _ := by rw [e, mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ htn))]

lemma monoInner_mk {n : ℕ} {a b : Fin (N + 1) →₀ ℕ} (ha : a.degree = n) (hb : b.degree = n)
    (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    monoInner n a b (Projectivization.mk ℂ v hv).rep = monoInner n a b v := by
  obtain ⟨t, ht⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [← ht, Units.smul_def]
  exact monoInner_smul ha hb t t.ne_zero v

lemma continuous_monoInner_rep {n : ℕ} {a b : Fin (N + 1) →₀ ℕ} (ha : a.degree = n)
    (hb : b.degree = n) : Continuous fun x : CP N => monoInner n a b x.rep := by
  rw [ProjTopology.continuous_iff]
  have : (fun x : CP N => monoInner n a b x.rep) ∘ Projectivization.mk' ℂ =
      fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => monoInner n a b v.1 := by
    funext ⟨v, hv⟩
    exact monoInner_mk ha hb v hv
  rw [this]
  have hc : Continuous fun v : Fin (N + 1) → ℂ => norm2 v :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
      (continuous_norm.comp (continuous_apply j)).pow 2)
  unfold monoInner
  refine Continuous.div ?_ ?_ ?_
  · exact (Complex.continuous_conj.comp ((continuous_eval _).comp continuous_subtype_val)).mul
      ((continuous_eval _).comp continuous_subtype_val)
  · exact Complex.continuous_ofReal.comp ((hc.comp continuous_subtype_val).pow _)
  · intro v
    exact_mod_cast (pow_pos (euclideanNorm_pos v.2) _).ne'

lemma integral_fsMeasure_eq (f : CP N → ℂ) (hf : Continuous f) :
    ∫ x, f x ∂CP.fsMeasure N = ∫ z, (CP.fsVolumeDensity 0 z : ℂ) * f (CP.chartInv 0 z) := by
  rw [CP.fsMeasure, integral_map (CP.measurable_chartInv 0).aemeasurable hf.aestronglyMeasurable,
    CP.fsChartMeasure]
  have hd : (fun z => ENNReal.ofReal (CP.fsVolumeDensity (N := N) 0 z)) =
      fun z => (((CP.fsVolumeDensity (N := N) 0 z).toNNReal : NNReal) : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul (CP.measurable_fsVolumeDensity 0).real_toNNReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (CP.fsVolumeDensity_pos 0 z).le, Complex.real_smul]

lemma eval_chartVec_monomial (a : Fin (N + 1) →₀ ℕ) (w : Fin N → ℂ) :
    eval (CP.chartVec 0 w) (monomial a (1 : ℂ)) = ∏ j, w j ^ a j.succ := by
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_succ,
    CP.chartVec_self, one_pow, one_mul]
  simp only [CP.chartVec_zero_succ]

theorem integral_monoInner_eq_zero {a b : Fin (N + 1) →₀ ℕ} (hab : a ≠ b)
    (hb : b.degree = a.degree) :
    ∫ x, monoInner a.degree a b x.rep ∂CP.fsMeasure N = 0 := by

  obtain ⟨k, hk⟩ : ∃ k : Fin N, a k.succ ≠ b k.succ := by
    by_contra! h
    apply hab
    have hdeg : ∀ c : Fin (N + 1) →₀ ℕ, c.degree = c 0 + ∑ j : Fin N, c j.succ := fun c => by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]
    have h0 : a 0 = b 0 := by
      have h1 := hdeg a
      have h2 := hdeg b
      simp only [h] at h1
      omega
    ext i
    exact Fin.cases h0 (fun j => h j) i
  set p := a k.succ with hp
  set q := b k.succ with hq
  set θ : ℝ := Real.pi / ((q : ℝ) - p) with hθ
  set u : Circle := Circle.exp θ with hu
  have hlam : starRingEnd ℂ (u : ℂ) ^ p * (u : ℂ) ^ q = -1 := by
    have hqp : ((q : ℂ) - p) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hk))
    rw [hu, Circle.coe_exp, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add]
    have h1 : (θ : ℂ) * ((q : ℂ) - p) = Real.pi := by
      rw [hθ]
      push_cast
      field_simp
    have h2 : (p : ℂ) * (starRingEnd ℂ) (↑θ * Complex.I) + (q : ℂ) * (↑θ * Complex.I) =
        Real.pi * Complex.I := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      linear_combination Complex.I * h1
    rw [h2, Complex.exp_pi_mul_I]

  let c : Fin N → Circle := fun j => if j = k then u else 1
  have hc : ∀ j, (c j : ℂ) = if j = k then (u : ℂ) else 1 := fun j => by
    by_cases hj : j = k <;> simp [c, hj]
  let T : (Fin N → ℂ) ≃ₜ (Fin N → ℂ) :=
    Homeomorph.piCongrRight fun j => (rotation (c j)).toHomeomorph
  have hT : ∀ z j, T z j = c j * z j := fun z j => rfl
  have hTm : MeasurePreserving T volume volume :=
    measurePreserving_pi (fun _ => volume) (fun _ => volume)
      fun j => (rotation (c j)).measurePreserving
  have hnorm : ∀ z j, ‖T z j‖ = ‖z j‖ := fun z j => by
    rw [hT, norm_mul, Circle.norm_coe, one_mul]
  have hprod : ∀ (m : Fin (N + 1) →₀ ℕ) (z : Fin N → ℂ),
      eval (CP.chartVec 0 (T z)) (monomial m (1 : ℂ)) =
        (u : ℂ) ^ m k.succ * eval (CP.chartVec 0 z) (monomial m (1 : ℂ)) := fun m z => by
    rw [eval_chartVec_monomial, eval_chartVec_monomial]
    simp only [hT, mul_pow, Finset.prod_mul_distrib, hc, ite_pow, one_pow, Finset.prod_ite_eq',
      Finset.mem_univ, if_true]

  set G : (Fin N → ℂ) → ℂ := fun z =>
    (CP.fsVolumeDensity 0 z : ℂ) * monoInner a.degree a b (CP.chartVec 0 z) with hG
  have hGT : ∀ z, G (T z) = -G z := fun z => by
    have hdens : CP.fsVolumeDensity (N := N) 0 (T z) = CP.fsVolumeDensity 0 z := by
      rw [CP.fsVolumeDensity_eq, CP.fsVolumeDensity_eq, normSqSum, normSqSum]
      simp only [hnorm]
    have hn2 : norm2 (CP.chartVec 0 (T z)) = norm2 (CP.chartVec 0 z) := by
      rw [norm2, norm2, CP.normSq2_chartVec, CP.normSq2_chartVec]
      simp only [hnorm]
    simp only [hG, hdens, monoInner, hn2, hprod, map_mul, map_pow]
    rw [← hp, ← hq]
    linear_combination (CP.fsVolumeDensity 0 z : ℂ) *
      (starRingEnd ℂ (eval (CP.chartVec 0 z) (monomial a (1 : ℂ))) *
        eval (CP.chartVec 0 z) (monomial b (1 : ℂ)) /
          ((norm2 (CP.chartVec 0 z) ^ (2 * a.degree) : ℝ) : ℂ)) * hlam
  have hint : ∫ x, monoInner a.degree a b x.rep ∂CP.fsMeasure N = ∫ z, G z := by
    rw [integral_fsMeasure_eq _ (continuous_monoInner_rep rfl hb)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hG, CP.chartInv, monoInner_mk rfl hb]
  have hinv : ∫ z, G z = -∫ z, G z := by
    calc ∫ z, G z = ∫ z, G (T z) := (hTm.integral_comp T.measurableEmbedding G).symm
      _ = ∫ z, -G z := by simp only [hGT]
      _ = -∫ z, G z := integral_neg _
  rw [hint]
  linear_combination hinv / 2

theorem integral_monoInner_self (a : Fin (N + 1) →₀ ℕ) :
    ∫ x, monoInner a.degree a a x.rep ∂CP.fsMeasure N =
      (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (a.degree + N).factorial : ℝ) : ℂ) := by
  have hpt : ∀ v : CP N, monoInner a.degree a a v.rep =
      ((CP.fsNormPoly a.degree (monomial a (1 : ℂ)) v ^ 2 : ℝ) : ℂ) := fun v => by
    have e := Complex.conj_mul' (eval v.rep (monomial a (1 : ℂ)))
    unfold monoInner CP.fsNormPoly
    push_cast
    rw [div_pow, ← e]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal]
  congr 1
  change CP.sectionL2NormSq (N := N) a.degree (monomial a (1 : ℂ)) = _
  rw [← CP.fubiniStudy_l2Norm_sq_eq, CP.fubiniStudy_l2Norm_monomial_sq]

end L2MonomialOrthogonality

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
