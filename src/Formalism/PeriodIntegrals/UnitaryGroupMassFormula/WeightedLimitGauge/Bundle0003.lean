module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushE
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem continuous_opBeta (k : ℕ) (a : Fin k) : Continuous (fun q : TrE k => opBeta k q a) := by

  have hq : ∀ i, Continuous (fun q : TrE k => ((q i : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous
  unfold opBeta
  exact ((hq _).add ((hq _).mul continuous_const)).div_const _

theorem continuous_opGen (k r : ℕ) : Continuous (opGen k r : TrE k → Mat k r) := by

  have hq : ∀ i, Continuous (fun q : TrE k => ((q i : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  unfold opGen
  split_ifs
  all_goals first
    | exact continuous_const
    | exact continuous_opBeta k _
    | exact (continuous_opBeta k _).star
    | exact (hq none).mul continuous_const

theorem continuous_opEmap (k r : ℕ) (T' : ℝ) :
    Continuous (fun q : TrE k => opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) := by

  letI : NormedRing (Mat k r) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Mat k r) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Mat k r) := Matrix.linftyOpNormedAlgebra
  have h1 : Continuous (fun q : TrE k => NormedSpace.exp (opGen k r q)) :=
    NormedSpace.exp_continuous.comp (continuous_opGen k r)
  have h2 : Continuous (fun q : TrE k => NormedSpace.exp (opGen k r q) *ᵥ opBase k r T') :=
    h1.matrix_mulVec continuous_const
  unfold opCo
  exact (continuous_pi (fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp h2)).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp h2)

theorem opEMeas : OpEMeas := by

  intro k r T' ρ
  unfold opE
  have hball : Metric.ball (0 : TrE k) ρ = ⋃ n : ℕ, Metric.closedBall 0 (ρ - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Metric.mem_ball, Metric.mem_closedBall, Set.mem_iUnion, dist_zero_right]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hball, Set.image_iUnion]
  refine MeasurableSet.iUnion (fun n => ?_)
  exact ((isCompact_closedBall _ _).image (continuous_opEmap k r T')).isClosed.measurableSet

theorem normSq_sum_eq (k : ℕ) (y : EuclideanSpace ℂ (Fin k)) : ∑ i, Complex.normSq (y i) = ‖y‖ ^ 2 := by

  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl (fun i _ => by rw [Complex.sq_norm])

theorem hypPar_mem (k : ℕ) (T' : ℝ) (hT' : 0 < T') (q : EuclideanSpace ℂ (Fin k) × ℝ) :
    hypPar k T' q ∈ hypS k T' := by

  have h1 : Complex.normSq (Complex.exp (q.2 * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  simp only [hypS, hypPar, Set.mem_setOf_eq]
  rw [normSq_sum_eq, Complex.normSq_mul, Complex.normSq_ofReal, h1, mul_one,
    Real.mul_self_sqrt (by positivity)]
  ring

theorem hypLF : HypLF := by
  intro k T' hT'
  have hcont : Continuous (hypPar k T') := by
    unfold hypPar
    refine (continuous_pi (fun i => ?_)).prodMk ?_
    · exact (EuclideanSpace.proj i).continuous.comp continuous_fst
    · refine (Complex.continuous_ofReal.comp ?_).mul ?_
      · exact Real.continuous_sqrt.comp (((continuous_norm.comp continuous_fst).pow 2).add continuous_const)
      · exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hmeas : Measurable (hypPar k T') := hcont.measurable
  have hSc : IsClosed (hypS k T') := by
    have h1 : Continuous (fun p : (Fin k → ℂ) × ℂ => ∑ i, Complex.normSq (p.1 i) - Complex.normSq p.2) :=
      (continuous_finsetSum _ (fun i _ => Complex.continuous_normSq.comp ((continuous_apply i).comp continuous_fst))).sub
        (Complex.continuous_normSq.comp continuous_snd)
    exact isClosed_eq h1 continuous_const
  constructor
  · unfold hypM
    rw [Measure.smul_apply, Measure.map_apply hmeas hSc.measurableSet.compl]
    have h2 : hypPar k T' ⁻¹' (hypS k T')ᶜ = ∅ := by
      ext q
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
      exact hypPar_mem k T' hT' q
    rw [h2, measure_empty, smul_zero]
  · intro C hC
    obtain ⟨R, hR⟩ := (hC.image continuous_fst).isBounded.exists_norm_le
    have hsub : hypPar k T' ⁻¹' C ⊆
        Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2)) ×ˢ Set.univ := by
      intro q hq
      refine ⟨?_, Set.mem_univ _⟩
      have h1 : ‖(hypPar k T' q).1‖ ≤ R := hR _ ⟨_, hq, rfl⟩
      have h2 : ∀ i, ‖q.1 i‖ ≤ R := fun i => le_trans (norm_le_pi_norm (hypPar k T' q).1 i) h1
      rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖q.1 i‖ ^ 2 ≤ ∑ i : Fin k, R ^ 2 :=
            Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h2 i) 2)
        _ = k * R ^ 2 := by simp
    unfold hypM
    rw [Measure.smul_apply, Measure.map_apply hmeas hC.isClosed.measurableSet, smul_eq_mul]
    refine ENNReal.mul_lt_top (ENNReal.div_lt_top ENNReal.one_ne_top two_ne_zero) ?_
    calc _ ≤ (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))))
          (Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2)) ×ˢ Set.univ) :=
          measure_mono hsub
      _ = volume (Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2))) *
          volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) Set.univ := Measure.prod_prod _ _
      _ < ⊤ := by
        apply ENNReal.mul_lt_top measure_closedBall_lt_top
        rw [Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushQ
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

@[simp] theorem wlp_fst_toLp {α β : Type*} [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (a : α × β) :
    (WithLp.toLp 2 a).fst = a.1 := rfl

@[simp] theorem wlp_snd_toLp {α β : Type*} [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (a : α × β) :
    (WithLp.toLp 2 a).snd = a.2 := rfl

theorem wlp_ext {α β : Type*} [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {p q : WithLp 2 (α × β)}
    (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := by
  cases p
  cases q
  congr 1
  exact Prod.ext h1 h2

def qFw (k : ℕ) (x : TrE k) : WithLp 2 (EuclideanSpace ℂ (Fin k) × ℝ) :=
  WithLp.toLp 2 (WithLp.toLp 2 (fun a => ((x (some (a, false)) : ℂ) + (x (some (a, true)) : ℂ) * Complex.I)),
    x none)

def qBw (k : ℕ) (p : WithLp 2 (EuclideanSpace ℂ (Fin k) × ℝ)) : TrE k :=
  WithLp.toLp 2 (fun o => match o with
    | none => p.snd
    | some (a, b) => if b then (p.fst a).im else (p.fst a).re)

theorem qBw_qFw (k : ℕ) (x : TrE k) : qBw k (qFw k x) = x := by
  ext o
  rcases o with _ | ⟨a, _ | _⟩ <;> simp [qBw, qFw]

theorem qFw_qBw (k : ℕ) (p : WithLp 2 (EuclideanSpace ℂ (Fin k) × ℝ)) : qFw k (qBw k p) = p := by
  refine wlp_ext ?_ ?_
  · ext a
    apply Complex.ext <;> simp [qFw, qBw]
  · simp [qFw, qBw]

theorem qFw_norm_sq (k : ℕ) (x : TrE k) : ‖qFw k x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [qFw, wlp_fst_toLp, wlp_snd_toLp]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [PiLp.toLp_apply, Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs,
    sq_abs, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by ring

def qIso (k : ℕ) : TrE k ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℂ (Fin k) × ℝ) where
  toFun := qFw k
  invFun := qBw k
  map_add' x y := by
    refine wlp_ext ?_ ?_
    · ext a
      apply Complex.ext <;> simp [qFw]
    · simp [qFw]
  map_smul' c x := by
    refine wlp_ext ?_ ?_
    · ext a
      apply Complex.ext <;> simp [qFw]
    · simp [qFw]
  left_inv := qBw_qFw k
  right_inv := qFw_qBw k
  norm_map' x := by
    have h := qFw_norm_sq k x
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem qIso_measurePreserving (k : ℕ) :
    MeasurePreserving (fun x : TrE k => WithLp.ofLp (qFw k x)) volume (volume.prod volume) := by
  exact (WithLp.volume_preserving_ofLp _ _).comp (qIso k).measurePreserving

end PI.RhsWLim.W
end
end

