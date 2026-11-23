module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ChartLim
section
noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace PI.RhsWLim.W

theorem chartLim : ChartLim := by
  intro E _ _ _ _ _ _ X _ Φ ν δ hδ hδ0 hν
  obtain ⟨ε0, hε0, hν⟩ := hν
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have he : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  have hnhds : Set.Icc (δ 0 - ENNReal.ofReal (ε / 2)) (δ 0 + ENNReal.ofReal (ε / 2)) ∈ 𝓝 (δ 0) :=
    ENNReal.Icc_mem_nhds hδ0 he.ne'
  obtain ⟨η1, hη1, hball⟩ := Metric.mem_nhds_iff.mp (hδ hnhds)
  refine ⟨min η1 ε0, lt_min hη1 hε0, fun {ρ} hρ hdist => ?_⟩
  have hρ0 : 0 < ρ := Set.mem_Ioi.mp hρ
  have hρ' : ρ < min η1 ε0 := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hρ0] at hdist
  have hρη : ρ < η1 := lt_of_lt_of_le hρ' (min_le_left _ _)
  have hρε : ρ < ε0 := lt_of_lt_of_le hρ' (min_le_right _ _)
  have hV0 : volume (Metric.ball (0 : E) ρ) ≠ 0 := (Metric.measure_ball_pos volume (0 : E) hρ0).ne'
  have hVt : volume (Metric.ball (0 : E) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hbd : ∀ x ∈ Metric.ball (0 : E) ρ,
      δ x ∈ Set.Icc (δ 0 - ENNReal.ofReal (ε / 2)) (δ 0 + ENNReal.ofReal (ε / 2)) :=
    fun x hx => hball (Metric.ball_subset_ball hρη.le hx)
  have hup : ∫⁻ x in Metric.ball (0 : E) ρ, δ x ≤
      (δ 0 + ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ) := by
    calc ∫⁻ x in Metric.ball (0 : E) ρ, δ x
        ≤ ∫⁻ _ in Metric.ball (0 : E) ρ, (δ 0 + ENNReal.ofReal (ε / 2)) :=
          setLIntegral_mono' measurableSet_ball fun x hx => (hbd x hx).2
      _ = (δ 0 + ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ) := setLIntegral_const _ _
  have hlo : (δ 0 - ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ) ≤
      ∫⁻ x in Metric.ball (0 : E) ρ, δ x := by
    calc (δ 0 - ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ)
        = ∫⁻ _ in Metric.ball (0 : E) ρ, (δ 0 - ENNReal.ofReal (ε / 2)) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in Metric.ball (0 : E) ρ, δ x :=
          setLIntegral_mono' measurableSet_ball fun x hx => (hbd x hx).1
  have htop1 : δ 0 + ENNReal.ofReal (ε / 2) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hδ0, ENNReal.ofReal_ne_top⟩
  have hAt : ∫⁻ x in Metric.ball (0 : E) ρ, δ x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top htop1 hVt) hup
  have hVr : 0 < (volume (Metric.ball (0 : E) ρ)).toReal := ENNReal.toReal_pos hV0 hVt
  have hupR : (∫⁻ x in Metric.ball (0 : E) ρ, δ x).toReal ≤
      ((δ 0).toReal + ε / 2) * (volume (Metric.ball (0 : E) ρ)).toReal := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top htop1 hVt) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add hδ0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at h1
  have hloR : ((δ 0).toReal - ε / 2) * (volume (Metric.ball (0 : E) ρ)).toReal ≤
      (∫⁻ x in Metric.ball (0 : E) ρ, δ x).toReal := by
    have h1 := ENNReal.toReal_mono hAt hlo
    rw [ENNReal.toReal_mul] at h1
    have h2 : (δ 0).toReal - ε / 2 ≤ (δ 0 - ENNReal.ofReal (ε / 2)).toReal := by
      have h3 := ENNReal.le_toReal_sub (a := δ 0) (b := ENNReal.ofReal (ε / 2)) ENNReal.ofReal_ne_top
      rwa [ENNReal.toReal_ofReal (by linarith)] at h3
    exact le_trans (mul_le_mul_of_nonneg_right h2 hVr.le) h1
  have h4 := (div_le_iff₀ hVr).mpr hupR
  have h5 := (le_div_iff₀ hVr).mpr hloR
  rw [hν ρ hρ0 hρε, Real.dist_eq, abs_lt]
  constructor <;> linarith

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

def opBase (k r : ℕ) (T' : ℝ) : Fin (2 * r + k + 1) → ℂ := (Real.sqrt T' : ℂ) • wLast k r

def opCo (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : (Fin k → ℂ) × ℂ :=
  (fun i => v (wI k r (Fin.castSucc i)), v (wI k r (Fin.last k)))

def opOrb (k r : ℕ) (T' : ℝ) (x : Mt k r) : (Fin k → ℂ) × ℂ := opCo k r (Matrix.of x *ᵥ opBase k r T')

def opVec (k r : ℕ) (p : (Fin k → ℂ) × ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val < r + k then p.1 ⟨i.val - r, by omega⟩
  else if i.val = r + k then p.2 else 0

def opAct (k r : ℕ) (s : Mat k r) (p : (Fin k → ℂ) × ℂ) : (Fin k → ℂ) × ℂ := opCo k r (s *ᵥ opVec k r p)

def hypS (k : ℕ) (T' : ℝ) : Set ((Fin k → ℂ) × ℂ) :=
  {p | ∑ i, Complex.normSq (p.1 i) - Complex.normSq p.2 = -T'}

def hypPar (k : ℕ) (T' : ℝ) (q : EuclideanSpace ℂ (Fin k) × ℝ) : (Fin k → ℂ) × ℂ :=
  (fun i => q.1 i, (Real.sqrt (‖q.1‖ ^ 2 + T') : ℂ) * Complex.exp (q.2 * Complex.I))

def hypM (k : ℕ) (T' : ℝ) : Measure ((Fin k → ℂ) × ℂ) :=
  (1 / 2 : ℝ≥0∞) • (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))).map (hypPar k T')

abbrev TrE (k : ℕ) := EuclideanSpace ℝ (Option (Fin k × Bool))

def opBeta (k : ℕ) (q : TrE k) (a : Fin k) : ℂ :=
  ((q (some (a, false)) : ℂ) + (q (some (a, true)) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)

def opGen (k r : ℕ) (q : TrE k) : Mat k r := fun i j =>
  if hi : r ≤ i.val ∧ i.val < r + k then (if j.val = r + k then opBeta k q ⟨i.val - r, by omega⟩ else 0)
  else if i.val = r + k then
    (if hj : r ≤ j.val ∧ j.val < r + k then star (opBeta k q ⟨j.val - r, by omega⟩)
     else if j.val = r + k then (q none : ℂ) * Complex.I else 0)
  else 0

def opE (k r : ℕ) (T' : ℝ) (ρ : ℝ) : Set ((Fin k → ℂ) × ℂ) :=
  (fun q : TrE k => opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) '' Metric.ball 0 ρ

def tVol (k : ℕ) (ρ : ℝ) : ℝ := (volume (Metric.ball (0 : TrE k) ρ)).toReal

def HypInv : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ s ∈ UWb k r, (hypM k T').map (opAct k r s) = hypM k T'

def OrbRepY : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ Q : Measure ((Fin k → ℂ) × ℂ), (∀ s ∈ UWb k r, Q.map (opAct k r s) = Q) → Q (hypS k T')ᶜ = 0 →
      (∀ C, IsCompact C → Q C < ⊤) → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ Q = c • νg.map (opOrb k r T')

def GaugeK : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ νK : Measure (Mt k r), IsGaugeOn k r (UWset k r (wLast k r)) νK

def TubeLimK : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ νg νK : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    IsGaugeOn k r (UWset k r (wLast k r)) νK →
    Tendsto (fun ρ : ℝ => (νg (opOrb k r T' ⁻¹' opE k r T' ρ)).toReal / tVol k ρ) (𝓝[>] 0)
      (𝓝 (νK Set.univ).toReal)

def HypLocal : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' →
    Tendsto (fun ρ : ℝ => (hypM k T' (opE k r T' ρ)).toReal / tVol k ρ) (𝓝[>] 0) (𝓝 (T' ^ k / 2 ^ (k + 1)))

def OpEMeas : Prop :=
  ∀ (k r : ℕ) (T' : ℝ) (ρ : ℝ), MeasurableSet (opE k r T' ρ)

def HypLF : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → hypM k T' (hypS k T')ᶜ = 0 ∧ ∀ C, IsCompact C → hypM k T' C < ⊤

theorem op_volU_pos (j : ℕ) : 0 < volU j :=
  Finset.prod_pos fun i _ => div_pos (pow_pos (by positivity) _) (Nat.cast_pos.mpr (Nat.factorial_pos i))

theorem continuous_opOrb (T' : ℝ) : Continuous (opOrb k r T') := by
  have h : Continuous fun x : PI.RhsWLim.Mt k r => Matrix.of x *ᵥ opBase k r T' :=
    Continuous.matrix_mulVec (by exact continuous_id) continuous_const
  unfold opOrb opCo
  exact (continuous_pi fun i => (continuous_apply (PI.RhsWLim.wI k r (Fin.castSucc i))).comp h).prodMk
    ((continuous_apply (PI.RhsWLim.wI k r (Fin.last k))).comp h)

theorem continuous_hypPar (k : ℕ) (T' : ℝ) : Continuous (hypPar k T') := by
  unfold hypPar
  fun_prop

theorem hypMeas_eq (k : ℕ) (T' : ℝ) {f : (Fin k → ℂ) × ℂ → ℝ≥0∞} (hf : Measurable f) :
    hypMeas k T' f = ∫⁻ p, f p ∂hypM k T' := by
  have hm : Measurable (hypPar k T') := (continuous_hypPar k T').measurable
  unfold hypM hypMeas
  rw [lintegral_smul_measure, smul_eq_mul, lintegral_map hf hm,
    lintegral_prod (fun a => f (hypPar k T' a)) (hf.comp hm).aemeasurable]
  rfl

theorem orbitPush_of (h2 : GaugeVolUk) (hK : GaugeK) (hT : TubeLimK) (hI : HypInv) (hR : OrbRepY)
    (hL : HypLocal) (hE : OpEMeas) (hF : HypLF) : OrbitPush := by
  intro k r T' hk hT' νg hνg f hf
  obtain ⟨νK, hνK⟩ := hK k r hk
  obtain ⟨c, hctop, hc⟩ := hR k r T' hk hT' νg hνg (hypM k T')
    (hI k r T' hk hT') (hF k T' hT').1 (hF k T' hT').2
  have hmeas : Measurable (opOrb k r T') := (continuous_opOrb T').measurable
  have hU : 0 < PI.RhsWLim.volU k := op_volU_pos k
  have hK1 : (νK Set.univ).toReal = PI.RhsWLim.volU k := by
    rw [h2 k r νK hνK, ENNReal.toReal_ofReal hU.le]
  have hlim1 := hT k r T' hk hT' νg νK hνg hνK
  rw [hK1] at hlim1
  have hlim2 := hL k r T' hk hT'
  have heqfun : (fun ρ : ℝ => (hypM k T' (opE k r T' ρ)).toReal / tVol k ρ) =
      fun ρ => c.toReal * ((νg (opOrb k r T' ⁻¹' opE k r T' ρ)).toReal / tVol k ρ) := by
    funext ρ
    rw [hc, smul_apply, Measure.map_apply hmeas (hE k r T' ρ), smul_eq_mul, ENNReal.toReal_mul,
      mul_div_assoc]
  rw [heqfun] at hlim2
  have hkey : T' ^ k / 2 ^ (k + 1) = c.toReal * PI.RhsWLim.volU k :=
    tendsto_nhds_unique hlim2 (hlim1.const_mul c.toReal)
  have hRHS : hypMeas k T' f = c * ∫⁻ p, f p ∂(νg.map (opOrb k r T')) := by
    rw [hypMeas_eq k T' hf, hc, lintegral_smul_measure, smul_eq_mul]
  show ∫⁻ x, f (opOrb k r T' x) ∂νg = _
  rw [← lintegral_map hf hmeas, hRHS, ← mul_assoc]
  have hX : PI.RhsWLim.volU k * 2 ^ (k + 1) / T' ^ k * c.toReal = 1 := by
    have hT'k : (0 : ℝ) < T' ^ k := pow_pos hT' k
    rw [show PI.RhsWLim.volU k * 2 ^ (k + 1) / T' ^ k * c.toReal =
        2 ^ (k + 1) / T' ^ k * (c.toReal * PI.RhsWLim.volU k) by ring, ← hkey]
    field_simp
  have hcc : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
  rw [hcc, ← ENNReal.ofReal_mul (div_pos (mul_pos hU (by positivity)) (pow_pos hT' k)).le, hX,
    ENNReal.ofReal_one, one_mul]

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWLimOf
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem rhsWLim_of (hM : MBaseMem) (hB : TBallMeas) (hG : GaugeExists) (hR : RhsHaar) (hU : HaarUniq)
    (hC : ConstVal) : RhsWLim := by
  intro k r z z' μW μW' a a' μsec hD
  have hk := hD.k_pos
  obtain ⟨νg, hνg, ⟨ε, hε, hpos⟩, hlim⟩ := hG k r hk
  obtain ⟨ν, hν, ⟨ε', hε', hfin⟩, hrep⟩ := hR k r z z' μW μW' a a' μsec hD
  obtain ⟨c, hc, hνc⟩ := hU k r ν νg hk hν hνg ⟨min ε ε', lt_min hε hε', fun ρ h0 hlt =>
    ⟨hfin ρ h0 (lt_of_lt_of_le hlt (min_le_right _ _)),
     (hpos ρ h0 (lt_of_lt_of_le hlt (min_le_left _ _))).1,
     (hpos ρ h0 (lt_of_lt_of_le hlt (min_le_left _ _))).2⟩⟩
  have hrep' : ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      rhsW k r z z' μW μW' μsec φ = c * ∫⁻ x, φ x ∂νg := by
    intro φ hφ
    rw [hrep φ hφ, hνc, lintegral_smul_measure, smul_eq_mul]
  have hcv := hC k r z z' μW μW' a a' μsec hD νg c hνg hlim hrep'
  have hm := hM k r z z' μW μW' a a' μsec hD
  have hmeas : ∀ ρ, MeasurableSet (mBall k r z z' μsec ρ) := fun ρ => hB k r (mBase k r z z' μsec) ρ
  have heq : ∀ ρ, (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ
      = c.toReal * ((νg (tBall k r (mBase k r z z' μsec) ρ)).toReal / bVol k r ρ) := by
    intro ρ
    rw [hrep' _ (measurable_one.indicator (hmeas ρ)), lintegral_indicator_one (hmeas ρ),
      ENNReal.toReal_mul, mul_div_assoc]
    all_goals rfl
  refine (tendsto_congr heq).2 ?_
  rw [← hcv]
  have := (hlim _ hm).const_mul c.toReal
  rw [mul_one] at this
  exact this

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem continuous_expChart (k r : ℕ) (S : Set (Mat k r)) :
    Continuous (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) i j :
        lieE S → Mt k r) := by
  set n := 2 * r + k + 1
  have hexp : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp A) := by
    let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    have : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ) PseudoMetricSpace.toUniformSpace := by
      let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
      exact FiniteDimensional.complete ℂ _
    let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra (R := ℚ)
    exact NormedSpace.exp_continuous
  have hun : Continuous (fun x : EuclideanSpace ℝ (Fin n × Fin n × Bool) => unrealify x) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hmk : Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := Complex.equivRealProdCLM.symm.continuous
    show Continuous (fun x : EuclideanSpace ℝ (Fin n × Fin n × Bool) => (⟨x (i, j, false), x (i, j, true)⟩ : ℂ))
    exact hmk.comp ((PiLp.continuous_apply 2 (fun _ : Fin n × Fin n × Bool => ℝ) (i, j, false)).prodMk
      (PiLp.continuous_apply 2 (fun _ : Fin n × Fin n × Bool => ℝ) (i, j, true)))
  have hall : Continuous (fun x : lieE S =>
      NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) :=
    (hexp.comp hun).comp continuous_subtype_val
  exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hall)

theorem measurableSet_expBall (k r : ℕ) (S : Set (Mat k r)) (ρ : ℝ) :
    MeasurableSet (expBall (k := k) (r := r) S ρ) := by
  have hball : IsSigmaCompact (Metric.ball (0 : lieE S) ρ) :=
    isSigmaCompact_iff_sigmaCompactSpace.2
      (haveI : LocallyCompactSpace (Metric.ball (0 : lieE S) ρ) := Metric.isOpen_ball.locallyCompactSpace
       inferInstance)
  obtain ⟨K, hK, hKU⟩ := hball.image (continuous_expChart k r S)
  unfold expBall
  rw [← hKU]
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

theorem tBallMeas : TBallMeas := by
  intro k r m ρ
  have hc : Continuous (fun x : Mt k r => fun i j => (m⁻¹ * Matrix.of x) i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact (measurableSet_expBall (k := k) (r := r) (UWb k r) ρ).preimage hc.measurable

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolURatio
section
noncomputable section

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem volURatio : VolURatio := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [volU, Finset.prod_range_succ, Nat.add_sub_cancel]
  ring

end PI.RhsWLim.W
end
end

