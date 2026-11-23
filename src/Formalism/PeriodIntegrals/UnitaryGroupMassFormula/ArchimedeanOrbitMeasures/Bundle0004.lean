module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTube

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetMulRCReal
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

section MulR

variable {r m : ℕ}

def mulRC (A : Matrix (Fin m) (Fin m) ℂ) : (Fin r → Fin m → ℂ) →ₗ[ℂ] (Fin r → Fin m → ℂ) :=
  LinearMap.pi fun i => A.vecMulLinear.comp (LinearMap.proj i)

theorem mulRC_apply (A : Matrix (Fin m) (Fin m) ℂ) (Y : Fin r → Fin m → ℂ) :
    mulRC A Y = (Matrix.of Y * A : Matrix (Fin r) (Fin m) ℂ) := by
  ext i j
  simp [mulRC, Matrix.vecMul, Matrix.mul_apply, dotProduct]

theorem det_mulRC (A : Matrix (Fin m) (Fin m) ℂ) : (mulRC (r := r) A).det = A.det ^ r := by
  rw [mulRC, LinearMap.det_pi]
  have h : A.vecMulLinear = Matrix.toLin' Aᵀ := by
    ext v i
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  simp [h, LinearMap.det_toLin', Matrix.det_transpose]

theorem det_mulRC_real (A : Matrix (Fin m) (Fin m) ℂ) :
    ((mulRC (r := r) A).restrictScalars ℝ).det = Complex.normSq A.det ^ r := by
  rw [LinearMap.det_restrictScalars, det_mulRC, map_pow, Algebra.norm_complex_apply]

def reimE : (Fin r → Fin m → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin r × Fin m × Bool) where
  toFun Y := reim (Matrix.of Y)
  invFun y := fun i j => ⟨y (i, j, true), y (i, j, false)⟩
  map_add' Y Z := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
  map_smul' c Y := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
  left_inv Y := by
    funext i j
    apply Complex.ext <;> simp [reim]
  right_inv y := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]

theorem map_mulR (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin r × Fin m × Bool))).map
        (fun y => reim (Matrix.of ((reimE (r := r)).symm y) * A)) =
      ENNReal.ofReal (Complex.normSq A.det ^ r)⁻¹ • volume := by
  set F : EuclideanSpace ℝ (Fin r × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin r × Fin m × Bool) :=
    (reimE (r := r)).toLinearMap ∘ₗ ((mulRC (r := r) A).restrictScalars ℝ) ∘ₗ (reimE (r := r)).symm.toLinearMap
    with hF
  have hdet : F.det = Complex.normSq A.det ^ r := by
    rw [hF, LinearMap.det_conj, det_mulRC_real]
  have hpos : 0 < Complex.normSq A.det ^ r := pow_pos (Complex.normSq_pos.2 hA) _
  have hfun : (fun y => reim (Matrix.of ((reimE (r := r)).symm y) * A)) = F := by
    funext y
    simp only [hF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulRC_apply]
    rfl
  have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin r × Fin m × Bool)))) (f := F) (by rw [hdet]; exact hpos.ne')
  rw [hfun, h, hdet, abs_of_pos (inv_pos.2 hpos)]

def trC {c : ℕ} : (Fin c → Fin m → ℂ) ≃ₗ[ℂ] (Fin m → Fin c → ℂ) where
  toFun Y := fun j i => Y i j
  invFun Z := fun i j => Z j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def mulLC {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin c → ℂ) →ₗ[ℂ] (Fin m → Fin c → ℂ) :=
  (trC (m := m) (c := c)).toLinearMap ∘ₗ mulRC (r := c) Aᵀ ∘ₗ (trC (m := m) (c := c)).symm.toLinearMap

theorem mulLC_apply {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (Y : Fin m → Fin c → ℂ) :
    mulLC A Y = (A * Matrix.of Y : Matrix (Fin m) (Fin c) ℂ) := by
  ext j i
  simp [mulLC, trC, mulRC, Matrix.vecMul, Matrix.mulVec, Matrix.mul_apply, dotProduct, mul_comm]

theorem det_mulLC_real {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    ((mulLC (c := c) A).restrictScalars ℝ).det = Complex.normSq A.det ^ c := by
  rw [LinearMap.det_restrictScalars, mulLC, LinearMap.det_conj, det_mulRC, Matrix.det_transpose, map_pow,
    Algebra.norm_complex_apply]

theorem map_mulL {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin m × Fin c × Bool))).map
        (fun y => reim (A * Matrix.of ((reimE (r := m) (m := c)).symm y))) =
      ENNReal.ofReal (Complex.normSq A.det ^ c)⁻¹ • volume := by
  set F : EuclideanSpace ℝ (Fin m × Fin c × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin c × Bool) :=
    (reimE (r := m) (m := c)).toLinearMap ∘ₗ ((mulLC (c := c) A).restrictScalars ℝ) ∘ₗ
      (reimE (r := m) (m := c)).symm.toLinearMap with hF
  have hdet : F.det = Complex.normSq A.det ^ c := by
    rw [hF, LinearMap.det_conj, det_mulLC_real]
  have hpos : 0 < Complex.normSq A.det ^ c := pow_pos (Complex.normSq_pos.2 hA) _
  have hfun : (fun y => reim (A * Matrix.of ((reimE (r := m) (m := c)).symm y))) = ⇑F := by
    funext y
    simp only [hF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulLC_apply]
    rfl
  have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin m × Fin c × Bool)))) (f := F) (by rw [hdet]; exact hpos.ne')
  rw [hfun, h, hdet, abs_of_pos (inv_pos.2 hpos)]

end MulR

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FourierSD
section
noncomputable section

namespace PI.AprimeInfW.FSD

open MeasureTheory Real Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped FourierTransform RealInnerProductSpace

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem selfDual_lin (A : V ≃L[ℝ] V) (hA : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫) :
    SelfDual (ENNReal.ofReal (Real.sqrt |LinearMap.det (A : V →ₗ[ℝ] V)|) • (volume : Measure V))
      (fun x y => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ)) := by
  set d := LinearMap.det (A : V →ₗ[ℝ] V) with hd_def
  have hd : d ≠ 0 := (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  set c := Real.sqrt |d| with hc_def
  have hc0 : 0 < c := Real.sqrt_pos.2 (abs_pos.2 hd)
  have hcc : c * c = |d| := Real.mul_self_sqrt (abs_nonneg d)
  have hcr : (ENNReal.ofReal c).toReal = c := ENNReal.toReal_ofReal hc0.le
  have hc1 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc0).ne'
  let e : V ≃ᵐ V := A.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = A y := fun _ => rfl
  have hmap : (volume : Measure V).map e = ENNReal.ofReal |d⁻¹| • volume := by
    show (volume : Measure V).map (A : V →ₗ[ℝ] V) = _
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  have hdi : (ENNReal.ofReal |d⁻¹|).toReal = |d|⁻¹ := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  refine ⟨Measure.IsAddHaarMeasure.smul (μ := (volume : Measure V)) hc1 ENNReal.ofReal_ne_top, fun Φ hc hs hI z => ?_⟩
  have hT : ∀ y, ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂(ENNReal.ofReal c • (volume : Measure V)) =
      (c : ℂ) * 𝓕⁻ Φ (A y) := by
    intro y
    rw [integral_smul_measure, hcr, fourierInv_eq, Complex.real_smul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Circle.smul_def, smul_eq_mul]; ring)
  simp only [hT] at hI ⊢

  have hI1 : Integrable (fun y => (c : ℂ) * 𝓕⁻ Φ (A y)) volume :=
    (integrable_smul_measure hc1 ENNReal.ofReal_ne_top).1 hI
  have hI2 : Integrable (fun y => 𝓕⁻ Φ (e y)) volume := by
    have := hI1.const_mul ((c : ℂ)⁻¹)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [he]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hc0.ne'), one_mul]
  have hI3 : Integrable (𝓕⁻ Φ) volume := by
    have h := (integrable_map_equiv e (𝓕⁻ Φ)).2 hI2
    rw [hmap] at h
    exact (integrable_smul_measure (by simp [hd]) ENNReal.ofReal_ne_top).1 h
  have hF : Integrable (𝓕 Φ) volume := by
    have h := hI3.comp_neg
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [fourierInv_eq_fourier_neg, neg_neg]
  have hΦ : Integrable Φ volume := hc.integrable_of_hasCompactSupport hs
  have hinv : 𝓕⁻ (𝓕⁻ Φ) z = Φ (-z) := by
    rw [fourierInv_eq_fourier_neg]
    exact congrFun (hc.fourier_fourierInv_eq hΦ hF) (-z)

  have hout : ∫ y, (c : ℂ) * 𝓕⁻ Φ (A y) * ((𝐞 ⟪y, A z⟫ : Circle) : ℂ) ∂(volume : Measure V) =
      (c : ℂ) * (|d|⁻¹ : ℝ) * 𝓕⁻ (𝓕⁻ Φ) z := by
    have e1 : (fun y => (c : ℂ) * 𝓕⁻ Φ (A y) * ((𝐞 ⟪y, A z⟫ : Circle) : ℂ)) =
        fun y => (c : ℂ) * (((𝐞 ⟪e y, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ (e y)) := by
      funext y
      simp only [he, hA y z]
      ring
    have key : ∫ y, (c : ℂ) * (((𝐞 ⟪e y, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ (e y)) ∂(volume : Measure V) =
        ∫ u, (c : ℂ) * (((𝐞 ⟪u, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ u) ∂((volume : Measure V).map e) :=
      (integral_map_equiv e (fun u => (c : ℂ) * (((𝐞 ⟪u, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ u))).symm
    rw [e1, key, hmap, integral_smul_measure, hdi, integral_const_mul, fourierInv_eq,
      Complex.real_smul]
    simp only [Circle.smul_def, smul_eq_mul]
    push_cast
    ring
  rw [integral_smul_measure, hcr, hout, hinv, Complex.real_smul]
  have : (c : ℂ) * ((c : ℂ) * ((|d|⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [← mul_assoc, ← Complex.ofReal_mul, hcc, ← Complex.ofReal_mul, mul_inv_cancel₀ (abs_pos.2 hd).ne',
      Complex.ofReal_one]
  calc (c : ℂ) * ((c : ℂ) * ((|d|⁻¹ : ℝ) : ℂ) * Φ (-z)) = ((c : ℂ) * ((c : ℂ) * ((|d|⁻¹ : ℝ) : ℂ))) * Φ (-z) := by
        ring
    _ = Φ (-z) := by rw [this, one_mul]

end PI.AprimeInfW.FSD
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpChartC
section
noncomputable section

namespace PI.AprimeInfG

open MeasureTheory Topology Filter Metric Set
open scoped ENNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem tubeChart_of (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → G) (χ : EuclideanSpace ℝ η → H) {r0 : ℝ} (hr0 : 0 < r0)
    (hκc : ContinuousOn κ (ball 0 r0)) (hχc : ContinuousOn χ (ball 0 r0)) (hχi : InjOn χ (ball 0 r0))
    (hinj : ∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r0, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r0,
      (κ a)⁻¹ * κ b ∈ H → a = b)
    (φ : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → G) (U : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ)
    (hφ : ∀ A ⊆ U, MeasurableSet A → μ (φ '' A) = ∫⁻ z in A, ENNReal.ofReal (D z))
    (F : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → EuclideanSpace ℝ ι × EuclideanSpace ℝ η)
    (F' : EuclideanSpace ℝ ι × EuclideanSpace ℝ η →
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ η →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (hF : ∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, HasFDerivWithinAt F (F' p) (ball 0 r0) p)
    (hFi : InjOn F (ball 0 r0)) (hFU : F '' ball 0 r0 ⊆ U)
    (hΦ : ∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, κ p.1 * (χ p.2 : G) = φ (F p))
    (e : EuclideanSpace ℝ η → ℝ)
    (hνH : ∀ s, 0 < s → s ≤ r0 → ν (χ '' ball 0 s) = ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)) :
    TubeChart μ H ν κ χ r0 (fun p => |(F' p).det| * D (F p)) e := by
  have : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : PolishSpace G := PI.AprimeInfA.polish_of_lcsc G
  have hbox : ∀ ρ s, ρ ≤ r0 → s ≤ r0 →
      ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s ⊆
        ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0 := by
    intro ρ s hρ hs p hp
    rw [mem_ball_zero_iff, Prod.norm_def]
    exact max_lt ((mem_ball_zero_iff.1 hp.1).trans_le hρ) ((mem_ball_zero_iff.1 hp.2).trans_le hs)
  have himg : ∀ ρ s, tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s) =
      (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => κ p.1 * (χ p.2 : G)) '' (ball 0 ρ ×ˢ ball 0 s) := by
    intro ρ s
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      exact ⟨κ x, ⟨x, hx, rfl⟩, χ y, ⟨y, hy, rfl⟩, rfl⟩
  have hΦinj : InjOn (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => κ p.1 * (χ p.2 : G))
      (ball 0 r0 ×ˢ ball 0 r0) := by
    intro p hp q hq he
    simp only at he
    have hm : (κ p.1)⁻¹ * κ q.1 ∈ H := by
      have : (κ p.1)⁻¹ * κ q.1 = (χ p.2 : G) * (χ q.2 : G)⁻¹ := by
        calc (κ p.1)⁻¹ * κ q.1 = (κ p.1)⁻¹ * (κ q.1 * (χ q.2 : G)) * (χ q.2 : G)⁻¹ := by group
          _ = (κ p.1)⁻¹ * (κ p.1 * (χ p.2 : G)) * (χ q.2 : G)⁻¹ := by rw [he]
          _ = (χ p.2 : G) * (χ q.2 : G)⁻¹ := by group
      rw [this]
      exact H.mul_mem (χ p.2).2 (H.inv_mem (χ q.2).2)
    have h1 := hinj _ hp.1 _ hq.1 hm
    rw [h1] at he
    have h2 : (χ p.2 : G) = χ q.2 := mul_left_cancel he
    exact Prod.ext h1 (hχi hp.2 hq.2 (Subtype.ext h2))
  refine ⟨hr0, hinj, ?_, ?_, ?_, ?_, hνH⟩
  · intro s hs hsr
    exact measurableSet_ball.image_of_continuousOn_injOn (hχc.mono (ball_subset_ball hsr))
      (hχi.mono (ball_subset_ball hsr))
  · intro ρ s hρ hρr hs hsr
    rw [himg]
    have hsub : ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s ⊆ ball 0 r0 ×ˢ ball 0 r0 :=
      prod_mono (ball_subset_ball hρr) (ball_subset_ball hsr)
    have hc : ContinuousOn (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => κ p.1 * (χ p.2 : G))
        (ball 0 ρ ×ˢ ball 0 s) :=
      (hκc.comp continuousOn_fst fun p (hp : p ∈ ball 0 ρ ×ˢ _) => ball_subset_ball hρr hp.1).mul
        (continuous_subtype_val.comp_continuousOn (hχc.comp continuousOn_snd fun p (hp : p ∈ _ ×ˢ ball 0 s) => ball_subset_ball hsr hp.2))
    exact (measurableSet_ball.prod measurableSet_ball).image_of_continuousOn_injOn hc (hΦinj.mono hsub)
  · intro ρ hρ hρr
    have : PolishSpace (H : Set G) := hH.polishSpace
    have : PolishSpace H := this
    have e1 : tubeS H (κ '' ball 0 ρ) univ =
        (fun p : EuclideanSpace ℝ ι × H => κ p.1 * (p.2 : G)) '' (ball 0 ρ ×ˢ univ) := by
      ext g
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, h, -, rfl⟩
        exact ⟨(x, h), ⟨hx, mem_univ _⟩, rfl⟩
      · rintro ⟨⟨x, h⟩, ⟨hx, -⟩, rfl⟩
        exact ⟨κ x, ⟨x, hx, rfl⟩, h, mem_univ _, rfl⟩
    rw [e1]
    have hc : ContinuousOn (fun p : EuclideanSpace ℝ ι × H => κ p.1 * (p.2 : G)) (ball 0 ρ ×ˢ univ) :=
      (hκc.comp continuousOn_fst fun p (hp : p ∈ ball 0 ρ ×ˢ _) => ball_subset_ball hρr hp.1).mul
        (continuous_subtype_val.comp continuous_snd).continuousOn
    have hi : InjOn (fun p : EuclideanSpace ℝ ι × H => κ p.1 * (p.2 : G)) (ball 0 ρ ×ˢ univ) := by
      intro p hp q hq he
      simp only at he
      have hm : (κ p.1)⁻¹ * κ q.1 ∈ H := by
        have : (κ p.1)⁻¹ * κ q.1 = (p.2 : G) * (q.2 : G)⁻¹ := by
          calc (κ p.1)⁻¹ * κ q.1 = (κ p.1)⁻¹ * (κ q.1 * (q.2 : G)) * (q.2 : G)⁻¹ := by group
            _ = (κ p.1)⁻¹ * (κ p.1 * (p.2 : G)) * (q.2 : G)⁻¹ := by rw [he]
            _ = (p.2 : G) * (q.2 : G)⁻¹ := by group
        rw [this]
        exact H.mul_mem p.2.2 (H.inv_mem q.2.2)
      have h1 := hinj _ (ball_subset_ball hρr hp.1) _ (ball_subset_ball hρr hq.1) hm
      rw [h1] at he
      have h2 : (p.2 : G) = q.2 := mul_left_cancel he
      exact Prod.ext h1 (Subtype.ext h2)
    exact (measurableSet_ball.prod MeasurableSet.univ).image_of_continuousOn_injOn hc hi
  · intro ρ s hρ hρr hs hsr
    have hB := hbox ρ s hρr hsr
    have hBm : MeasurableSet (ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s) :=
      measurableSet_ball.prod measurableSet_ball
    have hF2 : ∀ p ∈ ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s,
        HasFDerivWithinAt F (F' p) (ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s) p :=
      fun p hp => (hF p (hB hp)).mono hB
    have e2 : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => κ p.1 * (χ p.2 : G)) ''
        (ball 0 ρ ×ˢ ball 0 s) = φ '' (F '' (ball 0 ρ ×ˢ ball 0 s)) := by
      rw [image_image]
      exact image_congr fun p hp => hΦ p (hB hp)
    rw [himg, e2, hφ _ ((image_mono hB).trans hFU) (measurable_image_of_fderivWithin hBm hF2 (hFi.mono hB)),
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hBm hF2 (hFi.mono hB)]
    simp_rw [ENNReal.ofReal_mul (abs_nonneg _)]

theorem contAt_dens {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {F : P → P} {F' : P → (P →L[ℝ] P)}
    {D : P → ℝ} (hF : ContinuousAt F 0) (hdet : ContinuousAt (fun p => |(F' p).det|) 0) (hD : ContinuousAt D (F 0)) :
    ContinuousAt (fun p => |(F' p).det| * D (F p)) 0 :=
  hdet.mul (ContinuousAt.comp (g := D) hD hF)

end PI.AprimeInfG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Upq
section
noncomputable section

open Matrix TensorProduct

namespace HcS.UG

section Group

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix n n A) = 1 := by
  simp [cT, Matrix.map_one]

def UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = cT σ (b : Matrix n n A) * (cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

end Group

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

def Upq (p q : ℕ) : Subgroup (GL (Fin p ⊕ Fin q) ℂ) := UJ (starRingEnd ℂ) (Jpq p q)

end Points

section Split

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

end Split

section Abstract

variable {G : Type} [Group G]

end Abstract

section Tj

variable {L : Type} [Field L]

end Tj

section Coeff

variable (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]

end Coeff

section More

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

end More

open NumberField IsDedekindDomain

end HcS.UG
end
end

