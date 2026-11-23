module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffOnFubiniStudyProfileInvNormSqFirst
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory OnePoint Filter Topology

noncomputable section

def p1Re : (Fin 1 → ℂ) →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)

def p1Im : (Fin 1 → ℂ) →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)

@[simp] theorem rea_apply (w : Fin 1 → ℂ) : p1Re w = (w 0).re := rfl
@[simp] theorem ima_apply (w : Fin 1 → ℂ) : p1Im w = (w 0).im := rfl

def projectiveLineNormSqDerivative : (Fin 1 → ℂ) →L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ) :=
  (2 : ℝ) • (p1Re.smulRight p1Re + p1Im.smulRight p1Im)

theorem dNormSq_apply (w v : Fin 1 → ℂ) :
    projectiveLineNormSqDerivative w v = 2 * ((w 0).re * (v 0).re + (w 0).im * (v 0).im) := by
  simp only [projectiveLineNormSqDerivative, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, rea_apply, ima_apply, smul_eq_mul]

theorem projLine_norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
  rw [Complex.sq_norm, Complex.normSq_apply]

theorem projLine_hasFDerivAt_normSq (w : Fin 1 → ℂ) :
    HasFDerivAt (fun w : Fin 1 → ℂ => ‖w 0‖ ^ 2) (projectiveLineNormSqDerivative w) w := by
  have h : (fun w : Fin 1 → ℂ => ‖w 0‖ ^ 2) = fun w => p1Re w * p1Re w + p1Im w * p1Im w := by
    funext w
    rw [projLine_norm_sq_eq]
    rfl
  rw [h]
  have h2 : HasFDerivAt (fun w => p1Re w * p1Re w + p1Im w * p1Im w)
      ((p1Re w • p1Re + p1Re w • p1Re) + (p1Im w • p1Im + p1Im w • p1Im)) w :=
    (p1Re.hasFDerivAt.mul p1Re.hasFDerivAt).add (p1Im.hasFDerivAt.mul p1Im.hasFDerivAt)
  convert h2 using 1
  ext v
  rw [dNormSq_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, rea_apply,
    ima_apply]
  ring

theorem projLine_continuous_normSq : Continuous (fun w : Fin 1 → ℂ => ‖w 0‖ ^ 2) := (continuous_norm.comp (continuous_apply 0)).pow 2

theorem projLine_leviForm_radial {F : (Fin 1 → ℂ) → ℝ} {G G' : ℝ → ℝ} {G'' : ℝ} {y : Fin 1 → ℂ}
    (hF : ∀ᶠ w in 𝓝 y, F w = G (‖w 0‖ ^ 2))
    (hG : ∀ᶠ t in 𝓝 (‖y 0‖ ^ 2), HasDerivAt G (G' t) t)
    (hG' : HasDerivAt G' G'' (‖y 0‖ ^ 2)) (v : Fin 1 → ℂ) :
    levi F y v = (G'' * ‖y 0‖ ^ 2 + G' (‖y 0‖ ^ 2)) * ‖v 0‖ ^ 2 := by
  have hqd : ∀ w : Fin 1 → ℂ, HasFDerivAt (fun w : Fin 1 → ℂ => ‖w 0‖ ^ 2) (projectiveLineNormSqDerivative w) w :=
    projLine_hasFDerivAt_normSq
  have hev : ∀ᶠ w in 𝓝 y, HasFDerivAt F (G' (‖w 0‖ ^ 2) • projectiveLineNormSqDerivative w) w := by
    have h1 : ∀ᶠ w in 𝓝 y, ∀ᶠ z in 𝓝 w, F z = G (‖z 0‖ ^ 2) := hF.eventually_nhds
    have h2 : ∀ᶠ w in 𝓝 y, HasDerivAt G (G' (‖w 0‖ ^ 2)) (‖w 0‖ ^ 2) :=
      (projLine_continuous_normSq.tendsto y).eventually hG
    filter_upwards [h1, h2] with w hw1 hw2
    exact (hw2.comp_hasFDerivAt w (hqd w)).congr_of_eventuallyEq hw1
  have hfd : fderiv ℝ F =ᶠ[𝓝 y] fun w => G' (‖w 0‖ ^ 2) • projectiveLineNormSqDerivative w :=
    hev.mono fun w hw => hw.fderiv
  have hc : HasFDerivAt (fun w : Fin 1 → ℂ => G' (‖w 0‖ ^ 2)) (G'' • projectiveLineNormSqDerivative y) y :=
    hG'.comp_hasFDerivAt y (hqd y)
  have hL : HasFDerivAt (fun w : Fin 1 → ℂ => projectiveLineNormSqDerivative w) projectiveLineNormSqDerivative y := projectiveLineNormSqDerivative.hasFDerivAt
  have h2 := (hc.smul hL).congr_of_eventuallyEq hfd
  rw [levi, h2.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, dNormSq_apply, Pi.smul_apply, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [projLine_norm_sq_eq (y 0), projLine_norm_sq_eq (v 0)]
  ring

open scoped Classical in
theorem continuous_chart1_inv :
    Continuous (fun w : Fin 1 → ℂ => if w 0 = 0 then (∞ : OnePoint ℂ) else (((w 0)⁻¹ : ℂ) : OnePoint ℂ)) := by
  set g : ℂ → OnePoint ℂ := fun z => if z = 0 then (∞ : OnePoint ℂ) else ((z⁻¹ : ℂ) : OnePoint ℂ)
    with hg_def
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      have hf0 : g 0 = ∞ := by simp [hg_def]
      show Tendsto g (𝓝 0) (𝓝 (g 0))
      rw [← nhdsNE_sup_pure (0 : ℂ)]
      refine Tendsto.sup ?_ (tendsto_pure_nhds g 0)
      have h1 : Tendsto (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 ∞) := by
        refine OnePoint.tendsto_coe_infty.comp ?_
        rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
        exact Filter.tendsto_inv₀_nhdsNE_zero
      rw [hf0]
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w ≠ 0 := hw
      simp [hg_def, hw']
    · have h1 : ContinuousAt (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) z :=
        OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)
      refine h1.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      simp [hg_def, hw]
  exact hg.comp (continuous_apply 0)

theorem projLine_analyticAt_apply_zero (w : Fin 1 → ℂ) : AnalyticAt ℂ (fun w : Fin 1 → ℂ => w 0) w := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt w

theorem projLine_analyticAt_inv_apply_zero {w : Fin 1 → ℂ} (hw : w 0 ≠ 0) :
    AnalyticAt ℂ (fun w : Fin 1 → ℂ => (w 0)⁻¹) w := (projLine_analyticAt_apply_zero w).inv hw

theorem projLine_analyticAt_const_apply_zero (w : Fin 1 → ℂ) :
    AnalyticAt ℂ (fun w : Fin 1 → ℂ => fun _ : Fin 1 => w 0) w := AnalyticAt.pi fun _ => projLine_analyticAt_apply_zero w

theorem projLine_analyticAt_const_inv_apply_zero {w : Fin 1 → ℂ} (hw : w 0 ≠ 0) :
    AnalyticAt ℂ (fun w : Fin 1 → ℂ => fun _ : Fin 1 => (w 0)⁻¹) w := AnalyticAt.pi fun _ => projLine_analyticAt_inv_apply_zero hw

def fubiniStudyProfile (t : ℝ) : ℝ := (1 / 2) * Real.log (1 + t)
def fubiniStudyProfileInv (t : ℝ) : ℝ := (1 / 2) * Real.log (1 + t⁻¹)
def fsQ (w : Fin 1 → ℂ) : ℝ := ‖w 0‖ ^ 2

theorem contDiff_fsQ : ContDiff ℝ (⊤ : ℕ∞) fsQ := (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) 0)

theorem contDiff_fubiniStudyProfile_normSqFirst : ContDiff ℝ (⊤ : ℕ∞) (fun w => fubiniStudyProfile (fsQ w)) := by
  unfold fubiniStudyProfile
  refine contDiff_const.mul ((contDiff_const.add contDiff_fsQ).log fun w => ?_)
  have h0 : 0 ≤ fsQ w := by unfold fsQ; positivity
  exact ne_of_gt (by linarith)

theorem contDiffOn_fubiniStudyProfileInv_normSqFirst : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => fubiniStudyProfileInv (fsQ w)) {w | w 0 ≠ 0} := by
  unfold fubiniStudyProfileInv
  have hne : ∀ w ∈ {w : Fin 1 → ℂ | w 0 ≠ 0}, fsQ w ≠ 0 := by
    intro w hw
    unfold fsQ
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  refine contDiffOn_const.mul ((contDiffOn_const.add (contDiff_fsQ.contDiffOn.inv hne)).log ?_)
  intro w hw
  have h0 : 0 ≤ (fsQ w)⁻¹ := by unfold fsQ; positivity
  show 1 + (fsQ w)⁻¹ ≠ 0
  exact ne_of_gt (by linarith)

theorem projLine_continuous_of_smooth {e : ℕ} {X : Type*} [TopologicalSpace X]
    (A : FinHolAtlas e X) {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have hf' : A.SmoothOn Set.univ f := hf
  have hc : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    have h0 := (hf' j).continuousOn
    simpa using h0
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    hc.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem hasDerivAt_fubiniStudyProfile {t : ℝ} (ht : -1 < t) : HasDerivAt fubiniStudyProfile ((1 / 2) * (1 + t)⁻¹) t := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
  have h2 := (h1.log (ne_of_gt (by linarith))).const_mul (1 / 2 : ℝ)
  exact h2.congr_deriv (by simp only [one_div])

theorem hasDerivAt_fubiniStudyProfileInv {t : ℝ} (ht : 0 < t) :
    HasDerivAt fubiniStudyProfileInv (-(1 / 2) * (t * (t + 1))⁻¹) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have ht1 : t + 1 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => 1 + x⁻¹) (-(t ^ 2)⁻¹) t := (hasDerivAt_inv ht0).const_add 1
  have hne : 1 + t⁻¹ ≠ 0 := by positivity
  have h2 := (h1.log hne).const_mul (1 / 2 : ℝ)
  refine h2.congr_deriv ?_
  field_simp

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas

noncomputable section

def IsPotentialAddStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P Q : LocPot X),
    IsPotential A P → IsPotential A Q → IsPotential A (P + Q)

def IsPotentialZsmulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (m : ℤ) (P : LocPot X),
    IsPotential A P → IsPotential A (P.zsmul m)

def IsPotentialPullbackStatement : Prop :=
  ∀ {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X)
    (B : FinHolAtlas e' Y) (h : Y → X) (hh : HoloMap B A h) (P : LocPot X),
    IsPotential A P → IsPotential B (P.pullback h hh.1)

def IsPotentialRsmulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ) (P : LocPot X),
    IsPotential A P → IsPotential A (P.rsmul c)

def IsPshRsmulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ) (P : LocPot X),
    0 ≤ c → IsPotential A P → IsPsh A P → IsPsh A (P.rsmul c)

def PshShiftStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Ω : LocPot X), IsPotential A Ω → IsPosPot A Ω → ∀ w : X → ℝ, A.Smooth w →
      ∃ C : ℝ, IsPsh A (LocPot.ofFun w + Ω.rsmul C)

def SNCInducedAtlasStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (W : Fin r → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
      ∀ k, ∃ B : FinHolAtlas e (W k), HoloMap B A Subtype.val

def IsPshAddStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P Q : LocPot X),
    IsPotential A P → IsPotential A Q → IsPsh A P → IsPsh A Q → IsPsh A (P + Q)

def ExistsPartitionStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X),
    Nonempty (ChartPartition A)

def LocDensBaseStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → ∀ j, ∀ y ∈ (A.chart j).target, ∀ x : Fin e → X,
      (∀ i, (A.chart j).symm y ∈ (Φ i).U (x i)) →
      locDens A Φ j y = maDens (fun i y' => (Φ i).φ (x i) ((A.chart j).symm y')) y

def LocDensContStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → ∀ j, ContinuousOn (locDens A Φ j) (A.chart j).target

def LocDensChartStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → ∀ j k, ∀ y ∈ (A.chart j).target,
      (A.chart j).symm y ∈ (A.chart k).source →
      locDens A Φ j y = locDens A Φ k (A.chart k ((A.chart j).symm y)) *
        ‖LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2

def IntegralWithIndepStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P Q : ChartPartition A) (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    ∀ g : X → ℝ, MIntegrable A Φ g → integralWith A P Φ g = integralWith A Q Φ g

def MIntEqStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    ∀ g : X → ℝ, MIntegrable A Φ g → mInt A Φ g = integralWith A P Φ g

def MIntAtlasIndepStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A B : FinHolAtlas e X), A.Compatible B → ∀ Φ : Fin e → LocPot X,
    (∀ i, IsPotential A (Φ i)) → ∀ g : X → ℝ, MIntegrable A Φ g →
      MIntegrable B Φ g ∧ mInt A Φ g = mInt B Φ g

def MIntegrableContStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → ∀ g : X → ℝ, Continuous g → MIntegrable A Φ g

def MIntSymmStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (σ : Equiv.Perm (Fin e)) (g : X → ℝ), mInt A (Φ ∘ σ) g = mInt A Φ g

def MIntAddStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (P Q : LocPot X) (Φ : Fin e → LocPot X),
    IsPotential A P → IsPotential A Q → (∀ i, IsPotential A (Φ i)) → ∀ g : X → ℝ,
    MIntegrable A (Fin.cons P Φ) g → MIntegrable A (Fin.cons Q Φ) g →
      mInt A (Fin.cons (P + Q) Φ) g = mInt A (Fin.cons P Φ) g + mInt A (Fin.cons Q Φ) g

def MIntZsmulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X) (m : ℤ)
    (P : LocPot X) (Φ : Fin e → LocPot X), IsPotential A P → (∀ i, IsPotential A (Φ i)) →
    ∀ g : X → ℝ, mInt A (Fin.cons (P.zsmul m) Φ) g = m * mInt A (Fin.cons P Φ) g

def MIntRsmulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X) (c : ℝ)
    (P : LocPot X) (Φ : Fin e → LocPot X), IsPotential A P → (∀ i, IsPotential A (Φ i)) →
    ∀ g : X → ℝ, mInt A (Fin.cons (P.rsmul c) Φ) g = c * mInt A (Fin.cons P Φ) g

def MIntLinearStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) → ∀ (c : ℝ) (g g' : X → ℝ),
    MIntegrable A Φ g → MIntegrable A Φ g' →
      mInt A Φ (fun x => c * g x + g' x) = c * mInt A Φ g + mInt A Φ g'

def MIntNonnegStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → (∀ i, IsPsh A (Φ i)) → ∀ g : X → ℝ, (∀ x, 0 ≤ g x) →
      0 ≤ mInt A Φ g

def MaMeasureStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    (∀ i, IsPsh A (Φ i)) → IsFiniteMeasure (maMeasure A Φ) ∧
      ∀ g : X → ℝ, Measurable g → (MIntegrable A Φ g ↔ Integrable g (maMeasure A Φ)) ∧
        (MIntegrable A Φ g → mInt A Φ g = ∫ x, g x ∂maMeasure A Φ)

def MaMeasureMonoStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : FinHolAtlas e X) (Φ Θ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    (∀ i, IsPsh A (Φ i)) → (∀ i, IsPotential A (Θ i)) → (∀ i, IsPsh A (Θ i)) →
      maMeasure A Φ ≤ maMeasure A (fun i => Φ i + Θ i)

def AnalyticNullStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (S : Set X),
    A.IsAnalyticSubset S → interior S = ∅ →
      ∀ j, volume ((A.chart j) '' (S ∩ (A.chart j).source)) = 0

def MIntCongrNullStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (S : Set X), A.IsAnalyticSubset S → interior S = ∅ → ∀ g g' : X → ℝ,
    (∀ x ∉ S, g x = g' x) → mInt A Φ g = mInt A Φ g'

def StokesStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (w : X → ℝ), A.Smooth w → ∀ Φ : Fin e → LocPot X,
    (∀ i, IsPotential A (Φ i)) → mInt A (Fin.cons (LocPot.ofFun w) Φ) (fun _ => 1) = 0

def ByPartsSymmStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (v w : X → ℝ), A.Smooth v → A.Smooth w →
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun w) Φ) v = mInt A (Fin.cons (LocPot.ofFun v) Φ) w

def ByPartsNonposStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (v : X → ℝ), A.Smooth v → ∀ Φ : Fin e → LocPot X,
    (∀ i, IsPotential A (Φ i)) → (∀ i, IsPsh A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun v) Φ) v ≤ 0

def MassIndepStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (u : Fin e → X → ℝ), (∀ i, IsPotential A (Φ i)) →
    (∀ i, A.Smooth (u i)) →
      mInt A (fun i => Φ i + LocPot.ofFun (u i)) (fun _ => 1) = mInt A Φ (fun _ => 1)

def LogNormIntegrableStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (W : Fin r → Set X),
    IsPotential A L → IsSection A L s → IsSNC A L s m W → ∀ Φ : Fin e → LocPot X,
    (∀ i, IsPotential A (Φ i)) → MIntegrable A Φ (logNormSec L s)

def PoincareLelongStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (W : Fin r → Set X) (B : ∀ k, FinHolAtlas e (W k)),
    IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ k, HoloMap (B k) A Subtype.val) →
    ∀ v : X → ℝ, A.Smooth v → ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
        ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
            (v ∘ Subtype.val) - mInt A (Fin.cons L Φ) v

def LocDensPullbackStatement : Prop :=
  ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X)
    (B : FinHolAtlas e Y) (h : Y → X) (hh : HoloMap B A h) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → ∀ j k, ∀ y ∈ (B.chart j).target,
      h ((B.chart j).symm y) ∈ (A.chart k).source →
      locDens B (fun i => (Φ i).pullback h hh.1) j y =
        locDens A Φ k (A.chart k (h ((B.chart j).symm y))) *
          ‖LinearMap.det (fderiv ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y :
            (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2

def RankDropStatement : Prop :=
  ∀ {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e' X)
    (B : FinHolAtlas e Y) (h : Y → X) (hh : HoloMap B A h),
    (∀ j k, ∀ y ∈ (B.chart j).target, h ((B.chart j).symm y) ∈ (A.chart k).source →
      Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e' → ℂ))) < e) →
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∀ g : Y → ℝ,
      mInt B (fun i => (Φ i).pullback h hh.1) g = 0

def IsDegreeOff {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X) (d : ℕ) (S : Set X) : Prop :=
  A.IsAnalyticSubset S ∧ interior S = ∅ ∧ B.IsAnalyticSubset (h ⁻¹' S) ∧
    interior (h ⁻¹' S) = ∅ ∧ (∀ x ∉ S, (h ⁻¹' {x}).ncard = d) ∧
    ∀ j k, ∀ y ∈ (B.chart j).target, (B.chart j).symm y ∉ h ⁻¹' S →
      h ((B.chart j).symm y) ∈ (A.chart k).source →
      LinearMap.det (fderiv ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0

def DegreeFormulaStatement : Prop :=
  ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X)
    (hh : HoloMap B A h) (d : ℕ) (S : Set X), IsDegreeOff A B h d S →
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∀ g : X → ℝ, Continuous g →
      mInt B (fun i => (Φ i).pullback h hh.1) (g ∘ h) = d * mInt A Φ g

def DegreeFormulaIntStatement : Prop :=
  ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X)
    (hh : HoloMap B A h) (d : ℕ) (S : Set X), IsDegreeOff A B h d S →
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∀ g : X → ℝ, MIntegrable A Φ g →
      MIntegrable B (fun i => (Φ i).pullback h hh.1) (g ∘ h) ∧
        mInt B (fun i => (Φ i).pullback h hh.1) (g ∘ h) = d * mInt A Φ g

end

end ReciprocityTheory.AnForm.M
end

