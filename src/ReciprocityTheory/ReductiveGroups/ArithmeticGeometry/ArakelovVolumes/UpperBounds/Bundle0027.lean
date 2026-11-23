module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FrameMeasStatementPfC
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def ufL : (Ix X.Ψ r → ℂ) ≃ₗ[ℂ] Frame X.Ψ r where
  toFun := uf X
  invFun x i := x i.1 i.2.1 i.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def ufC : (Ix X.Ψ r → ℂ) ≃L[ℂ] Frame X.Ψ r := (ufL X).toContinuousLinearEquiv

theorem haarF : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure := by
  haveI h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]
    exact Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]
    exact Measure.pi.isAddHaarMeasure _
  rw [volume_pi]
  exact Measure.pi.isAddHaarMeasure _

theorem haarIx : (volume : Measure (Ix X.Ψ r → ℂ)).IsAddHaarMeasure := by
  infer_instance

attribute [local instance] haarF haarIx

theorem lintegral_ufC (F : Frame X.Ψ r → ℝ≥0∞) :
    ∫⁻ v, F (ufC X v) = Measure.addHaarScalarFactor (volume.map (ufC X)) volume * ∫⁻ x, F x := by
  haveI : (volume.map (ufC X)).IsAddHaarMeasure := (ufC X).isAddHaarMeasure_map volume
  have e1 : ∫⁻ v, F (ufC X v) = ∫⁻ x, F x ∂(volume.map (ufC X)) :=
    (lintegral_map_equiv F (ufC X).toHomeomorph.toMeasurableEquiv).symm
  rw [e1]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (volume.map (ufC X)) volume]
  rw [lintegral_smul_measure]
  rfl

theorem continuous_UF : Continuous (UF X) := by
  apply continuous_pi
  intro τ
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [UF, Umat, Matrix.of_apply]
  by_cases hh : b < a
  · simp only [hh, not_true_eq_false, dite_false]
    exact continuous_const
  · simp only [hh, not_false_eq_true, dite_true]
    fun_prop

theorem continuous_rmul : Continuous fun q : Frame X.Ψ r × Frame X.Ψ r => rmul q.1 q.2 := by
  apply continuous_pi
  intro τ
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  apply continuous_finsetSum
  intro k _
  fun_prop

def fI (C : Set (Frame X.Ψ r)) (q : Frame X.Ψ r × (UpI X.Ψ r → ℂ)) : ℝ≥0∞ :=
  if ∀ τ b, q.2 (dI τ b) ≠ 0 then
    ENNReal.ofReal (Complex.normSq (jacU q.2)) * C.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul q.1 (UF X q.2)) else 0

theorem measurable_fI {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C) : Measurable (fI X C) := by
  have hJ : Continuous (fun y : UpI X.Ψ r → ℂ => jacU y) := by
    unfold jacU
    apply continuous_finsetProd
    intro i _
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  have hS : MeasurableSet {q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) | ∀ τ b, q.2 (dI τ b) ≠ 0} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun τ => MeasurableSet.iInter fun b => ?_
    have hc : Continuous fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) => q.2 (dI τ b) :=
      (continuous_apply (dI τ b) : Continuous fun y : UpI X.Ψ r → ℂ => y (dI τ b)).comp continuous_snd
    exact (isOpen_ne_fun hc continuous_const).measurableSet
  have hf : Measurable (fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) =>
      ENNReal.ofReal (Complex.normSq (jacU q.2))) :=
    ENNReal.measurable_ofReal.comp ((Complex.continuous_normSq.comp (hJ.comp continuous_snd)).measurable)
  have hg : Measurable (fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) =>
      C.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul q.1 (UF X q.2))) :=
    (measurable_one.indicator hCm).comp
      ((continuous_rmul X).comp (continuous_fst.prodMk ((continuous_UF X).comp continuous_snd))).measurable
  unfold fI
  exact Measurable.ite hS (hf.mul hg) measurable_const

theorem measurable_Jp {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C) : Measurable (Jp X C) := by
  exact (measurable_fI X hCm).lintegral_prod_right'

theorem Jp_eq_zero {C : Set (Frame X.Ψ r)} {q : Frame X.Ψ r}
    (h : ∀ y : UpI X.Ψ r → ℂ, (∀ τ b, y (dI τ b) ≠ 0) → rmul q (UF X y) ∉ C) : Jp X C q = 0 := by
  unfold Jp
  have hz : ∀ y : UpI X.Ψ r → ℂ, (if ∀ τ b, y (dI τ b) ≠ 0 then
      ENNReal.ofReal (Complex.normSq (jacU y)) * C.indicator 1 (rmul q (UF X y)) else 0) = 0 := by
    intro y
    split_ifs with hy
    · simp [Set.indicator, h y hy]
    · rfl
  simp_rw [hz]
  exact lintegral_zero

theorem mem_sat {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {x0 : Frame X.Ψ r} {z : V (nd X)}
    {y : UpI X.Ψ r → ℂ} (hd : ∀ τ b, y (dI τ b) ≠ 0) (hxC : rmul (cpt X x0 z) (UF X y) ∈ C) :
    z ∈ sat X x0 C := by
  have hb := UF_mem X hd
  refine ⟨?_, rmul (cpt X x0 z) (UF X y), hxC, invF X (UF X y), invF_mem' X hb, (rmul_invF X hb).symm⟩
  show cpt X x0 z ∈ X.dom
  have := OrthogonalFrameDomain.rmul_mem_dom X (hCd hxC) (invF_mem' X hb)
  rwa [rmul_invF X hb] at this

theorem not_dom_rmul {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {p : Frame X.Ψ r} (hp : p ∉ X.dom)
    {y : UpI X.Ψ r → ℂ} (hd : ∀ τ b, y (dI τ b) ≠ 0) : rmul p (UF X y) ∉ C := fun h => by
  have hb := UF_mem X hd
  have := OrthogonalFrameDomain.rmul_mem_dom X (hCd h) (invF_mem' X hb)
  rw [rmul_invF X hb] at this
  exact hp this

theorem inner_le {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C)
    (hCd : C ⊆ X.dom) {R0 : ℝ} (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0)
    {G : Frame X.Ψ r → ℝ≥0∞} (hGinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x)
    (x : LoI X.Ψ r → ℂ) :
    ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then ENNReal.ofReal (Complex.normSq (jacU y)) *
      C.indicator G (ufC X (LA (fun τ => mat x0 τ) (lu ((eS X.Ψ r).symm (x, y))))) else 0) ≤
      KR X R0 * GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x := by
  set p := rmul x0 (NF X x) with hpdef
  have hg : ∀ y, C.indicator G (ufC X (LA (fun τ => mat x0 τ) (lu ((eS X.Ψ r).symm (x, y))))) =
      C.indicator G (rmul p (UF X y)) := by
    intro y
    change C.indicator G (rmul x0 (uf X (lu ((eS X.Ψ r).symm (x, y))))) = _
    rw [uf_lu_eS, rmul_assoc']
  by_cases hp : p ∈ X.dom
  · have hmeas : Measurable fun y => fI X C (p, y) :=
      (measurable_fI X hCm).comp (measurable_const.prodMk measurable_id)
    calc _ = ∫⁻ y, G p * fI X C (p, y) := lintegral_congr fun y => by
            simp only [fI]
            split_ifs with hd
            · rw [hg y]
              by_cases hxC : rmul p (UF X y) ∈ C
              · rw [Set.indicator_of_mem hxC, Set.indicator_of_mem hxC, hGinv p hp _ (UF_mem X hd),
                  Pi.one_apply, mul_one, mul_comm]
              · simp [Set.indicator_of_notMem hxC]
            · rw [mul_zero]
      _ = G p * Jp X C p := lintegral_const_mul _ hmeas
      _ ≤ KR X R0 * GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x := by
          unfold GLo
          rw [if_pos hp]
          by_cases hJ : Jp X C p = 0
          · rw [hJ, mul_zero]; exact bot_le
          · rw [Set.indicator_of_mem (show p ∈ {p | Jp X C p ≠ 0} from hJ)]
            calc G p * Jp X C p ≤ G p * (ENNReal.ofReal (densY X p) * KR X R0) := by
                  gcongr; exact Jp_le X hCd hR0 hp (fun τ => norm_dmin_last X hx0 x τ)
              _ = KR X R0 * (G p * ENNReal.ofReal (densY X p)) := by ring
  · calc _ = ∫⁻ y, (0 : ℝ≥0∞) := lintegral_congr fun y => by
            split_ifs with hd
            · rw [hg y, Set.indicator_of_notMem (not_dom_rmul X hCd hp hd), mul_zero]
            · rfl
      _ = 0 := lintegral_zero
      _ ≤ _ := bot_le

end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

theorem cpt_diff (x : Frame X.Ψ r) : Differentiable ℂ (cpt X x) := by
  exact (OntoB.cd_cpt X x).differentiable (by simp)

def Uc : Set (V (nd X)) := (cpt X (rmul x1' b1)) ⁻¹' ExtFPf.cell D

theorem isOpen_Uc : IsOpen (Uc X b1 D) := by
  have hcell : IsOpen (ExtFPf.cell D) :=
    (FourierCoefficientDomain.isOpen_dom (X := X)).inter (D.hΔ.continuous.isOpen_preimage _ isOpen_compl_singleton)
  exact (cpt_diff X _).continuous.isOpen_preimage _ hcell

theorem Φ_diffOn : DifferentiableOn ℂ (Φ X b1 D) (Uc X b1 D) := by
  exact D.hz.comp (cpt_diff X _).differentiableOn fun z hz => hz

theorem Φ_cdOn : ContDiffOn ℂ ∞ (Φ X b1 D) (Uc X b1 D) := by
  refine contDiffOn_piLp' 2 fun i => ?_
  have hi : DifferentiableOn ℂ (fun x => (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i) (Φ X b1 D x))
      (Uc X b1 D) :=
    (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i).differentiable.comp_differentiableOn (Φ_diffOn X b1 D)
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn (nd X) _ _ (isOpen_Uc X b1 D) hi

theorem jac_bound {ρ0 : ℝ} (hsub : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D) :
    ∃ Kj : ℝ, ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ0, |(fderiv ℝ (Φ X b1 D) z).det| ≤ Kj := by
  have hcd : ContDiffOn ℝ ∞ (Φ X b1 D) (Uc X b1 D) := (Φ_cdOn X b1 D).restrict_scalars ℝ
  have hfd : ContinuousOn (fun z => fderiv ℝ (Φ X b1 D) z) (Uc X b1 D) :=
    hcd.continuousOn_fderiv_of_isOpen (isOpen_Uc X b1 D) (by simp)
  have hdet : ContinuousOn (fun z => (fderiv ℝ (Φ X b1 D) z).det) (Uc X b1 D) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hfd
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hdet.mono hsub)
  exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC z hz⟩

theorem dens_bound {ρ0 : ℝ} (hsub : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D) :
    ∃ Kd : ℝ, ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ0, densF X x1' (Φ X b1 D z) ≤ Kd := by
  have hΦc : ContinuousOn (Φ X b1 D) (Uc X b1 D) := (Φ_diffOn X b1 D).continuousOn
  have hmaps : Set.MapsTo (Φ X b1 D) (Uc X b1 D) (OmF X x1') := fun z hz => (split X b1 D hz).1
  have hc : ContinuousOn (fun z => densF X x1' (Φ X b1 D z)) (Uc X b1 D) :=
    (OntoB.densF_continuousOn (X := X) (x0 := x1')).comp hΦc hmaps
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hc.mono hsub)
  exact ⟨C, fun z hz => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z hz)⟩

def Tset (x1 : Frame X.Ψ r) (ρ : ℝ) : Set (Frame X.Ψ r) :=
  (fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x1 p.1) p.2) '' (Metric.ball 0 ρ ×ˢ Bor X.Ψ r)

theorem Tset_eq {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D) :
    Tset X (rmul x1' b1) ρ = KU.Sset X x1' (Φ X b1 D '' Metric.ball 0 ρ) := by
  have hTmem : ∀ {y c : Frame X.Ψ r}, c ∈ Bor X.Ψ r →
      (rmul y c ∈ Tset X (rmul x1' b1) ρ ↔ y ∈ Tset X (rmul x1' b1) ρ) := fun hc =>
    KU.rmul_mem_S X (x0 := rmul x1' b1) (FF := Metric.ball 0 ρ) hc
  ext y
  constructor
  · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    have hs := split X b1 D (hsub hz)
    show rmul (cpt X (rmul x1' b1) z) b ∈ _
    rw [KU.rmul_mem_S X hb, hs.2.2]
    exact ⟨(Φ X b1 D z, β X b1 D z), ⟨⟨z, hz, rfl⟩, hs.2.1⟩, rfl⟩
  · rintro ⟨⟨w, b⟩, ⟨⟨z, hz, rfl⟩, hb⟩, rfl⟩
    have hs := split X b1 D (hsub hz)
    show rmul (cpt X x1' (Φ X b1 D z)) b ∈ Tset X (rmul x1' b1) ρ
    rw [hTmem hb, ← MI.rmul_invF X (y := cpt X x1' (Φ X b1 D z)) hs.2.1, ← hs.2.2,
      hTmem (MI.invF_mem' X hs.2.1)]
    exact ⟨(z, ExtFPf.oneF X), ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩

theorem meas_image {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D) (hx1 : rmul x1' b1 ∈ X.dom) :
    MeasurableSet (Φ X b1 D '' Metric.ball 0 ρ) := by
  exact measurableSet_ball.image_of_continuousOn_injOn ((Φ_diffOn X b1 D).continuousOn.mono hsub)
    ((Φ_injOn X b1 D hx1).mono hsub)

theorem meas_Tset (ho' : IsOrth X x1') {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D)
    (hx1 : rmul x1' b1 ∈ X.dom) : MeasurableSet (Tset X (rmul x1' b1) ρ) := by
  rw [Tset_eq X b1 D hsub]
  exact KU.meas_S X ho' (meas_image X b1 D hsub hx1)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfF
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoF

open NumberField Complex Matrix Topology Filter MeasureTheory Set Metric ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoC ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem sq_sub_le (a b : ℂ) : ‖b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
  have h := norm_sub_le a (a - b)
  rw [sub_sub_cancel] at h
  nlinarith [sq_nonneg (‖a‖ - ‖a - b‖), norm_nonneg b, norm_nonneg a, norm_nonneg (a - b)]

theorem ball_diff_eq {g1 : V (nd X) → ℂ} {z : V (nd X)} {ρ : ℝ} (hB : ball z ρ ⊆ OmF X x0) :
    ball z ρ \ {y | g1 y = 0} = ball z ρ ∩ Om1 X x0 g1 := by
  ext y
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq, Om1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, hB h1, h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩

theorem localRepresentationL2 {la : Wt X.Ψ r} {W : Frame X.Ψ r → ℝ≥0∞} {c : ℝ} (hc : 0 < c)
    (hWL : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x) {bb : ℝ}
    {g1 : V (nd X) → ℂ} (hg1 : DifferentiableOn ℂ g1 (OmF X x0)) {F0 F' : V (nd X) → ℂ}
    (hF0 : ContinuousOn F0 (OmF X x0))
    (hJ : ∫⁻ z in Om1 X x0 g1, ENNReal.ofReal (‖F0 z - F' z‖ ^ 2 / kaF X x0 bb z) *
      W (cpt X x0 z) ∂muF X x0 < ⊤) :
    ∀ z ∈ OmF X x0, ∃ ρ > 0, ball z ρ ⊆ OmF X x0 ∧
      ∫⁻ y in ball z ρ \ {y | g1 y = 0}, ENNReal.ofReal (‖F' y‖ ^ 2) < ⊤ := by
  intro z hz
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 (isOpen_OmF (X := X) (x0 := x0)) z hz
  set ρ := ε / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hKsub : closedBall z ρ ⊆ OmF X x0 := (closedBall_subset_ball (by linarith)).trans hεB
  have hBsub : ball z ρ ⊆ OmF X x0 := ball_subset_closedBall.trans hKsub
  have hKc : IsCompact (closedBall z ρ) := isCompact_closedBall z ρ
  have hzK : z ∈ closedBall z ρ := mem_closedBall_self hρ0.le
  refine ⟨ρ, hρ0, hBsub, ?_⟩
  rw [ball_diff_eq X x0 hBsub]

  obtain ⟨M0, hM0⟩ := hKc.exists_bound_of_continuousOn (hF0.mono hKsub)
  have hgc : ContinuousOn (fun y => c * Real.exp (-phla X la (cpt X x0 y))) (closedBall z ρ) :=
    (continuousOn_const.mul (expPhla_cont (X := X) (x0 := x0) la)).mono hKsub
  obtain ⟨y1, -, hy1⟩ := hKc.exists_isMinOn ⟨z, hzK⟩ hgc
  set w0 := c * Real.exp (-phla X la (cpt X x0 y1)) with hw0
  have hw0p : 0 < w0 := by positivity
  have hdc : ContinuousOn (densF X x0) (closedBall z ρ) := (densF_continuousOn (X := X) (x0 := x0)).mono hKsub
  obtain ⟨y2, hy2K, hy2⟩ := hKc.exists_isMinOn ⟨z, hzK⟩ hdc
  set d0 := densF X x0 y2 with hd0
  have hd0p : 0 < d0 := densF_pos (X := X) (x0 := x0) (hKsub hy2K)
  have hkc : ContinuousOn (kaF X x0 bb) (closedBall z ρ) := fun y hy =>
    (ka_contDiffAt (X := X) (x0 := x0) bb (hKsub hy)).continuousAt.continuousWithinAt
  obtain ⟨k1, hk1⟩ := hKc.exists_bound_of_continuousOn hkc
  set kmax := max k1 1 with hkmax
  have hka : ∀ y ∈ closedBall z ρ, 0 < kaF X x0 bb y ∧ kaF X x0 bb y ≤ kmax := fun y hy => by
    have hp : 0 < kaF X x0 bb y := Real.exp_pos _
    refine ⟨hp, ?_⟩
    have := hk1 y hy
    rw [Real.norm_eq_abs, abs_of_pos hp] at this
    exact this.trans (le_max_left _ _)

  have hOm1o : IsOpen (Om1 X x0 g1) :=
    hg1.continuousOn.isOpen_inter_preimage (isOpen_OmF (X := X) (x0 := x0)) isOpen_compl_singleton
  have hOm1m : MeasurableSet (Om1 X x0 g1) := hOm1o.measurableSet
  have hOm1s : Om1 X x0 g1 ⊆ OmF X x0 := fun y hy => hy.1
  set dd : V (nd X) → ℝ≥0∞ := fun y => ENNReal.ofReal (densF X x0 y) with hdd
  set h : V (nd X) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * W (cpt X x0 y) with hh
  have hJ' : ∫⁻ y in Om1 X x0 g1, dd y * h y < ⊤ := by
    have e : ∫⁻ y in Om1 X x0 g1, h y ∂muF X x0 = ∫⁻ y in Om1 X x0 g1, dd y * h y := by
      rw [muF, restrict_withDensity hOm1m, Measure.restrict_restrict hOm1m, Set.inter_eq_left.2 hOm1s]
      exact lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
        (((densF_continuousOn (X := X) (x0 := x0)).mono hOm1s).aemeasurable hOm1m).ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) h
    rw [← e]
    exact hJ
  set Cst : ℝ := 2 * kmax / (w0 * d0) with hCst
  have hpt : ∀ y ∈ ball z ρ ∩ Om1 X x0 g1, ENNReal.ofReal (‖F' y‖ ^ 2) ≤
      ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal Cst * (dd y * h y) := by
    rintro y ⟨hyB, -⟩
    have hyK : y ∈ closedBall z ρ := ball_subset_closedBall hyB
    have hyF : y ∈ OmF X x0 := hKsub hyK
    obtain ⟨hk0, hkle⟩ := hka y hyK
    have hdy : d0 ≤ densF X x0 y := hy2 hyK
    have hwy : w0 ≤ c * Real.exp (-phla X la (cpt X x0 y)) := hy1 hyK
    have hW : ENNReal.ofReal w0 ≤ W (cpt X x0 y) := (ENNReal.ofReal_le_ofReal hwy).trans (hWL _ hyF)
    have hq : 0 ≤ ‖F0 y - F' y‖ ^ 2 := by positivity
    have hM2 : ‖F0 y‖ ^ 2 ≤ M0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM0 y hyK) 2
    have hsq := sq_sub_le (F0 y) (F' y)
    have f1 : 1 ≤ kmax / kaF X x0 bb y := (one_le_div hk0).2 hkle
    have f2 : 1 ≤ densF X x0 y / d0 := (one_le_div hd0p).2 hdy
    have hdens : 0 ≤ densF X x0 y := hd0p.le.trans hdy
    have hCst0 : 0 ≤ Cst := by positivity
    have hreal : 2 * ‖F0 y - F' y‖ ^ 2 ≤
        Cst * densF X x0 y * (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * w0 := by
      have e : Cst * densF X x0 y * (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * w0 =
          2 * ‖F0 y - F' y‖ ^ 2 * ((kmax / kaF X x0 bb y) * (densF X x0 y / d0)) := by
        rw [hCst]
        field_simp
      rw [e]
      have f3 : 1 ≤ (kmax / kaF X x0 bb y) * (densF X x0 y / d0) := by nlinarith
      nlinarith
    calc ENNReal.ofReal (‖F' y‖ ^ 2)
        ≤ ENNReal.ofReal (2 * M0 ^ 2 + 2 * ‖F0 y - F' y‖ ^ 2) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal (2 * ‖F0 y - F' y‖ ^ 2) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal Cst * (dd y * h y) := by
          gcongr ENNReal.ofReal (2 * M0 ^ 2) + ?_
          calc ENNReal.ofReal (2 * ‖F0 y - F' y‖ ^ 2)
              ≤ ENNReal.ofReal (Cst * densF X x0 y * (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * w0) :=
                ENNReal.ofReal_le_ofReal hreal
            _ = ENNReal.ofReal Cst * (ENNReal.ofReal (densF X x0 y) *
                  (ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * ENNReal.ofReal w0)) := by
                rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCst0 hdens) (div_nonneg hq hk0.le)),
                  ENNReal.ofReal_mul (mul_nonneg hCst0 hdens), ENNReal.ofReal_mul hCst0]
                ring
            _ ≤ ENNReal.ofReal Cst * (dd y * h y) := by
                show _ ≤ ENNReal.ofReal Cst * (ENNReal.ofReal (densF X x0 y) *
                  (ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * W (cpt X x0 y)))
                gcongr
  calc ∫⁻ y in ball z ρ ∩ Om1 X x0 g1, ENNReal.ofReal (‖F' y‖ ^ 2)
      ≤ ∫⁻ y in ball z ρ ∩ Om1 X x0 g1, (ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal Cst * (dd y * h y)) :=
        setLIntegral_mono' (measurableSet_ball.inter hOm1m) hpt
    _ = ENNReal.ofReal (2 * M0 ^ 2) * volume (ball z ρ ∩ Om1 X x0 g1) +
          ENNReal.ofReal Cst * ∫⁻ y in ball z ρ ∩ Om1 X x0 g1, dd y * h y := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Measure.restrict_apply_univ]
    _ < ⊤ := by
        apply ENNReal.add_lt_top.2 ⟨?_, ?_⟩
        · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top)
        · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((lintegral_mono_set Set.inter_subset_right).trans_lt hJ')

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoF
end

