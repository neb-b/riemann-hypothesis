module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInvT
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem fibTrans {D : D7} (X : HidaSetting D) (μinf : Measure (TupI X)) (νinf : Measure (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)))
    (fibInf : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) → Measure (TupI X))
    (hfib : IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ fibInf)
    (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (hS : μinf.map (fun y => g • y) = μinf) :
    IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ
      (fun b => (fibInf b).map (fun y => g • y)) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hm : Measurable (fun y : TupI X => g • y) := measurable_smul_tupI X g
  have hinv : ∀ b : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS), (fun y : TupI X => g • y) ⁻¹' ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X) =
      (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X := by
    intro b; ext y
    simp only [mem_preimage, mem_inter_iff, mem_singleton_iff, gramR_smulI, indI_smul_iff]
  have hmeasA : ∀ b : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS), MeasurableSet ((gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ⁻¹' {(b : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))} ∩ IndI X) := fun b =>
    (isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurableSet.inter
      (isOpen_IndI X).measurableSet
  have hU' : (fun y : TupI X => g • y) ⁻¹' IndI X = IndI X := by
    ext y; exact indI_smul_iff X g y
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hs hU => ?_⟩
  · rw [Measure.map_apply hm (hmeasA b).compl, preimage_compl, hinv b]
    exact hfib.1 b
  · calc ∫⁻ v in IndI X, φ v ∂μinf = ∫⁻ v in IndI X, φ v ∂(μinf.map (fun y => g • y)) := by rw [hS]
      _ = ∫⁻ v in IndI X, φ (g • v) ∂μinf := by
          rw [setLIntegral_map (isOpen_IndI X).measurableSet hφ hm, hU']
      _ = ∫⁻ b, ∫⁻ v, φ (g • v) ∂(fibInf b) ∂νinf := hfib.2.1 _ (hφ.comp hm)
      _ = ∫⁻ b, ∫⁻ v, φ v ∂((fibInf b).map (fun y => g • y)) ∂νinf := by
          congr 1; funext b; rw [lintegral_map hφ hm]
  · have hc' : Continuous (fun v => φ (g • v)) := hc.comp (continuous_smul_tupI X g)
    have hs' : HasCompactSupport (fun v => φ (g • v)) := hs.comp_homeomorph (smulH X g)
    have hU2 : tsupport (fun v => φ (g • v)) ⊆ IndI X := by
      rw [show (fun v => φ (g • v)) = φ ∘ smulH X g from rfl, tsupport_comp_eq_preimage]
      intro y hy
      exact (indI_smul_iff X g y).1 (hU hy)
    obtain ⟨hI, hC⟩ := hfib.2.2 _ hc' hs' hU2
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable]
      exact hI b hb
    · have e : (fun b => ∫ v, φ v ∂((fibInf b).map (fun y => g • y))) =
          fun b => ∫ v, φ (g • v) ∂(fibInf b) := by
        funext b; rw [integral_map hm.aemeasurable hc.aestronglyMeasurable]
      rw [e]
      exact hC

theorem fibEqI {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (μinf : Measure (TupI X))
    (νinf : Measure (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS))) (fib1 fib2 : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) → Measure (TupI X))
    (hμ : SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS) μinf)
    (hν : SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS) νinf)
    (h1 : IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ fib1)
    (h2 : IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ fib2) : fib1 = fib2 := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI := hμ.1
  haveI := hν.1
  haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))
  haveI : LocallyCompactSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :=
    (isClosed_HermRP (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact FU.fib_eq h1 h2 (continuous_gramHI X) (fun _ => rfl) Subtype.val_injective (isOpen_IndI X)

theorem invFib_of (hS : SdInvG) : InvFib := by
  intro D X u' ψ hT μinf νinf fibInf hP g
  have hfib := hP.2.2.2.2.2.2
  have h := fibEqI X ψ μinf νinf _ _ hP.2.2.2.2.1 hP.2.2.2.2.2.1
    (fibTrans X μinf νinf fibInf hfib g (hS X u' ψ hT μinf νinf fibInf hP g)) hfib
  exact congrFun h (TI X u' hT)

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GaugeVolU
section
noncomputable section

namespace PI.AprimeInfW

theorem jm_true (k : ℕ) : Formalism.REAL.Jm (fun _ : Fin k => true) = 1 := by
  simp [Formalism.REAL.Jm]

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacGlue
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def gVal {D : D7} (X : HidaSetting D) : ℝ :=
  Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F)

def tVal {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : ℝ :=
  Tw u' ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F))

def GrpLim {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  (∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ0 → MeasurableSet (TubeG X u' (κ '' ball 0 ρ)) ∧
      0 < X.measG.μGinf (TubeG X u' (κ '' ball 0 ρ)) ∧ X.measG.μGinf (TubeG X u' (κ '' ball 0 ρ)) < ⊤) ∧
  ∀ ρ : ℕ → ℝ, (∀ n, 0 < ρ n) → Tendsto ρ atTop (𝓝 0) →
    Tendsto (fun n => (X.measG.μGinf (TubeG X u' (κ '' ball 0 (ρ n)))).toReal /
      (volume (ball (0 : EuclideanSpace ℝ ι) (ρ n))).toReal) atTop (𝓝 (gVal X))

def PsiM {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : HmI X → MfI X) {ι η : Type}
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (eT : TupI X ≃ₜ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) : EuclideanSpace ℝ ι × EuclideanSpace ℝ η :=
  eT (κ z.1 • rmulT X (a (eH.symm z.2)) (Y0 X u'))

def TupJac {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (μinf : Measure (TupI X)) (νinf : Measure (HmI X)) (a : HmI X → MfI X) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  ∃ (η : Type) (_ : Fintype η) (eT : TupI X ≃ₜ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cμ cν : ℝ)
    (Ψ' : EuclideanSpace ℝ ι × EuclideanSpace ℝ η →
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ η →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (U : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)),
    0 < cμ ∧ 0 < cν ∧ μinf.map eT = ENNReal.ofReal cμ • volume ∧ νinf.map eH = ENNReal.ofReal cν • volume ∧
    U ∈ 𝓝 ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT)) ∧
    (∀ z ∈ U, HasFDerivWithinAt (PsiM X u' a κ eT eH) (Ψ' z) U z) ∧ Set.InjOn (PsiM X u' a κ eT eH) U ∧
    ContinuousAt (fun z => |(Ψ' z).det|) ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT)) ∧
    (∀ᶠ T in 𝓝 (TI X u' hT), IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X) ∧
    cμ * |(Ψ' ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT))).det| / cν = tVal X u'

def GoodP : ChartPred := fun X u' hT μinf νinf a =>
  ∃ (ι : Type) (_ : Fintype ι) (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J),
    GrpLim X u' κ ∧ TupJac X u' hT μinf νinf a κ

theorem splitAsym_good : SplitAsymFor GoodP := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  obtain ⟨ι, hι, κ, ⟨⟨ρ0, hρ0, hG0⟩, hGl⟩, η, hη, eT, eH, cμ, cν, Ψ', U, hcμ, hcν, hμ, hν, hU, hΨ', hinj,
    hdet, hev, harith⟩ := hPr
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  haveI : BorelSpace (HmI X) := ⟨rfl⟩
  haveI hHaar : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  set T0 := TI X u' hT with hT0
  set z0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η := (0, eH T0) with hz0
  set Ψ := PsiM X u' a κ eT eH with hΨ
  set d := |(Ψ' z0).det| with hd

  have hdet1 : (fun z => |(Ψ' z).det|) ⁻¹' Set.Iio (d + 1) ∈ 𝓝 z0 := hdet (Iio_mem_nhds (by linarith))
  have hHn : eH.symm ⁻¹' (Ω₂ ∩ {T | IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X}) ∈ 𝓝 (eH T0) := by
    apply eH.symm.continuous.continuousAt.preimage_mem_nhds
    rw [eH.symm_apply_apply]
    exact inter_mem hΩ₂n hev
  have hS : U ∩ (fun z => |(Ψ' z).det|) ⁻¹' Set.Iio (d + 1) ∩
      Prod.snd ⁻¹' (eH.symm ⁻¹' (Ω₂ ∩ {T | IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X})) ∈ 𝓝 z0 :=
    inter_mem (inter_mem hU hdet1) (continuous_snd.continuousAt.preimage_mem_nhds hHn)
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.1 hS
  set m0 := min r ρ0 with hm0
  have hm0p : 0 < m0 := lt_min hr hρ0
  set ρ : ℕ → ℝ := fun n => m0 / ((n : ℝ) + 2) with hρ
  have hρp : ∀ n, 0 < ρ n := fun n => div_pos hm0p (by positivity)
  have hρle : ∀ n, ρ n < m0 := fun n => by
    show m0 / ((n : ℝ) + 2) < m0
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hρr : ∀ n, ρ n < r := fun n => (hρle n).trans_le (min_le_left _ _)
  have hρ0' : ∀ n, ρ n < ρ0 := fun n => (hρle n).trans_le (min_le_right _ _)
  have hρlim : Tendsto ρ atTop (𝓝 0) := by
    have h1 := (tendsto_const_div_atTop_nhds_zero_nat m0).comp (tendsto_add_atTop_nat 2)
    refine h1.congr fun n => ?_
    simp only [Function.comp, hρ, Nat.cast_add, Nat.cast_ofNat]

  set A : ℕ → Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) := fun n => ball 0 (ρ n) ×ˢ ball (eH T0) (ρ n) with hA
  have hAb : ∀ n, A n = ball z0 (ρ n) := fun n => ball_prod_same _ _ _
  have hAS : ∀ n, A n ⊆ U ∩ (fun z => |(Ψ' z).det|) ⁻¹' Set.Iio (d + 1) ∩
      Prod.snd ⁻¹' (eH.symm ⁻¹' (Ω₂ ∩ {T | IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X})) := fun n => by
    rw [hAb n]; exact (ball_subset_ball (hρr n).le).trans hrS
  have hAU : ∀ n, A n ⊆ U := fun n z hz => (hAS n hz).1.1
  have hAm : ∀ n, MeasurableSet (A n) := fun n => by rw [hAb n]; exact measurableSet_ball
  set V : ℕ → Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := fun n => κ '' ball 0 (ρ n) with hV
  set W : ℕ → Set (HmI X) := fun n => eH ⁻¹' ball (eH T0) (ρ n) with hW
  have hWp : ∀ n, ∀ T ∈ W n, T ∈ Ω₂ ∧ IsUnit (a T) ∧ rmulT X (a T) (Y0 X u') ∈ IndI X := by
    intro n T hTW
    have h1 := (hAS n (show ((0 : EuclideanSpace ℝ ι), eH T) ∈ A n from ⟨by exact Set.mem_preimage.mpr (mem_ball_self (hρp n)), hTW⟩)).2
    simpa [eH.symm_apply_apply] using h1
  set_option synthInstance.maxHeartbeats 100000 in
  have hΨc : ∀ n, ContinuousOn Ψ (A n) := fun n z hz =>
    ((hΨ' z (hAU n hz)).mono (hAU n)).continuousWithinAt
  have hΨm : ∀ n, MeasurableSet (Ψ '' A n) := fun n =>
    (hAm n).image_of_continuousOn_injOn (hΨc n) (hinj.mono (hAU n))
  have hBox : ∀ n, BoxT X u' a (V n) (W n) = eT ⁻¹' (Ψ '' A n) := by
    intro n
    ext y
    constructor
    · rintro ⟨T, hTW, g, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨(x, eH T), ⟨hx, hTW⟩, ?_⟩
      simp [hΨ, PsiM, eH.symm_apply_apply]
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, hy⟩
      refine ⟨eH.symm t, ?_, κ x, ⟨x, hx, rfl⟩, ?_⟩
      · show eH (eH.symm t) ∈ ball (eH T0) (ρ n)
        rw [eH.apply_symm_apply]; exact ht
      · apply eT.injective
        rw [← hy]
        rfl
  have hvolΨ : ∀ n, volume (Ψ '' A n) = ∫⁻ z in A n, ENNReal.ofReal |(Ψ' z).det| := fun n =>
    (lintegral_abs_det_fderiv_eq_addHaar_image volume (hAm n)
      (fun z hz => (hΨ' z (hAU n hz)).mono (hAU n)) (hinj.mono (hAU n))).symm
  have hvolA : ∀ n, volume (A n) = volume (ball (0 : EuclideanSpace ℝ ι) (ρ n)) * volume (ball (eH T0) (ρ n)) :=
    fun n => by rw [Measure.volume_eq_prod, Measure.prod_prod]
  have hAt : ∀ n, volume (A n) < ⊤ := fun n => by rw [hAb n]; exact measure_ball_lt_top
  have hA0 : ∀ n, 0 < volume (A n) := fun n => by rw [hAb n]; exact measure_ball_pos _ _ (hρp n)
  have hΨt : ∀ n, volume (Ψ '' A n) < ⊤ := by
    intro n
    rw [hvolΨ n]
    calc ∫⁻ z in A n, ENNReal.ofReal |(Ψ' z).det| ≤ ∫⁻ _ in A n, ENNReal.ofReal (d + 1) :=
          lintegral_mono_ae ((ae_restrict_iff' (hAm n)).2 (Eventually.of_forall fun z hz =>
            ENNReal.ofReal_le_ofReal (le_of_lt (hAS n hz).1.2)))
      _ = ENNReal.ofReal (d + 1) * volume (A n) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hAt n)
  have hμB : ∀ n, μinf (BoxT X u' a (V n) (W n)) = ENNReal.ofReal cμ * volume (Ψ '' A n) := fun n => by
    rw [hBox n, ← Measure.map_apply eT.continuous.measurable (hΨm n), hμ, Measure.smul_apply, smul_eq_mul]
  have hνW : ∀ n, νinf (W n) = ENNReal.ofReal cν * volume (ball (eH T0) (ρ n)) := fun n => by
    rw [hW, ← Measure.map_apply eH.continuous.measurable measurableSet_ball, hν, Measure.smul_apply, smul_eq_mul]
  have hBy0 : ∀ n, 0 < volume (ball (eH T0) (ρ n)) := fun n => measure_ball_pos _ _ (hρp n)
  have hBx0 : ∀ n, 0 < volume (ball (0 : EuclideanSpace ℝ ι) (ρ n)) := fun n => measure_ball_pos _ _ (hρp n)
  refine ⟨V, W, fun n => (volume (ball (0 : EuclideanSpace ℝ ι) (ρ n))).toReal, fun n => ?_, ?_, ?_, ?_⟩
  · obtain ⟨g1, g2, g3⟩ := hG0 (ρ n) (hρp n) (hρ0' n)
    refine ⟨measurableSet_ball.preimage eH.continuous.measurable, fun T hT' => (hWp n T hT').1, ?_, ?_,
      fun T hT' => (hWp n T hT').2.1, ?_, ?_, ?_, g1, g2, g3, ENNReal.toReal_pos (hBx0 n).ne' measure_ball_lt_top.ne⟩
    · rw [hνW n]; exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hcν).ne' (hBy0 n).ne'
    · rw [hνW n]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
    · rw [hBox n]; exact eT.continuous.measurable (hΨm n)
    · rintro y ⟨T, hTW, g, -, rfl⟩
      have hinj : Function.Injective (Matrix.mulVecLin
          ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) := by
        intro x x' h
        have h2 := congrArg (fun v => Matrix.mulVec (((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g)⁻¹ : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) v) h
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using h2
      exact LinearIndependent.map' (hWp n T hTW).2.2 _ (LinearMap.ker_eq_bot.2 hinj)
    · rw [hμB n]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hΨt n)
  · intro U' hU'
    have h1 : eH.symm ⁻¹' U' ∈ 𝓝 (eH T0) := by
      apply eH.symm.continuous.continuousAt.preimage_mem_nhds
      rw [eH.symm_apply_apply]; exact hU'
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 h1
    filter_upwards [hρlim.eventually (gt_mem_nhds hε)] with n hn
    intro T hTW
    have h2 : eH T ∈ ball (eH T0) ε := ball_subset_ball hn.le hTW
    have h3 := hεs h2
    simpa [eH.symm_apply_apply] using h3
  · exact hGl ρ hρp hρlim
  · have hi := img_ratio (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) hΨ' hinj hdet A hAm hAU
      hA0 hAt (fun V' hV' => by
        obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hV'
        filter_upwards [hρlim.eventually (gt_mem_nhds hε)] with n hn
        rw [hAb n]; exact (ball_subset_ball hn.le).trans hεs)
    have hval : cμ / cν * d = tVal X u' := by rw [← harith]; ring
    change Tendsto _ atTop (𝓝 (tVal X u'))
    rw [← hval]
    refine (hi.const_mul (cμ / cν)).congr fun n => ?_
    have hx : 0 < (volume (ball (0 : EuclideanSpace ℝ ι) (ρ n))).toReal :=
      ENNReal.toReal_pos (hBx0 n).ne' measure_ball_lt_top.ne
    have hy : 0 < (volume (ball (eH T0) (ρ n))).toReal := ENNReal.toReal_pos (hBy0 n).ne' measure_ball_lt_top.ne
    rw [hμB n, hνW n, hvolA n, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hcμ.le, ENNReal.toReal_ofReal hcν.le]
    field_simp

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.KerMeasHolds
section
noncomputable section

namespace PI.AprimeInfK

open MeasureTheory Topology Set
open scoped ENNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {X : Type} [MulAction G X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem ker_meas (x0 : X) (hc : Continuous fun g : G => g • x0)
    (ν : Measure (MulAction.stabilizer G x0)) [ν.IsMulLeftInvariant] [SFinite ν] (s : X → G)
    (hs : ∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) (h1 : ∀ y, ¬ (∃ g : G, g • x0 = y) → s y = 1) :
    Measurable (fun y => Measure.map (fun h : MulAction.stabilizer G x0 => s y * (h : G)) ν) := by
  classical
  have hcl : IsClosed ((MulAction.stabilizer G x0 : Subgroup G) : Set G) := isClosed_singleton.preimage hc
  haveI : IsClosed ((MulAction.stabilizer G x0 : Subgroup G) : Set G) := hcl
  haveI : PolishSpace G := PI.AprimeInfA.polish_of_lcsc G
  haveI : PolishSpace (G ⧸ MulAction.stabilizer G x0) := PI.AprimeInfA.polish_of_lcsc _
  haveI : BorelSpace (G ⧸ MulAction.stabilizer G x0) := CosetSpace.borelSpace
  set ι : G ⧸ MulAction.stabilizer G x0 → X := fun q => q.out • x0 with hιdef
  have hemb : MeasurableEmbedding ι := (PI.AprimeInfA.orb_cont x0 hc).measurableEmbedding (PI.AprimeInfA.orb_inj x0)
  have hmv : ∀ t : G, Measurable (fun h : MulAction.stabilizer G x0 => t * (h : G)) :=
    fun t => (continuous_const_mul t |>.comp continuous_subtype_val).measurable
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hf : Measurable (A.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hA
  have eq : (fun y => Measure.map (fun h : MulAction.stabilizer G x0 => s y * (h : G)) ν A) =
      Function.extend ι (fun q : G ⧸ MulAction.stabilizer G x0 =>
        ∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (q.out * (h : G)) ∂ν)
        (fun _ => ∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (h : G) ∂ν) := by
    funext y
    have e0 : Measure.map (fun h : MulAction.stabilizer G x0 => s y * (h : G)) ν A = ∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (s y * (h : G)) ∂ν := by
      rw [Measure.map_apply (hmv _) hA, ← lintegral_indicator_one ((hmv _) hA)]
      rfl
    rw [e0]
    by_cases hy : ∃ q, ι q = y
    · obtain ⟨q, rfl⟩ := hy
      rw [hemb.injective.extend_apply]
      have hsq : s (ι q) • x0 = q.out • x0 := hs (ι q) ⟨q.out, rfl⟩
      have hk : q.out⁻¹ * s (ι q) ∈ MulAction.stabilizer G x0 := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, hsq, inv_smul_smul]
      have hsk : s (ι q) = q.out * (q.out⁻¹ * s (ι q)) := by group
      rw [hsk]
      exact PI.AprimeInfA.avg_mul_mem (MulAction.stabilizer G x0) ν _ q.out ⟨_, hk⟩
    · rw [Function.extend_apply' _ _ _ (by simpa using hy)]
      have hno : ¬ ∃ g : G, g • x0 = y := by
        rintro ⟨g, rfl⟩
        exact hy ⟨(g : G ⧸ MulAction.stabilizer G x0), PI.AprimeInfA.orb_mk x0 g⟩
      rw [h1 y hno]
      simp only [one_mul]
  rw [eq]
  exact hemb.measurable_extend (PI.AprimeInfA.meas_avg_q (MulAction.stabilizer G x0) ν hf) measurable_const

end PI.AprimeInfK

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem kerMeas_holds : KerMeas := by
  intro D X u' ψ hT μinf νinf fibInf hP
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  set x0 := ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) with hx0
  have hc : Continuous fun g : GI X => g • x0 :=
    PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J _
  have hcl : IsClosed ((MulAction.stabilizer (GI X) x0 : Subgroup (GI X)) : Set (GI X)) :=
    isClosed_singleton.preimage hc
  haveI : LocallyCompactSpace (MulAction.stabilizer (GI X) x0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let ν : Measure (MulAction.stabilizer (GI X) x0) := (X.measW u').μHinf
  haveI hH : ν.IsHaarMeasure := (X.measW_norm u').2.1
  haveI : SecondCountableTopology (MulAction.stabilizer (GI X) x0) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace (MulAction.stabilizer (GI X) x0) := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hs : ∀ y, (∃ g : GI X, g • x0 = y) → sect X u' y • x0 = y := fun y hy => sect_spec X u' y hy
  have h1 : ∀ y, ¬ (∃ g : GI X, g • x0 = y) → sect X u' y = 1 := by
    intro y hy
    unfold sect
    exact dif_neg hy
  exact PI.AprimeInfK.ker_meas (G := GI X) x0 hc ν (sect X u') hs h1

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperL
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem pushLFin_of_proper (h : ProperOrb) : PushLFin := by
  intro D X u' ψ hT μinf νinf fibInf hH K hK hKI
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  obtain ⟨N, hN, C, hC, hNC⟩ := h X u' ψ hT μinf νinf fibInf hH K hK hKI
  rw [Measure.map_apply (measurable_orbM X u') hK.isClosed.measurableSet]
  refine lt_of_le_of_lt (measure_mono fun g hg => hNC 1 (mem_of_mem_nhds hN) g ?_) hC.measure_lt_top
  rw [rmulT_one]; exact hg

end PI.AprimeInfW
end
end

