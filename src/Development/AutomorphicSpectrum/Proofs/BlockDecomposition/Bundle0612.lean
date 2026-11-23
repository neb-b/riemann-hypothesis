module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0527
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0531
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionSmoothLieDerivative
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def psi (v : GA E a) : Lie E a := toL (GeneralLinearGroup.map (pInf E) v⁻¹).val

def wt (U : Subgroup (GL (Fin a) (Af E))) (F : GA E a → ℂ) (g : GA E a) : GA E a → ℂ :=
  Set.indicator {v | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U} fun v => F (g * v)


open Classical in
theorem wt_apply (U : Subgroup (GL (Fin a) (Af E))) (F : GA E a → ℂ) (g v : GA E a) :
    wt U F g v = if GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U then F (g * v) else 0 := by
  simp only [wt, Set.indicator_apply, Set.mem_setOf_eq]

def hb (β : Lie E a → ℂ) (q : Lie E a × Lie E a) : ℂ := β (toL (Matrix.of q.2 * Matrix.of q.1))

theorem continuous_psi : Continuous (psi (E := E) (a := a)) :=
  ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((ContAut.continuous_map_pInf E a).comp continuous_inv))

theorem contDiff_mul_lie : ContDiff ℝ ∞ fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e : (fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) i j) =
      fun q => ∑ k, q.2 i k * q.1 k j := by
    funext q; simp [toL, Matrix.mul_apply]
  rw [e]
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply ℝ _ k).comp ((contDiff_apply ℝ _ i).comp contDiff_snd)).mul
      ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_fst))

theorem contDiff_hb {β : Lie E a → ℂ} (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (hb (E := E) (a := a) β) :=
  hβ.comp contDiff_mul_lie

end GlobalTheory.CompanionTheory.SmoothRep.TstConv

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_compact_of_mul_mem_tsupport : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ), IsTest β →
    ∀ x₀ ∈ invSet E a, ∃ Kc : Set (Lie E a), IsCompact Kc ∧ Kc ⊆ invSet E a ∧ ∃ N ∈ 𝓝 x₀,
      ∀ y x : Lie E a, x ∈ N → toL (Matrix.of y * Matrix.of x) ∈ tsupport β → y ∈ Kc := by
  intro E _ _ _ a β hβ x₀ hx₀
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_invSet (E := E) (a := a)) x₀ hx₀
  set N := Metric.closedBall x₀ (δ / 2)
  have hNs : N ⊆ invSet E a := (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hball
  have hNc : IsCompact N := isCompact_closedBall x₀ (δ / 2)
  have hN' := isCompact_setOf_toL_mem (E := E) (a := a) hNc hNs
  have hB' := isCompact_setOf_toL_mem (E := E) (a := a) hβ.compact hβ.support
  have hcont : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Cinf E) => toL (p.1 * p.2⁻¹).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp (continuous_fst.mul continuous_snd.inv)
  refine ⟨_, (hB'.prod hN').image hcont, ?_, N, Metric.closedBall_mem_nhds x₀ (half_pos hδ), ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    exact val_mem_invSet _
  · intro y x hx hm
    obtain ⟨u, hu⟩ := hNs hx
    obtain ⟨b, hb⟩ := hβ.support hm
    refine ⟨(b, u), ⟨?_, ?_⟩, ?_⟩
    · change toL b.val ∈ tsupport β
      rw [hb]
      exact hm
    · change toL u.val ∈ N
      rw [hu]
      exact hx
    · change toL (b * u⁻¹).val = y
      have e : (b * u⁻¹).val = Matrix.of y := by
        rw [Units.val_mul, hb]
        change Matrix.of y * Matrix.of x * u⁻¹.val = Matrix.of y
        rw [← hu, mul_assoc, Units.mul_inv, mul_one]
      rw [e]
      rfl

theorem measurableSet_integrableOn_wt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ Fl : GA E a → ℂ, LocallyIntegrable Fl μ →
    ∀ Kc : Set (Lie E a), IsCompact Kc → Kc ⊆ invSet E a → ∀ g : GA E a,
      MeasurableSet {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} ∧
      IntegrableOn (wt U Fl g) {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} μ := by
  intro E _ _ _ a μ _ U hU hUc Fl hFl Kc hKc hKs g
  have hS : IsOpen {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U} :=
    hU.preimage ((ContAut.continuous_map_pFin E a).comp continuous_inv)
  have hm : MeasurableSet {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} :=
    hS.measurableSet.inter (hKc.isClosed.preimage continuous_psi).measurableSet
  refine ⟨hm, ?_⟩
  have hK' := isCompact_setOf_toL_mem (E := E) (a := a) hKc hKs
  have hcont : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹ :=
    ((GlobalTheory.CuspQuot.continuous_infGL.comp continuous_fst).mul
      ((GlobalTheory.BlockLevel.continuous_finGL a).comp continuous_snd)).inv
  have hD := (hK'.prod hUc).image hcont
  have hCD : {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} ⊆
      (fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹) ''
        ({y : GL (Fin a) (Cinf E) | toL y.val ∈ Kc} ×ˢ (U : Set (GL (Fin a) (Af E)))) := by
    rintro v ⟨hvU, hvK⟩
    exact ⟨(GeneralLinearGroup.map (pInf E) v⁻¹, GeneralLinearGroup.map (pFin E) v⁻¹), ⟨hvK, hvU⟩,
      by simp only [infGL_mul_finGL, inv_inv]⟩
  have hDg := hD.image (continuous_const_mul g)
  have hi : IntegrableOn (fun v => Fl (g * v)) ((fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) =>
      (infGL E a p.1 * finGL E a p.2)⁻¹) '' ({y : GL (Fin a) (Cinf E) | toL y.val ∈ Kc} ×ˢ
        (U : Set (GL (Fin a) (Af E))))) μ := by
    have := ((measurePreserving_mul_left μ g).integrableOn_comp_preimage
      (MeasurableEquiv.mulLeft g).measurableEmbedding).2 (hFl.integrableOn_isCompact hDg)
    rwa [Set.preimage_image_eq _ (mul_right_injective g)] at this
  exact (hi.mono_set hCD).indicator hS.measurableSet

theorem convR_tst_mul_infGL (μ : Measure (GA E a)) [μ.IsMulLeftInvariant] (U : Subgroup (GL (Fin a) (Af E)))
    (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    convR μ (tst U β) Fl (g * infGL E a y) = ∫ v, hb β (toL y.val, psi v) * wt U Fl g v ∂μ := by
  rw [← integral_mul_left_eq_self (fun v => hb β (toL y.val, psi v) * wt U Fl g v) (infGL E a y)]
  unfold convR
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hf : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ = GeneralLinearGroup.map (pFin E) v⁻¹ := by
    simp [_root_.mul_inv_rev, map_mul, map_inv]
  have hi : GeneralLinearGroup.map (pInf E) (infGL E a y * v)⁻¹ = GeneralLinearGroup.map (pInf E) v⁻¹ * y⁻¹ := by
    simp [_root_.mul_inv_rev, map_mul, map_inv]
  show _ = hb β (toL y.val, psi (infGL E a y * v)) * wt U Fl g (infGL E a y * v)
  rw [wt_apply]
  by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
  · have h' : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ ∈ U := hf ▸ h
    simp only [tst, ker, if_pos h, if_pos h', hb, psi, hi]
    have he : toL ((GeneralLinearGroup.map (pInf E) v⁻¹ * y⁻¹).val * y.val) =
        toL (GeneralLinearGroup.map (pInf E) v⁻¹).val := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    simp only [show ∀ m, Matrix.of (toL m) = m from fun m => Matrix.of.apply_symm_apply m, mul_assoc]
    change β (toL (GeneralLinearGroup.map (pInf E) v⁻¹).val) * Fl (g * (infGL E a y * v)) =
      β (toL ((GeneralLinearGroup.map (pInf E) v⁻¹ * y⁻¹).val * y.val)) * Fl (g * (infGL E a y * v))
    rw [he]
  · have h' : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ ∉ U := hf ▸ h
    simp only [tst, ker, if_neg h, if_neg h']
    simp
end GlobalTheory.CompanionTheory.SmoothRep.TstConv

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem fderiv_hb_one {β : Lie E a → ℂ} (hβ : ContDiff ℝ ∞ β) (y X : Lie E a) :
    fderiv ℝ (fun q => hb β (q, y)) (oneL E a) X = dTest X β y := by
  have e : (fun q => hb β (q, y)) = β ∘ lmul y := rfl
  have e1 : lmul y (oneL E a) = y := mul_one (Matrix.of y)
  rw [e, fderiv_comp _ (by rw [e1]; exact (hβ.differentiable (by simp)).differentiableAt)
    (lmul y).differentiableAt, e1, ContinuousLinearMap.fderiv]
  rfl

theorem exists_local {μ : Measure (GA E a)} [μ.IsHaarMeasure] {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ} (hFl : LocallyIntegrable Fl μ) (g : GA E a)
    {x₀ : Lie E a} (hx₀ : x₀ ∈ invSet E a) :
    ∃ C : Set (GA E a), ∃ K : Set (Lie E a), ∃ N ∈ 𝓝 x₀, MeasurableSet C ∧ IsCompact K ∧ (∀ v ∈ C, psi v ∈ K) ∧
      IntegrableOn (wt U Fl g) C μ ∧
      ∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N, toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β := by
  obtain ⟨Kc, hKc, hKs, N, hN, hNK⟩ := exists_compact_of_mul_mem_tsupport E a β hβ x₀ hx₀
  obtain ⟨hCm, hCi⟩ := measurableSet_integrableOn_wt E a μ U hU hUc Fl hFl Kc hKc hKs g
  exact ⟨_, Kc, N, hN, hCm, hKc, fun v hv => hv.2, hCi, fun v hv hvU x hx hm => hv ⟨hvU, hNK _ _ hx hm⟩⟩

theorem integrand_eq_zero {U : Subgroup (GL (Fin a) (Af E))} {β : Lie E a → ℂ} {Fl : GA E a → ℂ} {g : GA E a}
    {C : Set (GA E a)} {N : Set (Lie E a)}
    (hC : ∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N, toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β)
    {x : Lie E a} (hx : x ∈ N) (v : GA E a) (hv : v ∉ C) : hb β (x, psi v) * wt U Fl g v = 0 := by
  rw [wt_apply]
  by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
  · rw [hb, image_eq_zero_of_notMem_tsupport (hC v hv h x hx), zero_mul]
  · rw [if_neg h, mul_zero]

end GlobalTheory.CompanionTheory.SmoothRep.TstConv


open GlobalTheory.CompanionTheory.SmoothRep.TstConv in
theorem GlobalTheory.CompanionTheory.SmoothRep.convR_tst_mem_Sm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β → ∀ Fl : GA E a → ℂ, LocallyIntegrable Fl μ → convR μ (tst U β) Fl ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a), lieD X (convR μ (tst U β) Fl) g = convR μ (tst U (dTest X β)) Fl g := by
  intro E _ _ _ a μ _ _ U hU hUc β hβ Fl hFl

  have hchart : ∀ g, ∀ x ∈ invSet E a,
      chart (convR μ (tst U β) Fl) g x = ∫ v, hb β (x, psi v) * wt U Fl g v ∂μ := by
    intro g x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    rw [chart_val, convR_tst_mul_infGL]
  have hev : ∀ g, ∀ x ∈ invSet E a, chart (convR μ (tst U β) Fl) g =ᶠ[𝓝 x]
      fun x => ∫ v, hb β (x, psi v) * wt U Fl g v ∂μ := fun g x hx =>
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) (hchart g)

  have hloc : ∀ g, ∀ x₀ ∈ invSet E a, ∃ C : Set (GA E a), ∃ N ∈ 𝓝 x₀,
      (∀ x ∈ N, (∫ v, hb β (x, psi v) * wt U Fl g v ∂μ) = ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) ∧
      ContDiff ℝ ∞ (fun x => ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) ∧
      (∀ p X, fderiv ℝ (fun x => ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) p X =
        ∫ v in C, fderiv ℝ (fun q => hb β (q, psi v)) p X * wt U Fl g v ∂μ) ∧
      (∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N,
        toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β) := by
    intro g x₀ hx₀
    obtain ⟨C, K, N, hN, hCm, hK, hCK, hCi, hvan⟩ := exists_local hU hUc hβ hFl g hx₀
    have P := GlobalTheory.CompanionTheory.SmoothParam.contDiff_integral_density (GA E a) (Lie E a) (Lie E a) (μ.restrict C)
      (wt U Fl g) psi K hCi continuous_psi.aestronglyMeasurable hK
      ((ae_restrict_iff' hCm).2 (Filter.Eventually.of_forall hCK)) (hb β) (contDiff_hb hβ.contDiff)
    exact ⟨C, N, hN, fun x hx => (setIntegral_eq_integral_of_forall_compl_eq_zero
      (integrand_eq_zero hvan hx)).symm, P.1, P.2, hvan⟩
  refine ⟨fun g x hx => ?_, fun X g => ?_⟩
  · obtain ⟨C, N, hN, heq, hcd, -, -⟩ := hloc g x hx
    exact (hcd.contDiffAt.congr_of_eventuallyEq
      ((hev g x hx).trans (Filter.eventually_of_mem hN heq))).contDiffWithinAt
  · have h1 : oneL E a ∈ invSet E a := isUnit_one
    obtain ⟨C, N, hN, heq, hcd, hder, hvan⟩ := hloc g _ h1
    rw [lieD, ((hev g _ h1).trans (Filter.eventually_of_mem hN heq)).fderiv_eq, hder]
    simp_rw [fderiv_hb_one hβ.contDiff]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero ?_]
    · unfold convR
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      show dTest X β (psi v) * wt U Fl g v = tst U (dTest X β) v * Fl (g * v)
      rw [wt_apply]
      by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
      · simp only [tst, ker, if_pos h, psi]
      · simp only [tst, ker, if_neg h, mul_zero, zero_mul]
    · intro v hv
      rw [wt_apply]
      by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
      · have hn : psi v ∉ tsupport β := by
          have := hvan v hv h (oneL E a) (mem_of_mem_nhds hN)
          simpa [toL] using this
        have h0 : fderiv ℝ β (psi v) = 0 := by
          by_contra h0
          exact hn (support_fderiv_subset ℝ h0)
        rw [dTest, h0, ContinuousLinearMap.zero_apply, zero_mul]
      · rw [if_neg h, mul_zero]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfSizeMatrix
section
noncomputable section

namespace GlobalTheory.CompanionTheory.CuspCell

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.DiagCell

set_option synthInstance.maxHeartbeats 400000

theorem exists_eq_singleton_of_sum {ι A : Type*} [Fintype ι] [DecidableEq ι] {a : A} {t : ι → Multiset A}
    (h : ({a} : Multiset A) = ∑ j, t j) : ∃ j₀, t j₀ = {a} ∧ ∀ j, j ≠ j₀ → t j = 0 := by
  have hc : ∑ j, Multiset.card (t j) = 1 := by
    have := congrArg Multiset.card h
    rw [Multiset.card_sum] at this
    simpa using this.symm
  obtain ⟨j₀, -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hc.symm ▸ one_ne_zero)
  have hz : ∀ j, j ≠ j₀ → t j = 0 := fun j hj => by
    have h2 := Finset.add_le_sum (s := Finset.univ) (f := fun j => Multiset.card (t j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j₀) (Finset.mem_univ j) (Ne.symm hj)
    simp only [hc] at h2
    exact Multiset.card_eq_zero.1 (by omega)
  refine ⟨j₀, ?_, hz⟩
  rw [h, Finset.sum_eq_single j₀ (fun j _ hj => hz j hj) (by simp)]

theorem exists_equiv_of_sums {l c : ℕ} {A : Type*} {x : Fin l → A} {y : Fin c → A} {t : Fin l → Fin c → Multiset A}
    (hr : ∀ i, ({x i} : Multiset A) = ∑ j, t i j) (hc : ∀ j, ({y j} : Multiset A) = ∑ i, t i j) :
    ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, t i j = if e j = i then {x i} else 0 := by
  choose r hr1 hr0 using fun i => exists_eq_singleton_of_sum (hr i)
  choose e he1 he0 using fun j => exists_eq_singleton_of_sum (hc j)
  have hne : ∀ {a : A}, ({a} : Multiset A) ≠ 0 := Multiset.singleton_ne_zero _
  have h1 : ∀ i, e (r i) = i := fun i => by
    by_contra hi
    exact hne ((hr1 i).symm.trans (he0 (r i) i (Ne.symm hi)))
  have h2 : ∀ j, r (e j) = j := fun j => by
    by_contra hj
    exact hne ((he1 j).symm.trans (hr0 (e j) j (Ne.symm hj)))
  refine ⟨⟨e, r, h2, h1⟩, fun a => ?_, fun i j => ?_⟩
  · have h3 := hr1 (e a)
    rw [h2 a, he1 a] at h3
    exact Multiset.singleton_inj.1 h3
  · by_cases h : e j = i
    · subst h
      have h3 := hr1 (e j)
      rw [h2 j] at h3
      simpa using h3
    · simpa [h] using he0 j i (Ne.symm h)

theorem exists_equiv_of_jhMult_cell_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k))
    (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp)
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1)
    (h0 : jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0) :
    ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, b.1 i j = if e j = i then (x i).1 else 0 := by
  have hG := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, hrow, hcol⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (hG k).2 f g (fun i => (x i).2.rep.smooth)
    (fun i => (x i).2.rep.hasFiniteLength) hτ hτs h0
  have hR : ∀ i, ∃ t : Fin c → Multiset (IrrGL (k := k)), (∀ j, HasSupport (s i j).ρ (t j)) ∧ {x i} = ∑ j, t j :=
    fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_sum_of_jac hG hBZ (hasSupport_self (hxc i)) (f i)
      (_root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun j => s i j) (hrow i)
      (fun j => s i j) (fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle _ (fun j => (s i j).irr) j)
  choose t ht hAt using hR
  have hC : ∀ j, HasSupport (y j).rep (∑ i, t i j) := by
    intro j
    have hd : ∑ i, b.1 i j = (y j).1 := by simpa using Fintype.card_congr (g j)
    have hy := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) j (y j).2.rep.irr
      (hy.trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (s i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr)
    exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr)
      (fun i => (ht i j).of_equiv (IrrGL.equivOf _ _ _)) (y j).2.rep.irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  have hU : ∀ j, ({y j} : Multiset (IrrGL (k := k))) = ∑ i, t i j :=
    fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ (hasSupport_self (hyc j)) (hC j)
  obtain ⟨e, he, het⟩ := exists_equiv_of_sums hAt hU
  refine ⟨e, he, fun i j => ?_⟩
  have hd := (ht i j).sum_fst
  rw [het i j] at hd
  split_ifs at hd ⊢ <;> simpa using hd.symm

end GlobalTheory.CompanionTheory.CuspCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinUnfoldingSecondTerm
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

theorem unfold2 : Unfold2 := by
  intro D ψ hψ θ hθ V n r hrn μ 𝓕 hμ μr h𝓕r c a hca b Φ hΦ
  obtain ⟨𝓕r, hμr⟩ := h𝓕r
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn
  obtain ⟨μs, 𝓕s, hμs⟩ := exists_isCovolOne D V.rank s
  obtain ⟨hΦc, B, hB⟩ := _root_.GlobalTheory.CompanionTheory.EisUnfold.schwartzA_continuous_and_tsum_enorm_le D θ hθ V.rank (r + s) Φ hΦ
  have ha : IsUnit a.det := hca.1

  let e : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E ≃
      Matrix (Fin V.rank) (Fin (r + s)) D.host.E :=
    joinEquiv.trans
      { toFun := fun ξ => ξ * a
        invFun := fun ξ => ξ * a⁻¹
        left_inv := fun ξ => Matrix.mul_nonsing_inv_cancel_right a ξ ha
        right_inv := fun ξ => Matrix.nonsing_inv_mul_cancel_right a ξ ha }
  set T : Mx D V.rank (r + s) → ℂ := fun y => ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E,
    Heisenberg₂ ψ V (HMul.hMul (zy y) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D))) Φ
      (ξ.map (incA D)) with hT
  have hform : ∀ y₁ y₂, T (colJoin y₁ y₂) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b.1 a Φ pq.1 pq.2 y₁ y₂ := by
    intro y₁ y₂
    obtain ⟨hx, hy⟩ := _root_.GlobalTheory.CompanionTheory.EisUnfold.Parts.parts D V.rank r s b.1 a y₁ y₂
    rw [hT]
    dsimp only
    rw [← e.tsum_eq]
    exact tsum_congr fun pq => GlobalTheory.T.block_weil_action_theta_unfolding D ψ hψ V r s b.1 b.2 a ha Φ y₁ y₂ _ hx hy pq.1 pq.2
  have hper : ∀ γ ∈ ratMx D V.rank (r + s), ∀ y, T (γ + y) = T y := by
    intro γ hγ y
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    rw [← colJoin_colL_colR g, ← colJoin_colL_colR y, rat_colJoin, ← colJoin_add, hform, hform,
      add_comm (rat (colL g)), add_comm (rat (colR g))]
    exact _root_.GlobalTheory.CompanionTheory.EisUnfold.Period.tsum_cellTerm_add_rat D ψ hψ V r s b.1 a Φ (colL g) (colR g) (colL y) (colR y)
  have hE := _root_.GlobalTheory.CompanionTheory.EisUnfold.ProdCovol.isCovolOne_colJoin D V.rank r s μr 𝓕r μs 𝓕s hμr hμs
  show ∫ y in 𝓕, T y ∂μ = _
  rw [covolOne_integral_eq hE hμ T hper]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D V.rank s
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D V.rank (r + s)
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank s) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank (r + s)) := ⟨rfl⟩
  have hc : Continuous fun z : Mx D V.rank r × Mx D V.rank s => colJoin z.1 z.2 := by
    refine continuous_matrix fun i k => ?_
    simp only [colJoin, Matrix.of_apply]
    rcases finSumFinEquiv.symm k with j | j
    · exact (continuous_apply_apply i j).comp continuous_fst
    · exact (continuous_apply_apply i j).comp continuous_snd
  have hc' : Continuous fun y : Mx D V.rank (r + s) => ((colL y, colR y) : Mx D V.rank r × Mx D V.rank s) := by
    refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_)
    · exact continuous_apply_apply i (Fin.castAdd s j)
    · exact continuous_apply_apply i (Fin.natAdd r j)
  let hj : (Mx D V.rank r × Mx D V.rank s) ≃ₜ Mx D V.rank (r + s) :=
    { (joinEquiv : (Mx D V.rank r × Mx D V.rank s) ≃ Mx D V.rank (r + s)) with
      continuous_toFun := hc
      continuous_invFun := hc' }
  have hmp : MeasurePreserving hj.toMeasurableEquiv (μr.prod μs)
      ((μr.prod μs).map fun z => colJoin z.1 z.2) := ⟨hj.toMeasurableEquiv.measurable, rfl⟩
  have h1 := hmp.setIntegral_image_emb hj.toMeasurableEquiv.measurableEmbedding T (𝓕r ×ˢ 𝓕s)
  erw [h1]
  have h2 : ∀ z : Mx D V.rank r × Mx D V.rank s, T (hj.toMeasurableEquiv z) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b.1 a Φ pq.1 pq.2 z.1 z.2 := fun z => hform z.1 z.2
  simp only [h2]
  rw [_root_.GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq D ψ hψ V r s μr 𝓕r μs 𝓕s hμr hμs b.1 a ha Φ hΦc B hB]
  exact _root_.GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J D ψ V r s μr 𝓕r hμr c a hca b Φ

end GlobalTheory.CompanionTheory.EisUnfold

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPolynomialInStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_polynomial_in : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (A H₀ H : Matrix (Fin n) (Fin n) K), IsUnit A.det → A.charpoly.Separable → H₀.det ≠ 0 → cT σ A * H₀ * A = H₀ → cT σ A * H * A = H → ∃ m : K[X], H = H₀ * aeval A m := by
  first | exact @GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval | exact GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval | (intros; apply GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormOneStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_form_one : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0),
    CrystallineSemistableComparison.Om.L2.IsOmT q 0 e → e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  first | exact @GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | exact GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | (intros; apply GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducible_cuspidal_pair_nongeneric_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp →
      ¬ (prodIrr ![x, y] hd).IsIrreducible →
      ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ (prodIrr ![x, y] hd) ∧ ¬ IsGenericFor ψ τ.ρ := by
  first | exact @GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient | exact GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient | (intros; apply GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient <;> assumption)
end

