module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerate
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

section Abstract

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem meanC_thetaS_of_lintegral (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin n → Fin M → E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (hm : Measurable Φ)
    (hfin : ∫⁻ h in 𝓕, ∑' x : S, ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (x : Fin n → Fin M → E)))‖ₑ ∂μ < ⊤) :
    meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) := by
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM M J hJ (AF F)
  have ha : ∀ X, Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ X := fun X =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hsum : ∑' X : S, ∫⁻ h in 𝓕, ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1))‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum (f := fun (X : S) h => ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1))‖ₑ)
      fun X => (hm.enorm.comp (ha _)).aemeasurable]
    exact hfin.ne
  have hint : Integrable Φ (Measure.sum fun X : S =>
      (μ.restrict 𝓕).map fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    change ∫⁻ X, ‖Φ X‖ₑ ∂_ < ⊤
    rw [lintegral_sum_measure]
    simp only [lintegral_map hm.enorm (ha _)]
    exact hsum.lt_top
  rw [thetaMeas, integral_smul_measure, integral_sum_measure hint, meanC, ENNReal.toReal_inv]
  simp only [integral_map (ha _).aemeasurable hm.aestronglyMeasurable]
  exact congrArg _ (integral_tsum (fun X => (hm.comp (ha _)).aestronglyMeasurable) hsum)

end Abstract

end GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

variable {D : D7}

def colsOf {m r : ℕ} (X : Fin r → Fin m → D.host.E) : Matrix (Fin m) (Fin r) D.host.E :=
  Matrix.of fun i a => X a i

theorem gramQ_colsOf (V : HSp D) {r : ℕ} (X : Fin r → Fin V.rank → D.host.E) :
    gramQ V (colsOf X) = HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X := by
  refine Matrix.ext fun a b => ?_
  change ∑ i, D.sp.cm.sig (X a i) * ∑ j, V.gram i j * X b j =
    ∑ i, ∑ j, D.sp.cm.sig (X a i) * V.gram i j * X b j
  simp only [Finset.mul_sum, mul_assoc]

theorem rank_eq_of_gramQ (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (h : (gramQ V x).det ≠ 0) : x.rank = r := by
  refine le_antisymm (Matrix.rank_le_width x) ?_
  have h1 : (gramQ V x).rank = r := by
    have := Matrix.rank_of_isUnit (gramQ V x) ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h))
    simpa using this
  have h2 : gramQ V x = ((x.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * HSpace.gram V) * x := by
    rw [gramQ, Matrix.mul_assoc]
  calc r = (gramQ V x).rank := h1.symm
    _ ≤ x.rank := by
      rw [h2]
      exact Matrix.rank_mul_le_right _ _

def fibEquiv (V : HSp D) {r : ℕ} (β : HermE D r) (hβ : β.1.det ≠ 0) :
    {X : Fin r → Fin V.rank → D.host.E | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} where
  toFun X := ⟨colsOf X.1, rank_eq_of_gramQ V _ (by rw [gramQ_colsOf, X.2]; exact hβ),
    (gramQ_colsOf V X.1).trans X.2⟩
  invFun x := ⟨fun a i => x.1 i a, (gramQ_colsOf V _).symm.trans x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tupOf_actW (V : HSp D) {r : ℕ} (h : GA D V) (X : Fin r → Fin V.rank → D.host.E) :
    tupOf (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h⁻¹ (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) X)) =
      HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((colsOf X).map (incA D)) := by
  ext i a
  rfl

theorem average_eq_meanC (V : HSp D) (ν μH : Measure (GA D V)) (hν : ν.IsHaarMeasure) (hμ : μH.IsHaarMeasure)
    (𝓕 : Set (GA D V)) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) :
    ⨍ q, descend (GQ V) f q ∂autMeasure V ν = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 f := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  obtain ⟨h0, h1, -⟩ := GlobalTheory.Published.SiegelOneVector.normalise D.sp.cm.sig V.gram (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND V) μH 𝓕 hμ h𝓕
  have e := Measure.isMulLeftInvariant_eq_smul μH ν
  set c := Measure.haarScalarFactor μH ν
  have e1 : autMeasure V μH = (c : ENNReal) • autMeasure V ν := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have e2 : μH 𝓕 = c * autMeasure V ν Set.univ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]
    exact congrArg (fun m : Measure (AutQ V) => m Set.univ) e1
  have hc0 : ((c : ℝ≥0∞)).toReal ≠ 0 := by
    intro h
    have : (c : ℝ≥0∞) = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
      · exact h
      · exact absurd h ENNReal.coe_ne_top
    rw [this, zero_mul] at e2
    exact h0 e2
  have e3 : ∫ g in 𝓕, f g ∂μH = (c : ℝ≥0∞).toReal • ∫ q, descend (GQ V) f q ∂autMeasure V ν := by
    have h3 := GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕 (descend (GQ V) f)
    simp only [hf.descend_mk] at h3
    rw [← h3]
    change ∫ q, descend (GQ V) f q ∂autMeasure V μH = _
    rw [e1, integral_smul_measure]
  rw [average_eq, HeckeCharacterZeroLocus.SiegelWeilU.meanC, e3, e2, ENNReal.toReal_mul, smul_smul, Measure.real,
    mul_inv, mul_comm ((c : ℝ≥0∞).toReal)⁻¹, mul_assoc, inv_mul_cancel₀ hc0, mul_one]

theorem setLIntegral_absTheta_lt_top (V : HSp D) (ν μH : Measure (GA D V)) (hν : ν.IsHaarMeasure)
    (hμ : μH.IsHaarMeasure) (𝓕 : Set (GA D V)) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) {r : ℕ}
    (φ : Mx D V.rank r → ℂ) (habs : GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤) :
    ∫⁻ h in 𝓕, GlobalTheory.SiegelFormula.absTheta V φ h ∂μH < ⊤ := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have e := Measure.isMulLeftInvariant_eq_smul μH ν
  set c := Measure.haarScalarFactor μH ν
  have e1 : autMeasure V μH = (c : ENNReal) • autMeasure V ν := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have hL := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have h3 := GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure h𝓕 (descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ))
  simp only [hL.descend_mk] at h3
  rw [← h3]
  change ∫⁻ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q ∂autMeasure V μH < ⊤
  rw [e1, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top habs


set_option maxHeartbeats 1000000 in
theorem ifrB_eq_thetaPartD : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
    ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
    ∀ (μH : Measure (GA D V)) (𝓕 : Set (GA D V)), μH.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μH →
    ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = thetaPartD V μH 𝓕 φ β := by
  intro D r V θ hθ ν hν φ hφ habs μH 𝓕 hμ h𝓕 β hβ
  have hcm := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top D.host.F
  haveI := lcA
  haveI := scA
  haveI := t2A
  obtain ⟨-, -, sc, -, -, -, -, borelK, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props D.host.F D.host.E D.sp.cm.sig hcm (AF D.host.F)
  haveI := sc
  haveI := borelK r V.rank
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hL := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
    (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hI := average_eq_meanC V ν μH hν hμ 𝓕 h𝓕 _ hL
  let Φ : (Fin r → Fin V.rank → AE D) → ℂ := fun X => φ (tupOf X)
  have hΦc : Continuous Φ := hcont.comp (continuous_matrix fun i a =>
    (continuous_apply i).comp (continuous_apply a))
  have hΦm : Measurable Φ := hΦc.measurable
  let S : Set (Fin r → Fin V.rank → D.host.E) :=
    {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1}
  have hfin : ∫⁻ h in 𝓕, ∑' x : S, ‖Φ (GlobalTheory.CompanionTheory.SW.actW (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig V.gram h⁻¹
      (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) (x : Fin r → Fin V.rank → D.host.E)))‖ₑ ∂μH < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun h => ?_)
      (setLIntegral_absTheta_lt_top V ν μH hν hμ 𝓕 h𝓕 φ habs)
    have hinj : Function.Injective fun X : S => colsOf X.1 := fun X Y e =>
      Subtype.ext (funext fun a => funext fun i => congrFun (congrFun e i) a)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_))
      (ENNReal.tsum_comp_le_tsum_of_injective hinj fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V h ξ)‖ₑ)
    exact congrArg (fun y => ‖φ y‖ₑ) (tupOf_actW V h X.1)
  have hS : HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram Φ S =
      fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V h x.1) := by
    funext h
    refine (tsum_congr fun X => ?_).trans ((fibEquiv V β hβ).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    exact congrArg φ (tupOf_actW V h X.1)
  have key := meanC_thetaS_of_lintegral D.sp.cm.sig hcm V.gram hJ μH 𝓕 S Φ hΦm hfin
  rw [hS] at key
  exact hI.trans key

end GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralThetaMeasureFormula
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

variable {D : D7}

theorem trM_actW_ratTup (V : HSp D) {r : ℕ} (h : GA D V) (X : Fin r → Fin V.rank → D.host.E) :
    trM (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h⁻¹ (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) X)) =
      HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((trM X).map (incA D)) := by
  ext i a
  rfl

def framesEquiv (V : HSp D) {r : ℕ} (T : Matrix (Fin r) (Fin r) D.host.E) :
    framesE D.sp.cm.sig V.gram T ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = T} where
  toFun X := ⟨trM X.1, (trM_mem_framesE_iff V X.1 T).1 X.2⟩
  invFun x := ⟨fun a i => x.1 i a, (trM_mem_framesE_iff V _ T).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem glue : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → ∀ β : HermE D r, Integrable (fun X => φ (trM X)) (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) ∧ IfrB V ν φ β = ∫ X, φ (trM X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) := by
  intro D r V θ hθ ν hν 𝓕 h𝓕 φ hφ habs β
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  have hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND D.sp.cm.sig V.gram := isHermND_gram V
  have hν' : HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν := hν
  have h𝓕' : HeckeCharacterZeroLocus.SiegelWeilU.IsFDH D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν 𝓕 := h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top D.host.F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props _ _ D.sp.cm.sig hcm (AF D.host.F)
  have := hB r V.rank
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have htr : Continuous (trM : (Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) → Mx D V.rank r) :=
    continuous_pi fun i => continuous_pi fun a =>
      (show Continuous fun X : Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E => X a i from
        (continuous_apply i).comp (continuous_apply a))
  set S := framesE D.sp.cm.sig V.gram β.1 with hS
  set Φ : (Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => φ (trM X) with hΦdef
  have hΦ : Measurable Φ := (hcont.comp htr).measurable
  have hν0 : ν 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  have hinvtop : (ν 𝓕)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hν0
  have hL := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have habs' : ∫⁻ g in 𝓕, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν < ⊤ := by
    have e := GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure h𝓕 (descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ))
    simp only [hL.descend_mk] at e
    rw [← e]
    exact habs
  have hle : ∀ g : GA D V, ∑' X : S, ‖Φ (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram g⁻¹
      (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) (X : Fin r → Fin V.rank → D.host.E)))‖ₑ ≤
      GlobalTheory.SiegelFormula.absTheta V φ g := fun g => by
    have hinj : Function.Injective fun X : S => trM (X : Fin r → Fin V.rank → D.host.E) :=
      fun X Y h => (framesEquiv V β.1).injective (Subtype.ext h)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V g ξ)‖ₑ))
    simp only [hΦdef, trM_actW_ratTup, GlobalTheory.SiegelFormula.invPt]
  have hint : Integrable Φ (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 S) := by
    refine ⟨hΦ.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ ν 𝓕 hν' h𝓕' r S _ hΦ.enorm]
    exact ENNReal.mul_lt_top hinvtop.lt_top ((lintegral_mono hle).trans_lt habs')
  refine ⟨hint, ?_⟩
  rw [← PositivityTheory.PlacePermOperatorBicommutantSpan.theta_int D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ ν 𝓕 hν' h𝓕' r S Φ hΦ hint]
  have hInv := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(Matrix.rank_mul_eq_right_of_isUnit_det _ _
        ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hth : ∀ g : GA D V, HeckeCharacterZeroLocus.SiegelWeilU.thetaS _ _ D.sp.cm.sig V.rank V.gram Φ S g =
      ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V g x.1) := fun g => by
    refine (tsum_congr fun X => ?_).trans ((framesEquiv V β.1).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V g x.1))
    exact congrArg φ (trM_actW_ratTup V g X.1)
  rw [IfrB, average_eq, GlobalTheory.AutomorphicL2Unitary.autMeasure, Measure.real, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕,
    GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
  have e1 : ∀ g : GA D V, descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) (GlobalTheory.AutomorphicL2Unitary.mk (GQ V) g) =
      HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram Φ S g :=
    fun g => (hInv.descend_mk g).trans (hth g).symm
  simp only [e1]
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDiagonalNormalForm
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

section Field
variable {E : Type} [Field E] {c : E →+* E}

theorem exists_congr_diag_rank (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t) {n ρ p : ℕ} (hn : ρ + p = n)
    {G : Matrix (Fin n) (Fin n) E} (hG : ∀ a b, c (G a b) = G b a) (hr : ρ ≤ G.rank) :
    ∃ (a : Matrix (Fin n) (Fin n) E) (d₁ : Fin ρ → E) (d₂ : Fin p → E), a.det ≠ 0 ∧
      (a.map c).transpose * G * a = bl hn (Matrix.diagonal d₁) 0 0 (Matrix.diagonal d₂) ∧
      (∀ i, c (d₁ i) = d₁ i) ∧ (∀ i, c (d₂ i) = d₂ i) ∧ ∀ i, d₁ i ≠ 0 := by
  classical
  obtain ⟨P, d, hP, hPG, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal h2 hc hG
  have hQ : (P.map c).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero c).mpr hP
  have hrk : (Matrix.diagonal d).rank = G.rank := by
    rw [← hPG, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr hQ),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hP)]
  rw [Matrix.rank_diagonal, Fintype.card_subtype] at hrk
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (hr.trans hrk.ge)
  let e : Fin ρ ⊕ Fin p ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let A : Finset (Fin n) := Finset.univ.map ⟨fun i : Fin ρ => e (Sum.inl i), fun i j h => Sum.inl_injective (e.injective h)⟩
  have hAc : A.card = ρ := by simp [A]
  let e' : {x // x ∈ A} ≃ {x // x ∈ T} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hAc, hTc])
  let σ : Equiv.Perm (Fin n) := e'.extendSubtype
  have hσ : ∀ i : Fin ρ, d (σ (e (Sum.inl i))) ≠ 0 := by
    intro i
    have hm : σ (e (Sum.inl i)) ∈ T := Equiv.extendSubtype_mem e' _ (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    simpa using hTS hm
  refine ⟨(P.map c).submatrix id σ, fun i => d (σ (e (Sum.inl i))), fun j => d (σ (e (Sum.inr j))), ?_, ?_,
    fun i => hd _, fun j => hd _, hσ⟩
  · rw [Matrix.det_permute']
    refine mul_ne_zero ?_ hQ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · have hmc : (((P.map c).submatrix id σ).map c).transpose * G * (P.map c).submatrix id σ
        = (P.transpose * G * P.map c).submatrix σ σ := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id, hc]
    rw [hmc, hPG, Matrix.submatrix_diagonal_equiv]
    unfold PositivityTheory.Rg.Rsw.bl
    rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y <;> simp [e]

end Field

theorem exists_cg_dsum {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (β : HermE D n) (hr : ρ ≤ β.1.rank) :
    ∃ (a : GL (Fin n) D.host.E) (b₀ : HermE D ρ) (β' : HermE D p), IsDiagInv b₀ ∧ cg a β = dsum hn b₀ β' := by
  obtain ⟨G, hG⟩ := β
  have hc : ∀ t : D.host.E, D.sp.cm.sig.toRingHom (D.sp.cm.sig.toRingHom t) = t := fun t => star_star t
  obtain ⟨a, d₁, d₂, ha, hEq, hd₁, hd₂, hne⟩ := exists_congr_diag_rank (c := D.sp.cm.sig.toRingHom) two_ne_zero hc hn
    (G := G) (fun i j => congrFun (congrFun hG j) i) hr
  have hdiag : ∀ {m : ℕ} (d : Fin m → D.host.E), (∀ i, D.sp.cm.sig.toRingHom (d i) = d i) →
      ((Matrix.diagonal d).map ⇑D.sp.cm.sig).transpose = Matrix.diagonal d := by
    intro m d hd
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    congr 1
    funext i
    exact hd i
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a ha, ⟨Matrix.diagonal d₁, hdiag d₁ hd₁⟩,
    ⟨Matrix.diagonal d₂, hdiag d₂ hd₂⟩, ⟨Matrix.isDiag_diagonal _, ?_⟩, ?_⟩
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  · exact Subtype.ext hEq

end GlobalTheory.CompanionTheory.PcFc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodicPartialFourierMean
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem bT_add_right (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) (γ y : hermA D p) :
    bT hn z x (γ + y) = bT hn 0 0 γ + bT hn z x y := by
  apply Subtype.ext
  have h0 : adj (0 : Mx D ρ p) = 0 := by
    ext i j
    simp [adj]
  ext i j
  simp only [bT, AddSubgroup.coe_add, AddSubgroup.coe_zero, h0, Matrix.add_apply, bl, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
    simp

theorem bT_zero_mem_ratHerm (hn : ρ + p = n) {γ : hermA D p} (hγ : γ ∈ ratHerm D p) :
    bT hn 0 0 γ ∈ ratHerm D n := by
  obtain ⟨η, hη⟩ : γ.1 ∈ ratMx D p p := hγ
  have h0 : adj (0 : Mx D ρ p) = 0 := by
    ext i j
    simp [adj]
  refine (show (bT hn 0 0 γ : hermA D n).1 ∈ ratMx D n n from ⟨bl hn 0 0 0 η, ?_⟩)
  ext i j
  have hij : ∀ a b, (incA D) (η a b) = γ.1 a b := fun a b => by
    rw [← hη]
    rfl
  simp only [bT, AddSubgroup.coe_zero, h0, bl, AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
    simp [hij]

theorem isPer_pm {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
    (Φ : hermA D n → ℂ) (hΦ : IsPer Φ) : IsPer (pm hn m ψ b₀ Φ) := by
  intro γ hγ y
  have h : ∀ x z, Φ (bT hn z x (γ + y)) = Φ (bT hn z x y) := fun x z => by
    rw [bT_add_right]
    exact hΦ _ (bT_zero_mem_ratHerm hn hγ) _
  simp only [pm, h]

end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShAdd
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem sh_add : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y y' : Mx D ρ p),
    M.sh y * M.sh y' = M.sh (y + y') :=
  fun M y y' => GlobalTheory.CompanionTheory.PcB.sh_mul M y y'

end GlobalTheory.CompanionTheory.FJE
end
end

