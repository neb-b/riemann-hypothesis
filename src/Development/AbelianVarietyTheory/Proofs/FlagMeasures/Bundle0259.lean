module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgue
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0253
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalData
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpSides

open Filter Topology GlobalTheory.CWDeriv

variable {k r : ℕ}

theorem cwCont_of {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
    {σ : Mat k r → (H →L[ℂ] H)} {Bm : H → Wp} (h : IsCWCont (k := k) (r := r) σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ Bm := by
  have e : ∀ (w : List (Mat k r)) (v : H),
      dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
    intro w v
    induction w with
    | nil => rfl
    | cons X w ih => show dsig σ X _ = PI.UpqRep.dsig σ X _; rw [ih]; rfl
  unfold IsCWCont at h
  simp only [e] at h
  exact h

theorem continuousOn_orbit {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} (R : BranchingSupport.Rep k r)
    (hR : R.IsDS ε mu) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V)
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v)
    (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm) {v : R.H} (hv : v ∈ R.sm) :
    ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) := by
  have hD : DerFacts R := fun X hX =>
    ⟨fun _ hv => ⟨DerivedAction.dsig_smooth hR.2 hX hv, DerivedAction.hasDerivAt_dsig hX hv⟩,
      fun _ hv _ hw => DerivedAction.dsig_skew hR.2 hX hv hw⟩
  have hsm := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hB0 : Bm 0 = 0 := by simpa using hs 0 0 h0
  intro g hg
  have h1 := cw_tendsto hB (l := 𝓝[GG k r] g) (u := fun x => (1 : ℂ) • (R.σ x v - R.σ g v) - 0)
    (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact sm_comb 1 (hsm x hx) (hsm g hg) h0)
    (by
      intro W hW
      have h2 : Tendsto _ (𝓝[GG k r] g) _ :=
        (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW) g hg).tendsto
      have hW0 : PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0 = 0 := by
        have h := dsigW_comb hD W hW 0 h0 h0 h0
        simp only [zero_smul, zero_sub, neg_zero] at h
        rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ] at h
        simpa using h
      rw [← tendsto_sub_nhds_zero_iff] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [dsigW_comb hD W hW 1 (hsm x hx) (hsm g hg) h0, hW0, one_smul, sub_zero])
  refine tendsto_sub_nhds_zero_iff.mp (h1.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [lin_comb ha hs 1 (hsm x hx) (hsm g hg) h0, hB0, one_smul, sub_zero]

theorem isHaarOn_smul {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) {x : ℝ} (hx : 0 < x) :
    IsHaarOn S (ENNReal.ofReal x • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun h0 => h2 ?_, by rw [Measure.smul_apply, h3, smul_zero], fun s hs => by
    rw [Measure.map_smul, h4 s hs]
    exact (BesselUnitaryEquiv.continuous_lmulM s).measurable.aemeasurable⟩
  · exact inferInstanceAs (SigmaFinite (x.toNNReal • μ))
  · have h1 := Measure.measure_univ_eq_zero.2 h0
    rw [Measure.smul_apply, smul_eq_mul] at h1
    exact Measure.measure_univ_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (ENNReal.ofReal_pos.2 hx).ne')

theorem haarLie_eq (x : ℝ) :
    haarLie (Nset k r) (ENNReal.ofReal x) =
      ENNReal.ofReal (x * 2 ^ (r * (k + 1) + r * (r - 1))) • lebN k r := by
  have h := _root_.GlobalTheory.Amp.NLie.haarLie_eq_lebN k r
  unfold haarLie at h ⊢
  rw [one_smul] at h
  rw [h, smul_smul, mul_comm x, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
    mul_comm (ENNReal.ofReal x)]
  simp

theorem oneSide_of {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Mat k r → (Wp →L[ℂ] Wp)} {c : ℂ}
    {μG μW νS : Measure (Mt k r)} {Bm : H → Wp} {v₀ : H} {cN x : ℝ} (hx : 0 < x)
    (hlam : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) (hG : IsHaarOn (GG k r) μG) (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    (hq : IsQuotMeas μG (muS μW (haarLie (Nset k r) (ENNReal.ofReal x))) νS)
    (hB : IsBesselMapSm z (psi k r z c) σ π Bm) (hv : v₀ ∈ smoothVecs (k := k) (r := r) σ) (hc : 0 < cN)
    (hl : l2SG νS (fun g => Bm (σ g v₀)) = ENNReal.ofReal (cN * Module.finrank ℂ Wp)) :
    OneSide z π (psi k r z c) μG μW (ENNReal.ofReal (x * 2 ^ (r * (k + 1) + r * (r - 1))) • lebN k r) νS
      (fun g => Bm (σ g v₀)) cN := by
  let R : BranchingSupport.Rep k r := ⟨H, σ⟩
  have hR : R.IsDS ε lam := ⟨hlam, hσ⟩
  obtain ⟨e1, e2, e3⟩ := (GlobalTheory.Amp.Schur.type_irred_and_avg k r z π hz hT).1 u hπ
  rw [haarLie_eq] at hq
  refine ⟨hz, hT, e1, e2, e3, hG, hW, hW1, isHaarOn_smul (_root_.GlobalTheory.Amp.NHaar.isHaarOn_lebN k r) (by positivity), hq,
    fun n _ => by unfold psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _, fun a ha m hm g hg => ?_,
    continuousOn_orbit R hR Bm hB.1 hB.2.1 (cwCont_of hB.2.2.2) hv, hc, hl⟩
  have ham : a * m ∈ GG k r := (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r a ha.1).2.2 m hm.1
  have h1 := PI.UnitaryGroupMassFormula.CapelliEig.Hecke_multiplication k r ε lam H σ hσ _ ham g hg
  have h2 := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ v₀ hv g hg
  show Bm (σ (a * m * g) v₀) = _
  rw [h1]
  exact hB.2.2.1 a ha m hm _ h2

theorem oneSide_of_good : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → OneSide W.z W.π (psiS D W.z) W.μG W.μW (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS' A.Φ' A.cN := by
  intro D τ w w' θ W lam A hv hθ hT hT' hW hA
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩ := hW
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10, -⟩ := hA
  rw [w12] at w13 w14
  have hx : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ := by positivity
  exact ⟨oneSide_of hx a1 a2 w3 (w5 ▸ hT) w1 w7 w8 w9 w13 a3 a5 a8 a9,
    oneSide_of hx a1 a2 w4 (w6 ▸ hT') w2 w7 w10 w11 w14 a4 a5 a8 a10⟩

end GlobalTheory.AmpSides
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallVolSuccSqStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ballVol_succ_sq_eq_pow_mul_prod : ∀ (P Q : ℕ) (r : ℝ), 0 < r → ballVol ((P + Q + 1) ^ 2) r = (2 : ℝ≥0∞) ^ (P + Q) * ((volume : Measure (ℝ × Sp P Q)).prod (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))) {p | tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} := by
  first | exact @GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq | exact GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq | (intros; apply GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMatrixCoeffExtendsBoundedEquivariant
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.BesselExt

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp]
  {σ : Mat k r → (H →L[ℂ] H)} {w : H} {a : ℝ} {μG : Measure (Mt k r)} {d : ℝ}
  {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {μS : Measure (Mt k r)}

theorem afun_add (hStd : Std σ w a μG d) (hSide : Side z π μS) {v : H} (hv : v ∈ DD σ w) (ξ : Wp)
    {u u' : H} (hu : u ∈ DD σ w) (hu' : u' ∈ DD σ w) {x : Mat k r} (hx : x ∈ GG k r) :
    Afun (psiGen k r z c) π μS σ (u + u') v ξ x =
      Afun (psiGen k r z c) π μS σ u v ξ x + Afun (psiGen k r z c) π μS σ u' v ξ x := by
  have hst := (_root_.GlobalTheory.SgInfDD.DD_stable_dense k r σ w hStd.2.1).1
  have h1 := (_root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u) (hst x hx u hu) v hv).1
  have h2 := (_root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u') (hst x hx u' hu') v hv).1
  simp only [Afun, be, map_add (f := _), coef_add_left, add_smul]
  rw [integral_add h1 h2, ContinuousLinearMap.add_apply]

theorem afun_smul (b : ℂ) (u v : H) (ξ : Wp) (x : Mat k r) :
    Afun (psiGen k r z c) π μS σ (b • u) v ξ x = b • Afun (psiGen k r z c) π μS σ u v ξ x := by
  simp only [Afun, be, map_smul, coef_smul_left, mul_smul]
  rw [integral_smul, ContinuousLinearMap.smul_apply]

theorem afun_mul_right (hσ : IsURepOn (GG k r) σ) (u v : H) (ξ : Wp) {x y : Mat k r}
    (hx : x ∈ GG k r) (hy : y ∈ GG k r) :
    Afun (psiGen k r z c) π μS σ (σ y u) v ξ x = Afun (psiGen k r z c) π μS σ u v ξ (x * y) := by
  simp only [Afun, hσ.1.2 x hx y hy, ContinuousLinearMap.comp_apply]

theorem afun_mul_left (hStd : Std σ w a μG d) (hSide : Side z π μS) {v : H} (hv : v ∈ DD σ w) (ξ : Wp)
    {u : H} (hu : u ∈ DD σ w) {s x : Mat k r} (hs : s ∈ Sset k r z) (hx : x ∈ GG k r)
    (hSG : Sset k r z ⊆ GG k r) :
    Afun (psiGen k r z c) π μS σ u v ξ (s * x) =
      PiS (psiGen k r z c) π s (Afun (psiGen k r z c) π μS σ u v ξ x) := by
  have hst := (_root_.GlobalTheory.SgInfDD.DD_stable_dense k r σ w hStd.2.1).1
  have h := ((_root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u) (hst x hx u hu) v hv).2.1 s hs).1
  simp only [Afun]
  rw [hStd.2.1.1.2 s (hSG hs) x hx, ContinuousLinearMap.comp_apply, h, ContinuousLinearMap.comp_apply]

theorem continuous_lmulM' (s : Mat k r) : Continuous (lmulM s : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem lintegral_comp_le_image {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] {μ : Measure X} {φ : X → X} (hmp : MeasurePreserving φ μ μ) (hφ : Continuous φ)
    (f : X → ENNReal) {K : Set X} (hK : IsCompact K) (hf : AEMeasurable f μ) :
    ∫⁻ x in K, f (φ x) ∂μ ≤ ∫⁻ x in φ '' K, f x ∂μ := by
  have hm : MeasurableSet (φ '' K) := (hK.image hφ).isClosed.measurableSet
  have hmap : μ.map φ = μ := hmp.map_eq
  calc ∫⁻ x in K, f (φ x) ∂μ ≤ ∫⁻ x, (φ '' K).indicator f (φ x) ∂μ := by
        rw [← lintegral_indicator hK.isClosed.measurableSet]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K
        · simp [Set.indicator, hx, Set.mem_image_of_mem φ hx]
        · simp [Set.indicator, hx]
    _ = ∫⁻ y, (φ '' K).indicator f y ∂μ := by
        have := lintegral_map' (μ := μ) (f := (φ '' K).indicator f) (g := φ)
          (by rw [hmap]; exact hf.indicator hm) hφ.aemeasurable
        rw [hmap] at this
        exact this.symm
    _ = ∫⁻ y in φ '' K, f y ∂μ := lintegral_indicator hm _

end GlobalTheory.SgInf.BesselExt


open GlobalTheory.SgInf.BesselExt in
theorem GlobalTheory.SgInf.bessel_ext_bounded : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ T : H → Mat k r → Wp, (∀ u ∈ DD σ w, T u = Afun (psiGen k r z c) π μS σ u v ξ) ∧ (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) ∧ (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) ∧ (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) ∧ (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) ∧ (∀ s ∈ Sset k r z, ∀ u : H, (fun x : Mt k r => T u (s * Matrix.of x)) =ᵐ[μG] fun x => PiS (psiGen k r z c) π s (T u (Matrix.of x))) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ
  have hσ : IsURepOn (GG k r) σ := hStd.2.1
  have hHaar : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hw0 : w ≠ 0 := by
    intro h; have h1 := hStd.2.2.2.1; rw [h, norm_zero] at h1; exact zero_ne_one h1
  have hcl := _root_.GlobalTheory.SgInf.closedSub_groups k r z hSide.1 hSide.2.1
  have hSG : Sset k r z ⊆ GG k r := hcl.2.2.2.1.1
  have hDD := _root_.GlobalTheory.SgInfDD.DD_stable_dense k r σ w hσ
  have hst : ∀ g ∈ GG k r, ∀ u ∈ DD σ w, σ g u ∈ DD σ w := hDD.1
  have hdense : Dense (DD σ w : Set H) := hDD.2.1 hStd.2.2.1 hw0
  have hconc : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := by
    rw [ae_iff]; exact hHaar.2.2.1
  let F : H → Mt k r → Wp := fun u x => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)
  let K : ℕ → Set (Mt k r) := fun n => Metric.closedBall 0 n
  have hKm : ∀ n, MeasurableSet (K n) := fun n => Metric.isClosed_closedBall.measurableSet
  have hKc : ∀ n, IsCompact (K n) := fun n => isCompact_closedBall 0 n
  have hcov : ⋃ n, K n = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌈‖x‖⌉₊, ?_⟩
    simp only [K, Metric.mem_closedBall, dist_zero_right]; exact Nat.le_ceil _
  have hsub : ∀ L : Set (Mt k r), IsCompact L → ∃ n, L ⊆ K n := by
    intro L hL
    obtain ⟨R, hR⟩ := hL.isBounded.subset_closedBall 0
    exact ⟨⌈R⌉₊, hR.trans (Metric.closedBall_subset_closedBall (Nat.le_ceil R))⟩
  have hadd : ∀ u ∈ DD σ w, ∀ u' ∈ DD σ w, F (u + u') =ᵐ[μG] fun x => F u x + F u' x := by
    intro u hu u' hu'
    filter_upwards [hconc] with x hx
    exact afun_add hStd hSide hv ξ hu hu' hx
  have hsmul : ∀ (b : ℂ), ∀ u ∈ DD σ w, F (b • u) =ᵐ[μG] fun x => b • F u x :=
    fun b u _ => Filter.Eventually.of_forall fun x => afun_smul b u v ξ _
  obtain ⟨T0, hT0D, hT0add, hT0smul, hT0b⟩ := _root_.GlobalTheory.extend_ae_linear_of_local_sq μG K hKm hcov (DD σ w) hdense F hadd hsmul
    (fun n => _root_.GlobalTheory.SgInf.lint_Afun_compact_le k r σ w a μG d z c π μS hStd hSide v hv ξ (K n) (hKc n))
  have hT0m : ∀ u, AEStronglyMeasurable (T0 u) μG := by
    intro u
    have h : AEStronglyMeasurable (T0 u) (μG.restrict (⋃ n, K n)) :=
      aestronglyMeasurable_iUnion_iff.2 fun n => ((hT0b n).choose_spec u).1
    rwa [hcov, Measure.restrict_univ] at h
  have hT0bK : ∀ L : Set (Mt k r), IsCompact L → ∃ C : ℝ, ∀ u,
      ∫⁻ x in L, (‖T0 u x‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
    intro L hL
    obtain ⟨n, hn⟩ := hsub L hL
    obtain ⟨C, hC⟩ := hT0b n
    exact ⟨C, fun u => (lintegral_mono_set hn).trans (hC u).2⟩
  have hT0sub : ∀ u u', (fun x => T0 u x - T0 u' x) =ᵐ[μG] T0 (u - u') := by
    intro u u'
    filter_upwards [hT0add (u - u') u'] with x hx
    rw [sub_add_cancel] at hx
    rw [hx]; simp
  have hmeasn : ∀ u, AEMeasurable (fun x => (‖T0 u x‖₊ : ENNReal) ^ 2) μG := fun u =>
    (hT0m u).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2
  refine ⟨fun u M => T0 u (Matrix.of.symm M), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; funext M; show T0 u _ = _; rw [hT0D u hu]; rfl
  · intro u u'; exact hT0add u u'
  · intro b u; exact hT0smul b u
  · intro L hL
    obtain ⟨n, hn⟩ := hsub L hL
    obtain ⟨C, hC⟩ := hT0b n
    exact ⟨C, fun u => ⟨(hC u).1.mono_measure (Measure.restrict_mono hn le_rfl),
      (lintegral_mono_set hn).trans (hC u).2⟩⟩
  · intro y hy u
    have hmp : MeasurePreserving (rmulM y) μG μG :=
      ⟨(continuous_rmulM y).measurable, (_root_.GlobalTheory.SgInf.isUnimod_GG k r μG hHaar).1 y hy⟩
    refine _root_.GlobalTheory.ae_eq_of_dense_of_local_sq_bound μG K hKm hcov (DD σ w : Set H) hdense
      (fun u x => T0 (σ y u) x) (fun u x => T0 u (rmulM y x)) ?_ ?_ ?_ ?_ ?_ u
    · intro u u'
      filter_upwards [hT0sub (σ y u) (σ y u')] with x hx
      rw [hx, map_sub]
    · intro u u'; exact hmp.quasiMeasurePreserving.ae (hT0sub u u')
    · intro n
      obtain ⟨C, hC⟩ := hT0b n
      refine ⟨C, fun u => ⟨(hC (σ y u)).1, ?_⟩⟩
      rw [← hσ.2.1 y hy u]; exact (hC (σ y u)).2
    · intro n
      obtain ⟨C, hC⟩ := hT0bK _ ((hKc n).image (continuous_rmulM y))
      refine ⟨C, fun u => ⟨((hT0m u).comp_measurePreserving hmp).restrict, ?_⟩⟩
      exact (lintegral_comp_le_image hmp (continuous_rmulM y) _ (hKc n) (hmeasn u)).trans (hC u)
    · intro u hu
      show (fun x => T0 (σ y u) x) =ᵐ[μG] fun x => T0 u (rmulM y x)
      rw [hT0D _ (hst y hy u hu), hT0D u hu]
      filter_upwards [hconc] with x hx
      exact afun_mul_right hσ u v ξ hx hy
  · intro s hs u
    have hmp : MeasurePreserving (lmulM s : Mt k r → Mt k r) μG μG :=
      ⟨(continuous_lmulM' s).measurable, hHaar.2.2.2 s (hSG hs)⟩
    have hPi := _root_.GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hSide.1 hSide.2.1 hSide.2.2.1
    have hPin : ‖PiS (psiGen k r z c) π s‖ ≤ 1 := (hPi.2.2.1 s hs).1
    have hnorm : ∀ e : Wp, ‖PiS (psiGen k r z c) π s e‖₊ ≤ ‖e‖₊ := fun e => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
      exact ((PiS (psiGen k r z c) π s).le_opNorm e).trans
        (mul_le_of_le_one_left (norm_nonneg _) hPin)
    refine _root_.GlobalTheory.ae_eq_of_dense_of_local_sq_bound μG K hKm hcov (DD σ w : Set H) hdense
      (fun u x => T0 u (lmulM s x)) (fun u x => PiS (psiGen k r z c) π s (T0 u x)) ?_ ?_ ?_ ?_ ?_ u
    · intro u u'; exact hmp.quasiMeasurePreserving.ae (hT0sub u u')
    · intro u u'
      filter_upwards [hT0sub u u'] with x hx
      rw [← map_sub, hx]
    · intro n
      obtain ⟨C, hC⟩ := hT0bK _ ((hKc n).image (continuous_lmulM' s))
      refine ⟨C, fun u => ⟨((hT0m u).comp_measurePreserving hmp).restrict, ?_⟩⟩
      exact (lintegral_comp_le_image hmp (continuous_lmulM' s) _ (hKc n) (hmeasn u)).trans (hC u)
    · intro n
      obtain ⟨C, hC⟩ := hT0b n
      refine ⟨C, fun u => ⟨(PiS (psiGen k r z c) π s).continuous.comp_aestronglyMeasurable (hC u).1, ?_⟩⟩
      refine le_trans (lintegral_mono fun x => ?_) (hC u).2
      exact pow_le_pow_left₀ (by positivity) (ENNReal.coe_le_coe.2 (hnorm _)) 2
    · intro u hu
      show (fun x => T0 u (lmulM s x)) =ᵐ[μG] fun x => PiS (psiGen k r z c) π s (T0 u x)
      rw [hT0D u hu]
      filter_upwards [hconc] with x hx
      exact afun_mul_left hStd hSide hv ξ hu hs hx hSG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliEigenvalueKFiniteDiscreteSeriesCoeffStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_eigenvalue_kFinite_discreteSeries_coeff : PI.KFinSmooth → PI.DSInfCharCap.DSInfCharCap → PI.CapelliEig.CapEig := by
  first | exact @GlobalTheory.CapelliEigenvalue.capEig | exact GlobalTheory.CapelliEigenvalue.capEig | (intros; apply GlobalTheory.CapelliEigenvalue.capEig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DataConditionsOfGlobalAndRealRowsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataConditions_of_global_and_real_rows : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D → DuWin D C0 → StandingNumericalData D C0 := by
  first | exact @GlobalTheory.Diag.PG.data_of_rows | exact GlobalTheory.Diag.PG.data_of_rows | (intros; apply GlobalTheory.Diag.PG.data_of_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpInjectiveStrictUpperTriangular
section
open Matrix Filter Topology

namespace GlobalTheory.ExpStrictUpper

theorem conj_diagonal_eq {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i j, j ≤ i → X i j = 0)
    {τ : ℂ} (hτ : τ ≠ 0) :
    (Matrix.diagonal fun i : Fin m => (τ ^ (i : ℕ))⁻¹) * X *
      (Matrix.diagonal fun i : Fin m => τ ^ (i : ℕ)) =
      Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases h : j ≤ i
  · simp [hX i j h]
  · have hij : (i : ℕ) ≤ (j : ℕ) := by
      have := Fin.lt_def.mp (not_le.mp h)
      omega
    have hp : τ ^ (j : ℕ) = τ ^ (i : ℕ) * τ ^ ((j : ℕ) - (i : ℕ)) := by
      rw [← pow_add, Nat.add_sub_cancel' hij]
    rw [hp]
    calc (τ ^ (i : ℕ))⁻¹ * X i j * (τ ^ (i : ℕ) * τ ^ ((j : ℕ) - (i : ℕ)))
        = ((τ ^ (i : ℕ))⁻¹ * τ ^ (i : ℕ)) * (τ ^ ((j : ℕ) - (i : ℕ)) * X i j) := by ring
      _ = τ ^ ((j : ℕ) - (i : ℕ)) * X i j := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ hτ), one_mul]

theorem tendsto_scale {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i j, j ≤ i → X i j = 0) :
    Tendsto (fun τ : ℂ => (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j))
      (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun τ : ℂ => (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j)) :=
    continuous_matrix fun i j => by
      simp only [Matrix.of_apply]
      exact (continuous_pow _).mul continuous_const
  have h0 : (Matrix.of fun i j : Fin m => (0 : ℂ) ^ ((j : ℕ) - (i : ℕ)) * X i j) = 0 := by
    ext i j
    rw [Matrix.of_apply, Matrix.zero_apply]
    by_cases h : j ≤ i
    · rw [hX i j h, mul_zero]
    · have hn : (j : ℕ) - (i : ℕ) ≠ 0 := by
        have := Fin.lt_def.mp (not_le.mp h)
        omega
      rw [zero_pow hn, zero_mul]
  simpa only [h0] using hc.tendsto 0

theorem exp_inj_strictUpper : ∀ (m : ℕ) (X Y : Matrix (Fin m) (Fin m) ℂ),
    (∀ i j, j ≤ i → X i j = 0) → (∀ i j, j ≤ i → Y i j = 0) →
    NormedSpace.exp X = NormedSpace.exp Y → X = Y := by
  intro m X Y hX hY hXY
  obtain ⟨S, hS, hinj⟩ := (GlobalTheory.ExpBallNhds.exp_local_matrix (Fin m)).1
  have h1 : ∀ᶠ τ in 𝓝[≠] (0 : ℂ),
      (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j) ∈ S ∧
        (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * Y i j) ∈ S :=
    nhdsWithin_le_nhds (((tendsto_scale X hX).eventually_mem hS).and
      ((tendsto_scale Y hY).eventually_mem hS))
  have h2 : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), τ ≠ 0 := self_mem_nhdsWithin
  have hev := h1.and h2
  obtain ⟨τ, ⟨hxS, hyS⟩, hτ⟩ := hev.exists
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i : Fin m => τ ^ (i : ℕ) with hD
  set E : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i : Fin m => (τ ^ (i : ℕ))⁻¹ with hE
  have hDE : D * E = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (pow_ne_zero _ hτ)
  have hED : E * D = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (pow_ne_zero _ hτ)
  have hU : IsUnit D := ⟨⟨D, E, hDE, hED⟩, rfl⟩
  have hinv : D⁻¹ = E := Matrix.inv_eq_left_inv hED
  have hexp : ∀ Z : Matrix (Fin m) (Fin m) ℂ,
      NormedSpace.exp (E * Z * D) = E * NormedSpace.exp Z * D := by
    intro Z
    rw [← hinv]
    exact Matrix.exp_conj' D Z hU
  have hxS' : E * X * D ∈ S := by
    rw [hE, hD, conj_diagonal_eq X hX hτ]
    exact hxS
  have hyS' : E * Y * D ∈ S := by
    rw [hE, hD, conj_diagonal_eq Y hY hτ]
    exact hyS
  have key : E * X * D = E * Y * D :=
    hinj hxS' hyS' (by rw [hexp, hexp, hXY])
  calc X = (D * E) * X * (D * E) := by rw [hDE, one_mul, mul_one]
    _ = D * (E * X * D) * E := by simp only [mul_assoc]
    _ = D * (E * Y * D) * E := by rw [key]
    _ = (D * E) * Y * (D * E) := by simp only [mul_assoc]
    _ = Y := by rw [hDE, one_mul, mul_one]

end GlobalTheory.ExpStrictUpper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPowLeCardFlagQuotientStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_le_card_flag_quotient : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E) (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → IsLift Λ F → IsLift Λ F' → (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → Gval F F' ≠ 0 → Finite (BQ Λ F F') → NE (E := E) g ^ (r + 1) ≤ (Nat.card (BQ Λ F F') : ℝ) := by
  first | exact @GlobalTheory.LoopC.AdmissibleOrder.NE_pow_le_card_BQ | exact GlobalTheory.LoopC.AdmissibleOrder.NE_pow_le_card_BQ | (intros; apply GlobalTheory.LoopC.AdmissibleOrder.NE_pow_le_card_BQ <;> assumption)
end

