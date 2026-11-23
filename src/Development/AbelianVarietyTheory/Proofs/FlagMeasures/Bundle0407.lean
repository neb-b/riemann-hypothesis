module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselQuotientMassEqConstMulNormSqTranslates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGap
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFiniteBesselPeriodNeZeroGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselPeriodNonzeroGap

open Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity GlobalTheory.BesselPeriodNonzero


set_option maxHeartbeats 1600000 in
theorem nzOn_of_mass (hy : GlobalTheory.GapIn.Hyp) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {R : Rep k r}
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Mt k r)} {B l : R.H → Wp} {w : R.H} (hR : R.IsDS ε mu)
    (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hS : SideG k r z π u μW μN μG νq) (hB : IsBes R z π B) (hwK : R.KFin w) {c : ℝ} (hc : 0 ≤ c)
    (hiso : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = ENNReal.ofReal (c * ‖v‖ ^ 2))
    (h0 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0) (hl : IsBeL R z π μW μN l) :
    ∃ v ∈ R.sm, l v ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hK : PI.KFinSmooth := hy.1.1.2.2.1
  have hRG : R.IsDG ε mu := ⟨hR.1, hR.2, ⟨h, hgap, hok⟩⟩
  obtain ⟨hmul, hone, hun, hsm, hTK, hTKs, hKT, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have hwT := hKT w hwK
  have hw := hTK w hwT
  have hΦ := fun v hv => (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r ε mu R hR Wp B hB.1 hB.2.1 hB.2.2.2 v hv).1
  have hS' := hS
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hWh, hNh, hGh, hq⟩ := hS'
  have := hWh.1; have := hNh.1; have := hGh.1
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hof : Continuous (fun y : Mt k r => (Matrix.of y : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_id
  have hSeq : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN = (μW.prod μN).map (fun p => mulMt p.1 p.2) := rfl
  have hsf : SFinite (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) := by rw [hSeq]; infer_instance
  have hGm : MeasurableSet {y : Mt k r | Matrix.of y ∈ GG k r} := (isClosed_UH.preimage hof).measurableSet
  have hSae : ∀ᵐ s ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN), Matrix.of s ∈ GG k r := by
    rw [hSeq]
    refine (ae_map_iff measurable_mulMt.aemeasurable hGm).2 ?_
    filter_upwards [hPae] with p hp
    exact Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hS0 : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN ≠ 0 := GlobalTheory.SideCompare.muS_ne_zero hWh.2.1 hNh.2.1
  have hνae := GlobalTheory.BesselNorm.quot_ae hq hGae hSae hS0
  have hνs : SigmaFinite νq := GlobalTheory.SideCompare.sigmaFinite_of_isQuotMeas hS0 hq
  have hSC : SecondCountableTopology Wp := by
    have := FiniteDimensional.proper ℂ Wp
    infer_instance
  have one_mem : (1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) ∈ GG k r := by
    show (1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)ᴴ * Hpk k r * 1 = Hpk k r; simp
  have memDD : ∀ g ∈ GG k r, R.σ g w ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w :=
    fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have wDD : w ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w := by
    have := memDD 1 one_mem; rwa [hone] at this
  have DDsm : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, v ∈ R.sm := by
    intro v hv
    refine hTK v (Submodule.span_le.2 ?_ hv)
    rintro _ ⟨g, hg, rfl⟩
    exact hTKs g hg w hwT
  have hnorm : ∀ g ∈ GG k r, ‖R.σ g w‖ = ‖w‖ := fun g hg => (sigma_facts hR.2).2 g hg w
  have hcw : c * ‖w‖ ^ 2 ≠ 0 := by
    intro h1; apply h0; rw [hiso w wDD, h1, ENNReal.ofReal_zero]
  have hmeas : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      AEStronglyMeasurable (fun y : Mt k r => B (R.σ (Matrix.of y) v)) νq := fun v hv =>
    aesm_of_contOn ((hΦ v (DDsm v hv)).comp hof.continuousOn fun y hy => hy) hGm hνae
  have hsq : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      Integrable (fun y : Mt k r => ‖B (R.σ (Matrix.of y) v)‖ ^ 2) νq ∧
        ∫ y : Mt k r, ‖B (R.σ (Matrix.of y) v)‖ ^ 2 ∂νq = c * ‖v‖ ^ 2 := fun v hv =>
    sq_int (hmeas v hv) (by positivity) (hiso v hv)

  have hpair : ∀ a ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, ∀ b ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w,
      Integrable (fun y : Mt k r => ⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ) νq ∧
      ∫ y : Mt k r, ‖⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ‖ ∂νq ≤ c * ‖a‖ ^ 2 + c * ‖b‖ ^ 2 ∧
      (∫ y : Mt k r, ⟪B (R.σ (Matrix.of y) a), B (R.σ (Matrix.of y) b)⟫_ℂ ∂νq).re = c * (⟪a, b⟫_ℂ).re := by
    intro a ha b hb
    obtain ⟨i1, i2, i3⟩ := inner_int (hmeas a ha) (hmeas b hb) (hsq a ha).1 (hsq b hb).1
    have e : ∫ y : Mt k r, ‖B (R.σ (Matrix.of y) a) + B (R.σ (Matrix.of y) b)‖ ^ 2 ∂νq = c * ‖a + b‖ ^ 2 := by
      rw [← (hsq (a + b) (Submodule.add_mem _ ha hb)).2]
      apply integral_congr_ae
      filter_upwards [hνae] with y hy
      rw [map_add (f := _), hB.1 _ (hsm _ hy a (DDsm a ha)) _ (hsm _ hy b (DDsm b hb))]
    rw [(hsq a ha).2, (hsq b hb).2] at i2 i3
    rw [e, norm_add_sq (𝕜 := ℂ)] at i3
    refine ⟨i1, i2, ?_⟩
    simp only [RCLike.re_to_complex] at i3
    linarith

  set m : Mt k r → ℂ := fun g => ⟪w, R.σ (Matrix.of g) w⟫_ℂ with hm
  have hmc : ContinuousOn m {y : Mt k r | Matrix.of y ∈ GG k r} :=
    continuousOn_const.inner ((hcont w).comp hof.continuousOn fun y hy => hy)
  have hmi : Integrable m μG := by
    obtain ⟨C, Ws, -, hd⟩ := Gp91.GlobalTheory.BesselDecay.decay_TK hy.1 k r ε mu h R hRG hgap hok w hwT
    obtain ⟨-, -, t1, t2⟩ := GlobalTheory.thresholds_of_gapOK k r h hok
    have hg := GlobalTheory.gN_rpow_neg_integrable_haar k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) hGh (by linarith)
    refine (hg.const_mul (C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum)).mono'
      (aesm_of_contOn hmc hGm hGae) ?_
    filter_upwards [hGae] with y hy
    rw [neg_sub]
    exact hd w hw _ hy

  set F : Mt k r × Mt k r → ℂ := fun q =>
    star (m q.1) * ⟪B (R.σ (Matrix.of q.2) w), B (R.σ (Matrix.of q.2 * Matrix.of q.1) w)⟫_ℂ with hF
  have hFm : AEStronglyMeasurable F (μG.prod νq) := by
    have c1 : Continuous (fun q : Mt k r × Mt k r => (Matrix.of q.1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_fst
    have c2 : Continuous (fun q : Mt k r × Mt k r => (Matrix.of q.2 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) := continuous_snd
    refine aesm_of_contOn (s := {q : Mt k r × Mt k r | Matrix.of q.1 ∈ GG k r ∧ Matrix.of q.2 ∈ GG k r}) ?_
      ((isClosed_UH.preimage c1).inter (isClosed_UH.preimage c2)).measurableSet
      ((Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hνae))
    let hs : Set (Mt k r × Mt k r) := {q | Matrix.of q.1 ∈ GG k r ∧ Matrix.of q.2 ∈ GG k r}
    exact (continuous_star.comp_continuousOn (hmc.comp (s := hs) continuous_fst.continuousOn fun q hq => hq.1)).mul
      (((hΦ w hw).comp (s := hs) c2.continuousOn fun q hq => hq.2).inner
        ((hΦ w hw).comp (s := hs) (c2.matrix_mul c1).continuousOn fun q hq => Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hq.2 hq.1))
  have hF1 : ∀ g : Mt k r, Matrix.of g ∈ GG k r → (fun y => F (g, y)) =ᵐ[νq] fun y =>
      star (m g) * ⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ := by
    intro g hg
    filter_upwards [hνae] with y hy
    simp only [hF]
    rw [hmul _ hy _ hg]
  have hF2 : ∀ g : Mt k r, Matrix.of g ∈ GG k r → (fun y => F (g, y)) =ᵐ[νq] fun y =>
      ⟪B (R.σ (Matrix.of y) (m g • w)), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ := by
    intro g hg
    filter_upwards [hνae, hF1 g hg] with y hy h1
    rw [h1, map_smul, hB.2.1 _ _ (hsm _ hy w hw), inner_smul_left]
    rfl
  have hFi : Integrable F (μG.prod νq) := by
    rw [integrable_prod_iff hFm]
    constructor
    · filter_upwards [hGae] with g hg
      exact ((hpair w wDD _ (memDD _ hg)).1.const_mul _).congr (hF1 g hg).symm
    · refine (hmi.norm.mul_const (c * ‖w‖ ^ 2 + c * ‖w‖ ^ 2)).mono' hFm.norm.integral_prod_right' ?_
      filter_upwards [hGae] with g hg
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      have e : ∫ y, ‖F (g, y)‖ ∂νq = ‖m g‖ *
          ∫ y : Mt k r, ‖⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of y) (R.σ (Matrix.of g) w))⟫_ℂ‖ ∂νq := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hF1 g hg] with y hy
        rw [hy, norm_mul, norm_star]
      rw [e]
      have := (hpair w wDD _ (memDD _ hg)).2.1
      rw [hnorm _ hg] at this
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

  have hzero : ∫ q, F q ∂(μG.prod νq) = 0 := by
    rw [integral_prod_symm F hFi]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hνae, hFi.prod_left_ae] with y hy hi
    set f : Mt k r → ℂ := fun g => star ⟪R.σ (Matrix.of y) w, R.σ (Matrix.of g) w⟫_ℂ *
      ⟪B (R.σ (Matrix.of y) w), B (R.σ (Matrix.of g) w)⟫_ℂ with hf
    have hfc : ContinuousOn f {y : Mt k r | Matrix.of y ∈ GG k r} :=
      (continuous_star.comp_continuousOn (continuousOn_const.inner
        ((hcont w).comp hof.continuousOn fun y hy => hy))).mul
        (continuousOn_const.inner ((hΦ w hw).comp hof.continuousOn fun y hy => hy))
    have hfm : AEStronglyMeasurable f (μG.map (lmulM (Matrix.of y))) := by
      rw [hGh.2.2.2 _ hy]; exact aesm_of_contOn hfc hGm hGae
    have hlm : Measurable (lmulM (k := k) (r := r) (Matrix.of y)) :=
      measurable_mulMt.comp (measurable_const.prodMk measurable_id : Measurable fun x : Mt k r => (y, x))
    have e : (fun g => F (g, y)) =ᵐ[μG] f ∘ lmulM (Matrix.of y) := by
      filter_upwards [hGae] with g hg
      show star ⟪w, R.σ (Matrix.of g) w⟫_ℂ * _ = star ⟪R.σ (Matrix.of y) w, R.σ (Matrix.of y * Matrix.of g) w⟫_ℂ * _
      rw [hmul _ hy _ hg w, hun _ hy, ← hmul _ hy _ hg w]
      rfl
    have hfi : Integrable f μG := by
      rw [← hGh.2.2.2 _ hy]
      exact (integrable_map_measure hfm hlm.aemeasurable).2 (hi.congr e)
    have e2 : ∫ g, F (g, y) ∂μG = ∫ g, f g ∂μG := by
      rw [integral_congr_ae e]
      conv_rhs => rw [← hGh.2.2.2 _ hy]
      exact (integral_map hlm.aemeasurable hfm).symm
    rw [e2]
    refine unfold_zero hK hR hS hB hw (fun x hx => ?_) _ hfi
    obtain ⟨j1, j2⟩ := hl.2 x hx _ (hTKs _ hy w hwT)
    refine ⟨j1, ?_⟩
    rw [j2, hcon x hx]
    ext ξ; simp

  obtain ⟨d, hd, hSch⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hy.1 k r ε μG hGh
  obtain ⟨s1, s2⟩ := (hSch mu R hRG).2 w w w w
  have hdpos : 0 < d * fdegHC mu := mul_pos hd (GlobalTheory.BesselNorm.fdegHC_pos mu hR.1.1.injective)
  have hre : (∫ q, F q ∂(μG.prod νq)).re = c * (∫ g, m g * star (m g) ∂μG).re := by
    rw [integral_prod F hFi]
    have a1 := integral_re hFi.integral_prod_left
    have a2 := integral_re s1
    simp only [RCLike.re_to_complex] at a1 a2
    rw [← a1, ← a2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hGae] with g hg
    rw [integral_congr_ae (hF2 g hg), (hpair _ (Submodule.smul_mem _ _ wDD) _ (memDD _ hg)).2.2, inner_smul_left,
      mul_comm ((starRingEnd ℂ) (m g))]
    rfl
  rw [hzero, s2, inner_self_eq_norm_sq_to_K] at hre
  have e3 : (((‖w‖ : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / ((d * fdegHC mu : ℝ) : ℂ))).re =
      ‖w‖ ^ 2 * ‖w‖ ^ 2 / (d * fdegHC mu) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre' : 0 = c * (‖w‖ ^ 2 * ‖w‖ ^ 2 / (d * fdegHC mu)) := by rw [← e3]; exact hre
  have hw2 : ‖w‖ ^ 2 ≠ 0 := right_ne_zero_of_mul hcw
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcw
  exact mul_ne_zero hc0 (div_ne_zero (mul_ne_zero hw2 hw2) hdpos.ne') hre'.symm

theorem exists_kFin_period_ne_zero : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Mt k r)) (B l : R.H → Wp) (w : R.H), R.IsDS ε mu → GapAtLeast ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → SideG k r z π u μW μN μG νq → IsBes R z π B → R.KFin w → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0 → PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤ → IsBeL R z π μW μN l → ∃ v, R.KFin v ∧ l v ≠ 0 := by
  intro hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq B l w hR hgap hok hS hB hwK h0 hfin hl
  have hK : PI.KFinSmooth := hy.1.1.2.2.1
  have hw : w ∈ R.sm := hK k r ε mu R.H R.σ hR.1 hR.2 w hwK
  obtain ⟨c, hc, hiso⟩ := _root_.GlobalTheory.BesselIsometry.besselQuotientMass_eq_const_mul_norm_sq_translates k r ε mu R Wp z π u μW μN μG νq B w hR hS hB hw hfin
  exact GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r ε mu R hR Wp l hl.1.1 hl.1.2.1 hl.1.2.2.2
    (nzOn_of_mass hy hR hgap hok hS hB hwK hc hiso h0 hl)

end GlobalTheory.BesselPeriodNonzeroGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDoubleCosetsRationalLocalLatticeStabilizer
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblCos

variable {D : D7}

theorem img_mul (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (a b : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p)) :
    LocNG.img (a * b) Λ = LocNG.img a (LocNG.img b Λ) := by
  ext x
  simp only [LocNG.img, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem img_one (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (Λ : Submodule (M p).L.O (Vp D p)) : LocNG.img (1 : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) Λ = Λ := by
  ext x
  simp [LocNG.img]

theorem mem_Aut_iff (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p)) :
    g ∈ LocNG.Aut Λ ↔ LocNG.img g Λ = Λ := by
  constructor
  · intro hg

    let K : Subgroup (Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) :=
      { carrier := {a | LocNG.img a Λ = Λ}
        mul_mem' := fun {a b} ha hb => by
          have ha' : LocNG.img a Λ = Λ := ha
          have hb' : LocNG.img b Λ = Λ := hb
          show LocNG.img (a * b) Λ = Λ
          rw [img_mul p M, hb', ha']
        one_mem' := img_one p M Λ
        inv_mem' := fun {a} ha => by
          have ha' : LocNG.img a Λ = Λ := ha
          show LocNG.img a⁻¹ Λ = Λ
          calc LocNG.img a⁻¹ Λ = LocNG.img a⁻¹ (LocNG.img a Λ) := by rw [ha']
            _ = Λ := by rw [← img_mul p M, inv_mul_cancel, img_one p M] }
    exact (Subgroup.closure_le K).2 (fun a ha => ha) hg
  · intro h
    exact Subgroup.subset_closure h

theorem span_img (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p))
    (h : Submodule.span (D.s.atP p).Ep (Λ : Set (Vp D p)) = ⊤) :
    Submodule.span (D.s.atP p).Ep (LocNG.img g Λ : Set (Vp D p)) = ⊤ := by
  have himg : (LocNG.img g Λ : Set (Vp D p)) = (g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) '' (Λ : Set (Vp D p)) := by
    ext x
    simp [LocNG.img]
  rw [himg, Submodule.span_image, h, Submodule.map_top]
  exact LinearEquiv.range g

theorem img_key (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (c g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (A B C : Submodule (M p).L.O (Vp D p))
    (h1 : C = LocNG.img c B) (h2 : C = LocNG.img g A) : LocNG.img (c⁻¹ * g) A = B := by
  rw [img_mul p M, ← h2, h1, ← img_mul p M, inv_mul_cancel, img_one p M]

theorem img_key' (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (c s g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (A B C : Submodule (M p).L.O (Vp D p))
    (h1 : C = LocNG.img c B) (h2 : C = LocNG.img g A) (h3 : LocNG.img s A = B) :
    LocNG.img ((c * s)⁻¹ * g) A = A := by
  rw [mul_inv_rev, mul_assoc, img_mul p M, img_key p M c g A B C h1 h2, ← h3, ← img_mul p M,
    inv_mul_cancel, img_one p M]

private theorem latP_fg_and_span_eq_top (Z : LocDat D) (Λ : LV D) (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  haveI : Submodule.IsLattice D.host.E (GlobalTheory.Unfold.LatLoc.cL Λ) :=
    GlobalTheory.Unfold.LatLoc.isLattice_map (GlobalTheory.Unfold.LatLoc.cE D) Λ hΛ.toIsLattice
  have hc : Submodule.IsFullLattice D.host.E (GlobalTheory.Unfold.LatLoc.cL Λ) := by
    refine { span_eq_top := ?_ }
    change Submodule.span D.host.E ((GlobalTheory.Unfold.LatLoc.cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [← Submodule.map_span, hΛ.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have h := (_root_.GlobalTheory.HL.PlacesRec.lattice_local (GlobalTheory.HL.placesOf Z) (nV D) (GlobalTheory.Unfold.LatLoc.cL Λ) hc).2.1 p
  rw [GlobalTheory.Unfold.LatLoc.localLattice_eq]
  exact h

private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)


private theorem gmap_inv_gmap_flag_measures (γ : GV D) (L : LV D) :
    Formalism.HermitianLatticesTheory.gmap γ⁻¹ (Formalism.HermitianLatticesTheory.gmap γ L) = L := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hz' : (γ⁻¹ : GV D) (γ z) = z := γ.symm_apply_apply z
    rw [hz']
    exact hz
  · intro hx
    refine ⟨γ x, ⟨x, hx, rfl⟩, ?_⟩
    exact γ.symm_apply_apply x

end GlobalTheory.DblCos


open GlobalTheory.DblCos in
set_option maxHeartbeats 5000000 in
theorem GlobalTheory.DblCos.finite_double_cosets : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ S : Finset (∀ p, ↥(FP p).UW0), (∀ s ∈ S, {p | ((s p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite) ∧ ∀ g : ∀ p, ↥(FP p).UW0, {p | ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → ∃ s ∈ S, ∃ h : ↥(FlagPairStabilizer F F'), ∃ k : ∀ p, ↥(FP p).UW0, (∀ p, ((k p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)) ∧ g = φ h * s * k := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀
  obtain ⟨-, -, hLat, -⟩ := _root_.GlobalTheory.RatLocMove.rat_ext_moves D X Y u u' F F' w hw hG Z FP hB hR
  obtain ⟨-, Slat, hSlat⟩ := _root_.GlobalTheory.Unfold.ClFin.classes_finite D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  obtain ⟨hcmp, hglue⟩ := _root_.GlobalTheory.Unfold.LatLoc.lattices_local_global D Z

  let fam : LV D → ∀ p, ↥(FP p).UW0 := fun Λs p =>
    if hc : (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) ∧
        lattice₂ D Z.M p Λs ≠ lattice₂ D Z.M p Λ₀ then ⟨hc.1.choose, hc.1.choose_spec.1⟩ else 1
  have fam_one : ∀ Λs p, lattice₂ D Z.M p Λs = lattice₂ D Z.M p Λ₀ → fam Λs p = 1 := by
    intro Λs p he
    simp only [fam]
    rw [dite_eq_right]
    exact fun hc => hc.2 he
  have fam_spec : ∀ Λs p, (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) →
      LocNG.img ((fam Λs p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀) =
        lattice₂ D Z.M p Λs := by
    intro Λs p hex
    by_cases he : lattice₂ D Z.M p Λs = lattice₂ D Z.M p Λ₀
    · rw [fam_one Λs p he, he]
      exact img_one p Z.M _
    · have hc : (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) ∧
          lattice₂ D Z.M p Λs ≠ lattice₂ D Z.M p Λ₀ := ⟨hex, he⟩
      simp only [fam, dif_pos hc]
      exact hc.1.choose_spec.2
  refine ⟨(Slat.filter (fun Λs => Submodule.IsFullLattice D.host.E Λs)).image fam, ?_, ?_⟩
  ·
    intro s hs
    obtain ⟨Λs, hmem, rfl⟩ := Finset.mem_image.1 hs
    have hL : Submodule.IsFullLattice D.host.E Λs := (Finset.mem_filter.1 hmem).2
    apply (hcmp Λs Λ₀ hL hΛ₀).1.subset
    intro p hp
    by_contra he
    apply hp
    rw [fam_one Λs p (not_not.1 he)]
    exact (mem_Aut_iff p Z.M _ _).2 (img_one p Z.M _)
  · intro g hg

    obtain ⟨Λ, hΛ, hΛp⟩ := hglue Λ₀ hΛ₀
      (fun p => LocNG.img ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀))
      (fun p => by
        obtain ⟨hfg, hspan⟩ := latP_fg_and_span_eq_top Z Λ₀ hΛ₀ p
        exact ⟨hfg.map _, span_img p Z.M _ _ hspan⟩)
      (by
        apply hg.subset
        intro p hp hmem
        exact hp ((mem_Aut_iff p Z.M _ _).1 hmem))
    obtain ⟨Λs, hΛsS, γ, hγ, hγΛ⟩ := hSlat Λ hΛ (fun p => ⟨_, (g p).2, (hΛp p).symm⟩)
    have hΛfull : Submodule.IsFullLattice D.host.E Λ := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
      apply isFullLattice_of_local_span Z p Λ hΛ
      rw [hΛp p]
      exact span_img p Z.M _ _ (latP_fg_and_span_eq_top Z Λ₀ hΛ₀ p).2
    have hΛsL : Submodule.IsFullLattice D.host.E Λs := by
      have hfull : Submodule.IsFullLattice D.host.E (Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ) := by
        refine { toIsLattice := GlobalTheory.RatLocMove.isLattice_gmap' γ⁻¹ Λ hΛ, span_eq_top := ?_ }
        change Submodule.span D.host.E (((γ⁻¹ : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λ : Set (VS D).V)) = ⊤
        rw [Submodule.span_image, hΛfull.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
        exact (γ⁻¹ : GV D).surjective
      rwa [← hγΛ, gmap_inv_gmap_flag_measures] at hfull
    let hh : ↥(FlagPairStabilizer F F') := ⟨γ, (mem_H0sub F F' γ).2 hγ⟩
    let s := fam Λs
    refine ⟨s, Finset.mem_image.2 ⟨Λs, Finset.mem_filter.2 ⟨hΛsS, hΛsL⟩, rfl⟩, hh,
      s⁻¹ * (φ hh)⁻¹ * g, ?_, by group⟩
    intro p

    have hC1 : lattice₂ D Z.M p Λ = LocNG.img ((φ hh p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
        (lattice₂ D Z.M p Λs) := by
      rw [← hγΛ]
      exact hLat γ p _ Λs (hφ hh p)
    have hC2 := hΛp p
    have hex : ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs :=
      ⟨(((φ hh p)⁻¹ * g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p), ((φ hh p)⁻¹ * g p).2, by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, img_mul p Z.M, ← hC2, hC1, ← img_mul p Z.M,
          inv_mul_cancel, img_one p Z.M]⟩
    have hs := fam_spec Λs p hex
    rw [mem_Aut_iff p Z.M]
    have key := img_key' p Z.M _ _ _ _ _ _ hC1 hC2 hs
    simpa [Pi.mul_apply, Pi.inv_apply, mul_inv_rev, mul_assoc] using key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PgFrameAtRecord
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem pgFrame_at_record : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → C0 * Real.exp 8 ≤ D.R.k → LocalBesselAndTopKernel.FamilyMidVolume D → Formalism.L2.SG.RowsConc.TFrameAt D ∧ UnitaryVolumeMass.cTvA D ∧ UnitaryVolumeMass.cTvD D 1 ∧ ∀ w τ, (D.R.k : ℝ) ^ (3 * D.R.rS) ≤ gg D ^ (-(D.R.m : ℝ)) * Tcrit D w τ := by
  intro hSM hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT h h40 hCu hk hR
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  have hyp : LocalBesselAndTopKernel.hyp D large₂ C0 C' Cl Cg cb Cu cT CT := ⟨h.2.1, h.1, h.2.2⟩
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hg : LocalBesselAndTopKernel.MidVolumeChain D large₂ (1 / 3) 0 :=
    Formalism.L2.SG.Pf.SzHypFam.midVolumeChain_of_standingHypotheses hT h.1 (by nlinarith) (by norm_num) le_rfl
  have hD : UnitaryVolumeMass.cTvD D 1 :=
    Formalism.MainNotions.BridgeLemma.critical_level_lower_bound (C3' := 1) h40 (by norm_num) le_rfl hyp hg
  have hA : UnitaryVolumeMass.cTvA D :=
    Formalism.MainNotions.BridgeLemma.degree_ratio_formula_statement D large₂ C0 C' Cl Cg cb Cu cT CT
      (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hSM D) (Formalism.MainNotions.BridgeLemma.mass_two_bound_single_holds D) hR hyp
  have F := Formalism.MainNotions.BridgeLemma.tfFacts_of h
  have hm : 2 * (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; norm_num; exact_mod_cast this
  exact ⟨fun w => F.tframe (by linarith) hm hCu hA hD hk w, hA, hD,
    fun w τ => F.tcritLow (by linarith) hm hCu hD w τ⟩

end GlobalTheory
end

