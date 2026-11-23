module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstant
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNormSq

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_sum_sum {m : ℕ} (A C : Fin m → (Wq →L[ℂ] Wp)) :
    B.hsInner (∑ i, A i) (∑ j, C j) = ∑ i, ∑ j, B.hsInner (A i) (C j) := by
  have h : ∀ A : Fin m → (Wq →L[ℂ] Wp), B.hsVec (∑ i, A i) = ∑ i, B.hsVec (A i) := by
    intro A
    ext t
    simp [B.hsVec, ContinuousLinearMap.sum_apply]
  unfold B.hsInner
  rw [h, h, inner_sum]
  exact Finset.sum_congr rfl fun i _ => sum_inner _ _ _

theorem Ph_sum [FiniteDimensional ℂ Wp] (D : B.RealPlaceData k r Wp Wq) {m : ℕ} (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (f : Fin m → B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ g ∈ B.GV k r, F g = ∑ i, f i g) (p : B.SS k r)
    (hp : D.inSS p)
    (hint : ∀ i j, Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
      B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g))) D.μG) :
    B.Ph D F F p = ∑ i, ∑ j, B.Ph D (f i) (f j) p := by
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ B.GV k r := D.haarG.conc
  unfold B.Ph
  have e1 : ∀ i, ∑ j, ∫ g, B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g)) ∂D.μG =
      ∫ g, ∑ j, B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g)) ∂D.μG :=
    fun i => (integral_finsetSum _ fun j _ => hint i j).symm
  simp only [e1]
  rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine integral_congr_ae (hae.mono fun g hg => ?_)
  have h1 : B.rho D p F (Matrix.of g) = ∑ i, B.rho D p (f i) (Matrix.of g) := by
    unfold B.rho
    rw [hF _ (Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hg)]
    ext v
    simp [ContinuousLinearMap.sum_apply]
  simp only
  rw [h1, hF _ hg, hsInner_sum_sum]

theorem normSq_coef : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ F s, IsCoef R l l' F s → B.normSq D F = ENNReal.ofReal (c * ‖s‖ ^ 2 / dd) := by
  intro H k r Wp _ _ _ _ Wq _ _ _ _ D
  obtain ⟨c, hc, hnb⟩ := _root_.GlobalTheory.BesselNorm.normSq_eq_betaInf k r Wp Wq D
  refine ⟨c, hc, ?_⟩
  intro ε mu h R l l' dd hDS hgap hok hl hl' hdd F s hF
  have hA := (_root_.GlobalTheory.thresholds_of_gapOK k r h hok).2.1
  have hcc := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap H k r ε mu h R Wp Wq l l' F s hDS hgap hok hF).2
  obtain ⟨m, x, y, X, hxy, hFg, hs⟩ := hF
  set f : Fin m → B.Mat k r → (Wq →L[ℂ] Wp) := fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i with hf
  have hI := fun i j => GlobalTheory.T.bessel_formal_degree_pairing H k r ε mu h R Wp Wq D l l' dd hDS hgap hok hl hl' hdd
    (x i) (hxy i).1 (y i) (hxy i).2 (x j) (hxy j).1 (y j) (hxy j).2 (X i) (X j)
  have hPh : B.Ph D F F =ᵐ[D.μSS] fun p => ∑ i, ∑ j, B.Ph D (f i) (f j) p :=
    (Formalism.FourierDecayAlt.P.B6.ae_inSS D).mono fun p hp => Ph_sum D F f hFg p hp fun i j =>
      (GlobalTheory.T.bessel_formal_degree_identity H k r ε mu R Wp Wq D dd hDS hdd (x i) (y i) (x j) (y j) (X i) (X j) p hp).1
  have hint : Integrable (B.Ph D F F) D.μSS :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hI i j).1).congr hPh.symm
  have hxi : ∀ i j, Integrable (fun p => B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p) D.μSS := by
    intro i j
    refine Integrable.bdd_mul (c := 1) (hI i j).1 ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have c1 : Continuous fun p : B.SS k r => B.lam k r D.z (Matrix.of p.1.2) :=
        (Formalism.FourierDecayAlt.P.B6.lam_continuous k r D.z).comp (continuous_snd.comp continuous_fst)
      have c2 : Continuous fun p : B.SS k r => B.lam k r D.z' (Matrix.of p.2.2) :=
        (Formalism.FourierDecayAlt.P.B6.lam_continuous k r D.z').comp (continuous_snd.comp continuous_snd)
      unfold B.xiTau
      exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_const.mul c1).sub (continuous_const.mul c2))))
    · unfold B.xiTau
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hb : B.betaInf D F F = ((‖s‖ ^ 2 / dd : ℝ) : ℂ) := by
    rw [_root_.GlobalTheory.RegularisedIntegral.betaInf_eq_integral k r Wp Wq D _ F hA (hcc 4) hint]
    have e0 : ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS =
        ∫ p, ∑ i, ∑ j, B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p ∂D.μSS := by
      refine integral_congr_ae (hPh.mono fun p hp => ?_)
      simp only [hp, Finset.mul_sum]
    rw [e0, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hxi i j]
    have e1 : ∀ i, ∫ p, ∑ j, B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p ∂D.μSS =
        ∑ j, ⟪l (x i), X i (l' (y i))⟫_ℂ * star ⟪l (x j), X j (l' (y j))⟫_ℂ / (dd : ℂ) := by
      intro i
      rw [integral_finsetSum _ fun j _ => hxi i j]
      exact Finset.sum_congr rfl fun j _ => (hI i j).2
    simp only [e1]
    have e2 : ((‖s‖ ^ 2 / dd : ℝ) : ℂ) = s * star s / (dd : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [e2, hs, star_sum, Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]
  rw [hnb _ F hA (hcc 5), hb, ← Complex.ofReal_mul, Complex.ofReal_re, mul_div_assoc]

end GlobalTheory.BesselNormSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaCutFTendsto
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

namespace GlobalTheory.BetaCutLimit

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end GlobalTheory.BetaCutLimit

namespace GlobalTheory

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem exists_CCle_four_of_inCC_five {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ}
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) : ∃ c, _root_.Formalism.FourierDecayAlt.B.CCle A 4 G c := by
  unfold _root_.Formalism.FourierDecayAlt.B.InCC _root_.Formalism.FourierDecayAlt.B.CCle at hG
  obtain ⟨c, h1, h2⟩ := hG
  exact ⟨c, _root_.Formalism.FourierDecayAlt.P.B5.ckOn_mono (by norm_num) h1, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem measurableSet_Qset' (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) : MeasurableSet (_root_.Formalism.FourierDecayAlt.B.Qset Bs) :=
  measurableSet_lt measurable_const (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem aestronglyMeasurable_Qset_indicator_hsVec (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : ContinuousOn G (_root_.Formalism.FourierDecayAlt.B.GV k r)) :
    AEStronglyMeasurable ((_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
      volume := by
  refine (aestronglyMeasurable_indicator_iff (measurableSet_Qset' Bs)).2 ?_
  have h := _root_.Formalism.FourierDecayAlt.P.B7.jc_aesm_J Bs hG (1, 1)
  simp only [_root_.Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs G] at h
  exact _root_.Formalism.FourierDecayAlt.P.JCTx2.hsVec_cont'.comp_aestronglyMeasurable h

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem mem_Qset_iff_bcWeight_pos (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) :
    q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs ↔ 0 < _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q := Iff.rfl

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem aestronglyMeasurable_weighted_pairing_lemma_2 (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {G G' : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : ContinuousOn G (_root_.Formalism.FourierDecayAlt.B.GV k r))
    (hG' : ContinuousOn G' (_root_.Formalism.FourierDecayAlt.B.GV k r)) :
    AEStronglyMeasurable (fun q : (Fin r → ℂ) × ℂ =>
      (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
        inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G' (_root_.Formalism.FourierDecayAlt.B.gq Bs q))))
      volume := by
  have h := (Complex.continuous_ofReal.measurable.comp (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight (k := k) (r := r)
    (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z'))).aestronglyMeasurable.mul
    ((aestronglyMeasurable_Qset_indicator_hsVec Bs hG).inner (aestronglyMeasurable_Qset_indicator_hsVec Bs hG'))
  refine h.congr (Eventually.of_forall fun q => ?_)
  by_cases hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs
  · simp only [Pi.mul_apply, Function.comp_apply, Set.indicator_of_mem hq]
  · have hw : _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q = 0 :=
      le_antisymm (not_lt.1 ((mem_Qset_iff_bcWeight_pos Bs q).not.1 hq)) (_root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q)
    simp only [Pi.mul_apply, Function.comp_apply, hw, Complex.ofReal_zero, zero_mul]


open Filter Topology MeasureTheory in
theorem _root_.GlobalTheory.beta_cutF_tendsto : _root_.GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (A : ℝ) (X F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.C6.IsCut0 χ → _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A → _root_.Formalism.FourierDecayAlt.B.InCC A 5 X → _root_.Formalism.FourierDecayAlt.B.InCC A 5 F → Tendsto (fun ε : ℝ => _root_.Formalism.FourierDecayAlt.B.beta Bs X (_root_.Formalism.FourierDecayAlt.D.cutF Bs χ F ε)) (𝓝[>] 0) (𝓝 (_root_.Formalism.FourierDecayAlt.B.beta Bs X F)) := by
  intro hHC k r Wp Wq _ _ _ _ _ _ Bs χ A X F hχ hA hX hF
  have hint := _root_.GlobalTheory.betaIntegrand_integrable_of_xiExists
    (_root_.GlobalTheory.HCXi.xiExists_of_besselXiIntegrable hHC) k r Wp Wq Bs A X F hA hX hF
  obtain ⟨M, -, hM⟩ := _root_.Formalism.FourierDecayAlt.P.JCTx2.cut_bound hχ
  have hχ' := hχ
  unfold _root_.Formalism.FourierDecayAlt.C6.IsCut0 at hχ'
  obtain ⟨hχc, -, hχ1⟩ := hχ'
  obtain ⟨cF, hcF⟩ := exists_CCle_four_of_inCC_five hF
  obtain ⟨cX, hcX⟩ := exists_CCle_four_of_inCC_five hX
  have hFc : ContinuousOn F (_root_.Formalism.FourierDecayAlt.B.GV k r) := _root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cF, hcF⟩)
  have hXc : ContinuousOn X (_root_.Formalism.FourierDecayAlt.B.GV k r) := _root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cX, hcX⟩)
  have hcut : ∀ ε q, (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
      inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs (_root_.Formalism.FourierDecayAlt.D.cutF Bs χ F ε) (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
        (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) =
      (χ (_root_.Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' (_root_.Formalism.FourierDecayAlt.B.gq Bs q) / ε) : ℂ) *
        ((_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
          inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))) := by
    intro ε q
    rw [_root_.Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, _root_.Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_left, Complex.conj_ofReal]
    ring
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun ε q => (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
      inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs (_root_.Formalism.FourierDecayAlt.D.cutF Bs χ F ε) (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
        (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q))))
    (fun q => M * ‖(_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
      inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))‖)
    (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => Eventually.of_forall fun q => ?_)
    (hint.norm.const_mul M) ?_
  · refine aestronglyMeasurable_weighted_pairing_lemma_2 Bs ?_ hXc
    have hcont : ContinuousOn (fun g => ((χ (_root_.Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • F g)
        (_root_.Formalism.FourierDecayAlt.B.GV k r) :=
      ((Complex.continuous_ofReal.comp (hχc.continuous.comp
        ((_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont Bs.z Bs.z').div_const ε))).continuousOn).smul hFc
    exact hcont
  · rw [hcut, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  · filter_upwards [_root_.Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero Bs] with q hq
    simp_rw [hcut]
    rcases hq with hq | hq
    · have hG : 0 < _root_.Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' (_root_.Formalism.FourierDecayAlt.B.gq Bs q) := (_root_.Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs (by exact hq)).2.2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT hG] with ε hε
      rw [hχ1 _ ((one_le_div hε.1).2 hε.2), Complex.ofReal_one, one_mul]
      rfl
    · simp only [hq, Complex.ofReal_zero, zero_mul, mul_zero]
      exact tendsto_const_nhds

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingNormLe
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_capelliFold_norm_le : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Z : B.Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ), B.CkOn ⊤ (B.GV k r) X → B.CCle A (5 + w.length * (2 * r + k + 1)) X c → B.CCle A 5 Z c' → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z‖ ≤ C * c * c' := by
  intro k r Wp Wq _ _ _ _ _ _ Bs s w A hA
  obtain ⟨_, _, _, ⟨C, hC⟩, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq Bs A hA
  obtain ⟨K, hK0, hK⟩ := _root_.GlobalTheory.capelli_fold_ccle k r Wp Wq s w 5
  refine ⟨|C| * K, mul_nonneg (abs_nonneg _) hK0, ?_⟩
  intro X Z c c' hX hc hc'
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  have hc0' : 0 ≤ c' := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc'
  have hF := hK A c X hX hc
  have h := (hC _ _ _ _ ⟨_, hF⟩ ⟨_, hc'⟩ (Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (by norm_num) hF)
    (Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (by norm_num) hc')).2.2
  refine h.trans ?_
  rw [mul_assoc |C| K c]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hK0 hc0)) hc0'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingSesquilinear
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_foldCapelli_sesquilinear : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∀ (a : ℂ) (X X' Z Z' : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CkOn ⊤ (B.GV k r) X' → B.InCC A (5 + w.length * (2 * r + k + 1)) X → B.InCC A (5 + w.length * (2 * r + k + 1)) X' → B.InCC A 5 Z → B.InCC A 5 Z' → B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X + a • X') w) Z = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X') w) Z ∧ B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) (Z + a • Z') = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + (starRingEnd ℂ) a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z' := by
  intro k r Wp Wq _ _ _ _ _ _ Bs s w A hA a X X' Z Z' hX hX' hXc hX'c hZ hZ'
  obtain ⟨K, -, hK⟩ := _root_.GlobalTheory.capelli_fold_ccle k r Wp Wq s w 5
  obtain ⟨c, hc⟩ := hXc
  obtain ⟨c', hc'⟩ := hX'c
  have h1 : B.InCC A 5 _ := ⟨_, hK A c X hX hc⟩
  have h2 : B.InCC A 5 _ := ⟨_, hK A c' X' hX' hc'⟩
  refine ⟨?_, (Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq Bs hA hZ hZ' h1 a).2⟩
  rw [← (Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq Bs hA h1 h2 hZ a).1]
  exact Formalism.FourierDecayAlt.P.JCx2.sq_beta_congr Bs (fun g hg => GlobalTheory.capelliFold_add_smul k r Wp Wq s w a X X' hX hX' g hg)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsUnitIffNotIsUnitOfCoprime
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem isAdicComplete_ov_of_range {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (O : Type) [CommRing O]
    [Algebra O F] (hinj : Function.Injective (algebraMap O F))
    (hr : ∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) (g : ℕ)
    (hc : IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O) :
    IsAdicComplete (Ideal.span {((g : ℕ) : TWO.Ov v)}) (TWO.Ov v) := by
  let φ : O →+* TWO.Ov v := (algebraMap O F).codRestrict (TWO.Ov v) fun a => (hr _).2 ⟨a, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun z => ?_⟩
    obtain ⟨a, ha⟩ := (hr z).1 z.2
    exact ⟨a, Subtype.ext ha⟩
  have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {((g : ℕ) : O)}) (RingEquiv.ofBijective φ hφ)).2 hc
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

theorem isUnit_iff_not_isUnit_of_coprime {R : Type} [CommRing R] [IsLocalRing R] {x y u u' : R}
    (h : ¬ IsUnit (x * y)) (h1 : u * x + u' * y = 1) : IsUnit x ↔ ¬ IsUnit y := by
  refine ⟨fun hx hy => h (hx.mul hy), fun hy => ?_⟩
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h2 | h2
  · exact isUnit_of_mul_isUnit_right h2
  · exact absurd (isUnit_of_mul_isUnit_right h2) hy

theorem card_filter_val_lt (n₁ n₂ : ℕ) :
    (Finset.univ.filter fun b : Fin (n₁ + n₂) => b.val < n₁).card = n₁ := by
  rw [Fin.card_filter_val_lt]; omega

theorem lemmaBT_of_characters : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → LemmaBT := by
  intro L1 L2 L4 TB hch E _ _ _ H Dw l Xo c inst hst
  obtain rfl := starSt E H inst hst
  letI := H.starRing
  intro T io y hy C hfr P tors ϖ hϖ Q hQ g g' hg hg' hne og og' π π' hπ hπ' hcop hcop' hcard hnd hnu F _ _ _ _ _ _ v hv
    O _ _ _ _ hinj hO hOc I Φ M0 r b hΦ hb1 hb2 n₁ n₂ hn D' A' G' _ _ pD pA pG U' PU _ oD' hx1 hx2 m hm hd1 hd2 hd3 ρg hρg
  letI := io.toAlgebra
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  obtain ⟨σ, e, hσ, he1, -, heig, hval, hconj, ⟨lam, hlam⟩, hε, hgu⟩ :=
    GlobalTheory.T.exists_integral_types_and_directions' E H Dw l Xo c T io y C ϖ hϖ g hg hnu hcard hnd F v hv
  obtain ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, -, hact, htr⟩ :=
    GlobalTheory.T.integralChart_columns_to_tuple_harmonicValues L1 L2 L4 TB E H Dw l Xo c T io y C hfr P tors ϖ hϖ Q hQ F v hv
  obtain ⟨BT, -, hBT, -, -, -, -, hBF⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  have hdA : ∀ a, dAct F B a = dAct F C.ch.B a := by
    intro a
    have h1 : B.actK F a = C.ch.B.actK F a := by
      rw [← (hBF F).2.1 a]
      unfold FB.actK
      rw [hact, hBT]
    unfold dAct
    rw [h1]
  obtain ⟨rk, hrk, col, m', hcol, hty, hdeg, hmin⟩ :=
    minorSt E H Dw F (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₁ n₂ (by convert hm)
  obtain ⟨h₀, hh₀⟩ := canonGauge_exists T.V (chD C.ch) (𝓞 E) F B
  have hππ : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, mul_comm, hπ]
  obtain ⟨u₁, u₂, hu12⟩ := hcop
  have hg'0 : (0 : ℝ) < g' := by exact_mod_cast hg'.pos
  have hred : (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ :
      FamGerm.Pt1 E H T.V F).Red r b Φ (max M0 0) := by
    refine ⟨hΦ, le_max_right _ _, hb1, fun i z => ?_⟩
    have h1 := hb2 i z
    have h2 : (0 : ℝ) ≤ Q z := by
      by_cases hz : z = 0
      · rw [hz, Q_zero hϖ P.D hQ, Int.cast_zero]
      · have h3 := Q_pos hϖ P.D hQ hz
        exact_mod_cast (by omega : 0 ≤ Q z)
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h2)
  obtain ⟨s, s', t, f, gm, hs, hgm, hle⟩ := GlobalTheory.T.depth_bound_from_characters_pointDatum L1 L2 L4 TB hch g E H T.V F
    (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ)
    (isAdicComplete_ov_of_range v O hinj hO g hOc) hgu Dw I r b Φ (max M0 0) hred (star π) g' hππ
    ⟨u₂, u₁, by rw [star_star, add_comm, hu12]⟩ ((Nat.coprime_primes hg hg').2 hne) (E →+* ℂ) rk σ
    (fun l => e ⟨l.1, Fin.castLE (hrk l.1) l.2⟩)
    (fun a l => by rw [show dAct F _ a = dAct F C.ch.B a from hdA a]; exact heig a _)
    (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))))
    (fun τ h => (hval τ _).1 (by rw [hσ]; exact h)) (fun τ h => (hval τ _).2 (by rw [hσ]; exact h))
    ⟨fun l => lam ⟨l.1, Fin.castLE (hrk l.1) l.2⟩, fun l l' => by
      refine (hlam _ _).trans (if_congr ?_ rfl rfl)
      obtain ⟨τ, i⟩ := l
      obtain ⟨τ', i'⟩ := l'
      constructor
      · intro h
        obtain rfl : τ = τ' := congrArg Sigma.fst h
        have h2 := eq_of_heq (Sigma.mk.inj h).2
        obtain rfl : i = i' := Fin.castLE_injective _ h2
        rfl
      · intro h
        rw [h]⟩
    (by convert hε) (n₁ + n₂) (Finset.univ.filter fun b => b.val < n₁) col m' hcol
    (fun τ i => by rw [Finset.mem_filter, ← hty τ i]; simp) (degOf Dw m) hdeg.symm hd1 hd2
    (by
      rcases le_total M0 0 with h | h
      · rw [max_eq_right h, mul_zero]; exact hg'0
      · rw [max_eq_left h]; exact hd3)
    h₀ hh₀ ρg hρg
  simp only [star_star] at hs
  obtain ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', h, un, hbox, -, -, hvl⟩ :=
    htr g g' π hg.one_le hg'.one_le hπ (n₁ + n₂) D' A' G' pD pA pG U' PU oD' hx1 hx2 s s' t f hs
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hbox
  refine ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', h, gm, b1, b2, b3, b4, b5, b6, b7, b8, b9, ?_, ?_⟩
  · rw [hmin, hvl h₀ hh₀ rk hrk (FamGerm.minorsP F col m') ?_, ← hgm]
    · simp only [he1]
    · intro τ
      refine minors_disjoint_columns_harmonic F _ rk _ col m' _ rfl τ _ fun i i' hii => ?_
      have k1 := hty τ i
      have k2 := hty _ i'
      rw [hii, k2, ← hσ, ← hσ, hconj, star_star] at k1
      have k3 : ∀ a, 0 < v (σ τ a : F) ↔ ¬ IsUnit (σ τ a) := fun a =>
        ⟨fun h hu => hgu (isUnit_of_dvd_unit (Ideal.mem_span_singleton.1 ((hval τ a).1 h)) hu),
          fun h => by_contra fun h' => h ((hval τ a).2 h')⟩
      rw [k3, k3] at k1
      have k4 : IsUnit (σ τ π) ↔ ¬ IsUnit (σ τ (star π)) :=
        isUnit_iff_not_isUnit_of_coprime (u := σ τ u₁) (u' := σ τ u₂) (by rw [← map_mul, hπ, map_natCast]; exact hgu)
          (by rw [← map_mul, ← map_mul, ← map_add (f := _), hu12, map_one])
      tauto
  · rw [card_filter_val_lt] at hle
    have h1 : (0 : ℝ) ≤ (degOf Dw m : ℝ) ^ 2 * Φ / g' := by positivity
    have h2 : 2 * (degOf Dw m : ℝ) ^ 2 * Φ / g' = 2 * ((degOf Dw m : ℝ) ^ 2 * Φ / g') := by ring
    rw [h2, mul_comm (ρg : ℝ)]
    linarith

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialBetaPosOfXiExists
section
open MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.WeightedFormPos


open Formalism.FourierDecayAlt.P.JCx2 in
theorem radialBetaPos_of_xiExists (hXi : B.XiExists) : JC.RadialBetaPos := by
  intro Wp Wq _ _ _ _ _ _ P0 T j μ hμ
  obtain ⟨C1, hC1, hpair⟩ := rb_pairAt (T.bs j) μ hμ
  refine ⟨C1⁻¹, inv_pos.2 hC1, fun n x x' Φ Φ' ε _ hx hx' hΦ hΦ' => ?_⟩
  have h : P5.form μ 0 Φ Φ' 0 = (C1 : ℂ) * ∑ a, B.beta (T.bs j) (x a) (x' a) := by
    refine (rb_form_eq (k := P0.k) (r := P0.r - j) μ Φ Φ').trans ?_
    let f : Wd.Ix (Fin n) → (Fin (P0.r - j) → ℂ) × ℂ → ℂ := fun a q =>
      (bcWeight P0.k (P0.r - j) (Tz P0.k (P0.r - j) (T.bs j).z) (Tz P0.k (P0.r - j) (T.bs j).z') q : ℂ) *
        inner ℂ (B.hsVec (B.JF (T.bs j) (x' a) (B.gq (T.bs j) q))) (B.hsVec (B.JF (T.bs j) (x a) (B.gq (T.bs j) q)))
    have hint : ∀ a, Integrable (f a) := fun a =>
      betaIntegrand_integrable_of_xiExists hXi P0.k (P0.r - j) Wp Wq (T.bs j) _ (x a) (x' a) le_rfl
        ((hx a).2.1 _ 5) ((hx' a).2.1 _ 5)
    have hae : (fun c : Fin (P0.r - j) → ℂ => ((∏ a : Fin (P0.r - j), ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ b, P5.pairAt (k := P0.k) (r := P0.r - j) μ (Φ b) (Φ' b) c)
        =ᵐ[volume] fun c => ∑ b, (C1 : ℂ) * ∫ ζ, f b (c, ζ) := by
      filter_upwards [rb_ae_OmX] with c hc
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hpair (x b) (x' b) (Φ b) (Φ' b) (hΦ b) (hΦ' b) c hc, mul_left_comm, ← integral_const_mul]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      dsimp only
      rw [rb_weight hc]
      rfl
    refine (integral_congr_ae hae).trans ?_
    rw [integral_finsetSum _ (fun b _ => ((hint b).integral_prod_left).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, ← integral_prod _ (hint b)]
    rfl
  rw [h]
  have hC : (C1 : ℂ) ≠ 0 := by exact_mod_cast hC1.ne'
  push_cast
  field_simp

theorem radialModuleForm_of_xiExists (hXi : B.XiExists) : JC.RadialModuleForm :=
  radial_module_form_of_parts (radialBetaPos_of_xiExists hXi) radial_module_action bessel_function_finite_class
    bessel_module module_regularity

end GlobalTheory.WeightedFormPos
end

