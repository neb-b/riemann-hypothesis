module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgue
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiffQuotientBesselMapTendsto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupport
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellOrbInt

theorem ae_of_weil {X A : Type} [MeasurableSpace X] [MeasurableSpace A]
    (P ν : Measure X) (μ : Measure A) (act : A → X → X) (S : Set X) (hS : MeasurableSet S)
    (hP : ∀ᵐ x ∂P, x ∈ S) (hμ : μ ≠ 0)
    (hW : ∀ f : X → ENNReal, Measurable f → ∫⁻ x, f x ∂P = ∫⁻ x, (∫⁻ a, f (act a x) ∂μ) ∂ν)
    (hact : ∀ᵐ a ∂μ, ∀ x, act a x ∈ S → x ∈ S) : ∀ᵐ x ∂ν, x ∈ S := by
  classical
  have h := hW (Sᶜ.indicator 1) (measurable_one.indicator hS.compl)
  have h0 : ∫⁻ x, Sᶜ.indicator (1 : X → ENNReal) x ∂P = 0 := by
    rw [lintegral_indicator_one hS.compl]; exact hP
  have h1 : ∀ x, Sᶜ.indicator (fun _ => μ Set.univ) x ≤ ∫⁻ a, Sᶜ.indicator (1 : X → ENNReal) (act a x) ∂μ := by
    intro x
    by_cases hx : x ∈ S
    · simp [hx]
    · have : ∫⁻ a, Sᶜ.indicator (1 : X → ENNReal) (act a x) ∂μ = ∫⁻ _, 1 ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hact] with a ha
        have : act a x ∉ S := fun h => hx (ha x h)
        simp [this]
      rw [this, lintegral_const]
      simp [hx]
  have h2 := lintegral_mono (μ := ν) h1
  rw [← h, h0, lintegral_indicator_const hS.compl, nonpos_iff_eq_zero] at h2
  rcases mul_eq_zero.1 h2 with h2 | h2
  · exact absurd (Measure.measure_univ_eq_zero.1 h2) hμ
  · exact h2

variable {k r : ℕ}

theorem ae_mem_N (κ : ℝ≥0∞) : ∀ᵐ y ∂(haarLie (Nset k r) κ), Matrix.of y ∈ Nset k r := by
  unfold haarLie
  apply Measure.ae_smul_measure
  have hu : Continuous fun x : lieE (Nset k r) => unrealify (m := 2 * r + k + 1) x.1 := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [unrealify, Complex.mk_eq_add_mul_I]
    fun_prop
  have h : AEMeasurable (fun x : lieE (Nset k r) =>
      (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j : Mt k r)) volume := by
    haveI : BorelSpace (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := inferInstanceAs (BorelSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
    exact (GlobalTheory.Amp.NLie.cont_exp.comp hu).measurable.aemeasurable
  have hcl : IsClosed {y : Mt k r | Matrix.of y ∈ Nset k r} := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).closed
  rw [ae_map_iff h hcl.measurableSet]
  exact Filter.Eventually.of_forall fun x => GlobalTheory.Amp.NLie.exp_mem (GlobalTheory.Amp.NLie.mem_lieE x.2)

def pairSet (L : LocBessel k r) : Set (PairSp k r) :=
  {p | Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧
    Matrix.of p.2.2 ∈ Nset k r}

theorem closed_pairSet (L : LocBessel k r) : IsClosed (pairSet L) := by
  have hWc := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r L.z).closed
  have hWc' := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r L.z').closed
  have hNc := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).closed
  exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
    ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))

theorem meas_pairSet (L : LocBessel k r) : MeasurableSet (pairSet L) := by
  haveI : BorelSpace (PairSp k r) := Prod.borelSpace
  exact (closed_pairSet L).measurableSet

theorem ae_pairMeas (L : LocBessel k r) : ∀ᵐ p ∂(pairMeas L), p ∈ pairSet L := by
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have aN : ∀ᵐ y ∂L.μN, Matrix.of y ∈ Nset k r := ae_mem_N _
  have aW : ∀ᵐ y ∂L.μW, Matrix.of y ∈ UWset k r L.z := by rw [ae_iff]; exact L.hμW.1.2.2.1
  have aW' : ∀ᵐ y ∂L.μW', Matrix.of y ∈ UWset k r L.z' := by rw [ae_iff]; exact L.hμW'.1.2.2.1
  have b1 := (Measure.quasiMeasurePreserving_fst (μ := L.μW) (ν := L.μN)).ae aW
  have b2 := (Measure.quasiMeasurePreserving_snd (μ := L.μW) (ν := L.μN)).ae aN
  have c1 := (Measure.quasiMeasurePreserving_fst (μ := L.μW') (ν := L.μN)).ae aW'
  have c2 := (Measure.quasiMeasurePreserving_snd (μ := L.μW') (ν := L.μN)).ae aN
  have d1 := (Measure.quasiMeasurePreserving_fst (μ := L.μW.prod L.μN) (ν := L.μW'.prod L.μN)).ae (b1.and b2)
  have d2 := (Measure.quasiMeasurePreserving_snd (μ := L.μW.prod L.μN) (ν := L.μW'.prod L.μN)).ae (c1.and c2)
  unfold pairMeas
  filter_upwards [d1, d2] with p hp hq
  exact ⟨hp.1, hp.2, hq.1, hq.2⟩

theorem mem_N_of_mul {a x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r)
    (h : a * x ∈ Nset k r) : x ∈ Nset k r := by
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have := hN.mul_mem _ (hN.inv_mem a ha) _ h
  rwa [Matrix.nonsing_inv_mul_cancel_left _ _ (hN.unit a ha)] at this

theorem ae_quot (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hR : IsHaarOn (RStab k r γ) μR)
    (hQ : IsOrbQuot L γ μR ν) : ∀ᵐ p ∂ν, p ∈ pairSet L := by
  refine ae_of_weil (pairMeas L) ν μR (fun x p => stabAct γ (Matrix.of x) p) _ (meas_pairSet L) (ae_pairMeas L)
    hR.2.1 hQ ?_
  have aR : ∀ᵐ y ∂μR, Matrix.of y ∈ RStab k r γ := by rw [ae_iff]; exact hR.2.2.1
  filter_upwards [aR] with a ha p hp
  exact ⟨hp.1, mem_N_of_mul ha.1 hp.2.1, hp.2.2.1, mem_N_of_mul ha.2 hp.2.2.2⟩

theorem point_mem (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ ∈ UH (Hpk k r)) {p : PairSp k r} (hp : p ∈ pairSet L) :
    (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 ∈ UH (Hpk k r) := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  exact hG.mul_mem _ (hG.mul_mem _ (hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hp.1.1) _ (hG.inv_mem _ hp.2.1.1)) _ hγ)
    _ hp.2.2.2.1) _ hp.2.2.1.1

theorem continuous_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous fun x : Mt k r => psi k r z c (Matrix.of x) := by
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (Formalism.FourierDecayAlt.P.B7.continuous_ell z)))))

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem contOn_intg (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ ∈ UH (Hpk k r)) {F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)}
    (hF : ContinuousOn F (UH (Hpk k r))) : ContinuousOn (besselIntg L F γ) (pairSet L) := by
  set S := pairSet L with hS
  have hc : ContinuousOn L.π (UWset k r L.z) :=
    continuousOn_clm_apply.mpr (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_cont L.hz.2 (u := L.u) L.hπ)
  have hc' : ContinuousOn L.π' (UWset k r L.z') :=
    continuousOn_clm_apply.mpr (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_cont L.hz'.2 (u := L.u') L.hπ')
  have hxi : Continuous fun p : PairSp k r =>
      psi k r L.z L.c (Matrix.of p.1.2) * star (psi k r L.z' L.c (Matrix.of p.2.2)) :=
    ((continuous_psi L.z L.c).comp continuous_fst.snd).mul ((continuous_psi L.z' L.c).comp continuous_snd.snd).star
  have hπ : ContinuousOn (fun p : PairSp k r => L.π (Matrix.of p.1.1)) S :=
    hc.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)
  have hinv1 : ContinuousOn (fun p : PairSp k r => (Matrix.of p.1.1 : Formalism.FourierDecayAlt.B.Mat k r)⁻¹) S :=
    (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : PairSp k r => (Matrix.of p.1.2 : Formalism.FourierDecayAlt.B.Mat k r)⁻¹) S :=
    (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hinv3 : ContinuousOn (fun p : PairSp k r => (Matrix.of p.2.1 : Formalism.FourierDecayAlt.B.Mat k r)⁻¹) S :=
    (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)
  have hπ' : ContinuousOn (fun p : PairSp k r => L.π' (Matrix.of p.2.1 : Formalism.FourierDecayAlt.B.Mat k r)⁻¹) S :=
    hc'.comp hinv3 (fun p hp => (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.2.2.1).1)
  have hc4 : ContinuousOn (fun p : PairSp k r => (Matrix.of p.2.2 : Formalism.FourierDecayAlt.B.Mat k r)) S :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : PairSp k r => (Matrix.of p.2.1 : Formalism.FourierDecayAlt.B.Mat k r)) S :=
    (continuous_snd.fst).continuousOn
  have hsgs : ContinuousOn (fun p : PairSp k r =>
      (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1) S :=
    ((((hinv1.mul hinv2).mul continuousOn_const).mul hc4).mul hc5)
  have hFs := hF.comp hsgs (fun p hp => point_mem L hγ hp)
  unfold besselIntg
  exact hxi.continuousOn.smul (hπ.clm_comp (hFs.clm_comp hπ'))

theorem norm_intg_le (L : LocBessel k r) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) {p : PairSp k r}
    (hp : p ∈ pairSet L) : ‖besselIntg L F γ p‖ ≤
      ‖F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1)‖ := by
  have hu := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary L.hz.2 (u := L.u) L.hπ _ hp.1
  have hu' := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary L.hz'.2 (u := L.u') L.hπ' _ (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.2.2.1).1
  unfold besselIntg
  rw [norm_smul, norm_mul, norm_star, norm_psi, norm_psi, one_mul, one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hu, ← hu' w]
  exact ContinuousLinearMap.le_opNorm _ _

theorem coefF_eq (L : LocBessel k r) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    coefF L v v' ξ ξ' g = ⟪v, L.σ g v'⟫_ℂ • (innerSL ℂ ξ').smulRight ξ := by
  ext w
  simp only [coefF, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply]
  rw [smul_comm]

theorem orbInt_integrable : Hyps → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  intro H k r L h μG γ μR νR ν hgap hok _ hC
  obtain ⟨hγ, -, -, -, hR, hQ, -⟩ := hC
  have hae := ae_quot L hR hQ
  refine ⟨hae, fun b _ hb hint v v' hv hv' ξ ξ' => ?_⟩
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hsm := H.1.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ v' hv'
  obtain ⟨C, Ws, -, hdec⟩ := H.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v hv
  have hd := hdec v' hsm
  generalize C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W v'‖).sum = A at hd
  have hF : ContinuousOn (coefF L v v' ξ ξ') (UH (Hpk k r)) := by
    have e : coefF L v v' ξ ξ' = fun g => ⟪v, L.σ g v'⟫_ℂ • (innerSL ℂ ξ').smulRight ξ :=
      funext (coefF_eq L v v' ξ ξ')
    rw [e]
    exact (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ v')).smul continuousOn_const
  haveI : BorelSpace (PairSp k r) := Prod.borelSpace
  have hm : AEStronglyMeasurable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
    have := (contOn_intg L hγ hF).aestronglyMeasurable (μ := ν) (meas_pairSet L)
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
  refine (hint.const_mul (|A| * ‖(innerSL ℂ ξ').smulRight ξ‖)).mono' hm ?_
  filter_upwards [hae] with p hp
  refine (norm_intg_le L γ _ hp).trans ?_
  have hx := point_mem L hγ hp
  unfold pairMaj
  set x := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1
  have h1 : 1 ≤ Formalism.FourierDecayAlt.B.gN x := PI.PolynomialProperness.GN.gN_ge_one hx
  have h2 : Formalism.FourierDecayAlt.B.gN x ^ (1 - Formalism.FourierDecayAlt.ThreeDimData.aOf r h) ≤ Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have h3 : ‖⟪v, L.σ x v'⟫_ℂ‖ ≤ |A| * Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
    (hd x hx).trans ((mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg A)))
  rw [coefF_eq, norm_smul, mul_right_comm]
  exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

end GlobalTheory.CellOrbInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSides
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Side

theorem urep_irred_of_ds {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : IsDSHpk k r ε lam σ) : IsURepOn (GG k r) σ ∧ IsIrredOn (GG k r) σ := by
  obtain ⟨P, ⟨⟨hP, hH⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, hi, -⟩ := h
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPi : P * P⁻¹ = 1 := mul_nonsing_inv _ hd
  have hiP : P⁻¹ * P = 1 := nonsing_inv_mul _ hd
  have mem : ∀ g, g ∈ GG k r ↔ P * g * P⁻¹ ∈ UJset ε := uHConj _ ε _ P hd hH
  have back : ∀ g : Mat k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hiP]; simp
  have forth : ∀ g : Mat k r, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hPi]; simp
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simpa [hiP] using h1
  · intro a ha b hb
    have := hm _ ((mem a).1 ha) _ ((mem b).1 hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hiP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    simpa only [e, back] using this
  · intro g hg v
    have := hn _ ((mem g).1 hg) v
    simpa only [back] using this
  · intro v
    have hcont : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp hcont.continuousOn (s := GG k r) (fun g hg => (mem g).1 hg)
    refine this.congr fun g _ => ?_
    simp only [Function.comp, back]
  · intro S hS hst
    refine hi S hS fun g hg v hv => hst _ ((mem _).2 ?_) v hv
    rw [forth]; exact hg

theorem isHaarOn_smul {k r : ℕ} {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) {c : ℝ}
    (hc : 0 < c) : IsHaarOn S (ENNReal.ofReal c • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ENNReal.ofReal c • μ = c.toNNReal • μ := rfl
    rw [this]; infer_instance
  · intro h0
    rcases Measure.ennreal_smul_eq_zero.1 h0 with h | h
    · exact (ENNReal.ofReal_pos.2 hc).ne' h
    · exact h2 h
  · rw [Measure.smul_apply, h3, smul_zero]
  · intro s hs
    rw [Measure.map_smul, h4 s hs]
    haveI : BorelSpace (Mat k r) := inferInstanceAs (BorelSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
    exact (continuous_const.matrix_mul (continuous_id (X := Mat k r))).measurable.aemeasurable

theorem oneSide_of_bessel {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {σ : Mat k r → (H →L[ℂ] H)} {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {u : Fin k → ℝ}
    {s : ℂ} {μG μW μN νS : Measure (Mt k r)} {B : H → Wp} {v : H} {c : ℝ}
    (hσ : IsURepOn (GG k r) σ) (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsHCTypeW k r z u π)
    (hG : IsHaarOn (GG k r) μG) (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    (hN : IsHaarOn (Nset k r) μN) (hq : IsQuotMeas μG (muS μW μN) νS)
    (hB : IsBesselMapSm z (psi k r z s) σ π B) (hv : IsSmoothVec σ v) (hc : 0 < c)
    (hl : l2SG νS (fun g => B (σ g v)) = ENNReal.ofReal (c * Module.finrank ℂ Wp)) :
    OneSide z π (psi k r z s) μG μW μN νS (fun g => B (σ g v)) c := by
  have := FiniteDimensional.complete ℂ Wp
  obtain ⟨hnt, hu, hi⟩ := (GlobalTheory.Amp.Schur.type_irred_and_avg k r z π hz hT).1 u hπ
  refine ⟨hz, hT, hnt, hu, hi, hG, hW, hW1, hN, hq, fun n hn => (psiChar k r z s hz n hn).2, ?_, ?_, hc, hl⟩
  · intro h hh m hm g hg
    have hdet : IsUnit (Hpk k r).det :=
      Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
    have hhm : h * m ∈ GG k r := (uHGroup _ _ hdet).2.1 h hh.1 m hm.1
    have hs : IsSmoothVec σ (σ g v) := ((_root_.GlobalTheory.SgInfDD.DD_stable_dense k r σ v hσ).2.2.2.1 v hv).1 g hg
    have := hB.2.2.1 h hh m hm (σ g v) hs
    show B (σ (h * m * g) v) = _
    rw [hσ.1.2 _ hhm _ hg]
    exact this
  · exact (_root_.GlobalTheory.diffQuot_bessel k r σ z _ π B v 0 hσ hB hv (by simp [InLieHpk])).2.1

theorem both_sides : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) lam (A : LocS W), 0 < θ → 0 < D.host.v → HypTT D w w' → GoodW D τ w w' θ W → GoodS D lam A → IsURepOn (GG D.R.k D.R.rS) A.σ ∧ IsIrredOn (GG D.R.k D.R.rS) A.σ ∧ W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS ∧ OneSide W.z W.π (psiS D W.z) W.μG W.μW W.μN W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' W.μN W.νS' A.Φ' A.cN := by
  intro D τ w w' θ W lam A hθ hv hTT hW hA
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, w1', w2, w2', hN, q1, q2⟩ := hW
  obtain ⟨-, hds, b1, b2, hsm, -, -, hc, l1, l2, -⟩ := hA
  obtain ⟨hu, hi⟩ := urep_irred_of_ds hds
  have hpos : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ := by positivity
  have hμ : W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS := by
    have e : haarLie (Nset D.R.k D.R.rS) (kapN D θ) = kapN D θ • haarLie (Nset D.R.k D.R.rS) 1 := by
      unfold haarLie; rw [one_smul]
    rw [hN, e, _root_.GlobalTheory.Amp.NLie.haarLie_eq_lebN, smul_smul, ENNReal.ofReal_mul hpos.le, ENNReal.ofReal_pow (by norm_num)]
    simp [kapN]
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hμ]; exact isHaarOn_smul (_root_.GlobalTheory.Amp.NHaar.isHaarOn_lebN _ _) (by positivity)
  have hT1 : 0 < Tz D.R.k D.R.rS W.z := by
    rw [t1]; unfold Tr; exact_mod_cast hTT.1.pos
  have hT2 : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [t2]; unfold Tr; exact_mod_cast hTT.2.1.pos
  exact ⟨hu, hi, hμ, oneSide_of_bessel hu z1 hT1 c1 hG w1 w1' hNH q1 b1 hsm hc l1,
    oneSide_of_bessel hu z2 hT2 c2 hG w2 w2' hNH q2 b2 hsm hc l2⟩

end GlobalTheory.Amp.Side
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLevelOfPreservesFirstComponentsSplit
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem mem_levelVL_of_first_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (L : Submodule (𝓞 E) (Fin n → E)), SelfDualAt cm.sig J v L → ∀ κ ∈ UPts cm.sig J (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔ ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = ((bc ((RingHom.fst _ _).comp sp.toRingHom) κ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b) → κ ∈ levelVL cm.sig J v L := by
  intro F E _ _ _ _ _ _ cm n J v sp hsig hdiag L hsd κ hκ hfirst
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag

  have pair1 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).1 =
      ∑ i, ∑ j, (sp (z i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
    intro z y
    unfold hR hform
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl
  have pair2 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).2 =
      ∑ i, ∑ j, (sp (z i)).1 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).2 * (sp (y j)).2 := by
    intro z y
    unfold hR hform
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl

  have hprod : ∀ y : Fin n → E ⊗[F] v.adicCompletion F, y ∈ loc v L ↔
      (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2 := by
    intro y
    refine ⟨fun hy => ⟨⟨y, hy, fun _ => rfl⟩, y, hy, fun _ => rfl⟩, ?_⟩
    rintro ⟨⟨y₁, h₁, e₁⟩, y₂, h₂, e₂⟩
    have ha : sp.symm (1, 0) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
    have hb : sp.symm (0, 1) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩
    have hm := (loc v L).add_mem ((loc v L).smul_mem ⟨_, ha⟩ h₁) ((loc v L).smul_mem ⟨_, hb⟩ h₂)
    have hy : y = (⟨_, ha⟩ : intV E v) • y₁ + (⟨_, hb⟩ : intV E v) • y₂ := by
      funext b
      apply sp.injective
      change sp (y b) = sp (sp.symm (1, 0) * y₁ b + sp.symm (0, 1) * y₂ b)
      rw [map_add (f := _), map_mul, map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      ext
      · simp [e₁ b]
      · simp [e₂ b]
    rw [hy]; exact hm

  set Kv := v.adicCompletion F with hKv
  set φ1 : E ⊗[F] Kv →+* Kv := (RingHom.fst _ _).comp sp.toRingHom with hφ1
  set φ2 : E ⊗[F] Kv →+* Kv := (RingHom.snd _ _).comp sp.toRingHom with hφ2
  have e1 : ∀ a, φ1 a = (sp a).1 := fun _ => rfl
  have e2 : ∀ a, φ2 a = (sp a).2 := fun _ => rfl
  set K1 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ1 with hK1
  set K2 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ2 with hK2
  set J2 : Matrix (Fin n) (Fin n) Kv := (J.map (inclE (F := F) Kv)).map φ2 with hJ2

  have hU : cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) * J.map (inclE (F := F) Kv) *
      (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) = J.map (inclE (F := F) Kv) := hκ
  have hc : (cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv))).map φ2 = K1ᵀ := by
    refine Matrix.ext fun i j => ?_
    show (sp (sigR cm.sig Kv ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i))).2 = (sp ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i)).1
    rw [hsig]; rfl
  have hU2 : K1ᵀ * J2 * K2 = J2 := by
    have := congrArg (fun M => M.map φ2) hU
    simp only [Matrix.map_mul] at this
    rw [hc] at this
    exact this
  have hQ : ∀ u w : Fin n → Kv, (K1 *ᵥ u) ⬝ᵥ (J2 *ᵥ (K2 *ᵥ w)) = u ⬝ᵥ (J2 *ᵥ w) := by
    intro u w
    conv_rhs => rw [← hU2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have hsum : ∀ u w : Fin n → Kv, (∑ i, ∑ j, u i * J2 i j * w j) = u ⬝ᵥ (J2 *ᵥ w) := by
    intro u w
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

  have hL2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔
      ∀ u : Fin n → Kv, (∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = u b) → u ⬝ᵥ (J2 *ᵥ w) ∈ v.adicCompletionIntegers F := by
    intro w
    constructor
    · rintro ⟨y, hy, ey⟩ u ⟨z, hz, ez⟩
      have h := ((hint _).1 (((hsd y).1 hy) z hz)).2
      rw [pair2] at h
      simp only [ez, ey] at h
      rw [← hsum]; exact h
    · intro h
      refine ⟨fun b => sp.symm (0, w b), ?_, fun b => by simp⟩
      refine (hsd _).2 fun z hz => (hint _).2 ⟨?_, ?_⟩
      · rw [pair1]; simp
      · rw [pair2]
        have := h (fun b => (sp (z b)).1) ⟨z, hz, fun _ => rfl⟩
        rw [← hsum] at this
        have e : ∀ j, (sp (sp.symm (0, w j))).2 = w j := fun j => by simp
        simp only [e]
        exact this

  have hH : ∀ x : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔
      ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = (K1 *ᵥ x) b := hfirst
  have hK1inv : ∀ u : Fin n → Kv, ∃ u', K1 *ᵥ u' = u := by
    intro u
    refine ⟨(((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) *ᵥ u, ?_⟩
    rw [Matrix.mulVec_mulVec]
    have : K1 * (((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) = 1 := by
      have := (bc φ1 κ).mul_inv
      exact this
    rw [this, Matrix.one_mulVec]
  have hK2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔
      ∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = (K2 *ᵥ w) b := by
    intro w
    rw [hL2, hL2]
    constructor
    · intro h u hu
      obtain ⟨u', rfl⟩ := hK1inv u
      rw [hQ]
      exact h u' ((hH u').2 hu)
    · intro h u hu
      rw [← hQ]
      exact h _ ((hH u).1 hu)

  have hc1 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).1 =
      (K1 *ᵥ fun j => (sp (x j)).1) b := by
    intro x b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]
    rfl
  have hc2 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).2 =
      (K2 *ᵥ fun j => (sp (x j)).2) b := by
    intro x b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]
    rfl
  show κ ∈ UJ _ _ ⊓ stabGL _
  rw [Subgroup.mem_inf]
  refine ⟨hκ, fun x => ?_⟩
  change x ∈ loc v L ↔ _ ∈ loc v L
  rw [hprod x, hprod (_ *ᵥ x)]
  simp only [hc1, hc2]
  rw [hH (fun j => (sp (x j)).1), hK2 (fun j => (sp (x j)).2)]

end GlobalTheory.St.G
end

