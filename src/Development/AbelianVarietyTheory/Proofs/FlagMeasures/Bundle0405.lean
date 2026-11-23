module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0325
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGap
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpOrbGap

open GlobalTheory.AmpOrb GlobalTheory.CellOrbInt

theorem ampKF : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 := by
  intro hH k r L h μG w l l' hOne γ μR νR ν hD b hb0 hb hint v v' hv hv' ξ ξ'
  have H := hH.1
  obtain ⟨⟨hgap, hok, -, hw, hμ, -, -⟩, hl, hl'⟩ := hOne
  obtain ⟨hγ, -, -, hrel, hR, hQ, hQG⟩ := hD
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  let R : Rep k r := ⟨L.Hs, L.σ⟩
  have hDS : R.IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  obtain ⟨hmul, hone, huni, -⟩ := GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r L.ε L.lam R hDS
  have hsm := H.1.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ w (PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw)
  obtain ⟨C, Ws, -, hC⟩ := H.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v hv
  obtain ⟨C', Ws', -, hC'⟩ := H.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v' hv'
  have hw1 : ‖w‖ = 1 := hw.choose_spec.2.1
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨c, -, hc⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg H k r L.ε μG hμ
  have hDG : R.IsDG L.ε L.lam := ⟨L.hlam, hσ, h, hgap, hok⟩
  obtain ⟨hd, hS⟩ := hc L.lam R hDG
  have hd' : PI.BesselPeriodGGP.fdegH μG L.σ w = c * fdegHC L.lam := hd w hw0
  have hS' : ∀ y y' : L.Hs, ∫ x, ⟪y, L.σ (Matrix.of x) w⟫_ℂ * star ⟪y', L.σ (Matrix.of x) w⟫_ℂ ∂μG =
      (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹ * ⟪y, y'⟫_ℂ := fun y y' => by
    refine (hS w y w y').2.trans ?_
    have : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
    rw [hd']
    show ⟪w, w⟫_ℂ * ⟪y, y'⟫_ℂ / _ = _
    rw [this, one_mul, div_eq_inv_mul]
  haveI : SigmaFinite μG := hμ.1
  haveI : SigmaFinite μR := hR.1
  haveI : SFinite (pairMeas L) := by
    have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
    have : SigmaFinite L.μW := L.hμW.1.1
    have : SigmaFinite L.μW' := L.hμW'.1.1
    unfold pairMeas; infer_instance
  have aG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by rw [ae_iff]; exact hμ.2.2.1
  have aR : ∀ᵐ y ∂μR, Matrix.of y ∈ RStab k r γ := by rw [ae_iff]; exact hR.2.2.1
  have aν := ae_quot L hR hQ
  haveI : SFinite ν := sfinite_of_lintegral ν (fun p => ‖pairMaj γ b p‖ₑ) hint.1.enorm
    (aν.mono fun p hp => by
      have : 0 < pairMaj γ b p :=
        Real.rpow_pos_of_pos (one_pos.trans_le (PI.PolynomialProperness.GN.gN_ge_one (point_mem L hγ hp))) _
      simpa using this.ne') hint.2.ne
  have hRc := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (hG.unit _ hγ)
  have hinv : μR.map GlobalTheory.SgInf.invM = μR :=
    (GlobalTheory.UnipUnimod.isUnimod_of_subset_Nset (S := RStab k r γ)
      ⟨fun a ha => ha.1.1, hRc.closed, hRc.one_mem, hRc.mul_mem, hRc.inv_mem⟩ (fun a ha => ha.1) hR).2
  have mi : Measurable (GlobalTheory.SgInf.invM (k := k) (r := r)) := Formalism.FourierDecayAlt.P.B7.measurable_invM
  let cj : Mt k r → Mt k r := fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j
  have mc : Measurable cj :=
    meas_mul (g := fun _ => γ) (meas_mul (f := fun _ => (γ⁻¹ : MatKR k r)) measurable_const measurable_id)
      measurable_const
  let a₂ : Mt k r → Mt k r → Mt k r := fun a x => Matrix.of.symm (γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x)
  have m2 : Measurable fun q : Mt k r × Mt k r => a₂ q.2 q.1 :=
    meas_mul (mc.comp (mi.comp measurable_snd)) measurable_fst
  have hW2 : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ a, f (a₂ a x) ∂μR) ∂νR := by
    intro f hf
    rw [hQG f hf]
    refine lintegral_congr fun x => ?_
    have mf : Measurable fun s : Mt k r => f fun i j => (Matrix.of s * Matrix.of x) i j :=
      hf.comp (meas_mul measurable_id measurable_const)
    rw [lintegral_map mf mc]
    conv_lhs => rw [← hinv]
    rw [lintegral_map (f := fun s => f fun i j => (Matrix.of (cj s) * Matrix.of x) i j) (mf.comp mc) mi]
    rfl
  haveI : SFinite νR := sfinite_of_weil μG νR μR hR.2.1 a₂ m2 hW2
  have m1 : Measurable fun q : PairSp k r × Mt k r => stabAct γ (Matrix.of q.2) q.1 :=
    (measurable_fst.fst.fst.prodMk (meas_mul measurable_snd measurable_fst.fst.snd)).prodMk
      (measurable_fst.snd.fst.prodMk (meas_mul (mc.comp measurable_snd) measurable_fst.snd.snd))
  have hcl : IsClosed {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := hG.closed
  have aνR : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
    refine ae_of_weil μG νR μR a₂ _ hcl.measurableSet aG hR.2.1 hW2 ?_
    filter_upwards [aR] with a ha x hx
    have h1 := hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hγ) _ (hG.inv_mem _ ha.1.1)) _ hγ
    have h3 : γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x ∈ UH (Hpk k r) := hx
    have h2 := hG.mul_mem _ (hG.inv_mem _ h1) _ h3
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (hG.unit _ h1)] at h2
    exact h2
  have hI := integrable_ker L hγ w v v' ξ ξ' hμ aν (e := Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) hb0 (by linarith) hint
    (fun x hx => by rw [neg_sub]; exact hC w hsm x hx) (fun x hx => by rw [neg_sub]; exact hC' w hsm x hx)
  have key := double_weil (pairMeas L) ν μG νR μR (fun a p => stabAct γ (Matrix.of a) p) a₂
    (mp_of_weil _ _ _ (fun a p => stabAct γ (Matrix.of a) p) m1 hQ) (mp_of_weil _ _ _ a₂ m2 hW2)
    (ker L γ w v v' ξ ξ') (aesm_ker L hγ w v v' ξ ξ' _ _ (ae_pairMeas L) aνR) hI (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((Measure.quasiMeasurePreserving_fst.ae aν).and
        (Measure.quasiMeasurePreserving_snd.ae aR))] with t ht
      exact ker_act L hγ hrel w v v' ξ ξ' ht.2 ht.1 t.2)
  unfold ampJ OrbInt
  rw [Complex.ofReal_one, inv_one, one_smul, ← integral_smul, ← integral_smul]
  refine Eq.trans (integral_congr_ae ?_) (key.trans (integral_congr_ae ?_))
  · filter_upwards [aνR] with x hx
    rw [integral_ker_pair L hok.1 hγ hmul w v v' ξ ξ' hx,
      hl _ (Submodule.subset_span ⟨_, hG.mul_mem _ hγ _ hx, rfl⟩) v hv,
      hl' _ (Submodule.subset_span ⟨_, hx, rfl⟩) v' hv']
    ext η
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      inner_smul_left, inner_conj_symm]
    congr 1
    ring
  · filter_upwards [aν] with p hp
    exact integral_ker_group L hγ hmul hone huni aG hS' v v' ξ ξ' hp

end GlobalTheory.AmpOrbGap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMultOneDecayOfLargeGapHypotheses
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalInputsGap

open GlobalTheory.Amp.LocalInputs

theorem multOne_of_uniqGap (hU : GlobalTheory.GapIn.UniqGap) {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mat k r → (Wp →L[ℂ] Wp)} {h : ℝ}
    (hk : 1 ≤ k) (hg : GapAtLeast ε lam h) (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h)
    (hl : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z) (hc : c ≠ 0)
    (hπ : IsHCTypeW k r z u π) : MultOne z (psi k r z c) σ π := by
  intro B B' h1 h'
  rw [GlobalTheory.BesselMultOne.psi_eq_psiGen] at h1 h'
  obtain ⟨a, b, hab, e⟩ := hU k r ε lam h H σ z (fun _ => c) u Wp π hk hg hh hl hσ hz hT (fun _ => hc) hπ B B'
    (GlobalTheory.BesselMultOne.isBesselMapSm_of h1) (GlobalTheory.BesselMultOne.isBesselMapSm_of h')
  rcases hab with ha | hb
  · refine ⟨-(a⁻¹ * b), Or.inl fun v hv => ?_⟩
    have h3 : a • B v = -(b • B' v) := eq_neg_of_add_eq_zero_left (e v hv)
    rw [neg_smul, mul_smul, ← smul_neg, ← h3, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · refine ⟨-(b⁻¹ * a), Or.inr fun v hv => ?_⟩
    have h3 : b • B' v = -(a • B v) := eq_neg_of_add_eq_zero_right (e v hv)
    rw [neg_smul, mul_smul, ← smul_neg, ← h3, smul_smul, inv_mul_cancel₀ hb, one_smul]

theorem gap_small_le {k r : ℕ} (hk : 1 ≤ k) :
    120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 19 := by
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn2 : 2 ≤ n := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ r := by positivity
    rw [hn]; push_cast; linarith
  have h16 : (120 : ℝ) ≤ n ^ 16 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn2 16)
  have : n ^ 19 = n ^ 16 * n ^ 3 := by ring
  rw [this]; gcongr

theorem locIn_of_hypGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH Cg cb Cu cT CT C0
  have hU : GlobalTheory.GapIn.UniqGap := hH.2.1
  have hD : Formalism.FourierDecayAlt.ThreeDimData.DecLow := hH.1.1.1
  refine ⟨0, fun D large₂ C' Cl hB hZ τ w w' θ W hTT hW A hA => ?_⟩
  obtain ⟨c1, c2, z1, z2, t1, t2, -⟩ := hW
  obtain ⟨hl, hds, -, -, -, -, ⟨P, hP, hv⟩, -⟩ := hA
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv1, -, hgap, -, -, -, hCl⟩, -, -⟩ := hZ
  have hT1 : 0 < Tz D.R.k D.R.rS W.z := by
    rw [t1]; unfold Tr; exact_mod_cast hTT.1.pos
  have hT2 : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [t2]; unfold Tr; exact_mod_cast hTT.2.1.pos
  have hc : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have g0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
    have g1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
    have hka : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
    exact Complex.ofReal_ne_zero.2 (by positivity)
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hmf : (D.R.m : ℝ) ≤ D.R.f := by exact_mod_cast D.R.m_le_f
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hf5 : (D.R.m : ℝ) ≤ (D.R.f : ℝ) ^ 5 := hmf.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hge : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    rw [dimS_eq]
    calc (D.R.r : ℝ) ^ 19 = 1 * (D.R.r : ℝ) ^ 19 * 1 := by ring
      _ ≤ (Cl * D.R.m) * (D.R.r : ℝ) ^ 19 * large₂.sc.L := by gcongr; exact hB.2.1
      _ ≤ (Cl * (D.R.f : ℝ) ^ 5) * (D.R.r : ℝ) ^ 19 * large₂.sc.L := by gcongr
      _ = _ := by ring
  have hg := gap_of_nodes D τ _ hl.1 fun j h1 h2 => hge.trans (hgap τ j h1 h2)
  have hh := gap_small_le (r := D.R.rS) hk
  refine ⟨multOne_of_uniqGap hU hk hg hh hl hds z1 hT1 hc c1,
    multOne_of_uniqGap hU hk hg hh hl hds z2 hT2 hc c2, ?_⟩
  refine (decay_span (by positivity) (urep_of_ds hds) (decay_low hD hk hl hds hg hP)).mono ?_
  exact Submodule.span_mono fun v ⟨g, hg, e⟩ => ⟨g, hg, _, hv, e⟩

end GlobalTheory.Amp.LocalInputsGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIdentityTranslatesKFiniteLargeGap
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
noncomputable section

namespace GlobalTheory.AmpTKOneGap

open GlobalTheory.AmpOrb GlobalTheory.CellOrbInt GlobalTheory.AmpTK

variable {k r : ℕ}

theorem fdeg_ne_zero (H : GlobalTheory.GapIn.Hyp) (L : LocBessel k r) (hDG : (rep L).IsDG L.ε L.lam) {μG : Measure (Mt k r)} (hμ : IsHaarOn (UH (Hpk k r)) μG)
    {w : L.Hs} (hw : w ≠ 0) : (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ) ≠ 0 := by
  obtain ⟨c, hc0, hc⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg H.1 k r L.ε μG hμ
  obtain ⟨hd, -⟩ := hc L.lam (rep L) hDG
  have e : PI.BesselPeriodGGP.fdegH μG L.σ w = c * fdegHC L.lam := hd w hw
  rw [e]
  exact_mod_cast (mul_pos hc0 (GlobalTheory.BesselNorm.fdegHC_pos L.lam L.hlam.1.injective)).ne'

theorem ampTK_pt (H : GlobalTheory.GapIn.Hyp) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (l : L.Hs → L.Wp)
    (l' : L.Hs → L.Wq) (hgap : GapAtLeast L.ε L.lam h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hμ : IsHaarOn (UH (Hpk k r)) μG) (hBe : BeTK L l l') {w : L.Hs} (hw1 : ‖w‖ = 1)
    (hwK : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) (hR : IsHaarOn (RStab k r γ) μR)
    (hQ : IsOrbQuot L γ μR ν)
    (hQG : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b)
    (hint : Integrable (pairMaj γ b) ν) {v v' : L.Hs} (hv : v ∈ (rep L).TK) (hv' : v' ∈ (rep L).TK)
    (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν ∧
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  have hDG : (rep L).IsDG L.ε L.lam := ⟨L.hlam, hσ, h, hgap, hok⟩
  obtain ⟨hmul, hone, huni, hsmg, hTKsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS H.1.1.2.2.1 k r L.ε L.lam (rep L) hDS
  have hsm : w ∈ (rep L).sm := hTKsm w (hKT w hwK)
  obtain ⟨C, Ws, -, hC⟩ := Gp91.GlobalTheory.BesselDecay.decay_TK H.1 k r L.ε L.lam h (rep L) hDG hgap hok v hv
  obtain ⟨C', Ws', -, hC'⟩ := Gp91.GlobalTheory.BesselDecay.decay_TK H.1 k r L.ε L.lam h (rep L) hDG hgap hok v' hv'
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨c, -, hc⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg H.1 k r L.ε μG hμ
  obtain ⟨hd, hS⟩ := hc L.lam (rep L) hDG
  have hd' : PI.BesselPeriodGGP.fdegH μG L.σ w = c * fdegHC L.lam := hd w hw0
  have hS' : ∀ y y' : L.Hs, ∫ x, ⟪y, L.σ (Matrix.of x) w⟫_ℂ * star ⟪y', L.σ (Matrix.of x) w⟫_ℂ ∂μG =
      (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹ * ⟪y, y'⟫_ℂ := fun y y' => by
    refine (hS w y w y').2.trans ?_
    have : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
    rw [hd']
    show ⟪w, w⟫_ℂ * ⟪y, y'⟫_ℂ / _ = _
    rw [this, one_mul, div_eq_inv_mul]
  have hfd := fdeg_ne_zero H L hDG hμ hw0
  haveI : SigmaFinite μG := hμ.1
  haveI : SigmaFinite μR := hR.1
  haveI : SFinite (pairMeas L) := by
    have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
    have : SigmaFinite L.μW := L.hμW.1.1
    have : SigmaFinite L.μW' := L.hμW'.1.1
    unfold pairMeas; infer_instance
  have aG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by rw [ae_iff]; exact hμ.2.2.1
  have aR : ∀ᵐ y ∂μR, Matrix.of y ∈ RStab k r γ := by rw [ae_iff]; exact hR.2.2.1
  have aν := ae_quot L hR hQ
  haveI : SFinite ν := sfinite_of_lintegral ν (fun p => ‖pairMaj γ b p‖ₑ) hint.1.enorm
    (aν.mono fun p hp => by
      have : 0 < pairMaj γ b p :=
        Real.rpow_pos_of_pos (one_pos.trans_le (PI.PolynomialProperness.GN.gN_ge_one (point_mem L hγ hp))) _
      simpa using this.ne') hint.2.ne
  have hRc := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (hG.unit _ hγ)
  have hinv : μR.map GlobalTheory.SgInf.invM = μR :=
    (GlobalTheory.UnipUnimod.isUnimod_of_subset_Nset (S := RStab k r γ)
      ⟨fun a ha => ha.1.1, hRc.closed, hRc.one_mem, hRc.mul_mem, hRc.inv_mem⟩ (fun a ha => ha.1) hR).2
  have mi : Measurable (GlobalTheory.SgInf.invM (k := k) (r := r)) := Formalism.FourierDecayAlt.P.B7.measurable_invM
  let cj : Mt k r → Mt k r := fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j
  have mc : Measurable cj :=
    meas_mul (g := fun _ => γ) (meas_mul (f := fun _ => (γ⁻¹ : MatKR k r)) measurable_const measurable_id)
      measurable_const
  let a₂ : Mt k r → Mt k r → Mt k r := fun a x => Matrix.of.symm (γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x)
  have m2 : Measurable fun q : Mt k r × Mt k r => a₂ q.2 q.1 :=
    meas_mul (mc.comp (mi.comp measurable_snd)) measurable_fst
  have hW2 : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ a, f (a₂ a x) ∂μR) ∂νR := by
    intro f hf
    rw [hQG f hf]
    refine lintegral_congr fun x => ?_
    have mf : Measurable fun s : Mt k r => f fun i j => (Matrix.of s * Matrix.of x) i j :=
      hf.comp (meas_mul measurable_id measurable_const)
    rw [lintegral_map mf mc]
    conv_lhs => rw [← hinv]
    rw [lintegral_map (f := fun s => f fun i j => (Matrix.of (cj s) * Matrix.of x) i j) (mf.comp mc) mi]
    rfl
  haveI : SFinite νR := sfinite_of_weil μG νR μR hR.2.1 a₂ m2 hW2
  have m1 : Measurable fun q : PairSp k r × Mt k r => stabAct γ (Matrix.of q.2) q.1 :=
    (measurable_fst.fst.fst.prodMk (meas_mul measurable_snd measurable_fst.fst.snd)).prodMk
      (measurable_fst.snd.fst.prodMk (meas_mul (mc.comp measurable_snd) measurable_fst.snd.snd))
  have hcl : IsClosed {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := hG.closed
  have aνR : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
    refine ae_of_weil μG νR μR a₂ _ hcl.measurableSet aG hR.2.1 hW2 ?_
    filter_upwards [aR] with a ha x hx
    have h1 := hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hγ) _ (hG.inv_mem _ ha.1.1)) _ hγ
    have h3 : γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x ∈ UH (Hpk k r) := hx
    have h2 := hG.mul_mem _ (hG.inv_mem _ h1) _ h3
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (hG.unit _ h1)] at h2
    exact h2
  have hI := integrable_ker L hγ w v v' ξ ξ' hμ aν (e := Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) hb0 (by linarith) hint
    (fun x hx => by rw [neg_sub]; exact hC w hsm x hx) (fun x hx => by rw [neg_sub]; exact hC' w hsm x hx)
  have hgrp : ∀ᵐ p ∂ν, ∫ x, ker L γ w v v' ξ ξ' (p, x) ∂μG =
      (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹ • besselIntg L (coefF L v v' ξ ξ') γ p := by
    filter_upwards [aν] with p hp
    exact integral_ker_group L hγ hmul hone huni aG hS' v v' ξ ξ' hp
  refine ⟨(hI.integral_prod_left.smul (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)).congr ?_, ?_⟩
  · filter_upwards [hgrp] with p hp
    rw [Pi.smul_apply, hp, smul_smul, mul_inv_cancel₀ hfd, one_smul]
  have key := double_weil (pairMeas L) ν μG νR μR (fun a p => stabAct γ (Matrix.of a) p) a₂
    (mp_of_weil _ _ _ (fun a p => stabAct γ (Matrix.of a) p) m1 hQ) (mp_of_weil _ _ _ a₂ m2 hW2)
    (ker L γ w v v' ξ ξ') (aesm_ker L hγ w v v' ξ ξ' _ _ (ae_pairMeas L) aνR) hI (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((Measure.quasiMeasurePreserving_fst.ae aν).and
        (Measure.quasiMeasurePreserving_snd.ae aR))] with t ht
      exact ker_act L hγ hrel w v v' ξ ξ' ht.2 ht.1 t.2)
  unfold ampJ OrbInt
  rw [Complex.ofReal_one, inv_one, one_smul, ← integral_smul, ← integral_smul]
  refine Eq.trans (integral_congr_ae ?_) (key.trans (integral_congr_ae ?_))
  · filter_upwards [aνR] with x hx
    rw [integral_ker_pair L hok.1 hγ hmul w v v' ξ ξ' hx,
      hBe.1 (L.σ (γ * Matrix.of x) w) (hsmg _ (hG.mul_mem _ hγ _ hx) w hsm) v hv,
      hBe.2 (L.σ (Matrix.of x) w) (hsmg _ hx w hsm) v' hv']
    ext η
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      inner_smul_left, inner_conj_symm]
    congr 1
    ring
  · exact hgrp

theorem oneAt : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → GlobalTheory.AmpTK.BeTK L l l' → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (ν : MeasureTheory.Measure (Formalism.MainNotions.S.PairSp k r)), γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → Formalism.MainNotions.S.IsRelStab L γ → IsHaarOn (Formalism.MainNotions.S.RStab k r γ) μR → Formalism.MainNotions.S.IsOrbQuot L γ μR ν → PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR → ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj γ b) ν → GlobalTheory.AmpTK.OneAt L l l' γ ν := by
  intro H k r L h μG l l' hgap hok _ hμ hBe γ μR νR ν hγ hrel hR hQ hQG b hb0 hb hint
  obtain ⟨-, -, -, -, -, -, -, ⟨w, hw1, hwK, -⟩, -⟩ :=
    GlobalTheory.rep_basic_of_isDS H.1.1.2.2.1 k r L.ε L.lam (rep L) ⟨L.hlam, L.hσ⟩
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  have hDG : (rep L).IsDG L.ε L.lam := ⟨L.hlam, L.hσ, h, hgap, hok⟩
  have hfd := fdeg_ne_zero H L hDG hμ hw0
  have key : ∀ {v v' : L.Hs}, v ∈ (rep L).TK → v' ∈ (rep L).TK → ∀ (ξ : L.Wp) (ξ' : L.Wq),
      Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν ∧
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν :=
    fun hv hv' ξ ξ' =>
      ampTK_pt H L h μG l l' hgap hok hμ hBe hw1 hwK γ μR νR ν hγ hrel hR hQ hQG b hb0 hb hint hv hv' ξ ξ'
  refine ⟨(PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ) •
    ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ, ?_⟩
  rintro F s ⟨m, x, y, X, hxy, hF, rfl⟩
  have hc : ∀ i (ξ : L.Wp) (ξ' : L.Wq), OrbInt L (coefF L (x i) (y i) ξ ξ') γ ν =
      (⟪l (x i), ξ⟫_ℂ * ⟪ξ', l' (y i)⟫_ℂ) • (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ) •
        ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ := by
    intro i ξ ξ'
    rw [smul_comm, (key (hxy i).1 (hxy i).2 ξ ξ').2, smul_smul, mul_inv_cancel₀ hfd, one_smul]
  let e := stdOrthonormalBasis ℂ L.Wq
  have hX : ∀ T : L.Wq →L[ℂ] L.Wp, T = ∑ j, (innerSL ℂ (e j)).smulRight (T (e j)) := by
    intro T
    ext η
    conv_lhs => rw [← e.sum_repr' η]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [ContinuousLinearMap.sum_apply, map_sum]
  have hFe : ∀ g ∈ UH (Hpk k r), F g = ∑ i, ∑ j, coefF L (x i) (y i) (X i (e j)) (e j) g := by
    intro g hg
    rw [hF g hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun j _ => coefF_eq L (x i) (y i) (X i (e j)) (e j) g, ← Finset.smul_sum]
    exact congrArg₂ (· • ·) rfl (hX (X i))
  have hae : ∀ᵐ p ∂ν, besselIntg L F γ p =
      ∑ i, ∑ j, besselIntg L (coefF L (x i) (y i) (X i (e j)) (e j)) γ p := by
    filter_upwards [ae_quot L hR hQ] with p hp
    have e1 : besselIntg L F γ p =
        besselIntg L (fun g => ∑ i, ∑ j, coefF L (x i) (y i) (X i (e j)) (e j) g) γ p := by
      unfold besselIntg
      rw [hFe _ (point_mem L hγ hp)]
    rw [e1]
    exact (GlobalTheory.AmpTKOne.besselIntg_sum L Finset.univ (fun i g => ∑ j, coefF L (x i) (y i) (X i (e j)) (e j) g) γ p).trans
      (Finset.sum_congr rfl fun i _ =>
        GlobalTheory.AmpTKOne.besselIntg_sum L Finset.univ (fun j g => coefF L (x i) (y i) (X i (e j)) (e j) g) γ p)
  have hi : ∀ i j, Integrable (besselIntg L (coefF L (x i) (y i) (X i (e j)) (e j)) γ) ν :=
    fun i j => (key (hxy i).1 (hxy i).2 _ _).1
  have e2 : OrbInt L F γ ν = ∑ i, ∑ j, OrbInt L (coefF L (x i) (y i) (X i (e j)) (e j)) γ ν := by
    unfold OrbInt
    rw [integral_congr_ae hae, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hi i j
  rw [e2, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hc]
  rw [← Finset.sum_smul]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← e.sum_repr' (l' (y i)), map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, mul_comm]

end GlobalTheory.AmpTKOneGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapsProportionalDiscreteSeriesLargeGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapLine

theorem psi_const_gap : Formalism.FourierDecayAlt.ThreeDimData.PsiConst := by
  intro k r z c g
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA
  rw [Finset.mul_sum]

theorem line_of_uniqGap (hU : GlobalTheory.GapIn.UniqGap) {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ} {σ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hk : 1 ≤ k) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h)
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {B0 B : H → Wp}
    (h0 : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B0)
    (h1 : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B)
    {x0 : H} (hx0 : x0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (hne : B0 x0 ≠ 0) :
    ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B x = κ • B0 x := by
  have hpsi : Formalism.QuantumDeterminants.psi k r z c = PI.BesselMapUniq.psiGen k r z (fun _ => c) := funext (psi_const_gap k r z c)
  rw [hpsi] at h0 h1
  obtain ⟨a, b, hab, hrel⟩ :=
    hU k r ε lam h H σ z (fun _ => c) u Wp π hk hg hh hl hσ hz hT (fun _ => hc) hπ B B0 h1 h0
  have ha : a ≠ 0 := by
    rintro rfl
    have hb : b ≠ 0 := hab.resolve_left (fun h => h rfl)
    have := hrel x0 hx0
    simp only [zero_smul, zero_add] at this
    exact hne ((smul_eq_zero.mp this).resolve_left hb)
  refine ⟨-(b / a), fun x hx => ?_⟩
  have h' : a • B x = -(b • B0 x) := eq_neg_of_add_eq_zero_left (hrel x hx)
  calc B x = a⁻¹ • (a • B x) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = -(b / a) • B0 x := by rw [h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem bessel_line_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDG ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  intro hH k r ε mu R Wp _ _ _ _ z π u μW μN μG νq l l₁ hDG hS hl hnz hl₁
  obtain ⟨w, hw, hne⟩ := hnz
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -⟩ := hS
  obtain ⟨h, hgap, hk, hh, -, -⟩ := hDG.gap
  have hc : Formalism.QuantumDeterminants.cStd ≠ 0 := by
    unfold Formalism.QuantumDeterminants.cStd
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact line_of_uniqGap hH.2.1 hk hgap hh hDG.hc hDG.ds hz hT hc hπ hl hl₁ hw hne

end GlobalTheory.GapLine
end

