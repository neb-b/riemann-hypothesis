module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableMatrixCoefficientQuotientMeasure
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.QuotInt

theorem opn_continuous {n : ℕ} : Continuous (opn : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  have h : Continuous fun g : Matrix (Fin n) (Fin n) ℂ =>
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g :=
    LinearMap.continuous_of_finiteDimensional
      ({ toFun := fun g => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g
         map_add' := fun a b => map_add _ a b
         map_smul' := fun c a => map_smul _ c a } :
        Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
  exact h.norm

end GlobalTheory.SgInf.QuotInt

namespace GlobalTheory.SgInf


open GlobalTheory.SgInf.QuotInt in
theorem integrable_Afun_quotMeas : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu v hv ξ
  have hStd' := hStd
  have hSide' := hSide
  obtain ⟨hk, hrep, -, -, hHaar, -, ha, hdec, -⟩ := hStd'
  obtain ⟨hz, hT, hπ, hHaarS, -⟩ := hSide'
  have hcl := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  have hG : IsClosedSub k r (GG k r) := hcl.1
  have hS : IsClosedSub k r (Sset k r z) := hcl.2.2.2.1
  have hunim : IsUnimod (Sset k r z) μS := (_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT μS).1 hHaarS
  have hW := _root_.GlobalTheory.SgInf.weil_integrable k r (Sset k r z) μG μS ν hS hHaar hHaarS hunim hν
  have hνG : ν {x | Matrix.of x ∉ GG k r} = 0 := hW.2.1
  have hstab := (GlobalTheory.SgInfDD.DD_stable_dense k r σ w hrep).1
  have hD1 := _root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hstab hdec u hu v hv
  have hPi := _root_.GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hz hT hπ
  have hmeasG : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} :=
    (hG.2.1.preimage (f := fun x : Mt k r => (Matrix.of x : Mat k r)) continuous_id).measurableSet
  have haeG : ∀ᵐ x ∂ν, x ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := by
    rw [ae_iff]; simpa using hνG

  have hcont : ContinuousOn (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x))
      {x | Matrix.of x ∈ GG k r} := by
    have h1 : ContinuousOn (fun x : Mt k r => be (psiGen k r z c) π μS σ (σ (Matrix.of x) u) v)
        {x | Matrix.of x ∈ GG k r} :=
      hD1.2.2.2.comp (f := fun x : Mt k r => (Matrix.of x : Mat k r)) continuous_id.continuousOn
        (fun x hx => hx)
    exact h1.clm_apply continuousOn_const
  have hae : AEStronglyMeasurable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν := by
    have h1 := hcont.aestronglyMeasurable (μ := ν) hmeasG
    rwa [Measure.restrict_eq_self_of_ae_mem haeG] at h1
  refine ⟨hae, ?_⟩

  obtain ⟨C, hC⟩ := hdec u hu v hv
  have hC'0 : 0 ≤ max C 0 := le_max_right _ _
  let f : Mt k r → ENNReal := fun y => ENNReal.ofReal (max C 0 * opn (Matrix.of y : Mat k r) ^ (-a))
  have hopn : Measurable fun y : Mt k r => opn (Matrix.of y : Mat k r) :=
    Continuous.measurable (α := Mt k r) (opn_continuous (n := 2 * r + k + 1))
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hopn.pow_const (-a)))
  have hcoef : ∀ g ∈ GG k r, ‖coef σ u v g‖ₑ ≤ ENNReal.ofReal (max C 0 * opn g ^ (-a)) := by
    intro g hg
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((hC g hg).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (opn_nonneg _) _)
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
    rw [ae_iff]; simpa using hHaarS.2.2.1
  have hpt : ∀ x : Mt k r, Matrix.of x ∈ GG k r →
      ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ₑ ≤
        ‖ξ‖ₑ * ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x hx
    have h1 : ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ₑ ≤
        ‖be (psiGen k r z c) π μS σ (σ (Matrix.of x) u) v‖ₑ * ‖ξ‖ₑ :=
      ContinuousLinearMap.le_opENorm_of_le _ le_rfl
    refine h1.trans ?_
    rw [mul_comm]
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono_ae ?_
    filter_upwards [haeS] with s hs
    have hsG : Matrix.of s ∈ GG k r := hS.1 hs
    have hsi : (Matrix.of s : Mat k r)⁻¹ ∈ Sset k r z := hS.2.2.2.2 _ hs
    have hP : ‖PiS (psiGen k r z c) π (Matrix.of s)⁻¹‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (hPi.2.2.1 _ hsi).1
    have hc : coef σ (σ (Matrix.of x) u) v (Matrix.of s) = coef σ u v (Matrix.of s * Matrix.of x) := by
      simp only [coef, hrep.1.2 _ hsG _ hx, ContinuousLinearMap.comp_apply]
    rw [enorm_smul]
    calc _ ≤ ‖coef σ (σ (Matrix.of x) u) v (Matrix.of s)‖ₑ * 1 := by gcongr
      _ = ‖coef σ u v (Matrix.of s * Matrix.of x)‖ₑ := by rw [mul_one, hc]
      _ ≤ ENNReal.ofReal (max C 0 * opn (Matrix.of s * Matrix.of x : Mat k r) ^ (-a)) :=
        hcoef _ (hG.2.2.2.1 _ hsG _ hx)
  have hfin : ∫⁻ x, f x ∂μG < ⊤ := by
    have hn : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a := by
      have h2 : (1 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 < 2 * r + k + 1)
      have := pow_lt_pow_right₀ h2 (by norm_num : 2 < 5)
      linarith
    have hN := _root_.GlobalTheory.SgGrowth.normInt_lt_top k r (GG k r) μG a hG hHaar hn
    have heq : ∫⁻ x, f x ∂μG = ENNReal.ofReal (max C 0) * normInt μG a := by
      rw [normInt, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x => ?_
      exact ENNReal.ofReal_mul hC'0
    rw [heq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN
  unfold HasFiniteIntegral
  calc _ ≤ ∫⁻ x, ‖ξ‖ₑ * ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂ν :=
        lintegral_mono_ae (haeG.mono fun x hx => hpt x hx)
    _ = ‖ξ‖ₑ * ∫⁻ x, f x ∂μG := by rw [lintegral_const_mul' _ _ enorm_ne_top, hν f hfm]
    _ < ⊤ := ENNReal.mul_lt_top enorm_lt_top hfin

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LastMajorantLengthSqGeAndPos
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.LastLen

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma herm_splitForm_inv_mulVec_eq_of_mem {k r : ℕ} {g : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r}
    (hg : g ∈ _root_.BranchingSupport.GG k r) (w : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ w) (g⁻¹ *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w w := by
  have hgH : gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r := hg
  have hdet : IsUnit g.det := _root_.GlobalTheory.TensLen.isUnit_det_of_unitary (_root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq k r) hgH
  have h := _root_.Formalism.FourierDecayAlt.P.SettingConstruction.form_of_unitary (_root_.Formalism.QuantumDeterminants.Hpk k r) hgH (g⁻¹ *ᵥ w) (g⁻¹ *ᵥ w)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  exact h.symm

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma splitForm_mulVec_apply_eq_sgn_mul_sig (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) :
    (_root_.Formalism.QuantumDeterminants.Hpk k r *ᵥ u) i = _root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) := by
  simp only [Matrix.mulVec, dotProduct, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma herm_splitForm_eq_sum_star_mul_sgn_mul_sig (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) u u = ∑ i, star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)) := by
  unfold _root_.Formalism.QuantumDeterminants.herm
  simp only [dotProduct, Pi.star_apply, splitForm_mulVec_apply_eq_sgn_mul_sig]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma herm_splitForm_sub_eq_of_isotropic {k r : ℕ} (z y : Fin (2 * r + k + 1) → ℂ)
    (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hy : ∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (z - y) (z - y) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) z z := by
  have hz' : ∀ i : Fin (2 * r + k + 1), (i : ℕ) < r ∨ r + k < (i : ℕ) → z i = 0 := hz
  rw [herm_splitForm_eq_sum_star_mul_sgn_mul_sig, herm_splitForm_eq_sum_star_mul_sgn_mul_sig]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  by_cases h1 : (i : ℕ) < r
  · have hσ := _root_.Formalism.QuantumDeterminants.GBasic.sig_lo k r i h1
    rw [hz' i (Or.inl h1), hz' (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) (Or.inr (by omega)),
      hy (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) (by omega)]
    simp
  · by_cases h2 : r + k < (i : ℕ)
    · rw [hz' i (Or.inr h2), hy i (by omega)]
      simp
    · rw [_root_.Formalism.QuantumDeterminants.GBasic.sig_mid k r i (by omega) (by omega), hy i (by omega), sub_zero]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma neg_re_herm_splitForm_le_sum_normSq (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) :
    -(_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) u u).re ≤ ∑ i, Complex.normSq (u i) := by
  have hs : ∀ i, ‖_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i‖ = 1 := by
    intro i
    unfold _root_.Formalism.QuantumDeterminants.GBasic.sgn
    split_ifs <;> simp
  have hperm : ∑ i, Complex.normSq (u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)) = ∑ i, Complex.normSq (u i) :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (_root_.Formalism.QuantumDeterminants.GBasic.sig_sig k r)) (fun i => Complex.normSq (u i))
  rw [herm_splitForm_eq_sum_star_mul_sgn_mul_sig, Complex.re_sum, ← Finset.sum_neg_distrib]
  calc ∑ i, -(star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))).re
      ≤ ∑ i, (Complex.normSq (u i) + Complex.normSq (u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))) / 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := Complex.abs_re_le_norm (star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)))
        rw [norm_mul, norm_mul, norm_star, hs, one_mul] at h1
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
        nlinarith [neg_le_abs (star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))).re,
          sq_nonneg (‖u i‖ - ‖u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)‖)]
    _ = ∑ i, Complex.normSq (u i) := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hperm]
        ring


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.LastLen.last_len : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), _root_.Formalism.QuantumDeterminants.inWb k r z → 0 < _root_.Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ _root_.BranchingSupport.GG k r, _root_.Formalism.QuantumDeterminants.Tz k r z ≤ _root_.BranchingSupport.lenA k r z g (Fin.last r) ^ 2 ∧ ∀ a, 0 < _root_.BranchingSupport.lenA k r z g a ∧ _root_.BranchingSupport.lenA k r z g a = _root_.Formalism.MainNotions.S.lA k r z g a := by
  intro k r z hz hT g hg
  have hpos := (_root_.GlobalTheory.TensLen.lengths k r z hz hT g hg).2.2.1
  refine ⟨?_, fun a => ⟨hpos a, _root_.BranchingSupport.TensInh.lenA_eq_lA z g a⟩⟩
  have hbound : √(_root_.Formalism.QuantumDeterminants.Tz k r z) ≤ _root_.BranchingSupport.lenA k r z g (Fin.last r) := by
    rw [_root_.BranchingSupport.TensInh.lenA_eq_lA]
    unfold _root_.Formalism.MainNotions.S.lA _root_.Formalism.MainNotions.S.eucl
    refine le_csInf ⟨_, 0, Submodule.zero_mem _, rfl⟩ ?_
    rintro t ⟨y, hy, rfl⟩
    apply Real.sqrt_le_sqrt
    have hy0 : ∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0 := by
      intro i hi
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        unfold _root_.Formalism.QuantumDeterminants.bvec _root_.Formalism.QuantumDeterminants.eI
        refine Pi.single_eq_of_ne ?_ _
        intro h
        have h' := congrArg Fin.val h
        have := b.1.isLt
        simp only at h'
        omega
      | zero => rfl
      | add x x' _ _ hx hx' => simp [hx, hx']
      | smul c x _ hx => simp [hx]
    have hf : _root_.Formalism.QuantumDeterminants.fvec k r z (Fin.last r) = z := by
      unfold _root_.Formalism.QuantumDeterminants.fvec
      simp
    rw [hf]
    calc _root_.Formalism.QuantumDeterminants.Tz k r z = -(_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ (z - y)) (g⁻¹ *ᵥ (z - y))).re := by
          rw [herm_splitForm_inv_mulVec_eq_of_mem hg, herm_splitForm_sub_eq_of_isotropic z y hz hy0,
            _root_.Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq]
          simp
      _ ≤ _ := neg_re_herm_splitForm_le_sum_normSq k r _
  calc _root_.Formalism.QuantumDeterminants.Tz k r z = √(_root_.Formalism.QuantumDeterminants.Tz k r z) ^ 2 := (Real.sq_sqrt hT.le).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2

end GlobalTheory.LastLen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSeenInDefiniteSpaceDetRankIndex
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.SeenIso

section General

variable {K U V W : Type} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem exists_proj [StarRing K] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {h0 : W →ₗ⋆[K] W →ₗ[K] K}
    (ι : W →ₗ[K] V) (hι : ∀ x y, h (ι x) (ι y) = h0 x y) (X H : Submodule K V)
    (hWX : ∀ w, ι w ∈ X → w = 0)
    (hXι : ∀ x ∈ X, ∀ w, h x (ι w) = 0) (hXH : ∀ x ∈ X, ∀ v ∈ H, h x v = 0)
    (hsp : ∀ v ∈ H, ∃ w, v - ι w ∈ X) (hHX : H ⊓ X = ⊥) :
    ∃ π : H →ₗ[K] W, Function.Injective π ∧ (∀ x y, h0 (π x) (π y) = h x y) ∧
      ∀ x : H, (x : V) - ι (π x) ∈ X := by
  obtain ⟨g, hg⟩ := (X.mkQ ∘ₗ ι).exists_leftInverse_of_injective (by
    rw [eq_bot_iff]
    intro w hw
    exact hWX w ((Submodule.Quotient.mk_eq_zero X).1 hw))
  let p : V →ₗ[K] W := g ∘ₗ X.mkQ
  have hpι : ∀ w, p (ι w) = w := fun w => LinearMap.congr_fun hg w
  have hpX : ∀ u ∈ X, p u = 0 := fun u hu => by
    have : X.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero X).2 hu
    simp only [p, LinearMap.comp_apply, this, map_zero]
  have hF : ∀ x : H, (x : V) - ι (p x) ∈ X := fun x => by
    obtain ⟨w, hw⟩ := hsp x x.2
    have := hpX _ hw
    rw [map_sub, hpι, sub_eq_zero] at this
    rwa [this]
  refine ⟨p ∘ₗ H.subtype, ?_, fun x y => ?_, hF⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have h1 : p x = 0 := hx
    have h2 := hF x
    rw [h1, map_zero, sub_zero] at h2
    have h3 : (x : V) ∈ H ⊓ X := ⟨x.2, h2⟩
    rw [hHX] at h3
    exact Subtype.ext h3
  · change h0 (p x) (p y) = _
    have a := hXH _ (hF x) _ y.2
    have b := hXι _ (hF y) (p x)
    have c : h (ι (p x)) ((y : V) - ι (p y)) = 0 := by rw [← hs.eq, b, map_zero]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at a
    rw [map_sub, sub_eq_zero] at c
    rw [a, c, hι]

variable [NumberField K] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem finrank_span_map (i : U →ₗ[K] V) (hi : Function.Injective i) (N : Submodule (𝓞 K) U) :
    finrank K (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) =
      finrank K (Submodule.span K (N : Set U)) := by
  have : ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = i '' (N : Set U) := rfl
  rw [this, ← Submodule.map_span]
  exact (Submodule.equivMapOfInjective i hi _).finrank_eq.symm

theorem card_quot_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    Nat.card (↥(A.map (i.restrictScalars (𝓞 K))) ⧸
      (B.map (i.restrictScalars (𝓞 K))).comap (A.map (i.restrictScalars (𝓞 K))).subtype) =
      Nat.card (A ⧸ B.comap A.subtype) := by
  have := AddSubgroup.relIndex_map_map_of_injective (f := i.toAddMonoidHom) B.toAddSubgroup A.toAddSubgroup hi
  exact this

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (H : Submodule D.host.E (hS D).V), WHyp D F (Wsp D) → H ≤ orth (hS D) (Xplus F) → H ⊓ Xsp F = ⊥ → ∀ N N' : LatV D, N ≤ toO (hS D) H → N' ≤ toO (hS D) H → detW D (seen D F N) = latDet (hS D) N ∧ rkW D (seen D F N) = finrank D.host.E (spanE (hS D) N) ∧ idxW D (seen D F N) (seen D F N') = idx (hS D) N N' := by
  intro D T F H hW hH hHX N N' hN hN'
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have hiso : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y := D.sp.iXY_isom 0 hm
  have hXι : ∀ x ∈ Xsp F, ∀ w, (hS D).hT x (D.sp.iXY 0 w) = 0 := fun x hx w =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 (hW.1.le (Submodule.mem_sup_left ⟨w, rfl⟩)) x (Submodule.mem_sup_left hx)
  have hWX : ∀ w, D.sp.iXY 0 w ∈ Xsp F → w = 0 := fun w hw =>
    (D.sp.X 0).nondeg.1 w fun y => by rw [← hiso]; exact hXι _ hw y
  obtain ⟨π, hinj, hπ, hF⟩ := exists_proj (hS D).herm (D.sp.iXY 0) hiso (Xsp F) H hWX hXι
    (fun x hx v hv => (Formalism.MainNotions.mem_orth_iff _ _).1 (hH hv) x (Submodule.mem_sup_left hx))
    (fun v hv => by
      obtain ⟨_, ⟨w, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 (hW.1.ge (hH hv))
      exact ⟨w, by simpa using hx⟩) hHX
  have key : ∀ M : LatV D, M ≤ toO (hS D) H → ∃ M₀ : Submodule (𝓞 D.host.E) H,
      M = M₀.map (H.subtype.restrictScalars (𝓞 D.host.E)) ∧
        seen D F M = M₀.map (π.restrictScalars (𝓞 D.host.E)) := by
    intro M hM
    refine ⟨M.comap (H.subtype.restrictScalars (𝓞 D.host.E)), ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        exact ⟨⟨x, hM hx⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy
    · ext w
      constructor
      · intro hw
        obtain ⟨l, hl, x, hx, e⟩ := Submodule.mem_sup.1 hw
        refine ⟨⟨l, hM hl⟩, hl, ?_⟩
        have e' : l + x = D.sp.iXY 0 w := e
        have h1 := (Xsp F).add_mem (hF ⟨l, hM hl⟩) hx
        have h2 : w - π ⟨l, hM hl⟩ = 0 := hWX _ (by
          rw [map_sub, ← e']
          convert h1 using 1
          abel)
        exact (sub_eq_zero.1 h2).symm
      · rintro ⟨y, hy, rfl⟩
        refine Submodule.mem_sup.2 ⟨y, hy, _, (Xsp F).neg_mem (hF y), ?_⟩
        change _ = D.sp.iXY 0 (π y)
        abel
  obtain ⟨A, rfl, a⟩ := key N hN
  obtain ⟨B, rfl, b⟩ := key N' hN'
  rw [a, b]
  refine ⟨?_, ?_, ?_⟩
  · exact (_root_.GlobalTheory.LoopC.DetMap.latDetH_map _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ π hinj hπ A).trans
      (_root_.GlobalTheory.LoopC.DetMap.latDetH_map _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ H.subtype H.injective_subtype (fun _ _ => rfl) A).symm
  · exact (finrank_span_map π hinj A).trans (finrank_span_map H.subtype H.injective_subtype A).symm
  · exact (card_quot_map π hinj A B).trans (card_quot_map H.subtype H.injective_subtype A B).symm

end GlobalTheory.LoopC.SeenIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCoeffMulInnerBesselFunctionalEqIntegral
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem coef_mul_inner_Afun_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ y : Mt k r, Matrix.of y ∈ GG k r → coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ = ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy
  have hcl := _root_.GlobalTheory.SgInf.closedSub_groups k r z hSide.1 hSide.2.1
  have hSG : Sset k r z ⊆ GG k r := hcl.2.2.2.1.1
  have hstab : ∀ g ∈ GG k r, ∀ x ∈ DD σ w, σ g x ∈ DD σ w := (_root_.GlobalTheory.SgInfDD.DD_stable_dense k r σ w hStd.2.1).1
  have hu₂ : σ (Matrix.of y) u₁ ∈ DD σ w := hstab _ hy u₁ hu₁
  have hint := (_root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hstab
    hStd.2.2.2.2.2.2.2.1 _ hu₂ v hv).1
  have hint2 := hint.apply_continuousLinearMap ξ
  have hA : Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y) =
      ∫ s, (coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ ∂μS := by
    unfold Afun be
    exact ContinuousLinearMap.integral_apply hint ξ
  have hinner : ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ =
      ∫ s, ⟪(coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ, ξ⟫_ℂ ∂μS := by
    rw [hA, ← inner_conj_symm, ← integral_inner hint2, ← integral_conj]
    congr 1; funext s; rw [inner_conj_symm]
  rw [hinner, ← integral_const_mul]
  have hS0 : μS {x | Matrix.of x ∉ Sset k r z} = 0 := hSide.2.2.2.1.2.2.1
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
    rw [ae_iff]; simpa using hS0
  filter_upwards [hae] with s hs
  have hmul : σ (Matrix.of s * Matrix.of y) = (σ (Matrix.of s)).comp (σ (Matrix.of y)) :=
    hStd.2.1.1.2 _ (hSG hs) _ hy
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left]
  have hc : coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) = coef σ u₁ v (Matrix.of s * Matrix.of y) := by
    simp only [coef, hmul, ContinuousLinearMap.comp_apply]
  rw [hc, mul_assoc]
  rfl

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFundamentalDomainOfExtension
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem prod_fundamentalDomain_of_extension : ∀ {V₁ V₂ : Type} [AddCommGroup V₁] [AddCommGroup V₂] (Λ : AddSubgroup (V₁ × V₂)) (D₁ : Set V₁) (D₂ : Set V₂), (∀ a : V₁, ∃! l, l ∈ {a : V₁ | (a, (0 : V₂)) ∈ Λ} ∧ a + l ∈ D₁) → (∀ b : V₂, ∃! l, l ∈ {b : V₂ | ∃ a : V₁, (a, b) ∈ Λ} ∧ b + l ∈ D₂) → ∀ v : V₁ × V₂, ∃! l, l ∈ Λ ∧ v + l ∈ D₁ ×ˢ D₂ := by
  intro V₁ V₂ _ _ Λ D₁ D₂ h1 h2 v
  obtain ⟨l₂, ⟨⟨s, hs⟩, hl₂D⟩, -⟩ := h2 v.2
  obtain ⟨l₁, ⟨hl₁, hl₁D⟩, -⟩ := h1 (v.1 + s)
  have hl₁' : ((l₁, 0) : V₁ × V₂) ∈ Λ := hl₁
  refine ⟨(s + l₁, l₂), ⟨?_, ?_⟩, ?_⟩
  · have e : ((s + l₁, l₂) : V₁ × V₂) = (s, l₂) + (l₁, 0) := by simp
    rw [e]; exact Λ.add_mem hs hl₁'
  · refine ⟨?_, ?_⟩
    · show v.1 + (s + l₁) ∈ D₁
      rw [← add_assoc]; exact hl₁D
    · exact hl₂D
  · rintro ⟨m₁, m₂⟩ ⟨hm, hmD⟩
    have hmD1 : v.1 + m₁ ∈ D₁ := hmD.1
    have hmD2 : v.2 + m₂ ∈ D₂ := hmD.2
    have e2 : m₂ = l₂ := (h2 v.2).unique ⟨⟨m₁, hm⟩, hmD2⟩ ⟨⟨s, hs⟩, hl₂D⟩
    subst e2
    have hx : ((m₁ - s, 0) : V₁ × V₂) ∈ Λ := by
      have := Λ.sub_mem hm hs
      simpa using this
    have e1 : m₁ - s = l₁ := (h1 (v.1 + s)).unique
      ⟨hx, by show v.1 + s + (m₁ - s) ∈ D₁; simpa using hmD1⟩ ⟨hl₁, hl₁D⟩
    have : m₁ = s + l₁ := by rw [← e1]; abel
    rw [this]

end GlobalTheory
end

