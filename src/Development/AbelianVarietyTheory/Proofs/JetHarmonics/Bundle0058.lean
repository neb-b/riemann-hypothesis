module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsIsCayleyUIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapNormIdentity
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselAdjoint

theorem integral_comp_involution {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ) (hTT : ∀ᵐ p ∂μ, T (T p) = p) (f : X → E) :
    ∫ p, f (T p) ∂μ = ∫ p, f p ∂μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · have h1 : AEStronglyMeasurable f (μ.map T) := by rw [hT.map_eq]; exact hf
    rw [← integral_map hT.measurable.aemeasurable h1, hT.map_eq]
  · have hg : ¬ AEStronglyMeasurable (fun p => f (T p)) μ := by
      intro hg
      apply hf
      refine (hg.comp_measurePreserving hT).congr ?_
      filter_upwards [hTT] with p hp
      simp [hp]
    rw [integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable hg]

def adjR (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] :
    (W →L[ℂ] W) →ₗᵢ[ℝ] (W →L[ℂ] W) where
  toFun A := ContinuousLinearMap.adjoint A
  map_add' A B := map_add _ A B
  map_smul' c A := by
    have e : ∀ B : W →L[ℂ] W, c • B = (c : ℂ) • B := fun B => by
      ext x; simp
    rw [RingHom.id_apply, e, e, map_smulₛₗ]; simp
  norm_map' A := ContinuousLinearMap.adjoint.norm_map A

theorem adjoint_integral {X W : Type*} [MeasurableSpace X] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (μ : Measure X) (f : X → (W →L[ℂ] W)) :
    ContinuousLinearMap.adjoint (∫ p, f p ∂μ) = ∫ p, ContinuousLinearMap.adjoint (f p) ∂μ :=
  ((adjR W).integral_comp_comm f).symm

theorem adjoint_be : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.TK, ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v w := by
  intro _ k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS _ hOK hS v _ w _
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨-, hinv, -, -, -, hae⟩ := _root_.GlobalTheory.sParam_measurePreserving k r z μW μN hOK.1 hz hT hW hN
  obtain ⟨-, -, hψi, hψc, hUW, hNG⟩ := GlobalTheory.BesselPsi.psi_character k r z Formalism.QuantumDeterminants.cStd hz
  unfold be
  rw [adjoint_integral, ← integral_comp_involution hinv ?_ (beInt z Formalism.QuantumDeterminants.cStd π R.σ v w)]
  · refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hi, hhi, hih⟩ := P.MatrixMultiplicationContinuity.uw_inv hp1
    have hg1 : Matrix.of p.1 ∈ GG k r := hp1.1
    have hg2 : Matrix.of p.2 ∈ GG k r := hp2.1
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := by
      have a1 : (Matrix.of p.1)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.1 = Formalism.QuantumDeterminants.Hpk k r := hg1
      have a2 : (Matrix.of p.2)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.2 = Formalism.QuantumDeterminants.Hpk k r := hg2
      show (Matrix.of p.1 * Matrix.of p.2)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p.1 * Matrix.of p.2) = Formalism.QuantumDeterminants.Hpk k r
      calc _ = (Matrix.of p.2)ᴴ * ((Matrix.of p.1)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.1) * Matrix.of p.2 := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [a1, a2]
    have hii : ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.1 : Mx k r) := Matrix.inv_eq_left_inv hhi
    have e1 : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
        ((Matrix.of p.1 * Matrix.of p.2)⁻¹ : Mx k r) := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hih, Matrix.one_mul]
    have e2 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2)) := by
      rw [(hψc _ hp1 _ (hψi _ hp2).1).2.2.1, (hψi _ hp2).2]
    have e3 : ContinuousLinearMap.adjoint (π (Matrix.of p.1)⁻¹) = π (Matrix.of p.1) := by
      symm
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      rw [P.MatrixMultiplicationContinuity.piW_inner hT hπ hi, hii]
    show ContinuousLinearMap.adjoint ((⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹) =
      (⟪w, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)) v⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹))) •
        π ((Matrix.of p.1)⁻¹)⁻¹
    rw [e1, e2, hii, map_smulₛₗ, e3, P.MatrixMultiplicationContinuity.sigma_inner hDS.2 hg v w, map_mul, inner_conj_symm]
    rfl
  · filter_upwards [hae] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hi, hhi, hih⟩ := P.MatrixMultiplicationContinuity.uw_inv hp1
    obtain ⟨-, hni, hin⟩ := P.MatrixMultiplicationContinuity.uh_inv hp2.1
    have hii : ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.1 : Mx k r) := Matrix.inv_eq_left_inv hhi
    have hnn : ((Matrix.of p.2)⁻¹)⁻¹ = (Matrix.of p.2 : Mx k r) := Matrix.inv_eq_left_inv hni
    have e : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)⁻¹ * ((Matrix.of p.1)⁻¹)⁻¹ =
        (Matrix.of p.2 : Mx k r) := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hii, hnn, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hih,
        Matrix.one_mul, Matrix.mul_assoc, hih, Matrix.mul_one]
    exact Prod.ext hii e

end GlobalTheory.BesselAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotent
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace BesselGrowth

theorem continuous_hsNorm (k r : ℕ) :
    Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r)) := by
  unfold Formalism.FourierDecayAlt.B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  refine Complex.continuous_normSq.comp ?_
  exact (continuous_apply j).comp (continuous_apply i)

theorem measurable_hsNorm_rpow (k r : ℕ) (A : ℝ) :
    Measurable (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A)) :=
  (continuous_hsNorm k r).measurable.pow_const _

theorem hsNorm_nonneg {k r : ℕ} (g : Mx k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN g := Real.sqrt_nonneg _

theorem growthS_of (hN : NormInv) (hG : GrowthG) : GrowthS := by
  intro k r z μW μN μG νq A _ _ hW hNn hGm hq hA
  obtain ⟨hS0, hS⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hNn
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hGm.2.2.1 hS0 hS hq
  have hA0 : 0 ≤ A := by
    have : 0 ≤ AG k r := by unfold AG; positivity
    linarith
  have hint := hG k r μG A hGm hA
  have hm := measurable_hsNorm_rpow k r A
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A)) with hF
  have hFm : Measurable F := hm.ennreal_ofReal
  have hfin : ∫⁻ x, F x ∂μG < ⊤ := hint.lintegral_lt_top
  have hν : νq Set.univ ≠ 0 := by
    intro h0
    have h1 := hq (fun _ => 1) measurable_const
    rw [Measure.measure_univ_eq_zero.mp h0, lintegral_zero_measure, lintegral_one] at h1
    exact hGm.2.1 (Measure.measure_univ_eq_zero.mp h1)
  have hSfin : ∫⁻ s, F s ∂(muSof μW μN) < ⊤ := by
    by_contra hc
    have htop : ∫⁻ s, F s ∂(muSof μW μN) = ⊤ := top_le_iff.mp (not_lt.mp hc)
    have hle : ∫⁻ _x, (⊤ : ℝ≥0∞) ∂νq ≤
        ∫⁻ x, (∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muSof μW μN)) ∂νq := by
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with x hx
      have hx1 := ((hN k r).2 _ hx).2
      have hFx : F x ≠ 0 := by
        simp only [hF, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact Real.rpow_pos_of_pos (by linarith) _
      have h2 : ∫⁻ s, F s * F x ∂(muSof μW μN) = ⊤ := by
        rw [lintegral_mul_const _ hFm, htop, ENNReal.top_mul hFx]
      rw [← h2]
      refine lintegral_mono_ae ?_
      filter_upwards [(ae_iff.mpr hS : ∀ᵐ s ∂(muSof μW μN),
        Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))] with s hs
      have hsx := ((hN k r).2 _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hs hx)).2
      simp only [hF]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hsNorm_nonneg _) _),
        ← Real.mul_rpow (hsNorm_nonneg _) (hsNorm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos hsx) ((hN k r).1 _ _) (by linarith)
    rw [← hq F hFm, lintegral_const, ENNReal.top_mul hν] at hle
    exact absurd hfin (not_lt.mpr hle)
  have hf : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) :=
      continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) :=
      continuous_snd
    exact h1.matrix_mul h2
  have hI : Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A))
      (muSof μW μN) :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hsNorm_nonneg _) _)).mpr hSfin⟩
  exact (integrable_map_measure hm.aestronglyMeasurable hf.measurable.aemeasurable).mp hI

end BesselGrowth

theorem besselGrowthS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS :=
  BesselGrowth.growthS_of _root_.GlobalTheory.BesselNorm.hilbertSchmidt_normInv _root_.GlobalTheory.gN_rpow_neg_integrable_haar

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimirStatement
section
open Formalism.REAL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V), (∀ u x, K u ((u - 0) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧ ∀ u v, K u (PiLp.single 2 (Fin.last n) v) = qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) v := by
  first | exact @GlobalTheory.comatrix_last_row_inverts_casimir | exact GlobalTheory.comatrix_last_row_inverts_casimir | (intros; apply GlobalTheory.comatrix_last_row_inverts_casimir <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexifiedDerivedActionLieHomGramAdjoint
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.ComplexifiedAction

open PI.UpqRep GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gram_herm (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1

theorem gram_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1

theorem lie_iff {X : Mx k r} : InLieHpk k r X ↔ Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := Iff.rfl

theorem adj_of_lie {X : Mx k r} (hX : InLieHpk k r X) :
    Formalism.QuantumDeterminants.Hpk k r * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X := by
  have h := eq_neg_of_add_eq_zero_left (lie_iff.1 hX)
  rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, gram_sq, Matrix.one_mul]

theorem lie_of_adj {X : Mx k r} (h : Formalism.QuantumDeterminants.Hpk k r * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X) : InLieHpk k r X := by
  rw [lie_iff]
  have h2 := congrArg (fun A => Formalism.QuantumDeterminants.Hpk k r * A) h
  simp only [← Matrix.mul_assoc, gram_sq, Matrix.one_mul, Matrix.mul_neg] at h2
  rw [h2, neg_add_cancel]

theorem adj_adj (Y : Mx k r) :
    Formalism.QuantumDeterminants.Hpk k r * (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Y := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, gram_herm, ← Matrix.mul_assoc, gram_sq, Matrix.one_mul]
  rw [Matrix.mul_assoc, gram_sq, Matrix.mul_one]

theorem lie_re (Y : Mx k r) :
    InLieHpk k r ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  apply lie_of_adj
  have e : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, adj_adj, e]
  module

theorem lie_im (Y : Mx k r) :
    InLieHpk k r ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  apply lie_of_adj
  have e : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, adj_adj, e]
  module

theorem exists_decomp (Y : Mx k r) : ∃ X₁ X₂, InLieHpk k r X₁ ∧ InLieHpk k r X₂ ∧ Y = X₁ + Complex.I • X₂ := by
  refine ⟨_, _, lie_re Y, lie_im Y, ?_⟩
  have e : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [smul_smul, e]
  module

theorem adj_decomp {X₁ X₂ : Mx k r} (h₁ : InLieHpk k r X₁) (h₂ : InLieHpk k r X₂) :
    Formalism.QuantumDeterminants.Hpk k r * (X₁ + Complex.I • X₂)ᴴ * Formalism.QuantumDeterminants.Hpk k r = -X₁ + Complex.I • X₂ := by
  have e : star Complex.I = -Complex.I := by simp
  rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    adj_of_lie h₁, adj_of_lie h₂, e]
  module

theorem dC_decomp (R : Rep k r) {X₁ X₂ : Mx k r} (h₁ : InLieHpk k r X₁) (h₂ : InLieHpk k r X₂) (v : R.H) :
    R.dC (X₁ + Complex.I • X₂) v =
      dsig (k := k) (r := r) R.σ X₁ v + Complex.I • dsig (k := k) (r := r) R.σ X₂ v := by
  have e : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1 := by field_simp
  have e1 : (1 / 2 : ℂ) • (X₁ + Complex.I • X₂ + -(-X₁ + Complex.I • X₂)) = X₁ := by module
  have e2 : (1 / (2 * Complex.I)) • (X₁ + Complex.I • X₂ - -(-X₁ + Complex.I • X₂)) = X₂ := by
    have : X₁ + Complex.I • X₂ - -(-X₁ + Complex.I • X₂) = (2 * Complex.I) • X₂ := by module
    rw [this, smul_smul, e, one_smul]
  unfold Rep.dC
  rw [adj_decomp h₁ h₂, e1, e2]

theorem lie_zero : InLieHpk k r 0 := by rw [lie_iff]; simp

theorem lie_add {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) : InLieHpk k r (X + Y) := by
  apply lie_of_adj
  rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, adj_of_lie hX, adj_of_lie hY, neg_add]

theorem lie_smul (a : ℝ) {X : Mx k r} (hX : InLieHpk k r X) : InLieHpk k r (a • X) := by
  apply lie_of_adj
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, adj_of_lie hX, star_trivial, smul_neg]

theorem lie_neg {X : Mx k r} (hX : InLieHpk k r X) : InLieHpk k r (-X) := by
  simpa using lie_smul (-1) hX

theorem lie_br {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) : InLieHpk k r (X * Y - Y * X) := by
  have h1 := eq_neg_of_add_eq_zero_left (lie_iff.1 hX)
  have h2 := eq_neg_of_add_eq_zero_left (lie_iff.1 hY)
  rw [lie_iff]
  generalize Formalism.QuantumDeterminants.Hpk k r = H at h1 h2 ⊢
  have e1 : (X * Y)ᴴ * H = H * (Y * X) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.neg_mul, neg_neg,
      Matrix.mul_assoc]
  have e2 : (Y * X)ᴴ * H = H * (X * Y) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, h2, Matrix.mul_neg, ← Matrix.mul_assoc, h1, Matrix.neg_mul, neg_neg,
      Matrix.mul_assoc]
  rw [conjTranspose_sub, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel

theorem dsig_add_left (R : Rep k r) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (X + Y) v =
      dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ Y v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  rw [(hL _ hX).1, (hL _ hY).1, (hL _ (lie_add hX hY)).1, map_add (f := _)]

theorem dsig_smul_left (R : Rep k r) (a : ℝ) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (a • X) v = (a : ℂ) • dsig (k := k) (r := r) R.σ X v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  rw [(hL _ hX).1, (hL _ (lie_smul a hX)).1, map_smul, Complex.coe_smul]

theorem dsig_neg_left (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (-X) v = -dsig (k := k) (r := r) R.σ X v := by
  simpa using dsig_smul_left R (-1) hX hv

theorem dC_lie (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    R.dC X v = dsig (k := k) (r := r) R.σ X v := by
  have h := dC_decomp R hX lie_zero v
  have h0 := dsig_smul_left R 0 hX hv
  rw [zero_smul] at h0
  rw [smul_zero, add_zero, h0] at h
  simpa using h

theorem dC_lin_left (R : Rep k r) (Y Z : Mx k r) (a : ℂ) {v : R.H} (hv : v ∈ R.sm) :
    R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v := by
  obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
  obtain ⟨Z₁, Z₂, h3, h4, rfl⟩ := exists_decomp Z
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, a = x + y * Complex.I := ⟨a.re, a.im, (Complex.re_add_im a).symm⟩
  have e : ((x : ℂ) + y * Complex.I) • (Y₁ + Complex.I • Y₂) + (Z₁ + Complex.I • Z₂) =
      (x • Y₁ + (-y) • Y₂ + Z₁) + Complex.I • (y • Y₁ + x • Y₂ + Z₂) := by
    simp only [← Complex.coe_smul]
    push_cast
    linear_combination (norm := module) (y * Complex.I_mul_I) • Y₂
  have a1 := lie_smul x h1
  have a2 := lie_smul (-y) h2
  have a3 := lie_smul y h1
  have a4 := lie_smul x h2
  rw [e, dC_decomp R (lie_add (lie_add a1 a2) h3) (lie_add (lie_add a3 a4) h4), dC_decomp R h1 h2,
    dC_decomp R h3 h4, dsig_add_left R (lie_add a1 a2) h3 hv, dsig_add_left R a1 a2 hv,
    dsig_add_left R (lie_add a3 a4) h4 hv, dsig_add_left R a3 a4 hv, dsig_smul_left R _ h1 hv,
    dsig_smul_left R _ h2 hv, dsig_smul_left R _ h1 hv, dsig_smul_left R _ h2 hv]
  push_cast
  linear_combination (norm := module) (-(y : ℂ) * Complex.I_mul_I) • dsig (k := k) (r := r) R.σ Y₂ v

theorem complexified_action : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ Y, ∀ v ∈ R.sm, R.dC Y v ∈ R.sm) ∧ (∀ Y (a : ℂ), ∀ v ∈ R.sm, ∀ w ∈ R.sm, R.dC Y (a • v + w) = a • R.dC Y v + R.dC Y w) ∧ (∀ Y Z (a : ℂ), ∀ v ∈ R.sm, R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v) ∧ (∀ X, PI.UpqRep.InLieHpk k r X → ∀ v ∈ R.sm, R.dC X v = PI.UpqRep.dsig (k := k) (r := r) R.σ X v) ∧ (∀ Y Z, ∀ v ∈ R.sm, R.dC Y (R.dC Z v) - R.dC Z (R.dC Y v) = R.dC (Y * Z - Z * Y) v) ∧ ∀ Y, ∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪R.dC Y v, w⟫_ℂ = ⟪v, R.dC ((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r)) w⟫_ℂ := by
  intro hK k r ε mu R hR
  have hsm : ∀ {X}, InLieHpk k r X → ∀ {v}, v ∈ R.sm → dsig (k := k) (r := r) R.σ X v ∈ R.sm :=
    fun hX _ hv => dsig_smooth hR.2 hX hv
  have hlin : ∀ {X}, InLieHpk k r X → ∀ (a : ℂ) {v w}, v ∈ R.sm → w ∈ R.sm →
      dsig (k := k) (r := r) R.σ X (v + a • w) =
        dsig (k := k) (r := r) R.σ X v + a • dsig (k := k) (r := r) R.σ X w := by
    intro X hX a v w hv hw
    rw [dsig_add hX hv (R.smSub.smul_mem a hw), dsig_smul hX a hw]
  refine ⟨fun Y v hv => ?_, fun Y a v hv w hw => ?_, fun Y Z a v hv => dC_lin_left R Y Z a hv,
    fun X hX v hv => dC_lie R hX hv, fun Y Z v hv => ?_, fun Y v hv w hw => ?_⟩
  · exact R.smSub.add_mem (hsm (lie_re Y) hv) (R.smSub.smul_mem _ (hsm (lie_im Y) hv))
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    rw [dC_decomp R h1 h2, dC_decomp R h1 h2, dC_decomp R h1 h2, add_comm (a • v) w, hlin h1 a hw hv,
      hlin h2 a hw hv]
    module
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    obtain ⟨Z₁, Z₂, h3, h4, rfl⟩ := exists_decomp Z
    have e : (Y₁ + Complex.I • Y₂) * (Z₁ + Complex.I • Z₂) - (Z₁ + Complex.I • Z₂) * (Y₁ + Complex.I • Y₂) =
        ((Y₁ * Z₁ - Z₁ * Y₁) + -(Y₂ * Z₂ - Z₂ * Y₂)) + Complex.I • ((Y₁ * Z₂ - Z₂ * Y₁) + (Y₂ * Z₁ - Z₁ * Y₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
      linear_combination (norm := module) Complex.I_mul_I • (Y₂ * Z₂ - Z₂ * Y₂)
    have b := GlobalTheory.DerivedBracket.derived_action_bracket hK k r ε mu R hR
    rw [e, dC_decomp R (lie_add (lie_br h1 h3) (lie_neg (lie_br h2 h4))) (lie_add (lie_br h1 h4) (lie_br h2 h3)),
      dsig_add_left R (lie_br h1 h3) (lie_neg (lie_br h2 h4)) hv, dsig_neg_left R (lie_br h2 h4) hv,
      dsig_add_left R (lie_br h1 h4) (lie_br h2 h3) hv, ← b _ _ h1 h3 v hv, ← b _ _ h2 h4 v hv,
      ← b _ _ h1 h4 v hv, ← b _ _ h2 h3 v hv]
    simp only [dC_decomp R h1 h2, dC_decomp R h3 h4]
    rw [hlin h1 _ (hsm h3 hv) (hsm h4 hv), hlin h2 _ (hsm h3 hv) (hsm h4 hv), hlin h3 _ (hsm h1 hv) (hsm h2 hv),
      hlin h4 _ (hsm h1 hv) (hsm h2 hv)]
    linear_combination (norm := module) Complex.I_mul_I • (dsig (k := k) (r := r) R.σ Y₂ (dsig (k := k) (r := r) R.σ Z₂ v) -
      dsig (k := k) (r := r) R.σ Z₂ (dsig (k := k) (r := r) R.σ Y₂ v))
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    rw [adj_decomp h1 h2, dC_decomp R h1 h2, dC_decomp R (lie_neg h1) h2, dsig_neg_left R h1 hw, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, inner_neg_right, dsig_skew hR.2 h1 hv hw,
      dsig_skew hR.2 h2 hv hw, Complex.conj_I]
    ring

end GlobalTheory.ComplexifiedAction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayInputsOfDecAll
section
noncomputable section

namespace GlobalTheory.DecTransport

open Matrix Finset
open scoped InnerProductSpace
open Formalism.QuantumDeterminants (UH Hpk IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
open GlobalTheory.Count (dOp rkR)
open GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap (Mat decExp dimV DecGap DecKFin DecSmooth)

lemma hs_le_op {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, Complex.normSq (x i j) ≤ n * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ ^ 2 := by
  rw [Finset.sum_comm]
  have h : ∀ j, ∑ i, Complex.normSq (x i j) ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ ^ 2 := by
    intro j
    have h1 := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x).le_opNorm (EuclideanSpace.single j (1 : ℂ))
    rw [PiLp.norm_single, norm_one, mul_one] at h1
    refine le_trans (le_of_eq ?_) (pow_le_pow_left₀ (norm_nonneg _) h1 2)
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq]
    congr 2
    have := GlobalTheory.Dec.stdRep_apply x (EuclideanSpace.single j (1 : ℂ)) i
    simp only [GlobalTheory.Dec.stdRep] at this
    rw [this]
    simp
  calc _ ≤ ∑ _j : Fin n, ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ ^ 2 := Finset.sum_le_sum fun j _ => h j
    _ = _ := by simp

lemma op_conj {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (P * x * star P)‖ =
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ := by
  have hu : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P ∈ unitary _ := by
    rw [Unitary.mem_iff, ← map_star, ← map_mul, ← map_mul, Unitary.star_mul_self_of_mem hP,
      Unitary.mul_star_self_of_mem hP, map_one]
    exact ⟨rfl, rfl⟩
  rw [map_mul, map_mul, map_star, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu),
    CStarRing.norm_mem_unitary_mul _ hu]

lemma rkR_eq {k r : ℕ} (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
    (hP : PI.UpqRep.IsCayleyU k r ε P) : rkR ε = r + 1 := by
  have h1 := (GlobalTheory.UnitaryCayley.exists_isCayleyU_iff k r ε).1 ⟨P, hP⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * r + k + 1))))
    (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h2
  unfold rkR
  omega

lemma exp_le_rpow {a b c N G : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c) (hN : 0 ≤ Real.log N) (hG : 0 < G)
    (hGN : G ≤ c * N) : Real.exp (-b * Real.log N) ≤ c ^ a * G ^ (-a) := by
  have hN0 : 0 < N := by
    by_contra h
    nlinarith [mul_nonneg hc.le (neg_nonneg.2 (not_lt.1 h))]
  have hl := Real.log_le_log hG hGN
  rw [Real.log_mul hc.ne' hN0.ne'] at hl
  rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hG, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left hl ha, mul_le_mul_of_nonneg_right hab hN]

lemma gN_pos {k r : ℕ} {x : Mat k r} (hx : x ∈ UH (Hpk k r)) : 0 < gN x := by
  refine lt_of_le_of_ne (Real.sqrt_nonneg _) fun h => ?_
  have h0 : ∑ i, ∑ j, Complex.normSq (x i j) = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).1 h.symm
  have hx0 : x = 0 := by
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (x i j)).1 h0 i (mem_univ _)
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg (x i j)).1 h1 j (mem_univ _))
  have h2 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have h3 : xᴴ * Hpk k r * x = Hpk k r := hx
  rw [hx0, Matrix.mul_zero] at h3
  rw [← h3, Matrix.mul_zero] at h2
  exact zero_ne_one h2

end GlobalTheory.DecTransport
end
end

