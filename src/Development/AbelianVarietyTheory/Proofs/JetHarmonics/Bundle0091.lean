module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0089
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameWConjMatrixUnits
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0090

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreePairingStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_formal_degree_pairing : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  first | exact @GlobalTheory.integral_xi_mul_Ph | exact GlobalTheory.integral_xi_mul_Ph | (intros; apply GlobalTheory.integral_xi_mul_Ph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapGrowthBoundStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_integral_equivariant_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (g * m) w) v = Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  first | exact @GlobalTheory.BesselEquiv.be_equivariant | exact GlobalTheory.BesselEquiv.be_equivariant | (intros; apply GlobalTheory.BesselEquiv.be_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapPairingStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_gap_pairing : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (w + w') v = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w' v ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (a • w) v = a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, ∀ v' ∈ R.TK, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (v + v') = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v' ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (a • v) = star a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v := by
  first | exact @GlobalTheory.besselIntegral_sesquilinear | exact GlobalTheory.besselIntegral_sesquilinear | (intros; apply GlobalTheory.besselIntegral_sesquilinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingGapBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFirstLeft

theorem sigmaFinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : B.IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun {K} hK => h.finite_compact K hK⟩
  infer_instance

theorem left_integral {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (hk : 1 ≤ k) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hl : IsBeL R z π μW μN l)
    {Y x : R.H} (hY : Y ∈ R.sm) (hx : x ∈ R.TK) :
    Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1)) (μW.prod μN) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1) ∂(μW.prod μN) =
      (innerSL ℂ (l x)).smulRight (l Y) := by
  obtain ⟨-, -, -, -, hinv, hae⟩ := _root_.GlobalTheory.sParam_measurePreserving k r z μW μN hk hz hT
    (((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).2 hW) ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1.2 hN)
  obtain ⟨-, -, hψ, -, hU, -⟩ := _root_.GlobalTheory.BesselPsi.psi_character k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hint, hbe⟩ := hl.2 Y hY x hx
  set φ := (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) with hφ
  have heq : (fun p => beInt z Formalism.QuantumDeterminants.cStd π R.σ Y x (φ p)) =ᵐ[μW.prod μN]
      (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1)) := by
    filter_upwards [hae] with p hp
    have h1 : ((Matrix.of p.1 : Mx k r)⁻¹)⁻¹ = Matrix.of p.1 :=
      Matrix.nonsing_inv_nonsing_inv _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (hU _ hp.1 _ hp.1).2.2)
    have h2 := (hψ _ hp.2).2
    change (⟪x, R.σ ((Matrix.of p.1 : Mx k r)⁻¹ * (Matrix.of p.2 : Mx k r)⁻¹) Y⟫_ℂ *
      star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2 : Mx k r)⁻¹)) • π ((Matrix.of p.1 : Mx k r)⁻¹)⁻¹ = _
    rw [h1, h2, star_star, mul_comm]
  refine ⟨((hinv.integrable_comp hint.aestronglyMeasurable).2 hint).congr heq, ?_⟩
  rw [← integral_congr_ae heq, ← hbe, be]
  have := integral_map hinv.aemeasurable (f := beInt z Formalism.QuantumDeterminants.cStd π R.σ Y x)
    (by rw [hinv.map_eq]; exact hint.aestronglyMeasurable)
  rw [hinv.map_eq] at this
  exact this.symm

theorem bessel_integrate_left : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ A : R.H → Wq → Wq → Wp, (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = A y (ContinuousLinearMap.adjoint X (l x)) c := by
  intro hyp k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hok hl hl' γ hγ
  refine ⟨fun y a c => ∫ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
    (star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of q.2)) * ⟪a, D.π' (Matrix.of q.1)⁻¹ c⟫_ℂ) •
      l (R.σ (γ * Matrix.of q.2 * Matrix.of q.1) y) ∂(D.μW'.prod D.μN), ?_, ?_⟩
  · intro y a c t
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [inner_smul_left, smul_smul]
    congr 1
    rw [starRingEnd_apply]; ring
  intro x hx y hy X c
  haveI := sigmaFinite_of_haar D.haarW
  haveI := sigmaFinite_of_haar D.haarW'
  haveI := sigmaFinite_of_haar D.haarN
  obtain ⟨hmul, -, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hyp.1.2.2.1 k r ε mu R hDS
  have hcoef : IsCoef R l l' (fun g => ⟪x, R.σ g y⟫_ℂ • X) ⟪l x, X (l' y)⟫_ℂ :=
    ⟨1, fun _ => x, fun _ => y, fun _ => X, fun _ => ⟨hx, hy⟩, fun g _ => by simp, by simp⟩
  have hcc := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hyp k r ε mu h R Wp Wq l l' _ _ hDS hgap hok hcoef).2 0
  have hint := (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ _ (_root_.GlobalTheory.thresholds_of_gapOK k r h hok).1 hcc).1 γ hγ
  have hJ : B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ =
      ∫ p, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p ∂D.μSS := rfl
  rw [hJ, ContinuousLinearMap.integral_apply hint]
  have hint' : Integrable (fun p => JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p c)
      ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) :=
    (ContinuousLinearMap.apply ℂ Wp c).integrable_comp hint
  rw [B.RealPlaceData.μSS, integral_prod_symm _ hint']
  have hae := (_root_.GlobalTheory.sParam_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos
    (((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r D.μW).2.2 _ D.z_mem D.T_pos D.k_pos).2 D.haarW)
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r D.μN).2.1.2 D.haarN)).2.2.2.2.2
  have hae' := (_root_.GlobalTheory.sParam_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos
    (((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r D.μW').2.2 _ D.z'_mem D.T'_pos D.k_pos).2 D.haarW')
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r D.μN).2.1.2 D.haarN)).2.2.2.2.2
  obtain ⟨-, -, -, -, hU, hNG⟩ := _root_.GlobalTheory.BesselPsi.psi_character k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  obtain ⟨-, -, -, -, hU', -⟩ := _root_.GlobalTheory.BesselPsi.psi_character k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  refine integral_congr_ae ?_
  filter_upwards [hae'] with q hq
  have hg : γ * Matrix.of q.2 * Matrix.of q.1 ∈ GG k r :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hγ.1 (hNG _ hq.2)) (hU' _ hq.1 _ hq.1).2.2
  obtain ⟨hI, hE⟩ := left_integral R D.z D.π D.μW D.μN l D.k_pos D.z_mem D.T_pos D.haarW D.haarN hl
    (hsm _ hg y (hTK y hy)) hx
  have hE' := congrArg (fun T : Wp →L[ℂ] Wp =>
    star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of q.2)) • T (X (D.π' (Matrix.of q.1)⁻¹ c))) hE
  simp only [ContinuousLinearMap.integral_apply hI] at hE'
  rw [← integral_smul] at hE'
  rw [ContinuousLinearMap.adjoint_inner_left, ← smul_smul]
  refine Eq.trans (integral_congr_ae ?_) hE'
  filter_upwards [hae] with p hp
  have hs : (Matrix.of p.1 : Mx k r)⁻¹ * (Matrix.of p.2 : Mx k r)⁻¹ ∈ GG k r :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (hU _ hp.1 _ hp.1).2.2) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (hNG _ hp.2))
  rw [← hmul _ hs _ hg]
  simp only [JF.integrand, JF.xiP, B.rho, B.sgs, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_smul, smul_smul, Matrix.mul_assoc]
  congr 1
  ring

end GlobalTheory.BesselFirstLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingGapBoundDualStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_orbital_integral_factors_through_right_functional : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ Bb : R.H → Wp → Wq → Wp, (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = Bb x (X (l' y)) c := by
  first | exact @GlobalTheory.besselJ_coef_through_right | exact GlobalTheory.besselJ_coef_through_right | (intros; apply GlobalTheory.besselJ_coef_through_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselXiIntegrableHolds
section
namespace GlobalTheory

theorem besselXiIntegrable_holds : GlobalTheory.HCXi.BesselXiIntegrable :=
  ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsModular
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem isMod_smooth_of_isDS : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), 1 ≤ k → R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → IsMod ε E mu := by
  intro hH k r ε mu R hk hDS Q E hQ hE
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hU : IsUnit Q := by
    have h1 : Q * star Q = 1 := (Matrix.mem_unitaryGroup_iff).1 hQ.2
    have h2 : star Q * Q = 1 := (Matrix.mem_unitaryGroup_iff').1 hQ.2
    exact ⟨⟨Q, star Q, h1, h2⟩, rfl⟩
  have hG : Formalism.REAL.GlRel E := (GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hDS Q E hU hE).1
  refine ⟨hG, GlobalTheory.T.cayley_endomorphisms_unitary hK k r ε mu R hDS Q E hQ hE, ?_⟩
  exact _root_.GlobalTheory.CapelliCasimir.cas_of_capelli R.smSub (2 * r + k + 1) E mu (by omega) hG
    (GlobalTheory.T.quantum_determinant_eigenvalue hH k r ε mu R hDS Q E hU hE)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorBesselMoment
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace BesselProjectorValue

lemma star_Hpk (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    star (Formalism.QuantumDeterminants.Hpk k r i j) = Formalism.QuantumDeterminants.Hpk k r i j := by
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

lemma ev_flat {k r : ℕ} (R : Rep k r) (f : Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1) → R.H) :
    ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r f) x = ∑ j, f j • x j := by
  unfold ev
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h1 : ∀ i, star (flat k r f i) = ∑ p, f p * Formalism.QuantumDeterminants.Hpk k r p i := by
    intro i
    simp [flat, Formalism.QuantumDeterminants.herm, dotProduct, Matrix.mulVec_single_one, Matrix.col, star_Hpk]
  simp only [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h2 : ∀ p, ∑ i, f p * Formalism.QuantumDeterminants.Hpk k r p i * Formalism.QuantumDeterminants.Hpk k r i j = f p * (1 : Mx k r) p j := by
    intro p
    rw [← Formalism.QuantumDeterminants.GBasic.Hpk_sq k r, Matrix.mul_apply, Finset.mul_sum]
    simp only [mul_assoc]
  simp only [h2, Matrix.one_apply]
  simp

lemma sum_frame {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g)
    (f : Fin n → ℂ) (x : Fin n → V) :
    ∑ j, f j • x j = ∑ d, (g⁻¹ *ᵥ f) d • ∑ c, g c d • x c := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have : (g *ᵥ (g⁻¹ *ᵥ f)) j = f j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  rw [← this]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

lemma sum_coframe {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g)
    (ω : Fin n → ℂ) (v : V) (c : Fin n) :
    ∑ d, g⁻¹ d c • ((gᵀ *ᵥ ω) d • v) = ω c • v := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  simp only [smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have : ((g⁻¹)ᵀ *ᵥ (gᵀ *ᵥ ω)) c = ω c := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.transpose_one,
      Matrix.one_mulVec]
  rw [← this]
  rfl

end BesselProjectorValue


open BesselProjectorValue in
theorem bessel_ev_projector_value : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (RI : Fin (2 * r + k + 1) → Rep k r) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp), 1 ≤ k → R.IsDS ε mu → (∀ s, (RI s).IsDS ε (mu - Pi.single s 1)) → TensRaw dualM R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π l → ∀ s, ∃ c : ℂ, ‖c‖ = Formalism.QuantumDeterminants.Tz k r z * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ v ∈ R.sm, l (ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (fun c' => io s c' (∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d)))) = c • l v := by
  intro hy k r ε mu R RI io pr Wp _ _ _ _ z π u μW μN μG νq l hk hR hRI hT hS hB s
  have hK : PI.KFinSmooth := hy.1.2.2.1
  obtain ⟨hz, hTz, ⟨u₀, hu₀⟩, hcap, -⟩ := hS
  have hπ1 : π 1 = 1 := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hTz hu₀).1
  obtain ⟨g, hg, -⟩ := hu₀
  obtain ⟨hgu, hN, ⟨hfr, hunit⟩, hf, hω⟩ := _root_.GlobalTheory.CapFrame.frame_matrix_units k r z g hz hTz hg
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hgu
  have hQ : IsUnit g⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hgu
  have hgi : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv g hd
  obtain ⟨E, hE, hEg⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR g⁻¹ hQ
  choose F hF hFg using fun t => GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε _ (RI t) (hRI t) g⁻¹ hQ
  obtain ⟨io', pr', hcomm, -, hsum, -, -, hio, hpr⟩ :=
    GlobalTheory.T.dual_tensor_cayley_compatible hK k r ε mu R hR RI _ io pr g⁻¹ E F hRI hT hQ hE hF
  have hn : 2 ≤ 2 * r + k + 1 := by omega
  have hqE := GlobalTheory.T.quantum_determinant_eigenvalue hy k r ε mu R hR g⁻¹ E hQ hE
  have hcE := _root_.GlobalTheory.CapelliCasimir.cas_of_capelli _ _ E mu hn hEg hqE
  have hcF := fun t => _root_.GlobalTheory.CapelliCasimir.cas_of_capelli _ _ (F t) _ hn (hFg t)
    (GlobalTheory.T.quantum_determinant_eigenvalue hy k r ε _ (RI t) (hRI t) g⁻¹ (F t) hQ (hF t))
  have hsp := fun t => _root_.GlobalTheory.splitCas_on_summand _ _ _ E (F t) (io' t) mu t hcE (hcF t) (hcomm t)
  let L : R.smSub →ₗ[ℂ] Wp :=
    { toFun := fun v => l v
      map_add' := fun v w => hB.1 _ v.2 _ w.2
      map_smul' := fun c v => hB.2.1 c _ v.2 }
  have hL : ∀ v : R.smSub, L v = l v := fun _ => rfl
  have hE' : ∀ a b (v : R.smSub), ((E a b v : R.smSub) : R.H) = R.dC (g * Matrix.single a b 1 * g⁻¹) v := by
    intro a b v
    rw [hE a b v, hgi]
  obtain ⟨c, hc, hcv⟩ := _root_.GlobalTheory.capelli_projector_entry_value R.smSub Wp k r E L
    (fun a b => Formalism.QuantumDeterminants.ell k r z (g * Matrix.single a b 1 * g⁻¹) - star (Formalism.QuantumDeterminants.ell k r z
      (-((Formalism.QuantumDeterminants.Hpk k r) * (g * Matrix.single a b (1 : ℂ) * g⁻¹)ᴴ * (Formalism.QuantumDeterminants.Hpk k r)))))
    (Real.sqrt (Formalism.QuantumDeterminants.Tz k r z)) hk hEg
    (fun a b hab hnot => ⟨fun v => by
      rw [hL, hL, hE']
      exact GlobalTheory.T.bessel_functional_lie_triangular_eq_character_smul hK k r ε mu R hR Wp z π l hz (fun x => by rw [hπ1]; rfl) hB _ (hN a b hab hnot).1 _ v.2,
      (hN a b hab hnot).2⟩)
    mu u (fun i j => Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r)
      (fun i : Fin k => g *ᵥ Pi.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) 1) i j))
    hR.1.1.injective hqE
    (fun i j v => by
      rw [hL, hL, hE', hunit]
      exact GlobalTheory.T.bessel_frame_entry_relation hK k r ε mu R hR Wp z π l g hz hTz hg hB i j _ v.2)
    (fun w x => hcap _ hfr w x) s
  set a : ℂ := (if r = 0 then -((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) else 1) with ha
  set b : ℂ := (if r = 0 then ((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) else 1) with hb
  set i₀ : Fin (2 * r + k + 1) := (if r = 0 then Fin.last (2 * r + k) else 0) with hi₀
  have hf' : g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z 0 = b • Pi.single i₀ 1 := by
    rw [hf, hb, hi₀]
    split_ifs <;> simp
  refine ⟨b * c * a, ?_, fun v hv => ?_⟩
  · rw [norm_mul, norm_mul, hc, ha, hb]
    have hsq : Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) ^ 2 = Formalism.QuantumDeterminants.Tz k r z := Real.sq_sqrt hTz.le
    have hab : |Real.sqrt (Formalism.QuantumDeterminants.Tz k r z)| = Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) :=
      abs_of_nonneg (Real.sqrt_nonneg _)
    split_ifs
    · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, hab]
      generalize ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) = P
      linear_combination P * hsq
    · rw [hsq, norm_one, one_mul, mul_one]
  · let v' : R.smSub := ⟨v, hv⟩
    let x : Fin (2 * r + k + 1) → R.smSub := Pi.single (Fin.last (2 * r + k)) (a • v')
    have hx : ∀ d, ((x d : R.smSub) : R.H) = (gᵀ *ᵥ flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) d • v := by
      intro d
      rw [hω]
      by_cases h : d = Fin.last (2 * r + k)
      · subst h; simp [x, v']
      · simp [x, Pi.single_eq_of_ne h]
    have hp : ((pr' s x : (RI s).smSub) : (RI s).H) =
        ∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d) := by
      rw [hpr]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [hx]
      rw [sum_coframe g hgu]
      rfl
    have hmain := hcv (a • v') (fun t => io' t (pr' t x)) (fun t => hsp t _) (hsum x)
    rw [ev_flat, sum_frame g hgu, ← hp, hf']
    have h3 : ∀ d, ∑ c', g c' d • io s c' ((pr' s x : (RI s).smSub) : (RI s).H) =
        ((io' s (pr' s x) d : R.smSub) : R.H) := by
      intro d
      rw [hio, hgi]
    simp only [h3]
    rw [Finset.sum_eq_single i₀ (fun d _ hd => by simp [Pi.single_eq_of_ne hd]) (by simp)]
    have h4 : (b • Pi.single i₀ (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i₀ = b := by simp
    rw [h4]
    have h5 : l (b • ((io' s (pr' s x) i₀ : R.smSub) : R.H)) = b • L (io' s (pr' s x) i₀) :=
      hB.2.1 b _ (io' s (pr' s x) i₀).2
    rw [h5, hmain, map_smul, hL, smul_smul, smul_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boxFamily_multilinear_map : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => Fam D F k) (Fam D' F k), ∀ (s : Fin j → Fam D F k) (S : Fam D' F k), IsBoxFam pD F k S s ↔ S = bx s := by
  intro hG R _ _ j D D' pD F _ _ k
  have hexists := GlobalTheory.BoxFamily.exists_isBoxFam hG R j D D' pD F k
  choose bx hbx using hexists
  refine ⟨⟨bx, fun s i a b => GlobalTheory.BoxLinear.box_add pD (hbx _) (hbx _) (hbx _),
    fun s i c a => GlobalTheory.BoxLinear.box_smul pD (hbx _) (hbx _)⟩,
    fun s S => ⟨fun h => GlobalTheory.BoxLinear.box_unique pD h (hbx s), ?_⟩⟩
  rintro rfl
  exact hbx s
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapCoefficientDerivativeBoundStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → IsBeL R z π μW μN l → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → NzOn R l → IsIsoB R z π νq (fun w => ((Real.sqrt dd : ℝ) : ℂ) • l w) := by
  first | exact @GlobalTheory.scaled_bessel_isometric | exact GlobalTheory.scaled_bessel_isometric | (intros; apply GlobalTheory.scaled_bessel_isometric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSumStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_weighted_bessel_sum : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → IsCoef R l l' F s → ∃ (Ft : κ → Mx k r → (Wq →L[ℂ] Wp)) (st : κ → ℂ), (∀ I, IsCoef (RI I) (lI I) (lI' I) (Ft I) (st I)) ∧ (∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om • F g = ∑ I, Ft I g) ∧ (∀ I, (¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) → st I = 0) ∧ ∀ I (κ₀ κ₁ : ℂ), (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) → st I = (ep I : ℂ) * κ₁ * star κ₀ * s := by
  first | exact @GlobalTheory.coef_mul_split | exact GlobalTheory.coef_mul_split | (intros; apply GlobalTheory.coef_mul_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilPairingPowPolAVEqProdFieldStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_powPolAV_eq_prod_field : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (x x' : TFK (R := R) F ⟶ A'.A) (c : Fin j → Fˣ), (∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (x' ≫ pA.pr i) (unitOn (c i))) → WeilIs A'.A A'.L k x x' (unitOn (∏ i, c i)) := by
  first | exact @GlobalTheory.WeilPower.weilIs_pow_field | exact GlobalTheory.WeilPower.weilIs_pow_field | (intros; apply GlobalTheory.WeilPower.weilIs_pow_field <;> assumption)
end

