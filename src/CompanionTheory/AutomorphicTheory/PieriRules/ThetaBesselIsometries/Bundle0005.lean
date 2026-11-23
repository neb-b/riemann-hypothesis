module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0004
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjoint
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrechetContinuousContinuousOnOrbitHasDerivAt
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeries

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreeIdentityStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_formal_degree_identity : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (dd : ℝ), R.IsDG ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ (x y x' y' : R.H) (X X' : Wq →L[ℂ] Wp) (p : B.SS k r), D.inSS p → Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g)) (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) D.μG ∧ B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p = ⟪y', R.σ (JF.sR p) y⟫_ℂ * ⟪R.σ (JF.sL p) x, x'⟫_ℂ / (dd : ℂ) * B.hsInner ((D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹))) X' := by
  first | exact @GlobalTheory.BesselPhi.Ph_coeff | exact GlobalTheory.BesselPhi.Ph_coeff | (intros; apply GlobalTheory.BesselPhi.Ph_coeff <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapGrowthBound
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselEquiv

theorem integral_smul_comp_of_measurePreserving {X Wp : Type} [MeasurableSpace X] [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [CompleteSpace Wp] {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    {F F' : X → (Wp →L[ℂ] Wp)} (hF : Integrable F μ) (c : ℂ) (A : Wp →L[ℂ] Wp)
    (h : ∀ᵐ p ∂μ, F' p = c • A.comp (F (T p))) :
    ∫ p, F' p ∂μ = c • A.comp (∫ p, F p ∂μ) := by
  have hFT : Integrable (fun p => F (T p)) μ := hT.integrable_comp_of_integrable hF
  have e1 : ∫ p, F (T p) ∂μ = ∫ p, F p ∂μ := by
    have := integral_map (μ := μ) (φ := T) (f := F) hT.measurable.aemeasurable
      (by rw [hT.map_eq]; exact hF.aestronglyMeasurable)
    rw [hT.map_eq] at this
    exact this.symm
  rw [integral_congr_ae h, integral_smul, ← e1]
  congr 1
  exact (ContinuousLinearMap.compL ℂ Wp Wp Wp A).integral_comp_comm hFT

theorem be_equivariant : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (g * m) w) v = Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv w hw g hg m hm
  have hint := (GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv).1 w hw
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨hψ1, hψm, -, hψc, hUW, hNG⟩ := _root_.GlobalTheory.BesselPsi.psi_character k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hmp, -, -, -, -, hae⟩ := _root_.GlobalTheory.sParam_measurePreserving k r z μW μN hok.1 hz hT hW hN
  have hσ := (GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS).1
  have hπm := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ).2.1
  have hGm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := by
    intro a ha b hb
    have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
    have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
    show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
    calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [ha', hb']
  unfold be
  refine integral_smul_comp_of_measurePreserving (hmp g hg m hm).1 hint _ _ ?_
  filter_upwards [hae] with p hp
  obtain ⟨ha, hn⟩ := hp
  have key : ∀ a ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r,
      (⟪v, R.σ (a * n) (R.σ (g * m) w)⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd n)) • π a⁻¹ =
      Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp
        ((⟪v, R.σ (a * g * (g⁻¹ * n * g * m)) w⟫_ℂ *
          star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (g⁻¹ * n * g * m))) • π (a * g)⁻¹) := by
    intro a ha n hn
    obtain ⟨hag, -, haG⟩ := hUW a ha g hg
    have hgG := (hUW g hg g hg).2.2
    obtain ⟨-, hgg, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hg
    obtain ⟨hagi, -, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hag
    obtain ⟨-, hc, -, hcψ⟩ := hψc g hg n hn
    have e1 : a * g * (g⁻¹ * n * g * m) = a * n * (g * m) := by
      calc a * g * (g⁻¹ * n * g * m) = a * (g * g⁻¹) * n * (g * m) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgg, Matrix.mul_one]
    have e2 : g * (a * g)⁻¹ = a⁻¹ := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
    have e3 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ1 m]; simp
    rw [e1, hσ _ (hGm a haG n (hNG n hn)) _ (hGm g hgG m (hNG m hm)), (hψm _ hc m hm).2, hcψ,
      ContinuousLinearMap.comp_smul, ← hπm g hg _ hagi, e2, smul_smul, star_mul']
    congr 1
    linear_combination (-(⟪v, R.σ (a * n) (R.σ (g * m) w)⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd n))) * e3
  exact key _ ha _ hn

end GlobalTheory.BesselEquiv
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapPairing
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselIntegral_sesquilinear : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (w + w') v = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w' v ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (a • w) v = a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, ∀ v' ∈ R.TK, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (v + v') = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v' ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (a • v) = star a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v := by
  intro hG k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDG hGap hOK hSide
  have hI := Gp91.GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hG k r ε mu h R Wp z π u μW μN μG νq hDG hGap hOK hSide
  refine ⟨fun v hv w hw w' hw' a => ⟨?_, ?_⟩, fun w hw v hv v' hv' a => ⟨?_, ?_⟩⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_add ((hI v hv).1 w hw) ((hI v hv).1 w' hw')]
    congr 1
    funext p
    simp only [beInt, map_add, inner_add_right, add_mul, add_smul]
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_smul]
    congr 1
    funext p
    simp only [beInt, map_smul, inner_smul_right, smul_smul]
    congr 1
    ring
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_add ((hI v hv).1 w hw) ((hI v' hv').1 w hw)]
    congr 1
    funext p
    simp only [beInt, inner_add_left, add_mul, add_smul]
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_smul]
    congr 1
    funext p
    simp only [beInt, inner_smul_left, smul_smul]
    congr 1
    simp only [← Complex.star_def]
    ac_rfl

end GlobalTheory
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjointStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → (∀ Y, ∀ v ∈ R.sm, R.dC Y v ∈ R.sm) ∧ (∀ Y (a : ℂ), ∀ v ∈ R.sm, ∀ w ∈ R.sm, R.dC Y (a • v + w) = a • R.dC Y v + R.dC Y w) ∧ (∀ Y Z (a : ℂ), ∀ v ∈ R.sm, R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v) ∧ (∀ X, PI.UpqRep.InLieHpk k r X → ∀ v ∈ R.sm, R.dC X v = PI.UpqRep.dsig (k := k) (r := r) R.σ X v) ∧ (∀ Y Z, ∀ v ∈ R.sm, R.dC Y (R.dC Z v) - R.dC Z (R.dC Y v) = R.dC (Y * Z - Z * Y) v) ∧ ∀ Y, ∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪R.dC Y v, w⟫_ℂ = ⟪v, R.dC ((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r)) w⟫_ℂ := by
  first | exact @GlobalTheory.ComplexifiedAction.complexified_action | exact GlobalTheory.ComplexifiedAction.complexified_action | (intros; apply GlobalTheory.ComplexifiedAction.complexified_action <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorCapelliIntertwine
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DualEmb

open PI.UpqRep GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

private theorem hasDerivAt_exp_smul_apply_zero'
    (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j c : Fin (2 * r + k + 1)) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y) j c) (Y j c) 0 := by
  letI instNR : NormedRing (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    Matrix.linftyOpNormedAlgebra
  haveI : @CompleteSpace (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      (@PseudoMetricSpace.toUniformSpace _ (@SeminormedRing.toPseudoMetricSpace _
        (@NormedRing.toSeminormedRing _ instNR))) :=
    (inferInstance : CompleteSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • Y))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y) ((0 : ℝ) : ℂ) := hasDerivAt_exp_smul_const Y _
  let f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M j c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let e : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap f
  have he : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, e M = M j c := fun M => rfl
  have h2 := (e.hasFDerivAt.comp_hasDerivAt _ h1).comp_ofReal
  simp only [Function.comp_def, he, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

theorem hasDerivAt_inv_exp_entry (X : Mx k r) (j c : Fin (2 * r + k + 1)) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c) (-X j c) 0 := by
  have h := hasDerivAt_exp_smul_apply_zero' (-X) j c
  have hfun : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c) =
      fun s : ℝ => NormedSpace.exp ((s : ℂ) • (-X)) j c := by
    funext t
    rw [smul_neg, Matrix.exp_neg]
  rw [hfun]
  simpa using h

theorem lie_part₁ (Y : Mx k r) :
    InLieHpk k r ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  have hI := Gp91.GlobalTheory.CWDeriv.hInvol k r
  have h := (AAInvW.ana_hpartMem hI Y).1
  rw [AAInvW.ana_hpart1_eq hI] at h
  rw [← sub_eq_add_neg]
  exact h

theorem lie_part₂ (Y : Mx k r) :
    InLieHpk k r ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  have hI := Gp91.GlobalTheory.CWDeriv.hInvol k r
  have h := (AAInvW.ana_hpartMem hI Y).2.1
  rw [AAInvW.ana_hpart2_eq hI] at h
  rw [sub_neg_eq_add]
  exact h

theorem io_dsig (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDG ε mu) {RI : Fin (2 * r + k + 1) → Rep k r}
    {muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ}
    {io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H} {pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H}
    (hI : ∀ s, (RI s).IsDG ε (muI s)) (hT : TensRaw dualM R RI io pr) (s : Fin (2 * r + k + 1))
    {X : Mx k r} (hX : InLieHpk k r X) {y : (RI s).H} (hy : y ∈ (RI s).sm) (c : Fin (2 * r + k + 1)) :
    io s c (dsig (k := k) (r := r) (RI s).σ X y) =
      dsig (k := k) (r := r) R.σ X (io s c y) - ∑ j, X j c • io s j y := by
  classical
  have hsmc := hT.io_sm s c
  have hcw : PI.BesselMapUniq.IsCWCont (RI s).σ (io s c) := by
    have h0 := hsmc.cont [] (by simp)
    exact h0
  have hL := ((Gp91.GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r ε (muI s) (RI s) (hI s) R.H (io s c)
      hsmc.add hsmc.smul hcw) y hy).2 X hX
  have hDA := Gp91.GlobalTheory.DerivedAction.derived_action hK k r ε mu R hR X hX
  have hexp : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ BranchingSupport.GG k r :=
    fun t => Gp91.GlobalTheory.DerivedAction.exp_mem hX t
  have hfun : (fun t : ℝ => io s c ((RI s).σ (NormedSpace.exp ((t : ℂ) • X)) y)) =
      fun t : ℝ => ∑ j, (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c •
        R.σ (NormedSpace.exp ((t : ℂ) • X)) (io s j y) := by
    funext t
    have h := congrFun (hT.io_eq s _ (hexp t) y hy) c
    simpa [BranchingSupport.act, BranchingSupport.dualM, Matrix.transpose_apply] using h
  rw [hfun] at hL
  have hR' : HasDerivAt (fun t : ℝ => ∑ j, (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c •
        R.σ (NormedSpace.exp ((t : ℂ) • X)) (io s j y))
      (∑ j, ((NormedSpace.exp (((0 : ℝ) : ℂ) • X))⁻¹ j c • dsig (k := k) (r := r) R.σ X (io s j y) +
        (-X j c) • R.σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) (io s j y))) 0 := by
    have hs := HasDerivAt.sum (u := Finset.univ) (fun j _ => (hasDerivAt_inv_exp_entry X j c).smul
      ((hDA.1 (io s j y) ((hT.io_sm s j).mem y hy)).2))
    convert hs using 1
    funext t
    simp [Finset.sum_apply]
  have key := hL.unique hR'
  have hone : R.σ 1 = 1 := by
    obtain ⟨P, ⟨⟨hPu, -⟩, -⟩, hds⟩ := hR.ds
    have h1 := hds.2.2.1.1.1
    simp only [mul_one] at h1
    rwa [Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hPu)] at h1
  rw [key]
  simp [hone, Matrix.one_apply, Finset.sum_add_distrib, ite_smul, sub_eq_add_neg]

end GlobalTheory.DualEmb

namespace GlobalTheory

open DualEmb

theorem dualTens_io_dC : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H), (∀ s, (RI s).IsDG ε (muI s)) → TensRaw dualM R RI io pr → ∀ s Y, ∀ y ∈ (RI s).sm, ∀ c, io s c ((RI s).dC Y y) = R.dC Y (io s c y) - ∑ j, Y j c • io s j y := by
  intro hK k r ε mu R hR RI muI io pr hI hT s Y y hy c
  have h1 := DualEmb.lie_part₁ (k := k) (r := r) Y
  have h2 := DualEmb.lie_part₂ (k := k) (r := r) Y
  have e1 := DualEmb.io_dsig hK hR hI hT s h1 hy c
  have e2 := DualEmb.io_dsig hK hR hI hT s h2 hy c
  have hsmc := hT.io_sm s c
  have hd1 := ((Gp91.GlobalTheory.DerivedAction.derived_action hK k r ε (muI s) (RI s) (hI s) _ h1).1 y hy).1
  have hd2 := ((Gp91.GlobalTheory.DerivedAction.derived_action hK k r ε (muI s) (RI s) (hI s) _ h2).1 y hy).1
  have hzero : (0 : (RI s).H) ∈ (RI s).sm := by
    have hneg : -y ∈ (RI s).sm := by
      have := Gp91.GlobalTheory.CWDeriv.sm_comb (R := RI s) 1 hy hy hy
      simpa using this
    have h3 := Gp91.GlobalTheory.CWDeriv.sm_comb (R := RI s) (1 / 2) hy hneg hy
    have e : (1 / 2 : ℂ) • (y - -y) - y = 0 := by
      rw [sub_neg_eq_add, ← two_smul ℂ y, smul_smul]
      norm_num
    rwa [e] at h3
  have hsmul : ∀ (a : ℂ) {v : (RI s).H}, v ∈ (RI s).sm → a • v ∈ (RI s).sm := by
    intro a v hv
    have := Gp91.GlobalTheory.CWDeriv.sm_comb (R := RI s) a hv hzero hzero
    simpa using this
  have hYsplit : ∀ j, ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) j c +
      Complex.I * ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) j c =
      Y j c := by
    intro j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply, smul_eq_mul]
    field_simp
    ring
  have hsum : ∑ j, Y j c • io s j y =
      ∑ j, ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) j c • io s j y +
        Complex.I • ∑ j, ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) j c •
          io s j y := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hYsplit j, add_smul, mul_smul]
  simp only [BranchingSupport.Rep.dC]
  rw [hsmc.add _ hd1 _ (hsmul Complex.I hd2), hsmc.smul Complex.I _ hd2, e1, e2, hsum, smul_sub]
  abel

end GlobalTheory

end
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeriesStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ Formalism.REAL.KHighest ε E (Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (Formalism.REAL.kSpan ε E w) := by
  first | exact @GlobalTheory.LowestVector.exists_lowest_vector | exact GlobalTheory.LowestVector.exists_lowest_vector | (intros; apply GlobalTheory.LowestVector.exists_lowest_vector <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrechetContinuousContinuousOnOrbitHasDerivAtStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ v ∈ R.sm, ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → HasDerivAt (fun t : ℝ => Bm (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) (Bm (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) 0 := by
  first | exact @GlobalTheory.cwCont_continuousOn_hasDerivAt | exact GlobalTheory.cwCont_continuousOn_hasDerivAt | (intros; apply GlobalTheory.cwCont_continuousOn_hasDerivAt <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.GapCoefficientBound
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselNormSq

theorem integral_comp_mp {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) {F : X → ℂ} (hF : Integrable F μ) :
    ∫ x, F x ∂μ = ∫ x, F (f x) ∂μ := by
  have h1 : AEStronglyMeasurable F (μ.map f) := by rw [hf.map_eq]; exact hF.1
  rw [← integral_map hf.measurable.aemeasurable h1, hf.map_eq]

theorem inner_integral_apply {X Wp : Type} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {F : X → (Wp →L[ℂ] Wp)} (hF : Integrable F μ) (ξ η : Wp) :
    ⟪η, (∫ x, F x ∂μ) ξ⟫_ℂ = ∫ x, ⟪η, F x ξ⟫_ℂ ∂μ ∧
    ⟪(∫ x, F x ∂μ) ξ, η⟫_ℂ = ∫ x, ⟪F x ξ, η⟫_ℂ ∂μ ∧ Integrable (fun x => ⟪F x ξ, η⟫_ℂ) μ := by
  have h1 : Integrable (fun x => F x ξ) μ := hF.apply_continuousLinearMap ξ
  have h2 : ⟪η, (∫ x, F x ∂μ) ξ⟫_ℂ = ∫ x, ⟪η, F x ξ⟫_ℂ ∂μ := by
    rw [ContinuousLinearMap.integral_apply hF, integral_inner h1]
  refine ⟨h2, ?_, h1.inner_const η⟩
  rw [← inner_conj_symm, h2, ← integral_conj]
  simp only [inner_conj_symm]

end GlobalTheory.BesselNormSq


open GlobalTheory.BesselNormSq in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.bessel_norm_sq_double_integral : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ ξ : Wp, ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ‖ ^ 2 : ℝ) : ℂ) = ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, (∫ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, ⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star ⟪v, R.σ (Matrix.of q.1 * Matrix.of q.2 * (Matrix.of p.1 * Matrix.of p.2)) w⟫_ℂ * (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of q.2) * ⟪π (Matrix.of q.1)⁻¹ ξ, ξ⟫_ℂ) ∂(μW.prod μN)) ∂(μW.prod μN) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv w hw ξ
  have hint := (GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv).1 w hw
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨hψ1, hψm, -, hψc, hUW, -⟩ := _root_.GlobalTheory.BesselPsi.psi_character k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hmp, -, -, -, -, hae⟩ := _root_.GlobalTheory.sParam_measurePreserving k r z μW μN hok.1 hz hT hW hN
  obtain ⟨-, hmul, hunit, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ
  have e0 : ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ‖ ^ 2 : ℝ) : ℂ) =
      ⟪be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e0]
  refine ((GlobalTheory.BesselNormSq.inner_integral_apply hint ξ _).1).trans (integral_congr_ae ?_)
  filter_upwards [hae] with p hp
  obtain ⟨-, h2, h3⟩ := GlobalTheory.BesselNormSq.inner_integral_apply hint ξ (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v p ξ)
  refine h2.trans ((GlobalTheory.BesselNormSq.integral_comp_mp (hmp _ hp.1 _ hp.2).1 h3).trans (integral_congr_ae ?_))
  filter_upwards [hae] with q hq
  obtain ⟨⟨p1, p2⟩, hp1, hp2⟩ : ∃ p' : Mx k r × Mx k r, p'.1 = Matrix.of p.1 ∧ p'.2 = Matrix.of p.2 :=
    ⟨(_, _), rfl, rfl⟩
  obtain ⟨⟨q1, q2⟩, hq1, hq2⟩ : ∃ p' : Mx k r × Mx k r, p'.1 = Matrix.of q.1 ∧ p'.2 = Matrix.of q.2 :=
    ⟨(_, _), rfl, rfl⟩
  simp only at hp1 hp2 hq1 hq2
  have key : ∀ A : Mx k r, Matrix.of (fun i j => A i j) = A := fun A => rfl
  unfold beInt
  simp only [key]
  rw [← hp1, ← hp2] at hp
  rw [← hq1, ← hq2] at hq
  rw [← hp1, ← hp2, ← hq1, ← hq2]
  obtain ⟨hpi, hpp, hpp'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.1
  obtain ⟨hqi, -, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hq.1
  have e1 : q1 * p1 * (p1⁻¹ * q2 * p1 * p2) = q1 * q2 * (p1 * p2) := by
    calc q1 * p1 * (p1⁻¹ * q2 * p1 * p2) = q1 * (p1 * p1⁻¹) * q2 * (p1 * p2) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hpp, Matrix.mul_one]
  have e2 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (p1⁻¹ * q2 * p1 * p2) =
      Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd q2 * Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2 := by
    obtain ⟨-, a2, -, a4⟩ := hψc p1 hp.1 q2 hq.2
    rw [(hψm _ a2 _ hp.2).2, a4]
  have e3 : π (q1 * p1)⁻¹ = (π p1⁻¹).comp (π q1⁻¹) := by
    rw [Matrix.mul_inv_rev, hmul _ hpi _ hqi]
  have hiso : ∀ a b, ⟪π p1⁻¹ a, π p1⁻¹ b⟫_ℂ = ⟪a, b⟫_ℂ :=
    (LinearMap.norm_map_iff_inner_map_map ((π p1⁻¹ : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1 (hunit _ hpi)
  have e4 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2 * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd p2) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ1]; simp
  rw [e1, e2, e3]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_smul_left, inner_smul_right,
    hiso, map_mul, starRingEnd_apply, star_mul', star_star]
  linear_combination (⟪v, R.σ (p1 * p2) w⟫_ℂ * star ⟪v, R.σ (q1 * q2 * (p1 * p2)) w⟫_ℂ *
    (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd q2 * ⟪π q1⁻¹ ξ, ξ⟫_ℂ)) * e4
end Gp91
end

