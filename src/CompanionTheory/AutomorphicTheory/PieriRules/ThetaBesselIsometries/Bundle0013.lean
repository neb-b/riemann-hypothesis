module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0012
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0003
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsometricBesselCompare

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapDecay
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselOrbital

theorem bessel_integral_eq_smul : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
  classical
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hok hl hl'
  have hpt : ∀ γ ∈ JF.Om k r D.z D.z', ∃ O : Wq →L[ℂ] Wp, ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ X : Wq →L[ℂ] Wp,
      B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ = ⟪l x, X (l' y)⟫_ℂ • O := by
    intro γ hγ
    obtain ⟨A, hA1, hA2⟩ := GlobalTheory.T.bessel_orbital_integral_factors_through_left_functional hH k r ε mu h R Wp Wq D l l' hDS hgap hok hl hl' γ hγ
    obtain ⟨Bb, hB1, hB2⟩ := GlobalTheory.T.bessel_orbital_integral_factors_through_right_functional hH k r ε mu h R Wp Wq D l l' hDS hgap hok hl hl' γ hγ
    obtain ⟨O, hO⟩ := _root_.GlobalTheory.factorisation_of_two_partial_integrations R.TK Wp Wq (fun x => l x) (fun y => l' y)
      (fun x y X => B.JF D (fun g => ⟪(x : R.H), R.σ g y⟫_ℂ • X) γ)
      (fun y => A y) (fun x => Bb x) (fun y => hA1 y) (fun x => hB1 x)
      (fun x y X c => hA2 x x.2 y y.2 X c) (fun x y X c => hB2 x x.2 y y.2 X c)
    exact ⟨O, fun x hx y hy X => hO ⟨x, hx⟩ ⟨y, hy⟩ X⟩
  choose! OO hOO using hpt
  have hint : ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z',
      Integrable (JF.integrand D F γ) D.μSS := by
    intro F s hF γ hγ
    exact (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ F (_root_.GlobalTheory.thresholds_of_gapOK k r h hok).1
      ((GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH k r ε mu h R Wp Wq l l' F s hDS hgap hok hF).2 0)).1 γ hγ
  refine ⟨OO, fun F s hF γ hγ => ⟨hint F s hF γ hγ, ?_⟩⟩
  obtain ⟨m, x, y, X, hxy, hFe, hs⟩ := hF
  have hγG : γ ∈ GG k r := hγ.1
  obtain ⟨hloc, -, hsum, -⟩ := GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum k r Wp Wq D γ hγG
  rw [(hloc F (fun g => ∑ i, ⟪x i, R.σ g (y i)⟫_ℂ • X i) hFe).1,
    hsum (Fin m) (fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i) ?_, hs, Finset.sum_smul]
  · exact Finset.sum_congr rfl fun i _ => hOO γ hγ _ (hxy i).1 _ (hxy i).2 _
  · intro i
    refine hint _ ⟪l (x i), X i (l' (y i))⟫_ℂ ⟨1, fun _ => x i, fun _ => y i, fun _ => X i,
      fun _ => hxy i, fun g _ => ?_, ?_⟩ γ hγ
    · simp
    · simp

end GlobalTheory.BesselOrbital
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsModularStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.cayley_endomorphisms_modular : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), 1 ≤ k → R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → IsMod ε E mu := by
  first | exact @GlobalTheory.isMod_smooth_of_isDS | exact GlobalTheory.isMod_smooth_of_isDS | (intros; apply GlobalTheory.isMod_smooth_of_isDS <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorBesselMomentStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.dual_tensor_bessel_moment : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (RI : Fin (2 * r + k + 1) → Rep k r) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp), 1 ≤ k → R.IsDG ε mu → (∀ s, (RI s).IsDG ε (mu - Pi.single s 1)) → TensRaw dualM R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π l → ∀ s, ∃ c : ℂ, ‖c‖ = Formalism.QuantumDeterminants.Tz k r z * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ v ∈ R.sm, l (ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (fun c' => io s c' (∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d)))) = c • l v := by
  first | exact @GlobalTheory.bessel_ev_projector_value | exact GlobalTheory.bessel_ev_projector_value | (intros; apply GlobalTheory.bessel_ev_projector_value <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowthStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν ≤ q0 → (∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (‖w‖ ^ 2)) ∧ (NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧ ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)) := by
  first | exact @GlobalTheory.MomMass.mom_mass | exact GlobalTheory.MomMass.mom_mass | (intros; apply GlobalTheory.MomMass.mom_mass <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsometricBesselCompareStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.isometric_bessel_compare : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp) (Bm' : R'.H → Wp), R.IsDG ε mu → R'.IsDG ε mu' → mu ≠ mu' → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → IsIsoB R' z π νq Bm' → ∀ w ∈ R.sm, ∀ y ∈ R'.sm, ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = 0 := by
  first | exact @GlobalTheory.bessel_orth_of_param_ne | exact GlobalTheory.bessel_orth_of_param_ne | (intros; apply GlobalTheory.bessel_orth_of_param_ne <;> assumption)
end Gp91
end

