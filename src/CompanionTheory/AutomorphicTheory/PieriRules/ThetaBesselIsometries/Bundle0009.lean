module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreePairing
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0007
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapDimensionFormula
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0004
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselLieTriangularVanishing
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorCayleyCompatible
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionInjectiveParameters
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreePairingStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_formal_degree_pairing : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  first | exact @GlobalTheory.integral_xi_mul_Ph | exact GlobalTheory.integral_xi_mul_Ph | (intros; apply GlobalTheory.integral_xi_mul_Ph <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFrameEntryRelationStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_frame_entry_relation : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp) (g : Mx k r), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsFrameW k r z g → IsBes R z π l → ∀ i j : Fin k, ∀ v ∈ R.sm, l (R.dC (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) v) = Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) (l v) := by
  first | exact @GlobalTheory.BesselIntertwine.bessel_intertwines_glW | exact GlobalTheory.BesselIntertwine.bessel_intertwines_glW | (intros; apply GlobalTheory.BesselIntertwine.bessel_intertwines_glW <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapDimensionFormulaStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ dd : ℝ, (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → ∀ v ∈ R.TK, ∀ ξ : Wp, (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).re ∧ 0 < dd ∧ ∀ w ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ g w) v ξ) = ENNReal.ofReal (‖w‖ ^ 2 * (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).re / dd) := by
  first | exact @GlobalTheory.BesselNorm.norm_identity | exact GlobalTheory.BesselNorm.norm_identity | (intros; apply GlobalTheory.BesselNorm.norm_identity <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapIntegrability
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem be_apply_isBes : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ ξ : Wp, IsBes R z π (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv ξ
  obtain ⟨-, C, Ws, hWs, hC⟩ := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv
  obtain ⟨hlin, -⟩ := GlobalTheory.T.bessel_gap_pairing hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS
  have heq := GlobalTheory.T.bessel_integral_equivariant_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv
  refine ⟨fun w hw w' hw' => ?_, fun a w hw => ?_, fun g hg m hm w hw => ?_, ‖ξ‖ * C, Ws, hWs, fun w hw => ?_⟩
  · simp only [(hlin v hv w hw w' hw' 0).1, ContinuousLinearMap.add_apply]
  · simp only [(hlin v hv w hw w hw a).2, ContinuousLinearMap.smul_apply]
  · simp only [heq w hw g hg m hm, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [mul_comm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg _)

end GlobalTheory
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselLieTriangularVanishingStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_functional_lie_triangular_eq_character_smul : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), Formalism.QuantumDeterminants.inWb k r z → (∀ x, π 1 x = x) → IsBes R z π l → ∀ Y : Mx k r, (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → Y i j = 0) → ∀ v ∈ R.sm, l (R.dC Y v) = (Formalism.QuantumDeterminants.ell k r z Y - star (Formalism.QuantumDeterminants.ell k r z (-((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r))))) • l v := by
  first | exact @GlobalTheory.BesselNilp.bessel_dC | exact GlobalTheory.BesselNilp.bessel_dC | (intros; apply GlobalTheory.BesselNilp.bessel_dC <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPair
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory
namespace CoefDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dLR_zero (u v : List (B.Mat k r)) : B.dLR u v (0 : B.Mat k r → E) = 0 := by
  have h1 : B.Rw v (0 : B.Mat k r → E) = 0 := by
    unfold B.Rw
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.foldr_cons, ih]
      funext g
      simp [Formalism.REAL.RdV]
  unfold B.dLR
  rw [h1]
  induction u with
  | nil => rfl
  | cons X u ih =>
    rw [List.foldr_cons, ih]
    funext g
    simp [B.LdV]

theorem sum_mem {ι : Type} (A : ℝ) (f : ι → B.Mat k r → E) (t : Finset ι)
    (hf : ∀ i ∈ t, B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC A m (f i)) :
    B.CkOn ⊤ (B.GV k r) (∑ i ∈ t, f i) ∧ ∀ m : ℕ, B.InCC A m (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    refine ⟨fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
      fun m => ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩⟩
    intro u v _ _ _ g _
    simp [dLR_zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := hf i (Finset.mem_insert_self _ _)
    obtain ⟨h3, h4⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine ⟨Formalism.FourierDecayAlt.P.B4.ckOn_add h1 h3, fun m => ?_⟩
    obtain ⟨c, hc⟩ := h2 m
    obtain ⟨c', hc'⟩ := h4 m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r E A m _ _ c c' 1 hc hc').1⟩

end CoefDecay

theorem isCoef_ckOn_inCC : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsCoef R l l' F s → B.CkOn ⊤ (B.GV k r) F ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m F := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ l l' F s hR hg hok hF
  obtain ⟨n, x, y, X, hxy, hFe, -⟩ := hF
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hsm : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR).2.2.2.2.1
  let f : Fin n → B.Mat k r → (Wq →L[ℂ] Wp) := fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m (f i) := by
    intro i _
    obtain ⟨h1, h2⟩ := GlobalTheory.T.matrix_coefficient_smooth_derivatives hK k r ε mu R (Wq →L[ℂ] Wp) (X i) (f i) hR (x i) (hsm _ (hxy i).1)
      (y i) (hsm _ (hxy i).2) (fun g _ => rfl)
    refine ⟨h1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := GlobalTheory.T.matrix_coefficient_decay hH k r ε mu h R hR hg hok (x i) (hxy i).1 (y i) (hxy i).2 m
    refine ⟨c * ‖X i‖, Formalism.FourierDecayAlt.P.B6.smooth_on_mono le_top h1, fun u v hu hv hlen g hgG => ?_⟩
    rw [h2 u v (fun Y hY => (hu Y hY).1) (fun Y hY => (hv Y hY).1) g hgG, norm_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc u v hu hv hlen g hgG) (norm_nonneg _)
  obtain ⟨h1, h2⟩ := CoefDecay.sum_mem (aOf r h - 1) f Finset.univ hf
  have hc := GlobalTheory.ckOn_inCC_congr_on_group k r (Wq →L[ℂ] Wp) (aOf r h - 1) (∑ i, f i) F
    (fun g hgG => by rw [hFe g hgG, Finset.sum_apply])
  exact ⟨hc.1 h1, fun m => hc.2 m (h2 m)⟩

end GlobalTheory
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSumDecompositionStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.isBes_tensor_projection_and_ev_equivariant_smooth : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (om : ι → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → ∀ I, (∀ lI, IsBes (RI I) z π lI → IsBes R z π (fun v => lI (∑ c, pr I c (tm R om v c)))) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ y ∈ (RI I).sm, ev Γ R om (fun c => io I c ((RI I).σ s y)) = R.σ s (ev Γ R om (fun c => io I c y))) ∧ SmMap (RI I) R (fun y => ev Γ R om (fun c => io I c y)) := by
  first | exact @GlobalTheory.KapBes.main | exact GlobalTheory.KapBes.main | (intros; apply GlobalTheory.KapBes.main <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsUnitaryStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.cayley_endomorphisms_unitary : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → Formalism.REAL.IsUnitary ε E := by
  first | exact @GlobalTheory.CapUnitary.isUnitary_of_isE | exact GlobalTheory.CapUnitary.isUnitary_of_isE | (intros; apply GlobalTheory.CapUnitary.isUnitary_of_isE <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionExpandMatrixUnitsStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.derivedAction_expand_matrixUnits : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  first | exact @GlobalTheory.dC_expand_units | exact GlobalTheory.dC_expand_units | (intros; apply GlobalTheory.dC_expand_units <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorCayleyCompatibleStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.dual_tensor_cayley_compatible : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDG ε (muI s)) → TensRaw dualM R RI io pr → IsUnit Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧ (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧ (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧ (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧ (∀ s y d, ((io' s y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • io s c (y : (RI s).H)) ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  first | exact @GlobalTheory.RawTens.rawTens | exact GlobalTheory.RawTens.rawTens | (intros; apply GlobalTheory.RawTens.rawTens <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.PieriTensorDecomposition
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensExists

theorem l1_add_le {n : ℕ} (x y : Fin n → ℤ) : n1 (x + y) ≤ n1 x + n1 y := by
  unfold n1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem l1_sub_le {n : ℕ} (x y : Fin n → ℤ) : n1 (x - y) ≤ n1 x + n1 y := by
  unfold n1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_sub_le _ _

theorem n1_eZ_eq_card {n : ℕ} (I : Finset (Fin n)) : n1 (eZ I) = I.card := by
  unfold n1 eZ
  have : ∀ i : Fin n, (if i ∈ I then (1 : ℤ) else 0).natAbs = if i ∈ I then 1 else 0 := by
    intro i; split_ifs <;> rfl
  simp [this]

theorem l1_single {n : ℕ} (s : Fin n) : n1 (Pi.single s (1 : ℤ)) = 1 := by
  unfold n1
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem addSet_inj {n l : ℕ} (mu : Fin n → ℝ) : Function.Injective (fun I : Sub n l => addSet mu I.1) := by
  intro I J hIJ
  apply Subtype.ext
  ext a
  have h := congrFun hIJ a
  simp only [addSet, add_right_inj] at h
  by_cases h1 : a ∈ I.1 <;> by_cases h2 : a ∈ J.1 <;> simp_all

theorem sub_single_inj {n : ℕ} (mu : Fin n → ℝ) :
    Function.Injective (fun s : Fin n => mu - (Pi.single s 1 : Fin n → ℝ)) := by
  intro s t hst
  by_contra hne
  have h := congrFun hst s
  simp [Pi.single_apply, hne] at h

theorem tens_exists : HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFamG lam q0 R → ∀ ν, (∀ l, n1 ν + l ≤ q0 → ∃ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep) ∧ (n1 ν + 1 ≤ q0 → ∃ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep) := by
  intro hH k r lam u b bv ga h q0 R hN hF ν
  have hZ : ZuckG := hH.2.2.2.2.1
  have hnum := (_root_.GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN).2 ν
  constructor
  · intro l hl
    have h0 : n1 ν ≤ q0 := by omega
    have hR := hF ν h0
    have hI : ∀ I : Sub (2 * r + k + 1) l, (R (ν + eZ I.1)).IsDG (PI.BesselPeriodGGP.eps48 k r)
        (addSet (fun a => lam a + (ν a : ℝ)) I.1) := by
      intro I
      have h1 : n1 (ν + eZ I.1) ≤ q0 := by
        have := l1_add_le ν (eZ I.1)
        rw [n1_eZ_eq_card, I.2] at this
        omega
      have h2 := hF _ h1
      have e : (fun a => lam a + (((ν + eZ I.1) a : ℤ) : ℝ)) = addSet (fun a => lam a + (ν a : ℝ)) I.1 := by
        funext a
        simp only [addSet, eZ, Pi.add_apply]
        split_ifs <;> push_cast <;> ring
      rwa [e] at h2
    obtain ⟨io, pr, hT⟩ := (hZ k r _ lam q0 R hF ν).1 l hl
    exact _root_.Gp91.GlobalTheory.TensOrth.tensH_of_raw hH k r _ _ _ _ l _ _ io pr _ _ _ hR hI (addSet_inj _) (GlobalTheory.T.isFRep_exteriorPower_standardRep k r l) hT
  · intro hl
    have h0 : n1 ν ≤ q0 := by omega
    have hR := hF ν h0
    have hI : ∀ s : Fin (2 * r + k + 1), (R (ν - Pi.single s 1)).IsDG (PI.BesselPeriodGGP.eps48 k r)
        ((fun a => lam a + (ν a : ℝ)) - Pi.single s 1) := by
      intro s
      have h1 : n1 (ν - Pi.single s 1) ≤ q0 := by
        have := l1_sub_le ν (Pi.single s 1)
        rw [l1_single] at this
        omega
      have h2 := hF _ h1
      have e : (fun a => lam a + (((ν - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) =
          (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
        funext a
        simp only [Pi.sub_apply, Pi.single_apply]
        split_ifs <;> push_cast <;> ring
      rwa [e] at h2
    obtain ⟨io, pr, hT⟩ := (hZ k r _ lam q0 R hF ν).2 hl
    exact _root_.Gp91.GlobalTheory.TensOrth.tensH_of_raw hH k r _ _ _ _ 1 _ _ io pr _ _ _ hR hI (sub_single_inj _) (GlobalTheory.T.isFRep_dual_standard_unitaryRep k r) hT

end GlobalTheory.TensExists
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModelStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  first | exact @GlobalTheory.quotMeas_ae_mem_and_measurable | exact GlobalTheory.quotMeas_ae_mem_and_measurable | (intros; apply GlobalTheory.quotMeas_ae_mem_and_measurable <;> assumption)
end Gp91
end

